package leanvalidate

import (
	"fmt"
	"sort"
	"strings"

	validatepb "buf.build/gen/go/bufbuild/protovalidate/protocolbuffers/go/buf/validate"
	"google.golang.org/protobuf/compiler/protogen"
	"google.golang.org/protobuf/reflect/protoreflect"

	"github.com/petersonbill64/protovalidate-lean/celtolean"
)

// precAndOperand mirrors Lean's ∧ precedence: conjuncts of a multi-rule
// subtype are parenthesized when their translation binds more loosely.
const precAndOperand = 36

// runtimeNS qualifies the Protovalidate runtime absolutely: generated code
// lives inside proto-package namespaces whose components could shadow it.
const runtimeNS = "_root_.Protovalidate"

type fieldShape int

const (
	shapePlain  fieldShape = iota // scalar/enum, always present
	shapeOption                   // optional scalar/enum or singular message: Option
	shapeList                     // repeated: Array
	shapeMap                      // map: Std.HashMap
)

type fieldPlan struct {
	f         *protogen.Field
	protoName string
	leanName  string
	shape     fieldShape
	rules     []loweredRule
	// required unwraps Option shapes; for implicit-presence shapes a
	// non-zero rule was appended during planning.
	required bool
	// ignoreZero wraps the refinement in a zero-value escape disjunct.
	ignoreZero bool

	// thisType is the Lean type CEL's `this` denotes for the field's rules
	// (the element type under Option, the whole container for list/map).
	thisType string
	// typeText is the field's type in the validated structure.
	typeText string
	// viewName is the generated per-field CEL view function (base-typed
	// value-or-default) for Option-shaped refined/validated fields.
	viewName string
	// subBinder/props hold the subtype refinement when rules are present.
	subBinder string
	props     []string
	// nested is set when the field embeds another validated message.
	nested *msgInfo

	// ValidPred conjunct names (empty when the conjunct does not apply):
	// presenceConj is the `isSome` conjunct of required Option shapes,
	// elemsConj the element-predicate conjunct of rule-carrying nested lists,
	// mainConj the field's rule/nested-predicate conjunct.
	presenceConj string
	elemsConj    string
	mainConj     string
	// predBinder is the ∀-binder of Option/element conjuncts.
	predBinder string
}

func (p *fieldPlan) constrained() bool { return len(p.rules) > 0 }

// unwrapped reports whether an Option-shaped field is unwrapped by required.
func (p *fieldPlan) unwrapped() bool { return p.shape == shapeOption && p.required }

type oneofPlan struct {
	o         *protogen.Oneof
	protoName string
	leanName  string
	// required unwraps the Option (exactly one case must be set).
	required bool
	// constrained: some member carries rules or a validated payload, so a
	// validated sum type with refined constructor payloads is generated.
	constrained bool
	members     []*oneofMember
	baseSum     string // fully-qualified base sum type
	validSum    string // fully-qualified validated sum type (when constrained)
	sumLocal    string // declared name of the validated sum within the namespace
	typeText    string // the oneof field's type in the validated structure

	// ValidPred conjunct names (as for fieldPlan).
	presenceConj string
	mainConj     string
	predBinder   string
}

type oneofMember struct {
	// plan is a synthetic per-member field plan (members are always singular,
	// so shapePlain drives the shared rule-rendering helpers).
	plan   *fieldPlan
	nested *msgInfo // validated payload for unannotated message members
	// accName is the value-or-default accessor generated for the member
	// (CEL semantics: the payload when the case is active, else the member
	// type's zero value).
	accName string
}

// ctorType is the constructor's payload type in the validated sum.
func (mem *oneofMember) ctorType() string {
	p := mem.plan
	if p.constrained() {
		return "{ " + p.subBinder + " : " + p.thisType + " // " + p.props[0] + " }"
	}
	if mem.nested != nil {
		return validQualified(mem.nested.msg)
	}
	return p.thisType
}

type propPlan struct {
	name string
	hyp  string
	text string // over the validated structure's fields (structure Prop field)
	// predText/checkText phrase the same rule over the base value's
	// constructed views: predText references ValidPred fields by name,
	// checkText the checkPred hypothesis binders.
	predText  string
	checkText string
	rule      *validatepb.Rule
}

// refFn resolves a ValidPred conjunct name to its reference text in the
// current context: the bare field name inside the ValidPred structure,
// `h.<name>` in ofPred, the bound hypothesis in checkPred.
type refFn func(conjName string) string

type fileGen struct {
	cfg     Config
	msgs    map[protoreflect.FullName]*msgInfo
	targets map[string]bool
	// covered additionally includes cross-target dependency files whose
	// validated types can be referenced.
	covered map[string]bool
	notes   map[string]bool
	// regexes collects the literal patterns of every translated rule; each
	// gets a compile-time `#guard Cel.Regex.accepts` in the generated file.
	regexes map[string]bool
}

func generateFile(gen *protogen.Plugin, f *protogen.File, cfg Config, msgs map[protoreflect.FullName]*msgInfo, targets, covered map[string]bool) error {
	fg := &fileGen{cfg: cfg, msgs: msgs, targets: targets, covered: covered, notes: map[string]bool{}, regexes: map[string]bool{}}

	// Messages of this file needing a validated variant, topologically sorted
	// so embedded validated types are declared before their containers.
	var order []*msgInfo
	seen := map[protoreflect.FullName]bool{}
	var dfs func(mi *msgInfo)
	dfs = func(mi *msgInfo) {
		name := mi.msg.Desc.FullName()
		if seen[name] {
			return
		}
		seen[name] = true
		for _, fd := range mi.msg.Fields {
			if dep := validFieldEdge(mi, fd, msgs, covered); dep != nil && dep.needsValid &&
				dep.msg.Desc.ParentFile().Path() == f.Desc.Path() {
				dfs(dep)
			}
		}
		order = append(order, mi)
	}
	for _, m := range f.Messages {
		walkMessages(m, func(m *protogen.Message) {
			if mi := msgs[m.Desc.FullName()]; mi != nil && mi.needsValid {
				dfs(mi)
			}
		})
	}

	out := gen.NewGeneratedFile(protoStem(f.Desc.Path())+".lean", "")
	out.P("-- Generated by protoc-gen-lean-protovalidate. Do not edit.")
	out.P("-- Source: ", f.Desc.Path())
	out.P("module")
	out.P()
	if len(order) == 0 {
		out.P("-- No messages with protovalidate rules.")
		return nil
	}

	body := &strings.Builder{}
	for _, mi := range order {
		if err := fg.emitMessage(body, mi); err != nil {
			return fmt.Errorf("message %s: %w", mi.msg.Desc.FullName(), err)
		}
	}

	out.P("public import Protovalidate.Cel")
	out.P("public import Protovalidate.Runtime")
	if len(fg.regexes) > 0 {
		// #guard evaluates Cel.Regex.accepts at elaboration time, which needs
		// the implementation meta-imported under the module system.
		out.P("meta import Protovalidate.Cel.Regex")
	}
	out.P("public import ", cfg.BasePrefix, ".", protoStem(f.Desc.Path()))
	imports := f.Desc.Imports()
	for i := 0; i < imports.Len(); i++ {
		dep := imports.Get(i)
		if targets[dep.Path()] {
			out.P("public import ", cfg.BasePrefix, ".", protoStem(dep.Path()))
			out.P("public import ", cfg.Prefix, ".", protoStem(dep.Path()))
		} else if dm, ok := cfg.DepModules[dep.Path()]; ok {
			out.P("public import ", dm.Base, ".", protoStem(dep.Path()))
			out.P("public import ", dm.Valid, ".", protoStem(dep.Path()))
		}
	}
	out.P()
	out.P("public section")
	out.P()
	out.P("set_option linter.unusedVariables false")
	out.P()
	if len(fg.regexes) > 0 {
		out.P("-- Acceptance backstop: every literal regex must be inside the subset the")
		out.P("-- Lean engine (Cel.Regex) supports — an unsupported pattern would match")
		out.P("-- nothing at runtime, which is unsound under negation. A failing guard")
		out.P("-- means the generator's Go-side gate and the Lean engine disagree.")
		regexes := make([]string, 0, len(fg.regexes))
		for re := range fg.regexes {
			regexes = append(regexes, re)
		}
		sort.Strings(regexes)
		for _, re := range regexes {
			out.P("#guard Cel.Regex.accepts ", celtolean.LeanString(re))
		}
		out.P()
	}
	if len(fg.notes) > 0 {
		out.P("/- cel2lean translation notes:")
		notes := make([]string, 0, len(fg.notes))
		for n := range fg.notes {
			notes = append(notes, n)
		}
		sort.Strings(notes)
		for _, n := range notes {
			out.P("   - ", docText(n))
		}
		out.P("-/")
		out.P()
	}
	out.P("namespace ", validNamespace(f.Desc.Package()))
	out.P()
	out.P(strings.TrimRight(body.String(), "\n"))
	out.P()
	out.P("end ", validNamespace(f.Desc.Package()))
	return nil
}

func (fg *fileGen) translate(cel string, opts celtolean.Options) (*celtolean.Result, error) {
	res, err := celtolean.Translate(cel, opts)
	if err != nil {
		return nil, err
	}
	if res.Kind == "term" {
		return nil, fmt.Errorf("CEL expression %q is not boolean-valued", cel)
	}
	for _, w := range res.Warnings {
		fg.notes[w] = true
	}
	for _, re := range res.Regexes {
		fg.regexes[re] = true
	}
	return res, nil
}

// violationLit renders a Protovalidate.Violation structure literal.
func violationLit(fieldPath, id, message string) string {
	return "{ fieldPath := " + celtolean.LeanString(fieldPath) +
		", ruleId := " + celtolean.LeanString(id) +
		", message := " + celtolean.LeanString(message) + " }"
}

func ruleViolationLit(fieldPath string, r loweredRule) string {
	msg := r.message
	if msg == "" {
		msg = r.cel
	}
	return violationLit(fieldPath, r.id, msg)
}

// iteChain renders nested dependent ifs deciding each rule, yielding ok with
// all hypotheses in scope or the first failing rule's else-branch text.
func iteChain(w *strings.Builder, indent string, hyps, conds []string, ok string, errs []string) {
	if len(conds) == 0 {
		w.WriteString(indent + ok + "\n")
		return
	}
	w.WriteString(indent + "if " + hyps[0] + " : " + conds[0] + " then\n")
	iteChain(w, indent+"  ", hyps[1:], conds[1:], ok, errs[1:])
	w.WriteString(indent + "else " + errs[0] + "\n")
}

// andPath projects the i-th conjunct out of a right-nested n-conjunction
// proof term.
func andPath(base string, i, n int) string {
	s := base
	for k := 0; k < i; k++ {
		s += ".2"
	}
	if i < n-1 {
		s += ".1"
	}
	return s
}

// zeroEscape is the Lean proposition "the value is its protobuf zero value",
// used by ignoreZero refinements. The subject must be atomic.
func zeroEscape(p *fieldPlan, subject string) string {
	switch p.shape {
	case shapeList, shapeMap:
		return subject + ".isEmpty"
	case shapeOption, shapePlain:
	}
	switch p.f.Desc.Kind() {
	case protoreflect.StringKind:
		return subject + ".isEmpty"
	case protoreflect.BytesKind:
		return subject + ".size = 0"
	case protoreflect.BoolKind:
		return subject + " = false"
	case protoreflect.FloatKind, protoreflect.DoubleKind:
		return subject + " = 0.0"
	case protoreflect.EnumKind:
		if zero := p.f.Enum.Desc.Values().ByNumber(0); zero != nil {
			return "(" + subject + " matches ." + celtolean.LeanIdent(string(zero.Name())) + ")"
		}
		return subject + " = default"
	default:
		return subject + " = 0"
	}
}

// requiredRule encodes protovalidate `required` on implicit-presence shapes
// as a non-zero rule (explicit-presence fields are structurally unwrapped
// instead).
func requiredRule(p *fieldPlan) loweredRule {
	kind := p.f.Desc.Kind()
	shape := p.shape
	enum := p.f.Enum
	return loweredRule{
		id:      "required",
		message: "value is required",
		direct: func(_ *fileGen, subject string) (string, int, error) {
			switch shape {
			case shapeList, shapeMap:
				return "¬" + subject + ".isEmpty", 40, nil
			}
			switch kind {
			case protoreflect.StringKind:
				return "¬" + subject + ".isEmpty", 40, nil
			case protoreflect.BytesKind:
				return subject + ".size ≠ 0", 50, nil
			case protoreflect.BoolKind:
				return subject + " = true", 50, nil
			case protoreflect.FloatKind, protoreflect.DoubleKind:
				return subject + " ≠ 0.0", 50, nil
			case protoreflect.EnumKind:
				if enum != nil {
					if zero := enum.Desc.Values().ByNumber(0); zero != nil {
						return "¬(" + subject + " matches ." + celtolean.LeanIdent(string(zero.Name())) + ")", 40, nil
					}
				}
				return subject + " ≠ default", 50, nil
			default:
				return subject + " ≠ 0", 50, nil
			}
		},
	}
}

// renderProps renders every rule of a field against a subject, parenthesized
// for conjunction, with the zero-escape disjunct applied when ignoreZero.
func (fg *fileGen) renderProps(p *fieldPlan, subject string) (string, error) {
	parts := make([]string, 0, len(p.rules))
	for _, r := range p.rules {
		t, prec, err := fg.renderRule(r, subject)
		if err != nil {
			return "", fmt.Errorf("field %s: %w", p.protoName, err)
		}
		if len(p.rules) > 1 && prec < precAndOperand {
			t = "(" + t + ")"
		}
		parts = append(parts, t)
	}
	conj := strings.Join(parts, " ∧ ")
	if p.ignoreZero {
		return zeroEscape(p, subject) + " ∨ (" + conj + ")", nil
	}
	return conj, nil
}

// decisionChain renders the dependent-if chain deciding a field's rules as a
// Decision term: `okOf(proof)` on success, `.fail (fun hc => …) violation` on
// the first failing rule. `conjOf(hc)` recovers the field's whole rule
// conjunction from the step's conjunct hypothesis (e.g. `hc`, or
// `(hc x rfl)` under a presence quantifier), which the failure glue projects.
func (fg *fileGen) decisionChain(w *strings.Builder, indent string, p *fieldPlan, subject, fieldPath string,
	okOf func(proof string) string, conjOf func(hc string) string, hcName string) error {
	n := len(p.rules)
	conds := make([]string, 0, n)
	errs := make([]string, 0, n)
	hyps := make([]string, 0, n)
	for i, r := range p.rules {
		t, _, err := fg.renderRule(r, subject)
		if err != nil {
			return fmt.Errorf("field %s: %w", p.protoName, err)
		}
		conds = append(conds, t)
		hyp := fmt.Sprintf("h%d", i)
		hyps = append(hyps, hyp)
		var neg string
		if p.ignoreZero {
			neg = conjOf(hcName) + ".elim h_z (fun hcz => " + hyp + " " + andPath("hcz", i, n) + ")"
		} else {
			neg = hyp + " " + andPath(conjOf(hcName), i, n)
		}
		errs = append(errs, ".fail (fun "+hcName+" => "+neg+") "+ruleViolationLit(fieldPath, r))
	}
	proof := "⟨" + strings.Join(hyps, ", ") + "⟩"
	if n == 1 {
		proof = hyps[0]
	}
	if p.ignoreZero {
		w.WriteString(indent + "if h_z : " + zeroEscape(p, subject) + " then " + okOf("Or.inl h_z") + "\n")
		w.WriteString(indent + "else\n")
		iteChain(w, indent+"  ", hyps, conds, okOf("Or.inr "+proof), errs)
		return nil
	}
	iteChain(w, indent, hyps, conds, okOf(proof), errs)
	return nil
}

func (fg *fileGen) emitMessage(w *strings.Builder, mi *msgInfo) error {
	m := mi.msg
	local := localName(m)
	base := baseQualified(m.Desc.FullName())

	// Names already claimed by struct fields/oneofs (locals in validate).
	taken := map[string]bool{}
	// Identifiers used inside any of the message's rules: binders must dodge
	// them so translations cannot capture.
	ruleIdents := map[string]bool{}
	addIdents := func(rules []loweredRule) {
		for _, r := range rules {
			for id := range r.idents {
				ruleIdents[id] = true
			}
		}
	}

	// ---- plan fields -------------------------------------------------------
	var fields []*fieldPlan
	for _, fd := range m.Fields {
		if fd.Oneof != nil && !fd.Oneof.Desc.IsSynthetic() {
			continue // carried through the oneof sum type below
		}
		set := mi.fieldRules[string(fd.Desc.Name())]
		p := &fieldPlan{
			f:          fd,
			protoName:  string(fd.Desc.Name()),
			leanName:   celtolean.LeanIdent(string(fd.Desc.Name())),
			rules:      set.rules,
			required:   set.required,
			ignoreZero: set.ignoreZero,
		}
		taken[p.protoName] = true
		addIdents(p.rules)
		switch {
		case fd.Desc.IsMap():
			k, err := scalarText(fd.Desc.MapKey().Kind(), nil, nil)
			if err != nil {
				return fmt.Errorf("field %s key: %w", p.protoName, err)
			}
			vd := fd.Desc.MapValue()
			var vmsg protoreflect.MessageDescriptor
			var venum protoreflect.EnumDescriptor
			if vd.Kind() == protoreflect.MessageKind {
				vmsg = vd.Message()
			} else if vd.Kind() == protoreflect.EnumKind {
				venum = vd.Enum()
			}
			v, err := scalarText(vd.Kind(), venum, vmsg)
			if err != nil {
				return fmt.Errorf("field %s value: %w", p.protoName, err)
			}
			p.shape = shapeMap
			p.thisType = "Std.HashMap " + k + " " + v
		case fd.Desc.IsList():
			elem, err := scalarText(fd.Desc.Kind(), enumDesc(fd), msgDesc(fd))
			if err != nil {
				return fmt.Errorf("field %s: %w", p.protoName, err)
			}
			p.shape = shapeList
			p.thisType = "Array " + elem
		case fd.Desc.Kind() == protoreflect.MessageKind:
			p.shape = shapeOption
			p.thisType = baseQualified(fd.Desc.Message().FullName())
		case fd.Desc.HasOptionalKeyword():
			elem, err := scalarText(fd.Desc.Kind(), enumDesc(fd), msgDesc(fd))
			if err != nil {
				return fmt.Errorf("field %s: %w", p.protoName, err)
			}
			p.shape = shapeOption
			p.thisType = elem
		default:
			elem, err := scalarText(fd.Desc.Kind(), enumDesc(fd), msgDesc(fd))
			if err != nil {
				return fmt.Errorf("field %s: %w", p.protoName, err)
			}
			p.shape = shapePlain
			p.thisType = elem
		}
		// required on implicit-presence shapes is an ordinary non-zero rule;
		// on Option shapes it structurally unwraps (handled below).
		if p.required && p.shape != shapeOption {
			p.rules = append([]loweredRule{requiredRule(p)}, p.rules...)
		}
		fields = append(fields, p)
	}
	msgRuleIdents := func() error {
		for _, r := range mi.msgRules {
			ids, err := celtolean.Idents(r.GetExpression())
			if err != nil {
				return fmt.Errorf("message rule %q: %w", r.GetId(), err)
			}
			for id := range ids {
				ruleIdents[id] = true
			}
		}
		return nil
	}
	if err := msgRuleIdents(); err != nil {
		return err
	}

	// Validated element types and subtype refinements.
	for _, p := range fields {
		if dep := validFieldEdge(mi, p.f, fg.msgs, fg.covered); dep != nil && dep.needsValid {
			p.nested = dep
			if p.shape == shapeList {
				// Rules on a repeated-message field refine the array of
				// *validated* elements, composing the structural list rule
				// with per-element validation.
				p.thisType = "Array " + validQualified(dep.msg)
			}
		}
		if !p.constrained() {
			continue
		}
		p.subBinder = freshTaken("x", ruleIdents)
		props, err := fg.renderProps(p, p.subBinder)
		if err != nil {
			return err
		}
		p.props = []string{props}
	}

	// Name the CEL view functions (emitted later, referenced by ThisFields).
	for _, p := range fields {
		if p.shape == shapeOption && !p.unwrapped() && (p.constrained() || p.nested != nil) {
			p.viewName = celtolean.LeanIdent(uniqueName(p.protoName+"D", taken))
		}
	}

	// Struct field type text.
	for _, p := range fields {
		inner := p.thisType
		if p.constrained() {
			inner = "{ " + p.subBinder + " : " + p.thisType + " // " + p.props[0] + " }"
		} else if p.nested != nil {
			switch p.shape {
			case shapeOption:
				inner = validQualified(p.nested.msg)
			case shapeList:
				inner = "Array " + validQualified(p.nested.msg)
			}
		}
		if p.shape == shapeOption && !p.unwrapped() {
			p.typeText = "Option " + wrapType(inner)
		} else {
			p.typeText = inner
		}
	}

	// Oneofs (real ones). Members with rules (or validated message payloads)
	// yield a validated sum type whose constructors carry the refined
	// payloads; (buf.validate.oneof).required unwraps the Option.
	var oneofs []*oneofPlan
	for _, o := range m.Oneofs {
		if o.Desc.IsSynthetic() {
			continue
		}
		name := string(o.Desc.Name())
		taken[name] = true
		op := &oneofPlan{
			o:         o,
			protoName: name,
			leanName:  celtolean.LeanIdent(name),
			required:  oneofRequired(o),
			baseSum:   base + "." + celtolean.LeanIdent(name+"_Type"),
			sumLocal:  local + "." + celtolean.LeanIdent(name+"_Type"),
			validSum:  validQualified(m) + "." + celtolean.LeanIdent(name+"_Type"),
		}
		for _, fd := range o.Fields {
			set := mi.fieldRules[string(fd.Desc.Name())]
			if set.required {
				fg.notes[fmt.Sprintf("field %s.%s: `required` on a oneof member is ignored (the active case already implies presence; use (buf.validate.oneof).required)",
					m.Desc.FullName(), fd.Desc.Name())] = true
			}
			p := &fieldPlan{
				f:          fd,
				protoName:  string(fd.Desc.Name()),
				leanName:   celtolean.LeanIdent(string(fd.Desc.Name())),
				shape:      shapePlain,
				rules:      set.rules,
				ignoreZero: set.ignoreZero,
			}
			addIdents(p.rules)
			var payload string
			var perr error
			if fd.Desc.Kind() == protoreflect.MessageKind {
				payload = baseQualified(fd.Desc.Message().FullName())
			} else {
				payload, perr = scalarText(fd.Desc.Kind(), enumDesc(fd), msgDesc(fd))
				if perr != nil {
					return fmt.Errorf("oneof member %s: %w", p.protoName, perr)
				}
			}
			p.thisType = payload
			mem := &oneofMember{plan: p}
			if dep := validFieldEdge(mi, fd, fg.msgs, fg.covered); dep != nil && dep.needsValid {
				mem.nested = dep
			}
			op.members = append(op.members, mem)
		}
		memberNames := map[string]bool{}
		for _, mem := range op.members {
			memberNames[mem.plan.protoName] = true
			if mem.plan.constrained() || mem.nested != nil {
				op.constrained = true
			}
		}
		for _, mem := range op.members {
			mem.accName = celtolean.LeanIdent(uniqueName(mem.plan.protoName+"_or_default", memberNames))
		}
		inner := op.baseSum
		if op.constrained {
			inner = op.validSum
		}
		if op.required {
			op.typeText = inner
		} else {
			op.typeText = "Option (" + inner + ")"
		}
		oneofs = append(oneofs, op)
	}
	// Render member refinements (all rule identifiers are collected by now).
	for _, op := range oneofs {
		for _, mem := range op.members {
			p := mem.plan
			if !p.constrained() {
				continue
			}
			p.subBinder = freshTaken("x", ruleIdents)
			props, err := fg.renderProps(p, p.subBinder)
			if err != nil {
				return err
			}
			p.props = []string{props}
		}
	}

	// Message-level rules become dependent Prop fields over the value fields.
	// Text is the field's CEL value: base-typed, value-or-default for
	// presence fields — so rules traverse one hop into message fields
	// (`this.featured.sku`) with CEL's default-instance semantics.
	thisFields := map[string]celtolean.ThisField{}
	for _, p := range fields {
		text := p.leanName
		if p.constrained() && (p.shape != shapeOption || p.unwrapped()) {
			text = p.leanName + ".val"
		}
		has := p.hasText(text)
		if p.unwrapped() {
			has = "true" // required fields are always present
		}
		value := p.celValueText()
		if p.viewName != "" {
			value = "(" + local + "." + p.viewName + " " + p.leanName + ")"
		}
		thisFields[p.protoName] = celtolean.ThisField{Text: value, Has: has}
	}
	for _, op := range oneofs {
		accessorHome := op.sumLocal
		if !op.constrained {
			accessorHome = op.baseSum
		}
		for _, mem := range op.members {
			// Presence is a case test on the sum; value access follows CEL's
			// value-or-default semantics via the generated accessor.
			caseTest := op.leanName + " matches ." + mem.plan.leanName + " _"
			text := op.leanName + "." + mem.accName
			if !op.required {
				caseTest = op.leanName + ".any (· matches ." + mem.plan.leanName + " _)"
				text = "(" + accessorHome + "." + mem.accName + " " + op.leanName + ")"
			}
			thisFields[mem.plan.protoName] = celtolean.ThisField{Text: text, Has: caseTest}
		}
	}
	var props []*propPlan
	for i, r := range mi.msgRules {
		attrs, err := pathAttrsForMessage(m.Desc, r.GetExpression())
		if err != nil {
			return fmt.Errorf("message rule %q: %w", r.GetId(), err)
		}
		res, err := fg.translate(r.GetExpression(), celtolean.Options{ThisFields: thisFields, PathAttrs: attrs})
		if err != nil {
			return fmt.Errorf("message rule %q: %w", r.GetId(), err)
		}
		props = append(props, &propPlan{
			name: uniqueName(sanitizeRuleID(r.GetId(), i), taken),
			text: res.Lean,
			rule: r,
		})
	}

	// validate-scope binders, dodging fields, props, and every rule ident.
	// h0…/h_z are the fixed inner-chain hypothesis names; reserve them so the
	// generated conjunct hypotheses can never collide.
	binderTaken := map[string]bool{}
	for k := range taken {
		binderTaken[k] = true
	}
	for k := range ruleIdents {
		binderTaken[k] = true
	}
	for i := 0; i < 64; i++ {
		binderTaken[fmt.Sprintf("h%d", i)] = true
	}
	binderTaken["h_z"] = true
	bName := uniqueName("b", binderTaken)
	for _, pr := range props {
		pr.hyp = uniqueName("h_"+pr.name, binderTaken)
	}
	hName := uniqueName("h", binderTaken)
	hcName := uniqueName("hc", binderTaken)
	hhName := uniqueName("hh", binderTaken)
	hqName := uniqueName("hq", binderTaken)
	vName := uniqueName("v", binderTaken)

	// ---- ValidPred conjunct planning ----------------------------------------
	// Conjunct names live in the ValidPred structure's namespace: field names
	// are reused verbatim, presence/element conjuncts get suffixed names.
	predTaken := map[string]bool{}
	for _, p := range fields {
		predTaken[p.leanName] = true
	}
	for _, op := range oneofs {
		predTaken[op.leanName] = true
	}
	for _, pr := range props {
		predTaken[pr.name] = true
	}
	conjOrder := []string{} // ValidPred field order
	bindOf := map[string]string{}
	addConj := func(name string) string {
		conjOrder = append(conjOrder, name)
		bindOf[name] = uniqueName("h_"+name, binderTaken)
		return name
	}
	for _, p := range fields {
		if p.subBinder == "" && (p.nested != nil || p.shape == shapeOption) {
			p.predBinder = freshTaken("x", union(binderTaken, ruleIdents))
		} else {
			p.predBinder = p.subBinder
		}
		switch {
		case p.constrained() && p.shape != shapeOption:
			if p.nested != nil && p.shape == shapeList {
				p.elemsConj = addConj(celtolean.LeanIdent(uniqueName(p.protoName+"_elems", predTaken)))
			}
			p.mainConj = addConj(p.leanName)
		case p.shape == shapeOption && (p.constrained() || p.required):
			if p.required {
				p.presenceConj = addConj(celtolean.LeanIdent(uniqueName(p.protoName+"_present", predTaken)))
			}
			if p.constrained() || p.nested != nil {
				p.mainConj = addConj(p.leanName)
			}
		case p.nested != nil:
			p.mainConj = addConj(p.leanName)
		}
	}
	for _, op := range oneofs {
		op.predBinder = freshTaken("x", union(binderTaken, ruleIdents))
		if op.required {
			op.presenceConj = addConj(celtolean.LeanIdent(uniqueName(op.protoName+"_present", predTaken)))
		}
		if op.constrained {
			op.mainConj = addConj(op.leanName)
		}
	}
	for _, pr := range props {
		conjOrder = append(conjOrder, pr.name)
		bindOf[pr.name] = pr.hyp
	}
	if len(conjOrder) == 0 {
		return fmt.Errorf("internal: message needs a validated variant but has no rule conjuncts")
	}

	predRef := func(n string) string { return n }
	ofRef := func(n string) string { return hName + "." + n }
	checkRef := func(n string) string { return bindOf[n] }

	// Per-field ofPred construction and CEL views over the constructed value.
	fieldAccess := func(p *fieldPlan) string { return bName + "." + p.leanName }
	fieldConstr := func(p *fieldPlan, ref refFn) string {
		access := fieldAccess(p)
		vq := ""
		if p.nested != nil {
			vq = validQualified(p.nested.msg)
		}
		switch {
		case p.constrained() && p.shape != shapeOption:
			if p.nested != nil && p.shape == shapeList {
				return "⟨" + runtimeNS + ".mapArray " + access + " " + vq + ".ofPred " + ref(p.elemsConj) + ", " + ref(p.mainConj) + "⟩"
			}
			return "⟨" + access + ", " + ref(p.mainConj) + "⟩"
		case p.unwrapped():
			switch {
			case p.constrained():
				return runtimeNS + ".subtypeRequired " + access + " " + ref(p.presenceConj) + " " + ref(p.mainConj)
			case p.nested != nil:
				return runtimeNS + ".mapRequired " + access + " " + vq + ".ofPred " + ref(p.presenceConj) + " " + ref(p.mainConj)
			default:
				return runtimeNS + ".getSome " + access + " " + ref(p.presenceConj)
			}
		case p.shape == shapeOption && p.constrained():
			return runtimeNS + ".subtypeOption " + access + " " + ref(p.mainConj)
		case p.shape == shapeOption && p.nested != nil:
			return runtimeNS + ".mapOption " + access + " " + vq + ".ofPred " + ref(p.mainConj)
		case p.shape == shapeList && p.nested != nil:
			return runtimeNS + ".mapArray " + access + " " + vq + ".ofPred " + ref(p.mainConj)
		default:
			return access
		}
	}
	oneofAccess := func(op *oneofPlan) string { return bName + "." + op.leanName }
	oneofConstr := func(op *oneofPlan, ref refFn) string {
		access := oneofAccess(op)
		switch {
		case op.required && op.constrained:
			return runtimeNS + ".mapRequired " + access + " " + op.validSum + ".ofPred " + ref(op.presenceConj) + " " + ref(op.mainConj)
		case op.required:
			return runtimeNS + ".getSome " + access + " " + ref(op.presenceConj)
		case op.constrained:
			return runtimeNS + ".mapOption " + access + " " + op.validSum + ".ofPred " + ref(op.mainConj)
		default:
			return access
		}
	}

	// predThisFields phrases the message rules' CEL views over the base value
	// and the constructed validated fields — exactly the values the structure's
	// Prop fields see after `ofPred`, so the proofs transfer verbatim.
	predThisFields := func(ref refFn) map[string]celtolean.ThisField {
		out := map[string]celtolean.ThisField{}
		for _, p := range fields {
			access := fieldAccess(p)
			vq := ""
			if p.nested != nil {
				vq = validQualified(p.nested.msg)
			}
			var value, has string
			switch {
			case p.unwrapped():
				has = "true"
				switch {
				case p.constrained():
					value = "(" + fieldConstr(p, ref) + ").val"
				case p.nested != nil:
					value = "(" + fieldConstr(p, ref) + ").toBase"
				default:
					value = "(" + fieldConstr(p, ref) + ")"
				}
			case p.shape == shapeOption:
				if p.viewName != "" {
					value = "(" + local + "." + p.viewName + " (" + fieldConstr(p, ref) + "))"
					has = "(" + fieldConstr(p, ref) + ").isSome"
				} else {
					value = "(" + access + ".getD " + p.defaultText() + ")"
					has = access + ".isSome"
				}
			case p.shape == shapeList && p.nested != nil:
				// The refined array's `.val` reduces away on the literal
				// construction, so the view maps `toBase` over the mapped
				// elements directly (defeq to the structure's Prop text).
				mapped := "(" + runtimeNS + ".mapArray " + access + " " + vq + ".ofPred "
				if p.constrained() {
					mapped += ref(p.elemsConj) + ")"
				} else {
					mapped += ref(p.mainConj) + ")"
				}
				value = "(" + mapped + ".map " + vq + ".toBase)"
				has = "!" + value + ".isEmpty"
			default:
				// Plain shapes: refinements over the base value project away
				// definitionally, so the base access is the CEL value.
				value = access
				has = p.hasText(value)
			}
			out[p.protoName] = celtolean.ThisField{Text: value, Has: has}
		}
		for _, op := range oneofs {
			accessorHome := op.sumLocal
			if !op.constrained {
				accessorHome = op.baseSum
			}
			oc := oneofConstr(op, ref)
			if oc != oneofAccess(op) {
				oc = "(" + oc + ")"
			}
			for _, mem := range op.members {
				caseTest := oc + " matches ." + mem.plan.leanName + " _"
				text := oc + "." + mem.accName
				if !op.required {
					caseTest = oc + ".any (· matches ." + mem.plan.leanName + " _)"
					text = "(" + accessorHome + "." + mem.accName + " " + oc + ")"
				}
				out[mem.plan.protoName] = celtolean.ThisField{Text: text, Has: caseTest}
			}
		}
		return out
	}
	for _, pr := range props {
		attrs, err := pathAttrsForMessage(m.Desc, pr.rule.GetExpression())
		if err != nil {
			return fmt.Errorf("message rule %q: %w", pr.rule.GetId(), err)
		}
		res, err := fg.translate(pr.rule.GetExpression(), celtolean.Options{ThisFields: predThisFields(predRef), PathAttrs: attrs})
		if err != nil {
			return fmt.Errorf("message rule %q: %w", pr.rule.GetId(), err)
		}
		pr.predText = res.Lean
		res, err = fg.translate(pr.rule.GetExpression(), celtolean.Options{ThisFields: predThisFields(checkRef), PathAttrs: attrs})
		if err != nil {
			return fmt.Errorf("message rule %q: %w", pr.rule.GetId(), err)
		}
		pr.checkText = res.Lean
	}

	// Conjunct Prop texts (rendered per reference context).
	presenceType := func(access string) string { return access + ".isSome" }
	fieldMainType := func(p *fieldPlan, ref refFn) (string, error) {
		access := fieldAccess(p)
		switch {
		case p.constrained() && p.shape != shapeOption:
			subject := access
			if p.nested != nil && p.shape == shapeList {
				subject = "(" + runtimeNS + ".mapArray " + access + " " + validQualified(p.nested.msg) + ".ofPred " + ref(p.elemsConj) + ")"
			}
			return fg.renderProps(p, subject)
		case p.shape == shapeOption && p.constrained():
			propsText, err := fg.renderProps(p, p.predBinder)
			if err != nil {
				return "", err
			}
			return "∀ " + p.predBinder + ", " + access + " = some " + p.predBinder + " → (" + propsText + ")", nil
		case p.shape == shapeOption && p.nested != nil:
			return "∀ " + p.predBinder + ", " + access + " = some " + p.predBinder + " → " +
				validQualified(p.nested.msg) + ".ValidPred " + p.predBinder, nil
		case p.shape == shapeList && p.nested != nil:
			return "∀ " + p.predBinder + " ∈ " + access + ", " + validQualified(p.nested.msg) + ".ValidPred " + p.predBinder, nil
		}
		return "", fmt.Errorf("field %s: no main conjunct", p.protoName)
	}
	elemsTypeText := func(p *fieldPlan) string {
		return "∀ " + p.predBinder + " ∈ " + fieldAccess(p) + ", " + validQualified(p.nested.msg) + ".ValidPred " + p.predBinder
	}
	oneofMainType := func(op *oneofPlan) string {
		return "∀ " + op.predBinder + ", " + oneofAccess(op) + " = some " + op.predBinder + " → " +
			op.validSum + ".ValidPred " + op.predBinder
	}

	// ---- validated oneof sums ------------------------------------------------
	for _, op := range oneofs {
		if !op.constrained {
			continue
		}
		if err := fg.emitOneofSum(w, m, op, ruleIdents); err != nil {
			return err
		}
	}
	// Value-or-default accessors (CEL member access semantics) for every real
	// oneof: on the validated sum for constrained oneofs, extending the base
	// sum's namespace otherwise.
	for _, op := range oneofs {
		emitOneofAccessors(w, op)
	}

	// CEL view functions for Option-shaped refined/validated fields: the
	// base-typed value when set, the zero value otherwise. Message rules
	// select through these (plain Option fields inline `getD` directly, and
	// deeper hops use the base codegen's `<field>D` getters).
	for _, p := range fields {
		if p.viewName == "" {
			continue
		}
		body := "(" + p.leanName + ".map Subtype.val).getD " + p.defaultText()
		if !p.constrained() {
			body = "(" + p.leanName + ".map " + validQualified(p.nested.msg) + ".toBase).getD default"
		}
		fmt.Fprintf(w, "/-- CEL value view for `%s`: the base-typed value when set, its zero value otherwise. -/\n",
			p.protoName)
		fmt.Fprintf(w, "def %s.%s (%s : %s) : %s :=\n  %s\n\n",
			local, p.viewName, p.leanName, p.typeText, p.thisType, body)
	}

	// ---- ValidPred -----------------------------------------------------------
	ruleDocs := func(p *fieldPlan) string {
		docs := make([]string, 0, len(p.rules))
		for _, r := range p.rules {
			d := r.id
			if r.cel != "" {
				d = fmt.Sprintf("`%s` (%s)", docText(r.cel), docText(r.id))
			}
			docs = append(docs, d)
		}
		return strings.Join(docs, "; ")
	}
	fmt.Fprintf(w, "/-- Declarative validity of a base `%s`: one Prop per protovalidate rule\n", string(m.Desc.FullName()))
	fmt.Fprintf(w, "conjunct, over the base value. `validate` succeeds exactly on values satisfying it\n")
	fmt.Fprintf(w, "(`validate_sound`/`validate_complete`). -/\n")
	fmt.Fprintf(w, "structure %s.ValidPred (%s : %s) : Prop where\n", local, bName, base)
	for _, p := range fields {
		if p.elemsConj != "" {
			fmt.Fprintf(w, "  /-- every element satisfies `%s.ValidPred` -/\n", validQualified(p.nested.msg))
			fmt.Fprintf(w, "  %s : %s\n", p.elemsConj, elemsTypeText(p))
		}
		if p.presenceConj != "" {
			fmt.Fprintf(w, "  /-- required -/\n")
			fmt.Fprintf(w, "  %s : %s\n", p.presenceConj, presenceType(fieldAccess(p)))
		}
		if p.mainConj != "" {
			if p.constrained() {
				fmt.Fprintf(w, "  /-- %s -/\n", ruleDocs(p))
			} else {
				fmt.Fprintf(w, "  /-- `%s.ValidPred` for the embedded message -/\n", validQualified(p.nested.msg))
			}
			t, err := fieldMainType(p, predRef)
			if err != nil {
				return err
			}
			fmt.Fprintf(w, "  %s : %s\n", p.mainConj, t)
		}
	}
	for _, op := range oneofs {
		if op.presenceConj != "" {
			fmt.Fprintf(w, "  /-- required: exactly one case must be set -/\n")
			fmt.Fprintf(w, "  %s : %s\n", op.presenceConj, presenceType(oneofAccess(op)))
		}
		if op.mainConj != "" {
			fmt.Fprintf(w, "  /-- the active case satisfies `%s.ValidPred` -/\n", op.validSum)
			fmt.Fprintf(w, "  %s : %s\n", op.mainConj, oneofMainType(op))
		}
	}
	for _, pr := range props {
		fmt.Fprintf(w, "  /-- CEL: `%s` (%s) -/\n", docText(pr.rule.GetExpression()), docText(pr.rule.GetId()))
		fmt.Fprintf(w, "  %s : %s\n", pr.name, pr.predText)
	}
	w.WriteString("\n")

	// ---- structure ----------------------------------------------------------
	fmt.Fprintf(w, "/-- Validated `%s`: refinement of `%s` by its protovalidate rules. -/\n",
		m.Desc.FullName(), string(m.Desc.FullName()))
	fmt.Fprintf(w, "structure %s where\n", local)
	for _, p := range fields {
		if len(p.rules) > 0 || p.required {
			docs := make([]string, 0, len(p.rules)+1)
			if p.unwrapped() {
				docs = append(docs, "required")
			}
			if d := ruleDocs(p); d != "" {
				docs = append(docs, d)
			}
			fmt.Fprintf(w, "  /-- %s -/\n", strings.Join(docs, "; "))
		}
		fmt.Fprintf(w, "  %s : %s\n", p.leanName, p.typeText)
	}
	for _, op := range oneofs {
		if op.required {
			fmt.Fprintf(w, "  /-- required: exactly one case must be set -/\n")
		}
		fmt.Fprintf(w, "  %s : %s\n", op.leanName, op.typeText)
	}
	for _, pr := range props {
		fmt.Fprintf(w, "  /-- CEL: `%s` (%s) -/\n", docText(pr.rule.GetExpression()), docText(pr.rule.GetId()))
		fmt.Fprintf(w, "  %s : %s\n", pr.name, pr.text)
	}
	w.WriteString("\n")

	// ---- checkPred -----------------------------------------------------------
	fmt.Fprintf(w, "/-- Decide `ValidPred` wholesale: a proof of every rule, or a refutation with\n")
	fmt.Fprintf(w, "the first violation in protovalidate rule order. -/\n")
	fmt.Fprintf(w, "def %s.checkPred (%s : %s) : %s.Decision (%s.ValidPred %s) :=\n",
		local, bName, base, runtimeNS, local, bName)
	stepHead := func(qText string) string {
		return "  " + runtimeNS + ".Decision.step (q := " + qText + ")"
	}
	stepFoot := func(w *strings.Builder, conjNames []string) {
		projs := make([]string, 0, len(conjNames))
		binds := make([]string, 0, len(conjNames))
		for _, n := range conjNames {
			projs = append(projs, hhName+"."+n)
			binds = append(binds, bindOf[n])
		}
		proj := projs[0]
		bind := binds[0]
		if len(conjNames) > 1 {
			proj = "⟨" + strings.Join(projs, ", ") + "⟩"
			bind = "⟨" + strings.Join(binds, ", ") + "⟩"
		}
		fmt.Fprintf(w, "    (fun %s => %s) fun %s =>\n", hhName, proj, bind)
	}
	for _, p := range fields {
		access := fieldAccess(p)
		vq := ""
		if p.nested != nil {
			vq = validQualified(p.nested.msg)
		}
		switch {
		case p.constrained() && p.shape != shapeOption:
			if p.elemsConj != "" {
				w.WriteString(stepHead(elemsTypeText(p)) + "\n")
				fmt.Fprintf(w, "    (%s.checkArray %s.checkPred %s)\n", runtimeNS, vq, access)
				stepFoot(w, []string{p.elemsConj})
			}
			qText, err := fieldMainType(p, checkRef)
			if err != nil {
				return err
			}
			w.WriteString(stepHead(qText) + "\n")
			subject := access
			if p.elemsConj != "" {
				subject = "(" + runtimeNS + ".mapArray " + access + " " + vq + ".ofPred " + checkRef(p.elemsConj) + ")"
			}
			okOf := func(proof string) string { return ".ok " + wrapProof(proof) }
			conjOf := func(hc string) string { return hc }
			w.WriteString("    (")
			chain := &strings.Builder{}
			if err := fg.decisionChain(chain, "", p, subject, p.protoName, okOf, conjOf, hcName); err != nil {
				return err
			}
			w.WriteString(indentBlock(chain.String(), "     ") + ")\n")
			stepFoot(w, []string{p.mainConj})
		case p.shape == shapeOption && (p.constrained() || p.required):
			conjNames := []string{}
			if p.presenceConj != "" {
				conjNames = append(conjNames, p.presenceConj)
			}
			if p.mainConj != "" {
				conjNames = append(conjNames, p.mainConj)
			}
			pair := len(conjNames) == 2
			qParts := []string{}
			if p.presenceConj != "" {
				qParts = append(qParts, presenceType(access))
			}
			if p.mainConj != "" {
				t, err := fieldMainType(p, checkRef)
				if err != nil {
					return err
				}
				if pair {
					t = "(" + t + ")"
				}
				qParts = append(qParts, t)
			}
			w.WriteString(stepHead(strings.Join(qParts, " ∧ ")) + "\n")
			fmt.Fprintf(w, "    (match %s with\n", access)
			if p.required {
				neg := runtimeNS + ".not_isSome_none " + hcName
				if pair {
					neg = runtimeNS + ".not_isSome_none " + hcName + ".1"
				}
				fmt.Fprintf(w, "     | none => .fail (fun %s => %s) %s\n",
					hcName, neg, violationLit(p.protoName, "required", "value is required"))
			} else {
				fmt.Fprintf(w, "     | none => .ok %s.someHolds_none\n", runtimeNS)
			}
			switch {
			case p.constrained():
				fmt.Fprintf(w, "     | some %s =>\n", p.predBinder)
				okOf := func(proof string) string {
					if pair {
						return ".ok ⟨rfl, " + runtimeNS + ".someHolds_self " + wrapProof(proof) + "⟩"
					}
					return ".ok (" + runtimeNS + ".someHolds_self " + wrapProof(proof) + ")"
				}
				conjOf := func(hc string) string {
					if pair {
						return "(" + hc + ".2 " + p.predBinder + " rfl)"
					}
					return "(" + hc + " " + p.predBinder + " rfl)"
				}
				chain := &strings.Builder{}
				if err := fg.decisionChain(chain, "       ", p, p.predBinder, p.protoName, okOf, conjOf, hcName); err != nil {
					return err
				}
				w.WriteString(strings.TrimRight(chain.String(), "\n") + ")\n")
			case p.nested != nil:
				if pair {
					fmt.Fprintf(w, "     | some %s => (%s.checkPred %s).imp\n", p.predBinder, vq, p.predBinder)
					fmt.Fprintf(w, "         (fun %s => ⟨rfl, %s.someHolds_self %s⟩) (fun %s => %s.2 %s rfl))\n",
						vName, runtimeNS, vName, hqName, hqName, p.predBinder)
				} else {
					fmt.Fprintf(w, "     | some %s => (%s.checkPred %s).imp %s.someHolds_self (fun %s => %s %s rfl))\n",
						p.predBinder, vq, p.predBinder, runtimeNS, hqName, hqName, p.predBinder)
				}
			default: // required, no rules, plain payload
				fmt.Fprintf(w, "     | some _ => .ok rfl)\n")
			}
			stepFoot(w, conjNames)
		case p.shape == shapeOption && p.nested != nil:
			t, err := fieldMainType(p, checkRef)
			if err != nil {
				return err
			}
			w.WriteString(stepHead(t) + "\n")
			fmt.Fprintf(w, "    (match %s with\n", access)
			fmt.Fprintf(w, "     | none => .ok %s.someHolds_none\n", runtimeNS)
			fmt.Fprintf(w, "     | some %s => (%s.checkPred %s).imp %s.someHolds_self (fun %s => %s %s rfl))\n",
				p.predBinder, vq, p.predBinder, runtimeNS, hqName, hqName, p.predBinder)
			stepFoot(w, []string{p.mainConj})
		case p.shape == shapeList && p.nested != nil:
			t, err := fieldMainType(p, checkRef)
			if err != nil {
				return err
			}
			w.WriteString(stepHead(t) + "\n")
			fmt.Fprintf(w, "    (%s.checkArray %s.checkPred %s)\n", runtimeNS, vq, access)
			stepFoot(w, []string{p.mainConj})
		}
	}
	for _, op := range oneofs {
		access := oneofAccess(op)
		switch {
		case op.required && op.constrained:
			w.WriteString(stepHead(presenceType(access)+" ∧ ("+oneofMainType(op)+")") + "\n")
			fmt.Fprintf(w, "    (match %s with\n", access)
			fmt.Fprintf(w, "     | none => .fail (fun %s => %s.not_isSome_none %s.1) %s\n",
				hcName, runtimeNS, hcName,
				violationLit(op.protoName, "required", "exactly one field of oneof "+op.protoName+" must be set"))
			fmt.Fprintf(w, "     | some %s => (%s.checkPred %s).imp\n", op.predBinder, op.validSum, op.predBinder)
			fmt.Fprintf(w, "         (fun %s => ⟨rfl, %s.someHolds_self %s⟩) (fun %s => %s.2 %s rfl))\n",
				vName, runtimeNS, vName, hqName, hqName, op.predBinder)
			stepFoot(w, []string{op.presenceConj, op.mainConj})
		case op.required:
			w.WriteString(stepHead(presenceType(access)) + "\n")
			fmt.Fprintf(w, "    (match %s with\n", access)
			fmt.Fprintf(w, "     | none => .fail (fun %s => %s.not_isSome_none %s) %s\n",
				hcName, runtimeNS, hcName,
				violationLit(op.protoName, "required", "exactly one field of oneof "+op.protoName+" must be set"))
			fmt.Fprintf(w, "     | some _ => .ok rfl)\n")
			stepFoot(w, []string{op.presenceConj})
		case op.constrained:
			w.WriteString(stepHead(oneofMainType(op)) + "\n")
			fmt.Fprintf(w, "    (match %s with\n", access)
			fmt.Fprintf(w, "     | none => .ok %s.someHolds_none\n", runtimeNS)
			fmt.Fprintf(w, "     | some %s => (%s.checkPred %s).imp %s.someHolds_self (fun %s => %s %s rfl))\n",
				op.predBinder, op.validSum, op.predBinder, runtimeNS, hqName, hqName, op.predBinder)
			stepFoot(w, []string{op.mainConj})
		}
	}
	// Message rules, then the assembled proof.
	finalProof := make([]string, 0, len(conjOrder))
	for _, n := range conjOrder {
		finalProof = append(finalProof, bindOf[n])
	}
	// ValidPred is a structure: the anonymous constructor is required even for
	// a single conjunct (a bare proof term would not coerce).
	finalOk := ".ok ⟨" + strings.Join(finalProof, ", ") + "⟩"
	var propConds, propHyps, propErrs []string
	for _, pr := range props {
		propConds = append(propConds, pr.checkText)
		propHyps = append(propHyps, pr.hyp)
		msg := pr.rule.GetMessage()
		if msg == "" {
			msg = pr.rule.GetExpression()
		}
		propErrs = append(propErrs,
			".fail (fun "+hhName+" => "+pr.hyp+" "+hhName+"."+pr.name+") "+violationLit("", pr.rule.GetId(), msg))
	}
	iteChain(w, "  ", propHyps, propConds, finalOk, propErrs)
	w.WriteString("\n")

	// ---- ofPred --------------------------------------------------------------
	fmt.Fprintf(w, "/-- Construct the validated structure from a `ValidPred` proof. -/\n")
	fmt.Fprintf(w, "def %s.ofPred (%s : %s) (%s : %s.ValidPred %s) : %s :=\n",
		local, bName, base, hName, local, bName, local)
	var assigns []string
	for _, p := range fields {
		assigns = append(assigns, p.leanName+" := "+fieldConstr(p, ofRef))
	}
	for _, op := range oneofs {
		assigns = append(assigns, op.leanName+" := "+oneofConstr(op, ofRef))
	}
	for _, pr := range props {
		assigns = append(assigns, pr.name+" := "+ofRef(pr.name))
	}
	w.WriteString("  { " + strings.Join(assigns, ",\n    ") + " }\n\n")

	// ---- validate / Decidable / theorems ------------------------------------
	fmt.Fprintf(w, "/-- Decide every protovalidate rule on a `%s`, producing the validated refinement or the first violation. -/\n",
		string(m.Desc.FullName()))
	fmt.Fprintf(w, "def %s.validate (%s : %s) : Except %s.Violation %s :=\n",
		local, bName, base, runtimeNS, local)
	fmt.Fprintf(w, "  (%s.checkPred %s).toExcept (%s.ofPred %s)\n\n", local, bName, local, bName)

	fmt.Fprintf(w, "instance %s.instDecidableValidPred : (%s : %s) → Decidable (%s.ValidPred %s) :=\n",
		local, bName, base, local, bName)
	fmt.Fprintf(w, "  fun %s => (%s.checkPred %s).toDecidable\n\n", bName, local, bName)

	fmt.Fprintf(w, "/-- Soundness: a successful `validate` certifies `ValidPred` on the *input* base value. -/\n")
	fmt.Fprintf(w, "theorem %s.validate_sound {%s : %s} {%s : %s}\n", local, bName, base, vName, local)
	fmt.Fprintf(w, "    (%s : %s.validate %s = Except.ok %s) : %s.ValidPred %s :=\n",
		hName, local, bName, vName, local, bName)
	fmt.Fprintf(w, "  %s.Decision.pred_of_toExcept_ok %s\n\n", runtimeNS, hName)

	fmt.Fprintf(w, "/-- Completeness: `ValidPred` guarantees `validate` succeeds. -/\n")
	fmt.Fprintf(w, "theorem %s.validate_complete {%s : %s} (%s : %s.ValidPred %s) :\n",
		local, bName, base, hName, local, bName)
	fmt.Fprintf(w, "    (%s.validate %s).isOk :=\n", local, bName)
	fmt.Fprintf(w, "  %s.Decision.toExcept_isOk %s\n\n", runtimeNS, hName)

	// ---- toBase ---------------------------------------------------------------
	fmt.Fprintf(w, "/-- Forget the refinements (any unknown fields are dropped). -/\n")
	fmt.Fprintf(w, "def %s.toBase (v : %s) : %s :=\n", local, local, base)
	var backs []string
	for _, p := range fields {
		expr := "v." + p.leanName
		switch {
		case p.unwrapped():
			switch {
			case p.constrained():
				expr = "some " + expr + ".val"
			case p.nested != nil:
				expr = "some " + expr + ".toBase"
			default:
				expr = "some " + expr
			}
		case p.constrained() && p.shape != shapeOption:
			expr += ".val"
			if p.nested != nil {
				expr += ".map (·.toBase)"
			}
		case p.constrained():
			expr += ".map (·.val)"
		case p.nested != nil:
			expr += ".map (·.toBase)"
		}
		backs = append(backs, p.leanName+" := "+expr)
	}
	for _, op := range oneofs {
		expr := "v." + op.leanName
		switch {
		case op.required && op.constrained:
			expr = "some " + expr + ".toBase"
		case op.required:
			expr = "some " + expr
		case op.constrained:
			expr += ".map (·.toBase)"
		}
		backs = append(backs, op.leanName+" := "+expr)
	}
	if len(backs) == 0 {
		w.WriteString("  {}\n\n")
	} else {
		w.WriteString("  { " + strings.Join(backs, ",\n    ") + " }\n\n")
	}

	// ---- decodeValid ------------------------------------------------------------
	fmt.Fprintf(w, "/-- Decode the wire format and validate in one step. -/\n")
	fmt.Fprintf(w, "def %s.decodeValid (bytes : ByteArray) : Except String %s :=\n", local, local)
	fmt.Fprintf(w, "  %s.decodeThenValidate %s.decode %s.validate bytes\n\n", runtimeNS, base, local)

	fmt.Fprintf(w, "/-- Soundness of decode-then-validate: success factors through a successful\n")
	fmt.Fprintf(w, "decode and a successful validate. -/\n")
	fmt.Fprintf(w, "theorem %s.decodeValid_sound {bytes : ByteArray} {%s : %s}\n", local, vName, local)
	fmt.Fprintf(w, "    (%s : %s.decodeValid bytes = Except.ok %s) :\n", hName, local, vName)
	fmt.Fprintf(w, "    ∃ %s, %s.decode bytes = Except.ok %s ∧ %s.validate %s = Except.ok %s :=\n",
		bName, base, bName, local, bName, vName)
	fmt.Fprintf(w, "  %s.decodeThenValidate_sound %s\n\n", runtimeNS, hName)
	return nil
}

// wrapProof parenthesizes a proof term used in application position.
func wrapProof(proof string) string {
	if strings.ContainsRune(proof, ' ') && !strings.HasPrefix(proof, "⟨") && !strings.HasPrefix(proof, "(") {
		return "(" + proof + ")"
	}
	return proof
}

// indentBlock re-indents a rendered block, keeping its first line unindented
// (for insertion after an opening parenthesis).
func indentBlock(block, indent string) string {
	lines := strings.Split(strings.TrimRight(block, "\n"), "\n")
	for i := 1; i < len(lines); i++ {
		if lines[i] != "" {
			lines[i] = indent + lines[i]
		}
	}
	return strings.Join(lines, "\n")
}

// emitOneofSum generates the validated sum type for a constrained oneof: an
// inductive whose constructors carry refined payloads, with case-wise
// ValidPred/checkPred/ofPred/validate/toBase and the soundness/completeness
// theorems.
func (fg *fileGen) emitOneofSum(w *strings.Builder, m *protogen.Message, op *oneofPlan, ruleIdents map[string]bool) error {
	fmt.Fprintf(w, "/-- Validated `%s.%s`: the oneof sum with refined constructor payloads. -/\n",
		m.Desc.FullName(), op.protoName)
	fmt.Fprintf(w, "inductive %s where\n", op.sumLocal)
	for _, mem := range op.members {
		p := mem.plan
		if len(p.rules) > 0 {
			docs := make([]string, 0, len(p.rules))
			for _, r := range p.rules {
				d := r.id
				if r.cel != "" {
					d = fmt.Sprintf("`%s` (%s)", docText(r.cel), docText(r.id))
				}
				docs = append(docs, d)
			}
			fmt.Fprintf(w, "  /-- %s -/\n", strings.Join(docs, "; "))
		}
		fmt.Fprintf(w, "  | %s : %s → %s\n", p.leanName, mem.ctorType(), op.sumLocal)
	}
	w.WriteString("\n")

	taken := map[string]bool{}
	for k := range ruleIdents {
		taken[k] = true
	}
	for i := 0; i < 64; i++ {
		taken[fmt.Sprintf("h%d", i)] = true
	}
	taken["h_z"] = true
	bName := uniqueName("b", taken)
	hName := uniqueName("h", taken)
	hcName := uniqueName("hc", taken)
	vName := uniqueName("v", taken)

	// ---- ValidPred -----------------------------------------------------------
	fmt.Fprintf(w, "/-- Declarative validity of the active `%s.%s` case. -/\n", m.Desc.FullName(), op.protoName)
	fmt.Fprintf(w, "def %s.ValidPred : %s → Prop\n", op.sumLocal, op.baseSum)
	for _, mem := range op.members {
		p := mem.plan
		switch {
		case p.constrained():
			fmt.Fprintf(w, "  | .%s %s => %s\n", p.leanName, p.subBinder, p.props[0])
		case mem.nested != nil:
			binder := freshTaken("x", ruleIdents)
			fmt.Fprintf(w, "  | .%s %s => %s.ValidPred %s\n", p.leanName, binder, validQualified(mem.nested.msg), binder)
		default:
			fmt.Fprintf(w, "  | .%s _ => True\n", p.leanName)
		}
	}
	w.WriteString("\n")

	// ---- checkPred -----------------------------------------------------------
	fmt.Fprintf(w, "/-- Decide the member rules for the active case. -/\n")
	fmt.Fprintf(w, "def %s.checkPred : (%s : %s) → %s.Decision (%s.ValidPred %s)\n",
		op.sumLocal, bName, op.baseSum, runtimeNS, op.sumLocal, bName)
	for _, mem := range op.members {
		p := mem.plan
		switch {
		case p.constrained():
			binder := p.subBinder
			fmt.Fprintf(w, "  | .%s %s =>\n", p.leanName, binder)
			okOf := func(proof string) string { return ".ok " + wrapProof(proof) }
			conjOf := func(hc string) string { return hc }
			if err := fg.decisionChain(w, "    ", p, binder, p.protoName, okOf, conjOf, hcName); err != nil {
				return fmt.Errorf("oneof %s: %w", op.protoName, err)
			}
		case mem.nested != nil:
			binder := freshTaken("x", ruleIdents)
			fmt.Fprintf(w, "  | .%s %s => %s.checkPred %s\n",
				p.leanName, binder, validQualified(mem.nested.msg), binder)
		default:
			fmt.Fprintf(w, "  | .%s _ => .ok True.intro\n", p.leanName)
		}
	}
	w.WriteString("\n")

	// ---- ofPred --------------------------------------------------------------
	fmt.Fprintf(w, "/-- Construct the validated sum from a `ValidPred` proof. -/\n")
	fmt.Fprintf(w, "def %s.ofPred : (%s : %s) → %s.ValidPred %s → %s\n",
		op.sumLocal, bName, op.baseSum, op.sumLocal, bName, op.sumLocal)
	for _, mem := range op.members {
		p := mem.plan
		switch {
		case p.constrained():
			fmt.Fprintf(w, "  | .%s %s, %s => .%s ⟨%s, %s⟩\n",
				p.leanName, p.subBinder, hName, p.leanName, p.subBinder, hName)
		case mem.nested != nil:
			binder := freshTaken("x", ruleIdents)
			fmt.Fprintf(w, "  | .%s %s, %s => .%s (%s.ofPred %s %s)\n",
				p.leanName, binder, hName, p.leanName, validQualified(mem.nested.msg), binder, hName)
		default:
			binder := freshTaken("x", ruleIdents)
			fmt.Fprintf(w, "  | .%s %s, _ => .%s %s\n", p.leanName, binder, p.leanName, binder)
		}
	}
	w.WriteString("\n")

	// ---- validate / Decidable / theorems ------------------------------------
	fmt.Fprintf(w, "/-- Decide the member rules for the active case, producing the validated sum or the violation. -/\n")
	fmt.Fprintf(w, "def %s.validate (%s : %s) : Except %s.Violation %s :=\n",
		op.sumLocal, bName, op.baseSum, runtimeNS, op.sumLocal)
	fmt.Fprintf(w, "  (%s.checkPred %s).toExcept (%s.ofPred %s)\n\n", op.sumLocal, bName, op.sumLocal, bName)

	fmt.Fprintf(w, "instance %s.instDecidableValidPred : (%s : %s) → Decidable (%s.ValidPred %s) :=\n",
		op.sumLocal, bName, op.baseSum, op.sumLocal, bName)
	fmt.Fprintf(w, "  fun %s => (%s.checkPred %s).toDecidable\n\n", bName, op.sumLocal, bName)

	fmt.Fprintf(w, "/-- Soundness: a successful `validate` certifies `ValidPred` on the input sum. -/\n")
	fmt.Fprintf(w, "theorem %s.validate_sound {%s : %s} {%s : %s}\n", op.sumLocal, bName, op.baseSum, vName, op.sumLocal)
	fmt.Fprintf(w, "    (%s : %s.validate %s = Except.ok %s) : %s.ValidPred %s :=\n",
		hName, op.sumLocal, bName, vName, op.sumLocal, bName)
	fmt.Fprintf(w, "  %s.Decision.pred_of_toExcept_ok %s\n\n", runtimeNS, hName)

	fmt.Fprintf(w, "/-- Completeness: `ValidPred` guarantees `validate` succeeds. -/\n")
	fmt.Fprintf(w, "theorem %s.validate_complete {%s : %s} (%s : %s.ValidPred %s) :\n",
		op.sumLocal, bName, op.baseSum, hName, op.sumLocal, bName)
	fmt.Fprintf(w, "    (%s.validate %s).isOk :=\n", op.sumLocal, bName)
	fmt.Fprintf(w, "  %s.Decision.toExcept_isOk %s\n\n", runtimeNS, hName)

	fmt.Fprintf(w, "/-- Forget the refinements. -/\n")
	fmt.Fprintf(w, "def %s.toBase (v : %s) : %s :=\n", op.sumLocal, op.sumLocal, op.baseSum)
	fmt.Fprintf(w, "  match v with\n")
	for _, mem := range op.members {
		p := mem.plan
		switch {
		case p.constrained():
			fmt.Fprintf(w, "  | .%s x => .%s x.val\n", p.leanName, p.leanName)
		case mem.nested != nil:
			fmt.Fprintf(w, "  | .%s x => .%s x.toBase\n", p.leanName, p.leanName)
		default:
			fmt.Fprintf(w, "  | .%s x => .%s x\n", p.leanName, p.leanName)
		}
	}
	w.WriteString("\n")
	return nil
}

// celValueText is the Lean expression for the field's CEL value in message
// rules: base-typed, with value-or-default semantics for presence fields
// (unset message fields read as the default instance, unset optional scalars
// as their zero value). Refinements project away (`.val`/`.toBase`) so
// selects reach base fields.
func (p *fieldPlan) celValueText() string {
	name := p.leanName
	switch p.shape {
	case shapeOption:
		if p.unwrapped() { // required: always present
			switch {
			case p.constrained():
				return name + ".val"
			case p.nested != nil:
				return name + ".toBase"
			default:
				return name
			}
		}
		switch {
		case p.constrained():
			// Explicit Subtype.val: cdot lambdas cannot infer their argument
			// type in structure-field positions.
			return "((" + name + ".map Subtype.val).getD " + p.defaultText() + ")"
		case p.nested != nil:
			return "((" + name + ".map " + validQualified(p.nested.msg) + ".toBase).getD default)"
		default:
			return "(" + name + ".getD " + p.defaultText() + ")"
		}
	case shapeList:
		base := name
		if p.constrained() {
			base = name + ".val"
		}
		if p.nested != nil {
			return "(" + base + ".map " + validQualified(p.nested.msg) + ".toBase)"
		}
		return base
	default:
		if p.constrained() {
			return name + ".val"
		}
		return name
	}
}

// defaultText is the zero value of the field's element type.
func (p *fieldPlan) defaultText() string {
	if p.f.Desc.Kind() == protoreflect.MessageKind {
		return "default"
	}
	return defaultValueText(p.f)
}

// defaultValueText is the Lean expression for a member type's protobuf zero
// value (CEL's result when accessing an inactive oneof member).
func defaultValueText(fd *protogen.Field) string {
	switch fd.Desc.Kind() {
	case protoreflect.StringKind:
		return `""`
	case protoreflect.BoolKind:
		return "false"
	case protoreflect.FloatKind, protoreflect.DoubleKind:
		return "0.0"
	case protoreflect.EnumKind:
		if fd.Enum != nil {
			if zero := fd.Enum.Desc.Values().ByNumber(0); zero != nil {
				return "." + celtolean.LeanIdent(string(zero.Name()))
			}
		}
		return "default"
	case protoreflect.BytesKind, protoreflect.MessageKind, protoreflect.GroupKind:
		return "default"
	default:
		return "0"
	}
}

// emitOneofAccessors generates one value-or-default accessor per member,
// mirroring CEL's semantics for oneof member access: the payload (as its
// *base* type) when that case is active, the member type's zero value
// otherwise. The accessor takes the field's exact shape — the bare sum for
// required oneofs (dot notation), Option-wrapped otherwise.
func emitOneofAccessors(w *strings.Builder, op *oneofPlan) {
	home := op.sumLocal
	if !op.constrained {
		home = op.baseSum
	}
	argType := home
	if !op.required {
		argType = "Option (" + home + ")"
	}
	for _, mem := range op.members {
		p := mem.plan
		result := "v"
		switch {
		case p.constrained():
			result = "v.val"
		case mem.nested != nil:
			result = "v.toBase"
		}
		pattern := "." + p.leanName + " v"
		if !op.required {
			pattern = "some (." + p.leanName + " v)"
		}
		fmt.Fprintf(w, "/-- CEL value-or-default access for `%s`: the payload when the case is active, `%s` otherwise. -/\n",
			p.protoName, defaultValueText(p.f))
		fmt.Fprintf(w, "def %s.%s : %s → %s\n", home, mem.accName, argType, p.thisType)
		fmt.Fprintf(w, "  | %s => %s\n", pattern, result)
		fmt.Fprintf(w, "  | _ => %s\n\n", defaultValueText(p.f))
	}
}

// hasText renders the Bool expression deciding CEL has(this.f) for the field,
// given the Lean text of the field's value. Explicit-presence fields test the
// Option; implicit-presence fields test non-default per CEL's proto semantics.
func (p *fieldPlan) hasText(text string) string {
	switch p.shape {
	case shapeOption:
		return p.leanName + ".isSome"
	case shapeList, shapeMap:
		return "!" + text + ".isEmpty"
	}
	switch p.f.Desc.Kind() {
	case protoreflect.StringKind:
		return "!" + text + ".isEmpty"
	case protoreflect.BytesKind:
		return text + ".size != 0"
	case protoreflect.BoolKind:
		return text
	case protoreflect.EnumKind:
		zero := p.f.Enum.Desc.Values().ByNumber(0)
		if zero == nil {
			return ""
		}
		return "!(" + text + " matches ." + celtolean.LeanIdent(string(zero.Name())) + ")"
	case protoreflect.FloatKind, protoreflect.DoubleKind:
		return text + " != 0.0"
	case protoreflect.MessageKind, protoreflect.GroupKind:
		return "" // unreachable: message fields are shapeOption
	default:
		return text + " != 0"
	}
}

func enumDesc(fd *protogen.Field) protoreflect.EnumDescriptor {
	if fd.Enum != nil {
		return fd.Enum.Desc
	}
	return nil
}

func msgDesc(fd *protogen.Field) protoreflect.MessageDescriptor {
	if fd.Message != nil {
		return fd.Message.Desc
	}
	return nil
}

func wrapType(t string) string {
	if strings.ContainsRune(t, ' ') && !strings.HasPrefix(t, "{") && !strings.HasPrefix(t, "(") {
		return "(" + t + ")"
	}
	return t
}

func freshTaken(base string, taken map[string]bool) string {
	name := base
	for i := 1; taken[name]; i++ {
		name = fmt.Sprintf("%s_%d", base, i)
	}
	return name
}

func union(a, b map[string]bool) map[string]bool {
	out := map[string]bool{}
	for k := range a {
		out[k] = true
	}
	for k := range b {
		out[k] = true
	}
	return out
}
