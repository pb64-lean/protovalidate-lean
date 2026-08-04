package leanvalidate

import (
	"strings"
	"testing"
)

// A field's rules are decided as one dependent-`if` chain whose hypotheses are
// drawn from the fixed h0…h63 pool that every other generated binder is chosen
// to dodge. A longer chain would start shadowing outer binders, so the
// generator must refuse rather than emit subtly wrong Lean.
func TestRuleChainCap(t *testing.T) {
	fg := &fileGen{notes: map[string]bool{}, regexes: map[string]bool{}}
	id := func(s string) string { return s }

	run := func(n int) error {
		rules := make([]loweredRule, n)
		for i := range rules {
			rules[i] = loweredRule{
				id:     "r",
				direct: func(*fileGen, string) (string, int, error) { return "True", precAndOperand, nil },
			}
		}
		var w strings.Builder
		return fg.decisionChain(&w, "  ", &fieldPlan{protoName: "many", rules: rules},
			"x", "many", id, id, "hc")
	}

	if err := run(maxChainRules); err != nil {
		t.Fatalf("a chain of exactly %d rules must still generate: %v", maxChainRules, err)
	}
	err := run(maxChainRules + 1)
	if err == nil {
		t.Fatalf("a chain of %d rules must be refused", maxChainRules+1)
	}
	for _, want := range []string{"field many", "65 rules", "h0…h63"} {
		if !strings.Contains(err.Error(), want) {
			t.Errorf("error %q does not mention %q", err, want)
		}
	}
}
