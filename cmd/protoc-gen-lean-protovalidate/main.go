// protoc-gen-lean-protovalidate is a protoc plugin generating Lean 4
// refinement types from protovalidate CEL annotations, layered on top of
// grpc-lean's protoc-gen-lean4 base types.
//
// Options (comma-separated via --lean-protovalidate_opt or the _out suffix):
//
//	lean4_prefix=<Prefix>  module prefix for the generated valid modules
//	base_prefix=<Prefix>   module prefix protoc-gen-lean4 used for the same protos
//
// Example:
//
//	protoc --plugin=protoc-gen-lean-protovalidate=<bin> \
//	  --lean-protovalidate_out=out \
//	  --lean-protovalidate_opt=lean4_prefix=UserValid,base_prefix=UserLean \
//	  user.proto
package main

import (
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"strings"

	"google.golang.org/protobuf/compiler/protogen"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/pluginpb"

	"github.com/petersonbill64/protovalidate-lean/leanvalidate"
)

func main() {
	if err := run(); err != nil {
		fmt.Fprintf(os.Stderr, "protoc-gen-lean-protovalidate: %v\n", err)
		os.Exit(1)
	}
}

func run() error {
	in, err := io.ReadAll(os.Stdin)
	if err != nil {
		return err
	}
	req := &pluginpb.CodeGeneratorRequest{}
	if err := proto.Unmarshal(in, req); err != nil {
		return fmt.Errorf("unparseable CodeGeneratorRequest: %w", err)
	}

	// protogen insists on a Go import path per file; we emit Lean, so satisfy
	// the bookkeeping with a synthetic M mapping for every input file.
	params := []string{}
	if p := req.GetParameter(); p != "" {
		params = append(params, p)
	}
	for _, f := range req.GetProtoFile() {
		params = append(params, fmt.Sprintf("M%s=lean/%s", f.GetName(), strings.TrimSuffix(f.GetName(), ".proto")))
	}
	req.Parameter = proto.String(strings.Join(params, ","))

	var flags flag.FlagSet
	prefix := flags.String("lean4_prefix", "", "Lean module prefix for generated valid modules")
	basePrefix := flags.String("base_prefix", "", "Lean module prefix of the protoc-gen-lean4 base modules")
	depModulesSpec := flags.String("dep_modules", "",
		"cross-target deps as path@BasePrefix@ValidPrefix entries joined with ';'")
	gen, err := protogen.Options{ParamFunc: flags.Set}.New(req)
	if err != nil {
		return err
	}
	gen.SupportedFeatures = uint64(pluginpb.CodeGeneratorResponse_FEATURE_PROTO3_OPTIONAL)

	genErr := func() error {
		if *prefix == "" {
			return errors.New("lean4_prefix option is required (--lean-protovalidate_opt=lean4_prefix=...)")
		}
		if *basePrefix == "" {
			return errors.New("base_prefix option is required (--lean-protovalidate_opt=base_prefix=...)")
		}
		depModules := map[string]leanvalidate.DepModule{}
		if *depModulesSpec != "" {
			for _, entry := range strings.Split(*depModulesSpec, ";") {
				parts := strings.Split(entry, "@")
				if len(parts) != 3 || parts[0] == "" || parts[1] == "" || parts[2] == "" {
					return fmt.Errorf("invalid dep_modules entry %q (want path@BasePrefix@ValidPrefix)", entry)
				}
				depModules[parts[0]] = leanvalidate.DepModule{Base: parts[1], Valid: parts[2]}
			}
		}
		return leanvalidate.Generate(gen, leanvalidate.Config{
			Prefix:     *prefix,
			BasePrefix: *basePrefix,
			DepModules: depModules,
		})
	}()
	if genErr != nil {
		gen.Error(genErr)
	}
	out, err := proto.Marshal(gen.Response())
	if err != nil {
		return err
	}
	_, err = os.Stdout.Write(out)
	return err
}
