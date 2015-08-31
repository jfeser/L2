OCAMLBUILD = ocamlbuild
OPAM = opam
FLAGS = \
	-use-ocamlfind \
	-syntax camlp4o \
	-pkg core \
	-pkg Z3 \
    -pkg bolt \
	-pkg parmap \
	-pkg yojson \
	-pkg ounit \
	-pkg hashcons \
	-pkg camlp4.lib \
	-pkg sexplib.syntax,comparelib.syntax,fieldslib.syntax,variantslib.syntax,bin_prot.syntax \
	-tag thread \
	-tag debug \
	-tag annot \
	-tag bin_annot \
	-tag short_paths \
	-cflags "-w A-4-44" \
	-cflags -strict-sequence \
	-use-menhir \
	-j 4
DEPENDENCIES = core bolt menhir ocamlfind
BUILD_DIR = _build

.PHONY: clean deps profile

all: timing.native tests.native

%.native: *.ml
	$(OCAMLBUILD) $(FLAGS) $@

%.mli: *.ml
	$(OCAMLBUILD) $(FLAGS) $(@:.mli=.inferred.mli); mv $(BUILD_DIR)/$(@:.mli=.inferred.mli) $@

profile:
	$(OCAMLBUILD) $(FLAGS) -tag debug -tag profile timing.native

clean:
	rm -f timing.native interactive.native
	$(OCAMLBUILD) -clean

deps:
	opam install $(DEPENDENCIES)
