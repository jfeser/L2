OCAMLBUILD = ocamlbuild
OPAM = opam
FLAGS = \
	-use-ocamlfind \
	-syntax camlp4o \
	-pkg core \
	-pkg yojson \
    -pkg bolt \
	-pkg hashcons \
	-pkg faillib \
	-pkg camlp4.lib \
	-pkg sexplib.syntax,comparelib.syntax \
	-tag thread \
	-tag short_paths \
	-tag "warn(A-4-44)" \
	-tag strict_sequence \
	-tag strict_formats \
	-use-menhir \
	-j 4
DEPENDENCIES = core bolt yojson hashcons menhir ocamlfind
BUILD_DIR = _build

.PHONY: clean deps profile test release debug

all: debug

test:
	$(OCAMLBUILD) $(FLAGS) -pkg ounit tests.native

release:
	$(OCAMLBUILD) $(FLAGS) -cflags -unsafe -cflags -noassert timing.native

debug:
	$(OCAMLBUILD) $(FLAGS) -tag debug -tag bin_annot timing.native

debug-byte:
	$(OCAMLBUILD) $(FLAGS) -tag debug -tag bin_annot timing.byte

%.mli: *.ml
	$(OCAMLBUILD) $(FLAGS) $(@:.mli=.inferred.mli); mv $(BUILD_DIR)/$(@:.mli=.inferred.mli) $@

profile:
	$(OCAMLBUILD) $(FLAGS) -tag debug -tag profile timing.native

clean:
	rm -f timing.native interactive.native
	$(OCAMLBUILD) -clean

deps:
	opam install --yes $(DEPENDENCIES)
