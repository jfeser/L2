OCAMLBUILD = ocamlbuild
FLAGS = \
	-use-ocamlfind \
	-syntax camlp4o \
	-pkg core \
	-pkg Z3 \
    -pkg bolt \
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

.PHONY: clean

all: timing.native interactive.native

%.native: *.ml
	$(OCAMLBUILD) $(FLAGS) $@

profile:
	$(OCAMLBUILD) $(FLAGS) -tag debug -tag profile timing.native

clean:
	$(OCAMLBUILD) -clean
