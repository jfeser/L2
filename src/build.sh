#!/bin/sh

# -cflags "-w A-4-33-40-41-42-43-34-44" \
# -classic-display \

ocamlbuild \
    -use-ocamlfind \
    -pkg core \
    -tag thread \
    -tag debug \
    -tag annot \
    -tag bin_annot \
    -tag short_paths \
    -cflags "-w A-4-44" \
    -cflags -strict-sequence \
    -j 4 \
    $@
