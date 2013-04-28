#!/bin/sh

CFLAGS="-cflag -g -lflag -g"

target=${1:-"./bymc.native"} # use ./bymc.byte for debugging

ocamlbuild $CFLAGS -Is src -lib str -lib unix $target | ./script/ocaml-friendly
