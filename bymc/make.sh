#!/bin/sh

DEBUG="-cflag -g -lflag -g"

target=${1:-"./bymc.native"}

ocamlbuild $DEBUG -lib str -lib unix $target | ./ocaml-friendly
