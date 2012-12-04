#!/bin/sh

DEBUG="-cflag -g -lflag -g"

target=${1:-"./run.native"}

ocamlbuild $DEBUG -lib str -lib unix $target
