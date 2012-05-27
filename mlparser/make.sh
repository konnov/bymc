#!/bin/sh

DEBUG="-cflag -g -lflag -g"

ocamlbuild $DEBUG -lib str -lib unix ./run.native
