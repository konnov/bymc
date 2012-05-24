#!/bin/sh

DEBUG="-cflags -g"

ocamlbuild $DEBUG -lib str -lib unix ./run.native
