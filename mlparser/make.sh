#!/bin/sh

DEBUG="-cflag -g -lflag -g"

if [ "x$BYTE" = "x" ]; then
    ocamlbuild $DEBUG -lib str -lib unix ./run.native
else
    ocamlbuild $DEBUG -lib str -lib unix ./run.byte
fi
