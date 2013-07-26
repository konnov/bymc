#!/bin/sh
#
# Igor Konnov, 2012-2013

function check_version () {
  # primitive version check to do conditional compilation
  if [ "$1" -lt "3" -o "$2" -lt "11" ]; then
      # slitaz does have ocaml 3.10.2
      echo "Your ocaml is too old. Please upgrade it to version 3.11.0"
      exit 1
  fi
}

CFLAGS="-cflag -g -lflag -g"

target=${1:-"./bymc.native"} # use ./bymc.byte for debugging
ocamlver=`ocaml -version | egrep -o '[0-9]+\.[0-9]+\.[0-9]+'`
check_version `echo ${ocamlver} | sed 's/\./ /g'`

ocamlbuild $CFLAGS -Is src -lib str -lib unix $target \
    | ./script/ocaml-friendly
