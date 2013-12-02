#!/bin/bash
#
# Igor Konnov, 2012-2013

function check_version {
  # primitive version check to do conditional compilation
  if [ "$1" -le "3" -a "$2" -lt "11" ]; then
      # slitaz does have ocaml 3.10.2
      echo "Your ocaml ($1.$2.$3) is too old. Please upgrade it to version 3.11.0"
      exit 1
  fi
}

CFLAGS="-cflag -g -lflag -g -lflag -thread" # the last options fixes a bug

target=${1:-"./bymc.native"} # use ./bymc.byte for debugging
ocamlver=`ocaml -version | egrep -o '[0-9]+\.[0-9]+\.[0-9]+'`
check_version `echo ${ocamlver} | sed 's/\./ /g'`

case $1 in
  test)
    ocamlbuild -use-ocamlfind $CFLAGS ./unitTests.byte | ./script/ocaml-friendly;
    ./unitTests.byte
    ;;

  dist)
    ver=`date '+%Y%m%d'`
    git archive --prefix=bymc-src-${ver}/ master \
        | bzip2 > bymc-src-${ver}.tar.bz2
    ;;

  dist-bin)
    ver=`date '+%Y%m%d'`
    FILES='bymc.native cegar run-concrete script/ LICENSE'
    tar jhcf bymc-bin-${ver}.tar.bz2 $FILES
    ;;

  release)
    tag="$2"
    git archive --prefix=bymc-src-${tag}/ "$tag" \
        | bzip2 > bymc-src-${tag}.tar.bz2
    ;;

  clean)
    ocamlbuild -clean
    ;;

  *)
    ocamlbuild -use-ocamlfind $CFLAGS $target | ./script/ocaml-friendly
    find _build -regex '.*\.cm\(i\|o\)'\
        | sed 's#_build\/src\/##; s/.cm\(i\|o\)//'\
        >./bymc.mltop

    ocamlbuild -use-ocamlfind $CFLAGS ./bymc.top $target
    ;;
esac
