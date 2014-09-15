# Makefile to build them all
#
# Igor Konnov, 2012-2014

CFLAGS=-cflag -g -lflag -g -lflag -thread # the options at the end fix a bug

target="./bymc.native" # use ./bymc.byte for debugging
debug_target="./bymc.byte"
ocamlver := $(shell ocaml -version | egrep -o '[0-9]+\.[0-9]+\.[0-9]+')
ocaml_major := $(shell echo ${ocamlver} | perl -pe 's/([0-9]+)\.[0-9]+\.[0-9]+/\1/')
ocaml_minor := $(shell echo ${ocamlver} | perl -pe 's/[0-9]+\.([0-9]+)\.[0-9]+/\1/')
ocaml_rev := $(shell echo ${ocamlver} | perl -pe 's/[0-9]+\.[0-9]+\.([0-9]+)/\1/')
dist_ver := $(shell date '+%Y%m%d')

DIST_FILES=bymc.native verifyco-spin verifypa-spin script/ LICENSE

all: ${target}

compile: ${target}

debug: ${debug_target}

test: clean
	ocamlbuild -use-ocamlfind ${CFLAGS} ./unitTests.byte | ./script/ocaml-friendly
	./unitTests.byte

integrate: clean
	./test/func-test.sh

dist:

	git archive --prefix=bymc-src-${ver}/ master \
        | bzip2 > bymc-src-${ver}.tar.bz2

dist-bin: compile
	tar jhcf bymc-bin-${dist_ver}.tar.bz2 ${DIST_FILES}

release:
	git archive --prefix=bymc-src-${TAG}/ "${TAG}" \
        | bzip2 > bymc-src-${TAG}.tar.bz2

clean:
	$(info CLEANING)
	ocamlbuild -clean

${target}: ocaml-3.11.0
	$(info COMPILING)
	ocamlbuild -use-ocamlfind ${CFLAGS} ${target} | ./script/ocaml-friendly
	find _build -regex '.*\.cm\(i\|o\)'\
        | sed 's#_build\/src\/##; s/.cm\(i\|o\)//'\
        >./bymc.mltop
	ocamlbuild -use-ocamlfind ${CFLAGS} ./bymc.top ${target}

${debug_target}: ocaml-3.11.0
	$(info COMPILING DEBUG VERSION)
	ocamlbuild -use-ocamlfind ${CFLAGS} ${debug_target} | ./script/ocaml-friendly
	find _build -regex '.*\.cm\(i\|o\)'\
        | sed 's#_build\/src\/##; s/.cm\(i\|o\)//'\
        >./bymc.mltop
	ocamlbuild -use-ocamlfind ${CFLAGS} ./bymc.top ${debug_target}

ocaml-3.11.0:
	$(info Testing, whether ocaml version is at least 3.11.0)
	test ${ocaml_major} -gt 3 -o ${ocaml_minor} -ge 11
