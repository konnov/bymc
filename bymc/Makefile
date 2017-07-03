# Makefile to build them all
#
# Igor Konnov, 2012-2016

CFLAGS=-cflag -g -lflag -g -lflag -thread # the options at the end fix a bug

target="./bymc.native" # use ./bymc.byte for debugging
unittests=./unitTests.byte
debug_target="./bymc.byte"
ocamlver := $(shell ocaml -version | egrep -o '[0-9]+\.[0-9]+\.[0-9]+')
ocaml_major := $(shell echo ${ocamlver} | perl -pe 's/([0-9]+)\.[0-9]+\.[0-9]+/\1/')
ocaml_minor := $(shell echo ${ocamlver} | perl -pe 's/[0-9]+\.([0-9]+)\.[0-9]+/\1/')
ocaml_rev := $(shell echo ${ocamlver} | perl -pe 's/[0-9]+\.[0-9]+\.([0-9]+)/\1/')
dist_ver := $(shell date '+%Y%m%d')
OCAMLBUILD := ocamlbuild -use-ocamlfind

DIST_FILES=bymc.native verifyco-* verifypa-* syntpa-* script/ LICENSE

all: ${target}

compile: ${target}

debug: ${debug_target}

${unittests}: src/*.ml src/*.mli src/*.mly test/*.ml
	${OCAMLBUILD} ${CFLAGS} ./unitTests.byte

# unit tests
test: clean ${unittests}
	${unittests}

# functional tests
integrate: clean
	./test/func-test.sh

# just a synonym for integrate
fun: integrate

dist:

	git archive --prefix=bymc-src-${ver}/ master \
        | bzip2 > bymc-src-${ver}.tar.bz2

dist-bin: compile
	tar jhcf bymc-bin-${dist_ver}.tar.bz2 ${DIST_FILES}

release:
	git archive --prefix=bymc-src-${TAG}/ "${TAG}" \
        | bzip2 > bymc-src-${TAG}.tar.bz2

# ocaml doc
doc:
	mkdir -p _build/doc
	ocamldoc -I _build/src -html -keep-code -colorize-code \
		src/*.ml src/*.mli -d _build/doc

tags:
	otags src/*.ml src/*.mli test/*.ml

clean:
	$(info CLEANING)
	${OCAMLBUILD} -clean

${target}: ocaml-3.11.0
	$(info COMPILING)
	${OCAMLBUILD} ${CFLAGS} ${target}

${debug_target}: ocaml-3.11.0
	$(info COMPILING DEBUG VERSION)
	${OCAMLBUILD} ${CFLAGS} ${debug_target}

ocaml-3.11.0:
	$(info Testing, whether ocaml version is at least 3.11.0)
	test ${ocaml_major} -gt 3 -o ${ocaml_minor} -ge 11

