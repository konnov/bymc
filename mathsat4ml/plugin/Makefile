# set it to the directory, where mathsat is unpacked
MATHSAT_DIR=$(HOME)/usr/mathsat
CC=gcc
CCFLAGS=-fPIC -O3 -I${MATHSAT_DIR}/include -Wall
LDFLAGS=-fPIC -Wl,--no-as-needed -Wl,-rpath=${O} 
AR=ar
OCFLAGS=

O=`pwd`/_build
OBJ=$(O)/mathsat-driver.o
SRC_DIR=src
LIBNAME=${O}/libmathsat4ml_driver.so

# -rpath to statically set the location to mathsat4ml_driver
# if you want to move the directory, recompile the library
# (otherwise, one has to mess with LD_LIBRARY_PATH)
# --no-as-needed to include all symbols irrespectively of whether
# the compiler sees them used or not (Ctypes requires that)

all: ${LIBNAME} mlsrc/*.ml mlsrc/*.mli
	ocamlbuild ${OCFLAGS} -use-ocamlfind mathsat4ml.cmxs \
		-lflag -cclib -lflag \
		"-Wl,--no-as-needed -Wl,-rpath=${O} -L${O} -L${MATHSAT_DIR}/lib -lmathsat4ml_driver -lmathsat"
	cp _build/mlsrc/mathsat4ml.cmxs .

#${AR} rcs ${LIBNAME} ${OBJ}
${LIBNAME}: init ${OBJ}
	${CC} -shared ${LDFLAGS} -o ${LIBNAME} ${OBJ} -L${MATHSAT_DIR}/lib -lmathsat -lstdc++ -lgmp -lgmpxx

${O}/%.o: ${SRC_DIR}/%.c
	${CC} -o $@ ${CCFLAGS} -c $<

init:
	mkdir -p ${O}

clean:
	ocamlbuild -clean

