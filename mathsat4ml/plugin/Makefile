CC=gcc
CCFLAGS=-fPIC
LDFLAGS=-fPIC
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

all: ${LIBNAME}
	ocamlbuild ${OCFLAGS} -use-ocamlfind ./mathsat4ml.cmxs \
		-lflag -cclib -lflag \
		"-Wl,--no-as-needed -Wl,-rpath=${O} -L${O} -lmathsat4ml_driver"
	cp _build/mathsat4ml.cmxs .

#${AR} rcs ${LIBNAME} ${OBJ}
${LIBNAME}: init ${OBJ}
	${CC} -shared -o ${LIBNAME} ${LDFLAGS} ${OBJ}

${O}/%.o: ${SRC_DIR}/%.c
	${CC} -o $@ ${CCFLAGS} -c $<

init:
	mkdir -p ${O}

clean:
	rm -rI ${O}

