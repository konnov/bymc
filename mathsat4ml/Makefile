CC=gcc
CCFLAGS=
LDFLAGS=
AR=ar

O=./_build
OBJ=$(O)/mathsat_driver.o
SRC_DIR=src
LIBNAME=mathsat4ml.a

${LIBNAME}: init ${OBJ}
	${AR} rcs ${LIBNAME} ${OBJ}

${O}/%.o: ${SRC_DIR}/%.c
	${CC} -o $@ ${CFLAGS} -c $<

init:
	mkdir -p ${O}

clean:
	rm -rI ${O}

