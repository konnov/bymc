TARGET=test_plugin
OCFLAGS=

all: $(TARGET).native
	./$(TARGET).native --load 1

$(TARGET).native: src/*.ml
	ocamlbuild ${OCFLAGS} -use-ocamlfind ./$(TARGET).native

clean:
	ocamlbuild -clean

