include Makefile.config

#---------------------------------------
# Directories
#---------------------------------------

SRCDIR = $(shell pwd)
#
# Installation directory
#
SITE-LIB = $(shell $(OCAMLFIND) printconf destdir)
PKG-NAME = cudd
SITE-LIB-PKG = $(SITE-LIB)/$(PKG-NAME)

#---------------------------------------
# C part
#---------------------------------------

ICFLAGS = -Icudd-2.4.2/cudd -Icudd-2.4.2/mtr -Icudd-2.4.2/epd -Icudd-2.4.2/st -Icudd-2.4.2/util \
-I$(CAML_PREFIX)/lib/ocaml -I$(CAMLIDL_PREFIX)/lib/ocaml

#---------------------------------------
# OCaml part
#---------------------------------------

OCAMLCCOPT = \
-ccopt -L$(SITE-LIB)/stublibs \
-ccopt -L$(SITE-LIB-PKG) \
-ccopt -L$(CAMLIDL_PREFIX)/lib/ocaml \
-ccopt -L$(CAML_PREFIX)/lib/ocaml

#---------------------------------------
# Files
#---------------------------------------

IDLMODULES = hash cache memo man bdd vdd custom add

MLMODULES = hash cache memo man bdd vdd custom weakke pWeakke mtbdd mtbddc user mapleaf add

CCMODULES = \
	cuddauxAddCamlTable cuddauxAddIte cuddauxBridge cuddauxCompose \
	cuddauxGenCof cuddauxMisc cuddauxUtil \
	cuddauxTDGenCof cuddauxAddApply \
	$(IDLMODULES:%=%_caml) cudd_caml

CCLIB = libcuddcaml.a libcuddcaml.d.a libcuddcaml.p.a
ifneq ($(HAS_SHARED),)
	CCLIB += dllcuddcaml.so
endif

FILES_TOINSTALL = META \
	cudd-2.4.2/cudd/cudd.h cudd-2.4.2/cudd/cuddInt.h \
	cudd-2.4.2/mtr/mtr.h \
	cudd-2.4.2/epd/epd.h \
	cudd-2.4.2/st/st.h \
	cudd-2.4.2/util/util.h \
	cuddaux.h cudd_caml.h \
	$(IDLMODULES:%=%.idl) \
	cudd.cmi cudd.cma \
	cudd.cmx cudd.cmxa cudd.a \
	cudd.d.cmxa cudd.d.a \
	cudd.p.cmx cudd.p.cmxa cudd.p.a \
	$(CCLIB)

ifneq ($(OCAMLPACK),)
FILES_TOINSTALL += cudd_ocamldoc.mli
endif

#---------------------------------------
# Rules
#---------------------------------------

# Global rules
all: $(FILES_TOINSTALL)

# Example of compilation command with ocamlfind
%.byte: %.ml
	$(OCAMLFIND) ocamlc $(OCAMLFLAGS) $(OCAMLINC) -o $@ $*.ml \
	-package cudd -linkpkg
%.opt: %.ml
	$(OCAMLFIND) ocamlopt -verbose $(OCAMLOPTFLAGS) $(OCAMLINC) -o $@ $*.ml \
	-package cudd -linkpkg

install: $(FILES_TOINSTALL)
	$(OCAMLFIND) remove $(PKG-NAME)
	$(OCAMLFIND) install $(PKG-NAME) $^

uninstall:
	$(OCAMLFIND) remove $(PKG-NAME)

mostlyclean: clean
	(cd cudd-2.4.2; make clean)
	/bin/rm -f Makefile.depend TAGS
	/bin/rm -f $(IDLMODULES:%=%.ml) $(IDLMODULES:%=%.mli) $(IDLMODULES:%=%_caml.c) tmp/* html/*
	/bin/rm -f mlcuddidl.?? mlcuddidl.??? mlcuddidl.info example example.opt mlcuddidl.tex ocamldoc.tex *.dvi style.css ocamldoc.sty index.html

distclean: mostlyclean
	(cd cudd-2.4.2; make distclean; /bin/rm -f *.a)

clean:
	/bin/rm -f cuddtop *.byte *.opt
	/bin/rm -f cuddaux.?? cuddaux.??? cuddaux.info
	/bin/rm -f *.[ao] *.so *.cm[ioxat] *.cmti *.cmxa *.opt *.opt2 *.annot cudd_ocamldoc.mli
	/bin/rm -f cmttb*
	/bin/rm -fr html

# CAML rules

cudd.cma: cudd.cmo $(CCLIB)
	$(OCAMLFIND) ocamlc -verbose -a	-o $@ $< \
	-dllib -lcuddcaml \
	-cclib -lcuddcaml -cclib -lcamlidl $(OCAMLCCOPT)

cudd.cmxa: cudd.cmx $(CCLIB)
	$(OCAMLFIND) ocamlopt -verbose -a -o $@ $< \
	-cclib -lcuddcaml -cclib -lcamlidl $(OCAMLCCOPT)
cudd.p.cmxa: cudd.p.cmx $(CCLIB)
	$(OCAMLFIND) ocamlopt -verbose -p -a -o $@ $< \
	-cclib -lcuddcaml.p -cclib -lcamlidl $(OCAMLCCOPT)
cudd.d.cmxa: cudd.cmx $(CCLIB)
	$(OCAMLFIND) ocamlopt -verbose -a -o $@ $< \
	-cclib -lcuddcaml.d -cclib -lcamlidl $(OCAMLCCOPT)

cudd.cmo cudd.cmi: $(MLMODULES:%=%.cmo)
	$(OCAMLC) $(OCAMLFLAGS) $(OCAMLINC) -pack -o $@ $^
cudd.cmx: $(MLMODULES:%=%.cmx)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -pack -o $@ $^
cudd.p.cmx:  $(MLMODULES:%=%.p.cmx)
	$(OCAMLOPT) $(OCAMLOPTFLAGS_PROF) -p -pack -o $@ $^


# C rules
libcuddcaml.a: cudd-2.4.2/libcuddall.a $(CCMODULES:%=%.o)
	cp $< $@
	$(AR) r $@ $(CCMODULES:%=%.o)
	$(RANLIB) $@
libcuddcaml.p.a: cudd-2.4.2/libcuddall.p.a $(CCMODULES:%=%.p.o)
	cp $< $@
	$(AR) r $@ $(CCMODULES:%=%.p.o)
	$(RANLIB) $@
libcuddcaml.d.a: cudd-2.4.2/libcuddall.d.a $(CCMODULES:%=%.d.o)
	cp $< $@
	$(AR) r $@ $(CCMODULES:%=%.d.o)
	$(RANLIB) $@
dllcuddcaml.so: libcuddcaml.a
	mkdir -p tmp
	(cd tmp; /bin/rm -fr *.o; $(AR) x ../$^)
	$(CC) $(CFLAGS) $(XCFLAGS) -shared -o $@ tmp/*.o \
	-L$(CAMLIDL_PREFIX)/lib/ocaml -lcamlidl
	/bin/rm -f tmp/*.o

cudd-2.4.2/libcuddall.a:
	(cd cudd-2.4.2; \
	make libcuddall.a CPP="$(CC)" CC="$(CC)" XCFLAGS="$(XCFLAGS)" ICFLAGS="$(CFLAGS)" RANLIB="$(RANLIB)" DDDEBUG="" MTRDEBUG="")
cudd-2.4.2/libcuddall.p.a:
	(cd cudd-2.4.2; \
	make libcuddall.p.a CPP="$(CC)" CC="$(CC)" XCFLAGS="$(XCFLAGS)" ICFLAGS="$(CFLAGS_PROF)" RANLIB="$(RANLIB)" DDDEBUG="" MTRDEBUG="")
cudd-2.4.2/libcuddall.d.a:
	(cd cudd-2.4.2; \
	make libcuddall.d.a CPP="$(CC)" CC="$(CC)" XCFLAGS="$(XCFLAGS)" ICFLAGS="$(CFLAGS_DEBUG)" RANLIB="$(RANLIB)" DDDEBUG="-DDD_DEBUG -DDD_VERBOSE -DDD_STATS -DDD_CACHE_PROFILE -DDD_UNIQUE_PROFILE -DDD_COUNT" MTRDEBUG="-DMTR_DEBUG")

# HTML and LATEX rules
.PHONY: html

cudd_ocamldoc.mli: cudd.mlpacki $(MLMODULES:%=%.mli)
	$(OCAMLPACK) -o $@ -intro cudd.mlpacki -level 2 $(MLMODULES:%=%.mli)

mlcuddidl.pdf: mlcuddidl.dvi
	$(DVIPDF) mlcuddidl.dvi
mlcuddidl.dvi: cudd_ocamldoc.mli
	mkdir -p tmp
	cp cudd_ocamldoc.mli tmp/cudd.mli
	(cd tmp; $(OCAMLC) $(OCAMLINC) -c cudd.mli)
	$(OCAMLDOC) $(OCAMLINC) -I tmp \
-t "MLCUDDIDL: OCaml interface for CUDD library, version 2.2.0, 01/02/11" \
-latextitle 1,part -latextitle 2,chapter -latextitle 3,section -latextitle 4,subsection -latextitle 5,subsubsection -latextitle 6,paragraph -latextitle 7,subparagraph \
-latex -o ocamldoc.tex tmp/cudd.mli
	$(SED) -e 's/\\documentclass\[11pt\]{article}/\\documentclass[10pt,twosdie,a4paper]{book}\\usepackage{ae,fullpage,makeidx,fancyhdr}\\usepackage[ps2pdf]{hyperref}\\pagestyle{fancy}\\setlength{\\parindent}{0em}\\setlength{\\parskip}{0.5ex}\\sloppy\\makeindex\\author{Bertrand Jeannet}/' -e 's/\\end{document}/\\appendix\\printindex\\end{document}/' ocamldoc.tex >mlcuddidl.tex
	$(LATEX) mlcuddidl
	$(MAKEINDEX) mlcuddidl
	$(LATEX) mlcuddidl
	$(LATEX) mlcuddidl

dot: $(MLMODULES:%=%.ml)
	$(OCAMLDOC) -dot -dot-reduce -o cudd.dot $(MLMODULES:%=%.ml)

html: mlcuddidl.odoci cudd_ocamldoc.mli
	mkdir -p tmp
	cp cudd_ocamldoc.mli tmp/cudd.mli
	(cd tmp; $(OCAMLC) $(OCAMLINC) -c cudd.mli)
	mkdir -p html
	$(OCAMLDOC) $(OCAMLINC) -I tmp -html -d html -colorize-code -intro mlcuddidl.odoci tmp/cudd.mli

homepage: html mlcuddidl.pdf
	hyperlatex index
	scp -r index.html html mlcuddidl.pdf Changes \
		avedon:/home/wwwpop-art/people/bjeannet/mlxxxidl-forge/mlcuddidl
	ssh avedon chmod -R ugoa+rx /home/wwwpop-art/people/bjeannet/mlxxxidl-forge/mlcuddidl


#--------------------------------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#--------------------------------------------------------------

.SUFFIXES: .c .h .o .ml .mli .cmi .cmo .cmx .idl .d.o _caml.c

#-----------------------------------
# IDL
#-----------------------------------

# Generates X_caml.c, X.ml, X.mli from X.idl

# sed -f sedscript_caml allows to remove prefixes generated by camlidl
# grep --extended-regexp '^(.)+$$' removes blanks lines

$(IDLMODULES:%=%_caml.c) $(IDLMODULES:%=%.ml) $(IDLMODULES:%=%.mli): $(IDLMODULES:%=%.idl) macros.m4 sedscript_caml sedscript_c
	mkdir -p tmp
	for i in $(IDLMODULES); do \
		echo "module $$i"; \
		cp $${i}.idl tmp/$${i}.idl; \
		$(CAMLIDL) -no-include -prepro "$(M4) macros.m4" -I $(SRCDIR) tmp/$${i}.idl; \
		$(SED) -f sedscript_c tmp/$${i}_stubs.c >$${i}_caml.c; \
		$(SED) -f sedscript_caml tmp/$${i}.ml >$${i}.ml; \
		$(SED) -f sedscript_caml tmp/$${i}.mli >$${i}.mli; \
	done

#-----------------------------------
# C
#-----------------------------------

%.o: %.c cudd_caml.h cuddaux.h
	$(CC) $(CFLAGS) $(ICFLAGS) $(XCFLAGS) -c -o $@ $<
%.d.o: %.c cudd_caml.h cuddaux.h
	$(CC) $(CFLAGS_DEBUG) $(ICFLAGS) $(XCFLAGS) -c -o $@ $<
%.p.o: %.c cudd_caml.h cuddaux.h
	$(CC) $(CFLAGS_PROF) $(ICFLAGS) $(XCFLAGS) -c -o $@ $<

#-----------------------------------
# CAML
#-----------------------------------

%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) $(OCAMLINC) -c $<

%.cmo: %.ml %.cmi
	$(OCAMLC) $(OCAMLFLAGS) $(OCAMLINC) -c $<

$(MLMODULES:%=%.cmx): %.cmx: %.ml %.cmi
	$(OCAMLOPT) $(OCAMLOPTFLAGS) $(OCAMLINC) -for-pack Cudd -c $<

$(MLMODULES:%=%.p.cmx): %.p.cmx: %.ml %.cmi
	$(OCAMLOPT) -p $(OCAMLOPTFLAGS) $(OCAMLINC) -for-pack Cudd -c -o $@ $<

#-----------------------------------
# Dependencies
#-----------------------------------

depend: $(IDLMODULES:%=%.ml) $(IDLMODULES:%=%.mli)
	$(OCAMLDEP) $(MLMODULES:%=%.mli) $(MLMODULES:%=%.ml) >Makefile.depend

Makefile.depend: $(IDLMODULES:%=%.ml) $(IDLMODULES:%=%.mli)
	$(OCAMLDEP) $(MLMODULES:%=%.mli) $(MLMODULES:%=%.ml) >Makefile.depend

-include Makefile.depend
