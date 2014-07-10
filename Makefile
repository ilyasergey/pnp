MODULES      := Introduction FunProg LogicPrimer Induction Rewriting DepRecords LessAdHoc HTT
VS           := $(MODULES:%=coq/%.v)
TEX          := $(MODULES:%=latex/%.v.tex)
RELEASE      := $(VS) Makefile
ssr.pname    := $(SSRCOQ_LIB)
ssr.lname    := Ssreflect
COQLIBS      := ssr
MAKEFILE     := Makefile.coq
COQNOTES     := coqnotes

.PHONY: coq clean doc

all: coq doc

coq: $(MAKEFILE)
	make -f $(MAKEFILE)

SCRUB=
define scrub
$(if $(SCRUB),sed -e 's|\.opt||' $1 > $1.tmp; mv $1.tmp $1;)
endef

define print_flag
-I $($1.pname)$(if $($1.lname), -as $($1.lname)) 
endef

COQ_MK := coq_makefile
COQ_MK_FLAGS := $(VS) COQC = "\$$(COQBIN)ssrcoq" COQLIBS = "$(foreach f,$(COQLIBS),$(call print_flag,$f)) -I ." COQFLAGS = "-q \$$(OPT) \$$(COQLIBS) -dont-load-proofs -compile"

$(MAKEFILE): Makefile 
	$(COQ_MK) $(COQ_MK_FLAGS) -o $(MAKEFILE)
	$(call scrub,Makefile.coq)

%.vo: %.v
	$(MAKE) -f $(MAKEFILE) $@

doc: latex/$(COQNOTES).pdf

latex/%.v.tex: Makefile coq/%.v coq/%.glob
	cd coq ; coqdoc --interpolate --latex --body-only -s \
		$*.v -o ../latex/$*.v.tex

latex/$(COQNOTES).pdf: latex/$(COQNOTES).tex $(TEX) latex/references.bib latex/proceedings.bib
	cd latex ; pdflatex $(COQNOTES) ; pdflatex $(COQNOTES) ; bibtex $(COQNOTES) ; makeindex $(COQNOTES) ; pdflatex $(COQNOTES) ; pdflatex $(COQNOTES)

latex/%.pdf: latex/%.tex latex/references.bib latex/proceedings.bib
	cd latex ; pdflatex $* ; pdflatex $* ; bibtex $* ; makeindex $* ; pdflatex $* ; pdflatex $*

clean:  $(MAKEFILE)
	make -f $(MAKEFILE) clean
	rm -f $(MAKEFILE)
	cd latex; rm -f *.log *.aux *.dvi *.v.tex *.toc *.bbl *.blg *.idx *.ilg *.pdf *.ind *.out


# release: $(TARGET_DIR)
# 	cp -i Makefile $(RELEASE) $(TARGET_DIR)



