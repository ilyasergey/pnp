MODULES      := Introduction FunProg LogicPrimer Rewriting BoolReflect SsrStyle DepRecords HTT Conclusion
VS           := $(MODULES:%=coq/%.v)
TEX          := $(MODULES:%=latex/%.v.tex)
RELEASE      := $(VS) Makefile
ssr.pname    := $(SSRCOQ_LIB)
ssr.lname    := Ssreflect
COQLIBS      := ssr
MAKEFILE     := Makefile.coq
COQNOTES     := pnp

.PHONY: coq clean doc

all: coq doc

coq: $(MAKEFILE)
	make -f $(MAKEFILE)

SCRUB=
define scrub
$(if $(SCRUB),sed -e 's|\.opt||' $1 > $1.tmp; mv $1.tmp $1;)
endef


COQ_MK := coq_makefile
COQ_MK_FLAGS := $(VS) COQC = "\$$(COQBIN)coqc" COQLIBS = " -R ./htt \"\"" COQFLAGS = "-q \$$(OPT) \$$(COQLIBS)"

$(MAKEFILE): 
	cd htt && make && cd ..
	$(COQ_MK) $(COQ_MK_FLAGS) -o $(MAKEFILE)
	$(call scrub,Makefile.coq)

%.vo: %.v
	$(MAKE) -f $(MAKEFILE) $@

doc: latex/$(COQNOTES).pdf

latex/%.v.tex: Makefile coq/%.v coq/%.glob
	cd coq ; coqdoc --interpolate --latex --body-only -s \
		$*.v -o ../latex/$*.v.tex

latex/$(COQNOTES).pdf: latex/$(COQNOTES).tex $(TEX) latex/references.bib latex/proceedings.bib latex/defs.tex 
	cd latex && pdflatex $(COQNOTES) && pdflatex $(COQNOTES) && bibtex $(COQNOTES) -min-crossrefs=99 && makeindex $(COQNOTES) && pdflatex $(COQNOTES) && pdflatex $(COQNOTES)

latex/%.pdf: latex/%.tex latex/references.bib latex/proceedings.bib latex/defs.tex 
	cd latex && pdflatex $* && pdflatex $* && bibtex $* -min-crossrefs=99 && makeindex $* && pdflatex $* && pdflatex $*

cleanhtt:
	cd htt && make clean && cd ..

clean:  $(MAKEFILE)
	make -f $(MAKEFILE) clean
	rm -f $(MAKEFILE)
	rm -f pnp*.zip
	cd latex; rm -f *.html *.xml *.png *.brf *.css *.log *.aux *.dvi *.v.tex *.toc *.bbl *.blg *.idx *.ilg *.pdf *.ind *.out *.xref *.xdv *.tmp *.ncx *.epub *.4tc *.4ct *.mobi *.lg *.idv *.opf


ziplec:
	zip pnp-lectures.zip lectures/*.v lectures/Makefile

zipsol:
	zip pnp-solutions.zip solutions/*.v 
