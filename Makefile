all: default doc

MODULES      := Introduction FunProg LogicPrimer Rewriting BoolReflect SsrStyle DepRecords HTT Conclusion
TEX          := $(MODULES:%=latex/%.v.tex)
COQNOTES     := pnp

default: Makefile.coq
	make -f Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject > Makefile.coq

.PHONY: coq clean doc

doc: latex/$(COQNOTES).pdf

latex/%.v.tex: Makefile coq/%.v coq/%.glob coq/Introduction.v coq/FunProg.v coq/LogicPrimer.v coq/Rewriting.v coq/BoolReflect.v coq/SsrStyle.v coq/DepRecords.v coq/HTT.v coq/Conclusion.v
	cd coq ; coqdoc --interpolate --latex --body-only -s \
		$*.v -o ../latex/$*.v.tex

latex/$(COQNOTES).pdf: latex/$(COQNOTES).tex $(TEX) latex/references.bib latex/proceedings.bib latex/defs.tex 
	cd latex && pdflatex $(COQNOTES) && pdflatex $(COQNOTES) && bibtex $(COQNOTES) -min-crossrefs=99 && makeindex $(COQNOTES) && pdflatex $(COQNOTES) && pdflatex $(COQNOTES)

latex/%.pdf: latex/%.tex latex/references.bib latex/proceedings.bib latex/defs.tex 
	cd latex && pdflatex $* && pdflatex $* && bibtex $* -min-crossrefs=99 && makeindex $* && pdflatex $* && pdflatex $*

zip:
	zip pnp.zip Makefile lectures/*.v coq/*.v solutions/*.v htt/*.v latex/*.sty latex/*.bib latex/pnp.tex latex/*.png _CoqProject

