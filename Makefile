all: default doc

MODULES      := Introduction FunProg LogicPrimer Rewriting BoolReflect SsrStyle DepRecords HTT Conclusion
TEX          := $(MODULES:%=latex/%.v.tex)
COQNOTES     := pnp

default: Makefile.coq
	$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: coq clean doc zip

doc: latex/$(COQNOTES).pdf

latex/%.v.tex: Makefile coq/%.v coq/%.glob coq/Introduction.v coq/FunProg.v coq/LogicPrimer.v coq/Rewriting.v coq/BoolReflect.v coq/SsrStyle.v coq/DepRecords.v coq/HTT.v coq/Conclusion.v
	cd coq ; coqdoc --no-externals --interpolate --latex --body-only -s \
		$*.v -o ../latex/$*.v.tex

latex/$(COQNOTES).pdf: latex/$(COQNOTES).tex $(TEX) latex/references.bib latex/proceedings.bib latex/defs.tex 
	cd latex && pdflatex $(COQNOTES) && pdflatex $(COQNOTES) && bibtex $(COQNOTES) -min-crossrefs=99 && makeindex $(COQNOTES) && pdflatex $(COQNOTES) && pdflatex $(COQNOTES)

latex/%.pdf: latex/%.tex latex/references.bib latex/proceedings.bib latex/defs.tex 
	cd latex && pdflatex $* && pdflatex $* && bibtex $* -min-crossrefs=99 && makeindex $* && pdflatex $* && pdflatex $*
	mv pnp.pdf docs/

zip:
	rm -f pnp.zip
	zip pnp.zip ../pnp/Makefile ../pnp/lectures/*.v ../pnp/coq/*.v ../pnp/solutions/*.v ../pnp/htt/*.v ../pnp/latex/*.sty ../pnp/latex/*.bib ../pnp/latex/pnp.tex ../pnp/latex/*.png ../pnp/latex/defs.tex ../pnp/_CoqProject
