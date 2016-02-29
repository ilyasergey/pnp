all: default lecsol doc

MODULES      := Introduction FunProg LogicPrimer Rewriting BoolReflect SsrStyle DepRecords HTT Conclusion
TEX          := $(MODULES:%=latex/%.v.tex)
COQNOTES     := pnp

default: 
	cd htt && make && cd ..
	cd coq && make && cd ..

lecsol: default
	cd lectures && make -f Makefile.coq && cd ..
	cd solutions && make -f Makefile.coq && cd ..

cleanhtt:
	cd htt && make -f Makefile.coq clean && cd ..

cleancoq:
	cd coq && make -f Makefile.coq clean && cd ..

cleanlec:
	cd lectures && make -f Makefile.coq clean && cd ..

cleansol:
	cd solutions && make -f Makefile.coq clean && cd ..

clean: cleansol cleanlec cleancoq cleanhtt

.PHONY: coq clean doc

doc: latex/$(COQNOTES).pdf

latex/%.v.tex: Makefile coq/%.v coq/%.glob coq/Introduction.v coq/FunProg.v coq/LogicPrimer.v coq/Rewriting.v coq/BoolReflect.v coq/SsrStyle.v coq/DepRecords.v coq/HTT.v coq/Conclusion.v
	cd coq ; coqdoc --interpolate --latex --body-only -s \
		$*.v -o ../latex/$*.v.tex

latex/$(COQNOTES).pdf: latex/$(COQNOTES).tex $(TEX) latex/references.bib latex/proceedings.bib latex/defs.tex 
	cd latex && pdflatex $(COQNOTES) && pdflatex $(COQNOTES) && bibtex $(COQNOTES) -min-crossrefs=99 && makeindex $(COQNOTES) && pdflatex $(COQNOTES) && pdflatex $(COQNOTES)

latex/%.pdf: latex/%.tex latex/references.bib latex/proceedings.bib latex/defs.tex 
	cd latex && pdflatex $* && pdflatex $* && bibtex $* -min-crossrefs=99 && makeindex $* && pdflatex $* && pdflatex $*

ziplec: cleanlec
	zip pnp-lectures.zip lectures/*.v lectures/Makefile lectures/_CoqProject

ziphtt: cleanhtt
	zip htt.zip htt/*.v htt/Makefile htt/_CoqProject

zipsol: cleansol
	zip pnp-solutions.zip solutions/*.v solutions/_CoqProject
