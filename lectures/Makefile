MODULES      := FunProg LogicPrimer Rewriting BoolReflect SsrStyle DepRecords HTT
VS           := $(MODULES:%=./%.v)
RELEASE      := $(VS) Makefile
ssr.pname	    := $(SSRCOQ_LIB)
ssr.lname    := Ssreflect
COQLIBS      := ssr
MAKEFILE     := Makefile.coq
COQNOTES     := pnp

.PHONY: coq clean

all: coq 

coq: $(MAKEFILE)
	make -f $(MAKEFILE)

SCRUB=
define scrub
$(if $(SCRUB),sed -e 's|\.opt||' $1 > $1.tmp; mv $1.tmp $1;)
endef

COQ_MK := coq_makefile
COQ_MK_FLAGS := $(VS) COQC = "\$$(COQBIN)coqc" COQLIBS = " -R ./../htt \"\"" COQFLAGS = "-q \$$(OPT) \$$(COQLIBS)"

$(MAKEFILE): 
	$(COQ_MK) $(COQ_MK_FLAGS) -o $(MAKEFILE)
	$(call scrub,Makefile.coq)

%.vo: %.v
	$(MAKE) -f $(MAKEFILE) $@

clean:  $(MAKEFILE)
	make -f $(MAKEFILE) clean
	rm -f $(MAKEFILE)



