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

define print_flag
-I $($1.pname)$(if $($1.lname), -as $($1.lname)) 
endef

COQ_MK := coq_makefile
COQ_MK_FLAGS := $(VS) COQC = "\$$(COQBIN)ssrcoq" COQLIBS = "$(foreach f,$(COQLIBS),$(call print_flag,$f)) -I . -I ./../htt" COQFLAGS = "-q \$$(OPT) \$$(COQLIBS) -dont-load-proofs -compile"

$(MAKEFILE): 
	$(COQ_MK) $(COQ_MK_FLAGS) -o $(MAKEFILE)
	$(call scrub,Makefile.coq)

%.vo: %.v
	$(MAKE) -f $(MAKEFILE) $@

clean:  $(MAKEFILE)
	make -f $(MAKEFILE) clean
	rm -f $(MAKEFILE)



