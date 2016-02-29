all: default
default: Makefile.coq
	make -f Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject > Makefile.coq

.PHONY: coq clean
