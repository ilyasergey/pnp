MODULES := pred prelude idynamic ordtype pperm finmap domain pcm unionmap heap heaptac stmod stsep stlog stlogR array llistR
RELEASE := $(MODULES:%=%.v) Makefile Makefile.build
ssr.pname := $(SSRCOQ_LIB)
ssr.lname := Ssreflect
COQLIBS := ssr

include Makefile.build

all: coq
