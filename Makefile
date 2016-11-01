EXTRA_DIR:=extra
COQDOCFLAGS:= \
  --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
  --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQDOCLIBS?=\
  -R "." Randomness

COQMAKEFILE:=Makefile.coq
COQ_PROJ:=_CoqProject
DOCVS:=\
  ArithLemmas.v \
  BijNat.v \
  LeastNumberSearch.v \
  PreorderEquiv.v \
  MeetSemiLattice.v \
  DistrLattice.v \
  Frame.v \
  LogicalFrames.v \
  FreeFrame.v \
  Cantor.v \
  Points.v \
  FreeDistrLattice.v

#  MyNotations.v
#  canonical_names.v

VS:=$(wildcard *.v)

VS_IN_PROJ:=$(shell grep .v $(COQ_PROJ))

ifeq (,$(VS_IN_PROJ))
VS_OTHER := $(VS)
else
VS := $(VS_IN_PROJ)
endif

all: myhtml

clean: $(COQMAKEFILE)
	echo $(VS)
	echo $(VS_OTHER)
	echo $(VS_IN_PROJ)
	@$(MAKE) -f $(COQMAKEFILE) $@
	rm -f $(COQMAKEFILE)

html: $(COQMAKEFILE) $(VS)
	rm -fr html
	@$(MAKE) -f $(COQMAKEFILE) $@
	cp $(EXTRA_DIR)/resources/* html

myhtml: html
	rm -rf myhtml
	mkdir -p myhtml
	"coqdoc" -toc $(COQDOCFLAGS) -html $(COQDOCLIBS) -d myhtml $(DOCVS)
	cp extra/resources/* myhtml

$(COQMAKEFILE): $(COQ_PROJ) $(VS)
		coq_makefile -f $(COQ_PROJ) $(VS_OTHER) -o $@

%: $(COQMAKEFILE) force
	@$(MAKE) -f $(COQMAKEFILE) $@
force $(COQ_PROJ) $(VS): ;

.PHONY: clean all force
