DKS=$(wildcard *.dk)

# DKOS need not have the same name that the corresponding Dedukti
# files (modulogic.dk becomes zen.dko) but for each file f.dk, dkdep
# f.dk outputs the name of the produced dko file before the ':'
# character.
DKOS=$(shell cut -d ':' -f 1 .depend)

BASE_LOC = -I ../../theory
FLAGS = -e --snf

DKDEP=dkdep $(BASE_LOC)
DKCHECK=dkcheck $(BASE_LOC) $(FLAGS)

TIMEOUT = 0

all: $(DKOS)

%.dko:
	timeout $(TIMEOUT) $(DKCHECK) $< || echo "Pb with" $<

clean:
	rm -f *.dko .depend

depend: .depend
.depend:
	$(DKDEP) *.dk > ./.depend

include .depend
