AGDA_STD_DIR = /home/thiago/git/Agda2Dedukti/agda-stdlib
EXEC = $(shell pwd)/dist/build/Agda2Dedukti/Agda2Dedukti

DK_TEST_DIR = translation/dk/tests/
LP_TEST_DIR = translation/lp/tests/

DK_STD_DIR = translation/dk/std-lib/
LP_STD_DIR = translation/lp/std-lib/

AGDAS = $(wildcard tests/*.agda)
DKS = $(patsubst tests/%.agda, translation/dk/tests/%.dk, $(AGDAS))
LPS = $(patsubst tests/%.agda, translation/lp/tests/%.lp, $(AGDAS))

all: compile

compile:
	cabal build

translation/dk/tests/%.dk: tests/%.agda
	cd tests && $(EXEC) --dk $(OPTS) --outDir=../$(DK_TEST_DIR) $(<F)

translation/lp/tests/%.lp: tests/%.agda
	cd tests && $(EXEC) --dk --lp $(OPTS) --outDir=../$(LP_TEST_DIR) $(<F)

rm-agdai:
	cd tests && rm -f *.agdai && cd ..

test-dk: compile rm-agdai $(DKS)
	cd $(DK_TEST_DIR) && make

test-lp: compile rm-agdai $(LPS)


clean-tests-dk:
	rm $(DK_TEST_DIR)/*.dk* $(DK_TEST_DIR)/.depend

clean-tests-lp:
	rm $(LP_TEST_DIR)/*.lp* $(LP_TEST_DIR)/.depend


NB ?= -1
TIMEOUT ?=0

std-lib: compile
	bash "./translation/dk/generate_std-lib.sh" $(AGDA_STD_DIR) $(EXEC) "--dk $(OPTS)" $(shell pwd)/$(DK_STD_DIR) $(NB)
	cd $(STD_DIR) && make FLAGS="-e --snf $(DK_FLAGS)" TIMEOUT=$(TIMEOUT);

clean-std-lib:
	rm $(STD_DIR)/*.dk* $(STD_DIR)/.depend
