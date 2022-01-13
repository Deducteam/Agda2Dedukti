AGDA_STD_DIR = 
EXEC = stack exec -- Agda2Dedukti-exe

TEST_FILES = tests/files/
TEST_OUTPUT_DK = tests/output/dk/tests/
TEST_OUTPUT_LP = tests/output/lp/tests/

DK_STD_DIR = 
LP_STD_DIR = 

AGDAS = $(wildcard $(TEST_FILES)/*.agda)
DKS = $(patsubst $(TEST_FILES)/%.agda, $(TEST_OUTPUT_DK)/%.dk, $(AGDAS))
LPS = $(patsubst $(TEST_FILES)/%.agda, $(TEST_OUTPUT_LP)/%.lp, $(AGDAS))

all: compile

compile:
	stack build

theory-objects:
	cd theory/dk/eta && rm -f *.dko ; dkcheck -e univ.dk && dkcheck -e Agda.dk
	cd theory/dk/noEta && rm -f *.dko ; dkcheck -e univ.dk && dkcheck -e Agda.dk
	cd theory/lp/AgdaTheory && make clean && make install

tests/output/dk/tests/%.dk: tests/files/%.agda
	cd $(TEST_FILES) && $(EXEC) --dk $(OPTS) --outDir=../../$(TEST_OUTPUT_DK) $(<F)

tests/output/lp/tests/%.lp: tests/files/%.agda
	cd $(TEST_FILES) && $(EXEC) --dk --lp $(OPTS) --outDir=../../$(TEST_OUTPUT_LP) $(<F)

# sometimes using an old .agdai causes some problems
rm-agdai:
	-cd $(TEST_FILES) && rm -f *.agdai

set-eta:
	$(eval OPTS+= --eta)

test-dk-eta: clean-tests-dk set-eta compile rm-agdai $(DKS) theory-objects
	cd $(TEST_OUTPUT_DK) && make BASE_LOC="-I ../../../../theory/dk/eta"

test-dk-noEta: clean-tests-dk compile rm-agdai $(DKS) theory-objects
	cd $(TEST_OUTPUT_DK) && make BASE_LOC="-I ../../../../theory/dk/noEta"

test-lp-eta: clean-tests-lp set-eta compile rm-agdai $(LPS) theory-objects
	cd $(TEST_OUTPUT_LP) && make eta

test-lp-noEta: clean-tests-lp compile rm-agdai $(LPS) theory-objects
	cd $(TEST_OUTPUT_LP) && make noEta

clean-tests-dk:
	-rm $(TEST_OUTPUT_DK)/*.dk* $(TEST_OUTPUT_DK)/.depend

clean-tests-lp:
	-rm $(TEST_OUTPUT_LP)/*.lp*


NB ?= -1
TIMEOUT ?=0

std-lib-no-eta: compile
	bash "./translation/dk/generate_std-lib.sh" $(AGDA_STD_DIR) $(EXEC) "--dk $(OPTS)" $(shell pwd)/$(DK_STD_DIR) $(NB)
	cd $(STD_DIR) && make FLAGS="-e --snf $(DK_FLAGS)" TIMEOUT=$(TIMEOUT);

clean-std-lib:
	rm $(STD_DIR)/*.dk* $(STD_DIR)/.depend
