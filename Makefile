AGDA_STD_DIR = /home/thiago/Documents/Programacao/agda_guillaume/agda-stdlib/agda-stdlib/src
EXEC = $(shell pwd)/src/Main

TEST_DIR = translation/tests/
STD_DIR = translation/std-lib/

AGDAS = $(wildcard tests/*.agda)
DKS = $(patsubst tests/%.agda, translation/tests/%.dk, $(AGDAS))

all: compile

compile:
	cd src/ && ghc Main

translation/tests/%.dk: tests/%.agda
	cd tests && $(EXEC) --dk $(OPTS) --outDir=../$(TEST_DIR) $(<F)

test: compile $(DKS)
	cd $(TEST_DIR) && make

clean-tests:
	rm $(TEST_DIR)/*.dk* $(TEST_DIR)/.depend

NB ?= -1
TIMEOUT ?=0

std-lib: compile
	bash "./translation/generate_std-lib.sh" $(AGDA_STD_DIR) $(EXEC) "--dk $(OPTS)" $(shell pwd)/$(STD_DIR) $(NB)
	cd $(STD_DIR) && make FLAGS="-e --snf $(DK_FLAGS)" TIMEOUT=$(TIMEOUT);

clean-std-lib:
	rm $(STD_DIR)/*.dk* $(STD_DIR)/.depend
