all: compile

compile:
	stack build

theory-objects:
	cd theory/dk/eta && rm -f *.dko ; dkcheck -e univ.dk && dkcheck -e Agda.dk
	cd theory/dk/noEta && rm -f *.dko ; dkcheck -e univ.dk && dkcheck -e Agda.dk
	cd theory/lp/AgdaTheory && make clean && make install

# all tests
test: theory-objects 
	cd tests && bash test.sh "1 2 3 4"

# all tests, in verbose mode
test-verbose: theory-objects
	cd tests && bash test.sh "1 2 3 4" -v

# only dk tests
test-dk: theory-objects
	cd tests && bash test.sh "1 2"

# only lp tests
test-lp: theory-objects
	cd tests && bash test.sh "3 4"

# NB ?= -1
# TIMEOUT ?=0

# std-lib-no-eta: compile
# 	bash "./translation/dk/generate_std-lib.sh" $(AGDA_STD_DIR) $(EXEC) "--dk $(OPTS)" $(shell pwd)/$(DK_STD_DIR) $(NB)
#	cd $(STD_DIR) && make FLAGS="-e --snf $(DK_FLAGS)" TIMEOUT=$(TIMEOUT);

# clean-std-lib:
#	rm $(STD_DIR)/*.dk* $(STD_DIR)/.depend
