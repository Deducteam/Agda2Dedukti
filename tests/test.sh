#!/bin/bash

if [[ $* == *-v* ]];
then
    verbose=1
else
    verbose=0
fi

codes=$(echo "$1")
test_files=$(find files -name "*.agda" | sort)

# cleans previous agdai, dk, dko, lp, lpo files
rm -f files/*.agdai output/dk/eta/*.dk* output/dk/no-eta/*.dk* output/lp/eta/*.lp* output/lp/no-eta/*.lp*

code_to_option () {
	echo "$1" \
	| sed -e "s/1/--dk/g" \
	| sed -e "s/2/--dk --eta/g" \
	| sed -e "s/3/--dk --lp/g" \
	| sed -e "s/4/--dk --lp --eta/g"
}

code_to_option_name () {
	echo "$1" \
	| sed -e "s/1/dk-no-eta/g" \
	| sed -e "s/2/dk-eta/g" \
	| sed -e "s/3/lp-no-eta/g" \
	| sed -e "s/4/lp-eta/g"
}

code_to_output_dir () {
	if [ "$1" == "1" ]; then
		echo "output/dk/no-eta/"
	elif [ "$1" == "2" ]; then
		echo "output/dk/eta/"
	elif [ "$1" == "3" ]; then
		echo "output/lp/no-eta/"
	elif [ "$1" == "4" ]; then
		echo "output/lp/eta/"
	fi
}

code_to_typecheck_dir () {
	if [ "$1" == "1" ]; then
		echo "output/dk/no-eta"
	elif [ "$1" == "2" ]; then
		echo "output/dk/eta"
	elif [ "$1" == "3" ]; then
		echo "output/lp/no-eta"
	elif [ "$1" == "4" ]; then
		echo "output/lp/eta"
	fi
}


echo "------------------------"
echo "  Running tests for modes : $(code_to_option_name "$codes")"
echo "------------------------"
echo "see test-list for test configuration"
echo ""

for file in $test_files ; do
    echo -e "\033[4m$file\033[0m"
    basefilename=$(basename "$file" ".agda")
    # takes the codes of the tests this file will go through
    current_test=$(cat test-list | grep "$basefilename " \
		       | cut -d ' ' -f 2-6 \
		       | sed "s/[^$codes]*//g")
    for option_code in $current_test ; do
	option=$(code_to_option "$option_code")
	option_name=$(code_to_option_name "$option_code")
	echo -n "$option_name : "
	# translation phase	
	cd files
	output=$(stack exec -- Agda2Dedukti-exe $option --outDir="../$(code_to_output_dir $option_code)" $(basename $file))
	status=$?
	cd ..	
	if [ "$status" == "0" ] ; then
	    echo -e -n "\033[0;32m1) Translation ok\033[0m "
	    if [ $verbose == "1" ]; then
		echo ""
		echo "$output"
	    fi
	else
	    echo -e "\033[0;31m1) Translation failed with error:\033[0m"
	    echo -e "stack exec -- Agda2Dedukti-exe $option --outDir=\"../$(code_to_output_dir $option_code)\" $(basename $file)"
	    echo "$output"
	    continue
	fi
	# typechecking phase	
	typecheck_dir=$(code_to_typecheck_dir $option_code)
	cd $typecheck_dir
	# the output file does not contain '-', so we need to take them of
	output=$(bash test.sh $(echo $basefilename | sed "s/[-]*//g"))
	status=$?	
	cd ../../..
	if [ "$status" == "0" ] ; then
	    echo -e "\033[0;32m2) Typechecking ok\033[0m "
	    if [ $verbose == "1" ]; then
		echo "$output"
	    fi	    
	else
	    echo -e "\033[0;31m2) Typechecking failed with error:\033[0m"
	    echo "$output"
	    continue
	fi
    done
done
