#!/bin/bash

AGDA_DIR=$1
EXEC="$2"
flags="$3 --outDir=$4"
declare -i NB=$5

i=0
cd $AGDA_DIR
find . -name "*.agda" | sort |
    while read fil;
    do
        if (("$NB" == "$i"))
        then
            break
        fi;
        echo $i;
        i=$(($i+1));
        $EXEC $flags "$fil";
    done
