#!/bin/bash

rm Agda__Primitive.lp
cp ../Agda__Primitive-noEta.lp Agda__Primitive.lp

output=$(lambdapi check -c $1.lp 2>&1)
status=$?
echo "lambdapi check $1.lp"
echo "$output"
if [ $status = "0" ] && [ $(ls | grep $1.lpo) ]
then 
    exit 0
else
    exit 1
fi
