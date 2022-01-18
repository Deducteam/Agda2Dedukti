rm -f Agda__Primitive.dk && cp ../Agda__Primitive.dk Agda__Primitive.dk
dkdep -I ../../../../theory/dk/noEta/ *.dk > ./.depend
output=$(make $1.dko 2>&1)
status=$?
echo "$output"
if [ $status = "0" ] && [ $(ls | grep $1.dko) ]
then 
    exit 0
else
    exit 1
fi


