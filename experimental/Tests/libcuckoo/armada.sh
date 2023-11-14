#!/bin/bash

armada="mono ../../Binaries/Armada.exe /armadaPath:../.."
if [ "$1" == "" ]; then
    echo "Specify file to run";
    exit 1;
fi

#preprocessed_armada_file=`mktemp XXXXXXXX.tmp.arm`
preprocessed_armada_file=$1_preproc.arm
echo "Preprocessing..."
gcc -P -E - < $1 > $preprocessed_armada_file
echo "Finished preprocessing."
$armada $preprocessed_armada_file
