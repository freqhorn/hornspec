#!/bin/bash

FLAGS=""
BINARY_TIMEOUT="60s"
BINARY_OUTPUT="/tmp/binout"
TOOL_CMDLINE="../../build/tools/deep/freqhorn --data --v3 --freqs --eps --aggp "
SMT_TIMEOUT="100s"

#compile given input program
if [ $# -ne 1 ]
then
    echo "Usage: run.sh input_file.c"
    exit 1
fi

filename=$1
binary="/tmp/${filename%.*}"

echo "compiling $filename to $binary"
g++ -o $binary $filename 

if [ $? -ne 0 ]
then
    echo "compilation failed"
    exit 1
fi

#run the program and note output files
echo "running $binary with $BINARY_TIMEOUT timeout"
timeout -k 10 $BINARY_TIMEOUT $binary 2> $BINARY_OUTPUT
es=$?
if [ $es -eq 124 ]
then
    echo "make sure your program completes within $BINARY_TIMEOUT"
    exit 1
elif [ $es -ne 0 ]
then
    echo "program killed or program asserted (exit status: $es)"
    exit 1
fi


#run the tool with output files as options
toolcmd=$TOOL_CMDLINE
while read inputFile; do
    if [[ $inputFile == Output* ]]
    then
	continue
    fi
    toolcmd=$toolcmd" --data-input "$inputFile
done < $BINARY_OUTPUT

smtfile="../bench_horn_multiple/${filename%.*}.smt2"
if [ -f $smtfile ]
then
    toolcmd=$toolcmd" $smtfile"
    echo "running $toolcmd with $SMT_TIMEOUT timeout"
    timeout -k 10 $SMT_TIMEOUT $toolcmd
else
    echo $smtfile" not found"
fi

