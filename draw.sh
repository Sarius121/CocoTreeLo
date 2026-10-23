#!/bin/bash
FILE=$1

if [ -d $FILE ]; then
    find $FILE -maxdepth 1 -type f -iname "*.dot" -exec dot -Tsvg -O {} \;
else
    dot -Tsvg $FILE > $FILE.svg
fi
