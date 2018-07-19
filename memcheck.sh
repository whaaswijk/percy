#!/bin/bash

for filename in ./build/test/*; do
    echo "Checking memory of $filename"
    if ! valgrind --leak-check=full --error-exitcode=1 $filename; then
        echo "Memory check failed!"
        exit 1
    fi
done
