#!/bin/bash

# Author: Aaron Eline
# Combine and de-duplicate all of the csvs generated by dafny reporting

set -e

if [ -z "$1" ]; then
	DIR="."
else
	DIR="$1"
fi

version=$(cat Config | grep interfaces | cut -d "(" -f 2 | cut -d ")" -f 1)

cd "$DIR"

ls | grep csv | head -n1 | xargs head -n1 | awk '{ printf "%s,version\n", $0 }'


for file in *.csv; do
	tail -n+2 "$file"
done | sort | uniq | awk -v version=$version '{ printf "%s,%s\n", $0, version }'
