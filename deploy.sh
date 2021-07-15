#!/usr/bin/env bash
set -e
if [ "$#" -ne 2 ]; then
    echo "Usage example: $0 gihanmarasingha pure-maths-pages"
    exit 1
fi

# Ensure tempfile is deleted on exit
trap 'rm -f "$TMPFILE"' EXIT

# Build
make-lean-game

# 3. Deploy
rm -rf deploy
mkdir deploy
cd deploy
git init
cp -r ../html/ .
cp -r ../to-be-deployed/./ .

# Insertion of Google Analytics tracker. First make temp file
TMPFILE=$(mktemp) || exit

if grep -q "Global site tag (gtag\.js) - Google Analytics" html/index.html; then
	echo "Google Analytics tracker not inserted"
else
	cat google_tracker.txt > $TMPFILE;
	tail -n +4 html/index.html >> $TMPFILE
	cp $TMPFILE html/index.html
	echo "Google Analytics tracker inserted"
fi

# Now stage all files, commit, and push
git add .
git commit -m "Update `date`"
git push git@github.com:$1/$2 +HEAD:gh-pages

cd ..
rm -rf deploy