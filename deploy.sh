#!/usr/bin/env bash
set -e
if [ "$#" -ne 2 ]; then
    echo "Usage example: $0 gihanmarasingha pure-maths-pages"
    exit 1
fi

# Build
make-lean-game

# 3. Deploy
rm -rf deploy
git clone git@github.com:$1/$2 deploy
cd deploy
rm -rf * .gitignore
cp -Lr ../to-be-deployed/./ .

git add .
git commit -m "Update `date`"
git push

cd ..
rm -rf deploy