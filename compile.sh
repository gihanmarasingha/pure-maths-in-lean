#!/usr/bin/env bash

rm -rf html/ ; cd src/ ;
find . -name "*olean" | xargs rm
cd ../ ; make-lean-game
