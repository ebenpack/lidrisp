#!/bin/bash
set -e
idris --clean lidrisp.ipkg
idris --build lidrisp.ipkg
cd src/
idris -p contrib -i src --codegen node --interface  Main.idr -o ../dist/index.js
cd ..
npm install
npm run build-prod
