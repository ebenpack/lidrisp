#!/bin/bash
find . -name "*.ibc" -type f -delete
idris --build lidrisp.ipkg
idris -p contrib -i src --codegen node --interface  Main.idr -o dist/index.js
npm install
npm run build-prod
