# lidrisp

A quick and dirty port of [hascheme](https://github.com/ebenpack/hascheme) into
idris.

TL;DR it's an (almost certainly buggy and incomplete) implementation of scheme,
written in idris.

Very much based on Write Yourself a Scheme in 48 Hours, with a few notable
differences. E.g. more complete-ish number parsing and fuller numeric tower,
let/let*/letrec expressions, a slightly more sophisticated environment model,
etc.

    # Build
    > idris --build lidrisp.ipkg
    > idris -p contrib -i src --codegen javascript Main.idr -o bundle.js
