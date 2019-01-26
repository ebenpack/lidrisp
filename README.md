# pamperscript

Dependently typed, type-safe HTML library.

This is still very much a work-in-progress, but the idea is that invalid HTML
simply won't typecheck. E.g. the w3 spec specifies that the the `<address>`
element's content model (i.e. what content may be included as children and
descendants of the element) is:  "Flow content, but with no heading content
descendants, no sectioning content descendants, and no header, footer, or
address element descendants". With pamperscript, an `<address>` element that
doesn't meet these criteria (e.g. if it were to contain an address elements
descendant) won't typecheck. It won't compile.

    # Build
    > idris -p contrib -i src --codegen javascript Main.idr -o bundle.js
