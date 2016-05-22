# overflower

This project aims to produce a compiler plugin and supporting library to allow the programmer
to annotate their code to declare how integer overflows should be dealt with. The annotations
should look like this: `#![overflow(panic)]` or `#[overflow(wrap)]`.

This needs a nightly compiler both for the compiler plugin and the supporting library, as the
latter makes use of specialization, which is unstable for now.

This is a work in progress.

License: Apache 2.0
