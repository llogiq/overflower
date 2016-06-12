# overflower

This project contains a compiler plugin and supporting library to allow the 
programmer to annotate their code to declare how integer overflows should be 
dealt with. The annotations should look like this: `#![overflow(panic)]`, 
`#[overflow(wrap)]` or `#[overflow(saturate)]`. Sub-items where overflow 
handling should not be altered can be annotated out with 
`#[overflow(default)]`.

This needs a nightly compiler both for the compiler plugin and the supporting 
library, as the latter makes use of specialization, which is unstable for now.

This is a work in progress, but most things should already be usable.

License: Apache 2.0
