# Synopsis

A Prolog interpreter designed to run on some form of a continuation
monad. The goal is to make it a general monad transformer which is
reasonably standard-compliant with module support, as well as
reasonably efficient for pragmatic use case.

The support for modules is trickier that it should be because no major
Prolog implementations seems to be strictly following the standard in
this regard. I'm vaguely imagining to follow that of SWI-prolog
because that's what I've used most often.

The code was orignially based on "prolog" package by Matthias Bartsch.
