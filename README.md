# **Verified-Kisa**
A verified pretty-printer combinator library implemented in C.

## Build Requirements
To build this project, you'll need the Coq theorem prover and the VST library.
- See the Coq download page for instruction to download Coq: https://coq.inria.fr/download
- Software Foundations has instructions for installing VST: https://softwarefoundations.cis.upenn.edu/vc-current/Preface.html#lab3

## Project Layout
- `verified_printer/Format.v`: Part of the reference library for all the tools for working with Formats and pretty-printer combinators.
- `verified_printer/FormatTrivial.v`: Implementation of Doc functions.
- `verified_printer/Doc.v`: Definition of Doc structure.
- `printer_files/compiled_format.v`: Library code, compiled using ```clightgen```.
- `proof/format_specs.v`: The basic definitions necessary for proving theorems about Formats and combinators, tools for working with memory predicates, as well as program specifications related to Formats and combinators.
- `proof/list_specs.v`: Definitions for working with lists of Formats, as well as program specifications related to Doc functions.
- `proof/format_std_proof.v`: The proofs of functions’ compliance with their specifications for functions from the standard library, as well as functions manipulating lists of strings.
- `proof/format_combinator_proof.v`: The proofs of functions’ compliance with their specifications for pretty-printing combinators.
- `proof/list_trivial_proof.v`: The proofs of functions’ compliance with their specifications for Doc functions.
- `proof/format_proof.v`: The proofs of functions’ compliance with their specifications for all other functions working with formats.
- `proof/HahnBase.v`: Slightly modified part of the CoqHahn library, containing a number of useful tactics and lemmas for simplifying some proofs.

## Papers

* [Proof of correctness of the functional implementation of the pretty-printer combinator libraries with choice. ](https://se.math.spbu.ru/thesis/texts/Korolihin_Vladimir_Igorevich_Bachelor_Report_2020_text.pdf) (Thesis). Vladimir Korolihin
* [Designing and implementing combinator languages](https://www.cs.tufts.edu/~nr/cs257/archive/doaitse-swierstra/AFP3.pdf) (AFP 1998). S Doaitse Swierstra et al.
* [Polynomial-Time Optimal Pretty-Printing Combinators with Choice](http://dx.doi.org/10.1007/978-3-662-46823-4_21) (PSI 2014). Anton Podkopaev, Dmitri Boulytchev.