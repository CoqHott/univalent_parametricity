# Univalent Parametricity 
Univalent Parametricity for Effective Transport

The repository contains the companion code of the publication
"Equivalences for Free!
Univalent Parametricity for Effective Transport" (accepted at ICFP' 18).

## Structure

- ./theories
  contains the core development with type classes described in Section 5

- ./examples
  contains examples of the use of univalent parametricity

- ./translation
   contains the univalent parametricity translation (Fig 3) and associated proofs 

## Compilation

Hereafter, "the main development" denotes the directories theories/ and examples/.

You need Coq 8.8.0 to compile the main development. To compile the file in the translation/ directory, you need the hoqc compiler (the HoTT version of Coq provided by the HoTT Library -- available at https://github.com/HoTT/HoTT).

To compile the main development:

   set `$COQBIN` to the path where coqc is (`export COQBIN=/.../bin/`),
   or have Coq 8.8.0 in your path. Then, in the / directory, run:

	make

To compile translation/ run (requires hoqc):

    hoqc translation/Translation.v

## directory ./theories

This is the core development with type classes described in Section 5. 
The structure of the files follows more or less the structure of the paper.

* HoTT.v contains several definitions from the HoTT library; the point of this file is so that the main development is independent from hoqc.

Note that HoTT.v contains one admit
([hprop_isequiv](https://github.com/CoqHott/univalent_parametricity/blob/master/theories/HoTT.v#L649-L650)),
which corresponds to a standard result in the HoTT library, but whose
proof was too laborious to be added independently to this distribution.

* HoTT_axioms.v contains the definition of the univalence and
  functional extensionality axioms.

* UR.v contains the definition of the univalent logical relation using type classes.

* URTactics.v provides a bunch of tactics for automation of typeclass
resolution

* FP.v contains the proof that constructors of Coq enjoy the
fundamental property of the univalent logical relation.

* ADT.v contains tactics to automatize proofs that abstract data types are
univalent.

* Record.v contains tactics to automatize proofs that record types are
univalent.

* Transportable.v contains instances of the Transportable type class
  that allows for more computational rewriting.

## directory ./examples

* Vector.v is a copy-paste from Coq's standard library with the
  only modification that it uses universe polymorphism.

* Examples.v presents examples, most of them in the paper.

* MoreInductive.v deals with more examples of inductive types.


## directory ./translation

* Translation.v is a file showing the correctness of the univalent parametricity translation (Fig 3) using a deep embedding
