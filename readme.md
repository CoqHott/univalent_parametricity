# Univalent Parametricity 
Univalent Parametricity for Effective Transport

The repository contains the companion code of the publication
"Equivalences for Free!
Univalent Parametricity for Effective Transport" (submitted to ICFP' 18).

## Structure

- ./theories
  contains the core development with type classes described in Section 5

- ./examples
  contains examples of the use of univalent parametricity

- ./translation
   contains the univalent parametricity translation (Fig 3) and associated proofs 

## Compilation

You need Coq 8.7 to compile the main directory 
and the hoqc compiler from https://github.com/HoTT/ to compile
files in the translation/ directory. 

To compile in the main development:

   set $COQBIN to the path where coqc is, or have Coq 8.7 in your path.

   # make

To compile in translation/:

   # hoqc translation.v

## directory ./theories

This is the formalization discussed in Section 4. 
The structure of the files follows more or less the structure of the paper.

* HoTT.v contains several definitions from the HoTT library; the point of this file is so that our development is independent from hoqc (the HoTT version of Coq provided by the HoTT Library), hence avoiding a separate compiler installation.

Note that HoTT.v contains one admit [hprop_isequiv](https://github.com/CoqHott/univalent_parametricity/blob/master/theories/HoTT.v#L649-L650) that corresponds to a standard result in the HoTT library, but whose proof was too laborious to add independently to this distribution.

* HoTT_axioms.v contains the definition of the univalence axiom and
  functional extensionality.

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

* Vector.v is a copy and paste from Coq's standard library with the
  only modification that it uses universe polymorphism.

* MoreInductive.v deals with more examples of inductive types.

* Examples.v presents examples, most of them are also in the paper.


## directory ./translation/

* Translation.v is a file showing the correctness of the univalent parametricity translation (Fig 3) using a deep embedding
