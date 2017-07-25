# Univalent Parametricity 
Univalent Parametricity for Effective Transport

The repository contains the companion code of the publication
[Equivalences for Free!
Univalent Parametricity for Effective Transport](https://hal.inria.fr/hal-01559073)

## Structure

- ./
  contains this readme file and the development with type classes described in Section 5

- ./translation
   contains the univalent parametricity translation (Fig 3) and associated proofs 

## Compilation

You need Coq 8.6 to compile the main directory 
and the hoqc compiler from https://github.com/HoTT/ to compile
files in the translation/ directory. 

To compile in the main directory:

   set $COQBIN to the path where coqc is, or have Coq 8.6 in your path.

```
   $ make
```

To compile in translation/:

```
  $ hoqc translation.v
```
  
## directory ./

This is the formalization discussed in Section 5. 
The structure of the files follows more or less the structure of the paper.

* Vector.v and HoTT.v are auxiliary files. 

HoTT.v contains several definitions from the HoTT library; the point of this file is so that our development is independent from hoqc (the HoTT version of Coq provided by the HoTT Library), hence avoiding a separate compiler installation.

Note that HoTT.v contains one admit that corresponds to a standard result in the HoTT library, but whose proof was too laborious to add independently to this distribution.

* UR.v contains the definition of the univalent logical relation using type classes.

* FP.v contains the proof that constructors of Coq enjoy the fundamental property of the univalent logical relation.

As mentioned above, keeping these two admits is a design choice to make the main distribution independent from hoqc.

* Examples.v presents examples, most of them are also in the paper.

* MoreInductive.v deals with more examples of inductive types.


## directory ./translation/

* Translation.v is a file showing the correctness of the univalent parametricity translation (Fig 3) using a deep embedding
