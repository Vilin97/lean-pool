/-
Copyright (c) 2026 tangentstorm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tangentstorm
-/
import LeanPool.Leansieve.ASeq.ASeq
import LeanPool.Leansieve.PrimeGen.PrimeGen
import LeanPool.Leansieve.PrimeSieve.PrimeSieve
import LeanPool.Leansieve.Rake.Rake
import LeanPool.Leansieve.RakeMap.RakeMap
import LeanPool.Leansieve.RakeSieve.RakeSieve

/-!
# leansieve: a formally verified prime number sieve

A formalization of natural-number sieves in Lean 4, modeling the natural numbers
as collections of arithmetic sequences. An `ASeq` is a single arithmetic sequence
`k + d * n`; a `Rake` is a sorted collection of arithmetic sequences sharing the
same delta; a `RakeMap` bijects a rake with a predicate-defined subset of the
naturals. On top of these, `PrimeSieve` proves the generic correctness logic of a
prime sieve (each step produces the next consecutive prime, skipping none), and
`RakeSieve` instantiates that logic into a concrete, sieve-of-Eratosthenes-style
prime generator.

Source: url:https://github.com/tangentstorm/leansieve
Authors: tangentstorm
Status: verified
Main declarations: `hs_suffice`, `c_prime`, `no_skipped_prime`, `RakeSieve.init`, `RakeSieve.next`
Tags: prime-sieve, number-theory, arithmetic-sequences, eratosthenes
MSC: 11A41
-/
