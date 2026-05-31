/-
Copyright (c) 2023 Hu Yongle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/

import LeanPool.Neukirch.ExtensionOfDedekindDomains
import LeanPool.Neukirch.HilbertRamificationTheory

/-!
# Neukirch's Algebraic Number Theory: Hilbert ramification theory

Source: url:https://github.com/jjdishere/neukirch
Authors: Hu Yongle
Status: verified
Main declarations: `NumberField.ramificationIdx_mul_inertiaDeg_of_isGalois`
Tags: number-theory, algebraic-number-theory, ramification, galois-theory
MSC: 11R32, 11S15, 13B25
-/

/-!
## Mathematical overview

This project formalizes a portion of Hilbert's ramification theory for Galois
extensions of number fields, following Chapter I of Neukirch's *Algebraic Number
Theory*. The development was carried out in the `jjdishere/neukirch` repository;
only its fully proved, complete results are vendored here.

## Main results

- `NumberField.ramificationIdx_mul_inertiaDeg_of_isGalois`: the fundamental
  identity `g · e · f = [L : K]` for a Galois extension `L / K` of number fields,
  where `g` is the number of primes over `p`, and `e`, `f` are the common
  ramification index and inertia degree.
- `NumberField.finrank_eq_ramificationIdx_mul_inertiaDeg`: when `P` is the unique
  prime lying over `p`, the degree `[L : K]` equals `e · f`.
- `NumberField.DecompositionGroup` and `NumberField.InertiaGroup`: the
  decomposition and inertia subgroups of the Galois group, together with their
  fixed fields and the order computations
  `NumberField.DecompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg` and
  `NumberField.InertiaGroup_card_eq_ramificationIdx`.
- `NumberField.IsMaximal_conjugates`: the Galois group acts transitively on the
  primes lying over a fixed prime `p`.
- `NumberField.InertiaField_aut_equiv_ResidueField_aut`: the Galois group of the
  inertia field over `K` is isomorphic to the Galois group of the residue field
  extension.
- `Ideal.ramificationIdx_algebra_tower_of_eq` and
  `Ideal.inertiaDeg_algebra_tower_of_eq`: multiplicativity of ramification index
  and inertia degree in a tower of Dedekind domains.
-/
