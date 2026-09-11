/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TwoSidedIdeal.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Lattice
public import LeanPool.Koethe.Counterexample

/-!
# Disproof of the Köthe conjecture in Krempa's matrix form

Köthe's conjecture (1930) asks whether the sum of two nil left ideals of a ring is always
nil, equivalently whether every ring has a largest nil left ideal. Krempa (1972) showed it
equivalent to several other statements, among them that for every ring `R` and nil two-sided
ideal `I` the matrix ideal `M_n(I)` is nil in `M_n(R)` (already for `n = 2`).

This file states that matrix form exactly as Google DeepMind's Formal Conjectures does and
proves its negation from `KoetheCounterexample.counterexample`. The definitions `Koethe.IsNil`
and `Koethe.KotheRadical` and the bracketed conjecture inside
`Koethe.KotherConjecture.variants.general_matrix.disproof` are copied verbatim from
`FormalConjectures/Wikipedia/Koethe.lean` in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`9cbe1d3c12998c786b7c2cd99ce28a21b6631f66` (Copyright 2025 The Formal Conjectures Authors,
Apache-2.0), where `KotherConjecture.variants.general_matrix` is registered as a research-open
statement.

Since `M_n(I)` is the sum of its `n` column left ideals, each of which is nil when `I` is,
Köthe's original statement implies the matrix form; the counterexample therefore also refutes
the conjecture as originally stated. That implication is a standard argument and is not part
of this formal development.
-/

@[expose] public section

open Ideal TwoSidedIdeal Polynomial

open Matrix

variable {R : Type*}

variable [Ring R]

namespace Koethe

/-- Say a subset `I` of a ring `R` is nilpotent if all its elements are nilpotent. -/
def IsNil {S : Type*} [SetLike S R] (I : S) := ∀ i ∈ I, IsNilpotent i

variable (R) in
/-- The *Kothe Radical* of a ring `R` is the sum of all (two-sided) nil ideals of `R`.
Tags: Kothe Radical, upper nilradical -/
def KotheRadical : TwoSidedIdeal R := sSup {I : TwoSidedIdeal R | IsNil I}

end Koethe

open scoped Classical in
/--
**Disproof of the Köthe conjecture in Krempa's matrix form** (the
`KotherConjecture.variants.general_matrix` statement of Formal Conjectures): it is not the case
that for every ring `R`, every nil two-sided ideal `I` and every finite index type `n`, the
matrix ideal `M_n(I)` is nil.
-/
theorem Koethe.KotherConjecture.variants.general_matrix.disproof :
    ¬ (∀ {R : Type*} [Ring R] {I : TwoSidedIdeal R},
      IsNil I → ∀ (n : Type*) [Fintype n], IsNil (matrix n I)) := by
  classical
  intro h
  obtain ⟨S, hS, I, hI, W, hW, hn⟩ := KoetheCounterexample.counterexample
  let _ : Ring S := hS
  have ht := @h S hS I hI (ULift (Fin 2)) inferInstance
  let _ : DecidableEq (ULift (Fin 2)) := Classical.decEq _
  let e := Matrix.reindexAlgEquiv ℕ S (Equiv.ulift.symm : Fin 2 ≃ ULift (Fin 2))
  apply hn
  apply (IsNilpotent.map_iff e.injective).mp
  apply ht (e W)
  rw [TwoSidedIdeal.mem_matrix] at hW ⊢
  intro i j
  exact hW i.down j.down
