/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The recursively split flag space

This file contains only the neutral ambient vector-space model used by both
the exact flag-graph construction and the big-cell lower-bound argument.
Keeping it separate prevents the exact Proposition 3.1 chain from depending
on the lower-bound construction merely to obtain this coordinate model.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

public section

namespace MooreBound

open Module

namespace DegreeDiameter

universe u

/-- The recursively split `(2*k+1)`-dimensional coordinate space. -/
abbrev FlagSpace (K : Type u) : ℕ → Type u
  | 0 => Fin 1 → K
  | k + 1 => (Fin 2 → K) × FlagSpace K k

/-- The dimension of `FlagSpace`, kept recursive so adjoining its first two
coordinates remains definitionally transparent. -/
@[expose] def flagDim : ℕ → ℕ
  | 0 => 1
  | k + 1 => flagDim k + 2

theorem flagDim_eq (k : ℕ) : flagDim k = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [flagDim, ih]; omega

section LinearAlgebra

variable (K : Type u) [Field K]

instance flagSpaceAddCommGroup : ∀ k : ℕ, AddCommGroup (FlagSpace K k)
  | 0 => inferInstanceAs (AddCommGroup (Fin 1 → K))
  | k + 1 =>
      letI := flagSpaceAddCommGroup k
      inferInstanceAs (AddCommGroup ((Fin 2 → K) × FlagSpace K k))

instance flagSpaceModule : ∀ k : ℕ, Module K (FlagSpace K k)
  | 0 => inferInstanceAs (Module K (Fin 1 → K))
  | k + 1 =>
      letI := flagSpaceModule k
      inferInstanceAs (Module K ((Fin 2 → K) × FlagSpace K k))

noncomputable instance flagSpaceFiniteDimensional : ∀ k : ℕ,
    FiniteDimensional K (FlagSpace K k)
  | 0 => inferInstanceAs (FiniteDimensional K (Fin 1 → K))
  | k + 1 =>
      letI := flagSpaceFiniteDimensional k
      inferInstanceAs (FiniteDimensional K ((Fin 2 → K) × FlagSpace K k))

theorem finrank_flagSpace (k : ℕ) : finrank K (FlagSpace K k) = flagDim k := by
  induction k with
  | zero => simp [FlagSpace, flagDim]
  | succ k ih =>
      simp only [FlagSpace, flagDim, Module.finrank_prod]
      have htwo : finrank K (Fin 2 → K) = 2 := by simp
      rw [htwo, ih]
      omega

end LinearAlgebra

section Cardinality

variable (K : Type u)

instance flagSpaceFinite [Finite K] : ∀ k : ℕ, Finite (FlagSpace K k)
  | 0 => inferInstanceAs (Finite (Fin 1 → K))
  | k + 1 =>
      letI := flagSpaceFinite k
      inferInstanceAs (Finite ((Fin 2 → K) × FlagSpace K k))

theorem natCard_flagSpace (k : ℕ) :
    Nat.card (FlagSpace K k) = Nat.card K ^ flagDim k := by
  induction k with
  | zero => simp [FlagSpace, flagDim, Nat.card_fun]
  | succ k ih =>
      simp only [FlagSpace, flagDim, Nat.card_prod, ih]
      rw [Nat.card_fun]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      rw [← pow_add]
      congr 1
      omega

end Cardinality

end DegreeDiameter

end MooreBound
