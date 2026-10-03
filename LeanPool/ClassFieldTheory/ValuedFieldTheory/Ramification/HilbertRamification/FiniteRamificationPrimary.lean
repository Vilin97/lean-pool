/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RamificationPrimeToResidueTorsion
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup
/-!
# Finite ramification groups in positive and zero residue characteristic

In positive residue characteristic p, factoring a finite annihilating order
as p^a times a prime-to-p integer reduces the assertion to prime-to-residue
torsion triviality. In residue characteristic zero, every positive finite
order is nonzero in the residue field, so the ramification group is trivial.

All groups and principal-unit conditions are the actual valuation-subring
constructions. Only finiteness of the ramification group is used;
no normality, Henselianity, discreteness, perfectness, or finite residue field
is required.
-/

@[expose] public section

namespace RamificationTheory.HilbertRamification.ValuationSubring

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The actual finite ramification group is a p-group in residue characteristic p. -/
theorem ramificationGroup_isPGroup_of_residueChar
    (A : _root_.ValuationSubring L) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p] [Finite (ramificationGroup K A)] :
    IsPGroup p (ramificationGroup K A) := by
  intro σ
  obtain ⟨a, m, hm, hfactor⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos σ).ne' p (Fact.out : p.Prime).ne_one
  refine ⟨a, ?_⟩
  apply ramificationGroup_eq_one_of_pow_eq_one_of_residue_natCast_ne_zero K A
    (σ ^ (p ^ a)) m ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) p m).not.mpr hm)
  rw [← pow_mul, ← hfactor]
  exact pow_orderOf_eq_one σ

/-- The actual finite ramification group is trivial in residue characteristic zero. -/
theorem ramificationGroup_eq_bot_of_residueCharZero
    (A : _root_.ValuationSubring L) [CharZero (IsLocalRing.ResidueField A)]
    [Finite (ramificationGroup K A)] :
    ramificationGroup K A = ⊥ := by
  apply bot_unique
  intro σ hσ
  change σ = 1
  let τ : ramificationGroup K A := ⟨σ, hσ⟩
  have hτ : τ = 1 :=
    ramificationGroup_eq_one_of_pow_eq_one_of_residue_natCast_ne_zero K A
      τ (orderOf τ) (Nat.cast_ne_zero.mpr (orderOf_pos τ).ne') (pow_orderOf_eq_one τ)
  exact congrArg (fun t : ramificationGroup K A => (t : inertiaGroup K A)) hτ

end RamificationTheory.HilbertRamification.ValuationSubring
