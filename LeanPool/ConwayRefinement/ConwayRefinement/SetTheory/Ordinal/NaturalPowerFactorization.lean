/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.MultiplicativelyPrincipal

/-!
# Canonical factors in natural powers

The natural power of an additive-principal ordinal, multiplied by its residual factor,
has no canonical multiplicative factor below the original principal factor. Ordinary and natural
multiplication by that principal factor therefore agree. An additional ordinal with a larger
principal factor preserves this assertion.

These are the ordinal calculations used in the cancellation argument of Berarducci, Lemma 8.2;
they do not depend on a series ring or a valuation.
-/

public noncomputable section
open Ordinal
universe u

namespace Ordinal
private def GoodAt (w : Ordinal.{u}) (Y : NatOrdinal.{u}) : Prop :=
  IsAdditivelyPrincipal Y.val ∧
    ∀ t ∈ (log omega0 Y.val).additivePrincipalTerms, w ≤ t

private theorem GoodAt.one (w : Ordinal.{u}) : GoodAt w 1 := by
  refine ⟨isAdditivelyPrincipal_iff.mpr ⟨0, by simp⟩, fun t ht ↦ ?_⟩
  rw [show ((1 : NatOrdinal.{u}).val) = 1 from rfl, log_one_right,
    additivePrincipalTerms_zero] at ht
  exact absurd ht List.not_mem_nil

private theorem GoodAt.mul {w : Ordinal.{u}} {Y Z : NatOrdinal.{u}}
    (hY : GoodAt w Y) (hZ : GoodAt w Z) : GoodAt w (Y * Z) := by
  have hprod : (NatOrdinal.of Y.val * NatOrdinal.of Z.val).val = (Y * Z).val := by
    rw [NatOrdinal.of_val, NatOrdinal.of_val]
  constructor
  · obtain ⟨e, he⟩ := isAdditivelyPrincipal_iff.mp hY.1
    obtain ⟨f, hf⟩ := isAdditivelyPrincipal_iff.mp hZ.1
    refine isAdditivelyPrincipal_iff.mpr ⟨(NatOrdinal.of e + NatOrdinal.of f).val, ?_⟩
    rw [← hprod, he, hf, NatOrdinal.of_omega0_opow, NatOrdinal.of_omega0_opow,
      ← NatOrdinal.wpow_add, NatOrdinal.val_wpow]
  · intro t ht
    rw [← hprod] at ht
    rcases mem_additivePrincipalTerms_log_natMul hY.1 hZ.1 ht with h | h
    · exact hY.2 t h
    · exact hZ.2 t h

private theorem GoodAt.pow {w : Ordinal.{u}} {Y : NatOrdinal.{u}} (hY : GoodAt w Y) (n : ℕ) :
    GoodAt w (Y ^ n) := by
  induction n with
  | zero => simpa using GoodAt.one w
  | succ n ih => rw [pow_succ]; exact ih.mul hY

namespace AdditivePrincipalAboveOne
private theorem goodAt_value (B : AdditivePrincipalAboveOne.{u}) :
    GoodAt (log omega0 B.principalFactor) (NatOrdinal.of B.val) :=
  ⟨B.2.1, fun _ ht ↦ B.log_principalFactor_le_of_mem_terms ht⟩

private theorem goodAt_residual (B : AdditivePrincipalAboveOne.{u}) :
    GoodAt (log omega0 B.principalFactor) (NatOrdinal.of B.residualFactor) :=
  ⟨B.residualFactor_isAdditivelyPrincipal,
    fun _ ht ↦ B.log_principalFactor_le_of_mem_terms
      (B.mem_terms_of_mem_terms_log_residualFactor ht)⟩

/-- A natural power times the residual factor is additive principal, and ordinary multiplication
by the principal factor agrees with natural multiplication. -/
theorem power_residual_factorization (B : AdditivePrincipalAboveOne.{u}) (m : ℕ) :
    IsAdditivelyPrincipal (NatOrdinal.of B.val ^ m * NatOrdinal.of B.residualFactor).val ∧
      ((NatOrdinal.of B.val ^ m * NatOrdinal.of B.residualFactor) *
        NatOrdinal.of B.principalFactor).val =
        (NatOrdinal.of B.val ^ m * NatOrdinal.of B.residualFactor).val * B.principalFactor := by
  have h := (B.goodAt_value.pow m).mul B.goodAt_residual
  refine ⟨h.1, ?_⟩
  obtain ⟨e, he⟩ := isInfiniteMultiplicativelyPrincipal_iff.mp
    B.principalFactor_isInfiniteMultiplicativelyPrincipal
  have hp : IsAdditivelyPrincipal (log omega0 B.principalFactor) := by
    rw [he, log_opow one_lt_omega0]
    exact isAdditivelyPrincipal_omega0_opow e
  have hh := natOrdinal_of_mul_wpow_eq_mul_of_log_terms hp h.1 h.2
  rw [B.principalFactor_isInfiniteMultiplicativelyPrincipal.isAdditivelyPrincipal.opow_log_self,
    NatOrdinal.of_val] at hh
  exact (congrArg NatOrdinal.val hh).symm

/-- The same factorisation holds after adjoining a factor with no smaller principal factor. -/
theorem power_residual_mul_factorization (B C : AdditivePrincipalAboveOne.{u})
    (hp : B.principalFactor ≤ C.principalFactor) (m : ℕ) :
    IsAdditivelyPrincipal
        (NatOrdinal.of B.val ^ m * NatOrdinal.of B.residualFactor * NatOrdinal.of C.val).val ∧
      ((NatOrdinal.of B.val ^ m * NatOrdinal.of B.residualFactor * NatOrdinal.of C.val) *
        NatOrdinal.of B.principalFactor).val =
        (NatOrdinal.of B.val ^ m * NatOrdinal.of B.residualFactor * NatOrdinal.of C.val).val *
          B.principalFactor := by
  have hC : GoodAt (log omega0 B.principalFactor) (NatOrdinal.of C.val) :=
    ⟨C.2.1, fun _ ht ↦ (log_mono_right omega0 hp).trans
      (C.log_principalFactor_le_of_mem_terms ht)⟩
  have h := ((B.goodAt_value.pow m).mul B.goodAt_residual).mul hC
  refine ⟨h.1, ?_⟩
  obtain ⟨e, he⟩ := isInfiniteMultiplicativelyPrincipal_iff.mp
    B.principalFactor_isInfiniteMultiplicativelyPrincipal
  have hb : IsAdditivelyPrincipal (log omega0 B.principalFactor) := by
    rw [he, log_opow one_lt_omega0]
    exact isAdditivelyPrincipal_omega0_opow e
  have hh := natOrdinal_of_mul_wpow_eq_mul_of_log_terms hb h.1 h.2
  rw [B.principalFactor_isInfiniteMultiplicativelyPrincipal.isAdditivelyPrincipal.opow_log_self,
    NatOrdinal.of_val] at hh
  exact (congrArg NatOrdinal.val hh).symm
/-- A natural product of factors with no smaller principal factor also has no smaller principal
factor, whenever that product is greater than one. -/
theorem principalFactor_le_of_naturalProd (B C : AdditivePrincipalAboveOne.{u})
    (l : Multiset AdditivePrincipalAboveOne.{u})
    (hl : ∀ y ∈ l, B.principalFactor ≤ y.principalFactor)
    (hC : NatOrdinal.of C.val = (l.map fun y ↦ NatOrdinal.of y.val).prod) :
    B.principalFactor ≤ C.principalFactor := by
  have hgood : GoodAt (log omega0 B.principalFactor)
      (l.map fun y ↦ NatOrdinal.of y.val).prod := by
    clear hC
    induction l using Multiset.induction with
    | empty => simpa using GoodAt.one (log omega0 B.principalFactor)
    | cons a t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      apply GoodAt.mul
      · exact ⟨a.2.1, fun z hz ↦
          (log_mono_right omega0 (hl a (Multiset.mem_cons_self a t))).trans
            (a.log_principalFactor_le_of_mem_terms hz)⟩
      · exact ih fun y hy ↦ hl y (Multiset.mem_cons_of_mem hy)
  rw [← hC] at hgood
  have h := hgood.2 _ C.log_principalFactor_mem_terms
  have hpow := opow_le_opow_right omega0_pos h
  simpa only
    [B.principalFactor_isInfiniteMultiplicativelyPrincipal.isAdditivelyPrincipal.opow_log_self,
      C.principalFactor_isInfiniteMultiplicativelyPrincipal.isAdditivelyPrincipal.opow_log_self]
    using hpow

end AdditivePrincipalAboveOne
end Ordinal
