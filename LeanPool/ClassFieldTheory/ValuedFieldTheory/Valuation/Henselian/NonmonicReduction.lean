/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.MonicFactorization
/-!
# the nonmonic reduction branch

This file extracts the Newton--Vieta part of the converse Hensel argument
from the unique-extension criterion.  No uniqueness of valuation extensions is used here: once
all conjugate roots have the same value, a primitive irreducible polynomial
with nonunit leading coefficient has constant reduction.
-/

noncomputable section

open Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

universe u

/-- If the roots of a primitive irreducible polynomial all have the same
value in a splitting field, then the nonunit-leading-coefficient branch has
constant reduction. -/
theorem primitive_irreducible_reduction_natDegree_zero_of_leadingCoeff_nonunit_of_roots_eq
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (B : ValuationSubring L)
    [V.valuation.HasExtension B.valuation]
    (Q : Polynomial V) (hQprim : Q.IsPrimitive)
    (hQirr : Irreducible (Q.map V.subtype))
    [IsSplittingField K L (Q.map V.subtype)]
    (hlead : ¬ IsUnit Q.leadingCoeff)
    (hrootsEq : ∀ {a b : L},
      a ∈ ((Q.map V.subtype).map (algebraMap K L)).roots →
      b ∈ ((Q.map V.subtype).map (algebraMap K L)).roots →
      B.valuation a = B.valuation b) :
    (Q.map (IsLocalRing.residue V)).natDegree = 0 := by
  let p : Polynomial K := Q.map V.subtype
  let F : Polynomial L := p.map (algebraMap K L)
  let roots : Multiset L := F.roots
  have hsplit : F.Splits := by
    change (p.map (algebraMap K L)).Splits
    exact IsSplittingField.splits L p
  have hFnat : F.natDegree = p.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective p
  have hcardpos : 0 < roots.card := by
    rw [← hsplit.natDegree_eq_card_roots, hFnat]
    exact hQirr.natDegree_pos
  obtain ⟨α, hα⟩ := Multiset.card_pos_iff_exists_mem.mp hcardpos
  have hall : ∀ β ∈ roots, B.valuation β = B.valuation α := by
    intro β hβ
    exact hrootsEq hβ hα
  have hconst : IsUnit (Q.coeff 0) := by
    by_contra hconst
    exact
      (DiscreteValuationField.not_all_roots_same_valuation_of_primitive_irreducible_endpoints_nonunit
        V B hQprim hQirr hsplit hlead hconst hα) hall
  have hconstBase : V.valuation (Q.coeff 0 : K) = 1 :=
    (V.valuation_eq_one_iff (Q.coeff 0)).mp hconst
  have hconstTarget :
      B.valuation (algebraMap K L (Q.coeff 0 : K)) = 1 :=
    (Valuation.HasExtension.val_map_eq_one_iff
      V.valuation B.valuation (Q.coeff 0 : K)).mpr hconstBase
  have hleadMax : Q.leadingCoeff ∈ IsLocalRing.maximalIdeal V :=
    (IsLocalRing.mem_maximalIdeal Q.leadingCoeff).mpr hlead
  have hleadBase : V.valuation (Q.leadingCoeff : K) < 1 :=
    (V.valuation_lt_one_iff Q.leadingCoeff).mp hleadMax
  have hleadTarget :
      B.valuation (algebraMap K L (Q.leadingCoeff : K)) < 1 :=
    (Valuation.HasExtension.val_map_lt_one_iff
      V.valuation B.valuation (Q.leadingCoeff : K)).mpr hleadBase
  have hinjVK : Function.Injective (algebraMap V K) := by
    intro x y hxy
    exact Subtype.ext hxy
  have halgVK (x : V) : algebraMap V K x = (x : K) := rfl
  have hleadF :
      F.leadingCoeff = algebraMap K L (Q.leadingCoeff : K) := by
    rw [Polynomial.leadingCoeff_map_of_injective (algebraMap K L).injective]
    change algebraMap K L ((Q.map V.subtype).leadingCoeff) = _
    rw [Polynomial.leadingCoeff_map_of_injective V.subtype_injective]
    rfl
  have hcoeffFactor (j : ℕ) :
      algebraMap K L (Q.coeff j : K) =
        algebraMap K L (Q.leadingCoeff : K) *
          ((roots.map (fun x =>
            Polynomial.X - Polynomial.C x)).prod).coeff j := by
    have hcoeffSplit := congrArg (fun q : Polynomial L => q.coeff j)
      hsplit.eq_prod_roots
    simp only [Polynomial.coeff_C_mul] at hcoeffSplit
    rw [hleadF] at hcoeffSplit
    simpa [roots, F, p, Polynomial.coeff_map, halgVK] using hcoeffSplit
  let t : B.ValueGroup := B.valuation α
  have hroots : ∀ β ∈ roots, B.valuation β = t := by
    intro β hβ
    exact hall β hβ
  have hconstFactor :
      B.valuation (algebraMap K L (Q.coeff 0 : K)) =
        B.valuation (algebraMap K L (Q.leadingCoeff : K)) *
          t ^ roots.card := by
    calc
      B.valuation (algebraMap K L (Q.coeff 0 : K)) =
          B.valuation (F.coeff 0) := by
        simp [F, p, Polynomial.coeff_map]
      _ = B.valuation
          (((-1) ^ F.natDegree) * F.leadingCoeff * roots.prod) := by
        rw [hsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots]
      _ = B.valuation (algebraMap K L (Q.leadingCoeff : K)) *
          B.valuation roots.prod := by
        rw [B.valuation.map_mul, B.valuation.map_mul]
        rw [hleadF]
        simp
      _ = B.valuation (algebraMap K L (Q.leadingCoeff : K)) *
          t ^ roots.card := by
        rw [DiscreteValuationField.valuation_multiset_prod_eq_pow_card_of_eq
          B.valuation t roots hroots]
  have ht : 1 < t := by
    by_contra hnot
    have htle : t ≤ 1 := not_lt.mp hnot
    have hpow : t ^ roots.card ≤ 1 := pow_le_one₀ (bot_le : 0 ≤ t) htle
    have hlt :
        B.valuation (algebraMap K L (Q.leadingCoeff : K)) *
            t ^ roots.card < 1 := by
      exact mul_lt_one_of_lt_of_le hleadTarget hpow
    rw [← hconstFactor, hconstTarget] at hlt
    exact lt_irrefl 1 hlt
  have hleadTargetPos :
      0 < B.valuation (algebraMap K L (Q.leadingCoeff : K)) := by
    apply (Valuation.pos_iff B.valuation).2
    intro hzero
    have hzeroK : (Q.leadingCoeff : K) = 0 := by
      apply (algebraMap K L).injective
      simpa using hzero
    have hzeroV : Q.leadingCoeff = 0 := V.subtype_injective hzeroK
    exact Q.leadingCoeff_ne_zero.mpr hQprim.ne_zero hzeroV
  have hpositiveCoeff (j : ℕ) (hj : 0 < j) :
      V.valuation (Q.coeff j : K) < 1 := by
    have hprod :=
      DiscreteValuationField.valuation_coeff_prod_X_sub_C_lt_coeff_zero_of_one_lt
        B.valuation roots (fun β hβ => by rw [hroots β hβ]; exact ht) j hj
    have htarget :
        B.valuation (algebraMap K L (Q.coeff j : K)) <
          B.valuation (algebraMap K L (Q.coeff 0 : K)) := by
      rw [hcoeffFactor j, hcoeffFactor 0,
        B.valuation.map_mul, B.valuation.map_mul]
      exact mul_lt_mul_of_pos_left hprod hleadTargetPos
    have htargetOne :
        B.valuation (algebraMap K L (Q.coeff j : K)) < 1 := by
      rwa [hconstTarget] at htarget
    exact
      (Valuation.HasExtension.val_map_lt_one_iff
        V.valuation B.valuation (Q.coeff j : K)).mp htargetOne
  apply Polynomial.eq_C_coeff_zero_iff_natDegree_eq_zero.mp
  ext j
  cases j with
  | zero => simp
  | succ j =>
      rw [Polynomial.coeff_map]
      simp only [Polynomial.coeff_C, Nat.succ_ne_zero, ite_false]
      exact (IsLocalRing.residue_eq_zero_iff (Q.coeff (j + 1))).2
        ((V.valuation_lt_one_iff (Q.coeff (j + 1))).mpr
          (hpositiveCoeff (j + 1) (Nat.succ_pos j)))

end Valuations
end AlgebraicNumberTheory

end
