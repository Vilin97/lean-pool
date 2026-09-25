/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionReduction
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.MonicFactorization
import Mathlib.GroupTheory.OrderOfElement
/-!
# primitive irreducible reductions

This file supplies the last Galois/Newton-polygon input in the converse of
the unique-extension criterion.  Uniqueness of the extension valuation ring makes it invariant
under the finite Galois group of a splitting field.  Consequently conjugate
roots have the same value.  Vieta's formulas then show that a primitive
irreducible polynomial has either full-degree reduction or constant
reduction; in the full-degree case the monic normalization has no coprime
nonconstant residual factorization.
-/

noncomputable section

open Polynomial

namespace AlgebraicNumberTheory
namespace Valuations
open ValuationTheory.Valuations

universe u

/-- A finite-order ground-field automorphism stabilizing a valuation subring
preserves its canonical valuation exactly.  Stabilization first preserves
the order relation on values.  A strict change would iterate around the
finite orbit of the automorphism and give a strict cycle. -/
theorem valuation_algEquiv_eq_of_unique_extension_of_finiteDimensional
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation)
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (σ : L ≃ₐ[K] L) (x : L) :
    W.valuation (σ x) = W.valuation x := by
  have hle (a b : L) :
      W.valuation a ≤ W.valuation b ↔
        W.valuation (σ a) ≤ W.valuation (σ b) := by
    constructor
    · intro hab
      obtain ⟨c, hc⟩ := (W.valuation_le_iff a b).1 hab
      apply (W.valuation_le_iff (σ a) (σ b)).2
      refine ⟨⟨σ (c : L), ?_⟩, ?_⟩
      · exact
          (algEquiv_mem_valuationSubring_iff_of_unique_extension
            V W hW huniq σ (c : L)).2 c.2
      · change σ (c : L) * σ b = σ a
        rw [← map_mul, hc]
    · intro hab
      obtain ⟨c, hc⟩ := (W.valuation_le_iff (σ a) (σ b)).1 hab
      apply (W.valuation_le_iff a b).2
      refine ⟨⟨σ⁻¹ (c : L), ?_⟩, ?_⟩
      · exact
          (algEquiv_mem_valuationSubring_iff_of_unique_extension
            V W hW huniq σ⁻¹ (c : L)).2 c.2
      · apply σ.injective
        simpa using hc
  have hlt (a b : L) :
      W.valuation a < W.valuation b ↔
        W.valuation (σ a) < W.valuation (σ b) := by
    simpa only [lt_iff_not_ge] using not_congr (hle b a)
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  obtain ⟨n, hn, hσn⟩ := hfin.exists_pow_eq_one
  rcases lt_trichotomy (W.valuation (σ x)) (W.valuation x) with
      hdown | heq | hup
  · have hstep : ∀ m : ℕ,
        W.valuation ((σ ^ (m + 1)) x) <
          W.valuation ((σ ^ m) x) := by
      intro m
      induction m with
      | zero => simpa using hdown
      | succ m ih =>
          have hmapped := (hlt ((σ ^ (m + 1)) x) ((σ ^ m) x)).1 ih
          simpa [pow_succ'] using hmapped
    have hcycle : ∀ m : ℕ,
        W.valuation ((σ ^ (m + 1)) x) < W.valuation x := by
      intro m
      induction m with
      | zero => simpa using hdown
      | succ m ih => exact (hstep (m + 1)).trans ih
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have := hcycle m
    rw [hσn] at this
    simp at this
  · exact heq
  · have hstep : ∀ m : ℕ,
        W.valuation ((σ ^ m) x) <
          W.valuation ((σ ^ (m + 1)) x) := by
      intro m
      induction m with
      | zero => simpa using hup
      | succ m ih =>
          have hmapped := (hlt ((σ ^ m) x) ((σ ^ (m + 1)) x)).1 ih
          simpa [pow_succ'] using hmapped
    have hcycle : ∀ m : ℕ,
        W.valuation x < W.valuation ((σ ^ (m + 1)) x) := by
      intro m
      induction m with
      | zero => simpa using hup
      | succ m ih => exact ih.trans (hstep (m + 1))
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have := hcycle m
    rw [hσn] at this
    simp at this

/-- Roots of one irreducible ground-field polynomial have the same canonical
value in a finite normal splitting field with a unique extension valuation
ring. -/
theorem valuation_eq_on_roots_of_irreducible_of_unique_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Normal K L] [FiniteDimensional K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation)
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (p : Polynomial K) (hirr : Irreducible p)
    {a b : L}
    (ha : a ∈ (p.map (algebraMap K L)).roots)
    (hb : b ∈ (p.map (algebraMap K L)).roots) :
    W.valuation a = W.valuation b := by
  have hpL0 : p.map (algebraMap K L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).2 hirr.ne_zero
  have haeval : aeval a p = 0 := by
    have h := (Polynomial.mem_roots hpL0).1 ha
    simpa [aeval_def, Polynomial.eval_map] using h
  have hbeval : aeval b p = 0 := by
    have h := (Polynomial.mem_roots hpL0).1 hb
    simpa [aeval_def, Polynomial.eval_map] using h
  have hmin : minpoly K a = minpoly K b := by
    rw [← minpoly.eq_of_irreducible hirr haeval,
      ← minpoly.eq_of_irreducible hirr hbeval]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit L).1 hmin
  calc
    W.valuation a = W.valuation (σ b) := congrArg W.valuation hσ.symm
    _ = W.valuation b :=
      valuation_algEquiv_eq_of_unique_extension_of_finiteDimensional
        V W hW huniq σ b

/-- If all roots of a split monic product have value strictly larger than
one, every positive-degree coefficient has value strictly smaller than the
constant coefficient. -/
theorem valuation_coeff_prod_X_sub_C_lt_coeff_zero_of_one_lt
    {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (s : Multiset L)
    (hs : ∀ α ∈ s, 1 < w α) (j : ℕ) (hj : 0 < j) :
    w (((s.map (fun α => Polynomial.X - Polynomial.C α)).prod).coeff j) <
      w (((s.map (fun α => Polynomial.X - Polynomial.C α)).prod).coeff 0) :=
  DiscreteValuationField.valuation_coeff_prod_X_sub_C_lt_coeff_zero_of_one_lt
    w s hs j hj

open DiscreteValuationField renaming
  not_all_roots_same_valuation_of_primitive_irreducible_endpoints_nonunit →
    not_all_roots_same_valuation_of_primitive_irreducible_endpoints_nonunit in
/-- In the nonmonic branch of Artin's argument, uniqueness on the splitting
field forces every root to have value greater than one.  Vieta's formula then
puts every positive-degree coefficient in the maximal ideal, so the
reduction is constant. -/
theorem primitive_irreducible_reduction_natDegree_zero_of_leadingCoeff_nonunit
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation)
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (Q : Polynomial V) (hQprim : Q.IsPrimitive)
    (hQirr : Irreducible (Q.map V.subtype))
    [IsSplittingField K L (Q.map V.subtype)]
    (hlead : ¬ IsUnit Q.leadingCoeff) :
    (Q.map (IsLocalRing.residue V)).natDegree = 0 := by
  let : V.valuation.HasExtension W.valuation := hW
  let p : Polynomial K := Q.map V.subtype
  let F : Polynomial L := p.map (algebraMap K L)
  let roots : Multiset L := F.roots
  let : FiniteDimensional K L := IsSplittingField.finiteDimensional L p
  let : Normal K L := Normal.of_isSplittingField p
  have hsplit : F.Splits := by
    change (p.map (algebraMap K L)).Splits
    exact IsSplittingField.splits L p
  have hFnat : F.natDegree = p.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective p
  have hcardpos : 0 < roots.card := by
    rw [← hsplit.natDegree_eq_card_roots, hFnat]
    exact hQirr.natDegree_pos
  obtain ⟨α, hα⟩ := Multiset.card_pos_iff_exists_mem.mp hcardpos
  have hall : ∀ β ∈ roots, W.valuation β = W.valuation α := by
    intro β hβ
    exact valuation_eq_on_roots_of_irreducible_of_unique_extension
      V W hW huniq p hQirr hβ hα
  have hconst : IsUnit (Q.coeff 0) := by
    by_contra hconst
    exact
      (not_all_roots_same_valuation_of_primitive_irreducible_endpoints_nonunit
        V W hQprim hQirr hsplit hlead hconst hα) hall
  have hconstBase : V.valuation (Q.coeff 0 : K) = 1 :=
    (V.valuation_eq_one_iff (Q.coeff 0)).mp hconst
  have hconstTarget :
      W.valuation (algebraMap K L (Q.coeff 0 : K)) = 1 :=
    (Valuation.HasExtension.val_map_eq_one_iff
      V.valuation W.valuation (Q.coeff 0 : K)).mpr hconstBase
  have hleadMax : Q.leadingCoeff ∈ IsLocalRing.maximalIdeal V :=
    (IsLocalRing.mem_maximalIdeal Q.leadingCoeff).mpr hlead
  have hleadBase : V.valuation (Q.leadingCoeff : K) < 1 :=
    (V.valuation_lt_one_iff Q.leadingCoeff).mp hleadMax
  have hleadTarget :
      W.valuation (algebraMap K L (Q.leadingCoeff : K)) < 1 :=
    (Valuation.HasExtension.val_map_lt_one_iff
      V.valuation W.valuation (Q.leadingCoeff : K)).mpr hleadBase
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
  let t : W.ValueGroup := W.valuation α
  have hroots : ∀ β ∈ roots, W.valuation β = t := by
    intro β hβ
    exact hall β hβ
  have hconstFactor :
      W.valuation (algebraMap K L (Q.coeff 0 : K)) =
        W.valuation (algebraMap K L (Q.leadingCoeff : K)) *
          t ^ roots.card := by
    calc
      W.valuation (algebraMap K L (Q.coeff 0 : K)) =
          W.valuation (F.coeff 0) := by
        simp [F, p, Polynomial.coeff_map]
      _ = W.valuation
          (((-1) ^ F.natDegree) * F.leadingCoeff * roots.prod) := by
        rw [hsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots]
      _ = W.valuation (algebraMap K L (Q.leadingCoeff : K)) *
          W.valuation roots.prod := by
        rw [W.valuation.map_mul, W.valuation.map_mul]
        rw [hleadF]
        simp
      _ = W.valuation (algebraMap K L (Q.leadingCoeff : K)) *
          t ^ roots.card := by
        rw [DiscreteValuationField.valuation_multiset_prod_eq_pow_card_of_eq
          W.valuation t roots hroots]
  have ht : 1 < t := by
    by_contra hnot
    have htle : t ≤ 1 := not_lt.mp hnot
    have hpow : t ^ roots.card ≤ 1 := pow_le_one₀ (bot_le : 0 ≤ t) htle
    have hlt :
        W.valuation (algebraMap K L (Q.leadingCoeff : K)) *
            t ^ roots.card < 1 := by
      exact mul_lt_one_of_lt_of_le hleadTarget hpow
    rw [← hconstFactor, hconstTarget] at hlt
    exact lt_irrefl 1 hlt
  have hleadTargetPos :
      0 < W.valuation (algebraMap K L (Q.leadingCoeff : K)) := by
    apply (Valuation.pos_iff W.valuation).2
    intro hzero
    have hzeroK : (Q.leadingCoeff : K) = 0 := by
      apply (algebraMap K L).injective
      simpa using hzero
    have hzeroV : Q.leadingCoeff = 0 := V.subtype_injective hzeroK
    exact Q.leadingCoeff_ne_zero.mpr hQprim.ne_zero hzeroV
  have hpositiveCoeff (j : ℕ) (hj : 0 < j) :
      V.valuation (Q.coeff j : K) < 1 := by
    have hprod :=
      valuation_coeff_prod_X_sub_C_lt_coeff_zero_of_one_lt
        W.valuation roots (fun β hβ => by rw [hroots β hβ]; exact ht) j hj
    have htarget :
        W.valuation (algebraMap K L (Q.coeff j : K)) <
          W.valuation (algebraMap K L (Q.coeff 0 : K)) := by
      rw [hcoeffFactor j, hcoeffFactor 0,
        W.valuation.map_mul, W.valuation.map_mul]
      exact mul_lt_mul_of_pos_left hprod hleadTargetPos
    have htargetOne :
        W.valuation (algebraMap K L (Q.coeff j : K)) < 1 := by
      rwa [hconstTarget] at htarget
    exact
      (Valuation.HasExtension.val_map_lt_one_iff
        V.valuation W.valuation (Q.coeff j : K)).mp htargetOne
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

/-- The primitive-irreducible reduction property in the last paragraph of
the proof of the unique-extension criterion, obtained directly from unique extension valuation
rings on algebraic fields. -/
theorem primitiveIrreducibleReductionProperty_of_unique_algebraic_extensions
    {K : Type u} [Field K] (V : ValuationSubring K)
    (hunique : ∀ (E : Type u) [Field E] [Algebra K E]
      [Algebra.IsAlgebraic K E],
        ∃! W : ValuationSubring E,
          V.valuation.HasExtension W.valuation) :
    DiscreteValuationField.PrimitiveIrreducibleReductionProperty V := by
  intro Q hQprim hQirr
  let qbar : Polynomial (IsLocalRing.ResidueField V) :=
    Q.map (IsLocalRing.residue V)
  have hqbar0 : qbar ≠ 0 := by
    exact DiscreteValuationField.polynomial_residue_ne_zero_of_isPrimitive
      V hQprim
  by_cases hlead : IsUnit Q.leadingCoeff
  · have hdegree : qbar.natDegree = Q.natDegree := by
      exact Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff
        (IsLocalRing.residue V) hlead
    refine ⟨Or.inr hdegree, ?_⟩
    intro a b hfactor hcoprime
    let u : Vˣ := hlead.unit
    let F : Polynomial V := Polynomial.C ((u⁻¹ : Vˣ) : V) * Q
    have hu : (u : V) = Q.leadingCoeff := hlead.unit_spec
    have hFmonic : F.Monic := by
      apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
      change (((u⁻¹ : Vˣ) : V) * Q.leadingCoeff) = 1
      rw [← hu]
      simp
    have hscalarUnitK : IsUnit (((u⁻¹ : Vˣ) : V) : K) := by
      exact isUnit_iff_ne_zero.mpr
        (V.subtype_injective.ne (Units.ne_zero (u⁻¹ : Vˣ)))
    have hCunitK :
        IsUnit (Polynomial.C (((u⁻¹ : Vˣ) : V) : K)) :=
      Polynomial.isUnit_C.mpr hscalarUnitK
    have hFmap :
        F.map V.subtype =
          Polynomial.C (((u⁻¹ : Vˣ) : V) : K) * Q.map V.subtype := by
      dsimp [F]
      rw [Polynomial.map_mul, Polynomial.map_C]
      rfl
    have hFirr : Irreducible (F.map V.subtype) := by
      have hassoc : Associated (F.map V.subtype) (Q.map V.subtype) := by
        rw [hFmap]
        exact associated_unit_mul_left _ _ hCunitK
      exact hassoc.symm.irreducible hQirr
    let c : IsLocalRing.ResidueField V :=
      IsLocalRing.residue V (((u⁻¹ : Vˣ) : V))
    have hcunit : IsUnit c :=
      (IsLocalRing.residue V).isUnit_map (Units.isUnit (u⁻¹ : Vˣ))
    have hCunit : IsUnit (Polynomial.C c) :=
      Polynomial.isUnit_C.mpr hcunit
    let a' : Polynomial (IsLocalRing.ResidueField V) := Polynomial.C c * a
    have hfactor' : F.map (IsLocalRing.residue V) = a' * b := by
      dsimp [F, a', c]
      rw [Polynomial.map_mul, Polynomial.map_C, hfactor]
      ring
    have hcoprime' : IsCoprime a' b := by
      exact (isCoprime_mul_unit_left_left hCunit a b).2 hcoprime
    let E : Type u := (F.map V.subtype).SplittingField
    obtain ⟨W, hW, hWuniq⟩ := hunique E
    let : V.valuation.HasExtension W.valuation := hW
    have hdegrees : a'.natDegree = 0 ∨ b.natDegree = 0 :=
      irreducible_monic_reduction_coprime_factor_degree_zero
        V W hWuniq F hFmonic hFirr a' b hfactor' hcoprime'
    have hab0 : a ≠ 0 ∧ b ≠ 0 := by
      have hab : a * b ≠ 0 := by
        rw [← hfactor]
        exact hqbar0
      exact ⟨left_ne_zero_of_mul hab, right_ne_zero_of_mul hab⟩
    have ha'degree : a'.natDegree = a.natDegree := by
      dsimp [a']
      rw [Polynomial.natDegree_mul (Polynomial.isUnit_C.mpr hcunit).ne_zero hab0.1,
        Polynomial.natDegree_C, Nat.zero_add]
    rcases hdegrees with ha' | hb
    · exact Or.inl (ha'degree.symm.trans ha')
    · exact Or.inr hb
  · let E : Type u := (Q.map V.subtype).SplittingField
    obtain ⟨W, hW, hWuniq⟩ := hunique E
    have hdegree : qbar.natDegree = 0 :=
      primitive_irreducible_reduction_natDegree_zero_of_leadingCoeff_nonunit
        V W hW hWuniq Q hQprim hQirr hlead
    refine ⟨Or.inl hdegree, ?_⟩
    intro a b hfactor _hcoprime
    have hab : a * b ≠ 0 := by
      rw [← hfactor]
      exact hqbar0
    have hmulDegree :=
      Polynomial.natDegree_mul (left_ne_zero_of_mul hab) (right_ne_zero_of_mul hab)
    have hsum : a.natDegree + b.natDegree = 0 := by
      rw [← hmulDegree, ← hfactor, hdegree]
    exact Or.inl (Nat.eq_zero_of_add_eq_zero_right hsum)

end Valuations
end AlgebraicNumberTheory

end
