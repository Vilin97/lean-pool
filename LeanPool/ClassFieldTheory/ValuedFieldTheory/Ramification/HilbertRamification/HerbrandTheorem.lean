/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumberFormula
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.Herbrand.FixedField
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.FixedFieldRamification
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumberRestriction
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RamificationDepth
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.LocalRingEquiv
/-!
# Herbrand's theorem for general discrete valuation fields

This leaf contains the completion-free endpoints of
the Herbrand quotient theorem and the quotient and tower filtration theorems.  The private
  lemmas below isolate
the finite-group averaging argument used in the quotient-filtration comparison.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification
namespace Higher

open RamificationTheory.DiscreteValuationField
open RamificationTheory.DiscreteValuationField.HerbrandGroupTheory

universe u v w x

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]
variable [FiniteDimensional K L] [IsGalois K L]

private theorem mem_lowerRamificationGroup_iff_ramificationNumber_dvf
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (s : ℝ) (sigma : Gal(L/K)) :
    sigma ∈ lowerRamificationGroup
        (base := base) (target := target) huniq s ↔
      (realRamificationExponent s : ℕ∞) ≤
        intrinsicRamificationNumberOfUniqueExtension
          (base := base) (target := target) huniq sigma := by
  unfold intrinsicRamificationNumberOfUniqueExtension
  rw [mem_lowerRamificationGroup_iff,
    natCast_le_ramificationNumberOfUniqueExtension_iff]
  simp only [realRamificationIdeal]
  constructor
  · intro hsigma
    exact hsigma _
  · intro hgenerator a
    exact valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin
      (base := base) (target := target) huniq hgenerator (by
        rw [chosenRamificationGeneratorOfUniqueExtension_adjoin_eq_top
          (base := base) (target := target) huniq]
        simp)

private theorem realRamificationExponent_le_iff_add_one_le_dvf
    (s : ℝ) (n : ℕ) :
    realRamificationExponent s ≤ n ↔ s + 1 ≤ n := by
  rw [realRamificationExponent, Int.toNat_le, Int.ceil_le, Int.cast_natCast]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `fixedFieldRamificationIdeal_antitone`. -/
theorem fixedFieldRamificationIdeal_antitone
    (H : Subgroup Gal(L/K)) {s t : ℝ} (hst : s ≤ t) :
    fixedFieldRamificationIdealDVF
        (K := K) (target := target) H t ≤
      fixedFieldRamificationIdealDVF
        (K := K) (target := target) H s := by
  exact Ideal.pow_le_pow_right (realRamificationExponent_mono hst)

/-- States the theorem `fixedFieldLowerRamificationGroup_antitone`. -/
theorem fixedFieldLowerRamificationGroup_antitone
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] :
    Antitone (fixedFieldLowerRamificationGroup
      (base := base) (target := target) huniq H) := by
  intro s t hst q hq a
  exact fixedFieldRamificationIdeal_antitone
    (K := K) (target := target) H hst (hq a)

/-- States the theorem `fixedFieldLowerRamificationGroup_normal`. -/
theorem fixedFieldLowerRamificationGroup_normal
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (s : ℝ) :
    (fixedFieldLowerRamificationGroup
      (base := base) (target := target) huniq H s).Normal := by
  refine Subgroup.Normal.mk ?_
  intro q hq r a
  let b := fixedFieldValuationSubringAutDVF
    (base := base) (target := target) huniq H r⁻¹ a
  have hb :
      fixedFieldValuationSubringAutDVF
          (base := base) (target := target) huniq H q b - b ∈
        fixedFieldRamificationIdealDVF
          (K := K) (target := target) H s :=
    hq b
  let eqv := fixedFieldValuationSubringAutDVF
    (base := base) (target := target) huniq H r
  have hmap :
      eqv
          (fixedFieldValuationSubringAutDVF
            (base := base) (target := target) huniq H q b - b) ∈
        fixedFieldRamificationIdealDVF
          (K := K) (target := target) H s := by
    exact (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff eqv
      (realRamificationExponent s) _).2 hb
  have hrewrite :
      fixedFieldValuationSubringAutDVF
          (base := base) (target := target) huniq H (r * q * r⁻¹) a - a =
        eqv
          (fixedFieldValuationSubringAutDVF
            (base := base) (target := target) huniq H q b - b) := by
    simp [eqv, b, map_sub, fixedFieldValuationSubringAutDVF]
  rwa [hrewrite]

/-- The integral fixed-field lower groups, packaged as a lower filtration. -/
def fixedFieldLowerRamificationFiltration
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] :
    AntitoneNormalSubgroupFiltration Gal((fixedFieldDVF (K := K) H)/K) where
  lower n := fixedFieldLowerRamificationGroup
    (base := base) (target := target) huniq H (n : ℝ)
  lower_normal n :=
    fixedFieldLowerRamificationGroup_normal
      (base := base) (target := target) huniq H (n : ℝ)
  antitone := by
    intro m n hmn
    apply fixedFieldLowerRamificationGroup_antitone
      (base := base) (target := target) huniq H
    exact_mod_cast hmn

/-- States the theorem `fixedFieldLowerRamificationFiltration_lower`. -/
@[simp] theorem fixedFieldLowerRamificationFiltration_lower
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (n : ℕ) :
    (fixedFieldLowerRamificationFiltration
      (base := base) (target := target) huniq H).lower n =
      fixedFieldLowerRamificationGroup
        (base := base) (target := target) huniq H (n : ℝ) :=
  rfl

/-- Herbrand's eta function for the actual fixed extension `(L ^ H)/K`. -/
def fixedFieldHerbrandFunction
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (s : ℝ) : ℝ :=
  (fixedFieldLowerRamificationFiltration
    (base := base) (target := target) huniq H).herbrandFunction s

/-- The inverse Herbrand function for the actual fixed extension. -/
def fixedFieldInverseHerbrandFunction
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (t : ℝ) : ℝ :=
  (fixedFieldLowerRamificationFiltration
    (base := base) (target := target) huniq H).inverseHerbrandFunction t

/-- States the theorem `fixedFieldHerbrandFunction_inverseHerbrandFunction`. -/
@[simp] theorem fixedFieldHerbrandFunction_inverseHerbrandFunction
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (t : ℝ) :
    fixedFieldHerbrandFunction
        (base := base) (target := target) huniq H
        (fixedFieldInverseHerbrandFunction
          (base := base) (target := target) huniq H t) = t :=
  (fixedFieldLowerRamificationFiltration
    (base := base) (target := target) huniq H).herbrandFunction_inverseHerbrandFunction t

/-- States the theorem `fixedFieldInverseHerbrandFunction_herbrandFunction`. -/
@[simp] theorem fixedFieldInverseHerbrandFunction_herbrandFunction
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (s : ℝ) :
    fixedFieldInverseHerbrandFunction
        (base := base) (target := target) huniq H
        (fixedFieldHerbrandFunction
          (base := base) (target := target) huniq H s) = s :=
  (fixedFieldLowerRamificationFiltration
    (base := base) (target := target) huniq H).inverseHerbrandFunction_herbrandFunction s

/-- States the theorem `fixedFieldHerbrandFunction_strictMono`. -/
theorem fixedFieldHerbrandFunction_strictMono
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] :
    StrictMono (fixedFieldHerbrandFunction
      (base := base) (target := target) huniq H) :=
  (fixedFieldLowerRamificationFiltration
    (base := base) (target := target) huniq H).herbrandFunction_strictMono

/-- States the theorem `fixedFieldInverseHerbrandFunction_strictMono`. -/
theorem fixedFieldInverseHerbrandFunction_strictMono
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] :
    StrictMono (fixedFieldInverseHerbrandFunction
      (base := base) (target := target) huniq H) :=
  (fixedFieldLowerRamificationFiltration
    (base := base) (target := target) huniq H).inverseHerbrandFunction_strictMono

/-- States the theorem `fixedFieldInverseHerbrandFunction_ge_neg_one_iff`. -/
theorem fixedFieldInverseHerbrandFunction_ge_neg_one_iff
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] {t : ℝ} :
    -1 ≤ fixedFieldInverseHerbrandFunction
        (base := base) (target := target) huniq H t ↔ -1 ≤ t :=
  (fixedFieldLowerRamificationFiltration
    (base := base) (target := target) huniq H).inverseHerbrandFunction_mem_Ici_neg_one_iff

/-- Upper ramification groups of the actual fixed extension. -/
def fixedFieldUpperRamificationGroup
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (t : ℝ) :
    Subgroup Gal((fixedFieldDVF (K := K) H)/K) :=
  fixedFieldLowerRamificationGroup
    (base := base) (target := target) huniq H
    (fixedFieldInverseHerbrandFunction
      (base := base) (target := target) huniq H t)

/-- States the theorem `fixedFieldUpperRamificationGroup_herbrandFunction`. -/
@[simp] theorem fixedFieldUpperRamificationGroup_herbrandFunction
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (s : ℝ) :
    fixedFieldUpperRamificationGroup
        (base := base) (target := target) huniq H
        (fixedFieldHerbrandFunction
          (base := base) (target := target) huniq H s) =
      fixedFieldLowerRamificationGroup
        (base := base) (target := target) huniq H s := by
  unfold fixedFieldUpperRamificationGroup
  rw [fixedFieldInverseHerbrandFunction_herbrandFunction]
/-- Classical decidability of membership in each lower ramification subgroup. -/
noncomputable local instance lowerMembershipDecidable
    {G : Type*} [Group G] (F : AntitoneNormalSubgroupFiltration G)
    (n : ℕ) (sigma : G) : Decidable (sigma ∈ F.lower n) :=
  Classical.propDecidable _

/-- Every subgroup of a finite group is equipped with a finite enumeration. -/
noncomputable local instance finiteSubgroupFintype
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

private theorem truncate_depth_eq_intrinsic_summand_of_mem
    {G : Type*} [Group G]
    (F : AntitoneNormalSubgroupFiltration G) (depth : G → ℕ∞)
    (hmem : ∀ n sigma,
      sigma ∈ F.lower n ↔ (((n + 1 : ℕ) : ℕ∞) ≤ depth sigma))
    (m : ℕ) {s : ℝ} (hms : (m : ℝ) ≤ s) (hsm : s ≤ m + 1)
    (sigma : F.lower 0) :
    truncateENatAtDVF (depth (sigma : G)) (s + 1) =
      1 + (F.truncatedLowerDepth m sigma : ℝ) +
        (s - m) * (if (sigma : G) ∈ F.lower (m + 1) then 1 else 0) := by
  classical
  let i := depth (sigma : G)
  have hi_one : (1 : ℕ∞) ≤ i := by
    simpa [i] using (hmem 0 (sigma : G)).1 sigma.property
  by_cases hhigh : ((m + 2 : ℕ) : ℕ∞) ≤ i
  · have hsigma : (sigma : G) ∈ F.lower (m + 1) := by
      apply (hmem (m + 1) (sigma : G)).2
      simpa [i, Nat.add_assoc] using hhigh
    have hdepth : F.truncatedLowerDepth m sigma = m := by
      rw [AntitoneNormalSubgroupFiltration.truncatedLowerDepth]
      rw [Finset.filter_eq_self.2]
      · simp
      · intro j hj
        apply (hmem (j + 1) (sigma : G)).2
        have hjm : j < m := Finset.mem_range.1 hj
        have hjle : ((j + 2 : ℕ) : ℕ∞) ≤ ((m + 2 : ℕ) : ℕ∞) :=
          ENat.natCast_le_natCast.2 (by omega)
        simpa [i, Nat.add_assoc] using hjle.trans hhigh
    have htrunc : truncateENatAtDVF i (s + 1) = s + 1 := by
      exact truncateENatAtDVF_eq_right_of_natCast_le
        (m := m + 2) (by
          norm_num [Nat.cast_add, Nat.cast_ofNat] at hsm ⊢
          linarith) hhigh
    rw [htrunc, hdepth]
    simp [hsigma]
    ring
  · have hlt : i < ((m + 2 : ℕ) : ℕ∞) := lt_of_not_ge hhigh
    have hine : i ≠ ⊤ := ne_top_of_lt hlt
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hine
    have hk_one : 1 ≤ k := by
      exact_mod_cast (hi_one.trans_eq hk.symm)
    have hk_upper : k ≤ m + 1 := by
      have : k < m + 2 := by exact_mod_cast (hk.symm ▸ hlt)
      omega
    have hsigma : (sigma : G) ∉ F.lower (m + 1) := by
      intro hsigma
      apply hhigh
      simpa [i, Nat.add_assoc] using (hmem (m + 1) (sigma : G)).1 hsigma
    have hdepth : F.truncatedLowerDepth m sigma = k - 1 := by
      rw [AntitoneNormalSubgroupFiltration.truncatedLowerDepth]
      have hfilter :
          (Finset.range m).filter
              (fun j => (sigma : G) ∈ F.lower (j + 1)) =
            Finset.range (k - 1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        have hthreshold :
            ((sigma : G) ∈ F.lower (j + 1)) ↔ j + 2 ≤ k := by
          rw [hmem]
          change (((j + 1 + 1 : ℕ) : ℕ∞) ≤ i) ↔ j + 2 ≤ k
          rw [← hk]
          norm_cast
        rw [hthreshold]
        omega
      rw [hfilter, Finset.card_range]
    have htrunc : truncateENatAtDVF i (s + 1) = k := by
      rw [← hk, truncateENatAtDVF_coe, min_eq_left]
      have : (k : ℝ) ≤ m + 1 := by exact_mod_cast hk_upper
      linarith
    rw [htrunc, hdepth]
    simp [hsigma]
    exact_mod_cast (by omega : k = 1 + (k - 1))

private theorem truncate_depth_eq_zero_of_not_mem_lower_zero
    {G : Type*} [Group G]
    (F : AntitoneNormalSubgroupFiltration G) (depth : G → ℕ∞)
    (hmem : ∀ n sigma,
      sigma ∈ F.lower n ↔ (((n + 1 : ℕ) : ℕ∞) ≤ depth sigma))
    {s : ℝ} (hs : -1 ≤ s) {sigma : G}
    (hsigma : sigma ∉ F.lower 0) :
    truncateENatAtDVF (depth sigma) (s + 1) = 0 := by
  have hi : depth sigma < 1 := by
    rw [← not_le]
    intro hi
    exact hsigma ((hmem 0 sigma).2 (by simpa using hi))
  have hi0 : depth sigma = 0 := Order.lt_one_iff.1 hi
  rw [hi0]
  simp [truncateENatAtDVF,
    min_eq_left (show (0 : ℝ) ≤ s + 1 by linarith)]

private theorem sum_truncate_depth_eq_sum_lower_zero_of_mem
    {G : Type*} [Group G] [Fintype G]
    (F : AntitoneNormalSubgroupFiltration G) (depth : G → ℕ∞)
    (hmem : ∀ n sigma,
      sigma ∈ F.lower n ↔ (((n + 1 : ℕ) : ℕ∞) ≤ depth sigma))
    {s : ℝ} (hs : -1 ≤ s) :
    (∑ sigma : G, truncateENatAtDVF (depth sigma) (s + 1)) =
      ∑ sigma : F.lower 0,
        truncateENatAtDVF (depth (sigma : G)) (s + 1) := by
  classical
  let q : G → ℝ := fun sigma =>
    truncateENatAtDVF (depth sigma) (s + 1)
  calc
    ∑ sigma : G, q sigma =
        ∑ sigma : G, if sigma ∈ F.lower 0 then q sigma else 0 := by
      apply Finset.sum_congr rfl
      intro sigma _
      by_cases hsigma : sigma ∈ F.lower 0
      · simp [hsigma]
      · rw [ite_eq_right hsigma]
        exact truncate_depth_eq_zero_of_not_mem_lower_zero
          F depth hmem hs hsigma
    _ = ∑ sigma : F.lower 0, q (sigma : G) := by
      rw [← Finset.sum_filter (p := fun sigma : G => sigma ∈ F.lower 0)]
      simpa using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset G)) q
          (p := fun sigma : G => sigma ∈ F.lower 0)).symm

private theorem sum_lower_zero_truncate_depth_eq_intrinsic_of_mem
    {G : Type*} [Group G] [Finite G]
    (F : AntitoneNormalSubgroupFiltration G) (depth : G → ℕ∞)
    (hmem : ∀ n sigma,
      sigma ∈ F.lower n ↔ (((n + 1 : ℕ) : ℕ∞) ≤ depth sigma))
    (m : ℕ) {s : ℝ} (hms : (m : ℝ) ≤ s) (hsm : s ≤ m + 1) :
    (∑ sigma : F.lower 0,
        truncateENatAtDVF (depth (sigma : G)) (s + 1)) =
      Nat.card (F.lower 0) +
        (∑ sigma : F.lower 0, (F.truncatedLowerDepth m sigma : ℝ)) +
        (s - m) * Nat.card (F.lower (m + 1)) := by
  classical
  let := Fintype.ofFinite G
  classical
  simp_rw [truncate_depth_eq_intrinsic_summand_of_mem
    F depth hmem m hms hsm]
  have hindicator :
      (∑ sigma : F.lower 0,
        (if (sigma : G) ∈ F.lower (m + 1) then (1 : ℝ) else 0)) =
        Nat.card (F.lower (m + 1)) := by
    exact_mod_cast (F.card_lower_succ_eq_sum_indicator m).symm
  change Finset.sum Finset.univ (fun sigma : F.lower 0 =>
      (1 : ℝ) + (F.truncatedLowerDepth m sigma : ℝ) +
        (s - m) *
          (if (sigma : G) ∈ F.lower (m + 1) then 1 else 0)) = _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hindicator]
  simp

private theorem herbrandFunction_eq_depth_sum_of_mem
    {G : Type*} [Group G] [Fintype G]
    (F : AntitoneNormalSubgroupFiltration G) (depth : G → ℕ∞)
    (hmem : ∀ n sigma,
      sigma ∈ F.lower n ↔ (((n + 1 : ℕ) : ℕ∞) ≤ depth sigma))
    {s : ℝ} (hs : -1 ≤ s) :
    (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
      F) s =
      (1 / Nat.card (F.lower 0) : ℝ) *
        (∑ sigma : G, truncateENatAtDVF (depth sigma) (s + 1)) - 1 := by
  classical
  have hcard : (Nat.card (F.lower 0) : ℝ) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (show 0 < Nat.card (F.lower 0) from Finite.card_pos))
  rw [sum_truncate_depth_eq_sum_lower_zero_of_mem F depth hmem hs]
  by_cases hs0 : 0 ≤ s
  · let m := ⌊s⌋₊
    have hms : (m : ℝ) ≤ s := Nat.floor_le hs0
    have hsm : s ≤ m + 1 := (Nat.lt_floor_add_one s).le
    rw [sum_lower_zero_truncate_depth_eq_intrinsic_of_mem
      F depth hmem m hms hsm]
    rw [F.herbrandFunction_eq_depth_sum_of_mem_Icc m hms hsm]
    field_simp
    ring
  · have hsle : s ≤ 0 := le_of_not_ge hs0
    rw [(RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_of_nonpos F) hsle]
    have hpoint : ∀ sigma : F.lower 0,
        truncateENatAtDVF (depth (sigma : G)) (s + 1) = s + 1 := by
      intro sigma
      have hi : (1 : ℕ∞) ≤ depth (sigma : G) := by
        simpa using (hmem 0 (sigma : G)).1 sigma.property
      exact truncateENatAtDVF_eq_right_of_natCast_le
        (m := 1) (by
          norm_num at hsle ⊢
          linarith) hi
    simp_rw [hpoint]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    field_simp
    ring

private theorem fixedField_herbrandFunction_formula_dvf
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] {s : ℝ} (hs : -1 ≤ s) :
    fixedFieldHerbrandFunction
        (base := base) (target := target) huniq H s =
      (1 / Nat.card ((fixedFieldLowerRamificationFiltration
        (base := base) (target := target) huniq H).lower 0) : ℝ) *
        (∑ q : Gal((fixedFieldDVF (K := K) H)/K),
          truncateENatAtDVF
            (fixedFieldRamificationNumber
              (base := base) (target := target) huniq H q) (s + 1)) - 1 := by
  apply herbrandFunction_eq_depth_sum_of_mem
    (fixedFieldLowerRamificationFiltration
      (base := base) (target := target) huniq H)
    (fixedFieldRamificationNumber
      (base := base) (target := target) huniq H)
  · intro n q
    exact mem_fixedFieldLowerRamificationGroup_nat_iff
      (base := base) (target := target) huniq H n q
  · exact hs



/-- A quotient fiber of a finite group is equipped with an enumeration for the depth average. -/
noncomputable local instance finiteQuotientFiberFintype
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) [H.Normal]
    (q : G ⧸ H) : Fintype (NonarchimedeanDepth.QuotientFiber H q) :=
  Fintype.ofFinite _

private theorem truncate_depth_eq_intrinsic_summand
    {G : Type*} [Group G]
    (D : NonarchimedeanDepth G) (H : Subgroup G)
    (m : ℕ) {s : ℝ} (hms : (m : ℝ) ≤ s) (hsm : s ≤ m + 1)
    (tau : (D.depthLowerFiltration H).lower 0) :
    truncateENatAtDVF (D.depth ((tau : H) : G)) (s + 1) =
      1 + ((D.depthLowerFiltration H).truncatedLowerDepth m tau : ℝ) +
        (s - m) *
          (if (tau : H) ∈ (D.depthLowerFiltration H).lower (m + 1)
            then 1 else 0) := by
  classical
  let F := D.depthLowerFiltration H
  let i := D.depth ((tau : H) : G)
  have hi_one : (1 : ℕ∞) ≤ i := tau.property
  by_cases hhigh : ((m + 2 : ℕ) : ℕ∞) ≤ i
  · have hmem : (tau : H) ∈
        (D.depthLowerFiltration H).lower (m + 1) := hhigh
    have hdepth : F.truncatedLowerDepth m tau = m := by
      rw [AntitoneNormalSubgroupFiltration.truncatedLowerDepth]
      rw [Finset.filter_eq_self.2]
      · simp
      · intro j hj
        change ((j + 2 : ℕ) : ℕ∞) ≤ i
        have hjm : j < m := Finset.mem_range.1 hj
        have hjm' : ((j + 2 : ℕ) : ℕ∞) ≤ ((m + 2 : ℕ) : ℕ∞) :=
          ENat.natCast_le_natCast.2 (by omega)
        exact hjm'.trans hhigh
    have htrunc : truncateENatAtDVF i (s + 1) = s + 1 := by
      exact truncateENatAtDVF_eq_right_of_natCast_le
        (m := m + 2) (by
          norm_num [Nat.cast_add, Nat.cast_ofNat] at hsm ⊢
          linarith) hhigh
    rw [htrunc, hdepth]
    rw [ite_eq_left hmem]
    ring
  · have hlt : i < ((m + 2 : ℕ) : ℕ∞) := lt_of_not_ge hhigh
    have hine : i ≠ ⊤ := ne_top_of_lt hlt
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hine
    have hk_one : 1 ≤ k := by
      exact_mod_cast (hi_one.trans_eq hk.symm)
    have hk_upper : k ≤ m + 1 := by
      have : k < m + 2 := ENat.natCast_lt_natCast.1 (hk.symm ▸ hlt)
      omega
    have hmem : (tau : H) ∉
        (D.depthLowerFiltration H).lower (m + 1) := hhigh
    have hdepth : F.truncatedLowerDepth m tau = k - 1 := by
      rw [AntitoneNormalSubgroupFiltration.truncatedLowerDepth]
      have hfilter :
          (Finset.range m).filter
              (fun j => (tau : H) ∈ F.lower (j + 1)) =
            Finset.range (k - 1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        have hthreshold :
            ((tau : H) ∈ F.lower (j + 1)) ↔ j + 2 ≤ k := by
          change (((j + 2 : ℕ) : ℕ∞) ≤ i) ↔ j + 2 ≤ k
          rw [← hk]
          norm_cast
        rw [hthreshold]
        omega
      rw [hfilter, Finset.card_range]
    have htrunc : truncateENatAtDVF i (s + 1) = k := by
      rw [← hk, truncateENatAtDVF_coe, min_eq_left]
      have : (k : ℝ) ≤ m + 1 := by exact_mod_cast hk_upper
      linarith
    rw [htrunc, hdepth]
    rw [ite_eq_right hmem]
    simp only [mul_zero, add_zero]
    exact_mod_cast (by omega : k = 1 + (k - 1))

private theorem sum_truncate_depth_eq_sum_lower_zero
    {G : Type*} [Group G] [Finite G]
    (D : NonarchimedeanDepth G) (H : Subgroup G)
    {s : ℝ} (hs : -1 ≤ s) :
    (∑ tau : H, truncateENatAtDVF (D.depth (tau : G)) (s + 1)) =
      ∑ tau : (D.depthLowerFiltration H).lower 0,
        truncateENatAtDVF (D.depth ((tau : H) : G)) (s + 1) := by
  classical
  let := Fintype.ofFinite G
  classical
  let F := D.depthLowerFiltration H
  let f : H → ℝ := fun tau => truncateENatAtDVF (D.depth (tau : G)) (s + 1)
  calc
    ∑ tau : H, f tau =
        ∑ tau : H, if tau ∈ F.lower 0 then f tau else 0 := by
      apply Finset.sum_congr rfl
      intro tau _
      by_cases htau : tau ∈ F.lower 0
      · simp [htau]
      · rw [ite_eq_right htau]
        have hzero : D.depth (tau : G) = (0 : ℕ∞) := by
          exact D.depth_eq_zero_of_not_mem_lower_zero H tau htau
        change truncateENatAtDVF (D.depth (tau : G)) (s + 1) = 0
        rw [hzero]
        simp [truncateENatAtDVF, show (0 : ℝ) ≤ s + 1 by linarith]
    _ = ∑ tau : F.lower 0, f (tau : H) := by
      rw [← Finset.sum_filter (p := fun tau : H => tau ∈ F.lower 0)]
      change
        (∑ tau ∈ (Finset.univ : Finset H) with tau ∈ F.lower 0, f tau) =
          ∑ tau : {tau : H // tau ∈ F.lower 0}, f tau
      simpa using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset H)) f
          (p := fun tau : H => tau ∈ F.lower 0)).symm

private theorem sum_lower_zero_truncate_depth_eq_intrinsic
    {G : Type*} [Group G] [Finite G]
    (D : NonarchimedeanDepth G) (H : Subgroup G) [H.Normal]
    (m : ℕ) {s : ℝ} (hms : (m : ℝ) ≤ s) (hsm : s ≤ m + 1) :
    (∑ tau : (D.depthLowerFiltration H).lower 0,
        truncateENatAtDVF (D.depth ((tau : H) : G)) (s + 1)) =
      Nat.card ((D.depthLowerFiltration H).lower 0) +
        (∑ tau : (D.depthLowerFiltration H).lower 0,
          ((D.depthLowerFiltration H).truncatedLowerDepth m tau : ℝ)) +
        (s - m) * Nat.card ((D.depthLowerFiltration H).lower (m + 1)) := by
  classical
  let := Fintype.ofFinite G
  classical
  let F := D.depthLowerFiltration H
  change (∑ tau : F.lower 0,
      truncateENatAtDVF (D.depth (((tau : F.lower 0) : H) : G)) (s + 1)) =
    Nat.card (F.lower 0) +
      (∑ tau : F.lower 0, (F.truncatedLowerDepth m tau : ℝ)) +
      (s - m) * Nat.card (F.lower (m + 1))
  simp_rw [truncate_depth_eq_intrinsic_summand D H m hms hsm]
  have hindicator :
      (∑ tau : F.lower 0,
        (if (tau : H) ∈ F.lower (m + 1) then (1 : ℝ) else 0)) =
        Nat.card (F.lower (m + 1)) := by
    exact_mod_cast (F.card_lower_succ_eq_sum_indicator m).symm
  change Finset.sum Finset.univ (fun tau : F.lower 0 =>
      (1 : ℝ) + (F.truncatedLowerDepth m tau : ℝ) +
        (s - m) * (if (tau : H) ∈ F.lower (m + 1) then 1 else 0)) = _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hindicator]
  simp

/-- The Herbrand-function sum formula for an abstract nonarchimedean depth, in the form used
to compare the subgroup Herbrand parameter with a normalized depth sum. -/
private theorem depth_herbrandFunction_add_one_eq_average
    {G : Type*} [Group G] [Finite G]
    (D : NonarchimedeanDepth G) (H : Subgroup G) [H.Normal]
    {s : ℝ} (hs : -1 ≤ s) :
    (D.depthLowerFiltration H).herbrandFunction s + 1 =
      (1 / D.depthRamificationIndex H : ℝ) *
        ∑ tau : H, truncateENatAtDVF (D.depth (tau : G)) (s + 1) := by
  classical
  let := Fintype.ofFinite G
  classical
  let F := D.depthLowerFiltration H
  change
    (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
    F) s + 1 =
    (1 / (Nat.card (F.lower 0) : ℝ)) *
      ∑ tau : H, truncateENatAtDVF (D.depth (tau : G)) (s + 1)
  have he : (Nat.card (F.lower 0) : ℝ) ≠ 0 := by
    exact_mod_cast (show 0 < Nat.card (F.lower 0) from Finite.card_pos).ne'
  rw [sum_truncate_depth_eq_sum_lower_zero D H hs]
  by_cases hs0 : 0 ≤ s
  · let m := ⌊s⌋₊
    have hms : (m : ℝ) ≤ s := Nat.floor_le hs0
    have hsm : s ≤ m + 1 := (Nat.lt_floor_add_one s).le
    rw [sum_lower_zero_truncate_depth_eq_intrinsic D H m hms hsm]
    rw [F.herbrandFunction_eq_depth_sum_of_mem_Icc m hms hsm]
    field_simp
    ring
  · have hsle : s ≤ 0 := le_of_not_ge hs0
    rw [(RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_of_nonpos F) hsle]
    have hpoint : ∀ tau : F.lower 0,
        truncateENatAtDVF (D.depth (((tau : F.lower 0) : H) : G)) (s + 1) =
          s + 1 := by
      intro tau
      exact truncateENatAtDVF_eq_right_of_natCast_le
        (m := 1) (by
          norm_num
          linarith) tau.property
    simp_rw [hpoint]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    change s + 1 = (1 / (Nat.card (F.lower 0) : ℝ)) *
      (Nat.card (F.lower 0) * (s + 1))
    field_simp

private theorem truncate_min_coe_eq_of_le
    {i : ℕ∞} {m : ℕ} {r : ℝ} (hr : r ≤ m) :
    truncateENatAtDVF (min i (m : ℕ∞)) r = truncateENatAtDVF i r := by
  induction i using ENat.recTopCoe with
  | top =>
      simp only [min_top_left, truncateENatAtDVF_top,
        truncateENatAtDVF_coe]
      exact min_eq_right hr
  | coe n =>
      have hmin : min (n : ℕ∞) (m : ℕ∞) = ((min n m : ℕ) : ℕ∞) := by
        norm_cast
      rw [hmin, truncateENatAtDVF_coe, truncateENatAtDVF_coe]
      push_cast
      rw [min_assoc, min_eq_right hr]

/-- Truncating a nontrivial quotient-fibre average at the subgroup Herbrand
parameter equals the normalized sum of the truncated ambient depths. -/
private theorem min_quotientFiberAverage_eq_average_truncate
    {G : Type*} [Group G] [Fintype G]
    (D : NonarchimedeanDepth G) (H : Subgroup G) [H.Normal]
    {q : G ⧸ H} (hq : q ≠ 1) {s : ℝ} (hs : -1 ≤ s) :
    min (D.quotientFiberAverage H hq)
        ((D.depthLowerFiltration H).herbrandFunction s + 1) =
      (1 / D.depthRamificationIndex H : ℝ) *
        ∑ gamma : NonarchimedeanDepth.QuotientFiber H q,
          truncateENatAtDVF (D.depth (gamma : G)) (s + 1) := by
  classical
  obtain ⟨sigma, hsigmaq, hmax⟩ := D.exists_maximal_depth_representative H hq
  let m := D.quotientFiberDepth H hq ⟨sigma, hsigmaq⟩
  have hdepth : D.depth sigma = WithTop.some m :=
    (D.coe_quotientFiberDepth H hq ⟨sigma, hsigmaq⟩).symm
  have havg : D.quotientFiberAverage H hq - 1 =
      (D.depthLowerFiltration H).herbrandFunction ((m : ℝ) - 1) := by
    simpa [m] using
      D.quotientFiberAverage_sub_one_eq_herbrandFunction_of_maximal
        H hq hsigmaq hmax
  have he : (D.depthRamificationIndex H : ℝ) ≠ 0 := by
    exact_mod_cast
      (show 0 < Nat.card ((D.depthLowerFiltration H).lower 0) from
        Finite.card_pos).ne'
  by_cases hms : (m : ℝ) - 1 ≤ s
  · have heta :
        (D.depthLowerFiltration H).herbrandFunction ((m : ℝ) - 1) ≤
          (D.depthLowerFiltration H).herbrandFunction s :=
      (D.depthLowerFiltration H).herbrandFunction_strictMono.monotone hms
    rw [min_eq_left (by linarith [havg, heta])]
    have hpoint : ∀ gamma : NonarchimedeanDepth.QuotientFiber H q,
        truncateENatAtDVF (D.depth (gamma : G)) (s + 1) =
          (D.quotientFiberDepth H hq gamma : ℝ) := by
      intro gamma
      have hle : D.depth (gamma : G) ≤ D.depth sigma :=
        hmax gamma gamma.property
      rw [hdepth] at hle
      have hnat : D.quotientFiberDepth H hq gamma ≤ m := by
        apply WithTop.coe_le_coe.mp
        calc
          WithTop.some (D.quotientFiberDepth H hq gamma) =
              D.depth (gamma : G) :=
            D.coe_quotientFiberDepth H hq gamma
          _ ≤ WithTop.some m := hle
      have hbound :
          (D.quotientFiberDepth H hq gamma : ℝ) ≤ s + 1 :=
        (show (D.quotientFiberDepth H hq gamma : ℝ) ≤ (m : ℝ) by
          exact_mod_cast hnat) |>.trans (by linarith)
      calc
        truncateENatAtDVF (D.depth (gamma : G)) (s + 1) =
            truncateENatAtDVF
              (D.quotientFiberDepth H hq gamma : ℕ∞) (s + 1) :=
          congrArg
            (fun i : ℕ∞ => truncateENatAtDVF i (s + 1))
            (D.coe_quotientFiberDepth H hq gamma).symm
        _ = min (D.quotientFiberDepth H hq gamma : ℝ) (s + 1) :=
          truncateENatAtDVF_coe _ _
        _ = (D.quotientFiberDepth H hq gamma : ℝ) :=
          min_eq_left hbound
    rw [NonarchimedeanDepth.quotientFiberAverage]
    rw [show (∑ gamma : NonarchimedeanDepth.QuotientFiber H q,
        (D.quotientFiberDepth H hq gamma : ℝ)) =
      ∑ gamma : NonarchimedeanDepth.QuotientFiber H q,
        truncateENatAtDVF (D.depth (gamma : G)) (s + 1) by
          apply Finset.sum_congr rfl
          intro gamma _
          exact (hpoint gamma).symm]
    ring
  · have hsm : s ≤ (m : ℝ) - 1 := le_of_not_ge hms
    have heta :
        (D.depthLowerFiltration H).herbrandFunction s ≤
          (D.depthLowerFiltration H).herbrandFunction ((m : ℝ) - 1) :=
      (D.depthLowerFiltration H).herbrandFunction_strictMono.monotone hsm
    rw [min_eq_right (by linarith [havg, heta])]
    let trunc : WithTop ℕ → ℝ := fun i =>
      truncateENatAtDVF i (s + 1)
    have hsum := D.sum_depth_quotientFiber_eq_sum_min_of_maximal_representative
      H trunc
        (by
          intro gamma hgamma
          exact hmax gamma (hgamma.trans hsigmaq))
    rw [hsigmaq] at hsum
    have hr : s + 1 ≤ (m : ℝ) := by linarith
    have htrunc_min (tau : H) :
        trunc (min (D.depth (tau : G)) (D.depth sigma)) =
          trunc (D.depth (tau : G)) := by
      change truncateENatAtDVF
          (min (D.depth (tau : G)) (D.depth sigma)) (s + 1) =
        truncateENatAtDVF (D.depth (tau : G)) (s + 1)
      rw [hdepth]
      exact truncate_min_coe_eq_of_le hr
    have hsum' :
        (∑ gamma : NonarchimedeanDepth.QuotientFiber H q,
            truncateENatAtDVF (D.depth (gamma : G)) (s + 1)) =
          ∑ tau : H,
            truncateENatAtDVF (D.depth (tau : G)) (s + 1) := by
      change (∑ gamma : NonarchimedeanDepth.QuotientFiber H q,
          trunc (D.depth (gamma : G))) =
        ∑ tau : H, trunc (D.depth (tau : G))
      calc
        _ = ∑ tau : H,
            trunc (min (D.depth (tau : G)) (D.depth sigma)) := hsum
        _ = _ := by
          apply Finset.sum_congr rfl
          intro tau _
          exact htrunc_min tau
    rw [hsum']
    exact depth_herbrandFunction_add_one_eq_average D H hs

private theorem subgroupFiltration_lower_eq_depthLowerFiltration_dvf
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) (n : ℕ) :
    ((lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq).subgroupFiltration H).lower n =
      ((ramificationNumberDepthOfUniqueExtension
        (base := base) (target := target) huniq).depthLowerFiltration H).lower n := by
  ext tau
  change ((tau : H) : Gal(L/K)) ∈
      lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ) ↔
    (((n + 1 : ℕ) : ℕ∞) ≤
      intrinsicRamificationNumberOfUniqueExtension
        (base := base) (target := target) huniq ((tau : H) : Gal(L/K)))
  exact mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
    (base := base) (target := target) huniq n ((tau : H) : Gal(L/K))

private theorem fixedFieldSubextension_herbrandFunction_eq_depth_dvf
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (s : ℝ) :
    (fixedFieldSubextensionFiltration
      (lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq) H).herbrandFunction s =
      ((ramificationNumberDepthOfUniqueExtension
        (base := base) (target := target) huniq).depthLowerFiltration H).herbrandFunction s := by
  rw [fixedFieldSubextension_herbrandFunction]
  apply
    ((lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq).subgroupFiltration
        H).herbrandFunction_eq_of_card_lower_eq
      ((ramificationNumberDepthOfUniqueExtension
        (base := base) (target := target) huniq).depthLowerFiltration H)
  intro n
  rw [subgroupFiltration_lower_eq_depthLowerFiltration_dvf
    (base := base) (target := target) huniq H n]

private theorem card_fixedFieldSubextension_lower_eq_depth_dvf
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (n : ℕ) :
    Nat.card ((fixedFieldSubextensionFiltration
      (lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq) H).lower n) =
      Nat.card (((ramificationNumberDepthOfUniqueExtension
        (base := base) (target := target) huniq).depthLowerFiltration H).lower n) := by
  change Nat.card
      ((((lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq).subgroupFiltration H).transportEquiv
          (IntermediateField.subgroupEquivAlgEquiv H)).lower n) = _
  rw [AntitoneNormalSubgroupFiltration.card_lower_transportEquiv
    ((lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq).subgroupFiltration H)
    (IntermediateField.subgroupEquivAlgEquiv H) n]
  rw [subgroupFiltration_lower_eq_depthLowerFiltration_dvf
    (base := base) (target := target) huniq H n]
private theorem fixedFieldRamificationNumber_untop_eq_quotientFiberAverage
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (sigma : Gal(L/K)) (hq : QuotientGroup.mk' H sigma ≠ 1) :
    ∃ hfinite :
        fixedFieldRamificationNumber
          (base := base) (target := target) huniq H
          (IsGalois.normalAutEquivQuotient H sigma) ≠ ⊤,
      ((fixedFieldRamificationNumber
          (base := base) (target := target) huniq H
          (IsGalois.normalAutEquivQuotient H sigma)).untop hfinite : ℝ) =
        (ramificationNumberDepthOfUniqueExtension
          (base := base) (target := target) huniq).quotientFiberAverage H hq := by
  classical
  let D := ramificationNumberDepthOfUniqueExtension
    (base := base) (target := target) huniq
  let iM := fixedFieldRamificationNumber
    (base := base) (target := target) huniq H
    (IsGalois.normalAutEquivQuotient H sigma)
  let S := ∑ gamma : NonarchimedeanDepth.QuotientFiber
      H (QuotientGroup.mk' H sigma), D.quotientFiberDepth H hq gamma
  have hcoset :
      intrinsicCosetRamificationNumberSum
          (base := base) (target := target) huniq H sigma =
        (S : ℕ∞) := by
    unfold intrinsicCosetRamificationNumberSum
    calc
      (∑ tau : H,
          intrinsicRamificationNumberOfUniqueExtension
            (base := base) (target := target) huniq (sigma * tau)) =
          ∑ gamma : NonarchimedeanDepth.QuotientFiber
              H (QuotientGroup.mk' H sigma),
            (D.quotientFiberDepth H hq gamma : ℕ∞) := by
        apply Fintype.sum_equiv
          (NonarchimedeanDepth.rightCosetEquivQuotientFiber H sigma)
        intro tau
        exact (D.coe_quotientFiberDepth H hq
          ((NonarchimedeanDepth.rightCosetEquivQuotientFiber H sigma) tau)).symm
      _ = (S : ℕ∞) := by
        dsimp [S]
        norm_cast
  have hprop := ramificationIndex_nsmul_fixedFieldRamificationNumber_eq_cosetSum
    (base := base) (target := target) huniq H sigma
  rw [fixedFieldRamificationIndex_eq_card_depthLowerFiltration_zero
    (base := base) (target := target) huniq H, hcoset] at hprop
  change D.depthRamificationIndex H • iM = (S : ℕ∞) at hprop
  have hfinite : iM ≠ ⊤ := by
    intro htop
    have hcontra := hprop
    rw [htop] at hcontra
    have hpos : D.depthRamificationIndex H ≠ 0 :=
      (show 0 < Nat.card ((D.depthLowerFiltration H).lower 0) from
        Finite.card_pos).ne'
    simp [hpos] at hcontra
  refine ⟨hfinite, ?_⟩
  let m := iM.untop hfinite
  have hiM : (m : ℕ∞) = iM := WithTop.coe_untop iM hfinite
  rw [← hiM] at hprop
  have hnat : D.depthRamificationIndex H * m = S := by
    have hcast : ((D.depthRamificationIndex H * m : ℕ) : ℕ∞) = (S : ℕ∞) := by
      simpa [nsmul_eq_mul] using hprop
    exact_mod_cast hcast
  change (m : ℝ) = D.quotientFiberAverage H hq
  rw [NonarchimedeanDepth.quotientFiberAverage]
  change (m : ℝ) =
    (∑ gamma : NonarchimedeanDepth.QuotientFiber
      H (QuotientGroup.mk' H sigma),
      (D.quotientFiberDepth H hq gamma : ℝ)) /
        D.depthRamificationIndex H
  rw [show (∑ gamma : NonarchimedeanDepth.QuotientFiber
      H (QuotientGroup.mk' H sigma),
      (D.quotientFiberDepth H hq gamma : ℝ)) = (S : ℝ) by
        exact_mod_cast rfl]
  rw [← hnat]
  have he : (D.depthRamificationIndex H : ℝ) ≠ 0 := by
    exact_mod_cast
      (show 0 < Nat.card ((D.depthLowerFiltration H).lower 0) from
        Finite.card_pos).ne'
  field_simp
  norm_num [Nat.cast_mul, mul_comm]

/-- The Herbrand quotient theorem over the stated discretely valued field hypotheses
hypotheses.  The image of the ambient lower group is the lower group of the
actual fixed extension at the subgroup Herbrand parameter. -/
theorem lowerRamificationGroup_quotient
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (s : ℝ) :
    Subgroup.map (QuotientGroup.mk' H)
        (lowerRamificationGroup
          (base := base) (target := target) huniq s) =
      Subgroup.comap (IsGalois.normalAutEquivQuotient H).toMonoidHom
        (fixedFieldLowerRamificationGroup
          (base := base) (target := target) huniq H
          ((fixedFieldSubextensionFiltration
            (lowerRamificationFiltrationOfUniqueExtension
              (base := base) (target := target) huniq) H).herbrandFunction s)) := by
  classical
  let D := ramificationNumberDepthOfUniqueExtension
    (base := base) (target := target) huniq
  let F := lowerRamificationFiltrationOfUniqueExtension
    (base := base) (target := target) huniq
  have hetaSub (r : ℝ) :
      (fixedFieldSubextensionFiltration F H).herbrandFunction r =
        (D.depthLowerFiltration H).herbrandFunction r := by
    rw [fixedFieldSubextension_herbrandFunction]
    apply (F.subgroupFiltration H).herbrandFunction_eq_of_card_lower_eq
      (D.depthLowerFiltration H)
    intro n
    have hlevel :
        (F.subgroupFiltration H).lower n =
          (D.depthLowerFiltration H).lower n := by
      ext tau
      change ((tau : H) : Gal(L/K)) ∈
          lowerRamificationGroup
            (base := base) (target := target) huniq (n : ℝ) ↔
        (((n + 1 : ℕ) : ℕ∞) ≤
          intrinsicRamificationNumberOfUniqueExtension
            (base := base) (target := target) huniq ((tau : H) : Gal(L/K)))
      exact mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
        (base := base) (target := target) huniq n ((tau : H) : Gal(L/K))
    rw [hlevel]
  ext q
  by_cases hq : q = 1
  · subst q
    simp
  · obtain ⟨sigma, hsigmaq, hmax⟩ :=
      D.exists_maximal_depth_representative H hq
    subst q
    have hsigmaq :
        QuotientGroup.mk' H sigma = QuotientGroup.mk' H sigma := rfl
    let m := D.quotientFiberDepth H hq ⟨sigma, hsigmaq⟩
    have hdepth : (m : ℕ∞) = D.depth sigma :=
      D.coe_quotientFiberDepth H hq ⟨sigma, hsigmaq⟩
    have hleft :
        QuotientGroup.mk' H sigma ∈
            Subgroup.map (QuotientGroup.mk' H)
              (lowerRamificationGroup
                (base := base) (target := target) huniq s) ↔
          realRamificationExponent s ≤ m := by
      constructor
      · rintro ⟨gamma, hgamma, hgammaq⟩
        have hgammaDepth :
            (realRamificationExponent s : ℕ∞) ≤ D.depth gamma := by
          change (realRamificationExponent s : ℕ∞) ≤
            intrinsicRamificationNumberOfUniqueExtension
              (base := base) (target := target) huniq gamma
          exact (mem_lowerRamificationGroup_iff_ramificationNumber_dvf
            (base := base) (target := target) huniq s gamma).1 hgamma
        have hle : D.depth gamma ≤ D.depth sigma :=
          hmax gamma hgammaq
        have : (realRamificationExponent s : ℕ∞) ≤ (m : ℕ∞) := by
          rw [hdepth]
          exact hgammaDepth.trans hle
        exact_mod_cast this
      · intro hm
        refine ⟨sigma, ?_, hsigmaq⟩
        apply (mem_lowerRamificationGroup_iff_ramificationNumber_dvf
          (base := base) (target := target) huniq s sigma).2
        change (realRamificationExponent s : ℕ∞) ≤ D.depth sigma
        rw [← hdepth]
        exact_mod_cast hm
    obtain ⟨hfinite, havg⟩ :=
      fixedFieldRamificationNumber_untop_eq_quotientFiberAverage
        (base := base) (target := target) huniq H sigma hq
    have hright :
        QuotientGroup.mk' H sigma ∈
            Subgroup.comap (IsGalois.normalAutEquivQuotient H).toMonoidHom
              (fixedFieldLowerRamificationGroup
                (base := base) (target := target) huniq H
                ((fixedFieldSubextensionFiltration F H).herbrandFunction s)) ↔
          s ≤ (m : ℝ) - 1 := by
      simp only [Subgroup.mem_comap]
      change IsGalois.normalAutEquivQuotient H sigma ∈
          fixedFieldLowerRamificationGroup
            (base := base) (target := target) huniq H
            ((fixedFieldSubextensionFiltration F H).herbrandFunction s) ↔ _
      rw [mem_fixedFieldLowerRamificationGroup_iff_ramificationNumber]
      let iM := fixedFieldRamificationNumber
        (base := base) (target := target) huniq H
        (IsGalois.normalAutEquivQuotient H sigma)
      let k := iM.untop hfinite
      have hcoe : (k : ℕ∞) = iM := WithTop.coe_untop iM hfinite
      change (realRamificationExponent
          ((fixedFieldSubextensionFiltration F H).herbrandFunction s) : ℕ∞) ≤
        iM ↔ _
      rw [← hcoe, ENat.natCast_le_natCast]
      rw [realRamificationExponent_le_iff_add_one_le_dvf]
      rw [havg, hetaSub]
      have havgMax :=
        D.quotientFiberAverage_sub_one_eq_herbrandFunction_of_maximal
          H hq hsigmaq hmax
      change (D.depthLowerFiltration H).herbrandFunction s + 1 ≤
          D.quotientFiberAverage H hq ↔ s ≤ (m : ℝ) - 1
      rw [show
        (D.depthLowerFiltration H).herbrandFunction s + 1 ≤
              D.quotientFiberAverage H hq ↔
            (D.depthLowerFiltration H).herbrandFunction s ≤
              D.quotientFiberAverage H hq - 1 by
        constructor <;> intro h <;> linarith]
      rw [havgMax]
      exact (D.depthLowerFiltration H).herbrandFunction_strictMono.le_iff_le
    rw [hleft, hright]
    rw [realRamificationExponent_le_iff_add_one_le_dvf]
    constructor <;> intro h <;> linarith



/-- The quotient-filtration comparison over the stated discretely valued field hypotheses
hypotheses: Herbrand eta is transitive in the actual fixed-field tower. -/
private theorem herbrandFunction_trans_of_neg_one_le
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    {s : ℝ} (hs : -1 ≤ s) :
    herbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq s =
      fixedFieldHerbrandFunction
        (base := base) (target := target) huniq H
        ((fixedFieldSubextensionFiltration
          (lowerRamificationFiltrationOfUniqueExtension
            (base := base) (target := target) huniq) H).herbrandFunction s) := by
  classical
  let : Fintype Gal(L/K) := Fintype.ofFinite _
  let : Fintype (Gal(L/K) ⧸ H) := Fintype.ofFinite _
  let F := lowerRamificationFiltrationOfUniqueExtension
    (base := base) (target := target) huniq
  let D := ramificationNumberDepthOfUniqueExtension
    (base := base) (target := target) huniq
  let t := (fixedFieldSubextensionFiltration F H).herbrandFunction s
  let e0 := Nat.card (F.lower 0)
  let e1 := Nat.card ((fixedFieldLowerRamificationFiltration
    (base := base) (target := target) huniq H).lower 0)
  let e2 := D.depthRamificationIndex H
  have ht : -1 ≤ t :=
    ((fixedFieldSubextensionFiltration F H).herbrandFunction_mem_Ici_neg_one_iff).2 hs
  have heta2 : (D.depthLowerFiltration H).herbrandFunction s = t := by
    simpa [F, D, t] using
      (fixedFieldSubextension_herbrandFunction_eq_depth_dvf
        (base := base) (target := target) huniq H s).symm
  have hcard2 :
      Nat.card ((fixedFieldSubextensionFiltration F H).lower 0) = e2 := by
    simpa [F, D, e2, NonarchimedeanDepth.depthRamificationIndex] using
      card_fixedFieldSubextension_lower_eq_depth_dvf
        (base := base) (target := target) huniq H 0
  have hquot0 :
      (fixedFieldQuotientImageFiltration F H).lower 0 =
        (fixedFieldLowerRamificationFiltration
          (base := base) (target := target) huniq H).lower 0 := by
    change
      (F.quotientImageTransport H
        (IsGalois.normalAutEquivQuotient H)).lower 0 = _
    apply (F.quotientImageTransport_lower_eq_iff H
      (IsGalois.normalAutEquivQuotient H) 0 _).2
    simpa [F] using
      lowerRamificationGroup_quotient
        (base := base) (target := target) huniq H 0
  have hfactor :=
    card_fixedFieldSubextension_mul_card_fixedFieldQuotientImage F H 0
  rw [hcard2, hquot0] at hfactor
  have hetower : e0 = e1 * e2 := by
    simpa [e0, e1, Nat.mul_comm] using hfactor.symm
  have he0 : (e0 : ℝ) ≠ 0 := by
    exact_mod_cast (show 0 < e0 by
      dsimp [e0]
      exact Finite.card_pos).ne'
  have he1 : (e1 : ℝ) ≠ 0 := by
    exact_mod_cast (show 0 < e1 by
      dsimp [e1]
      exact Finite.card_pos).ne'
  have he2 : (e2 : ℝ) ≠ 0 := by
    exact_mod_cast (show 0 < e2 by
      dsimp [e2]
      exact Finite.card_pos).ne'
  have hpoint : ∀ q : Gal(L/K) ⧸ H,
      truncateENatAtDVF
          (fixedFieldRamificationNumber
            (base := base) (target := target) huniq H
            (IsGalois.normalAutEquivQuotient H q)) (t + 1) =
        (1 / e2 : ℝ) *
          ∑ gamma : NonarchimedeanDepth.QuotientFiber H q,
            truncateENatAtDVF (D.depth (gamma : Gal(L/K))) (s + 1) := by
    intro q
    by_cases hq : q = 1
    · subst q
      rw [map_one]
      have hone :
          fixedFieldRamificationNumber
              (base := base) (target := target) huniq H 1 = ⊤ := by
        rw [ENat.eq_top_iff_forall_ge]
        intro m
        cases m with
        | zero => exact bot_le
        | succ n =>
            rw [← mem_fixedFieldLowerRamificationGroup_nat_iff
              (base := base) (target := target) huniq H n 1]
            exact Subgroup.one_mem _
      rw [hone, truncateENatAtDVF_top, ← heta2]
      change (D.depthLowerFiltration H).herbrandFunction s + 1 =
        (1 / D.depthRamificationIndex H : ℝ) *
          ∑ gamma : NonarchimedeanDepth.QuotientFiber H 1,
            truncateENatAtDVF (D.depth (gamma : Gal(L/K))) (s + 1)
      rw [depth_herbrandFunction_add_one_eq_average D H hs]
      congr 1
      have hsumOne :
          (∑ tau : H,
              truncateENatAtDVF
                (D.depth ((1 : Gal(L/K)) * (tau : Gal(L/K)))) (s + 1)) =
            ∑ gamma : NonarchimedeanDepth.QuotientFiber H
                (QuotientGroup.mk' H (1 : Gal(L/K))),
              truncateENatAtDVF
                (D.depth (gamma : Gal(L/K))) (s + 1) :=
        (NonarchimedeanDepth.sum_quotientFiber_eq_sum_subgroup H
          (fun sigma => truncateENatAtDVF (D.depth sigma) (s + 1))
          (1 : Gal(L/K))).symm
      convert hsumOne using 1
      · simp only [one_mul]
      · rfl
    · obtain ⟨sigma, rfl⟩ := QuotientGroup.mk'_surjective H q
      obtain ⟨hfinite, havg⟩ :=
        fixedFieldRamificationNumber_untop_eq_quotientFiberAverage
          (base := base) (target := target) huniq H sigma hq
      rw [← WithTop.coe_untop
        (fixedFieldRamificationNumber
          (base := base) (target := target) huniq H
          (IsGalois.normalAutEquivQuotient H (QuotientGroup.mk' H sigma)))
        hfinite]
      change min
          ((fixedFieldRamificationNumber
            (base := base) (target := target) huniq H
            (IsGalois.normalAutEquivQuotient H
              (sigma : Gal(L/K) ⧸ H))).untop hfinite : ℝ) (t + 1) = _
      rw [havg, ← heta2]
      change min (D.quotientFiberAverage H hq)
          ((D.depthLowerFiltration H).herbrandFunction s + 1) =
        (1 / D.depthRamificationIndex H : ℝ) *
          ∑ gamma : NonarchimedeanDepth.QuotientFiber
              H (QuotientGroup.mk' H sigma),
            truncateENatAtDVF (D.depth (gamma : Gal(L/K))) (s + 1)
      exact min_quotientFiberAverage_eq_average_truncate D H hq hs
  have hsum :
      (∑ alpha : Gal((fixedFieldDVF (K := K) H)/K),
          truncateENatAtDVF
            (fixedFieldRamificationNumber
              (base := base) (target := target) huniq H alpha) (t + 1)) =
        (1 / e2 : ℝ) *
          ∑ sigma : Gal(L/K),
            truncateENatAtDVF (D.depth sigma) (s + 1) := by
    calc
      _ = ∑ q : Gal(L/K) ⧸ H,
          truncateENatAtDVF
            (fixedFieldRamificationNumber
              (base := base) (target := target) huniq H
              (IsGalois.normalAutEquivQuotient H q)) (t + 1) :=
        (Equiv.sum_comp (IsGalois.normalAutEquivQuotient H).toEquiv _).symm
      _ = ∑ q : Gal(L/K) ⧸ H,
          (1 / e2 : ℝ) *
            ∑ gamma : NonarchimedeanDepth.QuotientFiber H q,
              truncateENatAtDVF (D.depth (gamma : Gal(L/K))) (s + 1) := by
        apply Finset.sum_congr rfl
        intro q _
        exact hpoint q
      _ = (1 / e2 : ℝ) *
          ∑ q : Gal(L/K) ⧸ H,
            ∑ gamma : NonarchimedeanDepth.QuotientFiber H q,
              truncateENatAtDVF (D.depth (gamma : Gal(L/K))) (s + 1) := by
        rw [Finset.mul_sum]
      _ = _ := by
        congr 1
        exact NonarchimedeanDepth.sum_quotientFiber H
          (fun sigma => truncateENatAtDVF (D.depth sigma) (s + 1))
  have h0 := herbrandFunctionOfUniqueExtension_eq_intrinsicRamificationNumber_sum
    (base := base) (target := target) huniq hs
  have h1 := fixedField_herbrandFunction_formula_dvf
    (base := base) (target := target) huniq H ht
  change herbrandFunctionOfUniqueExtension
      (base := base) (target := target) huniq s =
    fixedFieldHerbrandFunction
      (base := base) (target := target) huniq H t
  rw [h0, h1, hsum]
  change (1 / (e0 : ℝ)) *
      (∑ sigma : Gal(L/K),
        truncateENatAtDVF (D.depth sigma) (s + 1)) - 1 =
    (1 / (e1 : ℝ)) *
      ((1 / (e2 : ℝ)) *
        ∑ sigma : Gal(L/K),
          truncateENatAtDVF (D.depth sigma) (s + 1)) - 1
  rw [hetower]
  push_cast
  field_simp


/-- States the theorem `herbrandFunction_trans`. -/
theorem herbrandFunction_trans
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (s : ℝ) :
    herbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq s =
      fixedFieldHerbrandFunction
        (base := base) (target := target) huniq H
        ((fixedFieldSubextensionFiltration
          (lowerRamificationFiltrationOfUniqueExtension
            (base := base) (target := target) huniq) H).herbrandFunction s) := by
  by_cases hs : -1 ≤ s
  · exact herbrandFunction_trans_of_neg_one_le
      (base := base) (target := target) huniq H hs
  · have hs0 : s ≤ 0 := by linarith
    let F := lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq
    let Q := fixedFieldLowerRamificationFiltration
      (base := base) (target := target) huniq H
    let S := fixedFieldSubextensionFiltration F H
    change
      (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction F) s = Q.herbrandFunction (S.herbrandFunction s)
    rw [(RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_of_nonpos F) hs0,
      S.herbrandFunction_of_nonpos hs0,
      Q.herbrandFunction_of_nonpos hs0]

/-- The quotient-filtration comparison over the stated discretely valued field hypotheses
hypotheses: inverse Herbrand functions compose in reverse tower order. -/
theorem inverseHerbrandFunction_trans
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (t : ℝ) :
    inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq t =
      (fixedFieldSubextensionFiltration
        (lowerRamificationFiltrationOfUniqueExtension
          (base := base) (target := target) huniq) H).inverseHerbrandFunction
        (fixedFieldInverseHerbrandFunction
          (base := base) (target := target) huniq H t) := by
  let F := lowerRamificationFiltrationOfUniqueExtension
    (base := base) (target := target) huniq
  let Q := fixedFieldLowerRamificationFiltration
    (base := base) (target := target) huniq H
  let S := fixedFieldSubextensionFiltration F H
  have heta : ∀ s : ℝ,
      (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction F) s = Q.herbrandFunction (S.herbrandFunction s) := by
    intro s
    simpa [F, Q, S, fixedFieldHerbrandFunction] using
      herbrandFunction_trans
        (base := base) (target := target) huniq H s
  change
    (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction F) t = S.inverseHerbrandFunction (Q.inverseHerbrandFunction t)
  apply
    (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_strictMono F).injective
  rw [(RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_inverseHerbrandFunction F)]
  rw [heta]
  rw [S.herbrandFunction_inverseHerbrandFunction,
    Q.herbrandFunction_inverseHerbrandFunction]

/-- The tower-filtration comparison over the stated discretely valued field hypotheses
hypotheses: upper numbering is invariant under a Galois quotient. -/
theorem upperRamificationGroup_quotient
    [Algebra.IsSeparable base.residueField target.residueField]
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] (t : ℝ) :
    Subgroup.map (QuotientGroup.mk' H)
        (upperRamificationGroupOfUniqueExtension
          (base := base) (target := target) huniq t) =
      Subgroup.comap (IsGalois.normalAutEquivQuotient H).toMonoidHom
        (fixedFieldUpperRamificationGroup
          (base := base) (target := target) huniq H t) := by
  unfold upperRamificationGroupOfUniqueExtension
  unfold fixedFieldUpperRamificationGroup
  have h107 := lowerRamificationGroup_quotient
    (base := base) (target := target) huniq H
    (inverseHerbrandFunctionOfUniqueExtension
      (base := base) (target := target) huniq t)
  have hparam :
      (fixedFieldSubextensionFiltration
        (lowerRamificationFiltrationOfUniqueExtension
          (base := base) (target := target) huniq) H).herbrandFunction
        (inverseHerbrandFunctionOfUniqueExtension
          (base := base) (target := target) huniq t) =
        fixedFieldInverseHerbrandFunction
          (base := base) (target := target) huniq H t := by
    rw [inverseHerbrandFunction_trans
      (base := base) (target := target) huniq H t]
    exact
      (fixedFieldSubextensionFiltration
        (lowerRamificationFiltrationOfUniqueExtension
          (base := base) (target := target) huniq) H).herbrandFunction_inverseHerbrandFunction _
  rw [hparam] at h107
  exact h107
end Higher
end RamificationTheory.HilbertRamification
