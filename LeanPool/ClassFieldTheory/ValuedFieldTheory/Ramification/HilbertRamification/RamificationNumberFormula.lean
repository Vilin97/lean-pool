/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumber
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction
/-!
# Herbrand-function sum formula for a general discretely valued field

This is the field-facing, noncomplete form of
the Herbrand-function sum formula.  The monogenic integral-generator theorem
supplies the generator hidden inside
`intrinsicRamificationNumberOfUniqueExtension`; the public endpoint therefore
uses exactly the canonical standing hypotheses and has no generator parameter.
-/

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  card_lower_succ_eq_sum_indicator →
    card_lower_succ_eq_sum_indicator

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction_eq_depth_sum_of_mem_Icc →
    herbrandFunction_eq_depth_sum_of_mem_Icc

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction_of_nonpos →
    herbrandFunction_of_nonpos

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  truncatedLowerDepth →
    truncatedLowerDepth


noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher


variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
variable [IsGalois K L]
variable [Algebra.IsSeparable base.residueField target.residueField]

/-- The finite Galois group is equipped with an enumeration for ramification-group sums. -/
local instance galoisFintype : Fintype Gal(L/K) :=
  Fintype.ofFinite Gal(L/K)

/-- Each subgroup of the finite Galois group is equipped with a finite enumeration. -/
local instance subgroupFintype (H : Subgroup Gal(L/K)) : Fintype H :=
  Fintype.ofFinite H

/-- Classical decidability of membership in a subgroup of the Galois group. -/
local instance subgroupMembershipDecidable
    (H : Subgroup Gal(L/K)) (sigma : Gal(L/K)) : Decidable (sigma ∈ H) :=
  Classical.propDecidable _

/-- `min {i,r}`, with the extended value `infinity` truncated to `r`. -/
def truncateENatAtDVF (i : ℕ∞) (r : ℝ) : ℝ :=
  ENat.recTopCoe r (fun n => min (n : ℝ) r) i

/-- States the theorem `truncateENatAtDVF_top`. -/
@[simp] theorem truncateENatAtDVF_top (r : ℝ) :
    truncateENatAtDVF ⊤ r = r := by
  simp [truncateENatAtDVF]

/-- States the theorem `truncateENatAtDVF_coe`. -/
@[simp] theorem truncateENatAtDVF_coe (n : ℕ) (r : ℝ) :
    truncateENatAtDVF (n : ℕ∞) r = min (n : ℝ) r := by
  simp [truncateENatAtDVF]

/-- States the theorem `truncateENatAtDVF_eq_right_of_natCast_le`. -/
theorem truncateENatAtDVF_eq_right_of_natCast_le
    {i : ℕ∞} {m : ℕ} {r : ℝ} (hr : r ≤ m) (hi : (m : ℕ∞) ≤ i) :
    truncateENatAtDVF i r = r := by
  induction i using ENat.recTopCoe with
  | top => simp
  | coe n =>
      simp only [truncateENatAtDVF_coe]
      rw [min_eq_right]
      have hmn : m ≤ n := by exact_mod_cast hi
      exact hr.trans (by exact_mod_cast hmn)

/-- Pointwise ramification-number contribution for an element of inertia. -/
theorem truncate_intrinsicRamificationNumberOfUniqueExtension_eq_intrinsic_summand
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (m : ℕ) {s : ℝ} (hms : (m : ℝ) ≤ s) (hsm : s ≤ m + 1)
    (sigma : (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq).lower 0) :
    truncateENatAtDVF
        (intrinsicRamificationNumberOfUniqueExtension
          (base := base) (target := target) huniq (sigma : Gal(L/K)))
        (s + 1) =
      1 + ((truncatedLowerDepth (lowerRamificationFiltrationOfUniqueExtension (base := base)
        (target := target) huniq)) m sigma : ℝ) +
      (s - m) *
        (if (sigma : Gal(L/K)) ∈ (lowerRamificationFiltrationOfUniqueExtension
          (base := base) (target := target) huniq).lower (m + 1)
        then 1 else 0) := by
  classical
  let F := lowerRamificationFiltrationOfUniqueExtension
    (base := base) (target := target) huniq
  let i := intrinsicRamificationNumberOfUniqueExtension
    (base := base) (target := target) huniq (sigma : Gal(L/K))
  change truncateENatAtDVF i (s + 1) =
    1 + ((truncatedLowerDepth F) m sigma : ℝ) +
      (s - m) * (if (sigma : Gal(L/K)) ∈ F.lower (m + 1) then 1 else 0)
  have hi_one : (1 : ℕ∞) ≤ i := by
    exact (mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
      (base := base) (target := target) huniq 0 (sigma : Gal(L/K))).1 sigma.property
  by_cases hhigh : ((m + 2 : ℕ) : ℕ∞) ≤ i
  · have hmem : (sigma : Gal(L/K)) ∈ F.lower (m + 1) := by
      exact (mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
        (base := base) (target := target) huniq (m + 1)
          (sigma : Gal(L/K))).2 (by simpa [i, Nat.add_assoc] using hhigh)
    have hdepth :
      (truncatedLowerDepth F) m sigma = m := by
      rw [truncatedLowerDepth]
      rw [Finset.filter_eq_self.2]
      · simp
      · intro j hj
        exact (mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
          (base := base) (target := target) huniq (j + 1)
            (sigma : Gal(L/K))).2 (by
              have hjm : j < m := Finset.mem_range.1 hj
              have : ((j + 2 : ℕ) : ℕ∞) ≤ (m + 2 : ℕ) := by
                exact_mod_cast (by omega : j + 2 ≤ m + 2)
              exact (by simpa [i, Nat.add_assoc] using this.trans hhigh))
    have htrunc : truncateENatAtDVF i (s + 1) = s + 1 := by
      exact truncateENatAtDVF_eq_right_of_natCast_le
        (m := m + 2) (by
          norm_num [Nat.cast_add, Nat.cast_ofNat] at hsm ⊢
          linarith) hhigh
    rw [htrunc, hdepth]
    simp [hmem]
    ring
  · have hlt : i < ((m + 2 : ℕ) : ℕ∞) := lt_of_not_ge hhigh
    have hine : i ≠ ⊤ := ne_top_of_lt hlt
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hine
    have hk_one : 1 ≤ k := by
      exact_mod_cast (hi_one.trans_eq hk.symm)
    have hk_upper : k ≤ m + 1 := by
      have : k < m + 2 := by exact_mod_cast (hk.symm ▸ hlt)
      omega
    have hmem : (sigma : Gal(L/K)) ∉ F.lower (m + 1) := by
      intro hmem
      have hge :=
        (mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
          (base := base) (target := target) huniq (m + 1)
            (sigma : Gal(L/K))).1 hmem
      exact hhigh (by simpa [i, Nat.add_assoc] using hge)
    have hdepth :
      (truncatedLowerDepth F) m sigma = k - 1 := by
      rw [truncatedLowerDepth]
      have hfilter :
          (Finset.range m).filter
              (fun j => (sigma : Gal(L/K)) ∈ F.lower (j + 1)) =
            Finset.range (k - 1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        have hthreshold :
            ((sigma : Gal(L/K)) ∈ F.lower (j + 1)) ↔ j + 2 ≤ k := by
          change
            ((sigma : Gal(L/K)) ∈ lowerRamificationGroup
              (base := base) (target := target) huniq ((j + 1 : ℕ) : ℝ)) ↔
                j + 2 ≤ k
          rw [mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
            (base := base) (target := target) huniq]
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
    simp only [lowerRamificationFiltrationOfUniqueExtension_lower, hmem, ↓reduceIte, mul_zero,
      add_zero]
    exact_mod_cast (by omega : k = 1 + (k - 1))

/-- States the theorem
`truncate_intrinsicRamificationNumberOfUniqueExtension_eq_zero_of_not_mem_inertia`. -/
theorem truncate_intrinsicRamificationNumberOfUniqueExtension_eq_zero_of_not_mem_inertia
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {s : ℝ} (hs : -1 ≤ s) {sigma : Gal(L/K)}
    (hsigma : sigma ∉ (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq).lower 0) :
    truncateENatAtDVF
        (intrinsicRamificationNumberOfUniqueExtension
          (base := base) (target := target) huniq sigma) (s + 1) = 0 := by
  have hi : intrinsicRamificationNumberOfUniqueExtension
      (base := base) (target := target) huniq sigma < 1 := by
    rw [← not_le]
    intro hi
    exact hsigma
      ((mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
        (base := base) (target := target) huniq 0 sigma).2 hi)
  have hi0 : intrinsicRamificationNumberOfUniqueExtension
      (base := base) (target := target) huniq sigma = 0 :=
    Order.lt_one_iff.1 hi
  rw [hi0]
  simp [truncateENatAtDVF,
    min_eq_left (show (0 : ℝ) ≤ s + 1 by linarith)]

/-- States the theorem
`sum_truncate_intrinsicRamificationNumberOfUniqueExtension_eq_sum_inertia`. -/
theorem sum_truncate_intrinsicRamificationNumberOfUniqueExtension_eq_sum_inertia
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {s : ℝ} (hs : -1 ≤ s) :
    (∑ sigma : Gal(L/K), truncateENatAtDVF
      (intrinsicRamificationNumberOfUniqueExtension
        (base := base) (target := target) huniq sigma) (s + 1)) =
    ∑ sigma : (lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq).lower 0,
      truncateENatAtDVF
        (intrinsicRamificationNumberOfUniqueExtension
          (base := base) (target := target) huniq (sigma : Gal(L/K))) (s + 1) := by
  classical
  let H := (lowerRamificationFiltrationOfUniqueExtension
    (base := base) (target := target) huniq).lower 0
  let q : Gal(L/K) → ℝ := fun sigma => truncateENatAtDVF
    (intrinsicRamificationNumberOfUniqueExtension
      (base := base) (target := target) huniq sigma) (s + 1)
  calc
    ∑ sigma : Gal(L/K), q sigma =
        ∑ sigma : Gal(L/K), if sigma ∈ H then q sigma else 0 := by
      apply Finset.sum_congr rfl
      intro sigma _
      by_cases hsigma : sigma ∈ H
      · simp [hsigma]
      · rw [ite_eq_right hsigma]
        exact truncate_intrinsicRamificationNumberOfUniqueExtension_eq_zero_of_not_mem_inertia
          (base := base) (target := target) huniq hs hsigma
    _ = ∑ sigma : H, q (sigma : Gal(L/K)) := by
      rw [← Finset.sum_filter (p := fun sigma : Gal(L/K) => sigma ∈ H)]
      simpa only [Finset.subtype_univ] using
          (Finset.sum_subtype_eq_sum_filter
            (s := (Finset.univ : Finset Gal(L/K))) q
            (p := fun sigma : Gal(L/K) => sigma ∈ H)).symm

/-- States the theorem
`sum_inertia_truncate_intrinsicRamificationNumberOfUniqueExtension_eq_intrinsic`. -/
theorem sum_inertia_truncate_intrinsicRamificationNumberOfUniqueExtension_eq_intrinsic
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (m : ℕ) {s : ℝ} (hms : (m : ℝ) ≤ s) (hsm : s ≤ m + 1) :
    (∑ sigma : (lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq).lower 0,
      truncateENatAtDVF
        (intrinsicRamificationNumberOfUniqueExtension
          (base := base) (target := target) huniq (sigma : Gal(L/K))) (s + 1)) =
      Nat.card ((lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq).lower 0) +
      (∑ sigma : (lowerRamificationFiltrationOfUniqueExtension
          (base := base) (target := target) huniq).lower 0,
        ((truncatedLowerDepth (lowerRamificationFiltrationOfUniqueExtension (base := base)
          (target := target) huniq)) m sigma : ℝ)) +
      (s - m) * Nat.card ((lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq).lower (m + 1)) := by
  classical
  let F := lowerRamificationFiltrationOfUniqueExtension
    (base := base) (target := target) huniq
  change (∑ sigma : F.lower 0, truncateENatAtDVF
      (intrinsicRamificationNumberOfUniqueExtension
        (base := base) (target := target) huniq (sigma : Gal(L/K))) (s + 1)) =
    (Nat.card (F.lower 0) : ℝ) +
      (∑ sigma : F.lower 0,
        ((truncatedLowerDepth F) m sigma : ℝ)) +
      (s - m) * Nat.card (F.lower (m + 1))
  simp_rw [truncate_intrinsicRamificationNumberOfUniqueExtension_eq_intrinsic_summand
    (base := base) (target := target) huniq m hms hsm]
  have hindicator :
      (∑ sigma : F.lower 0,
        (if (sigma : Gal(L/K)) ∈ F.lower (m + 1) then (1 : ℝ) else 0)) =
        Nat.card (F.lower (m + 1)) := by
    exact_mod_cast
      ((card_lower_succ_eq_sum_indicator F) m).symm
  change Finset.sum Finset.univ (fun sigma : F.lower 0 =>
      (1 : ℝ) +
        ((truncatedLowerDepth F) m sigma : ℝ) +
        (s - m) *
          (if (sigma : Gal(L/K)) ∈ F.lower (m + 1) then 1 else 0)) = _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [hindicator]
  simp

/-- The Herbrand-function sum formula under the stated discretely valued field
assumptions.  The generator from the monogenic integral-generator theorem is internal to the
  canonical
ramification number, so this endpoint has no generator hypothesis. -/
theorem herbrandFunctionOfUniqueExtension_eq_intrinsicRamificationNumber_sum
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {s : ℝ} (hs : -1 ≤ s) :
    herbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq s =
      (1 / Nat.card ((lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq).lower 0) : ℝ) *
        (∑ sigma : Gal(L/K), truncateENatAtDVF
          (intrinsicRamificationNumberOfUniqueExtension
            (base := base) (target := target) huniq sigma) (s + 1)) - 1 := by
  classical
  let F := lowerRamificationFiltrationOfUniqueExtension
    (base := base) (target := target) huniq
  change
    (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
    F) s =
    (1 / Nat.card (F.lower 0) : ℝ) *
      (∑ sigma : Gal(L/K), truncateENatAtDVF
        (intrinsicRamificationNumberOfUniqueExtension
          (base := base) (target := target) huniq sigma) (s + 1)) - 1
  have hcard : (Nat.card (F.lower 0) : ℝ) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (show 0 < Nat.card (F.lower 0) from Finite.card_pos))
  rw [sum_truncate_intrinsicRamificationNumberOfUniqueExtension_eq_sum_inertia
    (base := base) (target := target) huniq hs]
  by_cases hs0 : 0 ≤ s
  · let m := ⌊s⌋₊
    have hms : (m : ℝ) ≤ s := Nat.floor_le hs0
    have hsm : s ≤ m + 1 := (Nat.lt_floor_add_one s).le
    rw [sum_inertia_truncate_intrinsicRamificationNumberOfUniqueExtension_eq_intrinsic
      (base := base) (target := target) huniq m hms hsm]
    rw [(herbrandFunction_eq_depth_sum_of_mem_Icc F) m hms hsm]
    field_simp
    ring
  · have hsle : s ≤ 0 := le_of_not_ge hs0
    rw [(herbrandFunction_of_nonpos F) hsle]
    have hpoint : ∀ sigma : F.lower 0,
        truncateENatAtDVF
          (intrinsicRamificationNumberOfUniqueExtension
            (base := base) (target := target) huniq (sigma : Gal(L/K)))
          (s + 1) = s + 1 := by
      intro sigma
      have hi : (1 : ℕ∞) ≤ intrinsicRamificationNumberOfUniqueExtension
          (base := base) (target := target) huniq (sigma : Gal(L/K)) :=
        (mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
          (base := base) (target := target) huniq 0
            (sigma : Gal(L/K))).1 sigma.property
      exact truncateENatAtDVF_eq_right_of_natCast_le
        (m := 1) (by
          norm_num at hsle ⊢
          linarith) hi
    simp_rw [hpoint]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    field_simp
    ring

end Higher
end RamificationTheory.HilbertRamification
