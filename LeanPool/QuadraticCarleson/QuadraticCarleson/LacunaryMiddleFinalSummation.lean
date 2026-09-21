/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleKalton
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveHighHeightLacunaryEndpoint

/-!
# Finite residue summation and the final lacunary middle Orlicz budget

The sparse modulus remains the paper's exact `10^10`. Summing a complete
finite residue system contributes only that universal factor. The independent
factor `20` occurs in the height cutoff `B_k = 20 · 2^(2^k)`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace LacunaryMiddleFinalSummation

open LacunaryMiddleRange LacunaryMiddleOperator LacunaryMiddleKalton
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate
open CalderonZygmundStoppingIntervals PositiveLowFullEstimate


abbrev SparseResidue := Fin sparseModulus.toNat

/-- A complete finite residue system for the source modulus. -/
theorem existsUnique_sparseResidue (τ : ℤ) :
    ∃! ρ : SparseResidue, τ ≡ (ρ.val : ℤ) [ZMOD sparseModulus] := by
  have hM : 0 < sparseModulus := by norm_num [sparseModulus]
  have hnonneg : 0 ≤ τ % sparseModulus := Int.emod_nonneg _ hM.ne'
  have hlt : τ % sparseModulus < sparseModulus := Int.emod_lt_of_pos _ hM
  let ρ : SparseResidue := ⟨(τ % sparseModulus).toNat, by
    omega⟩
  have hρ : (ρ.val : ℤ) = τ % sparseModulus := Int.toNat_of_nonneg hnonneg
  refine ⟨ρ, ?_, ?_⟩
  · change τ ≡ (ρ.val : ℤ) [ZMOD sparseModulus]
    rw [hρ]
    exact (Int.mod_modEq τ sparseModulus).symm
  · intro σ hσ
    have hσlt : (σ.val : ℤ) < sparseModulus := by
      have hs := σ.isLt
      change σ.val < sparseModulus.toNat at hs
      omega
    have hσmod := hσ.eq
    rw [Int.emod_eq_of_lt (Nat.cast_nonneg _) hσlt] at hσmod
    apply Fin.ext
    have hcast : (σ.val : ℤ) = (ρ.val : ℤ) := hσmod.symm.trans hρ.symm
    exact_mod_cast hcast

/-- Each block belongs to exactly one of the finitely many sparse classes. -/
theorem sum_sparseResidue_indicator (τ : ℤ) (a : ℝ≥0∞) :
    (∑ ρ : SparseResidue, if τ ≡ (ρ.val : ℤ) [ZMOD sparseModulus] then a else 0) = a := by
  obtain ⟨ρ, hρ, huniq⟩ := existsUnique_sparseResidue τ
  rw [Finset.sum_eq_single ρ]
  · simp only [ite_eq_left hρ]
  · intro σ hσ hne
    have hnot : ¬τ ≡ (σ.val : ℤ) [ZMOD sparseModulus] := fun h ↦ hne (huniq σ h)
    simp only [ite_eq_right hnot]
  · simp

theorem sum_sparseFrozenBlockInputL1Mass_eq
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ : ℤ) :
    (∑ ρ : SparseResidue, sparseFrozenBlockInputL1Mass A f k B c (ρ.val : ℤ) τ) =
      frozenBlockInputL1Mass A f k B c τ :=
  sum_sparseResidue_indicator τ _

/-- Exact interchange of the finite residue sum and the countable block sum. -/
theorem tsum_frozenBlockInputL1Mass_eq_sum_residues
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) :
    (∑' τ : ℤ, frozenBlockInputL1Mass A f k B c τ) =
      ∑ ρ : SparseResidue, ∑' τ : ℤ,
        sparseFrozenBlockInputL1Mass A f k B c (ρ.val : ℤ) τ := by
  simp_rw [← sum_sparseFrozenBlockInputL1Mass_eq A f k B c]
  exact Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)

/-- Factor two from subtracting atom averages, times the exact residue count. -/
noncomputable def frozenMassPackingConstant : ℝ≥0∞ := 2 * (sparseModulus.toNat : ℝ≥0∞)

theorem frozenMassPackingConstant_eq : frozenMassPackingConstant = 20000000000 := by
  norm_num [frozenMassPackingConstant, sparseModulus, Int.toNat]

theorem frozenMassPackingConstant_lt_top : frozenMassPackingConstant < ∞ := by
  rw [frozenMassPackingConstant_eq]
  finiteness

/-- No sparse residue classes are discarded: their complete finite sum gives
the actual all-block input-mass packing bound. -/
theorem tsum_frozenBlockInputL1Mass_le_levelMass
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k B c : ℕ} (hAk : 0 ≤ A k) (hB : 0 < B) (hc : 2 * c ≤ 5 * B) :
    (∑' τ : ℤ, frozenBlockInputL1Mass A f k B c τ) ≤
      frozenMassPackingConstant * magnitudeLevelL1Mass volume A f k := by
  rw [tsum_frozenBlockInputL1Mass_eq_sum_residues]
  calc
    _ ≤ ∑ _ρ : SparseResidue, 2 * magnitudeLevelL1Mass volume A f k := by
      apply Finset.sum_le_sum
      intro ρ hρ
      exact tsum_sparseFrozenBlockInputL1Mass_le_levelMass hf hAk hB hc (ρ.val : ℤ)
    _ = frozenMassPackingConstant * magnitudeLevelL1Mass volume A f k := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        frozenMassPackingConstant]
      ring

/-- Collapse the complete block budget to the actual magnitude-level masses. -/
theorem frozenLogSquaredMassBudget_le_levelMass
    {f : ℝ → ℂ} (hf : Measurable f) {B : ℕ → ℕ} {c : ℕ}
    (hB : ∀ k, 0 < B k) (hc : ∀ k, 2 * c ≤ 5 * B k) :
    frozenLogSquaredMassBudget f B c ≤ frozenMassPackingConstant *
      ∑' k : ℕ, ENNReal.ofReal
        (paperLog 1 ((k : ℝ) + 2) * paperLog 1 (B k : ℝ) ^ 2) *
          magnitudeLevelL1Mass volume lacunaryAmplitude f k := by
  unfold frozenLogSquaredMassBudget
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  have h := mul_le_mul' (le_refl (ENNReal.ofReal
    (paperLog 1 ((k : ℝ) + 2) * paperLog 1 (B k : ℝ) ^ 2)))
    (tsum_frozenBlockInputL1Mass_le_levelMass hf (lacunaryAmplitude_pos k).le (hB k) (hc k))
  simpa only [mul_left_comm] using h

noncomputable def frozenMiddleOrliczConstant : ℝ≥0∞ :=
  frozenMassPackingConstant * ENNReal.ofReal (lacunaryLowLevelConstant 20)

theorem frozenMiddleOrliczConstant_lt_top : frozenMiddleOrliczConstant < ∞ :=
  ENNReal.mul_lt_top frozenMassPackingConstant_lt_top ENNReal.ofReal_lt_top

theorem lacunaryLowLevelConstant_twenty_nonneg : 0 ≤ lacunaryLowLevelConstant 20 := by
  exact add_nonneg (lacunarySmallLevelConstant_nonneg (by norm_num))
    (mul_nonneg (by norm_num) (sq_nonneg _))

/-- Exact paper cutoff and complete sparse residue sum, with no assumed
summability or assumed final Orlicz inequality. -/
theorem frozenLogSquaredMassBudget_paperCutoff_le_orlicz
    {f : ℝ → ℂ} (hf : Measurable f) {c : ℕ}
    (hc : ∀ k, 2 * c ≤ 5 * lacunaryHighCutoff k) :
    frozenLogSquaredMassBudget f lacunaryHighCutoff c ≤
      frozenMiddleOrliczConstant *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖) := by
  have hmass := frozenLogSquaredMassBudget_le_levelMass hf lacunaryHighCutoff_pos hc
  simp_rw [cast_lacunaryHighCutoff] at hmass
  have hlevel := tsum_lacunaryLowWeight_mul_levelMass_le_orlicz volume
    (C := 20) (by norm_num) hf
  have h := hmass.trans (mul_le_mul' (le_refl frozenMassPackingConstant) hlevel)
  simp_rw [ENNReal.ofReal_mul lacunaryLowLevelConstant_twenty_nonneg] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  simpa only [frozenMiddleOrliczConstant, mul_assoc] using h

/-- The support convention `C₀ = 1` corresponds to `c = 0` and requires no
additional geometric hypothesis. -/
theorem frozenLogSquaredMassBudget_paperCutoff_zero_le_orlicz
    {f : ℝ → ℂ} (hf : Measurable f) :
    frozenLogSquaredMassBudget f lacunaryHighCutoff 0 ≤
      frozenMiddleOrliczConstant *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖) :=
  frozenLogSquaredMassBudget_paperCutoff_le_orlicz hf (by intro k; omega)

theorem frozenLogSquaredMassBudget_paperCutoff_lt_top
    {f : ℝ → ℂ} (hf : Measurable f) {c : ℕ}
    (hc : ∀ k, 2 * c ≤ 5 * lacunaryHighCutoff k)
    (horlicz : (∫⁻ x, ENNReal.ofReal
      (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖)) < ∞) :
    frozenLogSquaredMassBudget f lacunaryHighCutoff c < ∞ :=
  (frozenLogSquaredMassBudget_paperCutoff_le_orlicz hf hc).trans_lt
    (ENNReal.mul_lt_top frozenMiddleOrliczConstant_lt_top horlicz)

/-- Kalton's actual frozen main output has the final lacunary Orlicz bound,
conditional only on the individual finite-block weak estimate. -/
theorem lacunaryFrozenMainOutput_paperCutoff_compl_levelSet_mul_le_orlicz
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {c : ℕ} {C : ℝ} (hc : ∀ k, 2 * c ≤ 5 * lacunaryHighCutoff k)
    (hblock : HasLogSquaredFrozenBlockWeakBounds f lacunaryHighCutoff c C)
    {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal a * volume
      ({x | ENNReal.ofReal a < lacunaryFrozenMainOutput f lacunaryHighCutoff c x} ∩
        (fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength)ᶜ) ≤
      (24 * ENNReal.ofReal C * frozenMiddleOrliczConstant) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖) := by
  refine (lacunaryFrozenMainOutput_compl_levelSet_mul_le_logSquaredMass hf hfi hblock ha).trans ?_
  simpa only [mul_assoc] using mul_le_mul' (le_refl (24 * ENNReal.ofReal C))
    (frozenLogSquaredMassBudget_paperCutoff_le_orlicz hf hc)

theorem lacunaryFrozenMainOutput_paperCutoff_compl_levelSet_one_le_orlicz
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {c : ℕ} {C : ℝ} (hc : ∀ k, 2 * c ≤ 5 * lacunaryHighCutoff k)
    (hblock : HasLogSquaredFrozenBlockWeakBounds f lacunaryHighCutoff c C) :
    volume
      ({x | 1 < lacunaryFrozenMainOutput f lacunaryHighCutoff c x} ∩
        (fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength)ᶜ) ≤
      (24 * ENNReal.ofReal C * frozenMiddleOrliczConstant) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖) := by
  simpa only [ENNReal.ofReal_one, one_mul] using
    lacunaryFrozenMainOutput_paperCutoff_compl_levelSet_mul_le_orlicz hf hfi hc hblock
      (by norm_num : (0 : ℝ) < 1)

theorem lintegral_enorm_le_lacunaryOrlicz (f : ℝ → ℂ) :
    (∫⁻ x, ‖f x‖ₑ) ≤
      ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖) := by
  apply lintegral_mono
  intro x
  change ‖f x‖ₑ ≤ ENNReal.ofReal _
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_one, mul_assoc] using
    mul_le_mul_of_nonneg_left (one_le_lacunaryEndpointFactor (norm_nonneg (f x)))
      (norm_nonneg (f x))

/-- The canonical fivefold exceptional set is included, with its explicit
mass cost absorbed into the same Orlicz modular. -/
theorem lacunaryFrozenMainOutput_paperCutoff_levelSet_one_le_orlicz
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {c : ℕ} {C : ℝ} (hc : ∀ k, 2 * c ≤ 5 * lacunaryHighCutoff k)
    (hblock : HasLogSquaredFrozenBlockWeakBounds f lacunaryHighCutoff c C) :
    volume {x | 1 < lacunaryFrozenMainOutput f lacunaryHighCutoff c x} ≤
      (5 + 24 * ENNReal.ofReal C * frozenMiddleOrliczConstant) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖) := by
  refine (lacunaryFrozenMainOutput_levelSet_one_le_logSquaredMass hf hfi hblock).trans ?_
  rw [add_mul]
  apply add_le_add
  · exact mul_le_mul' le_rfl (lintegral_enorm_le_lacunaryOrlicz f)
  · simpa only [mul_assoc] using mul_le_mul' (le_refl (24 * ENNReal.ofReal C))
      (frozenLogSquaredMassBudget_paperCutoff_le_orlicz hf hc)

/-- A completely specified geometric convention: no additional assumption on
the scale/block arrangement remains. The individual-block analytic input is
still displayed explicitly. -/
theorem lacunaryFrozenMainOutput_paperCutoff_zero_levelSet_one_le_orlicz
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) {C : ℝ}
    (hblock : HasLogSquaredFrozenBlockWeakBounds f lacunaryHighCutoff 0 C) :
    volume {x | 1 < lacunaryFrozenMainOutput f lacunaryHighCutoff 0 x} ≤
      (5 + 24 * ENNReal.ofReal C * frozenMiddleOrliczConstant) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖) :=
  lacunaryFrozenMainOutput_paperCutoff_levelSet_one_le_orlicz hf hfi
    (by intro k; omega) hblock


end LacunaryMiddleFinalSummation
end QuadraticCarleson
