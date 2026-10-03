/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingNorm
public import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundLevelAtoms
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Genuine high-height estimate: disjoint level-atom inputs

The paper's high part uses the strict height range `r > B_k` and the input
`b_k = ∑ I, b_{I,k}`. This file constructs that countable disjoint atom sum,
proves its L² input bound from the actual atom estimates, and invokes the
proved real-parameter fixed-height quadratic maximal theorem.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveHighHeightEstimate

open CalderonZygmundLevelAtoms PositiveLevelIntegration

/-- The sum of level atoms over the given family of centers and interval lengths. -/
noncomputable def disjointLevelAtomSum {ι : Type*}
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (z R : ι → ℝ) (x : ℝ) : ℂ :=
  ∑' i, levelAtom A f k (z i) (R i) x

theorem levelAtom_eq_zero_of_other_mem {ι : Type*}
    {A : ℕ → ℝ} {f : ℝ → ℂ} {k : ℕ} {z R : ι → ℝ}
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i)))
    {i j : ι} (hji : j ≠ i) {x : ℝ} (hx : x ∈ centeredInterval (z i) (R i)) :
    levelAtom A f k (z j) (R j) x = 0 := by
  apply levelAtom_eq_zero_of_not_mem
  intro hxj
  exact Set.disjoint_left.mp (hdisj hji) hxj hx

/-- Disjointness makes the atom sum pointwise a single atom or zero. -/
theorem map_disjointLevelAtomSum {ι : Type*}
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (z R : ι → ℝ)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i)))
    (Φ : ℂ → ℝ≥0∞) (hΦ : Φ 0 = 0) (x : ℝ) :
    Φ (disjointLevelAtomSum A f k z R x) =
      ∑' i, Φ (levelAtom A f k (z i) (R i) x) := by
  classical
  by_cases hx : ∃ i, x ∈ centeredInterval (z i) (R i)
  · obtain ⟨i, hi⟩ := hx
    have hz : ∀ j, j ≠ i → levelAtom A f k (z j) (R j) x = 0 :=
      fun j hji ↦ levelAtom_eq_zero_of_other_mem hdisj hji hi
    rw [disjointLevelAtomSum, tsum_eq_single i hz,
      tsum_eq_single i (fun j hji ↦ by rw [hz j hji, hΦ])]
  · have hz : ∀ i, levelAtom A f k (z i) (R i) x = 0 := by
      intro i
      exact levelAtom_eq_zero_of_not_mem (fun hi ↦ hx ⟨i, hi⟩)
    simp [disjointLevelAtomSum, hz, hΦ]

theorem measurable_disjointLevelAtomSum {ι : Type*} [Countable ι]
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    (k : ℕ) (z R : ι → ℝ) : Measurable (disjointLevelAtomSum A f k z R) := by
  exact Measurable.tsum (fun i ↦ measurable_levelAtom hf k (z i) (R i))

theorem lintegral_sq_enorm_levelAtom_le
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k) {z R : ℝ} (hR : 0 < R) :
    (∫⁻ x, ‖levelAtom A f k z R x‖ₑ ^ 2) ≤
      ENNReal.ofReal (2 * A k) * ENNReal.ofReal (∫ x, ‖levelAtom A f k z R x‖) := by
  have hbound (x : ℝ) : ‖levelAtom A f k z R x‖ₑ ≤ ENNReal.ofReal (2 * A k) := by
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal
      (norm_levelAtom_le_two_mul hAk hR x)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (2 * A k) * ‖levelAtom A f k z R x‖ₑ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [pow_two]
      exact mul_le_mul' (hbound x) le_rfl
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by finiteness)]
      congr 1
      symm
      simpa only [ofReal_norm] using ofReal_integral_eq_lintegral_ofReal
        (integrable_levelAtom hf hAk z R).norm
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg (levelAtom A f k z R x))

/-- Countable disjoint summation loses no overlap constant. The atom L²
estimate becomes `‖b_k‖₂² ≤ 4 A_k ∫_{F_k}|f|`. -/
theorem disjointLevelAtomSum_sq_lintegral_le {ι : Type*} [Countable ι]
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k) (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∫⁻ x, ‖disjointLevelAtomSum A f k z R x‖ₑ ^ 2) ≤
      ENNReal.ofReal (4 * A k) * magnitudeLevelL1Mass volume A f k := by
  have hp (x : ℝ) := map_disjointLevelAtomSum A f k z R hdisj
    (fun b ↦ ‖b‖ₑ ^ 2) (by simp) x
  simp_rw [hp]
  rw [lintegral_tsum (fun i ↦
    ((measurable_levelAtom hf k (z i) (R i)).enorm.pow_const 2).aemeasurable)]
  calc
    _ ≤ ∑' i, ENNReal.ofReal (2 * A k) *
        ENNReal.ofReal (∫ x, ‖levelAtom A f k (z i) (R i) x‖) :=
      ENNReal.tsum_le_tsum (fun i ↦ lintegral_sq_enorm_levelAtom_le hf hAk (hR i))
    _ = ENNReal.ofReal (2 * A k) *
        ∑' i, ENNReal.ofReal (∫ x, ‖levelAtom A f k (z i) (R i) x‖) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (2 * A k) * (2 * magnitudeLevelL1Mass volume A f k) :=
      mul_le_mul' le_rfl (tsum_atomL1Mass_le_two_mul_global_level_mass hf hAk z R hdisj)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * A k)]
      congr 2
      ring

theorem memLp_disjointLevelAtomSum {ι : Type*} [Countable ι]
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    MemLp (disjointLevelAtomSum A f k z R) 2 := by
  have hm := measurable_disjointLevelAtomSum (A := A) hf k z R
  have hmass : magnitudeLevelL1Mass volume A f k < ∞ := by
    apply lt_of_le_of_lt ?_ hfi.hasFiniteIntegral
    simpa only [magnitudeLevelL1Mass, ofReal_norm, Measure.restrict_univ] using
      lintegral_mono_set (μ := volume) (f := fun x ↦ ‖f x‖ₑ)
        (subset_univ (magnitudeLevelSet A f k))
  have hs : (∫⁻ x, ‖disjointLevelAtomSum A f k z R x‖ₑ ^ 2) < ∞ :=
    (disjointLevelAtomSum_sq_lintegral_le hf hAk z R hR hdisj).trans_lt
      (ENNReal.mul_lt_top (by finiteness) hmass)
  rw [MemLp, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hm.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hs.ne

/-- The high-height input estimate invokes the genuine, unrestricted
real-parameter maximal L² theorem, not a supplied oscillatory hypothesis. -/
theorem fixedHeight_disjointLevelAtomSum_eLpNorm_le {ι : Type*} [Countable ι]
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) (height : ℕ) :
    eLpNorm (paperFixedHeightQuadraticMaximal height (disjointLevelAtomSum A f k z R)) 2 ≤
      ENNReal.ofReal (fixedHeightL2DecayConstant * (2 : ℝ) ^ (-(height : ℝ) / 10)) *
        (ENNReal.ofReal (4 * A k) * magnitudeLevelL1Mass volume A f k) ^ (1 / 2 : ℝ) := by
  apply (paperFixedHeightQuadraticMaximal_eLpNorm_decay height
    (memLp_disjointLevelAtomSum hf hfi hAk z R hR hdisj)).trans
  apply mul_le_mul' le_rfl
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (measurable_disjointLevelAtomSum (A := A) hf k z R).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow (disjointLevelAtomSum_sq_lintegral_le hf hAk z R hR hdisj)
    (by norm_num)

end PositiveHighHeightEstimate
end QuadraticCarleson
