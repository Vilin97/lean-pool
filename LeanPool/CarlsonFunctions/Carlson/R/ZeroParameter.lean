/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.ZeroParameter

/-!
# Zero-parameter deletion for the continued R-function

Every finite set of right-half-plane nodes fits in a disk of holomorphy of
the principal power. Carlson's continued Taylor formula therefore deletes a
zero parameter for every complex exponent and every remaining parameter vector.
-/

open Complex Set
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- A finite right-half-plane node vector lies in a disk centered on the positive
real axis whose open disk is contained in the right half-plane. -/
theorem exists_carlsonR_center {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    ∃ A : ℝ, 0 < A ∧ ‖fun i => z i - (A : ℂ)‖ < A := by
  let d := fun i => normSq (z i) / (2 * (z i).re)
  have hd (i : ι) : 0 ≤ d i :=
    div_nonneg (normSq_nonneg _) (mul_nonneg (by norm_num) (hz i).le)
  let A := (∑ i, d i) + 1
  have hA : 0 < A :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ => hd i)) zero_lt_one
  refine ⟨A, hA, (pi_norm_lt_iff hA).mpr (fun i => ?_)⟩
  have hi : d i < A := lt_of_le_of_lt
    (Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)) (by dsimp [A]; linarith)
  have hip : normSq (z i) < A * (2 * (z i).re) :=
    (div_lt_iff₀ (mul_pos (by norm_num) (hz i))).mp hi
  have hs : ‖z i - (A : ℂ)‖ ^ 2 = normSq (z i) + A ^ 2 - 2 * (z i).re * A := by
    rw [Complex.sq_norm, normSq_sub]
    simp [normSq_ofReal, mul_re, pow_two, mul_assoc]
  nlinarith [norm_nonneg (z i - (A : ℂ))]

/-- The principal power is holomorphic on any disk centered at a positive real
number with that number as radius. -/
theorem analyticOnNhd_cpow_carlsonR_center (t : ℂ) (A : ℝ) :
    AnalyticOnNhd ℂ (fun w : ℂ => w ^ t) (Metric.ball (A : ℂ) A) := by
  intro w hw
  have hnorm : ‖(A : ℂ) - w‖ < A := by simpa [dist_eq_norm, norm_sub_rev] using hw
  have hreal : 0 < w.re := by
    have h := re_le_norm ((A : ℂ) - w)
    simp only [sub_re, ofReal_re] at h
    linarith
  have hslit : w ∈ slitPlane := carlsonRightHalfPlane_subset_slitPlane hreal
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_slitPlane.eventually_mem hslit] with v hv
  exact differentiableAt_id.cpow_const hv

/-- Carlson's zero-parameter deletion for the general continued R-function.
The exponent and remaining Dirichlet parameters are arbitrary complex numbers. -/
theorem regCarlsonRContinued_option_zero [Nonempty ι] (t : ℂ)
    {b : Option ι → ℂ} (hb : b none = 0)
    {z : Option ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRContinued t z hz b =
      regCarlsonRContinued t (z ∘ some) (fun i => hz (some i)) (b ∘ some) := by
  obtain ⟨A, hA, hzA⟩ := exists_carlsonR_center hz
  exact IsRegCarlsonContinuation.option_zero (analyticOnNhd_cpow_carlsonR_center t A) hzA
    (isRegCarlsonRContinuation_continued t hz)
    (isRegCarlsonRContinuation_continued t (fun i => hz (some i))) hb

end DirichletTransform
end
