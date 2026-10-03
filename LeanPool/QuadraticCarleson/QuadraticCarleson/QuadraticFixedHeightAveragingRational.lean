/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingContinuity

/-!
# Rational reduction without crossing scale-selection jumps

We parametrize each modulation band by the positive square root of the
absolute modulation. Rational roots strictly inside that band yield rational
nonzero modulations of either sign. Fixed-scale continuity then extends their
bound to the lower endpoint of the half-open band as well.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace QuadraticCarleson

/-- A square modulation with sign selected by a Boolean flag. -/
def signedSquareModulation (negative : Bool) (r : ℝ) : ℝ :=
  if negative then -(r ^ 2) else r ^ 2

/-- A rational square modulation with sign selected by a Boolean flag. -/
def signedRationalSquareModulation (negative : Bool) (q : ℚ) : ℚ :=
  if negative then -(q ^ 2) else q ^ 2

theorem coe_signedRationalSquareModulation (negative : Bool) (q : ℚ) :
    (signedRationalSquareModulation negative q : ℝ) =
      signedSquareModulation negative (q : ℝ) := by
  cases negative <;> simp [signedSquareModulation, signedRationalSquareModulation]

theorem abs_signedSquareModulation (negative : Bool) (r : ℝ) :
    |signedSquareModulation negative r| = r ^ 2 := by
  cases negative <;> simp [signedSquareModulation, abs_of_nonneg (sq_nonneg r)]

theorem signedRationalSquareModulation_ne_zero (negative : Bool)
    {q : ℚ} (hq : q ≠ 0) : signedRationalSquareModulation negative q ≠ 0 := by
  cases negative <;> simpa [signedRationalSquareModulation] using pow_ne_zero 2 hq

theorem continuous_signedSquareModulation (negative : Bool) :
    Continuous (signedSquareModulation negative) := by
  cases negative
  · change Continuous (fun r : ℝ ↦ r ^ 2)
    fun_prop
  · change Continuous (fun r : ℝ ↦ -(r ^ 2))
    fun_prop

theorem signedSquareModulation_sqrt_abs (lam : ℝ) :
    signedSquareModulation (decide (lam < 0)) (Real.sqrt |lam|) = lam := by
  unfold signedSquareModulation
  rw [Real.sq_sqrt (abs_nonneg lam)]
  by_cases hl : lam < 0
  · simp [hl, abs_of_neg hl]
  · simp [hl, abs_of_nonneg (le_of_not_gt hl)]

theorem oscillatoryScaleSpec_signedSquareModulation (negative : Bool)
    (height : ℕ) (j : ℤ) {r : ℝ} (hr : 0 ≤ r)
    (hscale : (2 : ℝ) ^ height ≤ (2 : ℝ) ^ j * r ∧
      (2 : ℝ) ^ j * r < (2 : ℝ) ^ (height + 1)) :
    OscillatoryScaleSpec (signedSquareModulation negative r) height j := by
  simpa only [OscillatoryScaleSpec, abs_signedSquareModulation, Real.sqrt_sq hr] using hscale

/-- The fixed-height maximal convolution over the enumerated nonzero rational modulations. -/
noncomputable def rationalFixedHeightQuadraticMaximal
    (height : ℕ) (f : ℝ → ℂ) : ℝ → ℝ≥0∞ :=
  countableConvolutionMaximal (fun n ↦ fixedHeightQuadraticKernel
    (rationalModulationSequence n) height (rationalModulationSequence_ne_zero n)) f

theorem fixedHeightQuadratic_integral_rational_le
    (height : ℕ) (q : ℚ) (hq : q ≠ 0) (f : ℝ → ℂ) (x : ℝ) :
    ‖∫ t, fixedHeightQuadraticKernel (q : ℝ) height
      (by exact_mod_cast hq) (x - t) * f t‖ₑ ≤
      rationalFixedHeightQuadraticMaximal height f x := by
  obtain ⟨n, hn⟩ := exists_rationalModulationSequence q hq
  have h := le_iSup (fun n ↦ ‖∫ t, fixedHeightQuadraticKernel
    (rationalModulationSequence n) height (rationalModulationSequence_ne_zero n)
      (x - t) * f t‖ₑ) n
  simpa only [rationalFixedHeightQuadraticMaximal, countableConvolutionMaximal, hn] using h

/-- On either signed modulation band, rational roots strictly inside the band
control every point of the half-open band, with its lower endpoint included. -/
theorem fixedScale_signedSquare_integral_enorm_le_rational
    (height : ℕ) (j : ℤ) (negative : Bool) {r : ℝ}
    (hscale : (2 : ℝ) ^ height ≤ (2 : ℝ) ^ j * r ∧
      (2 : ℝ) ^ j * r < (2 : ℝ) ^ (height + 1))
    {f : ℝ → ℂ} (hf : LocallyIntegrable f) (x : ℝ) :
    ‖∫ t, (dyadicPsi j (x - t) : ℂ) *
      phase (signedSquareModulation negative r * (x - t) ^ 2) * f t‖ₑ ≤
      rationalFixedHeightQuadraticMaximal height f x := by
  let a : ℝ := (2 : ℝ) ^ height / (2 : ℝ) ^ j
  let b : ℝ := (2 : ℝ) ^ (height + 1) / (2 : ℝ) ^ j
  have hj : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have ha : 0 < a := div_pos (by positivity) hj
  have hmem : r ∈ Ico a b := by
    constructor
    · exact (div_le_iff₀ hj).mpr (by simpa only [mul_comm] using hscale.1)
    · exact (lt_div_iff₀ hj).mpr (by simpa only [mul_comm] using hscale.2)
  have hab : a < b := hmem.1.trans_lt hmem.2
  let F : ℝ → ℝ≥0∞ := fun s ↦ ‖∫ t, (dyadicPsi j (x - t) : ℂ) *
    phase (signedSquareModulation negative s * (x - t) ^ 2) * f t‖ₑ
  have hF : Continuous F :=
    ((continuous_dyadicQuadraticConvolution_parameter j hf x).comp
      (continuous_signedSquareModulation negative)).enorm
  have hclosed : IsClosed {s | F s ≤ rationalFixedHeightQuadraticMaximal height f x} :=
    isClosed_le hF continuous_const
  have hsub : Ioo a b ∩ range (fun q : ℚ ↦ (q : ℝ)) ⊆
      {s | F s ≤ rationalFixedHeightQuadraticMaximal height f x} := by
    rintro s ⟨hs, q, rfl⟩
    have hqpos : (0 : ℝ) < q := ha.trans hs.1
    have hq : q ≠ 0 := by exact_mod_cast hqpos.ne'
    have hqR := signedRationalSquareModulation_ne_zero negative hq
    have hspec : OscillatoryScaleSpec
        (signedRationalSquareModulation negative q : ℝ) height j := by
      rw [coe_signedRationalSquareModulation]
      apply oscillatoryScaleSpec_signedSquareModulation negative height j hqpos.le
      constructor
      · simpa only [mul_comm] using (div_le_iff₀ hj).mp hs.1.le
      · simpa only [mul_comm] using (lt_div_iff₀ hj).mp hs.2
    have hidx := (oscillatoryScaleIndex_unique
      (signedRationalSquareModulation negative q : ℝ) height
      (by exact_mod_cast hqR) hspec).symm
    have hbound := fixedHeightQuadratic_integral_rational_le
      height (signedRationalSquareModulation negative q) hqR f x
    simp only [fixedHeightQuadraticKernel, hidx] at hbound
    simpa only [F, Set.mem_ofPred_eq,
      coe_signedRationalSquareModulation] using hbound
  exact closure_minimal hsub hclosed (Ico_subset_closure_rational_Ioo hab hmem)

/-- Every real nonzero modulation is controlled by the explicitly enumerated
rational modulations, without assuming continuity of the scale selector. -/
theorem fixedHeightQuadratic_integral_enorm_le_rational
    (height : ℕ) (lam : ℝ) (hlam : lam ≠ 0)
    {f : ℝ → ℂ} (hf : LocallyIntegrable f) (x : ℝ) :
    ‖∫ t, fixedHeightQuadraticKernel lam height hlam (x - t) * f t‖ₑ ≤
      rationalFixedHeightQuadraticMaximal height f x := by
  have hs := oscillatoryScaleIndex_spec lam height hlam
  have h := fixedScale_signedSquare_integral_enorm_le_rational
    height (oscillatoryScaleIndex lam height hlam) (decide (lam < 0))
    hs hf x
  simpa only [signedSquareModulation_sqrt_abs, fixedHeightQuadraticKernel] using h

end QuadraticCarleson
