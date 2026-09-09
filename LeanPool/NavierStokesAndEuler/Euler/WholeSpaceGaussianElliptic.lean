/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCalculus
public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySmoothWords
public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianEvolution
public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianLow
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicDerivatives
import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities
import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianFields
import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianHigh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-! The logarithmic middle heat scales for an actual elliptic curl equation. -/

@[expose] public section


noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set ContinuousLinearMap
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSobolevBoundedField
  EulerOrdinarySobolev EulerVectorCalculus EulerMeanHarmonic EulerMeanVectorIdentities Laplacian
open scoped ContDiff ENNReal RealInnerProductSpace Topology

/-- Middle cost, given by `5*(2:ℝ)^((3:ℝ)/2)`. -/
def middleCost : ℝ := 5*(2:ℝ)^((3:ℝ)/2)

theorem middleCost_nonneg : 0 ≤ middleCost := by unfold middleCost; positivity

theorem secondAverage_elliptic (A G H : SmoothL2Field ℝ) (a b j : Fin 3)
    (hΔ : ∀ y, Δ A.field y = partialDerivative G.field a y - partialDerivative H.field b y)
    {t : ℝ} (ht : 0 < t) (x : Space) :
    secondAverage t (A.directionalField (axis j)).field x =
      average t ((G.directionalField (axis a)).directionalField (axis j)).field x -
        average t ((H.directionalField (axis b)).directionalField (axis j)).field x := by
  rw [secondAverage_eq_laplacian ht]
  have he : Δ (A.directionalField (axis j)).field =
      fun y => ((G.directionalField (axis a)).directionalField (axis j)).field y -
        ((H.directionalField (axis b)).directionalField (axis j)).field y := by
    funext y
    change Δ (partialDerivative A.field j) y = _
    rw [laplacian_partialDerivative A.field A.smooth j y, funext hΔ,
      partialDerivative_sub _ _ (contDiff_partialDerivative G.field G.smooth a)
        (contDiff_partialDerivative H.field H.smooth b)]
    rfl
  rw [he, average_sub ht _ _ ((G.directionalField (axis a)).directionalField (axis j)).memLp
    ((H.directionalField (axis b)).directionalField (axis j)).memLp]

theorem secondAverage_elliptic_bound (A G H : SmoothL2Field ℝ) (a b j : Fin 3)
    (hΔ : ∀ y, Δ A.field y = partialDerivative G.field a y - partialDerivative H.field b y)
    (W : ℝ) (hG : ∀ y, ‖G.field y‖ ≤ W) (hH : ∀ y, ‖H.field y‖ ≤ W)
    {t : ℝ} (ht : 0 < t) (x : Space) :
    ‖(1/4:ℝ) • secondAverage t (A.directionalField (axis j)).field x‖ ≤
      middleCost*t⁻¹*W := by
  have hg := average_field_second_bound ht G W hG (axis j) (axis a) x
  have hh := average_field_second_bound ht H W hH (axis j) (axis b) x
  simp only [axis_norm, mul_one] at hg hh
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4),
    secondAverage_elliptic A G H a b j hΔ ht x]
  apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num : (0:ℝ) ≤ 1/4)).trans
  have h := mul_le_mul_of_nonneg_left (add_le_add hg hh) (by norm_num : (0:ℝ) ≤ 1/4)
  exact h.trans_eq (by unfold middleCost; ring)

/-- Integrating the genuine 1/t estimate gives the logarithmic middle term. -/
theorem derivative_elliptic_middle (A G H : SmoothL2Field ℝ) (a b j : Fin 3)
    (hΔ : ∀ y, Δ A.field y = partialDerivative G.field a y - partialDerivative H.field b y)
    (W : ℝ) (hG : ∀ y, ‖G.field y‖ ≤ W) (hH : ∀ y, ‖H.field y‖ ≤ W)
    (x : Space) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖average ε (A.directionalField (axis j)).field x -
        average 1 (A.directionalField (axis j)).field x‖ ≤
      middleCost*W*(-Real.log ε) := by
  let D := A.directionalField (axis j)
  let F : ℝ → ℝ := fun t => scaledAverage t D.field x
  let B : ℝ → ℝ := fun t => middleCost*t⁻¹*W
  have hc : Continuous F := scaledAverage_continuous D.field D.smooth.continuous
    ‖finiteField D‖ (field_sup_bound D) x
  have hd (t : ℝ) (ht : t ∈ Ioo ε 1) :
      HasDerivAt F ((1/4:ℝ) • secondAverage t D.field x) t :=
    scaledAverage_field_hasDerivAt (hε.trans ht.1) D x
  have hb (t : ℝ) (ht : t ∈ Ioo ε 1) : ‖deriv F t‖ ≤ B t := by
    rw [(hd t ht).deriv]
    exact secondAverage_elliptic_bound A G H a b j hΔ W hG hH (hε.trans ht.1) x
  have hbi : IntervalIntegrable B volume ε 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hε1
    exact (continuousOn_const.mul (continuousOn_id.inv₀
      (fun t ht => (hε.trans_le ht.1).ne'))).mul continuousOn_const
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le hε1 hc.continuousOn
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (Eventually.of_forall hb) hbi
  have he : (∫ t in ε..(1:ℝ), B t) = middleCost*W*(-Real.log ε) := by
    dsimp [B]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hε (by norm_num)]
    simp only [one_div, Real.log_inv]
    ring
  rw [he] at h
  change ‖scaledAverage 1 D.field x-scaledAverage ε D.field x‖ ≤ _ at h
  rw [scaledAverage_eq (by norm_num : (0:ℝ)<1), scaledAverage_eq hε, norm_sub_rev] at h
  exact h

/-- The three heat scales, with every term attached to the original field. -/
theorem elliptic_derivative_split (A G H : SmoothL2Field ℝ) (a b j : Fin 3)
    (hΔ : ∀ y, Δ A.field y = partialDerivative G.field a y - partialDerivative H.field b y)
    (W : ℝ) (hG : ∀ y, ‖G.field y‖ ≤ W) (hH : ∀ y, ‖H.field y‖ ≤ W)
    (x : Space) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖partialDerivative A.field j x‖ ≤
      lowCost*‖A.toLp‖ + middleCost*W*(-Real.log ε) + 3*ε^((1:ℝ)/4)*‖A.jetLp 3‖ := by
  have hh := derivative_high_remainder A j x hε
  have hm := derivative_elliptic_middle A G H a b j hΔ W hG hH x hε hε1
  have hl := average_field_first_bound A (axis j) x
  simp only [axis_norm, mul_one] at hl
  let v := partialDerivative A.field j x
  let m := average ε (A.directionalField (axis j)).field x
  let l := average 1 (A.directionalField (axis j)).field x
  have he : v = (v-m)+(m-l)+l := by ring
  calc
    ‖v‖ = ‖(v-m)+(m-l)+l‖ := congrArg norm he
    _ ≤ (‖v-m‖+‖m-l‖)+‖l‖ := (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      change ‖v-m‖ ≤ _ at hh
      change ‖m-l‖ ≤ _ at hm
      change ‖l‖ ≤ _ at hl
      linarith

end EulerWholeSpaceGaussian
