/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalSpace
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Norms
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryVorticityCoordinates
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCalculus
public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySmoothWords
public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianEvolution
public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianLow
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicDerivatives
import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities
import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussianFields
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import LeanPool.NavierStokesAndEuler.Euler.WholeSpaceGaussian

/-!
The whole-space logarithmic gradient estimate.  Every input norm belongs
to the given smooth L² field, and the vorticity is its literal curl.
The proof uses the constructed Gaussian kernel and its true heat equation.
-/

section

/-! The logarithmic middle heat scales for an actual elliptic curl equation. -/

section

/-! The small-time heat remainder from genuine third spatial L² derivatives. -/

@[expose] public section

noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set ContinuousLinearMap
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSobolevBoundedField
  EulerOrdinarySobolev EulerVectorCalculus
open scoped ContDiff ENNReal RealInnerProductSpace Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The heat remainder of one actual spatial derivative is O(ε^(1/4))
times the third spatial L² tensor. No Hölder or heat estimate is assumed. -/
theorem derivative_high_remainder (A : SmoothL2Field V) (j : Fin 3) (x : Space)
    {ε : ℝ} (hε : 0 < ε) :
    ‖fderiv ℝ A.field x (axis j) -
        average ε (A.directionalField (axis j)).field x‖ ≤
      3*ε^((1:ℝ)/4)*‖A.jetLp 3‖ := by
  let D := A.directionalField (axis j)
  let F : ℝ → V := fun t => scaledAverage t D.field x
  let B : ℝ → ℝ := fun t => (3/4:ℝ)*t^(-(3:ℝ)/4)*‖A.jetLp 3‖
  have hc : Continuous F := scaledAverage_continuous D.field D.smooth.continuous
    ‖finiteField D‖ (field_sup_bound D) x
  have hd (t : ℝ) (ht : t ∈ Ioo 0 ε) :
      HasDerivAt F ((1/4:ℝ) • secondAverage t D.field x) t :=
    scaledAverage_field_hasDerivAt ht.1 D x
  have hb (t : ℝ) (ht : t ∈ Ioo 0 ε) : ‖deriv F t‖ ≤ B t := by
    rw [(hd t ht).deriv, norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)]
    have h := mul_le_mul_of_nonneg_left (secondAverage_directional_bound ht.1 A j x)
      (by norm_num : (0:ℝ) ≤ 1/4)
    exact h.trans_eq (by dsimp [B]; ring)
  have hbi : IntervalIntegrable B volume 0 ε :=
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -(3:ℝ)/4)).const_mul
      (3/4:ℝ)).mul_const ‖A.jetLp 3‖
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le hε.le hc.continuousOn
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (Eventually.of_forall hb) hbi
  have he : (∫ t in (0:ℝ)..ε, B t) = 3*ε^((1:ℝ)/4)*‖A.jetLp 3‖ := by
    dsimp [B]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(3:ℝ)/4))]
    rw [show -(3:ℝ)/4+1=(1:ℝ)/4 by norm_num,
      Real.zero_rpow (by norm_num : (1:ℝ)/4 ≠ 0)]
    ring
  rw [he] at h
  change ‖scaledAverage ε D.field x-scaledAverage 0 D.field x‖ ≤ _ at h
  rw [scaledAverage_eq hε, scaledAverage_zero, norm_sub_rev] at h
  exact h

end EulerWholeSpaceGaussian

end
end

end

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

end
end

end

section

/-! The actual whole-space logarithmic derivative estimate for a scalar
elliptic equation whose right-hand side is the derivative of bounded fields. -/

section

/-! Optimization of the actual heat-scale estimate used in the
whole-space logarithmic gradient bound. -/

@[expose] public section

noncomputable section

namespace EulerLogarithmicCutoff

open Real

theorem optimize (X c L W H : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < 1 →
      X ≤ c*(L+W*(-log ε)+ε^(1/4 : ℝ)*H)) :
    X ≤ 4*c*(1+L+W*log (exp 1+H)) := by
  let A := exp 1+H
  have hE : 1 < exp (1 : ℝ) := by
    simpa only [exp_zero] using exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hA1 : 1 < A := by dsimp [A]; linarith
  have hA0 : 0 < A := zero_lt_one.trans hA1
  have hl : 0 < log A := log_pos hA1
  let ε := exp (-4*log A)
  have he0 : 0 < ε := exp_pos _
  have he1 : ε < 1 := by
    have hneg : -4*log A < 0 := by linarith
    simpa only [ε,exp_zero] using exp_lt_exp.mpr hneg
  have heLog : -log ε=4*log A := by simp only [ε,log_exp]; ring
  have hePow : ε^(1/4 : ℝ)=A⁻¹ := by
    dsimp [ε]
    rw [rpow_def_of_pos (exp_pos _),log_exp,
      show (-4*log A)*(1/4 : ℝ) = -log A by ring,exp_neg,exp_log hA0]
  have hHA : H ≤ A := le_add_of_nonneg_left (exp_pos 1).le
  have hsmall : A⁻¹*H ≤ 1 := by
    rw [mul_comm,← div_eq_mul_inv]
    exact (div_le_one hA0).mpr hHA
  have h := hbound ε he0 he1
  rw [heLog,hePow] at h
  have hmid : X ≤ c*(L+4*(W*log A)+1) := by
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hc
    nlinarith only [hsmall]
  have hdiff : 0 ≤ c*(3+3*L) := mul_nonneg hc (by linarith)
  change X ≤ 4*c*(1+L+W*log A)
  nlinarith only [hmid,hdiff]

end EulerLogarithmicCutoff

end
end

end

@[expose] public section

noncomputable section

namespace EulerWholeSpaceGaussian

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerVectorCalculus Laplacian
open scoped ContDiff ENNReal RealInnerProductSpace Topology

/-- Split cost, given by `lowCost+middleCost+3`. -/
def splitCost : ℝ := lowCost+middleCost+3

theorem splitCost_nonneg : 0 ≤ splitCost := by
  unfold splitCost
  linarith [lowCost_nonneg, middleCost_nonneg]

theorem splitCost_pos : 0 < splitCost := by
  unfold splitCost
  linarith [lowCost_nonneg, middleCost_nonneg]

/-- The bound is proved for the genuine derivative of A.  H only bounds
its actual third L² derivative tensor; the elliptic equation is literal. -/
theorem elliptic_derivative_logarithmic (A G J : SmoothL2Field ℝ) (a b j : Fin 3)
    (hΔ : ∀ y, Δ A.field y = partialDerivative G.field a y - partialDerivative J.field b y)
    (W : ℝ) (hG : ∀ y, ‖G.field y‖ ≤ W) (hJ : ∀ y, ‖J.field y‖ ≤ W)
    (H : ℝ) (hH : ‖A.jetLp 3‖ ≤ H) (x : Space) :
    ‖partialDerivative A.field j x‖ ≤
      4*splitCost*(1+‖A.toLp‖+W*Real.log (Real.exp 1+H)) := by
  have hH0 : 0 ≤ H := (norm_nonneg (A.jetLp 3)).trans hH
  have hW : 0 ≤ W := (norm_nonneg (G.field x)).trans (hG x)
  apply EulerLogarithmicCutoff.optimize _ splitCost ‖A.toLp‖ W H
    splitCost_nonneg (norm_nonneg _) hH0
  intro ε hε hε1
  have he : 0 ≤ -Real.log ε := neg_nonneg.mpr (Real.log_nonpos hε.le hε1.le)
  have hr : 0 ≤ ε^((1:ℝ)/4) := Real.rpow_nonneg hε.le _
  have hl : lowCost ≤ splitCost := by unfold splitCost; linarith [middleCost_nonneg]
  have hm : middleCost ≤ splitCost := by unfold splitCost; linarith [lowCost_nonneg]
  have hh : (3:ℝ) ≤ splitCost := by unfold splitCost; linarith [lowCost_nonneg, middleCost_nonneg]
  calc
    _ ≤ lowCost*‖A.toLp‖+middleCost*W*(-Real.log ε)+3*ε^((1:ℝ)/4)*‖A.jetLp 3‖ :=
      elliptic_derivative_split A G J a b j hΔ W hG hJ x hε hε1.le
    _ = lowCost*‖A.toLp‖+middleCost*(W*(-Real.log ε))+3*(ε^((1:ℝ)/4)*‖A.jetLp 3‖) := by ring
    _ ≤ splitCost*‖A.toLp‖+splitCost*(W*(-Real.log ε))+splitCost*(ε^((1:ℝ)/4)*H) := by
      apply add_le_add
      · exact add_le_add (mul_le_mul_of_nonneg_right hl (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hm (mul_nonneg hW he))
      · exact mul_le_mul hh (mul_le_mul_of_nonneg_left hH hr)
          (mul_nonneg hr (norm_nonneg _)) splitCost_nonneg
    _ = _ := by ring

end EulerWholeSpaceGaussian

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace EulerSmoothLimit Filter Set Finset
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerVectorCalculus EulerMeanCutoffCurl EulerMeanClassical EulerWholeSpaceGaussian
open scoped ContDiff ENNReal RealInnerProductSpace Topology

/-- Logarithmic gradient constant, given by `36*splitCost`. -/
def logarithmicGradientConstant : ℝ := 36*splitCost

theorem logarithmicGradientConstant_pos : 0 < logarithmicGradientConstant :=
  mul_pos (by norm_num) splitCost_pos

theorem logarithmicGradientConstant_nonneg : 0 ≤ logarithmicGradientConstant :=
  logarithmicGradientConstant_pos.le

/-- A genuine whole-space BKM logarithmic estimate from the actual
velocity, its actual H³ tensors, and its actual vorticity. -/
theorem logarithmic_gradient_bound (A : SmoothL2Field Space)
    (hdiv : ∀ y, divergence A.field y = 0) (W : ℝ)
    (hW : ∀ y, ‖vectorCurl A.field y‖ ≤ W) (x : Space) :
    ‖fderiv ℝ A.field x‖ ≤ logarithmicGradientConstant *
      (1+‖A.toLp‖+W*Real.log (Real.exp 1+tensorNorm 3 A)) := by
  have hW0 : 0 ≤ W := (norm_nonneg (vectorCurl A.field 0)).trans (hW 0)
  have hH0 := tensorNorm_nonneg 3 A
  have harg : 1 ≤ Real.exp 1+tensorNorm 3 A :=
    (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans (le_add_of_nonneg_right hH0)
  have hlog : 0 ≤ Real.log (Real.exp 1+tensorNorm 3 A) := Real.log_nonneg harg
  let K : ℝ := 4*splitCost*(1+‖A.toLp‖+W*Real.log (Real.exp 1+tensorNorm 3 A))
  have hK : 0 ≤ K := by dsimp [K]; positivity [splitCost_nonneg]
  have hcomponent (i : Fin 3) (y : Space) :
      ‖(componentField (vorticityField A) i).field y‖ ≤ W := by
    rw [componentField_apply]
    exact (PiLp.norm_apply_le ((vorticityField A).field y) i).trans
      (by simpa only [vorticityField_apply] using hW y)
  have hjet : ‖A.jetLp 3‖ ≤ tensorNorm 3 A :=
    single_le_sum (fun _ _ => norm_nonneg _) (by decide : 3 ∈ range (3+1))
  have hentries (i j : Fin 3) : ‖(fderiv ℝ A.field x (axis i)) j‖ ≤ K := by
    have h := elliptic_derivative_logarithmic (componentField A j)
      (componentField (vorticityField A) (j+1)) (componentField (vorticityField A) (j+2))
      (j+2) (j+1) i (componentField_laplacian A hdiv j) W
      (hcomponent (j+1)) (hcomponent (j+2)) (tensorNorm 3 A)
      ((componentField_jetLp_norm A j 3).trans hjet) x
    rw [componentField_partial] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) splitCost_nonneg)
    linarith [componentField_toLp_norm A j]
  have h := operator_norm_le_of_entries (fderiv ℝ A.field x) K hK hentries
  exact h.trans_eq (by unfold logarithmicGradientConstant; dsimp [K]; ring)

/-- This form discharges the entire logarithmic-estimate hypothesis of
the ordinary Euler continuation theorem. -/
theorem logarithmic_gradient_bound_solenoidal (A : SmoothL2Field Space) (W : ℝ)
    (hA : A.toLp ∈ solenoidalSpace) (hW : ∀ y, ‖vectorCurl A.field y‖ ≤ W) (x : Space) :
    ‖fderiv ℝ A.field x‖ ≤ logarithmicGradientConstant *
      (1+‖A.toLp‖+W*Real.log (Real.exp 1+tensorNorm 3 A)) :=
  logarithmic_gradient_bound A
    (solenoidal_representative_divergence A.toLp hA A.field A.smooth A.toLp_ae) W hW x

end EulerOrdinarySobolev
