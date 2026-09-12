/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanVariationalInverse
public import LeanPool.NavierStokesAndEuler.Euler.MeanScaledCutoff
public import LeanPool.NavierStokesAndEuler.Euler.MeanLocalL2Energy
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.MeanWeakHarmonicInterior
import LeanPool.NavierStokesAndEuler.Euler.MeanWeakHarmonicScaling

/-!
The mean inverse with the source's actual nonlocal boundary operator.
The boundary lower bound is proved from the spatial hypotheses (5), not an input.
-/

section

/-! The concrete boundary lower bound used in the mean time-variational solve. -/

section

/-! The source localization estimate for the constructed nonlocal boundary operator. -/

@[expose] public section

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanBoundary
  EulerMeanCurlTensor

/-- Boundary localization C1, given by `36 * (2 + 4 * weakHarmonicSmallBallConstant)`. -/
def boundaryLocalizationC1 : ℝ := 36 * (2 + 4 * weakHarmonicSmallBallConstant)
/-- Boundary localization C2, given by `4 * weakHarmonicSmallBallConstant`. -/
def boundaryLocalizationC2 : ℝ := 4 * weakHarmonicSmallBallConstant

theorem boundaryLocalizationC1_nonneg : 0 ≤ boundaryLocalizationC1 := by
  unfold boundaryLocalizationC1
  have hc := weakHarmonicSmallBallConstant_nonneg
  positivity

theorem boundaryLocalizationC2_nonneg : 0 ≤ boundaryLocalizationC2 := by
  unfold boundaryLocalizationC2
  exact mul_nonneg (by norm_num) weakHarmonicSmallBallConstant_nonneg

theorem norm_sub_sq_le_twice_L2 (z w : L2) :
    ‖z-w‖^2 ≤ 2*‖z‖^2 + 2*‖w‖^2 := by
  have h := norm_sub_le z w
  have hz := norm_nonneg z
  have hw := norm_nonneg w
  have hzw := norm_nonneg (z-w)
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

/-- The literal local mass estimate (8), with fixed dimensional constants. -/
theorem boundary_localization (χ : Cutoff) (R : ℝ) (hR : 0 < R) (z : L2)
    (hz : z ∈ solenoidalSpace)
    (hχ : ∀ x ∈ Metric.ball (0 : Space) R, χ.field x = 1)
    (r : ℝ) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4) :
    localL2Energy (Metric.ball (0 : Space) (R*r)) z ≤
      boundaryLocalizationC1 * ‖weakPotential χ z‖^2 +
      boundaryLocalizationC2 * r^3 * ‖z‖^2 := by
  let w := harmonicPart χ z
  have hh : WeakHarmonicOn (Metric.ball (0 : Space) R) (z-w) :=
    weakHarmonicOn_sub_harmonicPart χ _ z hz hχ
  have hloc := weakHarmonic_scaled_smallBall_energy (z-w) R hR hh r hr hrquarter
  have hw : ‖w‖^2 ≤ 36 * ‖weakPotential χ z‖^2 := by
    have H := pow_le_pow_left₀ (norm_nonneg w) (harmonicPart_norm_le χ z) 2
    simpa only [mul_pow, show (6:ℝ)^2 = 36 by norm_num] using H
  have hc := weakHarmonicSmallBallConstant_nonneg
  have hr3 : 0 ≤ r^3 := pow_nonneg hr _
  have hr31 : r^3 ≤ 1 := by
    have H := pow_le_pow_left₀ hr (show r ≤ (1:ℝ) by linarith) 3
    simpa only [one_pow] using H
  have hsplit := norm_sub_sq_le_twice_L2 z w
  calc
    _ ≤ 2 * localL2Energy (Metric.ball (0 : Space) (R*r)) (z-w) + 2 * ‖w‖^2 :=
      localL2Energy_le_of_decomposition _ z w
    _ ≤ 2 * (weakHarmonicSmallBallConstant * r^3 * ‖z-w‖^2) + 2 * ‖w‖^2 := by
      linarith
    _ ≤ 2 * (weakHarmonicSmallBallConstant * r^3 * (2*‖z‖^2+2*‖w‖^2)) +
        2 * ‖w‖^2 := by
      have H := mul_le_mul_of_nonneg_left hsplit (mul_nonneg hc hr3)
      linarith only [H]
    _ = 4 * weakHarmonicSmallBallConstant * r^3 * ‖z‖^2 +
        (2 + 4 * weakHarmonicSmallBallConstant * r^3) * ‖w‖^2 := by ring
    _ ≤ 4 * weakHarmonicSmallBallConstant * r^3 * ‖z‖^2 +
        (2 + 4 * weakHarmonicSmallBallConstant) * ‖w‖^2 := by
      have hfactor : 2 + 4 * weakHarmonicSmallBallConstant * r^3 ≤
          2 + 4 * weakHarmonicSmallBallConstant := by
        have H := mul_le_mul_of_nonneg_left hr31
          (show 0 ≤ 4 * weakHarmonicSmallBallConstant by positivity)
        linarith only [H]
      have H := mul_le_mul_of_nonneg_right hfactor (sq_nonneg ‖w‖)
      linarith only [H]
    _ ≤ 4 * weakHarmonicSmallBallConstant * r^3 * ‖z‖^2 +
        (2 + 4 * weakHarmonicSmallBallConstant) * (36 * ‖weakPotential χ z‖^2) := by
      have H := mul_le_mul_of_nonneg_left hw
        (show 0 ≤ 2 + 4 * weakHarmonicSmallBallConstant by positivity)
      linarith only [H]
    _ = _ := by unfold boundaryLocalizationC1 boundaryLocalizationC2; ring

/-- The same estimate directly in terms of the actual boundary quadratic form. -/
theorem boundary_localization_form (χ : Cutoff) (R : ℝ) (hR : 0 < R) (z : L2)
    (hz : z ∈ solenoidalSpace)
    (hχ : ∀ x ∈ Metric.ball (0 : Space) R, χ.field x = 1)
    (r : ℝ) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4) :
    localL2Energy (Metric.ball (0 : Space) (R*r)) z ≤
      boundaryLocalizationC1 * ⟪boundaryOperator χ z, z⟫_ℝ +
      boundaryLocalizationC2 * r^3 * ‖z‖^2 := by
  rw [boundaryOperator_energy]
  exact boundary_localization χ R hR z hz hχ r hr hrquarter

end EulerMeanHarmonic

end
end

end

section

/-! Integrating the source's different lower bounds inside and outside the core. -/

@[expose] public section

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerLiftedPressure
open scoped NNReal

theorem localized_coefficient_lower (M : Space → Space →L[ℝ] Space)
    (hM : AEStronglyMeasurable M volume) (C : ℝ≥0) (hC : ∀ x, ‖M x‖ ≤ C)
    (s : Set Space) (hs : MeasurableSet s) (Be Bc : ℝ) (hBe : 0 ≤ Be)
    (hext : ∀ x, x ∉ s → ∀ v : Space, -Be * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (hcore : ∀ x, x ∈ s → ∀ v : Space, -Bc * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (z : L2) :
    -Be * ‖z‖^2 - Bc * localL2Energy s z ≤
      ⟪coefficientOperator M hM C hC z, z⟫_ℝ := by
  have hi := integrable_norm_sq_L2 z
  have his := hi.indicator hs
  have hieq : (∫ x, -Be * ‖z x‖^2 - Bc * s.indicator (fun y => ‖z y‖^2) x) =
      -Be * ‖z‖^2 - Bc * localL2Energy s z := by
    rw [integral_sub (hi.const_mul (-Be)) (his.const_mul Bc), integral_const_mul,
      integral_const_mul, integral_indicator hs, integral_norm_sq_L2]
    rfl
  rw [← hieq, MeasureTheory.L2.inner_def]
  apply integral_mono_ae ((hi.const_mul (-Be)).sub (his.const_mul Bc))
    (MeasureTheory.L2.integrable_inner (coefficientOperator M hM C hC z) z)
  filter_upwards [coefficientOperator_ae M hM C hC z] with x hx
  change -Be * ‖z x‖^2 - Bc * s.indicator (fun y => ‖z y‖^2) x ≤
    ⟪(coefficientOperator M hM C hC z) x, z x⟫_ℝ
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs]
    have H := hcore x hxs (z x)
    linarith only [H, mul_nonneg hBe (sq_nonneg ‖z x‖)]
  · rw [Set.indicator_of_notMem hxs, mul_zero, sub_zero]
    exact hext x hxs (z x)

end EulerMeanHarmonic

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanBoundary
  EulerLiftedPressure
open scoped NNReal

/-- The actual localized boundary operator compensates for the core's negative gradient. -/
theorem mean_boundary_lower_bound (χ : Cutoff) (R : ℝ) (hR : 0 < R)
    (hχ : ∀ x ∈ Metric.ball (0 : Space) R, χ.field x = 1)
    (M : Space → Space →L[ℝ] Space) (hM : AEStronglyMeasurable M volume)
    (C : ℝ≥0) (hC : ∀ x, ‖M x‖ ≤ C)
    (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
    (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4)
    (hext : ∀ x, x ∉ Metric.ball (0 : Space) (R * r) →
      ∀ v : Space, -Be * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (hcore : ∀ x, x ∈ Metric.ball (0 : Space) (R*r) →
      ∀ v : Space, -Bc * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (z : L2) (hz : z ∈ solenoidalSpace) :
    -(Be + boundaryLocalizationC2 * Bc * r^3) * ‖z‖^2 ≤
      ⟪coefficientOperator M hM C hC z, z⟫_ℝ + L * ⟪boundaryOperator χ z, z⟫_ℝ := by
  have hcoeff := localized_coefficient_lower M hM C hC
    (Metric.ball (0 : Space) (R*r)) Metric.isOpen_ball.measurableSet Be Bc hBe hext hcore z
  have hloc := mul_le_mul_of_nonneg_left
    (boundary_localization_form χ R hR z hz hχ r hr hrquarter) hBc
  have hcomp := mul_le_mul_of_nonneg_right hL (boundaryOperator_positive χ z)
  linarith only [hcoeff, hloc, hcomp]

/-- The exact cutoff and physical-label core from source (7)–(8). -/
theorem scaled_mean_boundary_lower_bound (ℓ : ℝ) (hℓ : 0 < ℓ)
    (M : Space → Space →L[ℝ] Space) (hM : AEStronglyMeasurable M volume)
    (C : ℝ≥0) (hC : ∀ x, ‖M x‖ ≤ C)
    (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
    (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4)
    (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
    (z : L2) (hz : z ∈ solenoidalSpace) :
    -(Be + boundaryLocalizationC2 * Bc * r^3) * ‖z‖^2 ≤
      ⟪coefficientOperator M hM C hC z, z⟫_ℝ +
        L * ⟪boundaryOperator (scaledCutoff ℓ hℓ) z, z⟫_ℝ := by
  apply mean_boundary_lower_bound (scaledCutoff ℓ hℓ) ℓ⁻¹ (inv_pos.mpr hℓ)
    (scaledCutoff_one_on_ball ℓ hℓ) M hM C hC Be Bc L r hBe hBc hL hr hrquarter
    ?_ ?_ z hz
  · intro x hx
    apply hext x
    rw [← physical_ball_eq ℓ r hℓ] at hx
    exact le_of_not_gt hx
  · intro x hx
    apply hcore x
    rw [← physical_ball_eq ℓ r hℓ] at hx
    exact hx

end EulerMeanHarmonic

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanSourceInverse

open MeasureTheory Set InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanHarmonic EulerMeanBoundary EulerLiftedPressure EulerTimeLp
  EulerMeanVariationalInverse EulerTransverseVariationalInverse
open scoped NNReal

/-- Effective negative bound, given by `Be + boundaryLocalizationC2 * Bc * r^3`. -/
def effectiveNegativeBound (Be Bc r : ℝ) : ℝ :=
  Be + boundaryLocalizationC2 * Bc * r^3

theorem effectiveNegativeBound_nonneg (Be Bc r : ℝ)
    (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc) (hr : 0 ≤ r) :
    0 ≤ effectiveNegativeBound Be Bc r := by
  unfold effectiveNegativeBound
  have hc := boundaryLocalizationC2_nonneg
  positivity

theorem source_smallness (T K Be Bc r : ℝ)
    (hsmall : K * (T ^ 2 / 2) + Be * T + boundaryLocalizationC2 * Bc * r ^ 3 * T ≤ 1 / 2) :
    K*(T^2/2) + effectiveNegativeBound Be Bc r * T ≤ 1/2 := by
  calc
    _ = K*(T^2/2) + Be*T + boundaryLocalizationC2*Bc*r^3*T := by
      unfold effectiveNegativeBound
      ring
    _ ≤ _ := hsmall

variable (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ)
  (M : Space → Space →L[ℝ] Space) (hM : AEStronglyMeasurable M volume)
  (C : ℝ≥0) (hC : ∀ x, ‖M x‖ ≤ C)
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖ ^ 2 ≤ ⟪M x v, v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖ ^ 2 ≤ ⟪M x v, v⟫_ℝ)
  (FInv H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t z, ⟪H t z, z⟫_ℝ ≤ K * ‖z‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) + Be * T + boundaryLocalizationC2 * Bc * r ^ 3 * T ≤ 1 / 2)

/-- This is the actual Lax–Milgram mean inverse, with spatial coercivity discharged. -/
def sourceMeanSolver : TimeLp T L2 →L[ℝ] meanDerivatives T hT FInv :=
  meanSolver T hT FInv H (coefficientOperator M hM C hC)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L K (effectiveNegativeBound Be Bc r)
    hK (effectiveNegativeBound_nonneg Be Bc r hBe hBc hr) hF0 hH
    (scaled_mean_boundary_lower_bound ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter hext hcore)
    (source_smallness T K Be Bc r hsmall)

theorem sourceMeanSolver_norm (f : TimeLp T L2) :
    ‖sourceMeanSolver T hT ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter
      hext hcore FInv H K hK hF0 hH hsmall f‖ ≤ 2*T*‖f‖ :=
  meanSolver_norm T hT FInv H (coefficientOperator M hM C hC)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L K (effectiveNegativeBound Be Bc r)
    hK (effectiveNegativeBound_nonneg Be Bc r hBe hBc hr) hF0 hH
    (scaled_mean_boundary_lower_bound ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter hext hcore)
    (source_smallness T K Be Bc r hsmall) f

/-- The literal mean weak equation, retaining both original initial boundary terms. -/
theorem sourceMeanSolver_weak (f : TimeLp T L2) (v : meanDerivatives T hT FInv) :
    let u := sourceMeanSolver T hT ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter
      hext hcore FInv H K hK hF0 hH hsmall f
    ⟪(u : TimeLp T L2), (v : TimeLp T L2)⟫_ℝ -
      ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv v⟫_ℝ +
      ⟪coefficientOperator M hM C hC (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ +
      L * ⟪boundaryOperator (scaledCutoff ℓ hℓ) (meanTrace T hT FInv u),
        meanTrace T hT FInv v⟫_ℝ = -⟪f, meanPrimitive T hT FInv v⟫_ℝ :=
  meanSolver_weak T hT FInv H (coefficientOperator M hM C hC)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L K (effectiveNegativeBound Be Bc r)
    hK (effectiveNegativeBound_nonneg Be Bc r hBe hBc hr) hF0 hH
    (scaled_mean_boundary_lower_bound ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter hext hcore)
    (source_smallness T K Be Bc r hsmall) f v

include hK hF0 hH hsmall hBe hBc hL hr hrquarter hext hcore in
/-- Existence and uniqueness from the actual source spatial and time assumptions. -/
theorem existsUnique_source_mean_weak_solution (f : TimeLp T L2) :
    ∃! u : meanDerivatives T hT FInv, ∀ v : meanDerivatives T hT FInv,
      ⟪(u : TimeLp T L2), (v : TimeLp T L2)⟫_ℝ -
        ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv v⟫_ℝ +
        ⟪coefficientOperator M hM C hC (meanTrace T hT FInv u), meanTrace T hT FInv v⟫_ℝ +
        L * ⟪boundaryOperator (scaledCutoff ℓ hℓ) (meanTrace T hT FInv u),
          meanTrace T hT FInv v⟫_ℝ = -⟪f, meanPrimitive T hT FInv v⟫_ℝ :=
  existsUnique_mean_weak_solution T hT FInv H (coefficientOperator M hM C hC)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L K (effectiveNegativeBound Be Bc r)
    hK (effectiveNegativeBound_nonneg Be Bc r hBe hBc hr) hF0 hH
    (scaled_mean_boundary_lower_bound ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter hext hcore)
    (source_smallness T K Be Bc r hsmall) f

end EulerMeanSourceInverse
