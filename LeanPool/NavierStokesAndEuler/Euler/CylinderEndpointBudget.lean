/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointRegularity
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletPhysicalBounds

@[expose] public section

/-!
Source-only guards for the affine-terminal cylinder inverse. The affine
forcing is bounded for unit terminal data; no terminal amplitude, derivative
shift, or recursive grade occurs in the radius conditions.
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerGevrey
  EulerParameterWordGevrey EulerTransverseFixedSobolev EulerFixedEvolutionSobolev
  EulerTimeLpGramSobolev EulerTimeLpAccelerationSobolev
open scoped ContDiff BoundedContinuousFunction

def endpointForcingCost (ι : Type*) [Fintype ι] (q : ℕ) (T Rc C₁ : ℝ) : ℝ :=
  6*sobolevCoefficientAmplitude ι q Rc C₁*T⁻¹

variable {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure EndpointBudget (D : Coefficients T U E) (ι : Type*) [Fintype ι] (q : ℕ) where
  Rc : ℝ
  C₀ : ℝ
  C₁ : ℝ
  CH : ℝ
  R : ℝ
  Rc_nonneg : 0 ≤ Rc
  C₀_nonneg : 0 ≤ C₀
  C₁_nonneg : 0 ≤ C₁
  CH_nonneg : 0 ≤ CH
  time_le_one : T ≤ 1
  frame_smooth : ContDiff ℝ ∞ (translateCoefficientPath D.Q)
  frameDerivative_smooth : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁)
  hessian_smooth : ContDiff ℝ ∞ (translateCoefficientPath D.H)
  frame_bound : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q) a‖ ≤ C₀*majorant Rc 0 n
  frameDerivative_bound : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q₁) a‖ ≤
    C₁*majorant Rc 0 n
  hessian_bound : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.H) a‖ ≤ CH*majorant Rc 0 n
  weak_radius : 2*blockCost ι q T Rc C₀ C₁ CH D.lower (endpointForcingCost ι q T Rc C₁)*
    (sobolevCoefficientRadius ι Rc+1) ≤ R
  strong_radius : 2*gramBlockCost ι q D.lower Rc C₀
    (accelerationBlockAmplitude ι q Rc C₀ C₁ (endpointForcingCost ι q T Rc C₁) 1)*
      (sobolevCoefficientRadius ι Rc+1) ≤ R
  uniform_radius : 2*gramBlockCost ι q D.lower Rc C₀
    (accelerationBlockAmplitude ι q Rc C₀ C₁ (endpointForcingCost ι q T Rc C₁) (traceCost T))*
      (sobolevCoefficientRadius ι Rc+1) ≤ R

namespace EndpointBudget

variable {D : Coefficients T U E} {ι : Type*} [Fintype ι] {q : ℕ} (L : EndpointBudget D ι q)

theorem forcingCost_nonneg : 0 ≤ endpointForcingCost ι q T L.Rc L.C₁ :=
  mul_nonneg (mul_nonneg (by norm_num)
    (sobolevCoefficientAmplitude_nonneg q L.Rc L.C₁ L.Rc_nonneg L.C₁_nonneg))
      (inv_nonneg.mpr D.time_pos.le)

theorem radius_bounds : 1 ≤ L.R ∧ sobolevCoefficientRadius ι L.Rc ≤ L.R :=
  weak_radius_bounds ι q T L.Rc L.C₀ L.C₁ L.CH D.lower
    (endpointForcingCost ι q T L.Rc L.C₁) L.R D.time_pos.le L.Rc_nonneg
    L.C₀_nonneg L.C₁_nonneg L.CH_nonneg L.forcingCost_nonneg L.weak_radius

def coordinateCost (_L : EndpointBudget D ι q) : ℝ := T⁻¹+traceCost T
def velocityCost : ℝ := 3*sobolevCoefficientAmplitude ι q L.Rc L.C₀*L.coordinateCost
def derivativeCost : ℝ := 3*sobolevCoefficientAmplitude ι q L.Rc L.C₁*L.coordinateCost+
  3*sobolevCoefficientAmplitude ι q L.Rc L.C₀

theorem coordinateCost_nonneg : 0 ≤ L.coordinateCost :=
  add_nonneg (inv_nonneg.mpr D.time_pos.le) (traceCost_nonneg T D.time_pos.le)

end EndpointBudget
end EulerCylinderDirichlet.Coefficients
