/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketLocalHistory

@[expose] public section

/-!
# A fixed source budget for the joined transverse inverse

Every hypothesis is a coefficient, time-length, or homogeneous-propagator
bound. The radius guards use unit forcing amplitude and do not depend on
the forcing, its amplitude, its derivative shift, or the recursive grade.
Coercivity is required only on the actual history interval [0,τ].
-/

noncomputable section

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerGevrey EulerParameterWordGevrey EulerFixedEvolutionSobolev
  EulerTransverseFixedSobolev EulerTimeLpGramSobolev EulerTimeLpAccelerationSobolev
  EulerTimeLpGramGevrey EulerSourceCylinderForward EulerSourceCylinderForwardSobolev
  EulerSourceForwardCoefficient EulerLinearFundamentalExistence EulerSourceCylinderTimeBounds
  EulerLinearDuhamel
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

private local instance : NormedRing (U →L[ℝ] U) := inferInstance
private local instance : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

variable
  (D : Data U) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (ι : Type*) [Fintype ι] (q : ℕ)

/-- Source-only quantitative data, fixed once for all forcing profiles and grades. -/
structure Budget where
  g : C(Icc (0 : ℝ) (D.T-τ),ℝ)
  positive : ∀ t, 0 < g t
  initial_one : g ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ = 1
  neighborhood : Set Space
  neighborhood_measurable : MeasurableSet neighborhood
  neighborhood_open : IsOpen neighborhood
  support_subset : D.support ⊆ neighborhood
  neighborhood_halfball : ∀ x ∈ neighborhood, ‖x‖ ≤ (1/2 : ℝ)
  Rc : ℝ
  C₀ : ℝ
  C₁ : ℝ
  CH : ℝ
  C : ℝ
  Ri : ℝ
  R : ℝ
  Rc_nonneg : 0 ≤ Rc
  C₀_nonneg : 0 ≤ C₀
  C₁_nonneg : 0 ≤ C₁
  CH_nonneg : 0 ≤ CH
  C_nonneg : 0 ≤ C
  history_length : τ ≤ 1
  frame_bound : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤
    C₀*majorant Rc 0 n
  frameDerivative_bound : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C₁*majorant Rc 0 n
  hessian_bound : ∀ n t x,
    ‖iteratedFDeriv ℝ n (B.H.field t : Space → Space →L[ℝ] Space) x‖ ≤ CH*majorant Rc 0 n
  history_weak :
    2*blockCost ι q τ Rc C₀ C₁ CH (D.initial τ hτ hτT.le).frameLower 1*
      (sobolevCoefficientRadius ι Rc+1) ≤ R
  history_strong :
    2*gramBlockCost ι q (D.initial τ hτ hτT.le).frameLower Rc C₀
      (accelerationBlockAmplitude ι q Rc C₀ C₁ 1 1)*(sobolevCoefficientRadius ι Rc+1) ≤ R
  history_uniform :
    2*gramBlockCost ι q (D.initial τ hτ hτT.le).frameLower Rc C₀
      (accelerationBlockAmplitude ι q Rc C₀ C₁ 1 (traceCost τ))*(sobolevCoefficientRadius ι Rc+1) ≤
        R
  forward_inverse : 2*gramCost (D.tail τ hτ.le hτT).frameLower C₀ 1*(Rc+1) ≤ Ri
  forcing_radius : sobolevCoefficientRadius ι (4*Ri) ≤ R
  forward_radius :
    2*forwardSobolevCost ι q (D.T-τ) C (traceCost τ)
      (forcingCost ι q Ri C₀*1) (18*Ri*C₀*C₁) (4*Ri)*(sobolevCoefficientRadius ι (4*Ri)+1) ≤ R
  propagator : ∀ t s : Icc (0 : ℝ) (D.T-τ), s ≤ t → ∀ x : Space, ‖x‖ ≤ (1/2 : ℝ) →
    ‖((fundamentalPath (D.T-τ) (sub_pos.mpr hτT).le
        (sourceGenerator (D.tail τ hτ.le hτT).frame (D.tail τ hτ.le hτT).frameDerivative
          (D.tail τ hτ.le hτT).frameLower (D.tail τ hτ.le hτT).frameLower_pos
          (D.tail τ hτ.le hτT).frame_lower)).forward t x).comp
      ((fundamentalPath (D.T-τ) (sub_pos.mpr hτT).le
        (sourceGenerator (D.tail τ hτ.le hτT).frame (D.tail τ hτ.le hτT).frameDerivative
          (D.tail τ hτ.le hτT).frameLower (D.tail τ hτ.le hτT).frameLower_pos
          (D.tail τ hτ.le hτT).frame_lower)).backward s x)‖ ≤ C*g t/g s

namespace Budget

variable {D τ hτ hτT B ι q} (L : Budget D τ hτ hτT B ι q)

def fullProfile : C(Icc (0 : ℝ) D.T,ℝ) :=
  EulerElapsedTimePathGluing.profile D.T τ hτ.le hτT.le L.g L.initial_one

theorem fullProfile_pos (t : Icc (0 : ℝ) D.T) : 0 < L.fullProfile t :=
  EulerElapsedTimePathGluing.profile_pos D.T τ hτ.le hτT.le L.g L.initial_one L.positive t

theorem radius_bounds : 1 ≤ L.R ∧ sobolevCoefficientRadius ι L.Rc ≤ L.R :=
  weak_radius_bounds ι q τ L.Rc L.C₀ L.C₁ L.CH (D.initial τ hτ hτT.le).frameLower 1 L.R
    hτ.le L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg L.CH_nonneg zero_le_one L.history_weak

def velocityCost : ℝ :=
  3*sobolevCoefficientAmplitude ι q L.Rc L.C₀*traceCost τ+
    3*sobolevCoefficientAmplitude ι q L.Rc L.C₀

def derivativeCost : ℝ :=
  3*sobolevCoefficientAmplitude ι q L.Rc L.C₁*traceCost τ+
    3*sobolevCoefficientAmplitude ι q L.Rc L.C₀+
      physicalCost ι q L.Ri L.C₀ L.C₁ 1 1

end Budget
end EulerTransversePacketJoin
