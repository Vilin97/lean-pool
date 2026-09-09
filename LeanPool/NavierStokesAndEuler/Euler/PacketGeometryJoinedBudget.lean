/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryControlledGrowth
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentPhysicalBudgets

@[expose] public section

/-! The actual activation geometry supplies H3 in the complete joined
packet budget.  Source label bounds and the original curvature hypotheses
remain inputs; no propagator estimate or chosen growth profile is assumed. -/

noncomputable section

namespace EulerPacketSourceGeometry.Guards

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLpTranslation
  EulerPacketCofactor EulerPacketPiola EulerPacketParentLabelBounds EulerPacketSourcePropagator
  EulerTransversePacketProvider EulerGevrey EulerVolterraConvolution EulerTimeIntervalRestriction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T} {P : ParentFrame D τ}
  {H : HistoryData (D.initial τ hτ hτT.le)} (J : Guards hτ hτT P H)
  (hball : (1/2 : ℝ) ≤ J.radius)

def sourceGrowthProfile : C(Icc (0 : ℝ) (D.T-τ),ℝ) :=
  (J.halfBall_controlledGrowth hball).choose

theorem sourceGrowthProfile_positive (t : Icc (0 : ℝ) (D.T-τ)) :
    0 < J.sourceGrowthProfile hball t := (J.halfBall_controlledGrowth hball).choose_spec.1 t

theorem sourceGrowthProfile_initial :
    J.sourceGrowthProfile hball ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩=1 :=
  (J.halfBall_controlledGrowth hball).choose_spec.2.1

theorem sourceGrowthProfile_propagator :
    PhysicalGrowth (D.tail τ hτ.le hτT) EulerPacketParentPhysicalBudgets.halfBall
      (J.sourceGrowthProfile hball) (560*P.horizon^10/P.epsilon) :=
  (J.halfBall_controlledGrowth hball).choose_spec.2.2.1

theorem sourceGrowthProfile_amplitude (t : Icc (0 : ℝ) (D.T-τ)) :
    J.primaryAmplitude hball*J.sourceGrowthProfile hball t ≤
      8*Real.exp 6*J.δ*J.hchild/P.rayScale hτ hτT :=
  (J.halfBall_controlledGrowth hball).choose_spec.2.2.2 t

theorem primaryAmplitude_bound : J.primaryAmplitude hball ≤
    8*Real.exp 6*J.δ*J.hchild/P.rayScale hτ hτT := by
  have h := J.sourceGrowthProfile_amplitude hball ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩
  simpa only [J.sourceGrowthProfile_initial hball,mul_one] using h

def joinedBudget (q : ℕ)
    (A V : Icc (0 : ℝ) D.T → SmoothL2Field Space)
    (W : Icc (0 : ℝ) τ → SmoothL2Field Space)
    (F₂ : SmoothCoefficientPath (Icc (0 : ℝ) τ) (Space →L[ℝ] Space))
    (ℓ K Ti : ℝ) (hℓ : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) (hK : 0 ≤ K)
    (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)
    (hA : ∀ t, HasLabelBound K (A t)) (hV : ∀ t, HasLabelBound K (V t))
    (hW : ∀ t, HasLabelBound K (W t))
    (hF : ∀ t x, D.F.field t x = ContinuousLinearMap.id ℝ Space+fderiv ℝ (A t).field (ℓ • x))
    (hF₁ : ∀ t x, D.F₁.field t x = fderiv ℝ (V t).field (ℓ • x))
    (hF₂ : ∀ t x, F₂.field t x = fderiv ℝ (W t).field (ℓ • x))
    (h₂ : ∀ t ∈ Icc (0 : ℝ) τ, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath τ hτ.le (D.initial τ hτ hτT.le).F₁.field s x)
        (extendPath τ hτ.le F₂.field t x) (Icc (0 : ℝ) τ) t)
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hsub : D.support ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1/2 : ℝ)) :
    EulerTransversePacketJoin.Budget D τ hτ hτT H (Fin 4) q :=
  EulerPacketParentPhysicalBudgets.joinedBudget D τ hτ hτT H q A V W F₂
    ℓ K Ti (560*P.horizon^10/P.epsilon) hℓ hℓ1 hK hτ1 hTi J.growth_constant_pos.le
    hA hV hW hF hF₁ hF₂ h₂ hdet (J.sourceGrowthProfile hball)
    (J.sourceGrowthProfile_positive hball) (J.sourceGrowthProfile_initial hball)
    Ω hΩ hΩo hsub hΩball (J.sourceGrowthProfile_propagator hball)

end EulerPacketSourceGeometry.Guards
