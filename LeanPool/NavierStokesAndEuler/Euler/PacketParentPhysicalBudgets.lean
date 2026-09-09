/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketParentLabelBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentJoinedBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentForwardBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourcePropagator

@[expose] public section

/-! Source-budget constructors using the literal parent fields in (21) and
the physical tangent growth estimate.  H3 for the constructed coordinate
propagator, the Hessian jets, and every inverse radius guard are conclusions.
The curvature/smallness hypotheses remain in the genuine source data. -/

noncomputable section

namespace EulerPacketParentPhysicalBudgets

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLpTranslation
  EulerPacketCofactor EulerPacketPiola EulerPacketParentLabelBounds EulerPacketSourcePropagator
  EulerTransversePacketProvider EulerGevrey EulerVolterraConvolution EulerTimeIntervalRestriction
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

def halfBall : Set Space := {x | ‖x‖ ≤ (1/2 : ℝ)}

def physicalCost (K Cp : ℝ) : ℝ := 3*(frameAmplitude K)^3*Cp

theorem physicalCost_nonneg (K Cp : ℝ) (hCp : 0 ≤ Cp) : 0 ≤ physicalCost K Cp := by
  have h := frameAmplitude_nonneg K
  unfold physicalCost
  positivity

/-- At a zero-history stage the real label bounds and physical propagator
construct the complete source forward budget, before any forcing is chosen. -/
def forwardBudget (D : Data U) (q : ℕ)
    (A V : Icc (0 : ℝ) D.T → SmoothL2Field Space)
    (ℓ K Cp : ℝ) (hℓ : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) (hK : 0 ≤ K) (hCp : 0 ≤ Cp)
    (hA : ∀ t, HasLabelBound K (A t)) (hV : ∀ t, HasLabelBound K (V t))
    (hF : ∀ t x, D.F.field t x = ContinuousLinearMap.id ℝ Space+fderiv ℝ (A t).field (ℓ • x))
    (hF₁ : ∀ t x, D.F₁.field t x = fderiv ℝ (V t).field (ℓ • x))
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
    (g : C(Icc (0 : ℝ) D.T,ℝ)) (hg : ∀ t, 0 < g t)
    (hg0 : g ⟨0,le_rfl,D.T_pos.le⟩ = 1)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hsub : D.support ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1/2 : ℝ))
    (hphysical : PhysicalGrowth D halfBall g Cp) : EulerTransversePacketForward.Budget D (Fin 4) q
      := by
  have hbF := coefficient_deformation_bound D.F A (ℓ • ContinuousLinearMap.id ℝ Space)
    (labelScaling_norm_le ℓ hℓ hℓ1) hF K hK hA
  have hbF₁ := coefficient_gradient_bound D.F₁ V (ℓ • ContinuousLinearMap.id ℝ Space)
    (labelScaling_norm_le ℓ hℓ hℓ1) hF₁ K hK hV
  have hz : ∀ t x, ‖D.F.field t x‖ ≤ frameAmplitude K := by
    intro t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using hbF 0 t x
  apply EulerPacketParentForwardBudget.sourceForwardBudget D q (coefficientRadius K)
    (frameAmplitude K) (gradientAmplitude K) (physicalCost K Cp)
    (coefficientRadius_nonneg K) (frameAmplitude_nonneg K) (gradientAmplitude_nonneg K)
    (physicalCost_nonneg K Cp hCp) hdet hbF hbF₁ g hg hg0 Ω hΩ hΩo hsub hΩball
  intro t s hst x hx
  exact propagator_bound_of_deformation D halfBall g hg Cp (frameAmplitude K)
    hCp (frameAmplitude_nonneg K) hphysical (fun r y _ => hdet r y)
    (fun r y _ => hz r y) t s hst x hx

/-- Positive history uses the actual acceleration in (21) and its true
within-time derivative identity.  Jacobi and determinant one then supply
the Hessian multiplier bound needed by the joined variational inverse. -/
def joinedBudget (D : Data U) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
    (B : HistoryData (D.initial τ hτ hτT.le)) (q : ℕ)
    (A V : Icc (0 : ℝ) D.T → SmoothL2Field Space)
    (W : Icc (0 : ℝ) τ → SmoothL2Field Space)
    (F₂ : SmoothCoefficientPath (Icc (0 : ℝ) τ) EndSpace)
    (ℓ K Ti Cp : ℝ) (hℓ : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) (hK : 0 ≤ K)
    (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti) (hCp : 0 ≤ Cp)
    (hA : ∀ t, HasLabelBound K (A t)) (hV : ∀ t, HasLabelBound K (V t))
    (hW : ∀ t, HasLabelBound K (W t))
    (hF : ∀ t x, D.F.field t x = ContinuousLinearMap.id ℝ Space+fderiv ℝ (A t).field (ℓ • x))
    (hF₁ : ∀ t x, D.F₁.field t x = fderiv ℝ (V t).field (ℓ • x))
    (hF₂ : ∀ t x, F₂.field t x = fderiv ℝ (W t).field (ℓ • x))
    (h₂ : ∀ t ∈ Icc (0 : ℝ) τ, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath τ hτ.le (D.initial τ hτ hτT.le).F₁.field s x)
        (extendPath τ hτ.le F₂.field t x) (Icc (0 : ℝ) τ) t)
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
    (g : C(Icc (0 : ℝ) (D.T-τ),ℝ)) (hg : ∀ t, 0 < g t)
    (hg0 : g ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ = 1)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hsub : D.support ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1/2 : ℝ))
    (hphysical : PhysicalGrowth (D.tail τ hτ.le hτT) halfBall g Cp) :
    EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) q := by
  have hbF := coefficient_deformation_bound D.F A (ℓ • ContinuousLinearMap.id ℝ Space)
    (labelScaling_norm_le ℓ hℓ hℓ1) hF K hK hA
  have hbF₁ := coefficient_gradient_bound D.F₁ V (ℓ • ContinuousLinearMap.id ℝ Space)
    (labelScaling_norm_le ℓ hℓ hℓ1) hF₁ K hK hV
  have hbF₂ := coefficient_gradient_bound F₂ W (ℓ • ContinuousLinearMap.id ℝ Space)
    (labelScaling_norm_le ℓ hℓ hℓ1) hF₂ K hK hW
  have hz : ∀ t x, ‖D.F.field t x‖ ≤ frameAmplitude K := by
    intro t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using hbF 0 t x
  apply EulerPacketParentJoinedBudget.sourceJoinedBudget D τ hτ hτT B q Ti (coefficientRadius K)
    (frameAmplitude K) (gradientAmplitude K) (gradientAmplitude K) (physicalCost K Cp)
    hτ1 hTi (coefficientRadius_nonneg K) (frameAmplitude_nonneg K) (gradientAmplitude_nonneg K)
    (gradientAmplitude_nonneg K) (physicalCost_nonneg K Cp hCp) hdet hbF hbF₁ F₂ h₂ hbF₂
    g hg hg0 Ω hΩ hΩo hsub hΩball
  intro t s hst x hx
  exact propagator_bound_of_deformation (D.tail τ hτ.le hτT) halfBall g hg Cp (frameAmplitude K)
    hCp (frameAmplitude_nonneg K) hphysical
    (fun r y _ => hdet (tailInclusion D.T τ hτ.le r) y)
    (fun r y _ => hz (tailInclusion D.T τ hτ.le r) y) t s hst x hx

end EulerPacketParentPhysicalBudgets
