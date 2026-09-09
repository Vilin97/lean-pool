/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderDerivativeWeight
public import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift

@[expose] public section

/-!
# Actual forward coordinate and time-derivative bounds at one radius

The source propagator bound is used only on the support half-ball. The real
physical time derivative, divided by g, obeys the same fixed-Hq external-word
radius as the forcing and spends just the solve's one shift.
-/

noncomputable section

namespace EulerSourceCylinderForwardSobolev

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderCoefficients
  EulerSourceCylinderForward EulerSourceCylinderForcing EulerSourceForwardCoefficient
  EulerSourceCylinderEquation EulerSourceCylinderTimeBounds
  EulerGevrey EulerParameterWordGevrey EulerLinearDuhamel EulerLinearFundamentalExistence
  EulerTimeLpGramGevrey
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {U E ι : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
  (T : ℝ) (hT : 0 ≤ T) (S : Set Space) (hS : MeasurableSet S)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)
  (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
  (f : C(Icc (0 : ℝ) T,Supported P E S hS)) (a₀ : Supported P U S hS)

private local instance : NormedRing (U →L[ℝ] U) := inferInstance
private local instance : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

theorem normalizedCoordinates_contDiff (hSc : IsCompact S)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (includePath P S hS f)))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a (a₀ : CylinderL2 P U))) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (includePath P S hS
      (normalizedCoordinates P T hT S hS Q Q₁ c hc hQ g hg f a₀))) :=
  EulerLpCylinderRegularForward.source_solution_contDiff P T hT univ MeasurableSet.univ
    (sourceGenerator Q Q₁ c hc hQ) (sourceGenerator_translation_contDiff Q Q₁ c hc hQ)
    S hS hSc isOpen_univ (subset_univ _) g hg (projectedForcing P S hS Q c hc hQ f) a₀
    (projectedForcing_contDiff P S hS Q c hc hQ f hf) ha₀

variable (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hSc : IsCompact S) (hΩo : IsOpen Ω) (hsub : S ⊆ Ω)
  (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1/2 : ℝ))
  (hg₀ : g ⟨0,le_rfl,hT⟩ = 1)
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (includePath P S hS f)))
  (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a (a₀ : CylinderL2 P U)))
  (C A D Rc C₀ C₁ Ri R : ℝ)
  (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
  (hRi : 2*gramCost c C₀ 1*(Rc+1) ≤ Ri)
  (hbQ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q.field t : Space → U →L[ℝ] E) x‖ ≤ C₀*majorant Rc 0 n)
  (hbQ₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q₁.field t : Space → U →L[ℝ] E) x‖ ≤ C₁*majorant Rc 0 n)
  (hRforcing : sobolevCoefficientRadius ι (4*Ri) ≤ R)
  (hR : 2*forwardSobolevCost ι q T C A (forcingCost ι q Ri C₀*D) (18*Ri*C₀*C₁) (4*Ri)*
    (sobolevCoefficientRadius ι (4*Ri)+1) ≤ R)
  (hH3 : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ∀ x : Space, ‖x‖ ≤ (1/2 : ℝ) →
    ‖((fundamentalPath T hT (sourceGenerator Q Q₁ c hc hQ)).forward t x).comp
      ((fundamentalPath T hT (sourceGenerator Q Q₁ c hc hQ)).backward s x)‖ ≤ C*g t/g s)
  (d : ℕ)
  (hforce : ∀ n, block directions q
    (fun a : LiftTangent => pathTranslate P a (includePath P S hS f)) n 0 ≤ D*majorant R d n)
  (hinitial : ∀ n, block directions q
    (fun a : LiftTangent => translate P a (a₀ : CylinderL2 P U)) n 0 ≤ A*majorant R d n)

include hd hΩ hSc hΩo hsub hΩball hg₀ hf ha₀ hC hA hD hRc hC₀ hC₁ hRi hbQ hbQ₁ hRforcing hR hH3
  hforce hinitial

theorem coordinate_forward_block_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (includePath P S hS
      (normalizedCoordinates P T hT S hS Q Q₁ c hc hQ g hg f a₀))) n 0 ≤ majorant R (d+1) n := by
  obtain ⟨hi,-⟩ := EulerTransverseForwardCoefficientGevrey.inverseRadius_bounds c C₀ Rc Ri hc hRc
    hRi
  have hcost : 0 ≤ forcingCost ι q Ri C₀ := mul_nonneg (by norm_num)
    (sobolevCoefficientAmplitude_nonneg q (4*Ri) (3*Ri*C₀) (by positivity) (by positivity))
  exact source_forward_block_bound P directions hd q T hT Q Q₁ c hc hQ Ω S hΩ hS hSc hΩo hsub hΩball
    g hg hg₀ (projectedForcing P S hS Q c hc hQ f) a₀
    (projectedForcing_contDiff P S hS Q c hc hQ f hf) ha₀
    C A (forcingCost ι q Ri C₀*D) Rc C₀ C₁ Ri R hC hA (mul_nonneg hcost hD) hRc hC₀ hC₁ hRi
    hbQ hbQ₁ hR hH3 d
    (projectedForcing_block_bound P S hS Q c hc hQ directions hd q f hf Rc C₀ Ri R D
      hRc hC₀ hD hRi hRforcing hbQ d hforce) hinitial n

/-- The bounded field is the actual time derivative divided by g, by
normalized_full_velocityDerivative_eq. No profile derivative appears. -/
theorem derivative_forward_block_bound (hRone : 1 ≤ R) (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (includePath P S hS
      (normalizedVelocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ g hg))) n 0 ≤
      physicalCost ι q Ri C₀ C₁ D 1*majorant R (d+1) n := by
  have hub := coordinate_forward_block_bound P T hT S hS Q Q₁ c hc hQ g hg f a₀
    directions hd q Ω hΩ hSc hΩo hsub hΩball hg₀ hf ha₀ C A D Rc C₀ C₁ Ri R
    hC hA hD hRc hC₀ hC₁ hRi hbQ hbQ₁ hRforcing hR hH3 d hforce hinitial
  have hforce' (j : ℕ) : block directions q
      (fun a : LiftTangent => pathTranslate P a (includePath P S hS f)) j 0 ≤ D*majorant R (d+1) j
        :=
    (hforce j).trans (mul_le_mul_of_nonneg_left
      (majorant_mono_shift R hRone d (d+1) j (by omega)) hD)
  exact physicalRhs_block_bound P S hS Q Q₁ c hc hQ f
    (normalizedCoordinates P T hT S hS Q Q₁ c hc hQ g hg f a₀) directions hd q hf
    (normalizedCoordinates_contDiff P T hT S hS Q Q₁ c hc hQ g hg f a₀ hSc hf ha₀)
    Rc C₀ C₁ Ri R D 1 hRc hC₀ hC₁ hD zero_le_one hRi hRforcing hbQ hbQ₁
    (d+1) hforce' (fun j => by simpa only [one_mul] using hub j) n

end EulerSourceCylinderForwardSobolev
