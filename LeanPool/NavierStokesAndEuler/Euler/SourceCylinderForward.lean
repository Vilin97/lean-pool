/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceForwardCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelSobolevGevrey
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficients
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRegularSobolev
import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardCoefficientGevrey

/-!
# The source Gram generator on the genuine cylinder L²

The generator below is constructed from the actual frame and its first
time-derivative field by bounded-field Gram inversion. Its translated
coefficient bounds are derived from the frame jets. The forward solution
has the localized H3 bound and the true fixed-Hq mixed external-word
estimate at the same input/output radius.
-/

@[expose] public section


noncomputable section

namespace EulerSourceCylinderForward

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderCoefficients
  EulerLinearDuhamel EulerLinearFundamentalExistence EulerMeanCoefficients
  EulerSourceForwardCoefficient EulerGevrey EulerParameterWordGevrey
  EulerTransverseForwardCoefficientGevrey EulerTimeLpGramGevrey
open scoped BoundedContinuousFunction ContDiff

variable (period : ℝ) [Fact (0 < period)]
  {U E ι : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
  (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)

/-- Cache the standard `NormedRing (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instSourceCylinderForward1 : NormedRing (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedRing (Space →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instSourceCylinderForward2 : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

/-- Actual homogeneous evolution from the source Gram generator. -/
def evolution (S : Set Space) (hS : MeasurableSet S) :=
  constructedEvolution period S hS T hT (sourceGenerator Q Q₁ c hc hQ)

/-- The source coefficient automatically has the translated regularity needed by the solver. -/
theorem source_coefficient_contDiff :
    ContDiff ℝ ∞ (translateCoefficientPath (sourceGenerator Q Q₁ c hc hQ)) :=
  sourceGenerator_translation_contDiff Q Q₁ c hc hQ

include hd in
/-- Mixed spatial-angular external words, including a fixed Sobolev base,
obey the same radius for the actual constructed source solution. -/
theorem source_forward_block_bound
    (Ω K : Set Space) (hΩ : MeasurableSet Ω) (hK : MeasurableSet K)
    (hKc : IsCompact K) (hΩo : IsOpen Ω) (hsub : K ⊆ Ω)
    (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
    (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t) (hg₀ : g ⟨0, le_rfl, hT⟩ = 1)
    (f : C(Icc (0 : ℝ) T, Supported period U K hK)) (a₀ : Supported period U K hK)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period K hK f)))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period U)))
    (C A D Rc C₀ C₁ Ri R : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hRi : 2*gramCost c C₀ 1*(Rc+1) ≤ Ri)
    (hbQ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q.field t : Space → U →L[ℝ] E) x‖ ≤ C₀*majorant Rc 0 n)
    (hbQ₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q₁.field t : Space → U →L[ℝ] E) x‖ ≤ C₁*majorant Rc 0 n)
    (hR : 2*forwardSobolevCost ι q T C A D (18*Ri*C₀*C₁) (4*Ri) *
      (sobolevCoefficientRadius ι (4*Ri)+1) ≤ R)
    (hH3 : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ∀ x : Space, ‖x‖ ≤ (1/2 : ℝ) →
      ‖((fundamentalPath T hT (sourceGenerator Q Q₁ c hc hQ)).forward t x).comp
        ((fundamentalPath T hT (sourceGenerator Q Q₁ c hc hQ)).backward s x)‖ ≤ C*g t/g s)
    (d : ℕ)
    (hforce : ∀ n, block directions q
      (fun a : LiftTangent => pathTranslate period a (includePath period K hK f)) n 0 ≤ D*majorant
          R d n)
    (hinitial : ∀ n, block directions q (fun a : LiftTangent => translate period a (a₀ : CylinderL2
        period U)) n 0 ≤
      A*majorant R d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate period a (includePath period K hK
      ((evolution period T hT Q Q₁ c hc hQ K hK).weightedSolution g hg f a₀))) n 0 ≤
      majorant R (d+1) n := by
  obtain ⟨hRi₀,-⟩ := inverseRadius_bounds c C₀ Rc Ri hc hRc hRi
  exact EulerLpCylinderRegularForward.source_forward_block_bound period directions hd q T hT Ω hΩ
    (sourceGenerator Q Q₁ c hc hQ) (sourceGenerator_translation_contDiff Q Q₁ c hc hQ) g hg hg₀
    K hK hKc hΩo hsub hΩball f a₀ hf ha₀ C A D (18*Ri*C₀*C₁) (4*Ri) R
    hC hA hD (by positivity) (by positivity) hR
    (sourceGenerator_translation_bound Q Q₁ c hc hQ Rc C₀ C₁ Ri hRc hC₀ hC₁ hRi hbQ hbQ₁)
    hH3 d hforce hinitial n

end EulerSourceCylinderForward
