/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderForward
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderForcing
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRegularForward
import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardCoefficientGevrey

/-!
# The complete physical forward bound at one mixed-word radius

Physical forcing is projected by the actual Gram left inverse, the supported
coordinate equation is solved by the constructed evolution, and the result
is multiplied by the physical frame. All three operations use the same
external radius R. Only the solve spends one shift.
-/

@[expose] public section


noncomputable section

namespace EulerSourceCylinderForwardSobolev

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderCoefficients
  EulerSourceCylinderForward EulerSourceCylinderForcing EulerSourceForwardCoefficient
  EulerGevrey EulerParameterWordGevrey EulerLinearDuhamel EulerLinearFundamentalExistence
  EulerTimeLpGramGevrey
open scoped ContDiff BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]
  {U E ι : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
  (T : ℝ) (hT : 0 ≤ T) (S : Set Space) (hS : MeasurableSet S)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
  (f : C(Icc (0 : ℝ) T, Supported period E S hS)) (a₀ : Supported period U S hS)

/-- Cache the standard `NormedRing (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instSourceCylinderForwardSobolev1 : NormedRing (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedRing (Space →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instSourceCylinderForwardSobolev2 : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

/-- Actual profile-normalized coordinates with physical forcing as input. -/
def normalizedCoordinates : C(Icc (0 : ℝ) T,Supported period U S hS) :=
  (evolution period T hT Q Q₁ c hc hQ S hS).weightedSolution g hg
    (projectedForcing period S hS Q c hc hQ f) a₀

/-- The corresponding actual profile-normalized physical velocity. -/
def normalizedVelocity : C(Icc (0 : ℝ) T,Supported period E S hS) :=
  physicalVelocity period S hS Q (normalizedCoordinates period T hT S hS Q Q₁ c hc hQ g hg f a₀)

/-- Explicit coefficient cost of projecting a physical forcing at the fixed base order. -/
def forcingCost (ι : Type*) [Fintype ι] (q : ℕ) (Ri C₀ : ℝ) : ℝ :=
  3*sobolevCoefficientAmplitude ι q (4*Ri) (3*Ri*C₀)

/-- The physical solution has the source's genuine fixed-Hq mixed-word bound,
without changing the input external radius. -/
theorem physical_forward_block_bound
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (hSc : IsCompact S) (hΩo : IsOpen Ω) (hsub : S ⊆ Ω)
    (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
    (hg₀ : g ⟨0, le_rfl, hT⟩ = 1)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period U)))
    (C A D Rc C₀ C₁ Ri R : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hRi : 2*gramCost c C₀ 1*(Rc+1) ≤ Ri)
    (hbQ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q.field t : Space → U →L[ℝ] E) x‖ ≤ C₀*majorant Rc 0 n)
    (hbQ₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q₁.field t : Space → U →L[ℝ] E) x‖ ≤ C₁*majorant Rc 0 n)
    (hRforcing : sobolevCoefficientRadius ι (4*Ri) ≤ R)
    (hRframe : sobolevCoefficientRadius ι Rc ≤ R)
    (hR : 2*forwardSobolevCost ι q T C A (forcingCost ι q Ri C₀*D) (18*Ri*C₀*C₁) (4*Ri) *
      (sobolevCoefficientRadius ι (4*Ri)+1) ≤ R)
    (hH3 : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ∀ x : Space, ‖x‖ ≤ (1/2 : ℝ) →
      ‖((fundamentalPath T hT (sourceGenerator Q Q₁ c hc hQ)).forward t x).comp
        ((fundamentalPath T hT (sourceGenerator Q Q₁ c hc hQ)).backward s x)‖ ≤ C*g t/g s)
    (d : ℕ)
    (hforce : ∀ n, block directions q
      (fun a : LiftTangent => pathTranslate period a (includePath period S hS f)) n 0 ≤ D*majorant
          R d n)
    (hinitial : ∀ n, block directions q
      (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period U)) n 0 ≤ A*majorant R d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      (normalizedVelocity period T hT S hS Q Q₁ c hc hQ g hg f a₀))) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc C₀)*majorant R (d+1) n := by
  have hpf := projectedForcing_contDiff period S hS Q c hc hQ f hf
  have hu : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period S hS
      (normalizedCoordinates period T hT S hS Q Q₁ c hc hQ g hg f a₀))) :=
    EulerLpCylinderRegularForward.source_solution_contDiff period T hT Ω hΩ
      (sourceGenerator Q Q₁ c hc hQ) (sourceGenerator_translation_contDiff Q Q₁ c hc hQ)
      S hS hSc hΩo hsub g hg (projectedForcing period S hS Q c hc hQ f) a₀ hpf ha₀
  obtain ⟨hRi₀,-⟩ := EulerTransverseForwardCoefficientGevrey.inverseRadius_bounds c C₀ Rc Ri hc hRc
      hRi
  have hcost : 0 ≤ forcingCost ι q Ri C₀ := mul_nonneg (by norm_num)
    (sobolevCoefficientAmplitude_nonneg q (4*Ri) (3*Ri*C₀) (by positivity) (by positivity))
  have hub (j : ℕ) : block directions q (fun a : LiftTangent => pathTranslate period a (includePath
      period S hS
      (normalizedCoordinates period T hT S hS Q Q₁ c hc hQ g hg f a₀))) j 0 ≤ majorant R (d+1) j :=
    source_forward_block_bound period directions hd q T hT Q Q₁ c hc hQ Ω S hΩ hS hSc hΩo hsub
        hΩball
      g hg hg₀ (projectedForcing period S hS Q c hc hQ f) a₀ hpf ha₀
      C A (forcingCost ι q Ri C₀*D) Rc C₀ C₁ Ri R hC hA (mul_nonneg hcost hD) hRc hC₀ hC₁ hRi
      hbQ hbQ₁ hR hH3 d
      (projectedForcing_block_bound period S hS Q c hc hQ directions hd q f hf Rc C₀ Ri R D
        hRc hC₀ hD hRi hRforcing hbQ d hforce) hinitial j
  have hout := physicalVelocity_block_bound period S hS Q directions hd q
    (normalizedCoordinates period T hT S hS Q Q₁ c hc hQ g hg f a₀) hu
    Rc C₀ R 1 hRc hC₀ zero_le_one hRframe hbQ (d+1)
    (fun j => by simpa only [one_mul] using hub j) n
  simpa only [mul_one,normalizedVelocity] using hout

end EulerSourceCylinderForwardSobolev
