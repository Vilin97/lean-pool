/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderForwardSobolev
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderTimeBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing
import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathWeight
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderWeight
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryBounds
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRegularForward
import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift
import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardCoefficientGevrey
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderEquation
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTimeWeight

/-!
# The source forward estimates apply to the actual packet paths

The input bound below is on the literal forcing divided by g. The weighted
Duhamel identities identify the result with the actual unweighted solution,
and with its actual time derivative divided by g. No g derivative or profile
extremum is introduced.
-/

section

/-!
# Actual forward coordinate and time-derivative bounds at one radius

The source propagator bound is used only on the support half-ball. The real
physical time derivative, divided by g, obeys the same fixed-Hq external-word
radius as the forcing and spends just the solve's one shift.
-/

section

/-! The bounded time-right-side estimate applies to the actual PDE time derivative divided by g. -/

@[expose] public section

noncomputable section

namespace EulerSourceCylinderEquation

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerSourceCylinderTimeBounds EulerSourceCylinderForwardSobolev EulerContinuousTimeWeight
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(Icc (0 : ℝ) T, Supported P E S hS)) (a₀ : Supported P U S hS)

theorem velocityDerivative_eq_physicalRhs :
    velocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ =
      physicalRhs P S hS Q Q₁ c hc hQ f (coordinates P S hS T hT Q Q₁ c hc hQ f a₀) := rfl

variable (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)

/-- This is A_t/g, obtained from the actual equation rather than differentiating A/g. -/
def normalizedVelocityDerivative : C(Icc (0 : ℝ) T,Supported P E S hS) :=
  physicalRhs P S hS Q Q₁ c hc hQ f
    (normalizedCoordinates P T hT S hS Q Q₁ c hc hQ g hg f a₀)

theorem velocityDerivative_weight_eq :
    velocityDerivative P S hS T hT Q Q₁ c hc hQ (weight g f) a₀ =
      weight g (normalizedVelocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ g hg) := by
  rw [velocityDerivative_eq_physicalRhs,coordinates_weight_eq]
  exact physicalRhs_weight P S hS Q Q₁ c hc hQ f _ g

theorem normalized_full_velocityDerivative_eq :
    normalize g hg (includePath P S hS
      (velocityDerivative P S hS T hT Q Q₁ c hc hQ (weight g f) a₀)) =
      includePath P S hS (normalizedVelocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ g hg) := by
  rw [velocityDerivative_weight_eq,include_weight,normalize_weight]

end EulerSourceCylinderEquation

end
end

end

@[expose] public section

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
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
  (f : C(Icc (0 : ℝ) T, Supported P E S hS)) (a₀ : Supported P U S hS)

/-- Cache the standard `NormedRing (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instSourceCylinderDerivativeBounds1 : NormedRing (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedRing (Space →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instSourceCylinderDerivativeBounds2 : NormedRing (Space →ᵇ U →L[ℝ] U) :=
    inferInstance

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
  (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
  (hg₀ : g ⟨0, le_rfl, hT⟩ = 1)
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (includePath P S hS f)))
  (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a (a₀ : CylinderL2 P U)))
  (C A D Rc C₀ C₁ Ri R : ℝ)
  (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
  (hRi : 2 * gramCost c C₀ 1 * (Rc + 1) ≤ Ri)
  (hbQ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q.field t : Space → U →L[ℝ] E) x‖ ≤ C₀ * majorant Rc 0 n)
  (hbQ₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q₁.field t : Space → U →L[ℝ] E) x‖ ≤ C₁ * majorant Rc 0 n)
  (hRforcing : sobolevCoefficientRadius ι (4 * Ri) ≤ R)
  (hR : 2 * forwardSobolevCost ι q T C A (forcingCost ι q Ri C₀ * D) (18 * Ri * C₀ * C₁) (4 * Ri) *
    (sobolevCoefficientRadius ι (4 * Ri) + 1) ≤ R)
  (hH3 : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ∀ x : Space, ‖x‖ ≤ (1 / 2 : ℝ) →
    ‖((fundamentalPath T hT (sourceGenerator Q Q₁ c hc hQ)).forward t x).comp
      ((fundamentalPath T hT (sourceGenerator Q Q₁ c hc hQ)).backward s x)‖ ≤ C * g t / g s)
  (d : ℕ)
  (hforce : ∀ n, block directions q
    (fun a : LiftTangent => pathTranslate P a (includePath P S hS f)) n 0 ≤ D * majorant R d n)
  (hinitial : ∀ n, block directions q
    (fun a : LiftTangent => translate P a (a₀ : CylinderL2 P U)) n 0 ≤ A * majorant R d n)

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider.Forcing

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
      EulerLpCylinderRectangular
  EulerPacketProfileRecursion EulerGevrey EulerParameterWordGevrey EulerContinuousTimeWeight
  EulerSourceCylinderForwardSobolev EulerSourceCylinderEquation EulerSourceCylinderTimeBounds
  EulerSourceCylinderForward EulerSourceForwardCoefficient EulerLinearFundamentalExistence
  EulerTimeLpGramGevrey EulerLinearDuhamel
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Cache the standard `NormedRing (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instTransversePacketForwardBounds1 : NormedRing (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedRing (Space →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketForwardBounds2 : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

variable
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)
  (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t)
  {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω) (hsub : D.support ⊆ Ω)
  (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
  (hg0 : g ⟨0, le_rfl, D.T_pos.le⟩ = 1)
  (C A Cf Rc C₀ C₁ Ri R : ℝ)
  (hC : 0 ≤ C) (hA : 0 ≤ A) (hCf : 0 ≤ Cf) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
  (hRi : 2 * gramCost D.frameLower C₀ 1 * (Rc + 1) ≤ Ri)
  (hbF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C₀ * majorant
      Rc
      0 n)
  (hbF₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C₁ * majorant
      Rc 0 n)
  (hRforcing : sobolevCoefficientRadius ι (4 * Ri) ≤ R)
  (hR : 2 * forwardSobolevCost ι q D.T C A (forcingCost ι q Ri C₀ * Cf) (18 * Ri * C₀ * C₁) (4 *
      Ri) *
    (sobolevCoefficientRadius ι (4 * Ri) + 1) ≤ R)
  (hH3 : ∀ t s : Icc (0 : ℝ) D.T, s ≤ t → ∀ x : Space, ‖x‖ ≤ (1 / 2 : ℝ) →
    ‖((fundamentalPath D.T D.T_pos.le
        (sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos
            D.frame_lower)).forward t x).comp
      ((fundamentalPath D.T D.T_pos.le
        (sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos
            D.frame_lower)).backward s x)‖ ≤ C * g t / g s)
  (d : ℕ)
  (hforce : ∀ n, block directions q (fun a => pathTranslate P a
    (normalize g hg (includePath P D.support D.support_measurable G.path))) n 0 ≤ Cf * majorant R d
        n)
  (hinitial : ∀ n, block directions q
    (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ A * majorant R d n)

include hdir hΩ hΩo hsub hΩball hg0 hC hA hCf hRc hC₀ hC₁ hRi hbF hbF₁ hRforcing hR hH3 hforce
    hinitial

/-- The literal forward packet velocity divided by g, at the input radius. -/
theorem source_velocity_normalized_bound
    (hRframe : sobolevCoefficientRadius ι Rc ≤ R) (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize g hg (includePath P D.support D.support_measurable (G.velocityPath I)))) n 0 ≤
        (3*sobolevCoefficientAmplitude ι q Rc C₀)*majorant R (d+1) n := by
  have he := normalized_full_velocity_eq P D.support D.support_measurable D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower g hg
    (normalize g hg G.path) I.value
  rw [weight_normalize] at he
  change block directions q (fun a => pathTranslate P a
    (normalize g hg (includePath P D.support D.support_measurable
      (velocity P D.support D.support_measurable D.T D.T_pos.le
        D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value)))) n
            0 ≤ _
  rw [he]
  exact physical_forward_block_bound P D.T D.T_pos.le D.support D.support_measurable
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower g hg
    (normalize g hg G.path) I.value directions hdir q Ω hΩ D.support_compact hΩo hsub hΩball hg0
    (normalize_orbit_contDiff P g hg _ G.path_orbit) I.orbit C A Cf Rc C₀ C₁ Ri R
    hC hA hCf hRc hC₀ hC₁ hRi
    (fun j => D.frame_spatial_bound j _ (hbF j))
    (fun j => D.frameDerivative_spatial_bound j _ (hbF₁ j))
    hRforcing hRframe hR hH3 d hforce hinitial n

/-- This is A_t/g for the actual raw solution, not a derivative of A/g. -/
theorem source_derivative_normalized_bound (hRone : 1 ≤ R) (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize g hg (includePath P D.support D.support_measurable (G.derivativePath I)))) n 0 ≤
        physicalCost ι q Ri C₀ C₁ Cf 1*majorant R (d+1) n := by
  have he := normalized_full_velocityDerivative_eq P D.support D.support_measurable D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    (normalize g hg G.path) I.value g hg
  rw [weight_normalize] at he
  change block directions q (fun a => pathTranslate P a
    (normalize g hg (includePath P D.support D.support_measurable
      (velocityDerivative P D.support D.support_measurable D.T D.T_pos.le
        D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value)))) n
            0 ≤ _
  rw [he]
  exact derivative_forward_block_bound P D.T D.T_pos.le D.support D.support_measurable
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower g hg
    (normalize g hg G.path) I.value directions hdir q Ω hΩ D.support_compact hΩo hsub hΩball hg0
    (normalize_orbit_contDiff P g hg _ G.path_orbit) I.orbit C A Cf Rc C₀ C₁ Ri R
    hC hA hCf hRc hC₀ hC₁ hRi
    (fun j => D.frame_spatial_bound j _ (hbF j))
    (fun j => D.frameDerivative_spatial_bound j _ (hbF₁ j))
    hRforcing hR hH3 d hforce hinitial hRone n

end EulerTransversePacketProvider.Forcing
