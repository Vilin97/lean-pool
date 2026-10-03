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
    velocityDerivative P S hS T hT Q Q₁ c hc hQ
        (weight (K := Icc (0 : ℝ) T) (E := Supported P E S hS) g f) a₀ =
      weight (K := Icc (0 : ℝ) T) (E := Supported P E S hS) g
        (normalizedVelocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ g hg) :=
  (velocityDerivative_eq_physicalRhs P S hS T hT Q Q₁ c hc hQ _ a₀).trans
    ((congrArg (physicalRhs P S hS Q Q₁ c hc hQ
      (weight (K := Icc (0 : ℝ) T) (E := Supported P E S hS) g f))
    (coordinates_weight_eq P S hS T hT Q Q₁ c hc hQ g hg f a₀)).trans
    (physicalRhs_weight P S hS Q Q₁ c hc hQ f
      (normalizedCoordinates P T hT S hS Q Q₁ c hc hQ g hg f a₀) g))

theorem normalized_full_velocityDerivative_eq :
    EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) T) (E := CylinderL2 P E) g hg
        (includePath (K := Icc (0 : ℝ) T) (V := E) P S hS
          (velocityDerivative P S hS T hT Q Q₁ c hc hQ
            (weight (K := Icc (0 : ℝ) T) (E := Supported P E S hS) g f) a₀)) =
      includePath (K := Icc (0 : ℝ) T) (V := E) P S hS
        (normalizedVelocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ g hg) :=
  (congrArg (fun u => EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) T)
      (E := CylinderL2 P E) g hg (includePath (K := Icc (0 : ℝ) T) (V := E) P S hS u))
    (velocityDerivative_weight_eq P S hS T hT Q Q₁ c hc hQ f a₀ g hg)).trans
    (normalize_weight g hg (includePath (K := Icc (0 : ℝ) T) (V := E) P S hS
      (normalizedVelocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ g hg)))

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
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a
      (includePath (K := Icc (0 : ℝ) T) (V := E) P S hS f)))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate (V := U) P a (a₀ : CylinderL2 P U))) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate (K := Icc (0 : ℝ) T) (V := U) P a
      (includePath (K := Icc (0 : ℝ) T) (V := U) P S hS
        (normalizedCoordinates P T hT S hS Q Q₁ c hc hQ g hg f a₀))) :=
  EulerLpCylinderRegularForward.source_solution_contDiff P T hT univ MeasurableSet.univ
    (sourceGenerator Q Q₁ c hc hQ) (sourceGenerator_translation_contDiff Q Q₁ c hc hQ)
    S hS hSc isOpen_univ (subset_univ _) g hg (projectedForcing P S hS Q c hc hQ f) a₀
    (projectedForcing_contDiff P S hS Q c hc hQ f hf) ha₀

variable (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hSc : IsCompact S) (hΩo : IsOpen Ω) (hsub : S ⊆ Ω)
  (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
  (hg₀ : g ⟨0, le_rfl, hT⟩ = 1)
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a
    (includePath (K := Icc (0 : ℝ) T) (V := E) P S hS f)))
  (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate (V := U) P a (a₀ : CylinderL2 P U)))
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
    (fun a : LiftTangent => pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a
      (includePath (K := Icc (0 : ℝ) T) (V := E) P S hS f)) n 0 ≤ D * majorant R d n)
  (hinitial : ∀ n, block directions q
    (fun a : LiftTangent => translate (V := U) P a (a₀ : CylinderL2 P U)) n 0 ≤
      A * majorant R d n)

include hd hΩ hSc hΩo hsub hΩball hg₀ hf ha₀ hC hA hD hRc hC₀ hC₁ hRi hbQ hbQ₁ hRforcing hR hH3
    hforce hinitial

theorem coordinate_forward_block_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate (K := Icc (0 : ℝ) T) (V := U) P a
      (includePath (K := Icc (0 : ℝ) T) (V := U) P S hS
        (normalizedCoordinates P T hT S hS Q Q₁ c hc hQ g hg f a₀))) n 0 ≤ majorant R (d+1) n := by
  have hi := (EulerTransverseForwardCoefficientGevrey.inverseRadius_bounds c C₀ Rc Ri hc hRc
      hRi).1
  have hcost : 0 ≤ forcingCost ι q Ri C₀ := mul_nonneg (by norm_num)
    (sobolevCoefficientAmplitude_nonneg q (4*Ri) (3*Ri*C₀) (mul_nonneg zero_le_four hi)
      (mul_nonneg (mul_nonneg zero_le_three hi) hC₀))
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
    block directions q (fun a : LiftTangent => pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a
      (includePath (K := Icc (0 : ℝ) T) (V := E) P S hS
        (normalizedVelocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ g hg))) n 0 ≤
      physicalCost ι q Ri C₀ C₁ D 1*majorant R (d+1) n := by
  have hub := coordinate_forward_block_bound P T hT S hS Q Q₁ c hc hQ g hg f a₀
    directions hd q Ω hΩ hSc hΩo hsub hΩball hg₀ hf ha₀ C A D Rc C₀ C₁ Ri R
    hC hA hD hRc hC₀ hC₁ hRi hbQ hbQ₁ hRforcing hR hH3 d hforce hinitial
  have hforce' (j : ℕ) : block directions q
      (fun a : LiftTangent => pathTranslate (K := Icc (0 : ℝ) T) (V := E) P a
        (includePath (K := Icc (0 : ℝ) T) (V := E) P S hS f)) j 0 ≤ D*majorant R (d+1) j
          :=
    (hforce j).trans (mul_le_mul_of_nonneg_left
      (majorant_mono_shift R hRone d (d+1) j (by omega)) hD)
  exact physicalRhs_block_bound P S hS Q Q₁ c hc hQ f
    (normalizedCoordinates P T hT S hS Q Q₁ c hc hQ g hg f a₀) directions hd q hf
    (normalizedCoordinates_contDiff P T hT S hS Q Q₁ c hc hQ g hg f a₀ hSc hf ha₀)
    Rc C₀ C₁ Ri R D 1 hRc hC₀ hC₁ hD zero_le_one hRi hRforcing hbQ hbQ₁
    (d+1) hforce' (fun j => (hub j).trans_eq (one_mul _).symm) n

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

omit [CompleteSpace U] in
theorem normalize_path_orbit {D : Data U} {raw : VectorField} (G : Forcing P D raw)
    (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate (K := Icc (0 : ℝ) D.T) (V := Space) P a
      (includePath (K := Icc (0 : ℝ) D.T) (V := Space) P D.support D.support_measurable
        (EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T)
          (E := Supported P Space D.support D.support_measurable) g hg G.path))) := by
  rw [include_normalize]
  exact normalize_orbit_contDiff P g hg _ G.path_orbit

/-- The forward velocity divided by g is the normalized velocity of the normalized forcing. -/
theorem normalized_velocityPath_eq {D : Data U} {raw : VectorField} (G : Forcing P D raw)
    (I : InitialData P D) (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t) :
    EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T) (E := CylinderL2 P Space) g hg
        (includePath (K := Icc (0 : ℝ) D.T) (V := Space) P D.support D.support_measurable
          (G.velocityPath I)) =
      includePath (K := Icc (0 : ℝ) D.T) (V := Space) P D.support D.support_measurable
        (normalizedVelocity P D.T D.T_pos.le D.support D.support_measurable
          D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower g hg
          (EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T)
            (E := Supported P Space D.support D.support_measurable) g hg G.path) I.value) := by
  have hw := weight_normalize (K := Icc (0 : ℝ) D.T)
    (E := Supported P Space D.support D.support_measurable) g hg G.path
  exact (congrArg (fun p =>
      EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T) (E := CylinderL2 P Space) g hg
      (includePath (K := Icc (0 : ℝ) D.T) (V := Space) P D.support D.support_measurable
        (velocity P D.support D.support_measurable D.T D.T_pos.le
          D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower p I.value)))
    hw.symm).trans
    (normalized_full_velocity_eq P D.support D.support_measurable D.T D.T_pos.le
      D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower g hg
      (EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T)
        (E := Supported P Space D.support D.support_measurable) g hg G.path) I.value)

/-- The time derivative divided by g is the normalized derivative of the normalized forcing. -/
theorem normalized_derivativePath_eq {D : Data U} {raw : VectorField} (G : Forcing P D raw)
    (I : InitialData P D) (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t) :
    EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T) (E := CylinderL2 P Space) g hg
        (includePath (K := Icc (0 : ℝ) D.T) (V := Space) P D.support D.support_measurable
          (G.derivativePath I)) =
      includePath (K := Icc (0 : ℝ) D.T) (V := Space) P D.support D.support_measurable
        (normalizedVelocityDerivative P D.support D.support_measurable D.T D.T_pos.le
          D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
          (EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T)
            (E := Supported P Space D.support D.support_measurable) g hg G.path) I.value g hg) := by
  have hw := weight_normalize (K := Icc (0 : ℝ) D.T)
    (E := Supported P Space D.support D.support_measurable) g hg G.path
  exact (congrArg (fun p =>
      EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T) (E := CylinderL2 P Space) g hg
      (includePath (K := Icc (0 : ℝ) D.T) (V := Space) P D.support D.support_measurable
        (velocityDerivative P D.support D.support_measurable D.T D.T_pos.le
          D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower p I.value)))
    hw.symm).trans
    (normalized_full_velocityDerivative_eq P D.support D.support_measurable D.T D.T_pos.le
      D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
      (EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T)
        (E := Supported P Space D.support D.support_measurable) g hg G.path) I.value g hg)

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
  (hforce : ∀ n, block directions q
    (fun a => pathTranslate (K := Icc (0 : ℝ) D.T) (V := Space) P a
      (EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T) (E := CylinderL2 P Space) g hg
        (includePath (K := Icc (0 : ℝ) D.T) (V := Space) P D.support D.support_measurable
          G.path))) n 0 ≤ Cf * majorant R d n)
  (hinitial : ∀ n, block directions q
    (fun a => translate (V := U) P a (I.value : CylinderL2 P U)) n 0 ≤ A * majorant R d n)

include hdir hΩ hΩo hsub hΩball hg0 hC hA hCf hRc hC₀ hC₁ hRi hbF hbF₁ hRforcing hR hH3 hforce
    hinitial

/-- The literal forward packet velocity divided by g, at the input radius. -/
theorem source_velocity_normalized_bound
    (hRframe : sobolevCoefficientRadius ι Rc ≤ R) (n : ℕ) :
    block directions q (fun a => pathTranslate (K := Icc (0 : ℝ) D.T) (V := Space) P a
      (EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T) (E := CylinderL2 P Space) g hg
        (includePath (K := Icc (0 : ℝ) D.T) (V := Space) P D.support D.support_measurable
          (G.velocityPath I)))) n 0 ≤
        (3*sobolevCoefficientAmplitude ι q Rc C₀)*majorant R (d+1) n := by
  rw [G.normalized_velocityPath_eq I g hg]
  exact physical_forward_block_bound P D.T D.T_pos.le D.support D.support_measurable
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower g hg
    (EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T)
      (E := Supported P Space D.support D.support_measurable) g hg G.path)
    I.value directions hdir q Ω hΩ D.support_compact hΩo hsub hΩball hg0
    (G.normalize_path_orbit g hg) I.orbit C A Cf Rc C₀ C₁ Ri R
    hC hA hCf hRc hC₀ hC₁ hRi
    (fun j => D.frame_spatial_bound j _ (hbF j))
    (fun j => D.frameDerivative_spatial_bound j _ (hbF₁ j))
    hRforcing hRframe hR hH3 d hforce hinitial n

/-- This is A_t/g for the actual raw solution, not a derivative of A/g. -/
theorem source_derivative_normalized_bound (hRone : 1 ≤ R) (n : ℕ) :
    block directions q (fun a => pathTranslate (K := Icc (0 : ℝ) D.T) (V := Space) P a
      (EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T) (E := CylinderL2 P Space) g hg
        (includePath (K := Icc (0 : ℝ) D.T) (V := Space) P D.support D.support_measurable
          (G.derivativePath I)))) n 0 ≤
        physicalCost ι q Ri C₀ C₁ Cf 1*majorant R (d+1) n := by
  rw [G.normalized_derivativePath_eq I g hg]
  exact derivative_forward_block_bound P D.T D.T_pos.le D.support D.support_measurable
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower g hg
    (EulerContinuousTimeWeight.normalize (K := Icc (0 : ℝ) D.T)
      (E := Supported P Space D.support D.support_measurable) g hg G.path)
    I.value directions hdir q Ω hΩ D.support_compact hΩo hsub hΩball hg0
    (G.normalize_path_orbit g hg) I.orbit C A Cf Rc C₀ C₁ Ri R
    hC hA hCf hRc hC₀ hC₁ hRi
    (fun j => D.frame_spatial_bound j _ (hbF j))
    (fun j => D.frameDerivative_spatial_bound j _ (hbF₁ j))
    hRforcing hR hH3 d hforce hinitial hRone n

end EulerTransversePacketProvider.Forcing
