/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FixedEvolutionSobolev
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap
import LeanPool.NavierStokesAndEuler.Euler.CylinderActionWords
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletRegularity
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletSobolev

/-!
# Genuine fixed-Sobolev bounds for the cylinder history inverse

The actual mixed translation orbit has identical fixed-base word norms at
every translation. Thus the forcing needs a bound only at zero. Coefficient
jets lift to L² operator paths with constant one, and the true fixed-space
inverse adds one shift while preserving the external radius.
-/

@[expose] public section


noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerTimeLpBoundedMap EulerMeanCoefficients EulerTransverseFixedSobolev
  EulerParameterWordGevrey EulerGevrey EulerFixedEvolutionSobolev
  EulerTimeLpGramSobolev
open scoped BoundedContinuousFunction ContDiff

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

/-- Cache the standard `NormedAddCommGroup (CylinderL2 P U)` instance to shorten typeclass
synthesis. -/
local instance instCylinderDirichletTimeBounds1 : NormedAddCommGroup (CylinderL2 P U) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P U)` instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletTimeBounds2 : NormedSpace ℝ (CylinderL2 P U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P E)` instance to shorten typeclass
synthesis. -/
local instance instCylinderDirichletTimeBounds3 : NormedAddCommGroup (CylinderL2 P E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P E)` instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletTimeBounds4 : NormedSpace ℝ (CylinderL2 P E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P U →L[ℝ] CylinderL2 P E)` instance to
shorten typeclass synthesis. -/
local instance instCylinderDirichletTimeBounds5 : NormedAddCommGroup (CylinderL2 P U →L[ℝ]
    CylinderL2 P E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P U →L[ℝ] CylinderL2 P E)` instance to shorten
typeclass synthesis. -/
local instance instCylinderDirichletTimeBounds6 : NormedSpace ℝ (CylinderL2 P U →L[ℝ] CylinderL2 P
    E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P E →L[ℝ] CylinderL2 P E)` instance to
shorten typeclass synthesis. -/
local instance instCylinderDirichletTimeBounds7 : NormedAddCommGroup (CylinderL2 P E →L[ℝ]
    CylinderL2 P E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P E →L[ℝ] CylinderL2 P E)` instance to shorten
typeclass synthesis. -/
local instance instCylinderDirichletTimeBounds8 : NormedSpace ℝ (CylinderL2 P E →L[ℝ] CylinderL2 P
    E) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletTimeBounds9 : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P U
    →L[ℝ] CylinderL2 P E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletTimeBounds10 : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P U
    →L[ℝ] CylinderL2 P E) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletTimeBounds11 : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P
    E →L[ℝ] CylinderL2 P E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletTimeBounds12 : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P E
    →L[ℝ] CylinderL2 P E) :=
    inferInstance

variable {ι : Type*} [Fintype ι]
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q))
  (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁))
  (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H))
  (Rc C₀ C₁ CH Cf R : ℝ) (hRc : 0 ≤ Rc)
  (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH) (hCf : 0 ≤ Cf)
  (hbQ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q) a‖ ≤ C₀ * majorant Rc 0 n)
  (hbQ₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q₁) a‖ ≤ C₁ * majorant Rc 0 n)
  (hbH : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.H) a‖ ≤ CH * majorant Rc 0 n)
  (hRweak : 2 * blockCost ι q T Rc C₀ C₁ CH D.lower Cf * (sobolevCoefficientRadius ι Rc + 1) ≤ R)
  (hRstrong : 2 * gramBlockCost ι q D.lower Rc C₀
    (accelerationBlockAmplitude ι q Rc C₀ C₁ Cf 1) *
 (sobolevCoefficientRadius ι Rc + 1) ≤ R)

include hdir hQ hQ₁ hH hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hRweak hRstrong

/-- The actual cylinder acceleration in time L², with the same external radius. -/
theorem accelerationLp_block_bound (f : TimeLp T (CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => timeLift T (translate P a).toContinuousLinearMap f))
    (d : ℕ) (hfb : ∀ n, block directions q
      (fun a => timeLift T (translate P a).toContinuousLinearMap f) n 0 ≤ Cf * majorant R d n)
    (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => timeLift T (translate P b).toContinuousLinearMap
      (D.accelerationLp P f)) n a ≤ majorant R (d+2) n := by
  let g : LiftTangent → TimeLp T (CylinderL2 P E) :=
    fun b => timeLift T (translate P b).toContinuousLinearMap f
  change ContDiff ℝ ∞ g at hf
  have he : (fun b : LiftTangent => (D.shifted b.1).accelerationLp P
      (timeLift T (translate P b).toContinuousLinearMap f)) =
      fun b => timeLift T (translate P b).toContinuousLinearMap (D.accelerationLp P f) :=
    funext (fun b => D.accelerationLp_translation P b f)
  rw [← he]
  apply EulerFixedEvolutionSobolev.accelerationLp_block_gevrey directions hdir q T D.time_pos.le
    (fun b : LiftTangent => (D.shifted b.1).frame P)
    (fun b : LiftTangent => (D.shifted b.1).frameDerivative P)
    (fun b : LiftTangent => (D.shifted b.1).hessian P)
    D.lower D.lower_pos (fun b => (D.shifted b.1).frame_lower P)
    (fun b => (D.shifted b.1).frame_derivative P)
    D.potential D.potential_nonneg (fun b => (D.shifted b.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
    (fun k b => D.frameOrbit_bound P hQ k _ (hbQ k) b)
    (fun k b => D.frameDerivativeOrbit_bound P hQ₁ k _ (hbQ₁ k) b)
    (fun k b => D.hessianOrbit_bound P hH k _ (hbH k) b) hRweak hRstrong
    g hf d _ n a
  intro k b
  rw [time_block_constant P directions q T f hf k b]
  exact hfb k

/-- The actual continuous velocity trace from cylinder forcing. -/
theorem continuousVelocity_block_bound (hT1 : T ≤ 1)
    (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f))
    (d : ℕ) (hfb : ∀ n, block directions q (fun a => pathTranslate P a f) n 0 ≤ Cf * majorant R d n)
    (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => pathTranslate P b
      (D.velocityPath P (pathLp T D.time_pos.le f))) n a ≤ traceCost T*majorant R (d+2) n := by
  have he : (fun b : LiftTangent => (D.shifted b.1).velocityPath P
      (pathLp T D.time_pos.le (pathTranslate P b f))) =
      fun b => pathTranslate P b (D.velocityPath P (pathLp T D.time_pos.le f)) := by
    funext b
    apply ContinuousMap.ext
    intro t
    exact D.continuousVelocity_translation P b f t
  rw [← he]
  apply EulerFixedEvolutionSobolev.continuousVelocity_block_gevrey directions hdir q T D.time_pos.le
    (fun b : LiftTangent => (D.shifted b.1).frame P)
    (fun b : LiftTangent => (D.shifted b.1).frameDerivative P)
    (fun b : LiftTangent => (D.shifted b.1).hessian P)
    D.lower D.lower_pos (fun b => (D.shifted b.1).frame_lower P)
    (fun b => (D.shifted b.1).frame_derivative P)
    D.potential D.potential_nonneg (fun b => (D.shifted b.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
    (fun k b => D.frameOrbit_bound P hQ k _ (hbQ k) b)
    (fun k b => D.frameDerivativeOrbit_bound P hQ₁ k _ (hbQ₁ k) b)
    (fun k b => D.hessianOrbit_bound P hH k _ (hbH k) b) hRweak hRstrong D.time_pos hT1
    (fun b => pathTranslate P b f) hf d _ n a
  intro k b
  rw [path_block_constant P directions q f hf k b]
  exact hfb k

/-- Time-uniform acceleration of the actual history solution, including both endpoints. -/
theorem accelerationPath_block_bound (hT1 : T ≤ 1)
    (hRuniform : 2 * gramBlockCost ι q D.lower Rc C₀
      (accelerationBlockAmplitude ι q Rc C₀ C₁ Cf (traceCost T)) *
 (sobolevCoefficientRadius ι Rc + 1)
          ≤ R)
    (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f))
    (d : ℕ) (hfb : ∀ n, block directions q (fun a => pathTranslate P a f) n 0 ≤ Cf * majorant R d n)
    (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => pathTranslate P b (D.accelerationPath P f)) n a ≤
      majorant R (d+3) n := by
  have he : (fun b : LiftTangent => (D.shifted b.1).accelerationPath P (pathTranslate P b f)) =
      fun b => pathTranslate P b (D.accelerationPath P f) := by
    funext b
    apply ContinuousMap.ext
    intro t
    exact D.accelerationPath_translation P b f t
  rw [← he]
  apply EulerFixedEvolutionSobolev.classicalAcceleration_block_gevrey directions hdir q T
      D.time_pos.le
    (fun b : LiftTangent => (D.shifted b.1).frame P)
    (fun b : LiftTangent => (D.shifted b.1).frameDerivative P)
    (fun b : LiftTangent => (D.shifted b.1).hessian P)
    D.lower D.lower_pos (fun b => (D.shifted b.1).frame_lower P)
    (fun b => (D.shifted b.1).frame_derivative P)
    D.potential D.potential_nonneg (fun b => (D.shifted b.1).hessian_upper P) D.small
    (D.frameOrbit_contDiff P hQ) (D.frameDerivativeOrbit_contDiff P hQ₁) (D.hessianOrbit_contDiff P
        hH)
    Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
    (fun k b => D.frameOrbit_bound P hQ k _ (hbQ k) b)
    (fun k b => D.frameDerivativeOrbit_bound P hQ₁ k _ (hbQ₁ k) b)
    (fun k b => D.hessianOrbit_bound P hH k _ (hbH k) b) hRweak hRstrong D.time_pos hT1 hRuniform
    (fun b => pathTranslate P b f) hf d _ n a
  intro k b
  rw [path_block_constant P directions q f hf k b]
  exact hfb k

end EulerCylinderDirichlet.Coefficients
