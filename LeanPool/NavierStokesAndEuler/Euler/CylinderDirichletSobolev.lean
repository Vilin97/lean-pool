/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletRegularity
public import LeanPool.NavierStokesAndEuler.Euler.CylinderActionWords
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderPathBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedSobolev

@[expose] public section

/-!
# Genuine fixed-Sobolev bounds for the cylinder history inverse

The actual mixed translation orbit has identical fixed-base word norms at
every translation. Thus the forcing needs a bound only at zero. Coefficient
jets lift to L² operator paths with constant one, and the true fixed-space
inverse adds one shift while preserving the external radius.
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerTimeLpBoundedMap EulerMeanCoefficients EulerTransverseFixedSobolev
  EulerParameterWordGevrey EulerGevrey
open scoped BoundedContinuousFunction ContDiff

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

private local instance : NormedAddCommGroup (CylinderL2 P U) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P U) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E) :=
  inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E) :=
  inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E) :=
  inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E) :=
  inferInstance

omit [CompleteSpace U] [CompleteSpace E] in
theorem frameOrbit_bound (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q)) (n : ℕ) (C : ℝ)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q) a‖ ≤ C) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => (D.shifted b.1).frame P) a‖ ≤ C :=
  mixedOperatorPath_bound P D.Q hQ n C hb a

omit [CompleteSpace U] [CompleteSpace E] in
theorem frameDerivativeOrbit_bound (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁)) (n : ℕ) (C
  : ℝ)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q₁) a‖ ≤ C) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => (D.shifted b.1).frameDerivative P) a‖ ≤ C :=
  mixedOperatorPath_bound P D.Q₁ hQ₁ n C hb a

omit [CompleteSpace U] [CompleteSpace E] in
theorem hessianOrbit_bound (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H)) (n : ℕ) (C : ℝ)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.H) a‖ ≤ C) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => (D.shifted b.1).hessian P) a‖ ≤ C :=
  mixedOperatorPath_bound P D.H hH n C hb a

variable {ι : Type*} [Fintype ι]
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q))
  (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁))
  (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H))
  (Rc C₀ C₁ CH Cf R : ℝ) (hRc : 0 ≤ Rc)
  (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH) (hCf : 0 ≤ Cf)
  (hbQ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q) a‖ ≤ C₀*majorant Rc 0 n)
  (hbQ₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q₁) a‖ ≤ C₁*majorant Rc 0 n)
  (hbH : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.H) a‖ ≤ CH*majorant Rc 0 n)
  (hR : 2*blockCost ι q T Rc C₀ C₁ CH D.lower Cf*(sobolevCoefficientRadius ι Rc+1) ≤ R)

include hdir hQ hQ₁ hH hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hR

/-- Actual cylinder/time L² coordinate velocity: one shift at the original
radius and fixed Sobolev order, from forcing bounds at the base translation. -/
theorem velocityLp_block_bound (f : TimeLp T (CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => timeLift T (translate P a).toContinuousLinearMap f))
    (d : ℕ) (hfb : ∀ n, block directions q
      (fun a => timeLift T (translate P a).toContinuousLinearMap f) n 0 ≤ Cf*majorant R d n)
    (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => timeLift T (translate P b).toContinuousLinearMap (D.velocityLp P
      f)) n a ≤
      majorant R (d+1) n := by
  let g : LiftTangent → TimeLp T (CylinderL2 P E) :=
    fun b => timeLift T (translate P b).toContinuousLinearMap f
  change ContDiff ℝ ∞ g at hf
  have he : (fun b : LiftTangent => (D.shifted b.1).velocityLp P
      (timeLift T (translate P b).toContinuousLinearMap f)) =
      fun b => timeLift T (translate P b).toContinuousLinearMap (D.velocityLp P f) :=
    funext (fun b => D.velocityLp_translation P b f)
  rw [← he]
  apply EulerTransverseFixedSobolev.velocityLp_block_gevrey directions hdir q T D.time_pos.le
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
    (fun k b => D.hessianOrbit_bound P hH k _ (hbH k) b) hR
    g hf d _ n a
  intro k b
  rw [time_block_constant P directions q T f hf k b]
  exact hfb k

/-- For source intervals of length at most one, continuous forcing embeds
with no extra amplitude, and the same history estimate applies. -/
theorem continuous_velocityLp_block_bound (hT1 : T ≤ 1)
    (f : C(Icc (0 : ℝ) T,CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f))
    (d : ℕ) (hfb : ∀ n, block directions q (fun a => pathTranslate P a f) n 0 ≤ Cf*majorant R d n)
    (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => timeLift T (translate P b).toContinuousLinearMap
      (D.velocityLp P (pathLp T D.time_pos.le f))) n a ≤ majorant R (d+1) n := by
  have hsqrt : Real.sqrt T ≤ 1 := by simpa using Real.sqrt_le_sqrt hT1
  apply D.velocityLp_block_bound P directions hdir q hQ hQ₁ hH Rc C₀ C₁ CH Cf R hRc
    hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hR (pathLp T D.time_pos.le f)
    (pathLp_orbit_contDiff P T D.time_pos.le f hf) d _ n a
  intro k
  exact (pathLp_block_le P directions q T D.time_pos.le f hf k 0).trans
    ((mul_le_mul_of_nonneg_right hsqrt (block_nonneg directions q _ k 0)).trans
      (by simpa only [one_mul] using hfb k))

end EulerCylinderDirichlet.Coefficients
