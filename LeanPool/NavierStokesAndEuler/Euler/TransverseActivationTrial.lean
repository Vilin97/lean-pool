/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MovingNormalProjection
public import LeanPool.NavierStokesAndEuler.Euler.TerminalProjectionTrial
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointEnergy

/-!
The explicit activation trial and its endpoint-energy bound.  The trial uses
the actual moving normal, not a deformation-frame condition number.  A layer
of width `1/h` gives `‖Λ‖ ≤ (4 + 64 CM² + 2 CH) h` under the source's low
history bounds.
-/

@[expose] public section


noncomputable section


namespace EulerTransverseActivationTrial

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerInitialTimePrimitive EulerVolterraConvolution
  EulerTerminalProjectionTrial EulerTerminalLayerRamp
  EulerMovingNormalProjection EulerTransverseEndpointEnergy

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial1 : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial2 : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
/-- Cache the standard `AddCommGroup (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial3 : AddCommGroup (E →L[ℝ] E) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E)).toAddCommGroup
/-- Cache the standard `Module ℝ (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial4 : Module ℝ (E →L[ℝ] E) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E)).toModule
/-- Cache the standard `TopologicalSpace (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial5 : TopologicalSpace (E →L[ℝ] E) :=
  (inferInstance : PseudoMetricSpace (E →L[ℝ] E)).toUniformSpace.toTopologicalSpace
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial6 : NormedAddCommGroup (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial7 : NormedSpace ℝ (U →L[ℝ] E) := inferInstance
/-- Cache the standard `AddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial8 : AddCommGroup (U →L[ℝ] E) :=
  (inferInstance : NormedAddCommGroup (U →L[ℝ] E)).toAddCommGroup
/-- Cache the standard `Module ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial9 : Module ℝ (U →L[ℝ] E) :=
  (inferInstance : NormedSpace ℝ (U →L[ℝ] E)).toModule
/-- Cache the standard `TopologicalSpace (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial10 : TopologicalSpace (U →L[ℝ] E) :=
  (inferInstance : PseudoMetricSpace (U →L[ℝ] E)).toUniformSpace.toTopologicalSpace

variable (T : ℝ) (hT : 0 ≤ T) (m m₁ : C(Icc (0 : ℝ) T, E))
  (hne : ∀ t, m t ≠ 0) (R : U →L[ℝ] E)

/-- Projection path, given by `⟨fun t => (normalProjection (m t)).comp R,
(normalProjection_continuous m.continuous hne).clm_comp continuous_const⟩`. -/
def projectionPath : C(Icc (0 : ℝ) T, U →L[ℝ] E) :=
  ⟨fun t => (normalProjection (m t)).comp R,
    (normalProjection_continuous m.continuous hne).clm_comp continuous_const⟩

/-- Projection derivative path as an element of `C(Icc (0 : ℝ) T, U →L[ℝ] E)`. -/
def projectionDerivativePath : C(Icc (0 : ℝ) T, U →L[ℝ] E) :=
  ⟨fun t => (normalProjectionDerivative (m t) (m₁ t)).comp R,
    (normalProjectionDerivative_continuous m.continuous m₁.continuous hne).clm_comp
        continuous_const⟩

variable (hd : ∀ t : Icc (0 : ℝ) T,
  HasDerivWithinAt (extendPath T hT m) (m₁ t) (Icc (0 : ℝ) T) t)

include hd in
theorem projectionPath_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (projectionPath T m hne R))
      (projectionDerivativePath T m m₁ hne R t) (Icc (0 : ℝ) T) t := by
  have hm : extendPath T hT m t ≠ 0 := by
    simpa only [extendPath, projIcc_of_mem hT t.property] using hne t
  have hp := normalProjection_hasDerivWithinAt (hd t) hm
  have hc := hp.clm_comp (hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) R)
  convert! hc using 1
  simp only [projectionDerivativePath, ContinuousMap.coe_mk,
    extendPath, projIcc_of_mem hT t.property, comp_zero, add_zero]

theorem projectionPath_norm_le (hR : ‖R‖ ≤ 1) (t : Icc (0 : ℝ) T) :
    ‖projectionPath T m hne R t‖ ≤ 1 := by
  calc
    ‖projectionPath T m hne R t‖ ≤ ‖normalProjection (m t)‖ * ‖R‖ := opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (normalProjection_norm_le (m t) (hne t)) hR
      (norm_nonneg R) (by norm_num)
    _ = 1 := one_mul 1

variable [CompleteSpace E]

theorem projectionDerivativePath_norm_le (hR : ‖R‖ ≤ 1)
    (M : Icc (0 : ℝ) T → E →L[ℝ] E)
    (hRay : ∀ t, m₁ t = -(M t).adjoint (m t))
    (B : ℝ) (_hB : 0 ≤ B) (hM : ∀ t, ‖M t‖ ≤ B) (t : Icc (0 : ℝ) T) :
    ‖projectionDerivativePath T m m₁ hne R t‖ ≤ 4 * B := by
  calc
    ‖projectionDerivativePath T m m₁ hne R t‖ ≤
        ‖normalProjectionDerivative (m t) (m₁ t)‖ * ‖R‖ := opNorm_comp_le _ _
    _ ≤ (4 * ‖M t‖) * 1 := by
      apply mul_le_mul _ hR (norm_nonneg R) (by positivity)
      rw [hRay]
      exact normalProjectionDerivative_ray_bound (m t) (hne t) (M t)
    _ ≤ 4 * B := by nlinarith only [hM t]

/-- The actual derivative of the explicit terminal-layer displacement. -/
def activationTrial (h : ℝ) : U →L[ℝ] TimeLp T E :=
  trialDerivative T hT h (projectionPath T m hne R) (projectionDerivativePath T m m₁ hne R)

include hd in
theorem activationTrial_primitive (h : ℝ) (Y : U) (t : Icc (0 : ℝ) T) :
    initialPrimitive T hT (activationTrial T hT m m₁ hne R h Y) t =
      ramp T h t • normalProjection (m t) (R Y) :=
  initialPrimitive_trialDerivative T hT h (projectionPath T m hne R)
    (projectionDerivativePath T m m₁ hne R)
    (projectionPath_hasDerivWithinAt T hT m m₁ hne R hd) Y t

include hd in
theorem activationTrial_tangent (h : ℝ) (Y : U) (t : Icc (0 : ℝ) T) :
    ⟪m t, initialPrimitive T hT (activationTrial T hT m m₁ hne R h Y) t⟫_ℝ = 0 := by
  rw [activationTrial_primitive T hT m m₁ hne R hd, real_inner_smul_right,
    normalProjection_tangent (m t) (hne t), mul_zero]

include hd in
theorem activationTrial_terminal (h : ℝ) (hLayer : 1 ≤ h * T)
    (hR : ∀ Y, ⟪m ⟨T, hT, le_rfl⟩, R Y⟫_ℝ = 0) (Y : U) :
    initialPrimitive T hT (activationTrial T hT m m₁ hne R h Y) ⟨T, hT, le_rfl⟩ = R Y := by
  rw [activationTrial_primitive T hT m m₁ hne R hd, ramp_terminal hLayer,
    one_smul, normalProjection_fixed _ _ (hR Y)]

omit [CompleteSpace E] in
theorem potential_abs_bound (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (u : TimeLp T E) :
    |⟪timeMultiplier T hT H u, u⟫_ℝ| ≤ ‖H‖ * ‖u‖ ^ 2 := by
  calc
    |⟪timeMultiplier T hT H u, u⟫_ℝ| ≤ ‖timeMultiplier T hT H u‖ * ‖u‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖H‖ * ‖u‖) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (timeApply_bound T hT H u) (norm_nonneg u)
    _ = _ := by ring

variable [CompleteSpace U]

include hd in
/-- All input bounds concern the parent coefficients and the actual ray.  The
endpoint operator and its `O(h)` norm are constructed conclusions. -/
theorem activation_endpoint_norm
    (h : ℝ) (hh : 0 < h) (hLayer : 1 ≤ h * T)
    (hR : ‖R‖ ≤ 1) (CM CH : ℝ) (hCM : 0 ≤ CM) (hCH : 0 ≤ CH)
    (M : Icc (0 : ℝ) T → E →L[ℝ] E)
    (hRay : ∀ t, m₁ t = -(M t).adjoint (m t)) (hM : ∀ t, ‖M t‖ ≤ CM * h)
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (hHs : ∀ t, (H t).IsSymmetric)
    (hHnorm : ‖H‖ ≤ CH * h ^ 2)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
    (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2) :
    ‖dirichletToNeumann T hT (fun t => m t) H K hK hH hsmall
      (activationTrial T hT m m₁ hne R h)‖ ≤ (4 + 64 * CM ^ 2 + 2 * CH) * h := by
  apply dirichletToNeumann_norm_le T hT (fun t => m t) H K hK hH hsmall hHs
    (activationTrial T hT m m₁ hne R h) ((4 + 64 * CM ^ 2 + 2 * CH) * h) (by positivity)
  intro Y
  have hproj := projectionPath_norm_le T m hne R hR
  have hproj₁ := projectionDerivativePath_norm_le T m m₁ hne R hR M hRay
    (CM * h) (by positivity) hM
  have hD := trialDerivative_norm_sq_le T hT h (projectionPath T m hne R)
    (projectionDerivativePath T m m₁ hne R) hh hLayer
    (4 * (CM * h)) (by positivity) hproj hproj₁ Y
  have hη := trialDisplacement_norm_sq_le T hT h (projectionPath T m hne R)
    (projectionDerivativePath T m m₁ hne R)
    (projectionPath_hasDerivWithinAt T hT m m₁ hne R hd) hh hLayer hproj Y
  change ‖activationTrial T hT m m₁ hne R h Y‖ ^ 2 ≤
    (4 * h + 4 * (4 * (CM * h)) ^ 2 / h) * ‖Y‖ ^ 2 at hD
  change ‖initialPrimitiveTimeLp T hT (activationTrial T hT m m₁ hne R h Y)‖ ^ 2 ≤
    (2 / h) * ‖Y‖ ^ 2 at hη
  let u := activationTrial T hT m m₁ hne R h Y
  let η := initialPrimitiveTimeLp T hT u
  have hp : -⟪timeMultiplier T hT H η, η⟫_ℝ ≤ CH * h ^ 2 * ‖η‖ ^ 2 := by
    exact (neg_le_abs _).trans ((potential_abs_bound T hT H η).trans
      (mul_le_mul_of_nonneg_right hHnorm (sq_nonneg _)))
  change ‖u‖ ^ 2 - ⟪timeMultiplier T hT H η, η⟫_ℝ ≤ _
  calc
    ‖u‖ ^ 2 - ⟪timeMultiplier T hT H η, η⟫_ℝ ≤ ‖u‖ ^ 2 + CH * h ^ 2 * ‖η‖ ^ 2 := by
        linarith only [hp]
    _ ≤ (4 * h + 4 * (4 * (CM * h)) ^ 2 / h) * ‖Y‖ ^ 2 +
        CH * h ^ 2 * ((2 / h) * ‖Y‖ ^ 2) :=
      add_le_add hD (mul_le_mul_of_nonneg_left hη (by positivity))
    _ = (4 + 64 * CM ^ 2 + 2 * CH) * h * ‖Y‖ ^ 2 := by field_simp; ring

end EulerTransverseActivationTrial
