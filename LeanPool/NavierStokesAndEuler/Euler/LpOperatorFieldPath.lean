/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpOperatorField
public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldTimeDerivative
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Tactic.Positivity.Finset

/-!
# Actual rectangular L² frame paths and their time derivatives

The coefficient-to-operator map is a contraction on supported Hilbert spaces.
Continuous coefficient paths and their literal pointwise time derivatives
therefore give genuine operator paths and derivatives. Frame lower bounds,
quadratic upper bounds and pointwise composition identities pass to these
actual L² operators without a support-margin constant.
-/

@[expose] public section


noncomputable section

namespace EulerLpOperatorField

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerLpSupportedSubspace
  EulerVolterraConvolution
open scoped BoundedContinuousFunction

variable {α E F : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] (μ : Measure α) (S : Set α) (hS : MeasurableSet S)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instLpOperatorFieldPath1 : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instLpOperatorFieldPath2 : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ E →L[ℝ] F)` instance to shorten typeclass
synthesis. -/
local instance instLpOperatorFieldPath3 : NormedAddCommGroup (α →ᵇ E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instLpOperatorFieldPath4 : NormedSpace ℝ (α →ᵇ E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedAddCommGroup (supportedSpace (V := E) μ S hS)` instance to shorten
typeclass synthesis. -/
local instance instLpOperatorFieldPath5 : NormedAddCommGroup (supportedSpace (V := E) μ S hS) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (supportedSpace (V := E) μ S hS)` instance to shorten
typeclass synthesis. -/
local instance instLpOperatorFieldPath6 : NormedSpace ℝ (supportedSpace (V := E) μ S hS) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (supportedSpace (V := F) μ S hS)` instance to shorten
typeclass synthesis. -/
local instance instLpOperatorFieldPath7 : NormedAddCommGroup (supportedSpace (V := F) μ S hS) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (supportedSpace (V := F) μ S hS)` instance to shorten
typeclass synthesis. -/
local instance instLpOperatorFieldPath8 : NormedSpace ℝ (supportedSpace (V := F) μ S hS) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace
(V := F) μ S hS)` instance to shorten typeclass synthesis. -/
local instance instLpOperatorFieldPath9 : NormedAddCommGroup
    (supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace (V := F) μ S hS) := inferInstance
/-- Cache the standard `NormedSpace ℝ (supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace (V :=
F) μ S hS)` instance to shorten typeclass synthesis. -/
local instance instLpOperatorFieldPath10 : NormedSpace ℝ
    (supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace (V := F) μ S hS) := inferInstance

/-- Linearity in the actual rectangular coefficient field. -/
theorem supported_add (A B : α →ᵇ E →L[ℝ] F) :
    supported μ S hS (A+B) = supported μ S hS A + supported μ S hS B := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change full μ (A+B) (u : Lp E 2 μ) = full μ A (u : Lp E 2 μ) + full μ B (u : Lp E 2 μ)
  rw [full_add]
  rfl

theorem supported_smul (r : ℝ) (A : α →ᵇ E →L[ℝ] F) :
    supported μ S hS (r • A) = r • supported μ S hS A := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change full μ (r • A) (u : Lp E 2 μ) = r • full μ A (u : Lp E 2 μ)
  rw [full_smul]
  rfl

/-- The literal linear dependence of the supported multiplier on its coefficient. -/
def supportedLinear : (α →ᵇ E →L[ℝ] F) →ₗ[ℝ]
    (supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace (V := F) μ S hS) where
  toFun := supported μ S hS
  map_add' := supported_add μ S hS
  map_smul' := supported_smul μ S hS

/-- The real coefficient-to-L²-operator map on the supported spaces. -/
def supportedMap : (α →ᵇ E →L[ℝ] F) →L[ℝ]
    (supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace (V := F) μ S hS) where
  toLinearMap := supportedLinear μ S hS
  cont := AddMonoidHomClass.continuous_of_bound (supportedLinear μ S hS) 1 (fun A => by
    change ‖supported μ S hS A‖ ≤ 1*‖A‖
    simpa only [one_mul] using
      supported_norm μ S hS A ‖A‖ (norm_nonneg _) (fun x _ => A.norm_coe_le_norm x))

@[simp] theorem supportedMap_apply (A : α →ᵇ E →L[ℝ] F) : supportedMap μ S hS A = supported μ S hS
    A := rfl

theorem supportedMap_norm : ‖supportedMap (E := E) (F := F) μ S hS‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  simpa only [one_mul,supportedMap_apply] using
    supported_norm μ S hS A ‖A‖ (norm_nonneg _) (fun x _ => A.norm_coe_le_norm x)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The actual rectangular coefficient map uniformly along a compact time set. -/
def supportedPathMap : C(K,α →ᵇ E →L[ℝ] F) →L[ℝ]
    C(K,supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace (V := F) μ S hS) :=
  (supportedMap (E := E) (F := F) μ S hS).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem supportedPathMap_apply (A : C(K, α →ᵇ E →L[ℝ] F)) (t : K) :
    supportedPathMap μ S hS A t = supported μ S hS (A t) := rfl

theorem supportedPathMap_norm : ‖supportedPathMap (K := K) (E := E) (F := F) μ S hS‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  exact (supported_norm μ S hS (A t) ‖A t‖ (norm_nonneg _) (fun x _ => (A t).norm_coe_le_norm
      x)).trans
    (A.norm_coe_le_norm t)

omit [CompactSpace K] in
/-- Every-time pointwise lower frame bounds hold on the real L² frame path. -/
theorem supportedPath_lower (A : C(K, α →ᵇ E →L[ℝ] F)) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ t x, x ∈ S → ∀ v, c * ‖v‖ ^ 2 ≤ ‖A t x v‖ ^ 2)
    (t : K) (u : supportedSpace (V := E) μ S hS) :
    c*‖u‖^2 ≤ ‖supportedPathMap μ S hS A t u‖^2 :=
  supported_norm_sq_lower μ S hS (A t) c hc (hA t) u

section Derivative

variable [CompleteSpace F]
  (T : ℝ) (hT : 0 ≤ T) (A A' : C(Icc (0 : ℝ) T, α →ᵇ E →L[ℝ] F))

/-- Literal pointwise coefficient time derivatives give the genuine within-time
operator derivative; no global time extension is assumed. -/
theorem supportedPath_hasDerivWithinAt
    (hpoint : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : α,
      HasDerivWithinAt (fun s => extendPath T hT A s x)
        (extendPath T hT A' t x) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (supportedPathMap μ S hS A))
      (supportedPathMap μ S hS A' t) (Icc (0 : ℝ) T) t := by
  have hfield := EulerBoundedFieldTimeDerivative.hasDerivWithinAt T hT A A' hpoint t t.property
  have hlinear : HasFDerivAt
      (fun B : α →ᵇ E →L[ℝ] F => supportedMap μ S hS B)
      (supportedMap μ S hS) (extendPath T hT A t) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := α →ᵇ E →L[ℝ] F)
      (F := supportedSpace (V := E) μ S hS →L[ℝ] supportedSpace (V := F) μ S hS)
      (supportedMap μ S hS)
  have hd := hlinear.comp_hasDerivWithinAt (t : ℝ) hfield
  change HasDerivWithinAt (fun s => supportedMap μ S hS (A (projIcc 0 T hT s)))
    (supportedMap μ S hS (A' t)) (Icc (0 : ℝ) T) t
  change HasDerivWithinAt (fun s => supportedMap μ S hS (A (projIcc 0 T hT s)))
    (supportedMap μ S hS (A' (projIcc 0 T hT t))) (Icc (0 : ℝ) T) t at hd
  rwa [projIcc_of_mem hT t.property] at hd

end Derivative

/-- A localized Hessian upper bound passes to its genuine supported L² operator. -/
theorem supported_quadratic_upper (A : α →ᵇ E →L[ℝ] E) (C : ℝ)
    (hA : ∀ x ∈ S, ∀ v, ⟪A x v, v⟫_ℝ ≤ C * ‖v‖ ^ 2) (u : supportedSpace (V := E) μ S hS) :
    ⟪supported μ S hS A u,u⟫_ℝ ≤ C*‖u‖^2 := by
  change ⟪full μ A (u : Lp E 2 μ),(u : Lp E 2 μ)⟫_ℝ ≤ C*‖(u : Lp E 2 μ)‖^2
  rw [← real_inner_self_eq_norm_sq,L2.inner_def,L2.inner_def,← integral_const_mul]
  apply integral_mono_ae (L2.integrable_inner (full μ A (u : Lp E 2 μ)) (u : Lp E 2 μ))
    ((L2.integrable_inner (u : Lp E 2 μ) (u : Lp E 2 μ)).const_mul C)
  filter_upwards [full_ae μ A (u : Lp E 2 μ),
    (mem_supportedSpace_ae μ S hS (u : Lp E 2 μ)).1 u.property] with x hx hu
  rw [hx,real_inner_self_eq_norm_sq]
  by_cases hs : x ∈ S
  · exact hA x hs _
  · simp only [hu hs,map_zero,inner_zero_left,norm_zero,zero_pow (by
      decide : 2 ≠ 0),mul_zero,le_refl]

end EulerLpOperatorField
