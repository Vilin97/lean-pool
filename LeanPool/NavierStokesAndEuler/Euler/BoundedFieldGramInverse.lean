/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldCalculus
import LeanPool.NavierStokesAndEuler.Euler.Foundations.InverseRegularity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The constructed inverse Gram field in the uniform space-time norm

Uniform lower bounds for the pointwise frame construct a bounded continuous
inverse field. It forms an actual unit of the bounded-field Banach algebra.
The resulting time path and its parameter regularity are therefore proved in
the uniform spatial norm, not merely at each fixed spatial label.
-/

@[expose] public section


noncomputable section

namespace EulerBoundedFieldGramInverse

open ContinuousLinearMap EulerBoundedFieldCalculus EulerTransverseGramInverse
  EulerCoerciveProjection EulerInverseRegularity
open scoped BoundedContinuousFunction ContDiff

variable {α U E : Type*} [TopologicalSpace α]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramInverse1 : NormedAddCommGroup (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramInverse2 : NormedSpace ℝ (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramInverse3 : NormedAddCommGroup (E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramInverse4 : NormedSpace ℝ (E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramInverse5 : NormedAddCommGroup (α →ᵇ U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramInverse6 : NormedSpace ℝ (α →ᵇ U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ E →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramInverse7 : NormedAddCommGroup (α →ᵇ E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramInverse8 : NormedSpace ℝ (α →ᵇ E →L[ℝ] U) := inferInstance

/-- Cache the standard `NormedRing (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramInverse9 : NormedRing (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAlgebra ℝ (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramInverse10 : NormedAlgebra ℝ (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedRing (α →ᵇ U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramInverse11 : NormedRing (α →ᵇ U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAlgebra ℝ (α →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramInverse12 : NormedAlgebra ℝ (α →ᵇ U →L[ℝ] U) := inferInstance

/-- The literal positive Gram coefficient field. -/
def gramField (Q : α →ᵇ U →L[ℝ] E) : α →ᵇ U →L[ℝ] U :=
  compositionMap (adjointMap Q) Q

@[simp] theorem gramField_apply (Q : α →ᵇ U →L[ℝ] E) (x : α) : gramField Q x = gram (Q x) := rfl

variable (Q : α →ᵇ U →L[ℝ] E) (c : ℝ) (hc : 0 < c)
  (hQ : ∀ x v, c * ‖v‖ ^ 2 ≤ ‖Q x v‖ ^ 2)

/-- Continuity of the actual pointwise coercive inverse. -/
theorem inverseField_continuous : Continuous (fun x => gramInverse (Q x) c hc (hQ x)) := by
  have heq : (fun x => gramInverse (Q x) c hc (hQ x)) = fun x => Ring.inverse (gram (Q x)) := by
    funext x
    exact coerciveInverse_eq_ringInverse (gram (Q x)) c hc (gram_coercive (Q x) c (hQ x))
  rw [heq,continuous_iff_continuousAt]
  intro x
  let e := coerciveEquiv (gram (Q x)) c hc (gram_coercive (Q x) c (hQ x))
  have he : (e.toUnit : U →L[ℝ] U) = gram (Q x) := by
    ext v
    exact coerciveEquiv_apply (gram (Q x)) c hc (gram_coercive (Q x) c (hQ x)) v
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) e.toUnit).continuousAt
  rw [he] at hi
  exact hi.comp (x := x) (gramField Q).continuous.continuousAt

/-- The genuine bounded continuous inverse field, with coercive norm c⁻¹. -/
def inverseField : α →ᵇ U →L[ℝ] U :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => gramInverse (Q x) c hc (hQ x))
    (inverseField_continuous Q c hc hQ) c⁻¹ (fun x => gramInverse_norm (Q x) c hc (hQ x))

@[simp] theorem inverseField_apply (x : α) : inverseField Q c hc hQ x = gramInverse (Q x) c hc (hQ
    x) := rfl

theorem inverseField_norm : ‖inverseField Q c hc hQ‖ ≤ c⁻¹ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (inv_nonneg.mpr hc.le) _

/-- This actual inverse forms a unit in the bounded-field algebra. -/
def gramFieldUnit : (α →ᵇ U →L[ℝ] U)ˣ where
  val := gramField Q
  inv := inverseField Q c hc hQ
  val_inv := by
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    exact gram_inverse_apply (Q x) c hc (hQ x) v
  inv_val := by
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    exact inverse_gram_apply (Q x) c hc (hQ x) v

/-- Actual pointwise inversion equals the Banach-algebra inverse. -/
theorem inverseField_eq_ringInverse : inverseField Q c hc hQ = Ring.inverse (gramField Q) :=
  (Ring.inverse_unit (M₀ := α →ᵇ U →L[ℝ] U) (gramFieldUnit Q c hc hQ)).symm

section Paths

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramInverse13 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramInverse14 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E)) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramInverse15 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] U)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramInverse16 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] U)) := inferInstance

/-- The Gram field as an actual uniform time path. -/
def gramPath (Qp : C(K, α →ᵇ U →L[ℝ] E)) : C(K,α →ᵇ U →L[ℝ] U) :=
  pathCompositionMap (pathAdjointMap Qp) Qp

@[simp] theorem gramPath_apply (Qp : C(K, α →ᵇ U →L[ℝ] E)) (t : K) : gramPath Qp t = gramField (Qp
    t) := rfl

/-- The constructed inverse is continuous in the spatial uniform norm as time varies. -/
def inversePath (Qp : C(K, α →ᵇ U →L[ℝ] E))
    (hLower : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Qp t x v‖ ^ 2) : C(K,α →ᵇ U →L[ℝ] U) where
  toFun t := inverseField (Qp t) c hc (hLower t)
  continuous_toFun := by
    have heq : (fun t => inverseField (Qp t) c hc (hLower t)) = fun t => Ring.inverse (gramField
        (Qp t)) :=
      funext (fun t => inverseField_eq_ringInverse (Qp t) c hc (hLower t))
    rw [heq,continuous_iff_continuousAt]
    intro t
    exact ((hasFDerivAt_ringInverse (𝕜 := ℝ) (gramFieldUnit (Qp t) c hc (hLower
        t))).continuousAt).comp
      (x := t) (gramPath Qp).continuous.continuousAt

@[simp] theorem inversePath_apply (Qp : C(K, α →ᵇ U →L[ℝ] E))
    (hLower : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Qp t x v‖ ^ 2) (t : K) (x : α) :
    inversePath c hc Qp hLower t x = gramInverse (Qp t x) c hc (hLower t x) := rfl

/-- The uniform time-space inverse bound is the same coercive bound. -/
theorem inversePath_norm (Qp : C(K, α →ᵇ U →L[ℝ] E))
    (hLower : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Qp t x v‖ ^ 2) : ‖inversePath c hc Qp hLower‖ ≤ c⁻¹ := by
  apply (ContinuousMap.norm_le _ (inv_nonneg.mpr hc.le)).2
  intro t
  exact inverseField_norm (Qp t) c hc (hLower t)

/-- The pathwise Gram field is an actual unit of the full time-space Banach algebra. -/
def gramPathUnit (Qp : C(K, α →ᵇ U →L[ℝ] E))
    (hLower : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Qp t x v‖ ^ 2) : C(K,α →ᵇ U →L[ℝ] U)ˣ where
  val := gramPath Qp
  inv := inversePath c hc Qp hLower
  val_inv := by
    apply ContinuousMap.ext
    intro t
    exact (gramFieldUnit (Qp t) c hc (hLower t)).val_inv
  inv_val := by
    apply ContinuousMap.ext
    intro t
    exact (gramFieldUnit (Qp t) c hc (hLower t)).inv_val

/-- The actual inverse path is the algebra inverse in the uniform time-space norm. -/
theorem inversePath_eq_ringInverse (Qp : C(K, α →ᵇ U →L[ℝ] E))
    (hLower : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Qp t x v‖ ^ 2) :
    inversePath c hc Qp hLower = Ring.inverse (gramPath Qp) :=
  (Ring.inverse_unit (M₀ := C(K,α →ᵇ U →L[ℝ] U)) (gramPathUnit c hc Qp hLower)).symm

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Smoothness of the actual uniform Gram coefficient path. -/
theorem gramPath_contDiff (A : P → C(K, α →ᵇ U →L[ℝ] E)) {n : ℕ∞ω} (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (fun a => gramPath (A a)) :=
  pathComposition_contDiff (fun a => pathAdjointMap (A a)) A ((pathAdjointMap (α := α) (K := K) (U
      := U) (E := E)).contDiff.comp hA) hA

/-- Smoothness of the constructed inverse in the uniform time-space norm. -/
theorem inversePath_contDiff (A : P → C(K, α →ᵇ U →L[ℝ] E))
    (hLower : ∀ a t x v, c * ‖v‖ ^ 2 ≤ ‖A a t x v‖ ^ 2) {n : ℕ∞ω} (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (fun a => inversePath c hc (A a) (hLower a)) := by
  have heq : (fun a => inversePath c hc (A a) (hLower a)) = Ring.inverse ∘ (fun a => gramPath (A
      a)) :=
    funext (fun a => inversePath_eq_ringInverse c hc (A a) (hLower a))
  rw [heq,contDiff_iff_contDiffAt]
  intro a
  exact (contDiffAt_ringInverse ℝ (R := C(K,α →ᵇ U →L[ℝ] U))
    (gramPathUnit c hc (A a) (hLower a))).comp a (gramPath_contDiff A hA).contDiffAt

end Paths

end EulerBoundedFieldGramInverse
