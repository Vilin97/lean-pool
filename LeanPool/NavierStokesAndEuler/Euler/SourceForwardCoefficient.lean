/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramGevrey
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardCoefficientGevrey
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Operations
import LeanPool.NavierStokesAndEuler.Euler.BoundedInverseGevrey
import LeanPool.NavierStokesAndEuler.Euler.GevreyFixedShift
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldCalculus
import LeanPool.NavierStokesAndEuler.Euler.Foundations.InverseRegularity
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Actual source forward coefficient and its translated factorial bounds

The input consists of the source frame fields and their genuine uniform jets.
The generator itself is constructed by the bounded-field Gram inverse. Its
spatial translation family is identified pointwise and estimated in the actual
uniform time-space norm.
-/

section

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
  compositionMap (α := α) (U := U) (E := E) (F := U)
    (adjointMap (α := α) (U := U) (E := E) Q) Q

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
  pathCompositionMap (α := α) (K := K) (U := U) (E := E) (F := U)
    (pathAdjointMap (α := α) (K := K) (U := U) (E := E) Qp) Qp

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
  pathComposition_contDiff
    (fun a => pathAdjointMap (α := α) (K := K) (U := U) (E := E) (A a)) A
    ((pathAdjointMap (α := α) (K := K) (U := U) (E := E)).contDiff.comp hA) hA

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

end
end

end

section

/-! Actual factorial estimates for the uniformly bounded space-time Gram inverse. -/

@[expose] public section

noncomputable section

namespace EulerBoundedFieldGramInverse

open ContinuousLinearMap EulerBoundedFieldCalculus EulerTransverseGramInverse
  EulerOperatorGevreyCalculus EulerGevrey EulerTimeLpGramGevrey
open scoped BoundedContinuousFunction ContDiff

variable {α K P U E : Type*} [TopologicalSpace α] [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramGevrey1 : NormedAddCommGroup (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramGevrey2 : NormedSpace ℝ (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramGevrey3 : NormedAddCommGroup (E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramGevrey4 : NormedSpace ℝ (E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramGevrey5 : NormedAddCommGroup (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramGevrey6 : NormedSpace ℝ (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramGevrey7 : NormedAddCommGroup (α →ᵇ U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramGevrey8 : NormedSpace ℝ (α →ᵇ U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ E →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramGevrey9 : NormedAddCommGroup (α →ᵇ E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramGevrey10 : NormedSpace ℝ (α →ᵇ E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramGevrey11 : NormedAddCommGroup (α →ᵇ U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramGevrey12 : NormedSpace ℝ (α →ᵇ U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramGevrey13 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramGevrey14 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E)) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ E →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramGevrey15 : NormedAddCommGroup (C(K,α →ᵇ E →L[ℝ] U)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ E →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramGevrey16 : NormedSpace ℝ (C(K,α →ᵇ E →L[ℝ] U)) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramGevrey17 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] U)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramGevrey18 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] U)) := inferInstance

/-- The actual Gram field has the sharp fixed factorial product bound. -/
theorem gramPath_bound (Q : P → C(K, α →ᵇ U →L[ℝ] E)) (hQ : ContDiff ℝ ∞ Q)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C * majorant R 0 n) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => gramPath (Q y)) x‖ ≤ (3*C^2)*majorant R 0 n := by
  have hAdj := (pathAdjointMap (α := α) (K := K) (U := U) (E := E)).contDiff.comp hQ
  have hAdjBound := contraction_bound (pathAdjointMap (α := α) (K := K) (U := U) (E := E))
    pathAdjointMap_norm Q hQ R C hR hC 0 hbQ
  have h := pathComposition_bound
    (fun y => pathAdjointMap (α := α) (K := K) (U := U) (E := E) (Q y)) Q hAdj hQ
    R C C hR hC hC 0 0 hAdjBound hbQ n x
  have he : 3*C*C = 3*C^2 := by ring
  have hfun : (fun y => gramPath (Q y)) = (fun y =>
      pathCompositionMap (α := α) (K := K) (U := U) (E := E) (F := U)
        (pathAdjointMap (α := α) (K := K) (U := U) (E := E) (Q y)) (Q y)) := rfl
  exact (congrArg (fun g : P → C(K,α →ᵇ U →L[ℝ] U) => ‖iteratedFDeriv ℝ n g x‖) hfun).trans_le
    (by simpa only [Nat.add_zero,he] using h)

private theorem cost_bounds (c C : ℝ) (hc : 0 < c) :
    1 ≤ gramCost c C 1 ∧ c⁻¹*(3*C^2) ≤ gramCost c C 1 ∧ c⁻¹ ≤ gramCost c C 1 := by
  have hi : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  unfold gramCost
  constructor
  · have h : 0 ≤ c⁻¹*(3*C^2+1+1) := by positivity
    linarith
  constructor <;> nlinarith [sq_nonneg C]

/-- Cache the standard `NormedAddCommGroup C(K,α →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramGevrey19 : NormedAddCommGroup C(K,α →ᵇ U →L[ℝ] U) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,α →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldGramGevrey20 : NormedSpace ℝ C(K,α →ᵇ U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] U) →L[ℝ] C(K,α →ᵇ U →L[ℝ] U))`
instance to shorten typeclass synthesis. -/
local instance instBoundedFieldGramGevrey21 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] U) →L[ℝ] C(K,α
    →ᵇ U →L[ℝ] U)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] U) →L[ℝ] C(K,α →ᵇ U →L[ℝ] U))` instance
to shorten typeclass synthesis. -/
local instance instBoundedFieldGramGevrey22 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] U) →L[ℝ] C(K,α →ᵇ U
    →L[ℝ] U)) :=
    inferInstance

/-- The genuinely constructed inverse has one factorial shift in the uniform time-space norm. -/
theorem inversePath_gevrey (Q : P → C(K, α →ᵇ U →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (hLower : ∀ y t x v, c * ‖v‖ ^ 2 ≤ ‖Q y t x v‖ ^ 2)
    (hQ : ContDiff ℝ ∞ Q) (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C * majorant Rc 0 n)
    (R : ℝ) (hR : 2 * gramCost c C 1 * (Rc + 1) ≤ R) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => inversePath c hc (Q y) (hLower y)) x‖ ≤ majorant R 1 n := by
  let B := fun y => gramPath (Q y)
  let V := fun y => inversePath c hc (Q y) (hLower y)
  let M := pathCompositionMap (α := α) (K := K) (U := U) (E := U) (F := U)
  let A := fun y => M (B y)
  let I := fun y => M (V y)
  let onePath : C(K,α →ᵇ U →L[ℝ] U) :=
    ⟨fun _ => BoundedContinuousFunction.const α (ContinuousLinearMap.id ℝ U),continuous_const⟩
  have hB : ContDiff ℝ ∞ B := gramPath_contDiff Q hQ
  have hV : ContDiff ℝ ∞ V := inversePath_contDiff c hc Q hLower hQ
  have hA : ContDiff ℝ ∞ A := M.contDiff.comp hB
  have hsolve (y : P) : A y (V y) = onePath := by
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro z
    apply ContinuousLinearMap.ext
    intro v
    exact gram_inverse_apply (Q y t z) c hc (hLower y t z) v
  have hleft (y : P) (p : C(K,α →ᵇ U →L[ℝ] U)) : I y (A y p) = p := by
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro z
    apply ContinuousLinearMap.ext
    intro v
    exact inverse_gram_apply (Q y t z) c hc (hLower y t z) (p t z v)
  have hI (y : P) : ‖I y‖ ≤ c⁻¹ := by
    have h := (M.le_opNorm (V y)).trans
      (mul_le_mul_of_nonneg_right pathCompositionMap_norm (norm_nonneg (V y)))
    exact (h.trans_eq (one_mul _)).trans (inversePath_norm c hc (Q y) (hLower y))
  have hAall := contraction_bound M pathCompositionMap_norm B hB Rc (3*C^2) hRc
    (by positivity) 0 (gramPath_bound Q hQ Rc C hRc hC hbQ)
  have hApos (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ (j+1) A y‖ ≤
      (3*C^2)*(Rc^(j+1)*((j+1).factorial : ℝ)^2) := by
    simpa only [majorant,Nat.add_zero] using hAall (j+1) y
  obtain ⟨hM,hMC,hMD⟩ := cost_bounds c C hc
  have hR0 : 0 ≤ R := by nlinarith
  have hone : ‖onePath‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).2
    intro t
    apply (BoundedContinuousFunction.norm_le zero_le_one).2
    intro z
    exact norm_id_le
  exact EulerBoundedInverseGevrey.solution_gevrey A V (fun _ : P => onePath) hA hV contDiff_const
    hsolve I hleft c⁻¹ (3*C^2) 1 (gramCost c C 1) Rc R (by positivity) zero_le_one hM hMC
    (by simpa only [mul_one] using hMD) hRc hR hI hApos 0
    (const_bound onePath R 1 hR0 hone) n x

/-- A fixed coefficient radius absorbs the one inverse shift once, before recursive solves. -/
theorem inversePath_coefficient_bound (Q : P → C(K, α →ᵇ U →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (hLower : ∀ y t x v, c * ‖v‖ ^ 2 ≤ ‖Q y t x v‖ ^ 2)
    (hQ : ContDiff ℝ ∞ Q) (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C * majorant Rc 0 n)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : 2 * gramCost c C 1 * (Rc + 1) ≤ R) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => inversePath c hc (Q y) (hLower y)) x‖ ≤ R*majorant (4*R) 0 n :=
  (inversePath_gevrey Q c hc hLower hQ Rc C hRc hC hbQ R hR n x).trans
    (majorant_one_le_radius_four R hR0 n)

end EulerBoundedFieldGramInverse

end
end

end

section

/-!
# The actual source forward generator in uniform space-time coefficient norm

The Gram inverse is constructed in the bounded-field Banach algebra. This
produces the literal source coefficient -2(Q*Q)⁻¹Q*Q₁ and the projected-forcing
coefficient (Q*Q)⁻¹Q*. Spatial translation covariance and coefficient estimates
are proved for these actual fields.
-/

@[expose] public section

noncomputable section

namespace EulerBoundedFieldForwardGenerator

open Set ContinuousLinearMap EulerBoundedFieldCalculus EulerBoundedFieldGramInverse
  EulerTransverseGramInverse EulerOperatorGevreyCalculus EulerGevrey EulerTimeLpGramGevrey
  EulerTransverseForwardCoefficientGevrey
open scoped BoundedContinuousFunction ContDiff

variable {α K U E : Type*} [TopologicalSpace α] [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldForwardGenerator1 : NormedAddCommGroup (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldForwardGenerator2 : NormedSpace ℝ (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldForwardGenerator3 : NormedAddCommGroup (E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldForwardGenerator4 : NormedSpace ℝ (E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldForwardGenerator5 : NormedAddCommGroup (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldForwardGenerator6 : NormedSpace ℝ (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldForwardGenerator7 : NormedAddCommGroup (α →ᵇ U →L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldForwardGenerator8 : NormedSpace ℝ (α →ᵇ U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ E →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldForwardGenerator9 : NormedAddCommGroup (α →ᵇ E →L[ℝ] U) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldForwardGenerator10 : NormedSpace ℝ (α →ᵇ E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldForwardGenerator11 : NormedAddCommGroup (α →ᵇ U →L[ℝ] U) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldForwardGenerator12 : NormedSpace ℝ (α →ᵇ U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldForwardGenerator13 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldForwardGenerator14 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ E →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldForwardGenerator15 : NormedAddCommGroup (C(K,α →ᵇ E →L[ℝ] U)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ E →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldForwardGenerator16 : NormedSpace ℝ (C(K,α →ᵇ E →L[ℝ] U)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldForwardGenerator17 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] U)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldForwardGenerator18 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] U)) :=
    inferInstance

/-- Cache the pointwise distributive scalar action on bounded operator paths. -/
local instance instForwardPathDistribSMul : DistribSMul ℝ C(K, α →ᵇ U →L[ℝ] U) :=
  inferInstance

/-- The actual projected-forcing coefficient field. -/
def leftInversePath (c : ℝ) (hc : 0 < c) (Q : C(K, α →ᵇ U →L[ℝ] E))
    (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q t x v‖ ^ 2) : C(K,α →ᵇ E →L[ℝ] U) :=
  pathCompositionMap (α := α) (K := K) (U := E) (E := U) (F := U)
    (inversePath c hc Q hQ) (pathAdjointMap (α := α) (K := K) (U := U) (E := E) Q)

/-- The actual ordinary coefficient in source equation (12). -/
def generatorPath (c : ℝ) (hc : 0 < c) (Q Q₁ : C(K, α →ᵇ U →L[ℝ] E))
    (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q t x v‖ ^ 2) : C(K,α →ᵇ U →L[ℝ] U) :=
  (-2 : ℝ) • pathCompositionMap (α := α) (K := K) (U := U) (E := E) (F := U)
    (leftInversePath c hc Q hQ) Q₁

@[simp] theorem leftInversePath_apply (c : ℝ) (hc : 0 < c) (Q : C(K, α →ᵇ U →L[ℝ] E))
    (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q t x v‖ ^ 2) (t : K) (x : α) :
    leftInversePath c hc Q hQ t x = (gramInverse (Q t x) c hc (hQ t x)).comp (Q t x).adjoint := rfl

@[simp] theorem generatorPath_apply (c : ℝ) (hc : 0 < c) (Q Q₁ : C(K, α →ᵇ U →L[ℝ] E))
    (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q t x v‖ ^ 2) (t : K) (x : α) :
    generatorPath c hc Q Q₁ hQ t x =
      (-2 : ℝ) • (gramInverse (Q t x) c hc (hQ t x)).comp ((Q t x).adjoint.comp (Q₁ t x)) := rfl

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Genuine parameter regularity of the actual projected-forcing coefficient. -/
theorem leftInversePath_contDiff (c : ℝ) (hc : 0 < c) (Q : P → C(K, α →ᵇ U →L[ℝ] E))
    (hQ : ∀ y t x v, c * ‖v‖ ^ 2 ≤ ‖Q y t x v‖ ^ 2) {n : ℕ∞ω} (hQr : ContDiff ℝ n Q) :
    ContDiff ℝ n (fun y => leftInversePath c hc (Q y) (hQ y)) :=
  pathComposition_contDiff _ _ (inversePath_contDiff c hc Q hQ hQr) ((pathAdjointMap (α := α) (K :=
      K) (U := U) (E := E)).contDiff.comp hQr)

/-- Genuine parameter regularity of the actual source generator. -/
theorem generatorPath_contDiff (c : ℝ) (hc : 0 < c) (Q Q₁ : P → C(K, α →ᵇ U →L[ℝ] E))
    (hQ : ∀ y t x v, c * ‖v‖ ^ 2 ≤ ‖Q y t x v‖ ^ 2) {n : ℕ∞ω}
    (hQr : ContDiff ℝ n Q) (hQ₁r : ContDiff ℝ n Q₁) :
    ContDiff ℝ n (fun y => generatorPath c hc (Q y) (Q₁ y) (hQ y)) :=
  (pathComposition_contDiff _ Q₁ (leftInversePath_contDiff c hc Q hQ hQr) hQ₁r).const_smul (-2 : ℝ)

variable (Q Q₁ : P → C(K, α →ᵇ U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ y t x v, c * ‖v‖ ^ 2 ≤ ‖Q y t x v‖ ^ 2)
  (hQr : ContDiff ℝ ∞ Q) (hQ₁r : ContDiff ℝ ∞ Q₁)
  (Rc C₀ C₁ Ri : ℝ) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
  (hRi : 2 * gramCost c C₀ 1 * (Rc + 1) ≤ Ri)
  (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant Rc 0 n)
  (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant Rc 0 n)

include hQr hRc hC₀ hRi hbQ in
/-- The projected-forcing coefficient has a polynomial shift-zero amplitude. -/
theorem leftInversePath_bound (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => leftInversePath c hc (Q y) (hQ y)) x‖ ≤
      (3*Ri*C₀)*majorant (4*Ri) 0 n := by
  obtain ⟨hi,hbase⟩ := inverseRadius_bounds c C₀ Rc Ri hc hRc hRi
  have hrad : 0 ≤ 4*Ri := by positivity
  have hbQ' (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j Q y‖ ≤ C₀*majorant (4*Ri) 0 j :=
    (hbQ j y).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc (4*Ri) hRc hbase 0 j) hC₀)
  have hbAdj := contraction_bound (pathAdjointMap (α := α) (K := K) (U := U) (E := E))
    pathAdjointMap_norm Q hQr (4*Ri) C₀ hrad hC₀ 0 hbQ'
  exact pathComposition_bound (fun y => inversePath c hc (Q y) (hQ y))
    (fun y => pathAdjointMap (α := α) (K := K) (U := U) (E := E) (Q y))
    (inversePath_contDiff c hc Q hQ hQr)
    ((pathAdjointMap (α := α) (K := K) (U := U) (E := E)).contDiff.comp hQr) (4*Ri) Ri C₀ hrad hi
        hC₀ 0 0
    (EulerBoundedFieldGramInverse.inversePath_coefficient_bound Q c hc hQ hQr Rc C₀ hRc hC₀ hbQ Ri
        hi hRi)
    hbAdj n x

include hQr hQ₁r hRc hC₀ hC₁ hRi hbQ hbQ₁ in
/-- The literal generator in (12) satisfies the source's polynomial coefficient bound. -/
theorem generatorPath_bound (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => generatorPath c hc (Q y) (Q₁ y) (hQ y)) x‖ ≤
      (18*Ri*C₀*C₁)*majorant (4*Ri) 0 n := by
  obtain ⟨hi,hbase⟩ := inverseRadius_bounds c C₀ Rc Ri hc hRc hRi
  have hrad : 0 ≤ 4*Ri := by positivity
  have hbQ₁' (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j Q₁ y‖ ≤ C₁*majorant (4*Ri) 0 j :=
    (hbQ₁ j y).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc (4*Ri) hRc hbase 0 j) hC₁)
  let A := fun y => pathCompositionMap (α := α) (K := K) (U := U) (E := E) (F := U)
    (leftInversePath c hc (Q y) (hQ y)) (Q₁ y)
  have hAr : ContDiff ℝ ∞ A := pathComposition_contDiff _ Q₁
    (leftInversePath_contDiff c hc Q hQ hQr) hQ₁r
  have hAb : ‖iteratedFDeriv ℝ n A x‖ ≤ (3*(3*Ri*C₀)*C₁)*majorant (4*Ri) 0 n :=
    pathComposition_bound _ Q₁ (leftInversePath_contDiff c hc Q hQ hQr) hQ₁r
      (4*Ri) (3*Ri*C₀) C₁ hrad (by positivity) hC₁ 0 0
      (leftInversePath_bound Q c hc hQ hQr Rc C₀ Ri hRc hC₀ hRi hbQ) hbQ₁' n x
  change ‖iteratedFDeriv ℝ n (fun y => (-2 : ℝ) • A y) x‖ ≤ _
  simp only [iteratedFDeriv_const_smul_apply' (hAr.contDiffAt.of_le (by simp)), norm_smul]
  norm_num only [norm_neg,Real.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left hAb (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

end EulerBoundedFieldForwardGenerator

end
end

end

@[expose] public section

noncomputable section

namespace EulerSourceForwardCoefficient

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
    EulerBoundedFieldForwardGenerator
  EulerTransverseGramInverse EulerGevrey EulerTimeLpGramGevrey
open scoped BoundedContinuousFunction ContDiff

variable {K U E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (Q Q₁ : SmoothCoefficientPath K (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)

/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instSourceForwardCoefficient1 : NormedAddCommGroup (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instSourceForwardCoefficient2 : NormedSpace ℝ (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instSourceForwardCoefficient3 : NormedAddCommGroup (E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instSourceForwardCoefficient4 : NormedSpace ℝ (E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instSourceForwardCoefficient5 : NormedAddCommGroup (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instSourceForwardCoefficient6 : NormedSpace ℝ (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ U →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instSourceForwardCoefficient7 : NormedAddCommGroup (Space →ᵇ U →L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ U →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instSourceForwardCoefficient8 : NormedSpace ℝ (Space →ᵇ U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ E →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instSourceForwardCoefficient9 : NormedAddCommGroup (Space →ᵇ E →L[ℝ] U) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ E →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instSourceForwardCoefficient10 : NormedSpace ℝ (Space →ᵇ E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instSourceForwardCoefficient11 : NormedAddCommGroup (Space →ᵇ U →L[ℝ] U) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instSourceForwardCoefficient12 : NormedSpace ℝ (Space →ᵇ U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,Space →ᵇ U →L[ℝ] E))` instance to shorten
typeclass synthesis. -/
local instance instSourceForwardCoefficient13 : NormedAddCommGroup (C(K,Space →ᵇ U →L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,Space →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSourceForwardCoefficient14 : NormedSpace ℝ (C(K,Space →ᵇ U →L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,Space →ᵇ E →L[ℝ] U))` instance to shorten
typeclass synthesis. -/
local instance instSourceForwardCoefficient15 : NormedAddCommGroup (C(K,Space →ᵇ E →L[ℝ] U)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,Space →ᵇ E →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instSourceForwardCoefficient16 : NormedSpace ℝ (C(K,Space →ᵇ E →L[ℝ] U)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,Space →ᵇ U →L[ℝ] U))` instance to shorten
typeclass synthesis. -/
local instance instSourceForwardCoefficient17 : NormedAddCommGroup (C(K,Space →ᵇ U →L[ℝ] U)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,Space →ᵇ U →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instSourceForwardCoefficient18 : NormedSpace ℝ (C(K,Space →ᵇ U →L[ℝ] U)) :=
    inferInstance

/-- The actual bounded continuous source generator. -/
def sourceGenerator : C(K,Space →ᵇ U →L[ℝ] U) := generatorPath c hc Q.field Q₁.field hQ

/-- The actual bounded continuous projected-forcing coefficient. -/
def sourceForcing : C(K,Space →ᵇ E →L[ℝ] U) := leftInversePath c hc Q.field hQ

include hQ in
omit [CompleteSpace U] [CompleteSpace E] in
/-- Source lower bounds hold at every translated label. -/
theorem translated_lower (a : Space) (t : K) (x : Space) (v : U) :
    c*‖v‖^2 ≤ ‖translateCoefficientPath Q.field a t x v‖^2 := hQ t (x+a) v

/-- This is an equality of actual fields, not a chosen translated inverse. -/
theorem sourceGenerator_translated (a : Space) :
    generatorPath c hc (translateCoefficientPath Q.field a) (translateCoefficientPath Q₁.field a)
      (translated_lower Q c hQ a) = translateCoefficientPath (sourceGenerator Q Q₁ c hc hQ) a := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rfl

theorem sourceForcing_translated (a : Space) :
    leftInversePath c hc (translateCoefficientPath Q.field a) (translated_lower Q c hQ a) =
      translateCoefficientPath (sourceForcing Q c hc hQ) a := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rfl

/-- The actual generator's translated family is genuinely smooth in the uniform time-space norm. -/
theorem sourceGenerator_translation_contDiff :
    ContDiff ℝ ∞ (translateCoefficientPath (sourceGenerator Q Q₁ c hc hQ)) := by
  have he : translateCoefficientPath (sourceGenerator Q Q₁ c hc hQ) =
      fun a => generatorPath c hc (translateCoefficientPath Q.field a) (translateCoefficientPath
          Q₁.field a)
        (translated_lower Q c hQ a) := funext (fun a => (sourceGenerator_translated Q Q₁ c hc hQ
            a).symm)
  rw [he]
  exact generatorPath_contDiff c hc (translateCoefficientPath Q.field) (translateCoefficientPath
      Q₁.field)
    (translated_lower Q c hQ) Q.translation_contDiff Q₁.translation_contDiff

theorem sourceForcing_translation_contDiff :
    ContDiff ℝ ∞ (translateCoefficientPath (sourceForcing Q c hc hQ)) := by
  have he : translateCoefficientPath (sourceForcing Q c hc hQ) =
      fun a => leftInversePath c hc (translateCoefficientPath Q.field a) (translated_lower Q c hQ
          a) :=
    funext (fun a => (sourceForcing_translated Q c hc hQ a).symm)
  rw [he]
  exact leftInversePath_contDiff c hc (translateCoefficientPath Q.field) (translated_lower Q c hQ)
    Q.translation_contDiff

variable (Rc C₀ C₁ Ri : ℝ) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
  (hRi : 2 * gramCost c C₀ 1 * (Rc + 1) ≤ Ri)
  (hbQ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q.field t : Space → U →L[ℝ] E) x‖ ≤ C₀ * majorant Rc 0 n)
  (hbQ₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q₁.field t : Space → U →L[ℝ] E) x‖ ≤ C₁ * majorant Rc 0 n)

include hRc hC₀ hC₁ hRi hbQ hbQ₁ in
/-- The constructed source generator has a polynomial shift-zero coefficient bound. -/
theorem sourceGenerator_translation_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (sourceGenerator Q Q₁ c hc hQ)) a‖ ≤
      (18*Ri*C₀*C₁)*majorant (4*Ri) 0 n := by
  have he : translateCoefficientPath (sourceGenerator Q Q₁ c hc hQ) =
      fun a => generatorPath c hc (translateCoefficientPath Q.field a) (translateCoefficientPath
          Q₁.field a)
        (translated_lower Q c hQ a) := funext (fun a => (sourceGenerator_translated Q Q₁ c hc hQ
            a).symm)
  rw [he]
  exact generatorPath_bound (translateCoefficientPath Q.field) (translateCoefficientPath Q₁.field)
    c hc (translated_lower Q c hQ) Q.translation_contDiff Q₁.translation_contDiff
    Rc C₀ C₁ Ri hRc hC₀ hC₁ hRi
    (fun j x => Q.norm_iteratedFDeriv_translation_le j _ (mul_nonneg hC₀ (majorant_nonneg Rc hRc 0
        j)) (hbQ j) x)
    (fun j x => Q₁.norm_iteratedFDeriv_translation_le j _ (mul_nonneg hC₁ (majorant_nonneg Rc hRc 0
        j)) (hbQ₁ j) x) n a

include hRc hC₀ hRi hbQ in
/-- The actual projected-forcing coefficient has the corresponding polynomial bound. -/
theorem sourceForcing_translation_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (sourceForcing Q c hc hQ)) a‖ ≤
      (3*Ri*C₀)*majorant (4*Ri) 0 n := by
  have he : translateCoefficientPath (sourceForcing Q c hc hQ) =
      fun a => leftInversePath c hc (translateCoefficientPath Q.field a) (translated_lower Q c hQ
          a) :=
    funext (fun a => (sourceForcing_translated Q c hc hQ a).symm)
  rw [he]
  exact leftInversePath_bound (translateCoefficientPath Q.field) c hc (translated_lower Q c hQ)
    Q.translation_contDiff Rc C₀ Ri hRc hC₀ hRi
    (fun j x => Q.norm_iteratedFDeriv_translation_le j _ (mul_nonneg hC₀ (majorant_nonneg Rc hRc 0
        j)) (hbQ j) x) n a

end EulerSourceForwardCoefficient
