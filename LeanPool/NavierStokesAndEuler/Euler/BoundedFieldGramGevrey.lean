/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldGramInverse
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramGevrey
import LeanPool.NavierStokesAndEuler.Euler.BoundedInverseGevrey
import LeanPool.NavierStokesAndEuler.Euler.GevreyFixedShift
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp

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
  have h := pathComposition_bound (fun y => pathAdjointMap (Q y)) Q hAdj hQ
    R C C hR hC hC 0 0 hAdjBound hbQ n x
  have he : 3*C*C = 3*C^2 := by ring
  have hfun : (fun y => gramPath (Q y)) = (fun y => pathCompositionMap (pathAdjointMap (Q y)) (Q
      y)) := rfl
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
