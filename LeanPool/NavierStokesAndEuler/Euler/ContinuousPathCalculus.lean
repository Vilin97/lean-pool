/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Genuine coefficient calculus on continuous path spaces

Pointwise multiplication by an operator-valued continuous path depends
bounded-linearly on that path. Its operator norm, actual parameter
derivatives, and factorial estimates therefore come directly from the
coefficient, with no loss in the coefficient amplitude.
-/

@[expose] public section


noncomputable section

namespace EulerContinuousPathCalculus

open ContinuousLinearMap EulerContinuousTimeIntegral EulerOperatorGevreyCalculus EulerGevrey
open scoped ContDiff

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathCalculus1 : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathCalculus2 : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,E)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathCalculus3 : NormedAddCommGroup C(K,E) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,E)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathCalculus4 : NormedSpace ℝ C(K,E) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,F)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathCalculus5 : NormedAddCommGroup C(K,F) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,F)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathCalculus6 : NormedSpace ℝ C(K,F) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,E →L[ℝ] F)` instance to shorten typeclass
synthesis. -/
local instance instContinuousPathCalculus7 : NormedAddCommGroup C(K,E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathCalculus8 : NormedSpace ℝ C(K,E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,E) →L[ℝ] C(K,F))` instance to shorten typeclass
synthesis. -/
local instance instContinuousPathCalculus9 : NormedAddCommGroup (C(K,E) →L[ℝ] C(K,F)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,E) →L[ℝ] C(K,F))` instance to shorten typeclass
synthesis. -/
local instance instContinuousPathCalculus10 : NormedSpace ℝ (C(K,E) →L[ℝ] C(K,F)) := inferInstance

/-- The actual coefficient-to-continuous-multiplier map is linear. -/
def coefficientLinear : C(K,E →L[ℝ] F) →ₗ[ℝ] (C(K,E) →L[ℝ] C(K,F)) where
  toFun := multiplier
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro p
    apply ContinuousMap.ext
    intro t
    rfl
  map_smul' r A := by
    apply ContinuousLinearMap.ext
    intro p
    apply ContinuousMap.ext
    intro t
    rfl

/-- A bounded linear map in the actual uniform coefficient norm. -/
def coefficientMap : C(K,E →L[ℝ] F) →L[ℝ] (C(K,E) →L[ℝ] C(K,F)) where
  toLinearMap := coefficientLinear
  cont := AddMonoidHomClass.continuous_of_bound (coefficientLinear (K := K) (E := E) (F := F))
    1 (fun A => by
      change ‖multiplier A‖ ≤ (1 : ℝ)*‖A‖
      simpa only [one_mul] using multiplier_norm A)

@[simp] theorem coefficientMap_apply (A : C(K, E →L[ℝ] F)) : coefficientMap A = multiplier A := rfl

/-- Coefficient lifting to continuous paths is a norm contraction. -/
theorem coefficientMap_norm : ‖coefficientMap (K := K) (E := E) (F := F)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  simpa only [coefficientMap_apply, one_mul] using multiplier_norm A

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Genuine parameter regularity of the continuous multiplier. -/
theorem contDiff_multiplier (A : P → C(K, E →L[ℝ] F)) {n : ℕ∞ω} (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (fun x => multiplier (A x)) := by
  change ContDiff ℝ n ((coefficientMap (K := K) (E := E) (F := F)) ∘ A)
  exact ContDiff.comp (g := coefficientMap (K := K) (E := E) (F := F)) (f := A)
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
      (E := C(K,E →L[ℝ] F)) (F := C(K,E) →L[ℝ] C(K,F)) coefficientMap) hA

/-- Actual derivative estimates of the continuous multiplier have no amplitude loss. -/
theorem multiplier_bound (A : P → C(K, E →L[ℝ] F)) (hA : ContDiff ℝ ∞ A)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C * majorant R d n) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => multiplier (A y)) x‖ ≤ C*majorant R d n :=
  contraction_bound (coefficientMap (K := K) (E := E) (F := F)) coefficientMap_norm
    A hA R C hR hC d hb n x

/-- Pointwise application to a continuous path is genuinely smooth. -/
theorem contDiff_apply (A : P → C(K, E →L[ℝ] F)) (f : P → C(K, E))
    {n : ℕ∞ω} (hA : ContDiff ℝ n A) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => multiplier (A x) (f x)) :=
  (contDiff_multiplier A hA).clm_apply hf

/-- The actual pointwise product obeys the fixed factorial product estimate. -/
theorem apply_bound (A : P → C(K, E →L[ℝ] F)) (f : P → C(K, E))
    (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f)
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D) (c d : ℕ)
    (hA_bound : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C * majorant R c n)
    (hf_bound : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ D * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => multiplier (A y) (f y)) x‖ ≤
      (3*C*D)*majorant R (c+d) n :=
  clm_apply_bound (fun y => multiplier (A y)) f (contDiff_multiplier A hA) hf
    R C D hR hC hD c d (multiplier_bound A hA R C hR hC c hA_bound) hf_bound n x

end EulerContinuousPathCalculus
