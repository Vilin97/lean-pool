/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-! A continuous multilinear operation acts on genuine bounded fields in
the uniform norm. This includes the finite Faà di Bruno operations. -/

@[expose] public section


noncomputable section


open scoped BigOperators BoundedContinuousFunction

namespace EulerBoundedFieldCalculus

variable {α ι : Type*} [TopologicalSpace α] [Fintype ι]
  {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Cache the standard `NormedAddCommGroup (α →ᵇ V i)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldMultilinear1 (i : ι) : NormedAddCommGroup (α →ᵇ V i) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ V i)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldMultilinear2 (i : ι) : NormedSpace ℝ (α →ᵇ V i) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ W)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldMultilinear3 : NormedAddCommGroup (α →ᵇ W) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ W)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldMultilinear4 : NormedSpace ℝ (α →ᵇ W) := inferInstance

/-- Multilinear value, constructed using `BoundedContinuousFunction.ofNormedAddCommGroup`. -/
def multilinearValue (L : ContinuousMultilinearMap ℝ V W)
    (f : ∀ i, α →ᵇ V i) : α →ᵇ W :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => L (fun i => f i x))
    (L.cont.comp (continuous_pi (fun i => (f i).continuous)))
    (‖L‖ * ∏ i, ‖f i‖) (fun x => (L.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun i _ => (f i).norm_coe_le_norm x)) (norm_nonneg L)))

@[simp] theorem multilinearValue_apply (L : ContinuousMultilinearMap ℝ V W)
    (f : ∀ i, α →ᵇ V i) (x : α) :
    multilinearValue L f x = L (fun i => f i x) := rfl

theorem multilinearValue_norm (L : ContinuousMultilinearMap ℝ V W)
    (f : ∀ i, α →ᵇ V i) :
    ‖multilinearValue L f‖ ≤ ‖L‖ * ∏ i, ‖f i‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))) _

/-- Multilinear algebra as an element of `MultilinearMap ℝ (fun i => α →ᵇ V i) (α →ᵇ W)`. -/
def multilinearAlgebra (L : ContinuousMultilinearMap ℝ V W) :
    MultilinearMap ℝ (fun i => α →ᵇ V i) (α →ᵇ W) := by
  classical
  refine MultilinearMap.mk' (multilinearValue L) ?_ ?_
  · intro f i a b
    apply BoundedContinuousFunction.ext
    intro x
    change L (fun j => Function.update f i (a+b) j x) =
      L (fun j => Function.update f i a j x) + L (fun j => Function.update f i b j x)
    have he (c : α →ᵇ V i) :
        (fun j => Function.update f i c j x) =
          Function.update (fun j => f j x) i (c x) := by
      funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [hj]
    simp only [he, BoundedContinuousFunction.add_apply]
    exact L.map_update_add _ _ _ _
  · intro f i r a
    apply BoundedContinuousFunction.ext
    intro x
    change L (fun j => Function.update f i (r • a) j x) =
      r • L (fun j => Function.update f i a j x)
    have he (c : α →ᵇ V i) :
        (fun j => Function.update f i c j x) =
          Function.update (fun j => f j x) i (c x) := by
      funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [hj]
    simp only [he, BoundedContinuousFunction.smul_apply]
    exact L.map_update_smul _ _ _ _

/-- Multilinear map, given by `(multilinearAlgebra L).mkContinuous ‖L‖ (multilinearValue_norm
L)`. -/
def multilinearMap (L : ContinuousMultilinearMap ℝ V W) :
    ContinuousMultilinearMap ℝ (fun i => α →ᵇ V i) (α →ᵇ W) :=
  (multilinearAlgebra L).mkContinuous ‖L‖ (multilinearValue_norm L)

@[simp] theorem multilinearMap_apply (L : ContinuousMultilinearMap ℝ V W)
    (f : ∀ i, α →ᵇ V i) (x : α) :
    multilinearMap L f x = L (fun i => f i x) := rfl

theorem multilinearMap_norm (L : ContinuousMultilinearMap ℝ V W) :
    ‖multilinearMap (α := α) L‖ ≤ ‖L‖ :=
  (multilinearAlgebra L).mkContinuous_norm_le (norm_nonneg L) (multilinearValue_norm L)

end EulerBoundedFieldCalculus
