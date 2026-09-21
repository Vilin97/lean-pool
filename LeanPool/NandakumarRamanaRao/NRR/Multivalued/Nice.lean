/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Multivalued.SignedInterval

/-!
# `NRR.Multivalued.Nice` — nice multivalued functions

A nice multivalued function on a topological space `X` is represented by a single continuous
scalar map on `X × SignedInterval` whose zero set is its graph. The sign convention is that the
map is strictly negative at the left endpoint `-1` and strictly positive at the right endpoint `1`.

No separate set-valued topology is introduced: the multivalued function is bundled as one
continuous scalar observable together with the two strict endpoint sign conditions. This module
provides the evaluation projection, its continuity, extensionality reducing equality to pointwise
equality, the endpoint sign lemmas, and a constructor from an unbundled continuous function.
-/

namespace NRR

variable {X : Type*} [TopologicalSpace X]

/-- A nice multivalued function on `X`: a continuous scalar map on `X × SignedInterval` that is
strictly negative at the left endpoint and strictly positive at the right endpoint. Its graph is
the zero set of `evalMap`. -/
structure NiceMV (X : Type*) [TopologicalSpace X] where
  /-- The bundled continuous scalar observable on `X × SignedInterval`. -/
  evalMap : C(X × SignedInterval, ℝ)
  /-- The observable is strictly negative at the left endpoint `-1`. -/
  left_neg : ∀ x : X, evalMap (x, SignedInterval.left) < 0
  /-- The observable is strictly positive at the right endpoint `1`. -/
  right_pos : ∀ x : X, 0 < evalMap (x, SignedInterval.right)

namespace NiceMV

/-- Evaluate a nice multivalued function at a base point and a signed-interval coordinate. -/
def eval (φ : NiceMV X) (x : X) (y : SignedInterval) : ℝ :=
  φ.evalMap (x, y)

@[simp] theorem eval_def
    (φ : NiceMV X) (x : X) (y : SignedInterval) :
    φ.eval x y = φ.evalMap (x, y) := rfl

theorem continuous_eval
    (φ : NiceMV X) :
    Continuous fun z : X × SignedInterval =>
      φ.eval z.1 z.2 :=
  φ.evalMap.continuous

theorem continuous_eval_left
    (φ : NiceMV X) :
    Continuous fun x : X => φ.eval x SignedInterval.left :=
  φ.evalMap.continuous.comp (continuous_id.prodMk continuous_const)

theorem continuous_eval_right
    (φ : NiceMV X) :
    Continuous fun x : X => φ.eval x SignedInterval.right :=
  φ.evalMap.continuous.comp (continuous_id.prodMk continuous_const)

theorem eval_left_neg
    (φ : NiceMV X) (x : X) :
    φ.eval x SignedInterval.left < 0 :=
  φ.left_neg x

theorem eval_right_pos
    (φ : NiceMV X) (x : X) :
    0 < φ.eval x SignedInterval.right :=
  φ.right_pos x

@[ext] theorem ext
    {φ ψ : NiceMV X}
    (h : ∀ x y, φ.eval x y = ψ.eval x y) :
    φ = ψ := by
  cases φ with
  | mk fφ _ _ =>
    cases ψ with
    | mk fψ _ _ =>
      have hmap : fφ = fψ := by
        apply ContinuousMap.ext
        rintro ⟨x, y⟩
        exact h x y
      subst hmap
      rfl

/-- Build a nice multivalued function from an unbundled continuous function with the required
strict endpoint signs. -/
def ofFunction
    (f : X → SignedInterval → ℝ)
    (hf : Continuous fun z : X × SignedInterval => f z.1 z.2)
    (hleft : ∀ x, f x SignedInterval.left < 0)
    (hright : ∀ x, 0 < f x SignedInterval.right) :
    NiceMV X where
  evalMap := ContinuousMap.mk (fun z => f z.1 z.2) hf
  left_neg := hleft
  right_pos := hright

@[simp] theorem ofFunction_eval
    (f : X → SignedInterval → ℝ)
    (hf : Continuous fun z : X × SignedInterval => f z.1 z.2)
    (hleft : ∀ x, f x SignedInterval.left < 0)
    (hright : ∀ x, 0 < f x SignedInterval.right)
    (x : X) (y : SignedInterval) :
    (ofFunction f hf hleft hright).eval x y = f x y := rfl

end NiceMV

end NRR
