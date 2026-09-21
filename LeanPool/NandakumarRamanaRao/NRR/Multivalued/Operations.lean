/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Multivalued.ZeroSet

/-!
# `NRR.Multivalued.Operations` — constructors and transformations of nice multivalued functions

This module provides the reusable operations on nice multivalued functions used later in the
prime-refinement argument:

* `NiceMV.pullback` along a continuous base map;
* `NiceMV.ofObservable`, the canonical nice multivalued function `φ(x, y) = y - f x` attached to a
  bounded continuous observable `f` with `|f x| < 1`;
* `NiceMV.scale` by a strictly positive real constant;
* `NiceMV.reflect`, the interval-reflection operation that reverses the sign convention through
  interval negation without changing the represented zero relation.

The signed-interval negation `SignedInterval.neg` is introduced first, together with its coercion
and continuity lemmas. Each operation records its evaluation law and the corresponding
zero-set/zero relation identity.
-/

namespace NRR

namespace SignedInterval

/-- Negation on the signed interval: reflection `t ↦ -t` through the center `0`. -/
def neg (t : SignedInterval) : SignedInterval :=
  ⟨-(t : ℝ), by
    constructor
    · linarith [t.2.2]
    · linarith [t.2.1]⟩

@[simp] theorem coe_neg
    (t : SignedInterval) :
    ((SignedInterval.neg t : SignedInterval) : ℝ) = -(t : ℝ) := rfl

theorem continuous_neg :
    Continuous SignedInterval.neg :=
  (continuous_subtype_val.neg).subtype_mk _

@[simp] theorem neg_left : SignedInterval.neg SignedInterval.left = SignedInterval.right := by
  apply Subtype.ext; simp

@[simp] theorem neg_right : SignedInterval.neg SignedInterval.right = SignedInterval.left := by
  apply Subtype.ext; simp

end SignedInterval

namespace NiceMV

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pull back a nice multivalued function `φ` on `X` along a continuous map `f : Y → X`, giving a
nice multivalued function on `Y` evaluated by `(φ.pullback f).eval y t = φ.eval (f y) t`. -/
def pullback
    (φ : NiceMV X) (f : C(Y, X)) :
    NiceMV Y :=
  ofFunction (fun y t => φ.eval (f y) t)
    (φ.continuous_eval.comp ((f.continuous.comp continuous_fst).prodMk continuous_snd))
    (fun y => φ.eval_left_neg (f y))
    (fun y => φ.eval_right_pos (f y))

theorem pullback_eval
    (φ : NiceMV X) (f : C(Y, X))
    (y : Y) (t : SignedInterval) :
    (φ.pullback f).eval y t = φ.eval (f y) t := rfl

theorem pullback_zeroSet
    (φ : NiceMV X) (f : C(Y, X)) :
    (φ.pullback f).zeroSet =
      (fun z : Y × SignedInterval => (f z.1, z.2)) ⁻¹' φ.zeroSet := by
  ext z
  simp only [zeroSet, Set.mem_ofPred_eq, Set.mem_preimage, zero_iff, pullback_eval]

/-- The canonical nice multivalued function attached to a bounded continuous observable `f` with
`|f x| < 1`: it evaluates by `(t : ℝ) - f x`, so its zero set is the graph `t = f x`. -/
def ofObservable
    (f : C(X, ℝ))
    (hbound : ∀ x, |f x| < 1) :
    NiceMV X :=
  ofFunction (fun x t => (t : ℝ) - f x)
    ((continuous_subtype_val.comp continuous_snd).sub (f.continuous.comp continuous_fst))
    (fun x => by
      simp only [SignedInterval.coe_left]
      linarith [(abs_lt.mp (hbound x)).1])
    (fun x => by
      simp only [SignedInterval.coe_right]
      linarith [(abs_lt.mp (hbound x)).2])

theorem ofObservable_eval
    (f : C(X, ℝ)) (hbound : ∀ x, |f x| < 1)
    (x : X) (t : SignedInterval) :
    (NiceMV.ofObservable f hbound).eval x t = (t : ℝ) - f x := rfl

theorem ofObservable_zero_iff
    (f : C(X, ℝ)) (hbound : ∀ x, |f x| < 1)
    (x : X) (t : SignedInterval) :
    (NiceMV.ofObservable f hbound).Zero x t ↔ (t : ℝ) = f x := by
  simp only [zero_iff, ofObservable_eval, sub_eq_zero]

/-- Rescale a nice multivalued function by a strictly positive constant `c`; scaling preserves the
strict endpoint signs, hence yields a nice multivalued function evaluated by `c * φ.eval x t`. -/
def scale
    (φ : NiceMV X) (c : ℝ) (hc : 0 < c) :
    NiceMV X :=
  ofFunction (fun x t => c * φ.eval x t)
    (continuous_const.mul φ.continuous_eval)
    (fun x => mul_neg_of_pos_of_neg hc (φ.eval_left_neg x))
    (fun x => mul_pos hc (φ.eval_right_pos x))

theorem scale_eval
    (φ : NiceMV X) (c : ℝ) (hc : 0 < c)
    (x : X) (t : SignedInterval) :
    (φ.scale c hc).eval x t = c * φ.eval x t := rfl

theorem scale_zeroSet
    (φ : NiceMV X) (c : ℝ) (hc : 0 < c) :
    (φ.scale c hc).zeroSet = φ.zeroSet := by
  ext z
  simp only [zeroSet, Set.mem_ofPred_eq, zero_iff, scale_eval, mul_eq_zero, hc.ne', false_or]

/-- Reflect a nice multivalued function through interval negation: `reflect` negates both the
observable and the interval coordinate. It preserves the zero relation under `SignedInterval.neg`,
so it reverses the sign convention without changing the represented zero relation. -/
def reflect
    (φ : NiceMV X) :
    NiceMV X :=
  ofFunction (fun x t => -φ.eval x (SignedInterval.neg t))
    ((φ.continuous_eval.comp
        (continuous_fst.prodMk (SignedInterval.continuous_neg.comp continuous_snd))).neg)
    (fun x => by
      simp only [SignedInterval.neg_left]
      linarith [φ.eval_right_pos x])
    (fun x => by
      simp only [SignedInterval.neg_right]
      linarith [φ.eval_left_neg x])

theorem reflect_eval
    (φ : NiceMV X) (x : X) (t : SignedInterval) :
    φ.reflect.eval x t =
      -φ.eval x (SignedInterval.neg t) := rfl

theorem reflect_zero_iff
    (φ : NiceMV X) (x : X) (t : SignedInterval) :
    φ.reflect.Zero x t ↔
      φ.Zero x (SignedInterval.neg t) := by
  simp only [zero_iff, reflect_eval, neg_eq_zero]

end NiceMV

end NRR
