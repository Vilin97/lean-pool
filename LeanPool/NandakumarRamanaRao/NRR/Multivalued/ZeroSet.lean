/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Nice

/-!
# `NRR.Multivalued.ZeroSet` — zero sets, fibers, and existence of zeros

The graph of a nice multivalued function is the zero set of its scalar observable. This module
defines the zero predicate, the total zero set on `X × SignedInterval`, and the vertical zero
fiber over a base point. It records that these sets are closed, that fibers are compact and
nonempty, and that the total zero set is compact when `X` is compact.

Existence of a zero in every vertical fiber follows from the intermediate value theorem: the
observable is strictly negative at the left endpoint and strictly positive at the right endpoint,
and the signed interval is connected, so the continuous image contains `0`. No zero selector is
introduced; only existence is proved. Zeros never occur at either endpoint, by the strict signs.
-/

@[expose] public section

namespace NRR

variable {X : Type*} [TopologicalSpace X]

namespace NiceMV

/-- A point `(x, y)` is a zero of `φ` when the observable vanishes there. -/
def Zero (φ : NiceMV X) (x : X) (y : SignedInterval) : Prop :=
  φ.eval x y = 0

/-- The total zero set (graph) of `φ` inside `X × SignedInterval`. -/
def zeroSet (φ : NiceMV X) : Set (X × SignedInterval) :=
  {z | φ.Zero z.1 z.2}

/-- The vertical zero fiber of `φ` over a base point `x`. -/
def zeroFiber (φ : NiceMV X) (x : X) : Set SignedInterval :=
  {y | φ.Zero x y}

@[simp] theorem zero_iff
    (φ : NiceMV X) (x : X) (y : SignedInterval) :
    φ.Zero x y ↔ φ.eval x y = 0 := Iff.rfl

/-- Continuity of the observable along a single vertical fiber. -/
theorem continuous_eval_fiber (φ : NiceMV X) (x : X) :
    Continuous fun y : SignedInterval => φ.eval x y :=
  φ.continuous_eval.comp (SignedInterval.continuous_vertical x)

theorem isClosed_zeroSet
    (φ : NiceMV X) :
    IsClosed φ.zeroSet :=
  isClosed_eq φ.continuous_eval continuous_const

theorem isClosed_zeroFiber
    (φ : NiceMV X) (x : X) :
    IsClosed (φ.zeroFiber x) :=
  isClosed_eq (φ.continuous_eval_fiber x) continuous_const

theorem isCompact_zeroFiber
    (φ : NiceMV X) (x : X) :
    IsCompact (φ.zeroFiber x) :=
  (φ.isClosed_zeroFiber x).isCompact

theorem exists_zero
    (φ : NiceMV X) (x : X) :
    ∃ y : SignedInterval, φ.Zero x y := by
  have hmem : (0 : ℝ) ∈
      Set.Icc (φ.eval x SignedInterval.left) (φ.eval x SignedInterval.right) :=
    ⟨le_of_lt (φ.eval_left_neg x), le_of_lt (φ.eval_right_pos x)⟩
  obtain ⟨y, hy⟩ :=
    intermediate_value_univ SignedInterval.left SignedInterval.right
      (φ.continuous_eval_fiber x) hmem
  exact ⟨y, hy⟩

theorem zeroFiber_nonempty
    (φ : NiceMV X) (x : X) :
    (φ.zeroFiber x).Nonempty := by
  obtain ⟨y, hy⟩ := φ.exists_zero x
  exact ⟨y, hy⟩

theorem isCompact_zeroSet
    [CompactSpace X] (φ : NiceMV X) :
    IsCompact φ.zeroSet :=
  φ.isClosed_zeroSet.isCompact

theorem not_zero_left
    (φ : NiceMV X) (x : X) :
    ¬ φ.Zero x SignedInterval.left :=
  fun h => (ne_of_lt (φ.eval_left_neg x)) h

theorem not_zero_right
    (φ : NiceMV X) (x : X) :
    ¬ φ.Zero x SignedInterval.right :=
  fun h => (ne_of_gt (φ.eval_right_pos x)) h

end NiceMV

end NRR
