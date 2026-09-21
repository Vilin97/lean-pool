/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.OrderedForest

/-! # Nested integrals over ordered simplices

Defines the nested interval integral `orderedSimplexIntegral` over the
ordered simplex `0 ≤ tₙ ≤ … ≤ t₂ ≤ t₁ ≤ top` attached to a list of edges,
and the predicate `OrderedSimplexParams` describing its parameter lists.
These nested one-dimensional integrals are the raw form in which the
ordered expansion of the BKAR forest interpolation formula (see
`BKAR.Formula`) first produces its remainder terms.
-/

noncomputable section

namespace BKAR

variable {V : Type*} [DecidableEq V]

/--
Nested interval integral over the ordered simplex associated to an edge order.

The list of real parameters supplied to the integrand is in the same order as
the edge list. If `order = [e₁, e₂, ...]`, then the bounds are
`0 ≤ tₙ ≤ ... ≤ t₂ ≤ t₁ ≤ top`.
-/
def orderedSimplexIntegralAux (top : ℝ) :
    List (Edge V) → (List ℝ → ℝ) → ℝ
  | [], f => f []
  | _ :: order, f =>
      ∫ t in 0..top,
        orderedSimplexIntegralAux t order (fun ts => f (t :: ts))

/--
Nested interval integral over the ordered simplex with outer bound `1`.
-/
def orderedSimplexIntegral (order : List (Edge V)) (f : List ℝ → ℝ) : ℝ :=
  orderedSimplexIntegralAux 1 order f

/--
Predicate saying that a parameter list lies in the ordered simplex with outer
bound `top`: `0 ≤ tₙ ≤ ... ≤ t₂ ≤ t₁ ≤ top`.
-/
def OrderedSimplexParams : ℝ → List ℝ → Prop
  | _, [] => True
  | top, t :: ts => 0 ≤ t ∧ t ≤ top ∧ OrderedSimplexParams t ts

@[simp]
theorem orderedSimplexIntegralAux_nil (top : ℝ) (f : List ℝ → ℝ) :
    orderedSimplexIntegralAux top ([] : List (Edge V)) f = f [] :=
  rfl

@[simp]
theorem orderedSimplexIntegralAux_cons (top : ℝ) (e : Edge V)
    (order : List (Edge V)) (f : List ℝ → ℝ) :
    orderedSimplexIntegralAux top (e :: order) f =
      ∫ t in 0..top,
        orderedSimplexIntegralAux t order (fun ts => f (t :: ts)) :=
  rfl

@[simp]
theorem orderedSimplexIntegral_nil (f : List ℝ → ℝ) :
    orderedSimplexIntegral ([] : List (Edge V)) f = f [] :=
  rfl

@[simp]
theorem orderedSimplexIntegral_cons (e : Edge V) (order : List (Edge V))
    (f : List ℝ → ℝ) :
    orderedSimplexIntegral (e :: order) f =
      ∫ t in 0..(1 : ℝ),
        orderedSimplexIntegralAux t order (fun ts => f (t :: ts)) :=
  rfl

theorem orderedSimplexIntegral_singleton (e : Edge V) (f : List ℝ → ℝ) :
    orderedSimplexIntegral [e] f = ∫ t in 0..(1 : ℝ), f [t] :=
  rfl

theorem orderedSimplexIntegral_pair (e₁ e₂ : Edge V) (f : List ℝ → ℝ) :
    orderedSimplexIntegral [e₁, e₂] f =
      ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁, f [t₁, t₂] :=
  rfl

@[simp]
theorem orderedSimplexParams_nil (top : ℝ) :
    OrderedSimplexParams top [] :=
  trivial

@[simp]
theorem orderedSimplexParams_cons (top t : ℝ) (ts : List ℝ) :
    OrderedSimplexParams top (t :: ts) ↔
      0 ≤ t ∧ t ≤ top ∧ OrderedSimplexParams t ts :=
  Iff.rfl

namespace OrderedSimplexParams

theorem head_nonneg {top t : ℝ} {ts : List ℝ}
    (h : OrderedSimplexParams top (t :: ts)) :
    0 ≤ t :=
  h.1

theorem head_le_top {top t : ℝ} {ts : List ℝ}
    (h : OrderedSimplexParams top (t :: ts)) :
    t ≤ top :=
  h.2.1

theorem tail {top t : ℝ} {ts : List ℝ}
    (h : OrderedSimplexParams top (t :: ts)) :
    OrderedSimplexParams t ts :=
  h.2.2

theorem nonneg_of_mem :
    ∀ {top : ℝ} {ts : List ℝ} {t : ℝ},
      OrderedSimplexParams top ts → t ∈ ts → 0 ≤ t
  | _, [], _, _, ht => by
      cases ht
  | _, x :: xs, t, h, ht => by
      rw [List.mem_cons] at ht
      cases ht with
      | inl htx =>
          rw [htx]
          exact h.head_nonneg
      | inr htxs =>
          exact nonneg_of_mem h.tail htxs

theorem le_top_of_mem :
    ∀ {top : ℝ} {ts : List ℝ} {t : ℝ},
      OrderedSimplexParams top ts → t ∈ ts → t ≤ top
  | _, [], _, _, ht => by
      cases ht
  | _, x :: xs, t, h, ht => by
      rw [List.mem_cons] at ht
      cases ht with
      | inl htx =>
          rw [htx]
          exact h.head_le_top
      | inr htxs =>
          exact (le_top_of_mem h.tail htxs).trans h.head_le_top

theorem le_head_of_mem_tail {top t s : ℝ} {ts : List ℝ}
    (h : OrderedSimplexParams top (t :: ts)) (hs : s ∈ ts) :
    s ≤ t :=
  le_top_of_mem h.tail hs

end OrderedSimplexParams

theorem orderedSimplexIntegralAux_congr (top : ℝ) :
    ∀ (order : List (Edge V)) {f g : List ℝ → ℝ},
      (∀ ts, f ts = g ts) →
        orderedSimplexIntegralAux top order f =
          orderedSimplexIntegralAux top order g
  | [], _, _, hfg => hfg []
  | _ :: order, f, g, hfg => by
      apply intervalIntegral.integral_congr
      intro t _
      exact orderedSimplexIntegralAux_congr t order
        (f := fun ts => f (t :: ts))
        (g := fun ts => g (t :: ts))
        (fun ts => hfg (t :: ts))

theorem orderedSimplexIntegral_congr {order : List (Edge V)}
    {f g : List ℝ → ℝ} (hfg : ∀ ts, f ts = g ts) :
    orderedSimplexIntegral order f = orderedSimplexIntegral order g := by
  rw [orderedSimplexIntegral]
  exact orderedSimplexIntegralAux_congr 1 order hfg

/--
Congruence for nested simplex integrals when the integrands agree on
parameter lists whose length matches the remaining edge order.
-/
theorem orderedSimplexIntegralAux_congr_of_length (top : ℝ) :
    ∀ (order : List (Edge V)) {f g : List ℝ → ℝ},
      (∀ ts, ts.length = order.length → f ts = g ts) →
        orderedSimplexIntegralAux top order f =
          orderedSimplexIntegralAux top order g
  | [], _, _, hfg => hfg [] rfl
  | _ :: order, f, g, hfg => by
      apply intervalIntegral.integral_congr
      intro t _
      exact orderedSimplexIntegralAux_congr_of_length t order
        (f := fun ts => f (t :: ts))
        (g := fun ts => g (t :: ts))
        (fun ts hlen => hfg (t :: ts) (by simp [hlen]))

/--
Unit-bound version of `orderedSimplexIntegralAux_congr_of_length`.
-/
theorem orderedSimplexIntegral_congr_of_length {order : List (Edge V)}
    {f g : List ℝ → ℝ}
    (hfg : ∀ ts, ts.length = order.length → f ts = g ts) :
    orderedSimplexIntegral order f = orderedSimplexIntegral order g := by
  rw [orderedSimplexIntegral]
  exact orderedSimplexIntegralAux_congr_of_length 1 order hfg

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
