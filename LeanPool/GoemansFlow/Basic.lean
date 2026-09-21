/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Fintype.Basic

/-! # Directed walks, unsplittable loads, and Goemans' cost conjecture -/

@[expose] public section

namespace GoemansFlow

section Walks

variable {W E : Type}

/-- `IsWalk tail head x l y`: the list of arcs `l`, read left to right, is a walk from
vertex `x` to vertex `y`.  Repeated vertices and arcs are permitted. -/
def IsWalk (tail head : E → W) : W → List E → W → Prop
  | x, [], y => x = y
  | x, e :: l, y => tail e = x ∧ IsWalk tail head (head e) l y

@[simp] theorem IsWalk_nil (tail head : E → W) (x y : W) :
    IsWalk tail head x [] y ↔ x = y := Iff.rfl

@[simp] theorem IsWalk_cons (tail head : E → W) (x : W) (e : E) (l : List E) (y : W) :
    IsWalk tail head x (e :: l) y ↔ (tail e = x ∧ IsWalk tail head (head e) l y) := Iff.rfl

/-- Boolean decision procedure for `IsWalk` (kernel-friendly). -/
def walkBool [DecidableEq W] (tail head : E → W) : W → List E → W → Bool
  | x, [], y => decide (x = y)
  | x, e :: l, y => decide (tail e = x) && walkBool tail head (head e) l y

theorem walkBool_iff [DecidableEq W] (tail head : E → W) (x : W) (l : List E) (y : W) :
    walkBool tail head x l y = true ↔ IsWalk tail head x l y := by
  induction l generalizing x with
  | nil => simp [walkBool]
  | cons e l ih => simp [walkBool, ih]

instance instDecidableIsWalk [DecidableEq W] (tail head : E → W) (x : W) (l : List E) (y : W) :
    Decidable (IsWalk tail head x l y) :=
  decidable_of_iff _ (walkBool_iff tail head x l y)

end Walks

/-- Load induced on arc `a` by an unsplittable routing `P` with demands `d`:
`flow_P(a) = sum_{k : a in P k} d k`. -/
def unsplittableLoad {R K E : Type} [AddCommMonoid R] [Fintype K] [DecidableEq E]
    (d : K → R) (P : K → List E) (a : E) : R :=
  ∑ k : K, if a ∈ P k then d k else 0

/-- Goemans' cost conjecture (Conjecture 1.3 of arXiv:2308.02651), restricted to
simple, loopless, acyclic digraphs, with explicit capacities and strictly positive demands.

A refutation of this restricted form also refutes the conjecture over general digraphs.
The conclusion allows arbitrary walks; the counterexample proves that every admissible
walk is a simple path. The coefficient ring is generic, with the rational case matching
the source's setting. -/
def GoemansCostConjectureFull (R : Type) [CommRing R] [LinearOrder R] :
    Prop :=
  ∀ (W E K : Type) [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E] [Fintype K]
    (tail head : E → W) (src : W) (term : K → W) (d : K → R) (dmax : R) (x c u : E → R),
    -- the digraph is simple, loopless and acyclic
    Function.Injective (fun a : E => (tail a, head a)) →
    (∀ a, tail a ≠ head a) →
    (∃ r : W → ℕ, ∀ a, r (tail a) < r (head a)) →
    -- capacities, with the source's standing hypothesis
    (∀ a, x a ≤ u a) →
    -- the terminals are distinct from each other and from the source
    Function.Injective term →
    (∀ k, term k ≠ src) →
    -- demands are positive and `dmax` is the maximum demand
    (∀ k, 0 < d k) →
    (∀ k, d k ≤ dmax) →
    (∃ k, d k = dmax) →
    -- nonnegative costs and a nonnegative flow
    (∀ a, 0 ≤ c a) →
    (∀ a, 0 ≤ x a) →
    -- `x` is a feasible single-source flow for the demands
    (∀ z : W, z ≠ src →
      (∑ a : E, if head a = z then x a else 0) - (∑ a : E, if tail a = z then x a else 0)
        = ∑ k : K, if term k = z then d k else 0) →
    ((∑ a : E, if tail a = src then x a else 0)
        - (∑ a : E, if head a = src then x a else 0) = ∑ k : K, d k) →
    -- conclusion
    ∃ P : K → List E,
      (∀ k, IsWalk tail head src (P k) (term k)) ∧
      (∀ a, unsplittableLoad d P a ≤ x a + dmax) ∧
      (∑ a : E, c a * unsplittableLoad d P a) ≤ ∑ a : E, c a * x a

end GoemansFlow
