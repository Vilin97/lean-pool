/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import LeanPool.PebblingLean.Basic

/-!
# Product constructions

This file begins the deterministic part of the upper-bound proof.  The main
result here is the slice simulation lemma: a pebbling sequence in one factor of
a Cartesian product can be executed inside a fixed slice of the product.
-/

namespace PebblingLean

universe u v

namespace Graph

variable {V : Type u} {W : Type v}

/-- Cartesian product of simple graphs. -/
def cartesianProduct (G : Graph V) (H : Graph W) : Graph (V × W) where
  Adj p q :=
    (G.Adj p.1 q.1 ∧ p.2 = q.2) ∨ (p.1 = q.1 ∧ H.Adj p.2 q.2)
  symm := by
    intro p q h
    rcases h with h | h
    · exact Or.inl ⟨G.symm h.1, h.2.symm⟩
    · exact Or.inr ⟨h.1.symm, H.symm h.2⟩
  loopless := by
    intro p h
    rcases h with h | h
    · exact (G.loopless p.1) h.1
    · exact (H.loopless p.2) h.2

end Graph

namespace Pebbling

variable {V : Type u} {W : Type v}


/-- A product distribution assembled from first-factor fibers indexed by the
second factor.  The value at `(x, z)` is the value of the `z`-fiber at `x`. -/
def fibersDistribution (F : W → Pebbling V) : Pebbling (V × W) :=
  fun p => F p.2 p.1

@[simp]
theorem fibersDistribution_apply (F : W → Pebbling V) (x : V) (z : W) :
    fibersDistribution F (x, z) = F z x :=
  rfl

/-- Replace one first-factor fiber in a family of fibers. -/
def replaceFiber [DecidableEq W] (F : W → Pebbling V) (z : W) (E : Pebbling V) :
    W → Pebbling V :=
  fun z' => if z' = z then E else F z'

/-- The family obtained by replacing all fibers in `s` by their target fibers. -/
def updateFibers [DecidableEq W] (F F' : W → Pebbling V) (s : Finset W) :
    W → Pebbling V :=
  fun z => if z ∈ s then F' z else F z

/-- Total size of a fiber-assembled product distribution. -/
theorem size_fibersDistribution [Fintype V] [Fintype W] (F : W → Pebbling V) :
    size (fibersDistribution F) = ∑ z, size (F z) := by
  classical
  rw [size]
  change (∑ p : V × W, F p.2 p.1) = ∑ z : W, size (F z)
  rw [Fintype.sum_prod_type_right]
  simp [size]

/-- A pointwise fiber cost bound gives a product cost bound. -/
theorem size_fibersDistribution_le [Fintype V] [Fintype W] {F : W → Pebbling V}
    {cost : W → ℕ} (hcost : ∀ z : W, size (F z) ≤ cost z) :
    size (fibersDistribution F) ≤ ∑ z, cost z := by
  classical
  rw [size_fibersDistribution]
  exact Finset.sum_le_sum fun z _ => hcost z

/-- A distribution supported in the slice `{x} × W`, with profile `E` in the
second coordinate. -/
def sliceDistribution [DecidableEq V] (x : V) (E : Pebbling W) : Pebbling (V × W) :=
  fun p => if p.1 = x then E p.2 else 0

@[simp]
theorem sliceDistribution_apply_on [DecidableEq V] (x : V) (E : Pebbling W) (z : W) :
    sliceDistribution x E (x, z) = E z := by
  simp [sliceDistribution]

@[simp]
theorem sliceDistribution_apply_off [DecidableEq V] {x x' : V} (E : Pebbling W) (z : W)
    (h : x' ≠ x) :
    sliceDistribution x E (x', z) = 0 := by
  simp [sliceDistribution, h]

/-- One move in the first factor can be replayed inside a fixed fiber of the
Cartesian product, leaving all other fibers unchanged. -/
theorem replaceFiber_move_left [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E F : Pebbling V} {Fs : W → Pebbling V} {z : W}
    (hmove : Move G E F) :
    Move (Graph.cartesianProduct G H)
      (fibersDistribution (replaceFiber Fs z E))
      (fibersDistribution (replaceFiber Fs z F)) := by
  rcases hmove with ⟨u, v, huv, hE, rfl⟩
  refine ⟨(u, z), (v, z), ?_, ?_, ?_⟩
  · exact Or.inl ⟨huv, rfl⟩
  · simpa [fibersDistribution, replaceFiber] using hE
  · funext p
    cases p with
    | mk x z' =>
      by_cases hz' : z' = z
      · subst z'
        by_cases hxu : x = u
        · subst x
          simp [fibersDistribution, replaceFiber, moveDistribution]
        · by_cases hxv : x = v
          · subst x
            have hvu : v ≠ u := by
              intro hvu
              subst u
              exact (G.loopless v) huv
            simp [fibersDistribution, replaceFiber, moveDistribution, hvu]
          · simp [fibersDistribution, replaceFiber, moveDistribution, hxu, hxv]
      · have hp_ne_from : (x, z') ≠ (u, z) := by
          intro hp
          exact hz' (Prod.ext_iff.mp hp).2
        have hp_ne_to : (x, z') ≠ (v, z) := by
          intro hp
          exact hz' (Prod.ext_iff.mp hp).2
        simp [fibersDistribution, replaceFiber, moveDistribution, hz', hp_ne_from, hp_ne_to]

/-- A pebbling sequence in the first factor can be replayed inside a fixed
fiber of the product. -/
theorem replaceFiber_reaches_left [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E F : Pebbling V} {Fs : W → Pebbling V} {z : W}
    (hreach : Reaches G E F) :
    Reaches (Graph.cartesianProduct G H)
      (fibersDistribution (replaceFiber Fs z E))
      (fibersDistribution (replaceFiber Fs z F)) := by
  unfold Reaches at hreach ⊢
  refine hreach.head_induction_on ?refl ?head
  · exact Relation.ReflTransGen.refl
  · intro A B hmove _ hfiber
    exact Relation.ReflTransGen.head
      (replaceFiber_move_left (G := G) (H := H) (Fs := Fs) (z := z) hmove) hfiber

/-- Independent first-factor preparations in every fiber can be composed into
one product pebbling sequence. -/
theorem fibers_reaches_of_forall_reaches [Finite W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {F F' : W → Pebbling V}
    (hreach : ∀ z : W, Reaches G (F z) (F' z)) :
    Reaches (Graph.cartesianProduct G H) (fibersDistribution F) (fibersDistribution F') := by
  classical
  letI := Fintype.ofFinite W
  have hstep :
      ∀ s : Finset W,
        Reaches (Graph.cartesianProduct G H)
          (fibersDistribution F)
          (fibersDistribution (updateFibers F F' s)) := by
    intro s
    refine Finset.induction_on s ?base ?insert
    · have hbase :
          fibersDistribution (updateFibers F F' ∅) = fibersDistribution F := by
        funext p
        cases p with
        | mk x z =>
          simp [fibersDistribution, updateFibers]
      rw [hbase]
      exact Relation.ReflTransGen.refl
    · intro z s hz_not_mem ih
      have hreplace :
          Reaches (Graph.cartesianProduct G H)
            (fibersDistribution (replaceFiber (updateFibers F F' s) z (F z)))
            (fibersDistribution (replaceFiber (updateFibers F F' s) z (F' z))) :=
        replaceFiber_reaches_left (G := G) (H := H)
          (Fs := updateFibers F F' s) (z := z) (hreach z)
      have hstart :
          fibersDistribution (replaceFiber (updateFibers F F' s) z (F z)) =
            fibersDistribution (updateFibers F F' s) := by
        funext p
        cases p with
        | mk x z' =>
          by_cases hz' : z' = z
          · subst z'
            simp [fibersDistribution, replaceFiber, updateFibers, hz_not_mem]
          · simp [fibersDistribution, replaceFiber, updateFibers, hz']
      have hfinish :
          fibersDistribution (replaceFiber (updateFibers F F' s) z (F' z)) =
            fibersDistribution (updateFibers F F' (insert z s)) := by
        funext p
        cases p with
        | mk x z' =>
          by_cases hz' : z' = z
          · subst z'
            simp [fibersDistribution, replaceFiber, updateFibers]
          · simp [fibersDistribution, replaceFiber, updateFibers, hz']
      have hreplace' :
          Reaches (Graph.cartesianProduct G H)
            (fibersDistribution (updateFibers F F' s))
            (fibersDistribution (updateFibers F F' (insert z s))) := by
        simpa [hstart, hfinish] using hreplace
      exact Relation.ReflTransGen.trans ih hreplace'
  have hfinal : fibersDistribution (updateFibers F F' Finset.univ) = fibersDistribution F' := by
    funext p
    cases p with
    | mk x z =>
      simp [fibersDistribution, updateFibers]
  simpa [hfinal] using hstep Finset.univ

/-- One move in the second factor can be replayed inside a fixed product slice. -/
theorem slice_move_right [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E F : Pebbling W} {x : V}
    (hmove : Move H E F) :
    Move (Graph.cartesianProduct G H) (sliceDistribution x E) (sliceDistribution x F) := by
  rcases hmove with ⟨u, v, huv, hE, rfl⟩
  refine ⟨(x, u), (x, v), ?_, ?_, ?_⟩
  · exact Or.inr ⟨rfl, huv⟩
  · simpa [sliceDistribution] using hE
  · funext p
    by_cases hpx : p.1 = x
    · cases p with
      | mk x' z =>
        simp only at hpx
        subst x'
        by_cases hzu : z = u
        · subst z
          simp [sliceDistribution, moveDistribution]
        · by_cases hzv : z = v
          · subst z
            have hvu : v ≠ u := by
              intro hvu
              subst u
              exact (H.loopless v) huv
            simp [sliceDistribution, moveDistribution, hvu]
          · simp [sliceDistribution, moveDistribution, hzu, hzv]
    · cases p with
      | mk x' z =>
        simp only at hpx
        have hp_ne_from : (x', z) ≠ (x, u) := by
          intro hp
          exact hpx (Prod.ext_iff.mp hp).1
        have hp_ne_to : (x', z) ≠ (x, v) := by
          intro hp
          exact hpx (Prod.ext_iff.mp hp).1
        simp [sliceDistribution, moveDistribution, hpx, hp_ne_from, hp_ne_to]

/-- A pebbling sequence in the second factor can be replayed inside a fixed
slice of the product. -/
theorem slice_reaches_right [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E F : Pebbling W} {x : V}
    (hreach : Reaches H E F) :
    Reaches (Graph.cartesianProduct G H) (sliceDistribution x E) (sliceDistribution x F) := by
  unfold Reaches at hreach ⊢
  refine hreach.head_induction_on ?refl ?head
  · exact Relation.ReflTransGen.refl
  · intro A B hmove _ hslice
    exact Relation.ReflTransGen.head (slice_move_right (G := G) (H := H) (x := x) hmove) hslice

/-- If `E` solves a target in the second factor, then the corresponding slice
distribution solves the corresponding product target. -/
theorem slice_canReachAtLeast_right [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E : Pebbling W} {x : V} {target : W} {T : ℕ}
    (hcan : CanReachAtLeast H E target T) :
    CanReachAtLeast (Graph.cartesianProduct G H) (sliceDistribution x E) (x, target) T := by
  rcases hcan with ⟨F, hreach, htarget⟩
  exact ⟨sliceDistribution x F, slice_reaches_right (G := G) (H := H) (x := x) hreach, by
    simpa using htarget⟩

/-- Once a product distribution dominates a prepared slice, any target reachable
from the slice is also reachable from the product distribution. -/
theorem canReachAtLeast_of_dominates_slice_right [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {D : Pebbling (V × W)} {E : Pebbling W}
    {x : V} {target : W} {T : ℕ}
    (hdom : Dominates D (sliceDistribution x E))
    (hcan : CanReachAtLeast H E target T) :
    CanReachAtLeast (Graph.cartesianProduct G H) D (x, target) T :=
  canReachAtLeast_of_dominates
    (slice_canReachAtLeast_right (G := G) (H := H) (x := x) hcan) hdom

/-- Composition bridge for the deterministic product step: if a first phase
reaches a distribution dominating the prepared slice `{x} × W`, then a solution
inside the `W` factor can be appended to solve the product target. -/
theorem canReachAtLeast_after_prepared_slice_right [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {D Dprep : Pebbling (V × W)} {E : Pebbling W}
    {x : V} {target : W} {T : ℕ}
    (hprepReach : Reaches (Graph.cartesianProduct G H) D Dprep)
    (hprepDom : Dominates Dprep (sliceDistribution x E))
    (hcan : CanReachAtLeast H E target T) :
    CanReachAtLeast (Graph.cartesianProduct G H) D (x, target) T := by
  rcases canReachAtLeast_of_dominates_slice_right (G := G) (H := H)
      (D := Dprep) (E := E) (x := x) hprepDom hcan with
    ⟨Dfinish, hfinishReach, htarget⟩
  exact ⟨Dfinish, Relation.ReflTransGen.trans hprepReach hfinishReach, htarget⟩

/-- If every fiber can prepare the number of pebbles prescribed by `E` at the
same first-coordinate target `x`, then the product distribution can be moved to
a distribution dominating the slice `{x} × W` with profile `E`. -/
theorem fibers_prepare_slice_right [Finite W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E : Pebbling W} {F : W → Pebbling V} {x : V}
    (hcan : ∀ z : W, CanReachAtLeast G (F z) x (E z)) :
    ∃ Dprep : Pebbling (V × W),
      Reaches (Graph.cartesianProduct G H) (fibersDistribution F) Dprep ∧
        Dominates Dprep (sliceDistribution x E) := by
  classical
  choose F' hreach htarget using hcan
  refine ⟨fibersDistribution F', ?_, ?_⟩
  · exact fibers_reaches_of_forall_reaches (G := G) (H := H) hreach
  · intro p
    cases p with
    | mk v z =>
      by_cases hv : v = x
      · subst v
        simpa [fibersDistribution, sliceDistribution] using htarget z
      · simp [fibersDistribution, sliceDistribution, hv]

/-- Deterministic product step.  If `E` solves `H`, and each `z`-fiber has
enough demand-solvability in `G` to prepare `E z` pebbles at any chosen
first-coordinate target, then the assembled product distribution solves
`G □ H`. -/
theorem solvable_product_of_fiber_demands [Finite W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E : Pebbling W} {F : W → Pebbling V}
    (hE : Solvable H E)
    (hF : ∀ z : W, SolvableAtLeast G (F z) (E z)) :
    Solvable (Graph.cartesianProduct G H) (fibersDistribution F) := by
  intro target
  rcases target with ⟨x, y⟩
  rcases fibers_prepare_slice_right (G := G) (H := H) (E := E) (F := F) (x := x)
      (fun z => hF z x) with
    ⟨Dprep, hprepReach, hprepDom⟩
  exact canReachAtLeast_after_prepared_slice_right (G := G) (H := H)
    (D := fibersDistribution F) (Dprep := Dprep) (E := E) (x := x) (target := y)
    hprepReach hprepDom (hE y)

/-- Costed form of the deterministic product step, matching the recursive
upper-bound bookkeeping: only occupied vertices of `E` need nonzero demand
distributions in the first factor. -/
theorem hasSolvableAtMostSize_product_of_fiber_demands
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E : Pebbling W} {cost : W → ℕ}
    (hE : Solvable H E)
    (hcost : ∀ z : W, E z ≠ 0 → HasSolvableAtMostSize G (E z) (cost z)) :
    HasSolvableAtMostSize (Graph.cartesianProduct G H) 1
      (∑ z, if E z = 0 then 0 else cost z) := by
  classical
  let F : W → Pebbling V := fun z =>
    if hz : E z = 0 then (fun _ : V => 0) else Classical.choose (hcost z hz)
  have hFsolv : ∀ z : W, SolvableAtLeast G (F z) (E z) := by
    intro z
    by_cases hz : E z = 0
    · rw [hz]
      exact solvableAtLeast_zero G (F z)
    · simpa [F, hz] using (Classical.choose_spec (hcost z hz)).2
  have hFsize : ∀ z : W, size (F z) ≤ if E z = 0 then 0 else cost z := by
    intro z
    by_cases hz : E z = 0
    · simp [F, hz]
    · simpa [F, hz] using (Classical.choose_spec (hcost z hz)).1
  refine ⟨fibersDistribution F, ?_, ?_⟩
  · exact size_fibersDistribution_le hFsize
  · exact solvable_product_of_fiber_demands (G := G) (H := H) hE hFsolv

end Pebbling

end PebblingLean
