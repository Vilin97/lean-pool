/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import LeanPool.PebblingLean.Basic

/-!
# Transport across graph isomorphisms

The recursive upper bound is naturally proved on Cartesian products.  To apply
those product constructions to hypercubes, we need a lightweight way to move
pebbling distributions and solvability statements across graph isomorphisms.
-/

namespace PebblingLean

universe u v

/-- An adjacency-preserving equivalence between two simple graphs. -/
structure GraphIso {V : Type u} {W : Type v} (G : Graph V) (H : Graph W) where
  /-- The underlying equivalence between the vertex types. -/
  toEquiv : V ≃ W
  /-- The equivalence preserves and reflects adjacency. -/
  adj_iff : ∀ {x y : V}, G.Adj x y ↔ H.Adj (toEquiv x) (toEquiv y)

namespace GraphIso

variable {V : Type u} {W : Type v} {G : Graph V} {H : Graph W}

/-- Transport a pebbling distribution across the vertex equivalence. -/
def mapDistribution (iso : GraphIso G H) (D : Pebbling V) : Pebbling W :=
  fun w => D (iso.toEquiv.symm w)

@[simp]
theorem mapDistribution_apply (iso : GraphIso G H) (D : Pebbling V) (v : V) :
    iso.mapDistribution D (iso.toEquiv v) = D v := by
  simp [mapDistribution]

theorem size_mapDistribution [Fintype V] [Fintype W]
    (iso : GraphIso G H) (D : Pebbling V) :
    Pebbling.size (iso.mapDistribution D) = Pebbling.size D := by
  change (∑ w : W, D (iso.toEquiv.symm w)) = ∑ v : V, D v
  exact Equiv.sum_comp iso.toEquiv.symm D

/-- Reverse a graph isomorphism. -/
def symm (iso : GraphIso G H) : GraphIso H G where
  toEquiv := iso.toEquiv.symm
  adj_iff := by
    intro x y
    simpa using
      (iso.adj_iff (x := iso.toEquiv.symm x) (y := iso.toEquiv.symm y)).symm

theorem map_move [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {D E : Pebbling V}
    (hmove : Pebbling.Move G D E) :
    Pebbling.Move H (iso.mapDistribution D) (iso.mapDistribution E) := by
  rcases hmove with ⟨u, v, huv, hD, rfl⟩
  have huv_ne : u ≠ v := by
    intro h
    subst v
    exact (G.loopless u) huv
  have hvu_ne : v ≠ u := fun h => huv_ne h.symm
  have heuv_ne : iso.toEquiv u ≠ iso.toEquiv v := fun h => huv_ne (iso.toEquiv.injective h)
  have hevu_ne : iso.toEquiv v ≠ iso.toEquiv u := fun h => heuv_ne h.symm
  refine ⟨iso.toEquiv u, iso.toEquiv v, (iso.adj_iff.mp huv), ?_, ?_⟩
  · simpa [mapDistribution] using hD
  · funext w
    by_cases hwu : w = iso.toEquiv u
    · subst w
      simp [mapDistribution, Pebbling.moveDistribution]
    · by_cases hwv : w = iso.toEquiv v
      · subst w
        simp [mapDistribution, Pebbling.moveDistribution, hvu_ne, hevu_ne]
      · have hsymm_u : iso.toEquiv.symm w ≠ u := by
          intro h
          exact hwu (by
            calc
              w = iso.toEquiv (iso.toEquiv.symm w) := by simp
              _ = iso.toEquiv u := by rw [h])
        have hsymm_v : iso.toEquiv.symm w ≠ v := by
          intro h
          exact hwv (by
            calc
              w = iso.toEquiv (iso.toEquiv.symm w) := by simp
              _ = iso.toEquiv v := by rw [h])
        simp [mapDistribution, Pebbling.moveDistribution, hwu, hwv, hsymm_u, hsymm_v]

theorem map_reaches [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {D E : Pebbling V}
    (hreach : Pebbling.Reaches G D E) :
    Pebbling.Reaches H (iso.mapDistribution D) (iso.mapDistribution E) := by
  unfold Pebbling.Reaches at hreach ⊢
  refine hreach.head_induction_on ?refl ?head
  · exact Relation.ReflTransGen.refl
  · intro A B hmove _ ih
    exact Relation.ReflTransGen.head (iso.map_move hmove) ih

theorem map_canReachAtLeast [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {D : Pebbling V} {target : W} {T : ℕ}
    (hcan : Pebbling.CanReachAtLeast G D (iso.toEquiv.symm target) T) :
    Pebbling.CanReachAtLeast H (iso.mapDistribution D) target T := by
  rcases hcan with ⟨E, hreach, htarget⟩
  refine ⟨iso.mapDistribution E, iso.map_reaches hreach, ?_⟩
  simpa [mapDistribution] using htarget

theorem map_solvableAtLeast [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {D : Pebbling V} {T : ℕ}
    (hsolv : Pebbling.SolvableAtLeast G D T) :
    Pebbling.SolvableAtLeast H (iso.mapDistribution D) T := by
  intro target
  exact iso.map_canReachAtLeast (hsolv (iso.toEquiv.symm target))

theorem map_minOccupiedPileSize (iso : GraphIso G H) {D : Pebbling V} {S : ℕ}
    (hmin : Pebbling.MinOccupiedPileSize D S) :
    Pebbling.MinOccupiedPileSize (iso.mapDistribution D) S := by
  intro w hw
  exact hmin (iso.toEquiv.symm w) hw

theorem map_hasSolvableAtMostSize [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {T k : ℕ}
    (h : Pebbling.HasSolvableAtMostSize G T k) :
    Pebbling.HasSolvableAtMostSize H T k := by
  rcases h with ⟨D, hsize, hsolv⟩
  refine ⟨iso.mapDistribution D, ?_, iso.map_solvableAtLeast hsolv⟩
  simpa [iso.size_mapDistribution D] using hsize

end GraphIso

end PebblingLean
