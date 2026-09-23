/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Incidence counts in finite simple graphs -/

@[expose] public section

namespace ACMax

open Classical in
/-- **Bipartite double count** (generic-`V` port of `cross_count_nineteen`): for any two
vertex sets, the `X→Y` incidences equal the `Y→X` incidences.  The `DecidableEq` binder
lets the lemma instantiate to whichever instance the call site elaborated with
(`instDecidableEqFin` at `Fin n`, `Classical.propDecidable` at generic `V`). -/
theorem cross_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X Y : Finset V) :
    ∑ v ∈ X, (G.neighborFinset v ∩ Y).card = ∑ w ∈ Y, (G.neighborFinset w ∩ X).card := by
  have hL : ∀ v : V, (G.neighborFinset v ∩ Y).card
      = ∑ w ∈ Y, (if G.Adj v w then 1 else 0) := by
    intro v
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun w _ => by simp only [G.mem_neighborFinset])
  have hR : ∀ w : V, (G.neighborFinset w ∩ X).card
      = ∑ v ∈ X, (if G.Adj v w then 1 else 0) := by
    intro w
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl
      (fun v _ => by simp only [G.mem_neighborFinset, SimpleGraph.adj_comm])
  simp_rw [hL, hR]
  exact Finset.sum_comm

open Classical in
/-- A weighted adjacency sum supported on one pair is its contribution at that pair. -/
theorem sum_adj_eq_single {V R : Type*} [AddCommMonoid R] (G : SimpleGraph V)
    (A B : Finset V) (a b : V) (weight : V → V → R) (ha : a ∈ A) (hb : b ∈ B)
    (hsupport : ∀ i ∈ A, ∀ j ∈ B, G.Adj i j → i = a ∧ j = b) :
    (∑ i ∈ A, ∑ j ∈ B, if G.Adj i j then weight i j else 0) =
      if G.Adj a b then weight a b else 0 := by
  classical
  calc
    _ = ∑ j ∈ B, if G.Adj a j then weight a j else 0 := by
      apply Finset.sum_eq_single a
      · intro i hi hne
        apply Finset.sum_eq_zero
        intro j hj
        exact ite_eq_right fun hij => hne (hsupport i hi j hj hij).1
      · intro hnot
        exact (hnot ha).elim
    _ = if G.Adj a b then weight a b else 0 := by
      apply Finset.sum_eq_single b
      · intro j hj hne
        exact ite_eq_right fun haj => hne (hsupport a ha j hj haj).2
      · intro hnot
        exact (hnot hb).elim

end ACMax
