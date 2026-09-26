/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The internal-degree sum of a vertex set is even

For any finite simple graph `G` and vertex set `s`, the sum over `v ∈ s` of the number of
neighbours of `v` lying in `s` equals twice the number of edges internal to `s`, hence is even.
-/

public section

namespace ACMax

open Classical in
/-- `∑_{v ∈ s} |N(v) ∩ s|` is even (it counts each internal edge twice). -/
theorem sum_inDegree_even {V : Type*} [Fintype V] (G : SimpleGraph V) (s : Finset V) :
    Even (∑ v ∈ s, (G.neighborFinset v ∩ s).card) := by
  classical
  set T : Finset (V × V) := (s ×ˢ s).filter (fun p => G.Adj p.1 p.2) with hT
  have hsum : (∑ v ∈ s, (G.neighborFinset v ∩ s).card) = T.card := by
    rw [hT, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [SimpleGraph.mem_neighborFinset]
  rw [hsum, ← ZMod.natCast_eq_zero_iff_even]
  have hmem : ∀ p, p ∈ T → Prod.swap p ∈ T := by
    intro p hp
    simp only [hT, Finset.mem_filter, Finset.mem_product, Prod.fst_swap, Prod.snd_swap] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
  have hsum1 : ∑ _p ∈ T, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun p _ => Prod.swap p) (fun _ _ => by decide)
      (fun p hp _ => by
        have hadj : G.Adj p.1 p.2 := by
          simp only [hT, Finset.mem_filter] at hp
          exact hp.2
        intro heq
        apply G.ne_of_adj hadj
        have h := Prod.ext_iff.mp heq
        simp only [Prod.fst_swap, Prod.snd_swap] at h
        exact h.2)
      (fun p hp => hmem p hp) (fun _ _ => Prod.swap_swap _)
  calc (T.card : ZMod 2) = ∑ _p ∈ T, (1 : ZMod 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = 0 := hsum1

end ACMax
