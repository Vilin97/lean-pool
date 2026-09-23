/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.Ring
public import LeanPool.ACMax.Spectral.AlgConn
public import LeanPool.ACMax.Cuts.WeightedCut

/-!
# The "good `K_{2,3}`" certificate

An induced `K_{2,3}` (parts `{a,b}` and `{c,d,e}`, complete between, no edges inside parts) is a
weighted cut on 5 vertices with 6 internal edges: each of `a,b` has 3 neighbours inside, each of
`c,d,e` has 2, so the cut value is `∑deg − 12`.  The weighted-cut inequality
`n · (∑deg − 12) ≤ 2·5·(n−5)` certifies `algConn G ≤ 2`.

This is the dedicated cut for the `n = 12` sparse-hub residual that good `C₄` misses: a `K_{2,3}`
with two degree-4 vertices on the small side has `C₄`s of degree-sum `14 > 13` (not a good `C₄`),
yet the denser 5-vertex set still yields `cut = 5`.
-/

@[expose] public section

namespace ACMax

open Classical in
/-- An induced `K_{2,3}` with `n · (∑deg − 12) ≤ 2·5·(n−5)` certifies `algConn G ≤ 2`. -/
theorem algConn_le_two_of_good_K23 {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (a b c d e : V)
    (hcard : ({a, b, c, d, e} : Finset V).card = 5) (hn : 6 ≤ Fintype.card V)
    (hac : G.Adj a c) (had : G.Adj a d) (hae : G.Adj a e)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hbe : G.Adj b e)
    (hab : ¬ G.Adj a b) (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e) (hde : ¬ G.Adj d e)
    (hcut : Fintype.card V *
        ((G.degree a + G.degree b + G.degree c + G.degree d + G.degree e) - 12)
      ≤ 2 * (5 * (Fintype.card V - 5))) :
    algConn G ≤ 2 := by
  classical
  -- Distinctness of the five vertices, extracted from `hcard`: every literal `4`-element set has
  -- card `≤ 4`, so collapsing any coincidence in `{a,b,c,d,e}` would contradict `hcard = 5`.
  have card4le : ∀ w x y z : V, ({w, x, y, z} : Finset V).card ≤ 4 := by
    intro w x y z
    calc ({w, x, y, z} : Finset V).card
        ≤ ({x, y, z} : Finset V).card + 1 := Finset.card_insert_le _ _
      _ ≤ (({y, z} : Finset V).card + 1) + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ ≤ ((({z} : Finset V).card + 1) + 1) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
      _ = 4 := by simp
  have h1 : a ∉ ({b, c, d, e} : Finset V) := by
    intro h; rw [Finset.insert_eq_self.mpr h] at hcard; have := card4le b c d e; omega
  have h2 : b ∉ ({c, d, e} : Finset V) := by
    intro h; rw [Finset.insert_eq_self.mpr h] at hcard; have := card4le a c d e; omega
  have h3 : c ∉ ({d, e} : Finset V) := by
    intro h; rw [Finset.insert_eq_self.mpr h] at hcard; have := card4le a b d e; omega
  have h4 : d ∉ ({e} : Finset V) := by
    intro h; rw [Finset.insert_eq_self.mpr h] at hcard; have := card4le a b c e; omega
  have hab_ne : a ≠ b := fun h => h1 (by rw [h]; simp)
  have hde_ne : d ≠ e := Finset.notMem_singleton.mp h4
  set A : Finset V := ({a, b, c, d, e} : Finset V) with hAdef
  -- Card of the three-element neighbour set `{c, d, e}` and the part `{a, b}`.
  have hcde : ({c, d, e} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem h3, Finset.card_pair hde_ne]
  -- `a` and `b` each meet `A` in `{c, d, e}` (their three neighbours).
  have interA : (G.neighborFinset a ∩ A).card = 3 := by
    have hset : G.neighborFinset a ∩ A = {c, d, e} := by
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, hAdef,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨haw, rfl | rfl | rfl | rfl | rfl⟩
        · exact (G.irrefl haw).elim
        · exact (hab haw).elim
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · rintro (rfl | rfl | rfl)
        · exact ⟨hac, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨had, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
        · exact ⟨hae, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
    rw [hset, hcde]
  have interB : (G.neighborFinset b ∩ A).card = 3 := by
    have hset : G.neighborFinset b ∩ A = {c, d, e} := by
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, hAdef,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hbw, rfl | rfl | rfl | rfl | rfl⟩
        · exact (hab hbw.symm).elim
        · exact (G.irrefl hbw).elim
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · rintro (rfl | rfl | rfl)
        · exact ⟨hbc, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨hbd, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
        · exact ⟨hbe, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
    rw [hset, hcde]
  -- `c`, `d`, `e` each meet `A` in `{a, b}`.
  have interC : (G.neighborFinset c ∩ A).card = 2 := by
    have hset : G.neighborFinset c ∩ A = {a, b} := by
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, hAdef,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hcw, rfl | rfl | rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (G.irrefl hcw).elim
        · exact (hcd hcw).elim
        · exact (hce hcw).elim
      · rintro (rfl | rfl)
        · exact ⟨hac.symm, Or.inl rfl⟩
        · exact ⟨hbc.symm, Or.inr (Or.inl rfl)⟩
    rw [hset, Finset.card_pair hab_ne]
  have interD : (G.neighborFinset d ∩ A).card = 2 := by
    have hset : G.neighborFinset d ∩ A = {a, b} := by
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, hAdef,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hdw, rfl | rfl | rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hcd hdw.symm).elim
        · exact (G.irrefl hdw).elim
        · exact (hde hdw).elim
      · rintro (rfl | rfl)
        · exact ⟨had.symm, Or.inl rfl⟩
        · exact ⟨hbd.symm, Or.inr (Or.inl rfl)⟩
    rw [hset, Finset.card_pair hab_ne]
  have interE : (G.neighborFinset e ∩ A).card = 2 := by
    have hset : G.neighborFinset e ∩ A = {a, b} := by
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, hAdef,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hew, rfl | rfl | rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hce hew.symm).elim
        · exact (hde hew.symm).elim
        · exact (G.irrefl hew).elim
      · rintro (rfl | rfl)
        · exact ⟨hae.symm, Or.inl rfl⟩
        · exact ⟨hbe.symm, Or.inr (Or.inl rfl)⟩
    rw [hset, Finset.card_pair hab_ne]
  -- Hence each vertex sends `deg − (inter card)` edges out of `A`.
  have sd : ∀ (w : V) (k : ℕ), (G.neighborFinset w ∩ A).card = k →
      (G.neighborFinset w \ A).card + k = G.degree w := by
    intro w k hk
    have h := Finset.card_sdiff_add_card_inter (G.neighborFinset w) A
    rw [hk, G.card_neighborFinset_eq_degree] at h; exact h
  have sdA := sd a 3 interA
  have sdB := sd b 3 interB
  have sdC := sd c 2 interC
  have sdD := sd d 2 interD
  have sdE := sd e 2 interE
  -- The cut value is `∑ deg − 12`.
  have cutEq : ∑ v ∈ A, (G.neighborFinset v \ A).card
      = (G.neighborFinset a \ A).card + (G.neighborFinset b \ A).card
        + (G.neighborFinset c \ A).card + (G.neighborFinset d \ A).card
        + (G.neighborFinset e \ A).card := by
    rw [hAdef, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
        Finset.sum_insert h4, Finset.sum_singleton]
    ring
  have cutSum : ∑ v ∈ A, (G.neighborFinset v \ A).card
      = (G.degree a + G.degree b + G.degree c + G.degree d + G.degree e) - 12 := by
    rw [cutEq]; omega
  -- Cardinalities of the two parts.
  have hAccard : Aᶜ.card = Fintype.card V - 5 := by rw [Finset.card_compl, hcard]
  have hA : A.Nonempty := ⟨a, by simp [hAdef]⟩
  have hAc : Aᶜ.Nonempty := by rw [← Finset.card_pos, hAccard]; omega
  -- Apply the weighted-cut certificate.
  refine algConn_le_two_of_weighted_cut G A hA hAc ?_
  rw [cutSum, hcard, hAccard]
  exact hcut

end ACMax
