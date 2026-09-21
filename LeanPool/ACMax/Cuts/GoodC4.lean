/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import Mathlib.Tactic.Ring
import LeanPool.ACMax.Spectral.AlgConn
import LeanPool.ACMax.Cuts.WeightedCut

/-!
# The "good `C₄`" certificate

An induced 4-cycle `a–b–c–d–a` (with `a ≁ c`, `b ≁ d`) whose four vertices have small total degree
is a sparse weighted cut: each cycle vertex has exactly two neighbours inside `{a,b,c,d}`, so the
cut value is `∑ deg − 8`, and the weighted-cut inequality `n · (∑deg − 8) ≤ 2·4·(n−4)` certifies
`algConn G ≤ 2`.  This complements the "good triangle" certificate and, since `C₄` is `2K₂`-free,
applies in the no-`2K₂` regime where the induced-`2K₂` method fails.
-/

namespace ACMax

open Classical in
/-- An induced `C₄` on `{a,b,c,d}` with `n · (∑deg − 8) ≤ 2·4·(n−4)` certifies `algConn G ≤ 2`. -/
theorem algConn_le_two_of_good_C4 {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (a b c d : V)
    (hcard : ({a, b, c, d} : Finset V).card = 4) (hn : 5 ≤ Fintype.card V)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d)
    (hcut : Fintype.card V *
        ((G.degree a + G.degree b + G.degree c + G.degree d) - 8)
      ≤ 2 * (4 * (Fintype.card V - 4))) :
    algConn G ≤ 2 := by
  classical
  -- Distinctness: `a ∉ {b,c,d}` and `b ∉ {c,d}` from `hcard`, hence `a ≠ c`, `b ≠ d`.  Each literal
  -- `3`-element set has card `≤ 3`, so any coincidence would contradict `hcard = 4`.
  have card3le : ∀ x y z : V, ({x, y, z} : Finset V).card ≤ 3 := by
    intro x y z
    calc ({x, y, z} : Finset V).card
        ≤ ({y, z} : Finset V).card + 1 := Finset.card_insert_le _ _
      _ ≤ (({z} : Finset V).card + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ = 3 := by simp
  have h1 : a ∉ ({b, c, d} : Finset V) := by
    intro h; rw [Finset.insert_eq_self.mpr h] at hcard; have := card3le b c d; omega
  have h2 : b ∉ ({c, d} : Finset V) := by
    intro h; rw [Finset.insert_eq_self.mpr h] at hcard; have := card3le a c d; omega
  have hac_ne : a ≠ c := fun h => h1 (by rw [h]; simp)
  have hbd_ne : b ≠ d := fun h => h2 (by rw [h]; simp)
  set A : Finset V := ({a, b, c, d} : Finset V) with hAdef
  -- Each cycle vertex meets `A` in exactly its two cycle-neighbours.
  have interA : (G.neighborFinset a ∩ A).card = 2 := by
    have hset : G.neighborFinset a ∩ A = {b, d} := by
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, hAdef,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨haw, rfl | rfl | rfl | rfl⟩
        · exact (G.irrefl haw).elim
        · exact Or.inl rfl
        · exact (hac haw).elim
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hab, Or.inr (Or.inl rfl)⟩
        · exact ⟨hda.symm, Or.inr (Or.inr (Or.inr rfl))⟩
    rw [hset, Finset.card_pair hbd_ne]
  have interB : (G.neighborFinset b ∩ A).card = 2 := by
    have hset : G.neighborFinset b ∩ A = {a, c} := by
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, hAdef,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hbw, rfl | rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact (G.irrefl hbw).elim
        · exact Or.inr rfl
        · exact (hbd hbw).elim
      · rintro (rfl | rfl)
        · exact ⟨hab.symm, Or.inl rfl⟩
        · exact ⟨hbc, Or.inr (Or.inr (Or.inl rfl))⟩
    rw [hset, Finset.card_pair hac_ne]
  have interC : (G.neighborFinset c ∩ A).card = 2 := by
    have hset : G.neighborFinset c ∩ A = {b, d} := by
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, hAdef,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hcw, rfl | rfl | rfl | rfl⟩
        · exact (hac hcw.symm).elim
        · exact Or.inl rfl
        · exact (G.irrefl hcw).elim
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hbc.symm, Or.inr (Or.inl rfl)⟩
        · exact ⟨hcd, Or.inr (Or.inr (Or.inr rfl))⟩
    rw [hset, Finset.card_pair hbd_ne]
  have interD : (G.neighborFinset d ∩ A).card = 2 := by
    have hset : G.neighborFinset d ∩ A = {a, c} := by
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, hAdef,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hdw, rfl | rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact (hbd hdw.symm).elim
        · exact Or.inr rfl
        · exact (G.irrefl hdw).elim
      · rintro (rfl | rfl)
        · exact ⟨hda, Or.inl rfl⟩
        · exact ⟨hcd.symm, Or.inr (Or.inr (Or.inl rfl))⟩
    rw [hset, Finset.card_pair hac_ne]
  -- Hence each cycle vertex sends `deg − 2` edges out of `A`.
  have sd : ∀ (w : V), (G.neighborFinset w ∩ A).card = 2 →
      (G.neighborFinset w \ A).card + 2 = G.degree w := by
    intro w hk
    have h := Finset.card_sdiff_add_card_inter (G.neighborFinset w) A
    rw [hk, G.card_neighborFinset_eq_degree] at h; exact h
  have sdA := sd a interA
  have sdB := sd b interB
  have sdC := sd c interC
  have sdD := sd d interD
  -- The cut value is `∑ deg − 8`.
  have cutEq : ∑ v ∈ A, (G.neighborFinset v \ A).card
      = (G.neighborFinset a \ A).card + (G.neighborFinset b \ A).card
        + (G.neighborFinset c \ A).card + (G.neighborFinset d \ A).card := by
    rw [hAdef, Finset.sum_insert h1, Finset.sum_insert h2,
        Finset.sum_insert (by simp [hcd.ne] : c ∉ ({d} : Finset V)), Finset.sum_singleton]
    ring
  have cutSum : ∑ v ∈ A, (G.neighborFinset v \ A).card
      = (G.degree a + G.degree b + G.degree c + G.degree d) - 8 := by
    rw [cutEq]; omega
  -- Cardinalities of the two parts.
  have hAccard : Aᶜ.card = Fintype.card V - 4 := by rw [Finset.card_compl, hcard]
  have hA : A.Nonempty := ⟨a, by simp [hAdef]⟩
  have hAc : Aᶜ.Nonempty := by rw [← Finset.card_pos, hAccard]; omega
  -- Apply the weighted-cut certificate.
  refine algConn_le_two_of_weighted_cut G A hA hAc ?_
  rw [cutSum, hcard, hAccard]
  exact hcut

end ACMax
