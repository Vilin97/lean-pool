/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Tauto
public import LeanPool.ACMax.Spectral.AlgConn
public import LeanPool.ACMax.Cuts.SignedCut

/-!
# Induced-`2K₂` certificate

An **induced `2K₂`** — two disjoint edges `a–b`, `c–d` with no edges between `{a,b}`
and `{c,d}` — whose four endpoints have total degree `≤ 12` certifies `algConn G ≤ 2`.

This is the `{-1,0,1}` signed certificate with `P = {a,b}`, `N = {c,d}`: there are no
`P`–`N` edges (`e(P,N)=0`), and the boundary to the neutral set is
`e(P,Z) + e(N,Z) = (deg a + deg b − 2) + (deg c + deg d − 2) = degsum − 4 ≤ 8 = 4|P|`.

Equivalently (Cauchy interlacing on the complement): the four vertices induce a `C₄`
in `Gᶜ`, whose `4×4` Laplacian block `dI − A(C₄)` has `λ_max = d + 2`, forcing
`λ_max(L(Gᶜ)) ≥ n − 2`, i.e. `λ₂(G) ≤ 2`.  For four degree-3 vertices the bound is
tight (`degsum = 12`), which is exactly what certifies the `n = 9` Fiedler-eigenvector
graphs that no `±1` cut can.
-/

@[expose] public section

namespace ACMax

open Classical in
/-- An induced `2K₂` (`a–b`, `c–d`, no cross edges) on four distinct vertices of total
degree `≤ 12` gives `algConn G ≤ 2`. -/
theorem algConn_le_two_of_ind_2K2 {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (a b c d : V)
    (hdist : ({a, b, c, d} : Finset V).card = 4)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (had : ¬ G.Adj a d) (hbc : ¬ G.Adj b c) (hbd : ¬ G.Adj b d)
    (hdeg : G.degree a + G.degree b + G.degree c + G.degree d ≤ 12) :
    algConn G ≤ 2 := by
  classical
  have cardle : ∀ w x y : V, ({w, x, y} : Finset V).card ≤ 3 := by
    intro w x y
    calc ({w, x, y} : Finset V).card ≤ ({x, y} : Finset V).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (({y} : Finset V).card + 1) + 1 := by
          gcongr
          exact Finset.card_insert_le _ _
      _ = 3 := by simp
  -- Any coincidence among `a, b, c, d` would collapse `{a,b,c,d}` into a `3`-element set (card `≤
  -- 3`
  -- by `cardle`), contradicting `hcard = 4`; `collapse` packages that contradiction.
  have collapse : ∀ p q r : V, ({a, b, c, d} : Finset V) ⊆ {p, q, r} → False := by
    intro p q r hsub
    have := (Finset.card_le_card hsub).trans (cardle p q r); omega
  have hab' : a ≠ b := by
    rintro rfl
    exact collapse a c d (by intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  have hac' : a ≠ c := by
    rintro rfl
    exact collapse a b d (by intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  have had' : a ≠ d := by
    rintro rfl
    exact collapse a b c (by intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  have hbc' : b ≠ c := by
    rintro rfl
    exact collapse a b d (by intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  have hbd' : b ≠ d := by
    rintro rfl
    exact collapse a b c (by intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  have hcd' : c ≠ d := by
    rintro rfl
    exact collapse a b c (by intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  have hPN : ({a, b} : Finset V) ∪ {c, d} = {a, b, c, d} := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  -- The two cross-edge intersections are empty.
  have ha_inter0 : G.neighborFinset a ∩ ({c, d} : Finset V) = ∅ := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
    rintro ⟨hadj, (rfl | rfl)⟩
    · exact hac hadj
    · exact had hadj
  have hb_inter0 : G.neighborFinset b ∩ ({c, d} : Finset V) = ∅ := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
    rintro ⟨hadj, (rfl | rfl)⟩
    · exact hbc hadj
    · exact hbd hadj
  -- Each vertex meets `{a,b,c,d}` in exactly its partner.
  have ha_int4 : G.neighborFinset a ∩ ({a, b, c, d} : Finset V) = {b} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hadj, (rfl | rfl | rfl | rfl)⟩
      · exact absurd rfl (G.ne_of_adj hadj)
      · rfl
      · exact absurd hadj hac
      · exact absurd hadj had
    · rintro rfl; exact ⟨hab, Or.inr (Or.inl rfl)⟩
  have hb_int4 : G.neighborFinset b ∩ ({a, b, c, d} : Finset V) = {a} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hadj, (rfl | rfl | rfl | rfl)⟩
      · rfl
      · exact absurd rfl (G.ne_of_adj hadj)
      · exact absurd hadj hbc
      · exact absurd hadj hbd
    · rintro rfl; exact ⟨hab.symm, Or.inl rfl⟩
  have hc_int4 : G.neighborFinset c ∩ ({a, b, c, d} : Finset V) = {d} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hadj, (rfl | rfl | rfl | rfl)⟩
      · exact absurd hadj.symm hac
      · exact absurd hadj.symm hbc
      · exact absurd rfl (G.ne_of_adj hadj)
      · rfl
    · rintro rfl; exact ⟨hcd, Or.inr (Or.inr (Or.inr rfl))⟩
  have hd_int4 : G.neighborFinset d ∩ ({a, b, c, d} : Finset V) = {c} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hadj, (rfl | rfl | rfl | rfl)⟩
      · exact absurd hadj.symm had
      · exact absurd hadj.symm hbd
      · rfl
      · exact absurd rfl (G.ne_of_adj hadj)
    · rintro rfl; exact ⟨hcd.symm, Or.inr (Or.inr (Or.inl rfl))⟩
  -- Boundary cardinalities: since each of the four vertices meets `{a,b,c,d}` in exactly one
  -- vertex (its partner), it sends `deg − 1` edges out: `(N(v) \ {a,b,c,d}).card + 1 = deg v`.
  have ee : ∀ (w z : V), G.neighborFinset w ∩ ({a, b, c, d} : Finset V) = {z} →
      (G.neighborFinset w \ ({a, b, c, d} : Finset V)).card + 1 = G.degree w := by
    intro w z hz
    have h := Finset.card_sdiff_add_card_inter (G.neighborFinset w) ({a, b, c, d} : Finset V)
    rw [hz, Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree] at h
    exact h
  have ea := ee a b ha_int4
  have eb := ee b a hb_int4
  have ec := ee c d hc_int4
  have ed := ee d c hd_int4
  refine algConn_le_two_of_signed G {a, b} {c, d} ?_ ?_ ?_ ?_
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
    · exact hac' rfl
    · exact had' rfl
    · exact hbc' rfl
    · exact hbd' rfl
  · rw [Finset.card_pair hab', Finset.card_pair hcd']
  · rw [Finset.card_pair hab']; norm_num
  · rw [hPN, Finset.sum_pair hab', Finset.sum_pair hab', Finset.sum_pair hcd',
      Finset.card_pair hab', ha_inter0, hb_inter0, Finset.card_empty]
    omega

end ACMax
