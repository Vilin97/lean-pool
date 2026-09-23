/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import LeanPool.ACMax.Spectral.AlgConn

/-!
# A triangle-free graph of small degree on enough vertices has an induced `2K₂`

General combinatorial lemma (reusable across `n`): if a vertex set `D` induces a
triangle-free subgraph of `G` with every `D`-vertex having between `1` and `3`
neighbours inside `D`, and `|D| ≥ 7`, then `D` contains an induced `2K₂` — two
disjoint edges with no edges between them.

Reason: a `2K₂`-free triangle-free graph with no isolated vertex is connected; among such
graphs of maximum degree `≤ 3` the largest has exactly `7` vertices (a `C₅`-based
extremal example exists, verified by exhaustive search; every such graph on `≥ 8`
vertices contains an induced `2K₂`).  Hence `|D| ≥ 8` forces an induced `2K₂`.

NOTE: the threshold is `8`, not `7` — there is an explicit triangle-free, max-degree-3,
`2K₂`-free graph on `7` vertices (containing an induced `C₅`).
-/

@[expose] public section

namespace ACMax

open Classical in
private theorem exists_induced_2K2_of_triangleFree_smalldeg_hdom.{u_1} : ∀ {V : Type u_1} [Fintype
  V] (G : SimpleGraph V)
  (D : Finset V) (_ : ∀ a ∈ D, 1 ≤ (G.neighborFinset a ∩ D).card)
  (_ :
    ∀ (a b c d : V),
      a ∈ D →
        b ∈ D →
          c ∈ D →
            d ∈ D →
              (Finset.card {a, b, c, d}) = 4 → G.Adj a b → G.Adj c d → ¬G.Adj a c → ¬G.Adj a d →
                ¬G.Adj b c → ¬G.Adj b d → False)
  (_ : ∀ (p q r s : V), p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s → (Finset.card {p, q, r, s})
    = 4)
  (_ : ∀ (v z : V), z ∈ G.neighborFinset v ∩ D ↔ G.Adj v z ∧ z ∈ D) (x : V) (_ : x ∈ D),
  let Δ := (G.neighborFinset x ∩ D).card;
  ∀ (_ : ∀ x' ∈ D, (G.neighborFinset x' ∩ D).card ≤ Δ),
    ∀ z ∈ D, z = x ∨ z ∈ G.neighborFinset x ∩ D ∨ ∃ a ∈ G.neighborFinset x ∩ D, G.Adj z a := by
  classical
  intro V inst G D hmin key card4 hmemND x hxD Δ hxmax z hzD
  by_contra hcon
  push Not at hcon
  obtain ⟨hzx, hzNx, hzfar⟩ := hcon
  -- `z` has an in-`D` neighbour `z'`.
  obtain ⟨z', hz'⟩ : (G.neighborFinset z ∩ D).Nonempty :=
    Finset.card_pos.mp (by have := hmin z hzD; omega)
  rw [hmemND] at hz'
  obtain ⟨hzz', hz'D⟩ := hz'
  -- `z ∈ Nᴰ z'` while `z ∉ Nᴰ x`, and `Nᴰ z'` has at most `Δ` elements: so some
  -- `a ∈ Nᴰ x` is not in `Nᴰ z'`.
  have hzin : z ∈ G.neighborFinset z' ∩ D := (hmemND z' z).mpr ⟨hzz'.symm, hzD⟩
  have hsubset : ¬ (G.neighborFinset x ∩ D ⊆ G.neighborFinset z' ∩ D) := by
    intro hsub
    have hins : insert z (G.neighborFinset x ∩ D) ⊆ G.neighborFinset z' ∩ D :=
      Finset.insert_subset hzin hsub
    have hcardins : (insert z (G.neighborFinset x ∩ D)).card = Δ + 1 := by
      rw [Finset.card_insert_of_notMem hzNx]
    have := Finset.card_le_card hins
    have hle : (G.neighborFinset z' ∩ D).card ≤ Δ := hxmax z' hz'D
    omega
  obtain ⟨a, haNx, haz'⟩ := Finset.not_subset.mp hsubset
  rw [hmemND] at haNx
  obtain ⟨hxa, haD⟩ := haNx
  have haz'' : ¬ G.Adj z' a := by
    intro h; exact haz' ((hmemND z' a).mpr ⟨h, haD⟩)
  -- Build the induced `2K₂` on `{x, a, z, z'}`.
  have hxz : ¬ G.Adj x z := fun h => hzNx ((hmemND x z).mpr ⟨h, hzD⟩)
  have hxz' : ¬ G.Adj x z' := by
    intro h
    exact hzfar z' ((hmemND x z').mpr ⟨h, hz'D⟩) hzz'
  have haz : ¬ G.Adj a z := by
    intro h
    exact hzfar a ((hmemND x a).mpr ⟨hxa, haD⟩) h.symm
  have haz'3 : ¬ G.Adj a z' := fun h => haz'' h.symm
  have hxane : x ≠ a := by rintro rfl; exact G.irrefl hxa
  have hxzne : x ≠ z := fun h => hzx h.symm
  have hxz'ne : x ≠ z' := by rintro rfl; exact hxz hzz'.symm
  have hazne : a ≠ z := by rintro rfl; exact hxz hxa
  have haz'ne : a ≠ z' := by rintro rfl; exact hxz' hxa
  have hzz'ne : z ≠ z' := by rintro rfl; exact G.irrefl hzz'
  exact key x a z z' hxD haD hzD hz'D
    (card4 x a z z' hxane hxzne hxz'ne hazne haz'ne hzz'ne)
    hxa hzz' hxz hxz' haz haz'3

open Classical in
private theorem exists_induced_2K2_of_triangleFree_smalldeg_hDsub.{u_1} : ∀ {V : Type u_1}
  [Fintype V]
  (G : SimpleGraph V) (D : Finset V) (x : V) (_ : x ∈ D) (Δ : ℕ)
  (_ : ∀ x' ∈ D, (G.neighborFinset x' ∩ D).card ≤ Δ) (_ : Δ = (G.neighborFinset x ∩ D).card) (_ :
    Δ ≤ 3)
  (_ : ∀ z ∈ D, z = x ∨ z ∈ G.neighborFinset x ∩ D ∨ ∃ a ∈ G.neighborFinset x ∩ D, G.Adj z a)
  (_ : ∀ a ∈ G.neighborFinset x ∩ D, ∀ b ∈ G.neighborFinset x ∩ D, a ≠ b → ¬G.Adj a b),
  let B := {z ∈ D | ∃ a ∈ G.neighborFinset x ∩ D, G.Adj z a} \ insert x (G.neighborFinset x ∩ D);
  ∀ (_ : B = {z ∈ D | ∃ a ∈ G.neighborFinset x ∩ D, G.Adj z a} \ insert x (G.neighborFinset x ∩ D)),
    D ⊆ insert x (G.neighborFinset x ∩ D ∪ B) := by
  classical
  intro V inst G D x hxD Δ hxmax hΔdef hΔ3 hdom hindNx B hBdef z hzD
  by_cases hz : z ∈ insert x (G.neighborFinset x ∩ D)
  · rw [Finset.mem_insert] at hz
    rcases hz with rfl | hzNx
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hzNx)
  · rw [Finset.mem_insert] at hz
    push Not at hz
    obtain ⟨hzx, hzNx⟩ := hz
    rcases hdom z hzD with h | h | ⟨a, haNx, hza⟩
    · exact absurd h hzx
    · exact absurd h hzNx
    · refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
      rw [hBdef, Finset.mem_sdiff]
      refine ⟨Finset.mem_filter.mpr ⟨hzD, a, haNx, hza⟩, ?_⟩
      rw [Finset.mem_insert]; push Not; exact ⟨hzx, hzNx⟩

open Classical in
private theorem exists_induced_2K2_of_triangleFree_smalldeg_hBa.{u_1} : ∀ {V : Type u_1} [Fintype
  V] (G : SimpleGraph V)
  (D : Finset V) (x : V) (_ : x ∈ D) (Δ : ℕ) (_ : ∀ x' ∈ D, (G.neighborFinset x' ∩ D).card ≤ Δ) (_
    : Δ ≤ 3),
  let B := {z ∈ D | ∃ a ∈ G.neighborFinset x ∩ D, G.Adj z a} \ insert x (G.neighborFinset x ∩ D);
  let Nx := G.neighborFinset x ∩ D;
  ∀ (_ : Δ = Nx.card) (_ : Nx = G.neighborFinset x ∩ D)
    (_ : ∀ b ∈ B, b ∈ D ∧ b ≠ x ∧ b ∉ Nx ∧ (G.neighborFinset b ∩ Nx).Nonempty)
    (_ : ∀ (b a : V), a ∈ G.neighborFinset b ∩ Nx ↔ G.Adj b a ∧ a ∈ Nx),
    ∀ a ∈ Nx, (Finset.card {b ∈ B | a ∈ G.neighborFinset b ∩ Nx}) ≤ Δ - 1 := by
  classical
  intro V inst G D x hxD Δ hxmax hΔ3 B Nx hΔdef hNx hBmem hcolmem a haNx
  have haD : a ∈ D := (Finset.mem_inter.mp (hNx ▸ haNx)).2
  have hxa : G.Adj x a := (G.mem_neighborFinset x a).mp (Finset.mem_inter.mp (hNx ▸ haNx)).1
  have hsub : B.filter (fun b => a ∈ G.neighborFinset b ∩ Nx) ⊆
      (G.neighborFinset a ∩ D).erase x := by
    intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hbB, hba⟩ := hb
    rw [hcolmem] at hba
    obtain ⟨hadj, _⟩ := hba
    obtain ⟨hbD, hbx, _, _⟩ := hBmem b hbB
    rw [Finset.mem_erase, Finset.mem_inter, G.mem_neighborFinset]
    exact ⟨hbx, hadj.symm, hbD⟩
  calc (B.filter (fun b => a ∈ G.neighborFinset b ∩ Nx)).card
      ≤ ((G.neighborFinset a ∩ D).erase x).card := Finset.card_le_card hsub
    _ = (G.neighborFinset a ∩ D).card - 1 := by
        rw [Finset.card_erase_of_mem]
        rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hxa.symm, hxD⟩
    _ ≤ Δ - 1 := by have := hxmax a haD; omega

open Classical in
private theorem exists_induced_2K2_of_triangleFree_smalldeg_hsumcol.{u_1} : ∀ {V : Type u_1}
  [Fintype V]
  (G : SimpleGraph V) (D : Finset V) (x : V) (Δ : ℕ),
  let B := {z ∈ D | ∃ a ∈ G.neighborFinset x ∩ D, G.Adj z a} \ insert x (G.neighborFinset x ∩ D);
  let Nx := G.neighborFinset x ∩ D;
  ∀ (_ : Δ = Nx.card) (_ : ∀ (b a : V), a ∈ G.neighborFinset b ∩ Nx ↔ G.Adj b a ∧ a ∈ Nx)
    (_ : ∀ a ∈ Nx, (Finset.card {b ∈ B | a ∈ G.neighborFinset b ∩ Nx}) ≤ Δ - 1),
    ∑ b ∈ B, (G.neighborFinset b ∩ Nx).card ≤ Δ * (Δ - 1) := by
  classical
  intro V inst G D x Δ B Nx hΔdef hcolmem hBa
  have hcard_eq : ∀ b : V, (G.neighborFinset b ∩ Nx).card
      = ∑ a ∈ Nx, (if a ∈ G.neighborFinset b then 1 else 0) := by
    intro b
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
  calc ∑ b ∈ B, (G.neighborFinset b ∩ Nx).card
      = ∑ b ∈ B, ∑ a ∈ Nx, (if a ∈ G.neighborFinset b then 1 else 0) := by
        simp_rw [hcard_eq]
    _ = ∑ a ∈ Nx, ∑ b ∈ B, (if a ∈ G.neighborFinset b then 1 else 0) := Finset.sum_comm
    _ = ∑ a ∈ Nx, (B.filter (fun b => a ∈ G.neighborFinset b)).card := by
        simp_rw [Finset.card_filter]
    _ ≤ ∑ a ∈ Nx, (Δ - 1) := by
        apply Finset.sum_le_sum
        intro a haNx
        have hfeq : B.filter (fun b => a ∈ G.neighborFinset b)
            = B.filter (fun b => a ∈ G.neighborFinset b ∩ Nx) := by
          apply Finset.filter_congr
          intro b _
          rw [hcolmem b a]
          simp [G.mem_neighborFinset, haNx]
        rw [hfeq]; exact hBa a haNx
    _ = Δ * (Δ - 1) := by
        rw [Finset.sum_const, smul_eq_mul, ← hΔdef]

open Classical in
private theorem exists_induced_2K2_of_triangleFree_smalldeg_hAdj.{u_1} : ∀ {V : Type u_1} [Fintype
  V] (G : SimpleGraph V)
  (D : Finset V)
  (_ :
    ∀ (a b c d : V),
      a ∈ D →
        b ∈ D →
          c ∈ D →
            d ∈ D →
              (Finset.card {a, b, c, d}) = 4 → G.Adj a b → G.Adj c d → ¬G.Adj a c → ¬G.Adj a d →
                ¬G.Adj b c → ¬G.Adj b d → False)
  (_ : ∀ (p q r s : V), p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s → (Finset.card {p, q, r, s})
    = 4) (x : V),
  let B := {z ∈ D | ∃ a ∈ G.neighborFinset x ∩ D, G.Adj z a} \ insert x (G.neighborFinset x ∩ D);
  ∀ (Nx : Finset V) (_ : ∀ a ∈ Nx, ∀ b ∈ Nx, a ≠ b → ¬G.Adj a b) (_ : Nx = G.neighborFinset x ∩ D)
    (_ : ∀ b ∈ B, b ∈ D ∧ b ≠ x ∧ b ∉ Nx ∧ (G.neighborFinset b ∩ Nx).Nonempty)
    (_ : ∀ (b a : V), a ∈ G.neighborFinset b ∩ Nx ↔ G.Adj b a ∧ a ∈ Nx),
    ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → Disjoint (G.neighborFinset b ∩ Nx) (G.neighborFinset b' ∩ Nx) →
      G.Adj b b' := by
  classical
  intro V inst G D key card4 x B Nx hindNx hNx hBmem hcolmem b hb b' hb' hbb' hdisj
  by_contra hnadj
  obtain ⟨hbD, hbx, hbNx, a, ha⟩ := hBmem b hb
  obtain ⟨hb'D, hb'x, hb'Nx, a', ha'⟩ := hBmem b' hb'
  rw [hcolmem] at ha ha'
  obtain ⟨hba, haNx⟩ := ha
  obtain ⟨hb'a', ha'Nx⟩ := ha'
  have haD : a ∈ D := (Finset.mem_inter.mp (hNx ▸ haNx)).2
  have ha'D : a' ∈ D := (Finset.mem_inter.mp (hNx ▸ ha'Nx)).2
  have haa' : a ≠ a' := by
    rintro rfl
    exact (Finset.disjoint_left.mp hdisj ((hcolmem b a).mpr ⟨hba, haNx⟩))
      ((hcolmem b' a).mpr ⟨hb'a', ha'Nx⟩)
  have hnaa' : ¬ G.Adj a a' := hindNx a haNx a' ha'Nx haa'
  have hnab' : ¬ G.Adj a b' := by
    intro h
    exact (Finset.disjoint_left.mp hdisj ((hcolmem b a).mpr ⟨hba, haNx⟩))
      ((hcolmem b' a).mpr ⟨h.symm, haNx⟩)
  have hnba' : ¬ G.Adj b a' := by
    intro h
    exact (Finset.disjoint_right.mp hdisj ((hcolmem b' a').mpr ⟨hb'a', ha'Nx⟩))
      ((hcolmem b a').mpr ⟨h, ha'Nx⟩)
  have hab : a ≠ b := fun h => hbNx (h ▸ haNx)
  have hab' : a ≠ b' := fun h => hb'Nx (h ▸ haNx)
  have ha'b : a' ≠ b := fun h => hbNx (h ▸ ha'Nx)
  have ha'b' : a' ≠ b' := fun h => hb'Nx (h ▸ ha'Nx)
  exact key a b a' b' haD hbD ha'D hb'D
    (card4 a b a' b' hab haa' hab' (Ne.symm ha'b) hbb' ha'b')
    hba.symm hb'a'.symm hnaa' hnab' hnba' hnadj

open Classical in
private theorem exists_induced_2K2_of_triangleFree_smalldeg_hUnion.{u_1} : ∀ {V : Type u_1}
  [Fintype V]
  (G : SimpleGraph V) (D : Finset V)
  (_ :
    ∀ (a b c d : V),
      a ∈ D →
        b ∈ D →
          c ∈ D →
            d ∈ D →
              (Finset.card {a, b, c, d}) = 4 → G.Adj a b → G.Adj c d → ¬G.Adj a c → ¬G.Adj a d →
                ¬G.Adj b c → ¬G.Adj b d → False)
  (_ : ∀ (p q r s : V), p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s → (Finset.card {p, q, r, s})
    = 4) (x : V)
  (_ : x ∈ D),
  let B := {z ∈ D | ∃ a ∈ G.neighborFinset x ∩ D, G.Adj z a} \ insert x (G.neighborFinset x ∩ D);
  ∀ (Nx : Finset V) (_ : Nx = G.neighborFinset x ∩ D)
    (_ : ∀ b ∈ B, b ∈ D ∧ b ≠ x ∧ b ∉ Nx ∧ (G.neighborFinset b ∩ Nx).Nonempty)
    (_ : ∀ (b a : V), a ∈ G.neighborFinset b ∩ Nx ↔ G.Adj b a ∧ a ∈ Nx),
    ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → G.Adj b b' → G.neighborFinset b ∩ Nx ∪ G.neighborFinset b' ∩ Nx =
      Nx := by
  classical
  intro V inst G D key card4 x hxD B Nx hNx hBmem hcolmem b hb b' hb' hbb' hadj
  apply Finset.Subset.antisymm
  · exact Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  · intro a haNx
    by_contra hni
    rw [Finset.mem_union] at hni
    push Not at hni
    obtain ⟨hnab, hnab'⟩ := hni
    obtain ⟨hbD, hbx, hbNx, _⟩ := hBmem b hb
    obtain ⟨hb'D, hb'x, hb'Nx, _⟩ := hBmem b' hb'
    have haD : a ∈ D := (Finset.mem_inter.mp (hNx ▸ haNx)).2
    have hxa : G.Adj x a := (G.mem_neighborFinset x a).mp (Finset.mem_inter.mp (hNx ▸ haNx)).1
    have hnxb : ¬ G.Adj x b := fun h =>
      hbNx (hNx ▸ Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x b).mpr h, hbD⟩)
    have hnxb' : ¬ G.Adj x b' := fun h =>
      hb'Nx (hNx ▸ Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x b').mpr h, hb'D⟩)
    have hnab2 : ¬ G.Adj a b := fun h => hnab ((hcolmem b a).mpr ⟨h.symm, haNx⟩)
    have hnab'2 : ¬ G.Adj a b' := fun h => hnab' ((hcolmem b' a).mpr ⟨h.symm, haNx⟩)
    have hxane : x ≠ a := fun h => G.irrefl (h ▸ hxa)
    have hxb : x ≠ b := fun h => hbx h.symm
    have hxb' : x ≠ b' := fun h => hb'x h.symm
    have hab : a ≠ b := fun h => hbNx (h ▸ haNx)
    have hab' : a ≠ b' := fun h => hb'Nx (h ▸ haNx)
    exact key x a b b' hxD haD hbD hb'D
      (card4 x a b b' hxane hxb hxb' hab hab' hbb') hxa hadj hnxb hnxb' hnab2 hnab'2

open Classical in
private theorem exists_induced_2K2_of_triangleFree_smalldeg_hdeg.{u_1} : ∀ {V : Type u_1} [Fintype
  V] (G : SimpleGraph V)
  (D : Finset V) (_ : ∀ a ∈ D, (G.neighborFinset a ∩ D).card ≤ 3) (x : V),
  let B := {z ∈ D | ∃ a ∈ G.neighborFinset x ∩ D, G.Adj z a} \ insert x (G.neighborFinset x ∩ D);
  ∀ (Nx : Finset V) (_ : Nx = G.neighborFinset x ∩ D)
    (_ : ∀ b ∈ B, b ∈ D ∧ b ≠ x ∧ b ∉ Nx ∧ (G.neighborFinset b ∩ Nx).Nonempty)
    (_ : ∀ (b a : V), a ∈ G.neighborFinset b ∩ Nx ↔ G.Adj b a ∧ a ∈ Nx),
    ∀ b ∈ B, (G.neighborFinset b ∩ Nx).card + (Finset.card {b' ∈ B | G.Adj b b'}) ≤ 3 := by
  classical
  intro V inst G D hmax x B Nx hNx hBmem hcolmem b hb
  obtain ⟨hbD, _, _, _⟩ := hBmem b hb
  have hdisj : Disjoint (G.neighborFinset b ∩ Nx) (B.filter (fun b' => G.Adj b b')) := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    have hcNx : c ∈ Nx := (Finset.mem_inter.mp hc).2
    have hcB : c ∈ B := (Finset.mem_filter.mp hc').1
    exact (hBmem c hcB).2.2.1 hcNx
  have hunion : (G.neighborFinset b ∩ Nx) ∪ (B.filter (fun b' => G.Adj b b'))
      ⊆ G.neighborFinset b ∩ D := by
    apply Finset.union_subset
    · intro c hc
      rw [hcolmem] at hc
      obtain ⟨hbc, hcNx⟩ := hc
      have hcD : c ∈ D := (Finset.mem_inter.mp (hNx ▸ hcNx)).2
      rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hbc, hcD⟩
    · intro c hc
      rw [Finset.mem_filter] at hc
      obtain ⟨hcB, hbc⟩ := hc
      rw [Finset.mem_inter, G.mem_neighborFinset]; exact ⟨hbc, (hBmem c hcB).1⟩
  calc (G.neighborFinset b ∩ Nx).card + (B.filter (fun b' => G.Adj b b')).card
      = ((G.neighborFinset b ∩ Nx) ∪ (B.filter (fun b' => G.Adj b b'))).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (G.neighborFinset b ∩ D).card := Finset.card_le_card hunion
    _ ≤ 3 := hmax b hbD

open Classical in
private theorem exists_induced_2K2_of_triangleFree_smalldeg_hall.{u_1} : ∀ {V : Type u_1} [Fintype
  V] (G : SimpleGraph V)
  (D : Finset V) (x : V) (Δ : ℕ),
  let B := {z ∈ D | ∃ a ∈ G.neighborFinset x ∩ D, G.Adj z a} \ insert x (G.neighborFinset x ∩ D);
  let Nx := G.neighborFinset x ∩ D;
  ∀ (_ : Δ = Nx.card) (_ : ∀ b ∈ B, b ∈ D ∧ b ≠ x ∧ b ∉ Nx ∧ (G.neighborFinset b ∩ Nx).Nonempty)
    (_ : Δ = 3)
    (_ : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → Disjoint (G.neighborFinset b ∩ Nx) (G.neighborFinset b' ∩ Nx)
      → G.Adj b b')
    (_ : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → G.Adj b b' → G.neighborFinset b ∩ Nx ∪ G.neighborFinset b' ∩
      Nx = Nx)
    (_ : ∀ b ∈ B, (G.neighborFinset b ∩ Nx).card + (Finset.card {b' ∈ B | G.Adj b b'}) ≤ 3) (b1 b2
      : V) (_ : b1 ≠ b2)
    (_ : b1 ∈ B) (_ : (G.neighborFinset b1 ∩ Nx).card = 1) (_ : b2 ∈ B)
    (_ : (G.neighborFinset b2 ∩ Nx).card = 1) (a₀ : V) (_ : G.neighborFinset b1 ∩ Nx = {a₀})
    (_ : G.neighborFinset b2 ∩ Nx = {a₀}), ∀ b ∈ B, a₀ ∈ G.neighborFinset b ∩ Nx := by
  classical
  intro V inst G D x Δ B Nx hΔdef hBmem hΔeq hAdj hUnion hdeg b1 b2 hb1b2 hb1B hb1card hb2B
    hb2card a₀ hcol1 hcol2 b hb
  by_contra hcon
  have hbb1 : b ≠ b1 := by
    rintro rfl; exact hcon (hcol1 ▸ Finset.mem_singleton_self a₀)
  have hbb2 : b ≠ b2 := by
    rintro rfl; exact hcon (hcol2 ▸ Finset.mem_singleton_self a₀)
  have hdisj1 : Disjoint (G.neighborFinset b ∩ Nx) (G.neighborFinset b1 ∩ Nx) := by
    rw [hcol1]; exact Finset.disjoint_singleton_right.mpr hcon
  have hdisj2 : Disjoint (G.neighborFinset b ∩ Nx) (G.neighborFinset b2 ∩ Nx) := by
    rw [hcol2]; exact Finset.disjoint_singleton_right.mpr hcon
  have hadj1 : G.Adj b b1 := hAdj b hb b1 hb1B hbb1 hdisj1
  have hadj2 : G.Adj b b2 := hAdj b hb b2 hb2B hbb2 hdisj2
  have hf1 : b1 ∈ B.filter (fun b' => G.Adj b b') := Finset.mem_filter.mpr ⟨hb1B, hadj1⟩
  have hf2 : b2 ∈ B.filter (fun b' => G.Adj b b') := Finset.mem_filter.mpr ⟨hb2B, hadj2⟩
  have hfcard : 2 ≤ (B.filter (fun b' => G.Adj b b')).card :=
    Finset.one_lt_card.mpr ⟨b1, hf1, b2, hf2, hb1b2⟩
  have hcolpos : 1 ≤ (G.neighborFinset b ∩ Nx).card :=
    Finset.card_pos.mpr (hBmem b hb).2.2.2
  have hdb := hdeg b hb
  have hcoleq : (G.neighborFinset b ∩ Nx).card = 1 := by omega
  obtain ⟨a', hcola'⟩ := Finset.card_eq_one.mp hcoleq
  have huni := hUnion b hb b1 hb1B hbb1 hadj1
  rw [hcola', hcol1] at huni
  have hle : Nx.card ≤ 2 := by
    rw [← huni]; exact le_trans (Finset.card_union_le _ _) (by simp)
  omega

open Classical in
/-- If `D` induces a triangle-free subgraph of `G` with in-`D` degrees in `[1,3]` and
`|D| ≥ 7`, then `D` contains an induced `2K₂`. -/
theorem exists_induced_2K2_of_triangleFree_smalldeg {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset V)
    (htri : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c))
    (hmin : ∀ a ∈ D, 1 ≤ (G.neighborFinset a ∩ D).card)
    (hmax : ∀ a ∈ D, (G.neighborFinset a ∩ D).card ≤ 3)
    (hcard : 8 ≤ D.card) :
    ∃ a ∈ D, ∃ b ∈ D, ∃ c ∈ D, ∃ d ∈ D,
      ({a, b, c, d} : Finset V).card = 4 ∧
      G.Adj a b ∧ G.Adj c d ∧
      ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d := by
  classical
  by_contra hno
  -- Reformulate the absence of an induced `2K₂` as a usable "no configuration" predicate.
  have key : ∀ a b c d : V, a ∈ D → b ∈ D → c ∈ D → d ∈ D →
      ({a, b, c, d} : Finset V).card = 4 → G.Adj a b → G.Adj c d →
      ¬ G.Adj a c → ¬ G.Adj a d → ¬ G.Adj b c → ¬ G.Adj b d → False := by
    intro a b c d ha hb hc hd hcard4 hab hcd hac had hbc hbd
    exact hno ⟨a, ha, b, hb, c, hc, d, hd, hcard4, hab, hcd, hac, had, hbc, hbd⟩
  -- Helper: card of an explicit 4-element set with pairwise-distinct entries.
  have card4 : ∀ p q r s : V, p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
      ({p, q, r, s} : Finset V).card = 4 := by
    intro p q r s hpq hpr hps hqr hqs hrs
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr, hps]),
        Finset.card_insert_of_notMem (by simp [hqr, hqs]),
        Finset.card_insert_of_notMem (by simp [hrs]), Finset.card_singleton]
  -- Membership in the in-`D` neighbourhood.
  have hmemND : ∀ v z : V, z ∈ G.neighborFinset v ∩ D ↔ G.Adj v z ∧ z ∈ D := by
    intro v z
    rw [Finset.mem_inter, G.mem_neighborFinset]
  -- `D` is nonempty.
  have hDne : D.Nonempty := Finset.card_pos.mp (by omega)
  -- Pick a vertex `x ∈ D` of maximum in-`D` degree `Δ`.
  obtain ⟨x, hxD, hxmax⟩ :=
    D.exists_max_image (fun v => (G.neighborFinset v ∩ D).card) hDne
  set Δ : ℕ := (G.neighborFinset x ∩ D).card with hΔdef
  have hΔ3 : Δ ≤ 3 := hmax x hxD
  -- STEP 1 (domination within distance two): every `z ∈ D` is `x`, in `Nᴰ x`, or adjacent
  -- to some vertex of `Nᴰ x`.
  have hdom :=
      exists_induced_2K2_of_triangleFree_smalldeg_hdom (V := V) (G := G) (D := D) (hmin) (key)
        (card4) (hmemND) (x := x) (hxD) (hxmax)
  -- The independent set `Nᴰ x` (triangle-freeness): no two `Nᴰ x`-vertices are adjacent.
  have hindNx : ∀ a ∈ G.neighborFinset x ∩ D, ∀ b ∈ G.neighborFinset x ∩ D,
      a ≠ b → ¬ G.Adj a b := by
    intro a ha b hb _ hadj
    rw [hmemND] at ha hb
    exact htri x hxD a ha.2 b hb.2 ⟨ha.1, hadj, hb.1⟩
  -- STEP 2 (decomposition): `D ⊆ {x} ∪ Nᴰ x ∪ B`, hence `|D| ≤ 1 + Δ + |B|`.
  set B : Finset V :=
    (D.filter (fun z => ∃ a ∈ G.neighborFinset x ∩ D, G.Adj z a))
      \ insert x (G.neighborFinset x ∩ D) with hBdef
  have hDsub :=
      exists_induced_2K2_of_triangleFree_smalldeg_hDsub (V := V) (G := G) (D := D) (x := x)
        (hxD) (Δ := Δ) (hxmax) (hΔdef) (hΔ3) (hdom) (hindNx) (hBdef)
  have hcardle : D.card ≤ 1 + Δ + B.card := by
    calc D.card
        ≤ (insert x (G.neighborFinset x ∩ D ∪ B)).card := Finset.card_le_card hDsub
      _ ≤ (G.neighborFinset x ∩ D ∪ B).card + 1 := Finset.card_insert_le _ _
      _ ≤ ((G.neighborFinset x ∩ D).card + B.card) + 1 := by
          have := Finset.card_union_le (G.neighborFinset x ∩ D) B; omega
      _ = 1 + Δ + B.card := by rw [hΔdef]; ring
  -- STEP 3 (core, residual): the third block `B` has at most three vertices.
  -- For `b ∈ B` set `col b := Nᴰ b ∩ Nᴰ x ⊆ Nᴰ x` (nonempty).  Three `2K₂`-free forcings
  -- pin down the structure: (T) `b ~ b' → col b ∩ col b' = ∅` (triangle-freeness);
  -- (A) `col b ∩ col b' = ∅ → b ~ b'` (else a `2K₂` on two `B`-edges); and crucially
  -- (X) `b ~ b' → col b ∪ col b' = Nᴰ x` (else a `2K₂` through `x`: the edge `(x, a)` with
  -- `a ∈ Nᴰ x \ (col b ∪ col b')` and the edge `(b, b')`).  With the per-colour bound
  -- `#{b : a ∈ col b} ≤ Δ - 1` and `deg_D ≤ 3`, the cases `Δ ≤ 2` give `|B| ≤ Δ(Δ-1) ≤ 2`
  -- by a double count, and `Δ = 3` reduces to an integer program over the `≤ 3`-element set
  -- `Nᴰ x` forcing `|B| ≤ 3`.
  have hBcard : B.card ≤ 3 := by
    set Nx : Finset V := G.neighborFinset x ∩ D with hNx
    -- Membership facts for a `B`-vertex: in `D`, not `x`, not in `Nx`, with a neighbour in `Nx`.
    have hBmem : ∀ b ∈ B, b ∈ D ∧ b ≠ x ∧ b ∉ Nx ∧ (G.neighborFinset b ∩ Nx).Nonempty := by
      intro b hb
      rw [hBdef, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_insert] at hb
      obtain ⟨⟨hbD, a, haNx, hba⟩, hbni⟩ := hb
      push Not at hbni
      obtain ⟨hbx, hbNx⟩ := hbni
      refine ⟨hbD, hbx, hbNx, a, ?_⟩
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hba, haNx⟩
    -- Membership in the "colour" set `Nᴰ b ∩ Nx`.
    have hcolmem : ∀ b a : V, a ∈ G.neighborFinset b ∩ Nx ↔ G.Adj b a ∧ a ∈ Nx := by
      intro b a
      rw [Finset.mem_inter, G.mem_neighborFinset]
    -- For `a ∈ Nx`, the number of `B`-vertices coloured by `a` is at most `Δ - 1`.
    have hBa :=
        exists_induced_2K2_of_triangleFree_smalldeg_hBa (V := V) (G := G) (D := D) (x := x)
          (hxD) (Δ := Δ) (hxmax) (hΔ3) (hΔdef) (hNx) (hBmem) (hcolmem)
    -- Double counting: `∑_b |col b| ≤ Δ (Δ - 1)`.
    have hsumcol :=
        exists_induced_2K2_of_triangleFree_smalldeg_hsumcol (V := V) (G := G) (D := D) (x :=
          x) (Δ := Δ) (hΔdef) (hcolmem) (hBa)
    -- Each `B`-vertex has a nonempty colour, so `|B| ≤ ∑_b |col b|`.
    have hBle : B.card ≤ ∑ b ∈ B, (G.neighborFinset b ∩ Nx).card := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro b hb
      exact Finset.card_pos.mpr (hBmem b hb).2.2.2
    have hBΔ : B.card ≤ Δ * (Δ - 1) := le_trans hBle hsumcol
    have hΔ1 : 1 ≤ Δ := by rw [hΔdef, hNx]; exact hmin x hxD
    have hΔcases : Δ = 1 ∨ Δ = 2 ∨ Δ = 3 := by omega
    rcases hΔcases with hΔeq | hΔeq | hΔeq
    · rw [hΔeq] at hBΔ; omega
    · rw [hΔeq] at hBΔ; omega
    · -- Δ = 3: the hard case requiring the structural forcings.
      have hNx3 : Nx.card = 3 := hΔdef.symm.trans hΔeq
      -- Forcing (A): disjoint colours force an edge (else an induced `2K₂` on the two edges).
      have hAdj :=
          exists_induced_2K2_of_triangleFree_smalldeg_hAdj (V := V) (G := G) (D := D) (key)
            (card4) (x := x) (Nx := Nx) (hindNx) (hNx) (hBmem) (hcolmem)
      -- Forcing (X): an edge between `B`-vertices forces their colours to cover `Nx`.
      have hUnion :=
          exists_induced_2K2_of_triangleFree_smalldeg_hUnion (V := V) (G := G) (D := D) (key)
            (card4) (x := x) (hxD) (Nx := Nx) (hNx) (hBmem)
            (hcolmem)
      -- Combined: disjoint colours force the union to be all of `Nx`.
      have hAX : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' →
          Disjoint (G.neighborFinset b ∩ Nx) (G.neighborFinset b' ∩ Nx) →
          (G.neighborFinset b ∩ Nx) ∪ (G.neighborFinset b' ∩ Nx) = Nx :=
        fun b hb b' hb' hbb' hdisj => hUnion b hb b' hb' hbb' (hAdj b hb b' hb' hbb' hdisj)
      -- Degree bound: colour size plus number of `B`-neighbours is at most `3`.
      have hdeg :=
          exists_induced_2K2_of_triangleFree_smalldeg_hdeg (V := V) (G := G) (D := D) (hmax) (x :=
            x) (Nx := Nx) (hNx) (hBmem) (hcolmem)
      -- Refined count: `2|B| ≤ ∑_b |col b| + s` where `s` counts singleton colours.
      have hsum6 : ∑ b ∈ B, (G.neighborFinset b ∩ Nx).card ≤ 6 := by
        have h := hsumcol; rw [hΔeq] at h; omega
      set s : ℕ := (B.filter (fun b => (G.neighborFinset b ∩ Nx).card = 1)).card with hs
      have h2B : 2 * B.card ≤ (∑ b ∈ B, (G.neighborFinset b ∩ Nx).card) + s := by
        have hptwise : ∀ b ∈ B, 2 ≤ (G.neighborFinset b ∩ Nx).card
            + (if (G.neighborFinset b ∩ Nx).card = 1 then 1 else 0) := by
          intro b hb
          have hpos : 1 ≤ (G.neighborFinset b ∩ Nx).card :=
            Finset.card_pos.mpr (hBmem b hb).2.2.2
          split <;> omega
        calc 2 * B.card = ∑ _b ∈ B, 2 := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
          _ ≤ ∑ b ∈ B, ((G.neighborFinset b ∩ Nx).card
                + (if (G.neighborFinset b ∩ Nx).card = 1 then 1 else 0)) :=
              Finset.sum_le_sum hptwise
          _ = (∑ b ∈ B, (G.neighborFinset b ∩ Nx).card) + s := by
              rw [Finset.sum_add_distrib, hs, Finset.card_filter]
      -- Case on the number `s` of singleton-coloured vertices.
      rcases Nat.lt_or_ge s 2 with hslt | hsge
      · omega
      · -- `s ≥ 2`: two singletons collapse `B` onto a single colour class of size `≤ 2`.
        have h1s : 1 < s := by omega
        obtain ⟨b1, hb1f, b2, hb2f, hb1b2⟩ := Finset.one_lt_card.mp h1s
        rw [Finset.mem_filter] at hb1f hb2f
        obtain ⟨hb1B, hb1card⟩ := hb1f
        obtain ⟨hb2B, hb2card⟩ := hb2f
        obtain ⟨a₀, hcol1⟩ := Finset.card_eq_one.mp hb1card
        obtain ⟨a₀', hcol2⟩ := Finset.card_eq_one.mp hb2card
        have ha₀Nx : a₀ ∈ Nx := by
          have : a₀ ∈ G.neighborFinset b1 ∩ Nx := hcol1 ▸ Finset.mem_singleton_self a₀
          exact (Finset.mem_inter.mp this).2
        have ha₀eq : a₀ = a₀' := by
          by_contra hne
          have hdisj : Disjoint (G.neighborFinset b1 ∩ Nx) (G.neighborFinset b2 ∩ Nx) := by
            rw [hcol1, hcol2]; exact Finset.disjoint_singleton.mpr hne
          have huni := hAX b1 hb1B b2 hb2B hb1b2 hdisj
          rw [hcol1, hcol2] at huni
          have hle : Nx.card ≤ 2 := by
            rw [← huni]; exact le_trans (Finset.card_union_le _ _) (by simp)
          omega
        rw [← ha₀eq] at hcol2
        -- Every `B`-vertex is coloured by `a₀`.
        have hall :=
            exists_induced_2K2_of_triangleFree_smalldeg_hall (V := V) (G := G) (D := D) (x :=
              x) (Δ := Δ) (hΔdef) (hBmem) (hΔeq) (hAdj) (hUnion) (hdeg) (b1 := b1) (b2 := b2)
                (hb1b2) (hb1B) (hb1card) (hb2B) (hb2card) (a₀ := a₀) (hcol1) (hcol2)
        have hBeq : B = B.filter (fun b => a₀ ∈ G.neighborFinset b ∩ Nx) :=
          (Finset.filter_true_of_mem hall).symm
        have hle : B.card ≤ Δ - 1 := by rw [hBeq]; exact hBa a₀ ha₀Nx
        omega
  omega

end ACMax
