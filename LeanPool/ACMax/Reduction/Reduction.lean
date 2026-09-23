/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Ring
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import LeanPool.ACMax.Spectral.AlgConn
public import LeanPool.ACMax.Cuts.LowDegreeVertex
public import LeanPool.ACMax.Cuts.WeightedCut
public import LeanPool.ACMax.Cuts.Ind2K2
public import LeanPool.ACMax.Cuts.TriangleFree2K2
public import LeanPool.ACMax.Cuts.Disconnected
public import LeanPool.ACMax.Cuts.GoodC4
public import LeanPool.ACMax.Cuts.GoodK23

/-!
# The `n`-generic master reduction for the ACMAX conjecture

For every `n ≥ 12`, the upper-bound clause of Kolokolnikov's Conjecture 1.5
(arXiv:1412.6147) reduces to the residual predicate `ResidualCore`. The residual
hypothesis is discharged downstream in `LeanPool.ACMax.Band.Final`; the full
entry point also covers orders `4 ≤ n ≤ 11`.

## The reduction

Let `G` be a graph on `Fin n` (`n ≥ 12`) with `2(n-2)` edges.  Then `algConn G ≤ 2` follows
unconditionally in each of the following cases, via the *generic* certificate layer (each of the
lemmas below is already stated for an arbitrary finite vertex type):

1. `G` disconnected → `algConn_le_two_of_not_connected`;
2. some vertex has degree `≤ 2` → `algConn_le_two_of_low_degree_vertex`
   (the complement of the closed neighbourhood is nonempty since `n ≥ 12 > 3`);
3. otherwise `δ ≥ 3`, and the handshake `∑ deg = 4n − 8 = 3n + (n − 8)` forces at least `8`
   vertices of degree exactly `3` (`card_deg3_ge_eight`: each degree-`≥4` vertex absorbs at least
   one unit of the excess `n − 8`, so `|D| ≥ 8`);
4. a **good triangle** — three mutually adjacent vertices with
   `n·(∑deg − 6) ≤ 2·(3·(n−3))` — is a sparse weighted cut → `algConn_le_two_of_weighted_cut`
   (the triangle sends exactly `∑deg − 6` edges out).  Similarly a **good `C₄`**
   (`n·(∑deg − 8) ≤ 2·(4·(n−4))`) → `algConn_le_two_of_good_C4`, and a **good `K_{2,3}`**
   (`n·(∑deg − 12) ≤ 2·(5·(n−5))`) → `algConn_le_two_of_good_K23`.  These `n`-uniform
   thresholds are *exactly* the hypotheses the generic cut lemmas consume — no slack is given
   away (at `n = 19` they specialise to the familiar `∑deg ≤ 11 / ≤ 14 / ≤ 19`; see the
   sanity `example`s below);
5. no good triangle, and every degree-`3` vertex has a degree-`3` neighbour → the degree-`3` set
   `D` is triangle-free (a triangle in `D` has `∑deg = 9`, good for `n ≥ 6`), has min-`D`-degree
   `≥ 1` and max-`D`-degree `≤ 3`, and `|D| ≥ 8`, so `exists_induced_2K2_of_triangleFree_smalldeg`
   yields an induced `2K₂` of degree sum `12` → `algConn_le_two_of_ind_2K2`;
6. **the residual**: what survives is *exactly* `ResidualCore n G` — connected, `δ ≥ 3`,
   `2(n−2)` edges, an *isolated* degree-`3` vertex (one with no degree-`3` neighbour — the
   precise negation of the hypothesis step 5 consumes), no good triangle, no induced `2K₂` on
   degree-`3` vertices, no good `C₄`, no good `K_{2,3}`.

The conditional dispatcher `algConn_le_two_of_card_general_cond` takes the
residual case as an explicit hypothesis. `residual_algConn_le_two` in
`LeanPool.ACMax.Band.Final` proves that hypothesis from the unconditional
conjecture. The numeric examples below check the cut thresholds at order 19.
-/

@[expose] public section

namespace ACMax

/-! ## The `n`-uniform certificate predicates

Each predicate carries its degree-sum threshold in the exact `n`-uniform form consumed by the
corresponding generic cut lemma, so that the dispatch below gives away no slack. -/

open Classical in
/-- A **good triangle**: three mutually adjacent vertices whose degree sum satisfies the
`n`-uniform weighted-cut inequality `n·(∑deg − 6) ≤ 2·(3·(n−3))`.  (The triangle `A = {x,y,z}`
sends exactly `∑deg − 6` edges to `Aᶜ`, so this is precisely the hypothesis of
`algConn_le_two_of_weighted_cut`.)  At `n = 19` this is `∑deg ≤ 11`. -/
def HasGoodTriangle (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ x y z : Fin n, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
    n * (G.degree x + G.degree y + G.degree z - 6) ≤ 2 * (3 * (n - 3))

open Classical in
/-- An **induced `2K₂` on degree-`3` vertices**: four distinct vertices of degree `3` spanning
exactly the two edges `ab`, `cd`.  Its degree sum is `12`, so `algConn_le_two_of_ind_2K2`
applies (for every `n`). -/
def HasDeg3Ind2K2 (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c d : Fin n, ({a, b, c, d} : Finset (Fin n)).card = 4 ∧
    G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
    G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d

open Classical in
/-- A **good `C₄`**: an induced `4`-cycle `a-b-c-d-a` with the `n`-uniform threshold
`n·(∑deg − 8) ≤ 2·(4·(n−4))` — exactly the hypothesis of `algConn_le_two_of_good_C4`.
At `n = 19` this is `∑deg ≤ 14`. -/
def HasGoodC4 (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c d : Fin n, ({a, b, c, d} : Finset (Fin n)).card = 4 ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
    n * (G.degree a + G.degree b + G.degree c + G.degree d - 8) ≤ 2 * (4 * (n - 4))

open Classical in
/-- A **good `K_{2,3}`**: an induced complete bipartite `K_{2,3}` (parts `{a,b}`, `{c,d,e}`)
with the `n`-uniform threshold `n·(∑deg − 12) ≤ 2·(5·(n−5))` — exactly the hypothesis of
`algConn_le_two_of_good_K23`.  At `n = 19` this is `∑deg ≤ 19`. -/
def HasGoodK23 (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c d e : Fin n, ({a, b, c, d, e} : Finset (Fin n)).card = 5 ∧
    G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
    ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
    n * (G.degree a + G.degree b + G.degree c + G.degree d + G.degree e - 12)
      ≤ 2 * (5 * (n - 5))

/-! ## The residual predicate -/

open Classical in
/-- **The residual core** — exactly the class of graphs that survives the generic reduction
steps 1–5 (see the module docstring).  Every field is the *precise* negation of the branch
condition the corresponding step consumes; nothing is weakened and nothing extraneous is added:

* `connected` — step 1 (disconnected graphs are closed by `algConn_le_two_of_not_connected`);
* `min_degree` — step 2 (a degree-`≤2` vertex is closed by `algConn_le_two_of_low_degree_vertex`);
* `edge_card`, `n_ge` — the standing hypotheses (from which `≥ 8` degree-`3` vertices follow,
  `card_deg3_ge_eight`);
* `no_good_triangle` — step 4a (weighted cut on a triangle);
* `iso_deg3` — the negation of "every degree-`3` vertex has a degree-`3` neighbour"
  (step 5 consumes that hypothesis to extract an induced `2K₂` inside the degree-`3` set);
* `no_deg3_ind2K2` — step 5's certificate directly (an induced `2K₂` on degree-`3` vertices
  closes the graph regardless of how it was found);
* `no_good_C4`, `no_good_K23` — steps 4b, 4c.

Every such residual graph is closed by `residual_algConn_le_two` in
`LeanPool.ACMax.Band.Final`. -/
structure ResidualCore (n : ℕ) (G : SimpleGraph (Fin n)) : Prop where
  n_ge : 12 ≤ n
  edge_card : G.edgeFinset.card = 2 * (n - 2)
  connected : G.Connected
  min_degree : ∀ v : Fin n, 3 ≤ G.degree v
  iso_deg3 : ∃ t : Fin n, G.degree t = 3 ∧ ∀ w : Fin n, G.Adj t w → G.degree w ≠ 3
  no_good_triangle : ¬HasGoodTriangle n G
  no_deg3_ind2K2 : ¬HasDeg3Ind2K2 n G
  no_good_C4 : ¬HasGoodC4 n G
  no_good_K23 : ¬HasGoodK23 n G

/-! ## Step 3: the handshake counting lemma -/

open Classical in
/-- **Handshake counting.**  If every degree is `≥ 3` and `G` has `2(n−2)` edges, then at least
`8` vertices have degree exactly `3`: with `D = {deg = 3}` and `H = {deg ≥ 4}`,
`3|D| + 4|H| ≤ ∑deg = 4n − 8` and `|D| + |H| = n` give `|D| ≥ 8`. -/
theorem card_deg3_ge_eight (n : ℕ) (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    8 ≤ (Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card := by
  classical
  set D := Finset.univ.filter (fun v : Fin n => G.degree v = 3) with hD
  set H := Finset.univ.filter (fun v : Fin n => 4 ≤ G.degree v) with hH
  have hsum : ∑ v : Fin n, G.degree v = 2 * (2 * (n - 2)) := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hmemD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3 := by
    intro v; rw [hD]; simp
  have hmemH : ∀ v : Fin n, v ∈ H ↔ 4 ≤ G.degree v := by
    intro v; rw [hH]; simp
  have hDH : ∀ v : Fin n, v ∈ D ∨ v ∈ H := by
    intro v
    rcases Nat.lt_or_ge (G.degree v) 4 with hlt | hge
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemH v).mpr hge)
  have hdisj : Disjoint D H := by
    rw [Finset.disjoint_left]
    intro v hvD hvH
    have h1 := (hmemD v).mp hvD
    have h2 := (hmemH v).mp hvH
    omega
  have hunion : D ∪ H = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact hDH v
  have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ H, G.degree v = 2 * (2 * (n - 2)) := by
    rw [← Finset.sum_union hdisj, hunion]; exact hsum
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hsumH : H.card * 4 ≤ ∑ v ∈ H, G.degree v := by
    have hb : ∀ x ∈ H, 4 ≤ (fun v => G.degree v) x := fun i hi => (hmemH i).mp hi
    have h := Finset.card_nsmul_le_sum H (fun v => G.degree v) 4 hb
    simpa [smul_eq_mul] using h
  have hpart2 : D.card + H.card = n := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [hsumD] at hsumpart
  omega

/-! ## The master reduction -/

open Classical in
/-- **The `n`-generic master reduction** (`n ≥ 12`).  Every simple graph on `Fin n` with
exactly `2(n-2)` edges has algebraic connectivity at most `2`, *given* the residual lemma
`residual_algConn_le_two`.  Steps 1–5 of the dispatch (disconnected / low degree / good
triangle / triangle-free induced `2K₂` / induced `2K₂` on degree-`3` vertices / good `C₄` /
good `K_{2,3}`) are proved here uniformly in `n`. The hypothesis `hres` records
the residual case and is discharged by the downstream unconditional theorem. -/
theorem algConn_le_two_of_card_general_cond (n : ℕ) (hn : 12 ≤ n) [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (hres : ResidualCore n G → algConn G ≤ 2) :
    algConn G ≤ 2 := by
  -- Work with the classical `DecidableEq` throughout, so that all `Finset` operations built in
  -- this proof match the instances of the generic certificate lemmas.
  let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  -- Step 2: a vertex of degree ≤ 2 closes the graph.
  rcases Classical.em (∃ v : Fin n, G.degree v ≤ 2) with hlow | hlow
  · obtain ⟨u, hdeg⟩ := hlow
    refine algConn_le_two_of_low_degree_vertex G u hdeg ?_
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ]
    have hcard : (insert u (G.neighborFinset u)).card ≤ 3 := by
      calc (insert u (G.neighborFinset u)).card
          ≤ (G.neighborFinset u).card + 1 := Finset.card_insert_le _ _
        _ = G.degree u + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ 3 := by omega
    have huniv : (Finset.univ : Finset (Fin n)).card = n := by simp
    omega
  · -- δ ≥ 3.
    simp only [not_exists, not_le] at hlow
    have h3 : ∀ v : Fin n, 3 ≤ G.degree v := fun v => by have := hlow v; omega
    -- Step 4a: a good triangle is a sparse weighted cut.
    by_cases hT : HasGoodTriangle n G
    · obtain ⟨x, y, z, hxy_ne, hyz_ne, hxz_ne, hxy, hyz, hxz, hdsum⟩ := hT
      have hAcard : ({x, y, z} : Finset (Fin n)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy_ne, hxz_ne]),
            Finset.card_insert_of_notMem (by simp [hyz_ne]), Finset.card_singleton]
      have hAccard : (({x, y, z} : Finset (Fin n))ᶜ).card = n - 3 := by
        rw [Finset.card_compl, hAcard, Fintype.card_fin]
      have hA : ({x, y, z} : Finset (Fin n)).Nonempty := ⟨x, by simp⟩
      have hAc : (({x, y, z} : Finset (Fin n))ᶜ).Nonempty :=
        Finset.card_pos.mp (by rw [hAccard]; omega)
      -- Each triangle vertex meets the triangle in exactly its two partners.
      have triErase : ∀ a : Fin n, a ∈ ({x, y, z} : Finset (Fin n)) →
          (∀ b ∈ ({x, y, z} : Finset (Fin n)), b ≠ a → G.Adj a b) →
          G.neighborFinset a ∩ ({x, y, z} : Finset (Fin n))
            = ({x, y, z} : Finset (Fin n)).erase a := by
        intro a _ hadj
        ext w
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_erase]
        constructor
        · rintro ⟨haw, hw⟩
          refine ⟨?_, hw⟩
          rintro rfl
          exact G.irrefl haw
        · rintro ⟨hwa, hw⟩
          exact ⟨hadj w hw hwa, hw⟩
      have interCardEq : ∀ a : Fin n, a ∈ ({x, y, z} : Finset (Fin n)) →
          (∀ b ∈ ({x, y, z} : Finset (Fin n)), b ≠ a → G.Adj a b) →
          (G.neighborFinset a ∩ ({x, y, z} : Finset (Fin n))).card = 2 := by
        intro a ha hadj
        rw [triErase a ha hadj, Finset.card_erase_of_mem ha, hAcard]
      have adjX : ∀ b ∈ ({x, y, z} : Finset (Fin n)), b ≠ x → G.Adj x b := by
        intro b hb hbx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact absurd rfl hbx
        · exact hxy
        · exact hxz
      have adjY : ∀ b ∈ ({x, y, z} : Finset (Fin n)), b ≠ y → G.Adj y b := by
        intro b hb hby
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact hxy.symm
        · exact absurd rfl hby
        · exact hyz
      have adjZ : ∀ b ∈ ({x, y, z} : Finset (Fin n)), b ≠ z → G.Adj z b := by
        intro b hb hbz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact hxz.symm
        · exact hyz.symm
        · exact absurd rfl hbz
      have interX : (G.neighborFinset x ∩ ({x, y, z} : Finset (Fin n))).card = 2 :=
        interCardEq x (by simp) adjX
      have interY : (G.neighborFinset y ∩ ({x, y, z} : Finset (Fin n))).card = 2 :=
        interCardEq y (by simp) adjY
      have interZ : (G.neighborFinset z ∩ ({x, y, z} : Finset (Fin n))).card = 2 :=
        interCardEq z (by simp) adjZ
      -- Hence each triangle vertex sends `deg − 2` edges out of the triangle.
      have sdX : (G.neighborFinset x \ ({x, y, z} : Finset (Fin n))).card + 2 = G.degree x := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset x)
          ({x, y, z} : Finset (Fin n))
        rw [interX, G.card_neighborFinset_eq_degree] at h
        exact h
      have sdY : (G.neighborFinset y \ ({x, y, z} : Finset (Fin n))).card + 2 = G.degree y := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset y)
          ({x, y, z} : Finset (Fin n))
        rw [interY, G.card_neighborFinset_eq_degree] at h
        exact h
      have sdZ : (G.neighborFinset z \ ({x, y, z} : Finset (Fin n))).card + 2 = G.degree z := by
        have h := Finset.card_sdiff_add_card_inter (G.neighborFinset z)
          ({x, y, z} : Finset (Fin n))
        rw [interZ, G.card_neighborFinset_eq_degree] at h
        exact h
      have cutEq : ∑ a ∈ ({x, y, z} : Finset (Fin n)),
          (G.neighborFinset a \ ({x, y, z} : Finset (Fin n))).card
          = (G.neighborFinset x \ ({x, y, z} : Finset (Fin n))).card
            + (G.neighborFinset y \ ({x, y, z} : Finset (Fin n))).card
            + (G.neighborFinset z \ ({x, y, z} : Finset (Fin n))).card := by
        rw [Finset.sum_insert (by simp [hxy_ne, hxz_ne]),
            Finset.sum_insert (by simp [hyz_ne]), Finset.sum_singleton]
        ring
      refine algConn_le_two_of_weighted_cut G ({x, y, z} : Finset (Fin n)) hA hAc ?_
      rw [hAcard, hAccard, Fintype.card_fin, cutEq]
      have heq : (G.neighborFinset x \ ({x, y, z} : Finset (Fin n))).card
          + (G.neighborFinset y \ ({x, y, z} : Finset (Fin n))).card
          + (G.neighborFinset z \ ({x, y, z} : Finset (Fin n))).card
          = G.degree x + G.degree y + G.degree z - 6 := by omega
      rw [heq]
      exact hdsum
    · -- No good triangle: the degree-3 set `D` has `|D| ≥ 8` (step 3) and is triangle-free.
      set D := Finset.univ.filter (fun v : Fin n => G.degree v = 3) with hD
      have hmemD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3 := by
        intro v; rw [hD]; simp
      have hDcard : 8 ≤ D.card := by
        rw [hD]; exact card_deg3_ge_eight n (by omega) G hm h3
      have hmax : ∀ a ∈ D, (G.neighborFinset a ∩ D).card ≤ 3 := by
        intro a haD
        calc (G.neighborFinset a ∩ D).card
            ≤ (G.neighborFinset a).card := Finset.card_le_card Finset.inter_subset_left
          _ = G.degree a := G.card_neighborFinset_eq_degree a
          _ = 3 := (hmemD a).mp haD
      have htri : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) := by
        rintro a haD b hbD c hcD ⟨hab, hbc, hac⟩
        have da := (hmemD a).mp haD
        have db := (hmemD b).mp hbD
        have dc := (hmemD c).mp hcD
        -- A triangle inside `D` has degree sum `9`, hence is good for `n ≥ 6`.
        have h9 : G.degree a + G.degree b + G.degree c - 6 = 3 := by omega
        refine hT ⟨a, b, c, G.ne_of_adj hab, G.ne_of_adj hbc, G.ne_of_adj hac,
          hab, hbc, hac, ?_⟩
        rw [h9]
        omega
      by_cases hmin : ∀ a ∈ D, 1 ≤ (G.neighborFinset a ∩ D).card
      · -- Step 5: every degree-3 vertex has a degree-3 neighbour → induced `2K₂` inside `D`.
        obtain ⟨a, haD, b, hbD, c, hcD, d, hdD, hcard4, hab, hcd, hac, had, hbc, hbd⟩ :=
          exists_induced_2K2_of_triangleFree_smalldeg G D htri hmin hmax hDcard
        have hda := (hmemD a).mp haD
        have hdb := (hmemD b).mp hbD
        have hdc := (hmemD c).mp hcD
        have hdd := (hmemD d).mp hdD
        exact algConn_le_two_of_ind_2K2 G a b c d hcard4 hab hcd hac had hbc hbd (by omega)
      · -- Step 1: disconnected graphs are closed generically.
        by_cases hconn : G.Connected
        · -- Step 5': an induced `2K₂` on degree-3 vertices, however found, closes the graph.
          by_cases h2k2 : HasDeg3Ind2K2 n G
          · obtain ⟨a, b, c, d, hcard4, hda, hdb, hdc, hdd, hab, hcd, hac, had, hbc, hbd⟩ := h2k2
            refine algConn_le_two_of_ind_2K2 G a b c d ?_ hab hcd hac had hbc hbd (by omega)
            convert hcard4
          · -- Step 4b: a good `C₄`.
            by_cases hC4 : HasGoodC4 n G
            · obtain ⟨a, b, c, d, hcard4, hab, hbc, hcd, hda, hac, hbd, hdeg⟩ := hC4
              refine algConn_le_two_of_good_C4 G a b c d ?_ ?_ hab hbc hcd hda hac hbd ?_
              · convert hcard4
              · rw [Fintype.card_fin]; omega
              · rw [Fintype.card_fin]; exact hdeg
            · -- Step 4c: a good `K_{2,3}`.
              by_cases hK23 : HasGoodK23 n G
              · obtain ⟨a, b, c, d, e, hcard5, hac, had, hae, hbc, hbd, hbe, hab, hcd, hce, hde,
                  hdeg⟩ := hK23
                refine algConn_le_two_of_good_K23 G a b c d e ?_ ?_ hac had hae hbc hbd hbe
                  hab hcd hce hde ?_
                · convert hcard5
                · rw [Fintype.card_fin]; omega
                · rw [Fintype.card_fin]; exact hdeg
              · -- Step 6: the residual.  `¬hmin` supplies the isolated degree-3 vertex.
                have hiso : ∃ t : Fin n, G.degree t = 3 ∧
                    ∀ w : Fin n, G.Adj t w → G.degree w ≠ 3 := by
                  rw [not_forall] at hmin
                  obtain ⟨a, ha⟩ := hmin
                  rw [Classical.not_imp, not_le] at ha
                  obtain ⟨haD, hlt⟩ := ha
                  refine ⟨a, (hmemD a).mp haD, ?_⟩
                  intro w hadj hw
                  have hwmem : w ∈ G.neighborFinset a ∩ D := by
                    rw [Finset.mem_inter, G.mem_neighborFinset]
                    exact ⟨hadj, (hmemD w).mpr hw⟩
                  have hpos : 0 < (G.neighborFinset a ∩ D).card :=
                    Finset.card_pos.mpr ⟨w, hwmem⟩
                  omega
                exact hres ⟨hn, hm, hconn, h3, hiso, hT, h2k2, hC4, hK23⟩
        · exact algConn_le_two_of_not_connected G hconn

-- (The unconditional master reduction `algConn_le_two_of_card_general` is proved in
-- `LeanPool.ACMax.Band.Final`.)

/-! ## Sanity checks at `n = 19`

The `n`-uniform thresholds specialize at `n = 19` to these numerical bounds: -/

/-- Good-triangle threshold at `n = 19`: `19·(S−6) ≤ 2·(3·16) = 96 ↔ S ≤ 11`. -/
example : ∀ S : ℕ, 19 * (S - 6) ≤ 2 * (3 * (19 - 3)) ↔ S ≤ 11 := by intro S; omega

/-- Good-`C₄` threshold at `n = 19`: `19·(S−8) ≤ 2·(4·15) = 120 ↔ S ≤ 14`. -/
example : ∀ S : ℕ, 19 * (S - 8) ≤ 2 * (4 * (19 - 4)) ↔ S ≤ 14 := by intro S; omega

/-- Good-`K_{2,3}` threshold at `n = 19`: `19·(S−12) ≤ 2·(5·14) = 140 ↔ S ≤ 19`. -/
example : ∀ S : ℕ, 19 * (S - 12) ≤ 2 * (5 * (19 - 5)) ↔ S ≤ 19 := by intro S; omega

end ACMax
