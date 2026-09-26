/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gonality.DivisorialGonality
public import LeanPool.BrillNoetherGraphs.Utilities.Gonality.LegalFiring
public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.Bramble
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.UnderlyingSimpleGraph

/-!
# Theorem A: the bramble number bounds the gonality

This is §2 of van Dobben de Bruyn--Gijswijt (arXiv:1407.7055): for every bramble
`𝔅` of a connected graph `G`,

```
order 𝔅 ≤ divisorialGonality G + 1.
```

Combined with Seymour--Thomas duality this gives `treewidth ≤ gonality`
(`TreewidthGonality/Gonality/TreewidthGonality.lean`), but the statement here is
*stronger and unconditional*: the bramble number of `G` is at least
`treewidth G + 1` for any graph, so this bound implies the treewidth one and
holds whether or not the duality theorem has been formalized.

## Conventions

Brambles live on `underlyingSimpleGraph G` — treewidth and brambles do not see
edge multiplicities. The chip-firing side does: `outdegreeSet` and `edgeCut` count
**with multiplicity**, which only strengthens the inequalities used here
(more parallel edges make a cut more expensive, never less).

Connectivity of a vertex set is `((underlyingSimpleGraph G).induce (↑B : Set G.V)).Connected`,
the convention fixed in `TreewidthGonality/Treewidth/TreeDecomposition.lean`.
-/

@[expose] public section

namespace Utilities.Gonality

open Finset Utilities.Treewidth

variable {G : CFGraph}

/-! ## Supports and cuts -/

/-- The vertices carrying at least one chip. -/
def divisorSupport (D : CFDiv G) : Finset G.V :=
  Finset.univ.filter fun v => 0 < D v

@[simp] theorem mem_divisorSupport {D : CFDiv G} {v : G.V} :
    v ∈ divisorSupport D ↔ 0 < D v := by
  simp [divisorSupport]

/-- An effective divisor has at least one chip on each support vertex, so the
support is no bigger than the degree. -/
theorem card_divisorSupport_le_deg {D : CFDiv G} (hD : effective D) :
    ((divisorSupport D).card : ℤ) ≤ deg D := by
  have hsub : ∑ v ∈ divisorSupport D, (1 : ℤ) ≤ ∑ v ∈ divisorSupport D, D v :=
    Finset.sum_le_sum fun v hv => by
      have := mem_divisorSupport.mp hv
      omega
  have hrest : ∑ v ∈ divisorSupport D, D v ≤ ∑ v : G.V, D v := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro v _ _
    exact hD v
  have hdeg : deg D = ∑ v : G.V, D v := rfl
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsub
  omega

/-- The number of edges leaving `U`, counted with multiplicity. -/
def edgeCut (G : CFGraph) (U : Finset G.V) : ℤ :=
  (edgesBetween G U Uᶜ : ℤ)

theorem edgeCut_nonneg (U : Finset G.V) : 0 ≤ edgeCut G U := by
  simp [edgeCut]

/-- The cut is the total boundary of the vertices of `U`. -/
theorem edgeCut_eq_sum_outdeg (U : Finset G.V) :
    edgeCut G U = ∑ v ∈ U, outdegreeSet G U v := by
  unfold edgeCut edgesBetween outdegreeSet
  push_cast
  rfl

/-! ## The three lemmas of §2 -/

/-- **Lemma 2.2 (support containment).**  If firing `U` clears the support off a
connected set `B` that previously met the support, then `B` was contained in `U`.

Proved (2026-08-25); the paper's argument in two steps:

1. Chips outside the fired set never decrease
   (`le_set_firing_apply_of_not_mem`), so any
   `w ∈ B ∖ U` with `D w > 0` would still carry a chip after firing, contradicting
   `hmiss`.  Hence `B ∩ divisorSupport D ⊆ U`, and by `hmeet` the intersection
   `B ∩ U` is nonempty.
2. If `B ⊄ U`, connectedness of `B` gives an edge of `underlyingSimpleGraph G`
   inside `B` with one end `u ∈ U` and the other end `w ∈ B ∖ U`
   (`Utilities.Treewidth.exists_adj_across_of_walk`).  Then
   `setFiring G D U w = D w + outdegreeSet G Uᶜ w ≥ 0 + numEdges G w u > 0`, again
   contradicting `hmiss`.

Note no legality hypothesis is needed: only effectivity of `D` and the two
`set_firing_apply_*` formulas. -/
theorem support_containment {D : CFDiv G} {U B : Finset G.V} (hD : effective D)
    (hBconn : ((underlyingSimpleGraph G).induce (↑B : Set G.V)).Connected)
    (hmeet : (B ∩ divisorSupport D).Nonempty)
    (hmiss : B ∩ divisorSupport (setFiring G D U) = ∅) :
    B ⊆ U := by
  classical
  -- No vertex of `B` carries a chip after the firing.
  have hnot : ∀ z ∈ B, ¬ (0 < setFiring G D U z) := by
    intro z hz hpos
    have hmem : z ∈ B ∩ divisorSupport (setFiring G D U) :=
      Finset.mem_inter.mpr ⟨hz, mem_divisorSupport.mpr hpos⟩
    rw [hmiss] at hmem
    exact absurd hmem (Finset.notMem_empty z)
  -- Step 1: the vertex of `B` that carried a chip before the firing lies in `U`.
  obtain ⟨x, hx⟩ := hmeet
  obtain ⟨hxB, hxsupp⟩ := Finset.mem_inter.mp hx
  have hx0 := mem_divisorSupport.mp hxsupp
  have hxU : x ∈ U := by
    by_contra hxU
    refine hnot x hxB ?_
    have := le_set_firing_apply_of_not_mem G D hxU
    omega
  -- Step 2: a vertex of `B` outside `U` would receive a chip across the cut.
  intro w hwB
  by_contra hwU
  obtain ⟨p⟩ := hBconn.preconnected ⟨x, Finset.mem_coe.mpr hxB⟩
    ⟨w, Finset.mem_coe.mpr hwB⟩
  obtain ⟨a, ha, b, hb, hadj⟩ :=
    exists_adj_across_of_walk (S := {z : ↥(↑B : Set G.V) | (↑z : G.V) ∈ U}) p
      (show x ∈ U from hxU) hwU
  have hbB : (↑b : G.V) ∈ B := Finset.mem_coe.mp b.2
  refine hnot (↑b : G.V) hbB ?_
  rw [set_firing_apply_of_not_mem G D hb]
  have hpos : 0 < numEdges G (↑b : G.V) (↑a : G.V) := by
    have := hadj.symm
    simpa using this
  have hle : ((numEdges G (↑b : G.V) (↑a : G.V) : ℕ) : ℤ) ≤ outdegreeSet G Uᶜ (↑b : G.V) := by
    unfold outdegreeSet
    exact Finset.single_le_sum (f := fun u => (numEdges G (↑b : G.V) u : ℤ))
      (fun i _ => Int.natCast_nonneg _) (by simpa using ha)
  have hDb := hD (↑b : G.V)
  omega

/-- **Lemma 2.3 (a cut separating two members bounds the order).**  If a bramble
has a member inside `U` and a member inside the complement of `U`, then its order
is at most one more than the number of edges crossing the cut.

Proved (2026-08-25) following the paper's §2 verbatim (Lemma 2.3 there, where the
containments are named the other way round: their `B'` is our `B`).

The naive hitting set "all endpoints of cut edges" has size
`edgeCut + (components of the cut graph)`, so it overshoots.  The paper's
construction, reproduced here, is **one endpoint per cut edge plus one extra
vertex**, and the choice that makes the case analysis close is:

* let `X`, `Y` be the two shores of the cut and, **among all members contained in
  `U`, let `B₀` be one whose trace `B₀ ∩ X` is inclusionwise minimal** (realized
  here by minimizing `(B₀ ∩ X).card`) — this is the step that is easy to miss and
  without which the lemma's case 1 is false;
* let `s` be any vertex of `B₀ ∩ X` (nonempty because `B₀` touches `B'`);
* for each cut edge `xy` with `x ∈ X`, `y ∈ Y`, select `x` if `x ∉ B₀` and `y`
  otherwise; `S` is the selection together with `s`, so `|S| ≤ edgeCut + 1`.

`S` hits every member `A`:

* `A ∩ Y = ∅`: then `A ⊆ U`, so `A` is a competitor for the minimality of
  `B₀ ∩ X`.  Either some `x ∈ (A ∩ X) ∖ B₀`, and then `x` was selected for its own
  cut edge, or `A ∩ X ⊆ B₀ ∩ X`, whence `A ∩ X = B₀ ∩ X` by minimality and
  `s ∈ A`.
* `A ∩ X = ∅`: then `A ⊆ Uᶜ`, and the cut edge joining `A` to `B₀` has its
  `U`-end in `B₀`, so its `Uᶜ`-end — a vertex of `A` — was selected.
* both nonempty: connectedness puts a whole cut edge inside `A`, and one of its
  ends was selected.

The multiplicity convention only helps: the cut is modelled by the finite set of
*ordered pairs* `(x, y) ∈ U × Uᶜ` with `numEdges > 0`, whose cardinality is at
most `edgeCut`. -/
theorem hitting_of_cut (𝔅 : Bramble (underlyingSimpleGraph G)) {U B B' : Finset G.V}
    (hB : B ∈ 𝔅.members) (hB' : B' ∈ 𝔅.members)
    (hBU : B ⊆ U) (hB'U : B' ⊆ Uᶜ) :
    (𝔅.order : ℤ) ≤ edgeCut G U + 1 := by
  classical
  -- The cut, as a finite set of ordered pairs `(U`-end, `Uᶜ`-end`)`.  Working with
  -- pairs rather than with `Sym2` keeps the two shores syntactically separate;
  -- parallel edges are collapsed here, which only helps the count.
  set P : Finset (G.V × G.V) :=
    Finset.univ.filter (fun p : G.V × G.V => p.1 ∈ U ∧ p.2 ∉ U ∧ 0 < numEdges G p.1 p.2)
    with hPdef
  have hmemP : ∀ p : G.V × G.V,
      p ∈ P ↔ (p.1 ∈ U ∧ p.2 ∉ U ∧ 0 < numEdges G p.1 p.2) := by
    intro p; simp [hPdef]
  -- The two shores.
  set X : Finset G.V := P.image Prod.fst with hXdef
  set Y : Finset G.V := P.image Prod.snd with hYdef
  have hmemX : ∀ v : G.V, v ∈ X ↔ ∃ w : G.V, ((v, w) : G.V × G.V) ∈ P := by
    intro v
    simp only [hXdef, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, by simpa using hp⟩
    · rintro ⟨w, hw⟩
      exact ⟨(v, w), hw, rfl⟩
  have hmemY : ∀ v : G.V, v ∈ Y ↔ ∃ w : G.V, ((w, v) : G.V × G.V) ∈ P := by
    intro v
    simp only [hYdef, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, by simpa using hp⟩
    · rintro ⟨w, hw⟩
      exact ⟨(w, v), hw, rfl⟩
  have hXU : ∀ v ∈ X, v ∈ U := by
    intro v hv
    obtain ⟨w, hw⟩ := (hmemX v).mp hv
    exact ((hmemP _).mp hw).1
  have hYU : ∀ v ∈ Y, v ∉ U := by
    intro v hv
    obtain ⟨w, hw⟩ := (hmemY v).mp hv
    exact ((hmemP _).mp hw).2.1
  -- A connected set meeting both sides of the cut contains a whole cut edge.
  have hcross : ∀ A : Finset G.V,
      ((underlyingSimpleGraph G).induce (↑A : Set G.V)).Connected →
      ∀ a ∈ A, ∀ b ∈ A, a ∈ U → b ∉ U →
      ∃ p : G.V × G.V, p ∈ P ∧ p.1 ∈ A ∧ p.2 ∈ A := by
    intro A hconn a ha b hb haU hbU
    obtain ⟨w⟩ := hconn.preconnected ⟨a, Finset.mem_coe.mpr ha⟩ ⟨b, Finset.mem_coe.mpr hb⟩
    obtain ⟨z₁, hz₁, z₂, hz₂, hadj⟩ :=
      exists_adj_across_of_walk (S := {z : ↥(↑A : Set G.V) | (↑z : G.V) ∈ U}) w haU hbU
    refine ⟨((↑z₁ : G.V), (↑z₂ : G.V)), (hmemP _).mpr ⟨hz₁, hz₂, by simpa using hadj⟩,
      Finset.mem_coe.mp z₁.2, Finset.mem_coe.mp z₂.2⟩
  -- Any member inside `U` is disjoint from `B'`, hence joined to it by a cut edge.
  have hedgeUp : ∀ A ∈ 𝔅.members, A ⊆ U →
      ∃ x ∈ A, ∃ y ∈ B', 0 < numEdges G x y := by
    intro A hA hAU
    rcases 𝔅.exists_inter_or_adj hA hB' with hint | ⟨x, hx, y, hy, hadj⟩
    · obtain ⟨z, hz⟩ := hint
      obtain ⟨hzA, hzB'⟩ := Finset.mem_inter.mp hz
      exact absurd (hAU hzA) (Finset.mem_compl.mp (hB'U hzB'))
    · exact ⟨x, hx, y, hy, by simpa using hadj⟩
  -- **The key choice**: among the members contained in `U`, one whose shore trace
  -- is inclusionwise minimal (realized here by minimizing its cardinality).
  set M : Finset (Finset G.V) := 𝔅.members.filter (fun A => A ⊆ U) with hMdef
  have hBM : B ∈ M := by simp [hMdef, hB, hBU]
  obtain ⟨B₀, hB₀M, hB₀min⟩ :=
    Finset.exists_min_image M (fun A => (A ∩ X).card) ⟨B, hBM⟩
  have hB₀mem : B₀ ∈ 𝔅.members := (Finset.mem_filter.mp hB₀M).1
  have hB₀U : B₀ ⊆ U := (Finset.mem_filter.mp hB₀M).2
  -- Any member on the far side is joined to `B₀` by a cut edge.
  have hedgeDown : ∀ A ∈ 𝔅.members, (∀ a ∈ A, a ∉ U) →
      ∃ x ∈ A, ∃ y ∈ B₀, 0 < numEdges G x y := by
    intro A hA hAU
    rcases 𝔅.exists_inter_or_adj hA hB₀mem with hint | ⟨x, hx, y, hy, hadj⟩
    · obtain ⟨z, hz⟩ := hint
      obtain ⟨hzA, hzB₀⟩ := Finset.mem_inter.mp hz
      exact absurd (hB₀U hzB₀) (hAU z hzA)
    · exact ⟨x, hx, y, hy, by simpa using hadj⟩
  -- The distinguished extra vertex.
  obtain ⟨s, hsB₀, y₀, hy₀, hadj₀⟩ := hedgeUp B₀ hB₀mem hB₀U
  have hsX : s ∈ X :=
    (hmemX s).mpr ⟨y₀, (hmemP _).mpr
      ⟨hB₀U hsB₀, Finset.mem_compl.mp (hB'U hy₀), hadj₀⟩⟩
  -- One endpoint per cut edge: the `U`-end unless it lies in `B₀`.
  set f : G.V × G.V → G.V := fun p => if p.1 ∈ B₀ then p.2 else p.1 with hfdef
  set S : Finset G.V := insert s (P.image f) with hSdef
  have hhit : 𝔅.IsHittingSet S := by
    intro A hA
    have hAconn := 𝔅.connected_mem A hA
    by_cases hAY : A ∩ Y = ∅
    · -- Case 1: `A` avoids the far shore, so `A ⊆ U`.
      have hAU : A ⊆ U := by
        intro a ha
        by_contra haU
        by_cases hmeet : ∃ b ∈ A, b ∈ U
        · obtain ⟨b, hb, hbU⟩ := hmeet
          obtain ⟨p, hpP, hp1, hp2⟩ := hcross A hAconn b hb a ha hbU haU
          have hmem : p.2 ∈ A ∩ Y :=
            Finset.mem_inter.mpr ⟨hp2, (hmemY _).mpr ⟨p.1, by simpa using hpP⟩⟩
          rw [hAY] at hmem
          exact absurd hmem (Finset.notMem_empty _)
        · push Not at hmeet
          obtain ⟨x, hx, y, hy, hadj⟩ := hedgeDown A hA hmeet
          have hmem : x ∈ A ∩ Y :=
            Finset.mem_inter.mpr ⟨hx, (hmemY _).mpr ⟨y, (hmemP _).mpr
              ⟨hB₀U hy, hmeet x hx, by rw [num_edges_symmetric]; exact hadj⟩⟩⟩
          rw [hAY] at hmem
          exact absurd hmem (Finset.notMem_empty _)
      have hAM : A ∈ M := by simp [hMdef, hA, hAU]
      obtain ⟨a, ha, y, hy, hadj⟩ := hedgeUp A hA hAU
      have haX : a ∈ X :=
        (hmemX a).mpr ⟨y, (hmemP _).mpr
          ⟨hAU ha, Finset.mem_compl.mp (hB'U hy), hadj⟩⟩
      by_cases hsub : ∃ x ∈ A ∩ X, x ∉ B₀
      · -- a shore vertex of `A` outside `B₀` was selected for its own cut edge
        obtain ⟨x, hxAX, hxB₀⟩ := hsub
        obtain ⟨hxA, hxX⟩ := Finset.mem_inter.mp hxAX
        obtain ⟨w, hw⟩ := (hmemX x).mp hxX
        refine ⟨x, Finset.mem_inter.mpr ⟨hxA, ?_⟩⟩
        rw [hSdef]
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨(x, w), hw, by simp [hfdef, hxB₀]⟩)
      · -- otherwise minimality of `B₀ ∩ X` forces `A ∩ X = B₀ ∩ X`, so `s ∈ A`
        push Not at hsub
        have hsubset : A ∩ X ⊆ B₀ ∩ X := fun x hx =>
          Finset.mem_inter.mpr ⟨hsub x hx, (Finset.mem_inter.mp hx).2⟩
        have heq : A ∩ X = B₀ ∩ X :=
          Finset.eq_of_subset_of_card_le hsubset (hB₀min A hAM)
        have hsmem : s ∈ A ∩ X := by
          rw [heq]; exact Finset.mem_inter.mpr ⟨hsB₀, hsX⟩
        exact ⟨s, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hsmem).1,
          by rw [hSdef]; exact Finset.mem_insert_self s _⟩⟩
    · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hAY
      obtain ⟨hbA, hbY⟩ := Finset.mem_inter.mp hb
      have hbU : b ∉ U := hYU b hbY
      by_cases hAX : A ∩ X = ∅
      · -- Case 2: `A` avoids the near shore, so `A ⊆ Uᶜ`, and it is joined to `B₀`
        have hAU : ∀ a ∈ A, a ∉ U := by
          intro a ha haU
          obtain ⟨p, hpP, hp1, hp2⟩ := hcross A hAconn a ha b hbA haU hbU
          have hmem : p.1 ∈ A ∩ X :=
            Finset.mem_inter.mpr ⟨hp1, (hmemX _).mpr ⟨p.2, by simpa using hpP⟩⟩
          rw [hAX] at hmem
          exact absurd hmem (Finset.notMem_empty _)
        obtain ⟨x, hx, y, hy, hadj⟩ := hedgeDown A hA hAU
        have hpP : ((y, x) : G.V × G.V) ∈ P :=
          (hmemP _).mpr ⟨hB₀U hy, hAU x hx, by rw [num_edges_symmetric]; exact hadj⟩
        refine ⟨x, Finset.mem_inter.mpr ⟨hx, ?_⟩⟩
        rw [hSdef]
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨(y, x), hpP, by simp [hfdef, hy]⟩)
      · -- Case 3: `A` meets both shores, so it contains a whole cut edge
        obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hAX
        obtain ⟨haA, haX⟩ := Finset.mem_inter.mp ha
        obtain ⟨p, hpP, hp1, hp2⟩ := hcross A hAconn a haA b hbA (hXU a haX) hbU
        refine ⟨f p, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
        · by_cases hc : p.1 ∈ B₀ <;> simp [hfdef, hc, hp1, hp2]
        · rw [hSdef]
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hpP, rfl⟩)
  -- Counting: one vertex per cut edge, plus `s`.
  have hScard : S.card ≤ P.card + 1 := by
    rw [hSdef]
    exact le_trans (Finset.card_insert_le _ _)
      (Nat.add_le_add_right Finset.card_image_le 1)
  have hPsub : P ⊆ U ×ˢ Uᶜ := by
    intro p hp
    obtain ⟨h1, h2, _⟩ := (hmemP p).mp hp
    exact Finset.mem_product.mpr ⟨h1, Finset.mem_compl.mpr h2⟩
  have hPle : (P.card : ℤ) ≤ edgeCut G U := by
    have h1 : (P.card : ℤ) = ∑ _p ∈ P, (1 : ℤ) := by simp
    have h2 : ∑ _p ∈ P, (1 : ℤ) ≤ ∑ p ∈ P, (numEdges G p.1 p.2 : ℤ) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have := ((hmemP p).mp hp).2.2
      omega
    have h3 : ∑ p ∈ P, (numEdges G p.1 p.2 : ℤ)
        ≤ ∑ p ∈ U ×ˢ Uᶜ, (numEdges G p.1 p.2 : ℤ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hPsub fun _ _ _ => Int.natCast_nonneg _
    have h4 : ∑ p ∈ U ×ˢ Uᶜ, (numEdges G p.1 p.2 : ℤ) = edgeCut G U := by
      rw [Finset.sum_product]
      unfold edgeCut edgesBetween
      push_cast
      rfl
    linarith
  have hord := 𝔅.order_le_card_of_isHittingSet hhit
  have : (𝔅.order : ℤ) ≤ (P.card : ℤ) + 1 := by exact_mod_cast le_trans hord hScard
  linarith

/-- **The charge of a legal set.**  A legally fired set pays one chip per edge
leaving it, so it must have been carrying at least `edgeCut G U` chips. -/
theorem charge_of_legal {D : CFDiv G} {U : Finset G.V} (hU : legalSet G D U) :
    edgeCut G U ≤ ∑ v ∈ U, D v := by
  rw [edgeCut_eq_sum_outdeg]
  exact Finset.sum_le_sum fun v hv => hU v hv

/-- The degree of an effective divisor bounds any cut it can legally fire. -/
theorem edgeCut_le_deg_of_legal {D : CFDiv G} {U : Finset G.V} (hD : effective D)
    (hU : legalSet G D U) : edgeCut G U ≤ deg D := by
  refine le_trans (charge_of_legal hU) ?_
  have : ∑ v ∈ U, D v ≤ ∑ v : G.V, D v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun v _ _ => hD v
  exact this

/-! ## Theorem A -/

/-- **Theorem A** (van Dobben de Bruyn--Gijswijt §2).  Every bramble of a
connected graph has order at most `divisorialGonality G + 1`.

Proved (2026-08-25); this is the main theorem of §2 of the paper.  The proof
narrative, matching the code line for line:

Let `d = divisorialGonality G`.  Among all effective divisors `D` of degree `d`
with `rank G D ≥ 1` (a nonempty finite-to-choose-from family: nonempty by
`exists_divisor_of_divisorialGonality`), choose one **maximizing the number of
members of `𝔅` that `divisorSupport D` hits**.  This is a finite extremal choice:
the quantity being maximized is `(𝔅.members.filter fun B => (B ∩ divisorSupport D).Nonempty).card`,
bounded by `𝔅.members.card`.

*Case 1: `divisorSupport D` hits every member.*  Then `divisorSupport D` is a
hitting set, so `𝔅.order ≤ (divisorSupport D).card ≤ deg D = d` by
`Bramble.order_le_card_of_isHittingSet` and `card_divisorSupport_le_deg` — even
better than claimed.

*Case 2: some member `B₀` is unhit.*  Pick `v ∈ B₀` (members are nonempty,
`Bramble.nonempty_of_mem`).  Run the nested legal chain of
`exists_nested_legal_chain` at `q = v`: sets `U 0 ⊆ U 1 ⊆ … ⊆ U (k-1) ⊆ univ.erase v`
with divisors `Dᵢ = fireChain G D U i`, every `Dᵢ` effective
(`fireChain_effective`), every `Dᵢ` linearly equivalent to `D`
(`fireChain_linear_equiv`, so `deg Dᵢ = d` and `rank G Dᵢ ≥ 1`), and `D_k`
`v`-reduced. By `one_le_apply_of_q_reduced_of_rank_geq_one`, `D_k v ≥ 1`, so
`D_k` **does** hit `B₀`.

Let `i` be the first index at which the family of members hit by `D` fails to be
contained in the family hit by `D_i`.  Such an `i` exists: otherwise the hit
family only grows along the chain, while `B₀` is newly hit at the end, so `D_k`
would hit strictly more members than `D`, contradicting the extremal choice of
`D` (`D_k` is a competitor: effective, degree `d`, rank `≥ 1`).  Note `i ≥ 1`
because `D_0 = D`.

Write `U = U (i-1)`, `B'` for the member hit by `D` (hence, by minimality of `i`,
also by `D_{i-1}`) and unhit by `D_i`.  Then:

* `support_containment` applied to `D_{i-1}`, `U`, `B'` gives `B' ⊆ U`;
* `B₀ ⊆ Uᶜ`, by the paper's *second* index: maximality of `D` also forces
  `B₀ ∩ supp D_{i-1} = ∅` (otherwise `D_{i-1}` hits strictly more members than
  `D`), and `B₀` is hit by `D_k`, so there is a first `j ≥ i-1` with
  `B₀ ∩ supp D_j = ∅` and `B₀ ∩ supp D_{j+1} ≠ ∅`.  Since firing `(U j)ᶜ` undoes
  firing `U j` (`set_firing_compl_set_firing`), `support_containment` applied to `D_{j+1}`
  and the fired set `(U j)ᶜ` gives `B₀ ⊆ (U j)ᶜ ⊆ (U (i-1))ᶜ` by nestedness.
* `hitting_of_cut` for the pair `(B', B₀)` gives `𝔅.order ≤ edgeCut G U + 1`;
* `charge_of_legal`/`edgeCut_le_deg_of_legal` for the legal set `U` at `D_{i-1}`
  gives `edgeCut G U ≤ deg D_{i-1} = d`.

Hence `𝔅.order ≤ d + 1` in both cases.

The extremal choice is realized as `Nat.sSup` of the (nonempty, bounded by
`𝔅.members.card`) set of achievable hit counts, which avoids having to know that
the family of competitors is finite. -/
theorem bramble_order_le_gonality_succ (h_conn : graphConnected G)
    (𝔅 : Bramble (underlyingSimpleGraph G)) :
    𝔅.order ≤ divisorialGonality G + 1 := by
  classical
  set d : ℕ := divisorialGonality G with hd
  -- The members a divisor's support hits.
  set hitFam : CFDiv G → Finset (Finset G.V) :=
    fun E => 𝔅.members.filter (fun B => (B ∩ divisorSupport E).Nonempty) with hhitFam
  have hmemHit : ∀ (E : CFDiv G) (A : Finset G.V),
      A ∈ hitFam E ↔ (A ∈ 𝔅.members ∧ (A ∩ divisorSupport E).Nonempty) := by
    intro E A; simp [hhitFam]
  -- **The extremal choice**: among the effective degree-`d` divisors of rank ≥ 1,
  -- one hitting the most members.  The maximum exists because the counts form a
  -- nonempty set of naturals bounded by `𝔅.members.card`.
  set N : Set ℕ :=
    {n | ∃ E : CFDiv G, effective E ∧ deg E = (d : ℤ) ∧ rank G E ≥ 1 ∧ (hitFam E).card = n}
    with hNdef
  have hNne : N.Nonempty := by
    obtain ⟨E, hEeff, hEdeg, hErank⟩ := exists_divisor_of_divisorialGonality h_conn
    exact ⟨(hitFam E).card, E, hEeff, hEdeg, hErank, rfl⟩
  have hNbdd : BddAbove N := by
    refine ⟨𝔅.members.card, ?_⟩
    rintro n ⟨E, -, -, -, rfl⟩
    exact Finset.card_filter_le _ _
  obtain ⟨D, hDeff, hDdeg, hDrank, hDcard⟩ := Nat.sSup_mem hNne hNbdd
  have hmax : ∀ E : CFDiv G, effective E → deg E = (d : ℤ) → rank G E ≥ 1 →
      (hitFam E).card ≤ (hitFam D).card := by
    intro E h1 h2 h3
    rw [hDcard]
    exact le_csSup hNbdd ⟨E, h1, h2, h3, rfl⟩
  by_cases hcase : 𝔅.IsHittingSet (divisorSupport D)
  · -- *Case 1*: the support already hits everything, and the bound is even better.
    have h1 : 𝔅.order ≤ (divisorSupport D).card := 𝔅.order_le_card_of_isHittingSet hcase
    have h2 : ((divisorSupport D).card : ℤ) ≤ (d : ℤ) := by
      rw [← hDdeg]; exact card_divisorSupport_le_deg hDeff
    have h3 : ((𝔅.order : ℤ)) ≤ ((divisorSupport D).card : ℤ) := by exact_mod_cast h1
    have : ((𝔅.order : ℤ)) ≤ (d : ℤ) + 1 := by linarith
    exact_mod_cast this
  · -- *Case 2*: some member `B₀` is unhit; run the nested chain at a vertex of it.
    unfold Bramble.IsHittingSet at hcase
    push Not at hcase
    obtain ⟨B₀, hB₀mem, hB₀miss'⟩ := hcase
    obtain ⟨v, hv⟩ := 𝔅.nonempty_of_mem hB₀mem
    obtain ⟨k, U, hUsub, _hUne, hUmono, hUlegal, hUred⟩ :=
      exists_nested_legal_chain h_conn v hDeff
    have hEff : ∀ t, t ≤ k → effective (fireChain G D U t) :=
      fireChain_effective hDeff hUlegal
    have hDegT : ∀ t, deg (fireChain G D U t) = (d : ℤ) := by
      intro t
      have h := linear_equiv_preserves_deg G D (fireChain G D U t) (fireChain_linear_equiv D U t)
      rw [← h]; exact hDdeg
    have hRankT : ∀ t, rank G (fireChain G D U t) ≥ 1 := by
      intro t
      rw [← Utilities.rank_eq_of_linear_equiv G (fireChain_linear_equiv D U t)]
      exact hDrank
    -- The end of the chain does hit `B₀`, because it has a chip at `v`.
    have hvk : 1 ≤ fireChain G D U k v :=
      one_le_apply_of_q_reduced_of_rank_geq_one hUred (hRankT k)
    have hB₀k : (B₀ ∩ divisorSupport (fireChain G D U k)).Nonempty :=
      ⟨v, Finset.mem_inter.mpr ⟨hv, mem_divisorSupport.mpr (by omega)⟩⟩
    have hB₀notD : B₀ ∉ hitFam D := by
      intro hc
      have hne := ((hmemHit _ _).mp hc).2
      rw [hB₀miss'] at hne
      exact absurd hne (by simp)
    -- **The index bookkeeping.**  Some step loses a member that `D` hit; otherwise
    -- the end of the chain would hit strictly more members than `D` itself.
    have hex : ∃ t, t ≤ k ∧ ¬ (hitFam D ⊆ hitFam (fireChain G D U t)) := by
      by_contra hcon
      push Not at hcon
      have hsub : hitFam D ⊆ hitFam (fireChain G D U k) := hcon k le_rfl
      have hmemk : B₀ ∈ hitFam (fireChain G D U k) := (hmemHit _ _).mpr ⟨hB₀mem, hB₀k⟩
      have hss : hitFam D ⊂ hitFam (fireChain G D U k) :=
        (Finset.ssubset_iff_of_subset hsub).mpr ⟨B₀, hmemk, hB₀notD⟩
      have h1 := Finset.card_lt_card hss
      have h2 := hmax (fireChain G D U k) (hEff k le_rfl) (hDegT k) (hRankT k)
      omega
    obtain ⟨i, ⟨hik, hiQ⟩, hmin⟩ :
        ∃ i, (i ≤ k ∧ ¬ (hitFam D ⊆ hitFam (fireChain G D U i))) ∧
          ∀ m, m < i → ¬ (m ≤ k ∧ ¬ (hitFam D ⊆ hitFam (fireChain G D U m))) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
    have hipos : 0 < i := by
      rcases Nat.eq_zero_or_pos i with h0 | h
      · subst h0
        exact absurd (Finset.Subset.refl (hitFam D)) hiQ
      · exact h
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hi'k : i' < k := by omega
    have hi'sub : hitFam D ⊆ hitFam (fireChain G D U i') := by
      by_contra h
      exact hmin i' (by omega) ⟨by omega, h⟩
    obtain ⟨B', hB'D, hB'i⟩ :
        ∃ A, A ∈ hitFam D ∧ A ∉ hitFam (fireChain G D U (i' + 1)) := by
      by_contra h
      push Not at h
      exact hiQ fun a ha => h a ha
    have hB'mem : B' ∈ 𝔅.members := ((hmemHit _ _).mp hB'D).1
    have hB'meet : (B' ∩ divisorSupport (fireChain G D U i')).Nonempty :=
      ((hmemHit _ _).mp (hi'sub hB'D)).2
    have hB'miss : B' ∩ divisorSupport (fireChain G D U (i' + 1)) = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro hne
      exact hB'i ((hmemHit _ _).mpr ⟨hB'mem, hne⟩)
    have hB'U : B' ⊆ U i' :=
      support_containment (hEff i' (by omega)) (𝔅.connected_mem B' hB'mem) hB'meet hB'miss
    -- `B₀` is still unhit just before the losing step, again by maximality of `D`.
    have hB₀i' : B₀ ∩ divisorSupport (fireChain G D U i') = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro hne
      have hmemi : B₀ ∈ hitFam (fireChain G D U i') := (hmemHit _ _).mpr ⟨hB₀mem, hne⟩
      have hss : hitFam D ⊂ hitFam (fireChain G D U i') :=
        (Finset.ssubset_iff_of_subset hi'sub).mpr ⟨B₀, hmemi, hB₀notD⟩
      have h1 := Finset.card_lt_card hss
      have h2 := hmax (fireChain G D U i') (hEff i' (by omega)) (hDegT i') (hRankT i')
      omega
    -- The first later step at which `B₀` becomes hit; reverse it to place `B₀`
    -- outside the fired set.
    have hjex : ∃ t, i' ≤ t ∧ t ≤ k ∧ (B₀ ∩ divisorSupport (fireChain G D U t)).Nonempty :=
      ⟨k, by omega, le_rfl, hB₀k⟩
    obtain ⟨j, ⟨hji', hjk, hjne⟩, hjmin⟩ :
        ∃ j, (i' ≤ j ∧ j ≤ k ∧ (B₀ ∩ divisorSupport (fireChain G D U j)).Nonempty) ∧
          ∀ m, m < j →
            ¬ (i' ≤ m ∧ m ≤ k ∧ (B₀ ∩ divisorSupport (fireChain G D U m)).Nonempty) :=
      ⟨Nat.find hjex, Nat.find_spec hjex, fun m hm => Nat.find_min hjex hm⟩
    have hjpos : i' < j := by
      rcases Nat.lt_or_ge i' j with h | h
      · exact h
      · exfalso
        have hje : j = i' := le_antisymm h hji'
        rw [hje, hB₀i'] at hjne
        simp at hjne
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hj'i : i' ≤ j' := by omega
    have hj'k : j' < k := by omega
    have hB₀j' : B₀ ∩ divisorSupport (fireChain G D U j') = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro hne
      exact hjmin j' (by omega) ⟨hj'i, by omega, hne⟩
    have hB₀compl : B₀ ⊆ (U j')ᶜ := by
      refine support_containment (D := fireChain G D U (j' + 1)) (U := (U j')ᶜ) (B := B₀)
        (hEff (j' + 1) (by omega)) (𝔅.connected_mem B₀ hB₀mem) hjne ?_
      have hrev : setFiring G (fireChain G D U (j' + 1)) (U j')ᶜ =
          fireChain G D U j' := by
        rw [fireChain_succ, set_firing_compl_set_firing]
      rw [hrev]
      exact hB₀j'
    have hB₀i'c : B₀ ⊆ (U i')ᶜ := by
      intro z hz
      have h1 := hB₀compl hz
      rw [Finset.mem_compl] at h1 ⊢
      exact fun hc => h1 (hUmono i' j' hj'i hj'k hc)
    -- The two §2 lemmas close the argument.
    have horder := hitting_of_cut 𝔅 hB'mem hB₀mem hB'U hB₀i'c
    have hcut := edgeCut_le_deg_of_legal (hEff i' (by omega)) (hUlegal i' (by omega))
    rw [hDegT i'] at hcut
    have : ((𝔅.order : ℤ)) ≤ (d : ℤ) + 1 := by linarith
    exact_mod_cast this

end Utilities.Gonality
