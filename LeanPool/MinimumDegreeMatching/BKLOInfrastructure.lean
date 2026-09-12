/-
Copyright (c) 2026 Juan Pablo Traverso Giannini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Giannini, Aristotle
-/
import LeanPool.MinimumDegreeMatching.Spread
import Mathlib.Tactic.Order
import Mathlib.Tactic.Push

/-!
# Finite edge-set infrastructure for BKLO Lemma 10.7 at `r = 2`

This module contains only the finite graph vocabulary needed by the pseudorandom simultaneous
matching theorem. It is extracted from the independently frozen Paper III development and is kept
separate from the theorem-facing API.
-/

open Finset

namespace BKLOK2

variable {V : Type*} [DecidableEq V]

/-- The edge set (as `Sym2`) of a `Finset` of vertices, viewed as a complete graph on that set:
all unordered pairs of distinct vertices of `t`.  For a 3-set this is the triangle's three edges. -/
def cliqueEdges (t : Finset V) : Finset (Sym2 V) :=
  (t.sym2).filter (fun e => ¬ e.IsDiag)


theorem mem_cliqueEdgesV {t : Finset V} {e : Sym2 V} :
    e ∈ cliqueEdges t ↔ (∀ x ∈ e, x ∈ t) ∧ ¬ e.IsDiag := by
  simp [cliqueEdges, Finset.mem_sym2_iff]


/-- The number of edges of `E` at `v`. -/
def edeg (E : Finset (Sym2 V)) (v : V) : ℕ := (E.filter (fun e => v ∈ e)).card


/-- `N_E(x, S)`: the neighbours of `x` inside `S`. -/
def nbhdIn (E : Finset (Sym2 V)) (x : V) (S : Finset V) : Finset V :=
  S.filter (fun y => s(x, y) ∈ E)

/-- `d_E(x, S) = |N_E(x, S)|`. -/
def degTo (E : Finset (Sym2 V)) (x : V) (S : Finset V) : ℕ := (nbhdIn E x S).card

theorem mem_nbhdIn {E : Finset (Sym2 V)} {x y : V} {S : Finset V} :
    y ∈ nbhdIn E x S ↔ y ∈ S ∧ s(x, y) ∈ E := by
  simp [nbhdIn]

theorem nbhdIn_subset (E : Finset (Sym2 V)) (x : V) (S : Finset V) : nbhdIn E x S ⊆ S :=
  Finset.filter_subset _ _



/-- `E[S]`: the edges of `E` with both ends in `S`. -/
def edgesIn (E : Finset (Sym2 V)) (S : Finset V) : Finset (Sym2 V) :=
  E.filter (fun e => e ∈ S.sym2)

/-- `E[S, T]`: the edges of `E` with one end in `S` and the other in `T`. -/
def edgesBtw (E : Finset (Sym2 V)) (S T : Finset V) : Finset (Sym2 V) :=
  E.filter (fun e => ∃ a ∈ S, ∃ b ∈ T, e = s(a, b))

/-- `E − E[P] = ⋃_{W ∈ P} E[W]`: the edges of `E` lying inside a part of `P`. -/
def insideParts (E : Finset (Sym2 V)) (P : Finset (Finset V)) : Finset (Sym2 V) :=
  E.filter (fun e => ∃ W ∈ P, e ∈ W.sym2)

/-- `E[P]`: the edges of `E` joining two different parts of `P`. -/
def crossParts (E : Finset (Sym2 V)) (P : Finset (Finset V)) : Finset (Sym2 V) :=
  E.filter (fun e => ¬ ∃ W ∈ P, e ∈ W.sym2)

theorem mem_edgesIn {E : Finset (Sym2 V)} {S : Finset V} {e : Sym2 V} :
    e ∈ edgesIn E S ↔ e ∈ E ∧ ∀ v ∈ e, v ∈ S := by
  simp [edgesIn, Finset.mem_sym2_iff]

theorem mem_insideParts {E : Finset (Sym2 V)} {P : Finset (Finset V)} {e : Sym2 V} :
    e ∈ insideParts E P ↔ e ∈ E ∧ ∃ W ∈ P, ∀ v ∈ e, v ∈ W := by
  simp [insideParts, Finset.mem_sym2_iff]

theorem mem_crossParts {E : Finset (Sym2 V)} {P : Finset (Finset V)} {e : Sym2 V} :
    e ∈ crossParts E P ↔ e ∈ E ∧ ¬ ∃ W ∈ P, ∀ v ∈ e, v ∈ W := by
  simp [crossParts, Finset.mem_sym2_iff]

theorem edgesIn_subset (E : Finset (Sym2 V)) (S : Finset V) : edgesIn E S ⊆ E :=
  Finset.filter_subset _ _



/-- `d_E({x,y}, W) = |N_E(x,W) ∩ N_E(y,W)|`, the codegree of the pair `x, y` inside `W`. -/
def codegTo (E : Finset (Sym2 V)) (x y : V) (W : Finset V) : ℕ :=
  (nbhdIn E x W ∩ nbhdIn E y W).card


/-- The edges of a triangle family. -/
def famEdges (P : Finset (Finset V)) : Finset (Sym2 V) := P.biUnion cliqueEdges


/-- A `Finset (Finset V)` is a **matching** avoiding `x`: every member is a `2`-element set, the
members are pairwise disjoint, and none contains `x`. -/
structure IsMatchingAvoiding (M : Finset (Finset V)) (x : V) : Prop where
  card_two : ∀ e ∈ M, e.card = 2
  pairwise_disjoint : (M : Set (Finset V)).Pairwise Disjoint
  avoids : ∀ e ∈ M, x ∉ e


/-- The matching induced by a partner function `f` on `S`: the orbit `{a, f a}` for each `a ∈ S`. -/
def involutionMatching (S : Finset V) (f : V → V) : Finset (Finset V) :=
  S.image (fun a => {a, f a})

/-- **A fixed-point-free involution on `S` gives a matching of `S`, avoiding any `x ∉ S`.** -/
theorem isMatchingAvoiding_involutionMatching {S : Finset V} {f : V → V} {x : V}
    (hmap : ∀ a ∈ S, f a ∈ S) (hinv : ∀ a ∈ S, f (f a) = a) (hne : ∀ a ∈ S, f a ≠ a)
    (hx : x ∉ S) : IsMatchingAvoiding (involutionMatching S f) x := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- every orbit is a 2-element set
    intro e he
    rw [involutionMatching, Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    rw [Finset.card_pair (hne a ha).symm]
  · -- distinct orbits are disjoint
    intro e he f' hf' hef
    rw [Finset.mem_coe, involutionMatching, Finset.mem_image] at he hf'
    obtain ⟨a, ha, rfl⟩ := he
    obtain ⟨b, hb, rfl⟩ := hf'
    refine Finset.disjoint_left.2 fun c hc hc' => hef ?_
    -- the orbit `{w, f w}` of any `w ∈ {z, f z}` is `{z, f z}` itself
    have key : ∀ z ∈ S, ∀ w, w ∈ ({z, f z} : Finset V) → ({w, f w} : Finset V) = {z, f z} := by
      intro z hz w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rfl
      · rw [Finset.mem_singleton] at hw
        subst hw
        rw [hinv z hz]; exact Finset.pair_comm _ _
    -- so `{a, f a} = {c, f c} = {b, f b}`
    rw [← key a ha c hc]
    exact key b hb c hc'
  · -- the orbits avoid `x`
    intro e he
    rw [involutionMatching, Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    rw [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨fun h => hx (h ▸ ha), fun h => hx (h ▸ hmap a ha)⟩

/-- Every edge of `H` inside `S` is a clique edge of `S`, provided `H` is loopless. -/
theorem edgesIn_subset_cliqueEdges_loopless {H : Finset (Sym2 V)} (hloop : ∀ e ∈ H, ¬ e.IsDiag)
    (S : Finset V) : edgesIn H S ⊆ cliqueEdges S := by
  intro e he
  rw [mem_edgesIn] at he
  exact mem_cliqueEdgesV.2 ⟨he.2, hloop e he.1⟩

/-- The degree of `y ∈ S` into `S` is at most its edge degree in `H[S]`. -/
theorem degTo_le_edeg_edgesIn {H : Finset (Sym2 V)} {S : Finset V} {y : V} (hy : y ∈ S) :
    degTo H y S ≤ edeg (edgesIn H S) y := by
  classical
  have hinj : Set.InjOn (fun z => s(y, z)) (nbhdIn H y S) := by
    intro a _ b _ hab
    simp only [Sym2.eq_iff] at hab
    rcases hab with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  have hsub : (nbhdIn H y S).image (fun z => s(y, z))
      ⊆ (edgesIn H S).filter (fun e => y ∈ e) := by
    intro e he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 he
    rw [mem_nbhdIn] at hz
    refine Finset.mem_filter.2 ⟨mem_edgesIn.2 ⟨hz.2, ?_⟩, by simp⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact hy
    · exact hz.1
  calc degTo H y S = ((nbhdIn H y S).image (fun z => s(y, z))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ edeg (edgesIn H S) y := Finset.card_le_card hsub

/-- On a loopless edge set supported on `N`, counting neighbours of `v` is the same as counting
incident edges. This is the bridge from the BKLO finite-edge vocabulary to the generic spread
matching interface. -/
theorem card_edgeNeighbors_eq_edeg {A : Finset (Sym2 V)} {N : Finset V}
    (hAsub : A ⊆ cliqueEdges N) (v : V) :
    ((N.filter fun z => s(v, z) ∈ A).erase v).card = edeg A v := by
  classical
  unfold edeg
  apply Finset.card_bij (fun z _ => s(v, z))
  · intro z hz
    obtain ⟨-, hz'⟩ := Finset.mem_erase.1 hz
    obtain ⟨hzN, hzA⟩ := Finset.mem_filter.1 hz'
    exact Finset.mem_filter.2 ⟨hzA, by simp⟩
  · intro a ha b hb hab
    simp only [Sym2.eq_iff] at hab
    rcases hab with ⟨_, h⟩ | ⟨h₁, h₂⟩
    · exact h
    · exact h₂.trans h₁
  · intro e he
    obtain ⟨heA, hve⟩ := Finset.mem_filter.1 he
    have hcl := mem_cliqueEdgesV.1 (hAsub heA)
    induction e using Sym2.ind with
    | _ a b =>
      have haN : a ∈ N := hcl.1 a (by simp)
      have hbN : b ∈ N := hcl.1 b (by simp)
      have hab : a ≠ b := Sym2.mk_isDiag_iff.not.mp hcl.2
      simp only [Sym2.mem_iff] at hve
      rcases hve with rfl | rfl
      · refine ⟨b, ?_, rfl⟩
        exact Finset.mem_erase.2 ⟨hab.symm, Finset.mem_filter.2 ⟨hbN, heA⟩⟩
      · have heA' : s(v, a) ∈ A := by rwa [Sym2.eq_swap]
        refine ⟨a, Finset.mem_erase.2 ⟨hab, Finset.mem_filter.2 ⟨haN, heA'⟩⟩, ?_⟩
        exact Sym2.eq_swap

/-- The data the greedy sweep produces at an apex `x`: a perfect matching of `N_H(x,W)` avoiding
`x`, all of whose edges are edges of `H` inside `N_H(x,W)`. -/
structure GoodMatching (H : Finset (Sym2 V)) (W : Finset V) (x : V) (M : Finset (Finset V)) :
    Prop where
  matching : IsMatchingAvoiding M x
  subset : ∀ e ∈ M, e ⊆ nbhdIn H x W
  covers : ∀ a ∈ nbhdIn H x W, ∃ e ∈ M, a ∈ e
  edges : ∀ e ∈ M, cliqueEdges e ⊆ edgesIn H (nbhdIn H x W)

theorem edeg_le_edeg_sdiff_add_edeg (E F : Finset (Sym2 V)) (v : V) :
    edeg E v ≤ edeg (E \ F) v + edeg F v := by
  classical
  have hsub : E.filter (fun e => v ∈ e) ⊆
      (E \ F).filter (fun e => v ∈ e) ∪ F.filter (fun e => v ∈ e) := by
    intro e he
    rw [Finset.mem_filter] at he
    by_cases hF : e ∈ F
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hF, he.2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨he.1, hF⟩, he.2⟩)
  calc edeg E v ≤ ((E \ F).filter (fun e => v ∈ e) ∪ F.filter (fun e => v ∈ e)).card :=
        Finset.card_le_card hsub
    _ ≤ edeg (E \ F) v + edeg F v := Finset.card_union_le _ _

/-- **The slack absorbs the used edges.**  If every vertex has degree `≥ h + d` in `E`
(the `h + d` of Lemma 10.3(ii), `h = |N|/2`, `d` the slack) and the used set `D` has
degree `≤ d` at `v`, then the unused part `E \ D` still has degree `≥ h` at `v` — the
hypothesis Dirac needs. -/
theorem edeg_sdiff_ge_of_slack {E D : Finset (Sym2 V)} {v : V} {h d : ℕ}
    (hE : h + d ≤ edeg E v) (hD : edeg D v ≤ d) : h ≤ edeg (E \ D) v := by
  have hle := edeg_le_edeg_sdiff_add_edeg E D v
  omega



/-! ### Matchings from involutions -/

/-- The edges of the matching induced by a partner function are among the orbit edges. -/
theorem famEdges_involutionMatching_subset (N : Finset V) (f : V → V) :
    famEdges (involutionMatching N f) ⊆ N.image (fun a => s(a, f a)) := by
  classical
  intro e he
  rw [famEdges, Finset.mem_biUnion] at he
  obtain ⟨t, ht, het⟩ := he
  rw [involutionMatching, Finset.mem_image] at ht
  obtain ⟨a, ha, rfl⟩ := ht
  obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 het
  refine Finset.mem_image.2 ⟨a, ha, ?_⟩
  induction e using Sym2.ind with
  | _ p q =>
    have hp := hmem p (by simp)
    have hq := hmem q (by simp)
    rw [Sym2.mk_isDiag_iff] at hnd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl
    · rcases hq with rfl | rfl
      · exact absurd rfl hnd
      · rfl
    · rcases hq with rfl | rfl
      · rw [Sym2.eq_swap]
      · exact absurd rfl hnd

/-- **A partner involution gives all the data of a `GoodMatching`.**  This is the second half of
`BKLO.exists_perfect_matching_in`, with the involution supplied from outside. -/
theorem matching_data_of_involution {N : Finset V} {x : V} (hx : x ∉ N) {A : Finset (Sym2 V)}
    {f : V → V} (hmap : ∀ a ∈ N, f a ∈ N) (hinv : ∀ a ∈ N, f (f a) = a) (hfne : ∀ a ∈ N, f a ≠ a)
    (hadj : ∀ a ∈ N, s(a, f a) ∈ A) :
    IsMatchingAvoiding (involutionMatching N f) x ∧
      (∀ e ∈ involutionMatching N f, e ⊆ N) ∧
      (∀ a ∈ N, ∃ e ∈ involutionMatching N f, a ∈ e) ∧
      (∀ e ∈ involutionMatching N f, cliqueEdges e ⊆ A) := by
  classical
  refine ⟨isMatchingAvoiding_involutionMatching hmap hinv hfne hx, ?_, ?_, ?_⟩
  · intro e he
    rw [involutionMatching, Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ha
    · rw [Finset.mem_singleton] at hz; subst hz; exact hmap a ha
  · intro a ha
    exact ⟨{a, f a}, Finset.mem_image_of_mem _ ha, by simp⟩
  · intro e he
    rw [involutionMatching, Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    intro g hg
    obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 hg
    have hga : g = s(a, f a) := by
      induction g using Sym2.ind with
      | _ p q =>
        have hp := hmem p (by simp)
        have hq := hmem q (by simp)
        rw [Sym2.mk_isDiag_iff] at hnd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
        rcases hp with rfl | rfl
        · rcases hq with rfl | rfl
          · exact absurd rfl hnd
          · rfl
        · rcases hq with rfl | rfl
          · rw [Sym2.eq_swap]
          · exact absurd rfl hnd
    rw [hga]
    exact hadj a ha


end BKLOK2
