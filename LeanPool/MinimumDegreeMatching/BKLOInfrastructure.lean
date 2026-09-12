/-
Copyright (c) 2026 Juan Pablo Traverso Giannini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Giannini, Aristotle
-/
import LeanPool.MinimumDegreeMatching.Spread
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

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

/-! ### The graph induced by an edge set on a vertex subset -/

/-- The graph on the subtype `↥S` whose edges are the edges of `E` inside `S`. -/
def setGraph (S : Finset V) (E : Finset (Sym2 V)) : SimpleGraph {x // x ∈ S} where
  Adj a b := a ≠ b ∧ s((a : V), (b : V)) ∈ E
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (S : Finset V) (E : Finset (Sym2 V)) : DecidableRel (setGraph S E).Adj := by
  intro a b
  unfold setGraph
  infer_instance

/-- The embedding of `Sym2 ↥S` into `Sym2 V`. -/
def sym2val (S : Finset V) : Sym2 {x // x ∈ S} → Sym2 V := Sym2.map Subtype.val

omit [DecidableEq V] in
theorem sym2val_injective (S : Finset V) : Function.Injective (sym2val S) :=
  Sym2.map.injective Subtype.val_injective

omit [DecidableEq V] in
@[simp] theorem sym2val_mk (S : Finset V) (a b : {x // x ∈ S}) :
    sym2val S s(a, b) = s((a : V), (b : V)) := rfl

omit [DecidableEq V] in
theorem mem_sym2val (S : Finset V) (a : {x // x ∈ S}) (e : Sym2 {x // x ∈ S}) :
    (a : V) ∈ sym2val S e ↔ a ∈ e := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [sym2val_mk, Sym2.mem_iff]
    constructor
    · rintro (h | h)
      exacts [Or.inl (Subtype.ext h.symm).symm, Or.inr (Subtype.ext h.symm).symm]
    · rintro (rfl | rfl)
      exacts [Or.inl rfl, Or.inr rfl]

variable {S : Finset V} {E : Finset (Sym2 V)}

theorem mem_edgeFinset_setGraph {e : Sym2 {x // x ∈ S}} :
    e ∈ (setGraph S E).edgeFinset ↔ sym2val S e ∈ E ∧ ¬ e.IsDiag := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, sym2val_mk,
      Sym2.mk_isDiag_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- The edges of `setGraph S E`, pushed into `Sym2 V`, are exactly `E`. -/
theorem image_edgeFinset_setGraph (hE : E ⊆ cliqueEdges S) :
    (setGraph S E).edgeFinset.image (sym2val S) = E := by
  ext e
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (mem_edgeFinset_setGraph.1 hf).1
  · intro he
    obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 (hE he)
    induction e using Sym2.ind with
    | _ x y =>
      have hx : x ∈ S := hmem x (by simp)
      have hy : y ∈ S := hmem y (by simp)
      refine ⟨s((⟨x, hx⟩ : {x // x ∈ S}), ⟨y, hy⟩), ?_, rfl⟩
      refine mem_edgeFinset_setGraph.2 ⟨he, ?_⟩
      simp only [Sym2.mk_isDiag_iff]
      intro h
      exact hnd (by simpa [Sym2.mk_isDiag_iff] using congrArg Subtype.val h)

theorem card_edgeFinset_setGraph (hE : E ⊆ cliqueEdges S) :
    (setGraph S E).edgeFinset.card = E.card := by
  have h := Finset.card_image_of_injective (setGraph S E).edgeFinset (sym2val_injective S)
  rw [image_edgeFinset_setGraph hE] at h
  exact h.symm

theorem degree_setGraph (hE : E ⊆ cliqueEdges S) (a : {x // x ∈ S}) :
    (setGraph S E).degree a = edeg E (a : V) := by
  classical
  have h1 : (setGraph S E).degree a
      = ((setGraph S E).edgeFinset.filter (fun e => a ∈ e)).card := by
    rw [← (setGraph S E).card_incidenceFinset_eq_degree a,
      (setGraph S E).incidenceFinset_eq_filter a]
  have h2 : ((setGraph S E).edgeFinset.filter (fun e => a ∈ e)).image (sym2val S)
      = E.filter (fun e => (a : V) ∈ e) := by
    ext e
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨f, ⟨hf, haf⟩, rfl⟩
      exact ⟨(mem_edgeFinset_setGraph.1 hf).1, (mem_sym2val S a f).2 haf⟩
    · rintro ⟨he, hae⟩
      have hmem : e ∈ (setGraph S E).edgeFinset.image (sym2val S) := by
        rw [image_edgeFinset_setGraph hE]; exact he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hmem
      exact ⟨f, ⟨hf, (mem_sym2val S a f).1 hae⟩, rfl⟩
  rw [h1, edeg, ← h2, Finset.card_image_of_injective _ (sym2val_injective S)]

omit [DecidableEq V] in
theorem card_coe_eq (S : Finset V) : Fintype.card {x // x ∈ S} = S.card :=
  Fintype.card_coe S

/-- **Dirac, with the partner edges recorded.**  A nonempty even vertex set `N` carrying an edge
set `A ⊆ cliqueEdges N` of minimum degree at least `|N|/2` admits a fixed-point-free partner
involution whose orbit edges lie in `A`. -/
theorem exists_involution_adj {N : Finset V} {A : Finset (Sym2 V)}
    (hAsub : A ⊆ cliqueEdges N) (hEven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 ≤ edeg A v) (hne : N.Nonempty) :
    ∃ f : V → V, (∀ a ∈ N, f a ∈ N) ∧ (∀ a ∈ N, f (f a) = a) ∧ (∀ a ∈ N, f a ≠ a) ∧
      (∀ a ∈ N, s(a, f a) ∈ A) := by
  classical
  let _ : Nonempty {v // v ∈ N} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hdegG : ∀ a : {v // v ∈ N}, N.card / 2 ≤ (setGraph N A).degree a := by
    intro a
    rw [degree_setGraph hAsub a]
    exact hdeg (a : V) a.2
  have hmin : N.card / 2 ≤ (setGraph N A).minDegree :=
    SimpleGraph.le_minDegree_of_forall_le_degree _ (N.card / 2) hdegG
  obtain ⟨M, hM⟩ := SimpleGraph.exists_isPerfectMatching_of_card_le_minDegree
    (G := setGraph N A) (by rw [card_coe_eq]; exact hEven) (by simpa [card_coe_eq] using hmin)
  have hpartner : ∀ a : {v // v ∈ N}, ∃! b, M.Adj a b := fun a => hM.1 (hM.2 a)
  choose g hg huniq using hpartner
  have hginv : ∀ a, g (g a) = a := fun a => (huniq (g a) a (hg a).symm).symm
  have hgadj : ∀ a, (setGraph N A).Adj a (g a) := fun a => M.adj_sub (hg a)
  have hgne : ∀ a, g a ≠ a := by
    intro a h
    have hadj := hgadj a
    rw [h] at hadj
    exact hadj.ne rfl
  refine ⟨fun v => if h : v ∈ N then ((g ⟨v, h⟩ : {v // v ∈ N}) : V) else v, ?_, ?_, ?_, ?_⟩
  · intro a ha; simp only [dite_eq_left ha]; exact (g ⟨a, ha⟩).2
  · intro a ha
    simp only [dite_eq_left ha, dite_eq_left (g ⟨a, ha⟩).2]
    have h2 : (⟨((g ⟨a, ha⟩ : {v // v ∈ N}) : V), (g ⟨a, ha⟩).2⟩ : {v // v ∈ N}) = g ⟨a, ha⟩ := rfl
    rw [h2, hginv ⟨a, ha⟩]
  · intro a ha
    simp only [dite_eq_left ha]
    intro hcon
    exact hgne ⟨a, ha⟩ (Subtype.ext hcon)
  · intro a ha
    simp only [dite_eq_left ha]
    exact (hgadj ⟨a, ha⟩).2

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



/-- The edges of a partner involution meet each vertex at most once. -/
theorem edeg_image_partner_le_one {N : Finset V} {f : V → V}
    (hinv : ∀ a ∈ N, f (f a) = a) {v : V} :
    edeg (N.image (fun a => s(a, f a))) v ≤ 1 := by
  classical
  have hsub : (N.image (fun a => s(a, f a))).filter (fun e => v ∈ e)
      ⊆ ({s(v, f v)} : Finset (Sym2 V)) := by
    intro e he
    obtain ⟨heIm, hve⟩ := Finset.mem_filter.1 he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 heIm
    refine Finset.mem_singleton.2 ?_
    rcases Sym2.mem_iff.1 hve with h | h
    · rw [h]
    · have hfv : f v = a := by rw [h]; exact hinv a ha
      rw [hfv, h]
      exact Sym2.eq_swap
  exact le_trans (Finset.card_le_card hsub) (by simp)

/-- Deleting the edges of a partner involution deletes exactly the partner from each
neighbourhood. -/
theorem nbhdIn_sdiff_image_partner {N : Finset V} {A : Finset (Sym2 V)} {f : V → V}
    (hinv : ∀ a ∈ N, f (f a) = a) {y : V} (hy : y ∈ N) :
    nbhdIn (A \ N.image (fun a => s(a, f a))) y N = (nbhdIn A y N).erase (f y) := by
  classical
  ext z
  simp only [mem_nbhdIn, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_image]
  constructor
  · rintro ⟨hzN, hzA, hzE⟩
    refine ⟨?_, hzN, hzA⟩
    intro hzf
    exact hzE ⟨y, hy, by rw [hzf]⟩
  · rintro ⟨hzf, hzN, hzA⟩
    refine ⟨hzN, hzA, ?_⟩
    rintro ⟨a, ha, hae⟩
    rcases Sym2.eq_iff.1 hae with ⟨rfl, rfl⟩ | ⟨rfl, hfa⟩
    · exact hzf rfl
    · exact hzf (by rw [← hfa, hinv a ha])

/-- **Spread perfect matchings from Dirac slack (the inductive form).**  With `δ(A) ≥ |N|/2 + t`
there is a perfect matching of `N` inside `A` whose weight is at most a `1/(t+1)` fraction of the
total weight of the pairs still available in `A`. -/
theorem exists_spread_involution_aux {N : Finset V} (hEven : Even N.card)
    (w : V → V → ℝ) (hw : ∀ y z, 0 ≤ w y z) :
    ∀ (t : ℕ) (A : Finset (Sym2 V)), A ⊆ cliqueEdges N →
      (∀ v ∈ N, N.card / 2 + t ≤ edeg A v) →
      ∃ f : V → V, (∀ a ∈ N, f a ∈ N) ∧ (∀ a ∈ N, f (f a) = a) ∧ (∀ a ∈ N, f a ≠ a) ∧
        (∀ a ∈ N, s(a, f a) ∈ A) ∧
        ((t : ℝ) + 1) * ∑ y ∈ N, w y (f y) ≤ ∑ y ∈ N, ∑ z ∈ nbhdIn A y N, w y z := by
  classical
  rcases N.eq_empty_or_nonempty with rfl | hne
  · intro t A _ _
    exact ⟨id, by simp, by simp, by simp, by simp, by simp⟩
  intro t
  induction t with
  | zero =>
    intro A hAsub hdeg
    have hdeg0 : ∀ v ∈ N, N.card / 2 ≤ edeg A v := by
      intro v hv; have := hdeg v hv; omega
    obtain ⟨f, hmap, hinv, hfne, hadj⟩ := exists_involution_adj hAsub hEven hdeg0 hne
    refine ⟨f, hmap, hinv, hfne, hadj, ?_⟩
    rw [Nat.cast_zero, zero_add, one_mul]
    refine Finset.sum_le_sum fun y hy => ?_
    exact Finset.single_le_sum (f := fun z => w y z) (fun z _ => hw y z)
      (mem_nbhdIn.2 ⟨hmap y hy, hadj y hy⟩)
  | succ t ih =>
    intro A hAsub hdeg
    have hdeg0 : ∀ v ∈ N, N.card / 2 ≤ edeg A v := by
      intro v hv; have := hdeg v hv; omega
    obtain ⟨f₀, hmap0, hinv0, hne0, hadj0⟩ := exists_involution_adj hAsub hEven hdeg0 hne
    have hA'sub : A \ N.image (fun a => s(a, f₀ a)) ⊆ cliqueEdges N :=
      Finset.sdiff_subset.trans hAsub
    have hdeg' : ∀ v ∈ N, N.card / 2 + t ≤ edeg (A \ N.image (fun a => s(a, f₀ a))) v := by
      intro v hv
      have h1 := hdeg v hv
      have h2 : edeg (N.image (fun a => s(a, f₀ a))) v ≤ 1 := edeg_image_partner_le_one hinv0
      have h3 := edeg_le_edeg_sdiff_add_edeg A (N.image (fun a => s(a, f₀ a))) v
      omega
    obtain ⟨f₁, hmap1, hinv1, hne1, hadj1, hb1⟩ := ih _ hA'sub hdeg'
    have hsplit : ∑ y ∈ N, ∑ z ∈ nbhdIn (A \ N.image (fun a => s(a, f₀ a))) y N, w y z
        = (∑ y ∈ N, ∑ z ∈ nbhdIn A y N, w y z) - ∑ y ∈ N, w y (f₀ y) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [nbhdIn_sdiff_image_partner hinv0 hy,
        Finset.sum_erase_eq_sub (mem_nbhdIn.2 ⟨hmap0 y hy, hadj0 y hy⟩)]
    rw [hsplit] at hb1
    have htpos : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
    by_cases hcmp : ∑ y ∈ N, w y (f₀ y) ≤ ∑ y ∈ N, w y (f₁ y)
    · refine ⟨f₀, hmap0, hinv0, hne0, hadj0, ?_⟩
      have h5 := mul_le_mul_of_nonneg_left hcmp htpos
      push_cast
      linarith only [hb1, h5]
    · push Not at hcmp
      refine ⟨f₁, hmap1, hinv1, hne1, fun a ha => (Finset.mem_sdiff.1 (hadj1 a ha)).1, ?_⟩
      push_cast
      linarith only [hb1, hcmp]

/-- **Spread perfect matchings from Dirac slack.**  If `δ(A) ≥ |N|/2 + t` on an even set `N`, then
for every nonnegative weight `w` some perfect matching of `N` inside `A`, presented as a partner
involution `f`, satisfies `∑_{y ∈ N} w(y, f y) ≤ (1/(t+1)) ∑_{y,z ∈ N} w(y,z)`.

This replaces the probabilistic step of BKLO (Proposition 10.8): the `t+1` matchings averaged over
are pairwise edge-disjoint, obtained by applying Dirac's theorem `t+1` times in a row. -/
theorem exists_spread_involution {N : Finset V} {A : Finset (Sym2 V)} {t : ℕ}
    (hAsub : A ⊆ cliqueEdges N) (hEven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 + t ≤ edeg A v) (w : V → V → ℝ) (hw : ∀ y z, 0 ≤ w y z) :
    ∃ f : V → V, (∀ a ∈ N, f a ∈ N) ∧ (∀ a ∈ N, f (f a) = a) ∧ (∀ a ∈ N, f a ≠ a) ∧
      (∀ a ∈ N, s(a, f a) ∈ A) ∧
      ∑ y ∈ N, w y (f y) ≤ (1 / ((t : ℝ) + 1)) * ∑ y ∈ N, ∑ z ∈ N, w y z := by
  obtain ⟨f, h1, h2, h3, h4, h5⟩ := exists_spread_involution_aux hEven w hw t A hAsub hdeg
  refine ⟨f, h1, h2, h3, h4, ?_⟩
  have hmono : ∑ y ∈ N, ∑ z ∈ nbhdIn A y N, w y z ≤ ∑ y ∈ N, ∑ z ∈ N, w y z :=
    Finset.sum_le_sum fun y _ =>
      Finset.sum_le_sum_of_subset_of_nonneg (nbhdIn_subset A y N) (fun z _ _ => hw y z)
  have hkey : ((t : ℝ) + 1) * ∑ y ∈ N, w y (f y) ≤ ∑ y ∈ N, ∑ z ∈ N, w y z := h5.trans hmono
  have hpos : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hrw : (1 / ((t : ℝ) + 1)) * ∑ y ∈ N, ∑ z ∈ N, w y z
      = (∑ y ∈ N, ∑ z ∈ N, w y z) / ((t : ℝ) + 1) := by ring
  rw [hrw, le_div_iff₀ hpos]
  linarith only [hkey]

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
