/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.LLL.Obstruction
public import LeanPool.BlockSpectralSensitivity.Numerics.LLLBounds

/-!
# The local lemma produces a good gate labelling

This file proves the existence of a gate labelling satisfying the local certificate-list
conditions, and corresponds to Section 10 of `bs_lambda.txt`.

There are two families of bad events (Section 10):

* **type 1** — one active radius-one flag on a five-element support, of probability
  `p₁ = 144⁻⁶`;
* **type 2** — one consolidated radius-two internal obstruction on a nine-element
  support, of probability at most `p₂ = radiusTwoConst · 144⁻²⁰`.

Two events are declared adjacent when their vertex supports meet in at least two
vertices.  This is a legitimate dependency graph: by `disjoint_offDiag_of_card_inter_le_one`,
supports meeting in at most one vertex use disjoint sets of gate variables.

The dependency counts of Section 10.1 are `D11, D12, D21, D22` from
`BSLambda/Numerics/LLLBounds.lean`, where the two local-lemma inequalities
`lll_cond_one` and `lll_cond_two` have already been verified in exact rational
arithmetic.  Feeding all of this into `pr_avoid_pos_two_type` gives a configuration
avoiding every bad event, and Section 10.3 turns that into the conditions (L1) and (L2).

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

public section

namespace BSLambda

namespace LLL

open Numerics Construction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}

/-! ### The index type of bad events -/

/-- **The bad events** (Section 10): an *active* radius-one flag, or a nine-element
support carrying the consolidated radius-two obstruction.  Inactive flags and supports of
the wrong size are excluded, because the dependency counts of Section 10.1 count only the
active patterns. -/
@[expose]
def BadIdx (Arc : ι → ι → Bool) : Type _ :=
  {F : Flag1 ι // F.Active Arc} ⊕ {S : Finset ι // S.card = 9}

noncomputable instance : Fintype (BadIdx Arc) := by
  classical
  unfold BadIdx
  infer_instance

instance : DecidableEq (BadIdx Arc) := by
  classical
  unfold BadIdx
  infer_instance

/-- The vertex support of a bad event: five vertices for type 1, nine for type 2. -/
def badVerts : BadIdx Arc → Finset ι :=
  Sum.elim (fun F => F.1.supp) (fun S => S.1)

/-- The variable support of a bad event: the arc variables internal to its vertices, that
is, the off-diagonal pairs of `badVerts i`. -/
def badSupp (i : BadIdx Arc) : Finset (ι × ι) := (badVerts i).offDiag

/-- The type of a bad event: `false` for radius one, `true` for radius two. -/
def badTy : BadIdx Arc → Bool := Sum.elim (fun _ => false) (fun _ => true)

omit [Fintype ι] in
/-- A bad event of type `false` is an active radius-one flag. -/
theorem exists_inl_of_badTy_eq_false {j : BadIdx Arc} (hj : badTy j = false) :
    ∃ F : {F : Flag1 ι // F.Active Arc}, j = Sum.inl F := by
  cases j with
  | inl F => exact ⟨F, rfl⟩
  | inr S => exact absurd hj (by simp [badTy])

omit [Fintype ι] in
/-- A bad event of type `true` is a nine-element vertex support. -/
theorem exists_inr_of_badTy_eq_true {j : BadIdx Arc} (hj : badTy j = true) :
    ∃ S : {S : Finset ι // S.card = 9}, j = Sum.inr S := by
  cases j with
  | inl F => exact absurd hj (by simp [badTy])
  | inr S => exact ⟨S, rfl⟩

/-- The bad event itself, as a set of gate configurations. -/
noncomputable def badEvent (Arc : ι → ι → Bool) : BadIdx Arc → Finset (GateCfg ι r) :=
  Sum.elim (fun F => flagEvent Arc F.1) (fun S => radiusTwoEvent Arc S.1)

/-- The probability bound for each type (Sections 8.1 and 9). -/
noncomputable def badP : Bool → ℝ
  | false => p1
  | true => p2

/-- The local-lemma weights of Section 10.2. -/
noncomputable def badX : Bool → ℝ
  | false => x1
  | true => x2

/-- The dependency counts of Section 10.1. -/
def badD : Bool → Bool → ℕ
  | false, false => D11
  | false, true => D12
  | true, false => D21
  | true, true => D22

/-! ### The hypotheses of the local lemma -/

/-- Each bad event depends only on the arc variables internal to its own support
(Section 10). -/
theorem badEvent_determined (hT : IsTournament Arc) (i : BadIdx Arc) :
    Determined (β := fun _ : ι × ι => Fin r) (badSupp i) (badEvent (r := r) Arc i) := by
  cases i with
  | inl F => exact flagEvent_determined hT F.2
  | inr S => exact radiusTwoEvent_determined hT S.1

/-- Each bad event of type `t` has probability at most `badP t` (Sections 8.1 and 9). -/
theorem pr_badEvent_le [NeZero r] (hT : IsTournament Arc) (hr : r = 144) (i : BadIdx Arc) :
    pr (β := fun _ : ι × ι => Fin r) (badEvent Arc i) ≤ badP (badTy i) := by
  subst hr
  have : NeZero (144 : ℕ) := ⟨by norm_num⟩
  cases i with
  | inl F => simpa [badEvent, badTy, badP, p1] using pr_flagEvent_le (r := 144) hT F.2
  | inr S =>
    simpa [badEvent, badTy, badP, p2, radiusTwoConst] using
      pr_radiusTwoEvent_le (r := 144) hT S.2

/-- Two adjacent bad events have vertex supports meeting in at least two vertices: sharing a
gate variable forces sharing two vertices (Section 10). -/
theorem two_le_card_inter_of_mem_nbr {i j : BadIdx Arc}
    (h : j ∈ nbr (badSupp (Arc := Arc)) i) :
    2 ≤ (badVerts i ∩ badVerts j).card :=
  Nat.lt_of_not_le fun hle ↦ (mem_nbr.mp h).2 (disjoint_offDiag_of_card_inter_le_one hle)

/-! ### Counting helpers for the dependency bounds (Section 10.1) -/

omit [Fintype ι] in
/-- Two vertices shared between `V` and `W` yield a two-element subset of `V` contained in
`W`.  This is what turns `two_le_card_inter_of_mem_nbr` into "the neighbour's support
contains one of the `C(|V|,2)` pairs of `V`" (Section 10.1). -/
theorem exists_pair_subset_of_two_le_card_inter {V W : Finset ι}
    (h : 2 ≤ (V ∩ W).card) : ∃ p ∈ V.powersetCard 2, p ⊆ W := by
  obtain ⟨p, hp⟩ := Finset.powersetCard_nonempty.mpr h
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hp
  exact ⟨p, Finset.mem_powersetCard.mpr ⟨hsub.trans Finset.inter_subset_left, hcard⟩,
    hsub.trans Finset.inter_subset_right⟩

/-- The `m`-element subsets of `ι` meeting a fixed `V` in exactly `s` vertices are counted by
choosing the `s` shared vertices inside `V` and the other `m - s` outside `V` (Section 10.1);
this is the `Finset`-level refinement of Vandermonde's identity. -/
theorem card_filter_card_inter_eq (V : Finset ι) {s m : ℕ} (hsm : s ≤ m) :
    (Finset.univ.filter fun S : Finset ι => S.card = m ∧ (V ∩ S).card = s).card
      = V.card.choose s * (Fintype.card ι - V.card).choose (m - s) := by
  classical
  -- a pair `(A, B)` with `A ⊆ V` and `B ⊆ Vᶜ` is disjoint and recovered from its union
  have hsplit : ∀ A B : Finset ι, A ⊆ V → B ⊆ Vᶜ →
      Disjoint A B ∧ V ∩ (A ∪ B) = A ∧ (A ∪ B) \ V = B := by
    intro A B h1 h2
    have h2' : ∀ x ∈ B, x ∉ V := fun x hx ↦ Finset.mem_compl.mp (h2 hx)
    refine ⟨Finset.disjoint_left.mpr fun x hx1 hx2 ↦ h2' x hx2 (h1 hx1), ?_, ?_⟩
    · ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      exact ⟨fun hx ↦ hx.2.resolve_right fun hc ↦ h2' x hc hx.1, fun hx ↦ ⟨h1 hx, Or.inl hx⟩⟩
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      exact ⟨fun hx ↦ hx.1.resolve_left fun hc ↦ hx.2 (h1 hc), fun hx ↦ ⟨Or.inr hx, h2' x hx⟩⟩
  have key : (Finset.univ.filter fun S : Finset ι ↦ S.card = m ∧ (V ∩ S).card = s).card
      = (V.powersetCard s ×ˢ Vᶜ.powersetCard (m - s)).card := by
    refine Finset.card_nbij' (fun S ↦ (V ∩ S, S \ V)) (fun q ↦ q.1 ∪ q.2) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.coe_filter_univ, Set.mem_ofPred_eq] at hS
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard]
      have h1 : (S ∩ V).card + (S \ V).card = S.card := Finset.card_inter_add_card_sdiff S V
      rw [Finset.inter_comm] at h1
      exact ⟨⟨Finset.inter_subset_left, hS.2⟩,
        fun x hx ↦ Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2, by omega⟩
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hq
      obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hq
      obtain ⟨hdisj, hinter, -⟩ := hsplit q.1 q.2 ha1 hb1
      simp only [Finset.coe_filter_univ, Set.mem_ofPred_eq]
      refine ⟨?_, by rw [hinter, ha2]⟩
      rw [Finset.card_union_of_disjoint hdisj, ha2, hb2]
      omega
    · intro S _
      ext x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hq
      obtain ⟨-, hinter, hsdiff⟩ := hsplit q.1 q.2 hq.1.1 hq.2.1
      exact Prod.ext hinter hsdiff
  rw [key, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_compl]

open scoped Classical in
/-- Summing `card_filter_card_inter_eq` over the possible intersection sizes bounds the number
of `m`-element subsets meeting `V` in at least two vertices (Section 10.1). -/
theorem card_filter_two_le_card_inter_le (V : Finset ι) {m : ℕ} (hvm : V.card ≤ m) :
    (Finset.univ.filter fun S : Finset ι => S.card = m ∧ 2 ≤ (V ∩ S).card).card
      ≤ ∑ s ∈ Finset.Icc 2 V.card,
          V.card.choose s * (Fintype.card ι - V.card).choose (m - s) := by
  have hdisj : ∀ s ∈ Finset.Icc 2 V.card, ∀ t ∈ Finset.Icc 2 V.card, s ≠ t →
      Disjoint (Finset.univ.filter fun S : Finset ι ↦ S.card = m ∧ (V ∩ S).card = s)
        (Finset.univ.filter fun S : Finset ι ↦ S.card = m ∧ (V ∩ S).card = t) := by
    intro s _ t _ hne
    exact Finset.disjoint_filter.mpr fun S _ hs ht ↦ hne (hs.2.symm.trans ht.2)
  -- split the left-hand side according to the size of the intersection
  have heq : (Finset.univ.filter fun S : Finset ι ↦ S.card = m ∧ 2 ≤ (V ∩ S).card) =
      (Finset.Icc 2 V.card).biUnion fun s ↦
        Finset.univ.filter fun S : Finset ι ↦ S.card = m ∧ (V ∩ S).card = s := by
    ext S
    simp only [Finset.mem_filter_univ, Finset.mem_biUnion]
    constructor
    · rintro ⟨hcard, hge⟩
      exact ⟨(V ∩ S).card,
        Finset.mem_Icc.mpr ⟨hge, Finset.card_le_card Finset.inter_subset_left⟩, hcard, rfl⟩
    · rintro ⟨s, hs, hcard, hseq⟩
      exact ⟨hcard, hseq ▸ (Finset.mem_Icc.mp hs).1⟩
  rw [heq, Finset.card_biUnion fun s hs t ht hne ↦ hdisj s hs t ht hne]
  apply Finset.sum_le_sum
  intro s hs
  rw [card_filter_card_inter_eq]
  exact le_trans (Finset.mem_Icc.mp hs).2 hvm

/-! ### From dependency neighbourhoods to vertex supports (Section 10.1) -/

/-- The vertex support of a type-two neighbour of a bad event is a nine-element set meeting
the event's own vertex set in at least two vertices (Section 10.1). -/
theorem badVerts_mem_filter_of_mem_nbr {i j : BadIdx Arc}
    (hj : j ∈ (nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = true) :
    badVerts j ∈ Finset.univ.filter fun S : Finset ι =>
      S.card = 9 ∧ 2 ≤ (badVerts i ∩ S).card := by
  obtain ⟨S, rfl⟩ := exists_inr_of_badTy_eq_true (Finset.mem_filter.mp hj).2
  exact (Finset.mem_filter_univ _).mpr
    ⟨S.2, two_le_card_inter_of_mem_nbr (Finset.mem_filter.mp hj).1⟩

/-- A type-two bad event is determined by its vertex support, so the type-two neighbours of a
bad event are counted by their supports (Section 10.1). -/
theorem badVerts_injOn_type_two (i : BadIdx Arc) :
    Set.InjOn badVerts
      (((nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = true) : Set (BadIdx Arc)) := by
  intro j hj k hk hjk
  rw [Finset.mem_coe] at hj hk
  obtain ⟨S, rfl⟩ := exists_inr_of_badTy_eq_true (Finset.mem_filter.mp hj).2
  obtain ⟨T, rfl⟩ := exists_inr_of_badTy_eq_true (Finset.mem_filter.mp hk).2
  exact congrArg Sum.inr (Subtype.ext hjk)

/-- The type-two neighbours of a bad event are counted by the nine-element supports meeting
its vertex set in at least two vertices (Section 10.1). -/
theorem card_nbr_type_two_le (i : BadIdx Arc) :
    ((nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = true).card
      ≤ (Finset.univ.filter fun S : Finset ι =>
          S.card = 9 ∧ 2 ≤ (badVerts i ∩ S).card).card :=
  Finset.card_le_card_of_injOn badVerts (fun _ hj ↦ badVerts_mem_filter_of_mem_nbr hj)
    (badVerts_injOn_type_two i)

/-- Sharpened form of `card_nbr_type_two_le` for a type-two event: its own support is not one
of its neighbours, which is the `- 1` in `D22`. -/
theorem card_nbr_type_two_two_le (S : {S : Finset ι // S.card = 9}) :
    ((nbr (badSupp (Arc := Arc)) (Sum.inr S)).filter fun j => badTy j = true).card
      ≤ (Finset.univ.filter fun T : Finset ι =>
          T.card = 9 ∧ 2 ≤ (S.1 ∩ T).card).card - 1 := by
  set N := (nbr (badSupp (Arc := Arc)) (Sum.inr S)).filter fun j ↦ badTy j = true
  -- the support of `S` itself lies in the target but not in the image of the neighbours
  have hSmem : S.1 ∈ Finset.univ.filter fun T : Finset ι ↦ T.card = 9 ∧ 2 ≤ (S.1 ∩ T).card :=
    (Finset.mem_filter_univ _).mpr ⟨S.2, by simp [Finset.inter_self, S.2]⟩
  have hSnot : S.1 ∉ N.image badVerts := by
    rw [Finset.mem_image]
    rintro ⟨j, hj, hjeq⟩
    obtain ⟨T, rfl⟩ := exists_inr_of_badTy_eq_true (Finset.mem_filter.mp hj).2
    exact (mem_nbr.mp (Finset.mem_filter.mp hj).1).1 (congrArg Sum.inr (Subtype.ext hjeq))
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.image_subset_iff.mpr fun _ hj ↦ badVerts_mem_filter_of_mem_nbr hj,
      fun h ↦ hSnot (h ▸ hSmem)⟩)
  change (N.image badVerts).card < _ at hlt
  rw [Finset.card_image_of_injOn (badVerts_injOn_type_two (Arc := Arc) (Sum.inr S))] at hlt
  exact Nat.le_sub_one_of_lt hlt

open scoped Classical in
/-- Every type-one neighbour of a bad event is an active flag whose support contains one of
the `C(|V|,2)` pairs of the event's vertex set `V` (Section 10.1). -/
theorem card_nbr_type_one_le (i : BadIdx Arc) :
    ((nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = false).card
      ≤ ∑ p ∈ (badVerts i).powersetCard 2,
          (Finset.univ.filter fun G : Flag1 ι => G.Active Arc ∧ p ⊆ G.supp).card := by
  classical
  set T := (nbr (badSupp (Arc := Arc)) i).filter (fun j ↦ badTy j = false)
  rcases Finset.eq_empty_or_nonempty T with hT | ⟨j0, hj0⟩
  · simp [hT]
  obtain ⟨F0, rfl⟩ := exists_inl_of_badTy_eq_false (Finset.mem_filter.mp hj0).2
  -- the flag `F0` is the fallback value that makes the map to flags total
  set f : BadIdx Arc → Flag1 ι := Sum.elim (fun F ↦ F.1) (fun _ ↦ F0.1)
  set B : Finset (Flag1 ι) :=
    ((badVerts i).powersetCard 2).biUnion
      (fun p ↦ Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ p ⊆ G.supp)
  have hmaps : ∀ j ∈ T, f j ∈ B := by
    intro j hj
    obtain ⟨p, hp, hpsub⟩ := exists_pair_subset_of_two_le_card_inter
      (two_le_card_inter_of_mem_nbr (Finset.mem_filter.mp hj).1)
    obtain ⟨F, rfl⟩ := exists_inl_of_badTy_eq_false (Finset.mem_filter.mp hj).2
    exact Finset.mem_biUnion.mpr ⟨p, hp, (Finset.mem_filter_univ _).mpr ⟨F.2, hpsub⟩⟩
  have hinj : Set.InjOn f (T : Set (BadIdx Arc)) := by
    intro j1 hj1 j2 hj2 hfe
    rw [Finset.mem_coe] at hj1 hj2
    obtain ⟨F1, rfl⟩ := exists_inl_of_badTy_eq_false (Finset.mem_filter.mp hj1).2
    obtain ⟨F2, rfl⟩ := exists_inl_of_badTy_eq_false (Finset.mem_filter.mp hj2).2
    exact congrArg Sum.inl (Subtype.ext hfe)
  exact (Finset.card_le_card_of_injOn f hmaps hinj).trans Finset.card_biUnion_le

/-! ### Active radius-one flags through a fixed pair (Section 8.2) -/

/-- **The common out-neighbourhood of a flag head** (Section 8.2): the vertices dominated by
the owner `q.1` and, when it is present, by the top vertex `q.2`.  The bottom set of an active
flag is a subset of this (`Flag1.Active.bot_subset_headOut`), and its size is `d = 7005` for a
Type-A head and `t = 3502` for a Type-B head. -/
@[expose]
def headOut (Arc : ι → ι → Bool) (q : ι × Option ι) : Finset ι :=
  q.2.elim (outNbrs Arc q.1) (commonOut Arc q.1)

/-- The common out-neighbourhood of a Type-A head is the out-neighbourhood of the owner. -/
@[simp] theorem headOut_none (o : ι) : headOut Arc (o, none) = outNbrs Arc o := rfl

/-- The common out-neighbourhood of a Type-B head is the set of common out-neighbours of the
owner and the top vertex. -/
@[simp] theorem headOut_some (o a : ι) : headOut Arc (o, some a) = commonOut Arc o a := rfl

/-- The bottom set of an active flag lies in the common out-neighbourhood of its head. -/
theorem Flag1.Active.bot_subset_headOut {G : Flag1 ι} (hG : G.Active Arc) :
    G.bot ⊆ headOut Arc (G.owner, G.top) := fun j hj ↦ by
  cases ha : G.top with
  | none => simpa [ha] using hG.arc_owner_bot hj
  | some a => simpa [ha] using ⟨hG.arc_owner_bot hj, hG.arc_top_bot ha hj⟩

/-- **The counting scheme behind all six flag counts of Section 8.2.**  An active flag is
determined by its head `(owner, top)` together with its bottom set, and the bottom set is a
`c`-element subset of the common out-neighbourhood of the head containing the forced vertices
`W`.  So if every flag satisfying `P` has its head in `H` and at most `N` unforced candidates
for the remaining `c - |W|` bottom vertices, there are at most `|H| * C(N, c - |W|)` of them. -/
theorem card_flags_le_mul_choose {P : Flag1 ι → Prop} [DecidablePred P]
    {H : Finset (ι × Option ι)} {W : Finset ι} {c N : ℕ}
    (hact : ∀ G, P G → G.Active Arc) (hhead : ∀ G, P G → (G.owner, G.top) ∈ H)
    (hW : ∀ G, P G → W ⊆ G.bot) (hbot : ∀ G, P G → G.bot.card = c)
    (hN : ∀ G, P G → (headOut Arc (G.owner, G.top) \ W).card ≤ N) :
    (Finset.univ.filter P).card ≤ H.card * Nat.choose N (c - W.card) := by
  refine (Finset.card_le_card_of_injOn
      (fun G ↦ (⟨(G.owner, G.top), G.bot \ W⟩ : (_ : ι × Option ι) × Finset ι))
      (t := ((Finset.univ.filter P).image fun G ↦ (G.owner, G.top)).sigma
        fun q ↦ (headOut Arc q \ W).powersetCard (c - W.card)) ?_ ?_).trans ?_
  · intro G hG
    rw [Finset.mem_coe] at hG
    have hP : P G := (Finset.mem_filter.mp hG).2
    rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard]
    refine ⟨Finset.mem_image_of_mem _ hG,
      Finset.sdiff_subset_sdiff (hact G hP).bot_subset_headOut (Finset.Subset.refl W), ?_⟩
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (hW G hP), hbot G hP]
  · intro G₁ h₁ G₂ h₂ heq
    rw [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    have hq := congrArg Sigma.fst heq
    have hb : G₁.bot \ W = G₂.bot \ W := congrArg Sigma.snd heq
    refine Flag1.ext (congrArg Prod.fst hq) (congrArg Prod.snd hq) ?_
    rw [← Finset.sdiff_union_of_subset (hW G₁ h₁.2), hb,
      Finset.sdiff_union_of_subset (hW G₂ h₂.2)]
  · have hb : ∀ q ∈ (Finset.univ.filter P).image (fun G ↦ (G.owner, G.top)),
        ((headOut Arc q \ W).powersetCard (c - W.card)).card ≤ Nat.choose N (c - W.card) := by
      intro q hq
      obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hq
      rw [Finset.card_powersetCard]
      exact Nat.choose_le_choose _ (hN G (Finset.mem_filter.mp hG).2)
    have hsum := Finset.sum_le_card_nsmul _ _ _ hb
    have himg : ((Finset.univ.filter P).image fun G ↦ (G.owner, G.top)).card ≤ H.card :=
      Finset.card_le_card (Finset.image_subset_iff.mpr fun G hG ↦
        hhead G (Finset.mem_filter.mp hG).2)
    rw [Finset.card_sigma]
    exact le_trans (by simpa using hsum) (Nat.mul_le_mul_right _ himg)

open scoped Classical in
/-- **Section 8.2**, Type A, the fixed pair being owner and bottom vertex: at most
`C(d-1,3)` such flags, specializing to `C(7004,3)` in the construction. -/
theorem card_typeA_owner_bot {d t : ℕ} (hT : IsDRTournamentWith Arc d t) {u v : ι} :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top = none ∧ G.owner = u ∧ v ∈ G.bot).card ≤ Nat.choose (d - 1) 3 := by
  refine le_trans (card_flags_le_mul_choose (Arc := Arc) (H := {(u, none)}) (W := {v})
      (c := 4) (N := d - 1) ?_ ?_ ?_ ?_ ?_) ?_
  · exact fun G hG ↦ hG.1
  · rintro G ⟨-, ha, hh, -⟩
    simp [ha, hh]
  · exact fun G hG ↦ Finset.singleton_subset_iff.mpr hG.2.2.2
  · exact fun G hG ↦ hG.1.card_bot_of_top_eq_none hG.2.1
  · rintro G ⟨hAct, ha, hh, hv⟩
    rw [← Finset.erase_eq, Finset.card_erase_of_mem (hAct.bot_subset_headOut hv), ha,
      headOut_none, hh, hT.card_outNbrs]
  · simp only [Finset.card_singleton, Nat.reduceSub, one_mul, le_refl]

open scoped Classical in
/-- **Section 8.2**, Type A with an owner outside the fixed pair: at most
`t * C(d-2,2)` such flags, with `d = 7005`, `t = 3502` in the construction. -/
theorem card_typeA_bot_bot {d t : ℕ} (hT : IsDRTournamentWith Arc d t) {u v : ι} (huv : u ≠ v) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top = none ∧ u ∈ G.bot ∧ v ∈ G.bot).card
      ≤ t * Nat.choose (d - 2) 2 := by
  refine le_trans (card_flags_le_mul_choose (Arc := Arc)
      (H := commonIn Arc u v ×ˢ {none})
      (W := {u, v}) (c := 4) (N := d - 2) ?_ ?_ ?_ ?_ ?_) ?_
  · exact fun G hG ↦ hG.1
  · rintro G ⟨hAct, ha, hu, hv⟩
    simp only [Finset.mem_product, mem_commonIn, Finset.mem_singleton, ha]
    exact ⟨⟨hAct.arc_owner_bot hu, hAct.arc_owner_bot hv⟩, trivial⟩
  · rintro G ⟨-, -, hu, hv⟩
    simp [Finset.insert_subset_iff, hu, hv]
  · exact fun G hG ↦ hG.1.card_bot_of_top_eq_none hG.2.1
  · rintro G ⟨hAct, ha, hu, hv⟩
    have hsub : ({u, v} : Finset ι) ⊆ headOut Arc (G.owner, G.top) :=
      Finset.insert_subset (hAct.bot_subset_headOut hu)
        (Finset.singleton_subset_iff.mpr (hAct.bot_subset_headOut hv))
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_pair huv, ha,
      headOut_none, hT.card_outNbrs]
  · simp only [Finset.card_product, Finset.card_singleton, mul_one, hT.card_commonIn huv,
      Finset.card_pair huv, Nat.reduceSub, le_refl]

open scoped Classical in
/-- **Section 8.2**: at most `N_A = C(d-1,3) + t C(d-2,2) = 143,100,492,510` Type-A flags pass
through the ordered pair `u → v`.  The case `owner = v` is empty: it needs the reverse arc. -/
theorem card_typeA_through_pair (hT : IsDRTournamentWith Arc 7005 3502)
    {u v : ι} (huv : u ≠ v) (harc : Arc u v = true) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top = none ∧ u ∈ G.supp ∧ v ∈ G.supp).card
      ≤ 143100492510 := by
  have hrev : Arc v u ≠ true := hT.arc_asymm harc
  have hsub : (Finset.univ.filter fun G : Flag1 ι ↦
        G.Active Arc ∧ G.top = none ∧ u ∈ G.supp ∧ v ∈ G.supp) ⊆
      (Finset.univ.filter fun G : Flag1 ι ↦
        G.Active Arc ∧ G.top = none ∧ G.owner = u ∧ v ∈ G.bot) ∪
      (Finset.univ.filter fun G : Flag1 ι ↦
        G.Active Arc ∧ G.top = none ∧ u ∈ G.bot ∧ v ∈ G.bot) := by
    intro G hG
    obtain ⟨hAct, ha, hu, hv⟩ := (Finset.mem_filter_univ _).mp hG
    simp only [Flag1.mem_supp, Flag1.mem_nonOwners, ha, Option.not_mem_none, false_or]
      at hu hv
    simp only [Finset.mem_union, Finset.mem_filter_univ]
    rcases hu with rfl | hu
    · rcases hv with rfl | hv
      · exact absurd rfl huv
      · exact Or.inl ⟨hAct, ha, rfl, hv⟩
    · rcases hv with rfl | hv
      · exact absurd (hAct.arc_owner_bot hu) hrev
      · exact Or.inr ⟨hAct, ha, hu, hv⟩
  have howner := card_typeA_owner_bot hT (u := u) (v := v)
  have hbottom := card_typeA_bot_bot hT huv
  simp only [Nat.reduceSub] at howner hbottom
  exact (Finset.card_le_card hsub).trans (((Finset.card_union_le _ _).trans
    (add_le_add howner hbottom)).trans
    (le_of_eq typeAFlagSum_eq))

open scoped Classical in
/-- **Section 8.2**, Type B, the fixed pair being the ordered top pair `(a, h) = (u, v)`: at
most `C(t,3)` such flags, with `t = 3502` in the construction. -/
theorem card_typeB_top_owner {d t : ℕ} (hT : IsDRTournamentWith Arc d t) {u v : ι} (huv : u ≠ v) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top = some u ∧ G.owner = v).card ≤ Nat.choose t 3 := by
  refine le_trans (card_flags_le_mul_choose (Arc := Arc) (H := {(v, some u)}) (W := ∅)
      (c := 3) (N := t) ?_ ?_ ?_ ?_ ?_) ?_
  · exact fun G hG ↦ hG.1
  · rintro G ⟨-, ha, hh⟩
    simp [ha, hh]
  · exact fun _ _ ↦ Finset.empty_subset _
  · exact fun G hG ↦ hG.1.card_bot_of_top_eq_some hG.2.1
  · rintro G ⟨-, ha, hh⟩
    rw [Finset.sdiff_empty, ha, hh, headOut_some, hT.card_commonOut huv.symm]
  · simp only [Finset.card_singleton, Finset.card_empty, Nat.sub_zero, one_mul, le_refl]

open scoped Classical in
/-- **Section 8.2**, Type B with `u` the upper top vertex and `v` a bottom vertex: at most
`t * C(t-1,2)` such flags, with `t = 3502` in the construction. -/
theorem card_typeB_top_bot {d t : ℕ} (hT : IsDRTournamentWith Arc d t)
    {u v : ι} (harc : Arc u v = true) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top = some u ∧ v ∈ G.bot).card ≤ t * Nat.choose (t - 1) 2 := by
  refine le_trans (card_flags_le_mul_choose (Arc := Arc)
      (H := middles Arc u v ×ˢ {some u})
      (W := {v}) (c := 3) (N := t - 1) ?_ ?_ ?_ ?_ ?_) ?_
  · exact fun G hG ↦ hG.1
  · rintro G ⟨hAct, ha, hv⟩
    simp only [Finset.mem_product, mem_middles, Finset.mem_singleton, ha]
    exact ⟨⟨hAct.arc_top_owner ha, hAct.arc_owner_bot hv⟩, trivial⟩
  · exact fun G hG ↦ Finset.singleton_subset_iff.mpr hG.2.2
  · exact fun G hG ↦ hG.1.card_bot_of_top_eq_some hG.2.1
  · rintro G ⟨hAct, ha, hv⟩
    rw [← Finset.erase_eq, Finset.card_erase_of_mem (hAct.bot_subset_headOut hv), ha,
      headOut_some, hT.card_commonOut (hAct.owner_ne_top ha)]
  · have : Nontrivial ι := ⟨u, v, hT.ne_of_arc harc⟩
    have hmid : (middles Arc u v).card = t := hT.card_middles harc
    simp only [Finset.card_product, Finset.card_singleton, mul_one, hmid,
      Finset.card_singleton, Nat.reduceSub, le_refl]

open scoped Classical in
/-- **Section 8.2**, Type B with `u` the owner and `v` a bottom vertex: at most
`t * C(t-1,2)` such flags, with `t = 3502` in the construction. -/
theorem card_typeB_owner_bot {d t : ℕ} (hT : IsDRTournamentWith Arc d t)
    {u v : ι} (huv : u ≠ v) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top ≠ none ∧ G.owner = u ∧ v ∈ G.bot).card
      ≤ t * Nat.choose (t - 1) 2 := by
  refine le_trans (card_flags_le_mul_choose (Arc := Arc)
      (H := ({u} : Finset ι) ×ˢ (commonIn Arc u v).image some)
      (W := {v}) (c := 3) (N := t - 1) ?_ ?_ ?_ ?_ ?_) ?_
  · exact fun G hG ↦ hG.1
  · rintro G ⟨hAct, hane, hh, hv⟩
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hane
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_image, mem_commonIn, ha, hh]
    exact ⟨trivial, a, ⟨hh ▸ hAct.arc_top_owner ha, hAct.arc_top_bot ha hv⟩, rfl⟩
  · exact fun G hG ↦ Finset.singleton_subset_iff.mpr hG.2.2.2
  · rintro G ⟨hAct, hane, -, -⟩
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hane
    exact hAct.card_bot_of_top_eq_some ha
  · rintro G ⟨hAct, hane, -, hv⟩
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hane
    rw [← Finset.erase_eq, Finset.card_erase_of_mem (hAct.bot_subset_headOut hv), ha,
      headOut_some, hT.card_commonOut (hAct.owner_ne_top ha)]
  · simp only [Finset.card_product, Finset.card_singleton, one_mul,
      Finset.card_image_of_injective _ (Option.some_injective ι), hT.card_commonIn huv,
      Finset.card_singleton, Nat.reduceSub, le_refl]

open scoped Classical in
/-- **Section 8.2**, Type B with both fixed vertices at the bottom: the top pair is one of the
`C(t,2)` arcs between the common in-neighbours of `u` and `v`, and the third bottom vertex is
one of `t - 2`, giving at most `C(t,2) * (t-2)` such flags. -/
theorem card_typeB_bot_bot {d t : ℕ} (hT : IsDRTournamentWith Arc d t) {u v : ι} (huv : u ≠ v) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top ≠ none ∧ u ∈ G.bot ∧ v ∈ G.bot).card
      ≤ Nat.choose t 2 * (t - 2) := by
  have hinj : Function.Injective fun p : ι × ι ↦ (p.2, some p.1) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    exact Prod.ext h.2 h.1
  refine le_trans (card_flags_le_mul_choose (Arc := Arc)
      (H := (arcSet Arc (commonIn Arc u v)).image fun p ↦ (p.2, some p.1))
      (W := {u, v}) (c := 3) (N := t - 2) ?_ ?_ ?_ ?_ ?_) ?_
  · exact fun G hG ↦ hG.1
  · rintro G ⟨hAct, hane, hu, hv⟩
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hane
    refine Finset.mem_image.mpr ⟨(a, G.owner), mem_arcSet.2 ⟨⟨?_, ?_,
      (hAct.owner_ne_top ha).symm⟩, hAct.arc_top_owner ha⟩, by simp [ha]⟩
    · exact mem_commonIn.2 ⟨hAct.arc_top_bot ha hu, hAct.arc_top_bot ha hv⟩
    · exact mem_commonIn.2 ⟨hAct.arc_owner_bot hu, hAct.arc_owner_bot hv⟩
  · rintro G ⟨-, -, hu, hv⟩
    simp [Finset.insert_subset_iff, hu, hv]
  · rintro G ⟨hAct, hane, -, -⟩
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hane
    exact hAct.card_bot_of_top_eq_some ha
  · rintro G ⟨hAct, hane, hu, hv⟩
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hane
    have hsub : ({u, v} : Finset ι) ⊆ headOut Arc (G.owner, G.top) :=
      Finset.insert_subset (hAct.bot_subset_headOut hu)
        (Finset.singleton_subset_iff.mpr (hAct.bot_subset_headOut hv))
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_pair huv, ha,
      headOut_some, hT.card_commonOut (hAct.owner_ne_top ha)]
  · simp only [Finset.card_image_of_injective _ hinj, card_arcSet hT.toIsTournament,
      hT.card_commonIn huv, Finset.card_pair huv, Nat.choose_one_right,
      Nat.reduceSub, le_refl]

open scoped Classical in
/-- **Section 8.2**: at most `N_B = C(t,3) + 2 t C(t-1,2) + C(t,2)(t-2) = 71,519,595,000`
Type-B flags pass through the ordered pair `u → v`.  Of the nine possible pairs of roles for
`u` and `v`, two are impossible and three need the reverse arc `v → u`. -/
theorem card_typeB_through_pair (hT : IsDRTournamentWith Arc 7005 3502)
    {u v : ι} (huv : u ≠ v) (harc : Arc u v = true) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top ≠ none ∧ u ∈ G.supp ∧ v ∈ G.supp).card
      ≤ 71519595000 := by
  have hrev : Arc v u ≠ true := hT.arc_asymm harc
  have hsub : (Finset.univ.filter fun G : Flag1 ι ↦
        G.Active Arc ∧ G.top ≠ none ∧ u ∈ G.supp ∧ v ∈ G.supp) ⊆
      ((Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ G.top = some u ∧ G.owner = v) ∪
        (Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ G.top = some u ∧ v ∈ G.bot)) ∪
      ((Finset.univ.filter fun G : Flag1 ι ↦
          G.Active Arc ∧ G.top ≠ none ∧ G.owner = u ∧ v ∈ G.bot) ∪
        (Finset.univ.filter fun G : Flag1 ι ↦
          G.Active Arc ∧ G.top ≠ none ∧ u ∈ G.bot ∧ v ∈ G.bot)) := by
    intro G hG
    obtain ⟨hAct, hane, hu, hv⟩ := (Finset.mem_filter_univ _).mp hG
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hane
    simp only [Flag1.mem_supp, Flag1.mem_nonOwners, ha, Option.mem_some_iff] at hu hv
    simp only [Finset.mem_union, Finset.mem_filter_univ]
    rcases hu with rfl | rfl | hu
    · rcases hv with rfl | rfl | hv
      · exact absurd rfl huv
      · exact absurd (hAct.arc_top_owner ha) hrev
      · exact Or.inr (Or.inl ⟨hAct, hane, rfl, hv⟩)
    · rcases hv with rfl | rfl | hv
      · exact Or.inl (Or.inl ⟨hAct, ha, rfl⟩)
      · exact absurd rfl huv
      · exact Or.inl (Or.inr ⟨hAct, ha, hv⟩)
    · rcases hv with rfl | rfl | hv
      · exact absurd (hAct.arc_owner_bot hu) hrev
      · exact absurd (hAct.arc_top_bot ha hu) hrev
      · exact Or.inr (Or.inr ⟨hAct, hane, hu, hv⟩)
  have htop := card_typeB_top_owner hT huv
  have htopBottom := card_typeB_top_bot hT harc
  have hownerBottom := card_typeB_owner_bot hT huv
  have hbottom := card_typeB_bot_bot hT huv
  simp only [Nat.reduceSub] at htopBottom hownerBottom hbottom
  apply (Finset.card_le_card hsub).trans
  calc
    _ ≤ (Nat.choose 3502 3 + 3502 * Nat.choose 3501 2) +
        (3502 * Nat.choose 3501 2 + Nat.choose 3502 2 * 3500) := by
      apply (Finset.card_union_le _ _).trans
      apply add_le_add
      · apply (Finset.card_union_le _ _).trans
        exact add_le_add htop htopBottom
      · apply (Finset.card_union_le _ _).trans
        exact add_le_add hownerBottom hbottom
    _ ≤ 71519595000 := by
      norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

open scoped Classical in
/-- **Section 8.2**: at most `N_1 = N_A + N_B = 214,620,087,510` active flags pass through the
ordered pair `u → v`. -/
theorem card_active_flag_through_ordered_pair (hT : IsDRTournamentWith Arc 7005 3502)
    {u v : ι} (huv : u ≠ v) (harc : Arc u v = true) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ u ∈ G.supp ∧ v ∈ G.supp).card ≤ 214620087510 := by
  have hsplit : Finset.univ.filter (fun G : Flag1 ι ↦ G.Active Arc ∧ u ∈ G.supp ∧ v ∈ G.supp) =
    Finset.univ.filter (fun G : Flag1 ι ↦ G.Active Arc ∧ G.top = none ∧ u ∈ G.supp ∧ v ∈ G.supp) ∪
    Finset.univ.filter
      (fun G : Flag1 ι ↦ G.Active Arc ∧ G.top ≠ none ∧ u ∈ G.supp ∧ v ∈ G.supp) := by
    ext G
    by_cases h : G.top = none <;> simp [h]
  rw [hsplit]
  have hA := card_typeA_through_pair hT huv harc
  have hB := card_typeB_through_pair hT huv harc
  exact le_trans (Finset.card_union_le _ _) (add_le_add hA hB)

open scoped Classical in
/-- **Section 8.2**: at most `N_1` active flags pass through any two-element vertex set. -/
theorem card_active_flag_through_pair (hT : IsDRTournamentWith Arc 7005 3502)
    {p : Finset ι} (hp : p.card = 2) :
    (Finset.univ.filter fun G : Flag1 ι => G.Active Arc ∧ p ⊆ G.supp).card
      ≤ 214620087510 := by
  rcases Finset.card_eq_two.mp hp with ⟨u, v, huv, rfl⟩
  -- the pair is unordered, so only one of the two arcs between `u` and `v` is present
  have key : ∀ a b : ι, a ≠ b → Arc a b = true → ({a, b} : Finset ι) = {u, v} →
      (Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ ({u, v} : Finset ι) ⊆ G.supp).card
        ≤ 214620087510 := by
    intro a b hne harc hab
    have hord := card_active_flag_through_ordered_pair hT hne harc
    rw [← hab]
    convert hord using 2
    ext G
    simp [Finset.insert_subset_iff]
  rcases hT.arc_or_arc huv with harc | harc
  · exact key u v huv harc rfl
  · exact key v u huv.symm harc (Finset.pair_comm v u)

/-! ### The four reduced dependency counts -/

/-- A type-one event has at most `D11` type-one neighbours (Section 10.1). -/
theorem card_nbr_one_one_le_D11 (hT : IsDRTournamentWith Arc 7005 3502)
    (F : {F : Flag1 ι // F.Active Arc}) :
    ((nbr (badSupp (Arc := Arc)) (Sum.inl F)).filter fun j => badTy j = false).card
      ≤ D11 := by
  classical
  have h1 : ((nbr (badSupp (Arc := Arc)) (Sum.inl F)).filter fun j ↦ badTy j = false).card
      ≤ ∑ p ∈ (badVerts (Sum.inl F)).powersetCard 2,
          (Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ p ⊆ G.supp).card :=
    card_nbr_type_one_le _
  have hverts : badVerts (Sum.inl F) = F.1.supp := rfl
  rw [hverts] at h1
  have hle : (∑ p ∈ F.1.supp.powersetCard 2,
          (Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ p ⊆ G.supp).card)
      ≤ Finset.card (F.1.supp.powersetCard 2) * 214620087510 := by
    apply Finset.sum_le_card_nsmul
    intro p hp
    exact card_active_flag_through_pair hT (Finset.mem_powersetCard.mp hp).2
  refine (h1.trans hle).trans ?_
  rw [Finset.card_powersetCard, (Flag1.Active.card_supp F.2 : F.1.supp.card = 5), D11]
  decide

/-- A type-one event has at most `D12` type-two neighbours (Section 10.1). -/
theorem card_nbr_one_two_le_D12 (hk : Fintype.card ι = 14011)
    (F : {F : Flag1 ι // F.Active Arc}) :
    ((nbr (badSupp (Arc := Arc)) (Sum.inl F)).filter fun j => badTy j = true).card
      ≤ D12 := by
  have h1 : (badVerts (Sum.inl F)).card = 5 := Flag1.Active.card_supp F.2
  calc ((nbr (badSupp (Arc := Arc)) (Sum.inl F)).filter fun j ↦ badTy j = true).card
      ≤ (Finset.univ.filter fun S : Finset ι ↦
          S.card = 9 ∧ 2 ≤ (badVerts (Sum.inl F) ∩ S).card).card :=
        card_nbr_type_two_le (Sum.inl F)
    _ ≤ ∑ s ∈ Finset.Icc 2 (badVerts (Sum.inl F)).card,
          (badVerts (Sum.inl F)).card.choose s *
            (Fintype.card ι - (badVerts (Sum.inl F)).card).choose (9 - s) :=
        card_filter_two_le_card_inter_le _ (by omega)
    _ = D12 := by
        rw [h1, hk]
        norm_num
        exact D12_eq_sum.symm

/-- A type-two event has at most `D21` type-one neighbours (Section 10.1). -/
theorem card_nbr_two_one_le_D21 (hT : IsDRTournamentWith Arc 7005 3502)
    (S : {S : Finset ι // S.card = 9}) :
    ((nbr (badSupp (Arc := Arc)) (Sum.inr S)).filter fun j => badTy j = false).card
      ≤ D21 := by
  classical
  have hle : ((nbr (badSupp (Arc := Arc)) (Sum.inr S)).filter fun j ↦ badTy j = false).card
      ≤ ∑ p ∈ (badVerts (Sum.inr S)).powersetCard 2,
          (Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ p ⊆ G.supp).card :=
    card_nbr_type_one_le (i := Sum.inr S)
  have hcardS : (Finset.powersetCard 2 (S : Finset ι)).card = 36 := by
    rw [Finset.card_powersetCard, S.prop]
    decide
  have hsum : ∑ p ∈ (S : Finset ι).powersetCard 2,
      (Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ p ⊆ G.supp).card
      ≤ (Finset.powersetCard 2 (S : Finset ι)).card * 214620087510 := by
    apply Finset.sum_le_card_nsmul
    intro p hp
    exact card_active_flag_through_pair hT (Finset.mem_powersetCard.mp hp).2
  rw [hcardS] at hsum
  rw [D21_eq_thirtysix_mul]
  exact hle.trans hsum

/-- A type-two event has at most `D22` other type-two neighbours (Section 10.1). -/
theorem card_nbr_two_two_le_D22 (hk : Fintype.card ι = 14011)
    (S : {S : Finset ι // S.card = 9}) :
    ((nbr (badSupp (Arc := Arc)) (Sum.inr S)).filter fun j => badTy j = true).card
      ≤ D22 := by
  classical
  have h1 : ((nbr (badSupp (Arc := Arc)) (Sum.inr S)).filter fun j ↦ badTy j = true).card
      ≤ (Finset.univ.filter fun T : Finset ι ↦
          T.card = 9 ∧ 2 ≤ (S.1 ∩ T).card).card - 1 := card_nbr_type_two_two_le S
  have h2 : (Finset.univ.filter fun T : Finset ι ↦ T.card = 9 ∧ 2 ≤ (S.1 ∩ T).card).card
      ≤ ∑ s ∈ Finset.Icc 2 S.1.card,
          S.1.card.choose s * (Fintype.card ι - S.1.card).choose (9 - s) :=
    card_filter_two_le_card_inter_le S.1 (le_of_eq S.2)
  have h3 : (∑ s ∈ Finset.Icc 2 S.1.card,
      S.1.card.choose s * (Fintype.card ι - S.1.card).choose (9 - s)) - 1 = D22 := by
    rw [S.2, hk]
    norm_num
    exact D22_eq_sum.symm
  omega

/-- The dependency counts, packaged as required by `pr_avoid_pos_two_type`.  Double regularity
is what pins the number `N_1` of active flags through a pair (Section 8.2). -/
theorem card_nbr_le (hk : Fintype.card ι = 14011) (hT : IsDRTournamentWith Arc 7005 3502)
    (i : BadIdx Arc) (t : Bool) :
    ((nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = t).card
      ≤ badD (badTy i) t := by
  cases i with
  | inl F =>
    cases t with
    | false => exact card_nbr_one_one_le_D11 hT F
    | true => exact card_nbr_one_two_le_D12 hk F
  | inr S =>
    cases t with
    | false => exact card_nbr_two_one_le_D21 hT S
    | true => exact card_nbr_two_two_le_D22 hk S

/-- The two local-lemma inequalities of Section 10.2, in the shape required by
`pr_avoid_pos_two_type`. -/
theorem badP_le (t : Bool) :
    badP t ≤ badX t * (1 - badX false) ^ badD t false * (1 - badX true) ^ badD t true := by
  cases t with
  | false => exact lll_cond_one
  | true => exact lll_cond_two

/-- The weights are positive. -/
theorem badX_pos (t : Bool) : 0 < badX t := by
  cases t with
  | false => exact x1_pos
  | true => exact x2_pos

/-- The weights are less than one. -/
theorem badX_lt_one (t : Bool) : badX t < 1 := by
  cases t with
  | false => exact x1_lt_one
  | true => exact x2_lt_one

/-! ### The good configuration -/

/-- **Section 10.2**: some gate configuration avoids every bad event. -/
theorem exists_good_config [NeZero r] (hk : Fintype.card ι = 14011)
    (hT : IsDRTournamentWith Arc 7005 3502) (hr : r = 144) :
    ∃ ω : GateCfg ι r, ∀ i : BadIdx Arc, ω ∉ badEvent Arc i := by
  classical
  have hpos :=
    pr_avoid_pos_two_type (β := fun _ : ι × ι ↦ Fin r) (badEvent Arc)
      (badSupp (Arc := Arc)) (badEvent_determined hT.toIsTournament) badTy badP badX badD
      (pr_badEvent_le hT.toIsTournament hr)
      (card_nbr_le hk hT) badX_pos
      badX_lt_one badP_le
  obtain ⟨ω, hω⟩ := pr_pos_iff.mp hpos
  refine ⟨ω, ?_⟩
  simpa using (Finset.mem_filter.mp hω).2

/-! ### Consequences for certificate lists (Section 10.3) -/

/-- **Section 10.3**: a good configuration admits no radius-one internal obstruction on a
five-element support: `mem_flagEvent_of_intObstruction` would produce an active flag whose
event contains `ω`. -/
theorem not_intObstruction_five (hT : IsTournament Arc) {ω : GateCfg ι r}
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) {S : Finset ι} (hS : S.card = 5)
    {h : ι} (hh : h ∈ S) (hobs : IntObstruction Arc 1 S h (toGamma ω)) : False := by
  obtain ⟨F, hact, _, hmem⟩ := mem_flagEvent_of_intObstruction hT hS hh hobs
  exact hgood (Sum.inl ⟨F, hact⟩) hmem

/-- **Section 10.3**: a good configuration admits no radius-two internal obstruction on a
nine-element support, since such an obstruction puts `ω` into `radiusTwoEvent`. -/
theorem not_intObstruction_nine {ω : GateCfg ι r}
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) {S : Finset ι} (hS : S.card = 9)
    {h : ι} (hh : h ∈ S) (hobs : IntObstruction Arc 2 S h (toGamma ω)) : False := by
  have hev : ω ∈ radiusTwoEvent Arc S := mem_radiusTwoEvent.mpr ⟨h, hh, hobs⟩
  exact hgood (Sum.inr ⟨S, hS⟩) hev

/-- **Section 10.3**: a positive point of `C_h` cannot have four further certificates of a
five-element support at distance at most one. -/
theorem not_close_five (hT : IsTournament Arc) {ω : GateCfg ι r}
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) {S : Finset ι} (hS : S.card = 5)
    {h : ι} (hh : h ∈ S) {x : Input (Coord ι r)}
    (hx : (cert Arc (toGamma ω) h).Sat x)
    (hclose : ∀ i ∈ S, i ≠ h → (cert Arc (toGamma ω) i).dist x ≤ 1) : False :=
  not_intObstruction_five hT hgood hS hh (intObstruction_of_close hT hx hclose)

/-- **Section 10.3**: a positive point of `C_h` cannot have eight further certificates of a
nine-element support at distance at most two. -/
theorem not_close_nine (hT : IsTournament Arc) {ω : GateCfg ι r}
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) {S : Finset ι} (hS : S.card = 9)
    {h : ι} (hh : h ∈ S) {x : Input (Coord ι r)}
    (hx : (cert Arc (toGamma ω) h).Sat x)
    (hclose : ∀ i ∈ S, i ≠ h → (cert Arc (toGamma ω) i).dist x ≤ 2) : False :=
  not_intObstruction_nine hgood hS hh (intObstruction_of_close hT hx hclose)

/-- The counting step behind both (L1) and (L2): if adjoining `h` to any `m + 1` indices
satisfying `P` gives a support on which `P` is impossible, then at most `m` indices other
than `h` satisfy `P`. -/
theorem card_filter_le_of_no_support {P : ι → Prop} [DecidablePred P] {h : ι} {m : ℕ}
    (hno : ∀ S : Finset ι, S.card = m + 2 → h ∈ S → (∀ i ∈ S, i ≠ h → P i) → False) :
    (Finset.univ.filter fun j => j ≠ h ∧ P j).card ≤ m := by
  by_contra hcontra
  obtain ⟨U, hU, hUcard⟩ := Finset.exists_subset_card_eq (Nat.not_le.mp hcontra)
  have hh : h ∉ U := fun hmem ↦ ((Finset.mem_filter_univ _).mp (hU hmem)).1 rfl
  refine hno (insert h U) ?_ (Finset.mem_insert_self h U) fun i hi hih ↦
    ((Finset.mem_filter_univ _).mp (hU ((Finset.mem_insert.mp hi).resolve_left hih))).2
  rw [Finset.card_insert_of_notMem hh, hUcard]

/-- **(L1)** (Section 10.3): a positive point has at most three other certificates at
distance one. -/
theorem card_le_three_of_good (hT : IsTournament Arc) {ω : GateCfg ι r}
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) (h : ι)
    (x : Input (Coord ι r)) (hx : (cert Arc (toGamma ω) h).Sat x) :
    (Finset.univ.filter fun j =>
        j ≠ h ∧ (cert Arc (toGamma ω) j).dist x = 1).card ≤ 3 :=
  card_filter_le_of_no_support fun _ hS hh hclose ↦
    not_close_five hT hgood hS hh hx fun i hi hih ↦ (hclose i hi hih).le

/-- **(L2)** (Section 10.3): a positive point has at most seven other certificates at
distance at most two. -/
theorem card_le_seven_of_good (hT : IsTournament Arc) {ω : GateCfg ι r}
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) (h : ι)
    (x : Input (Coord ι r)) (hx : (cert Arc (toGamma ω) h).Sat x) :
    (Finset.univ.filter fun j =>
        j ≠ h ∧ (cert Arc (toGamma ω) j).dist x ≤ 2).card ≤ 7 :=
  card_filter_le_of_no_support fun _ hS hh hclose ↦ not_close_nine hT hgood hS hh hx hclose

/-- **Section 10**: a gate labelling satisfying the local certificate-list conditions
(L1) and (L2) exists. -/
theorem exists_gate_labelling [NeZero r] (hk : Fintype.card ι = 14011)
    (hT : IsDRTournamentWith Arc 7005 3502) (hr : r = 144) :
    ∃ γ : ι → ι → Fin r,
      (∀ h x, (cert Arc γ h).Sat x →
        (Finset.univ.filter fun j => j ≠ h ∧ (cert Arc γ j).dist x = 1).card ≤ 3) ∧
      (∀ h x, (cert Arc γ h).Sat x →
        (Finset.univ.filter fun j => j ≠ h ∧ (cert Arc γ j).dist x ≤ 2).card ≤ 7) := by
  obtain ⟨ω, hgood⟩ := exists_good_config hk hT hr
  exact ⟨toGamma ω, fun h x hx ↦ card_le_three_of_good hT.toIsTournament hgood h x hx,
    fun h x hx ↦ card_le_seven_of_good hT.toIsTournament hgood h x hx⟩

end LLL

end BSLambda
