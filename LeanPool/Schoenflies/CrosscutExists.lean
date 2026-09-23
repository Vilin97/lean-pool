/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.OuterChain

/-!
# Building the crosscut of the outer-chain descent

`Graph.CrosscutExists`, the combinatorial half of the descent step of `lem:outer-chain`,
discharged. Nothing here is geometric: the only fact about the plane that enters is
`Graph.IsPlaneChain.disjoint_block_far`, "`Γ j` meets the earlier chain only through
`Γ (j-1)`", and it is used exactly twice, to say that a vertex cannot lie on both
`Γ i ∪ ⋯ ∪ Γ (j-2)` and `Γ j`.

## The blueprint's argument, and how it is formalised here

The blueprint chooses points `a, b` in the relative interiors of an edge of `Γ j` and an edge
of the earlier chain, cuts the cycle `C` there, observes that each of the two arcs must meet
`Γ (j-1)`, and takes a minimum-length path of `Γ (j-1)` between two *maximal subpaths of
`C ∩ Γ (j-1)`* lying on different arcs.

Cutting a cycle at interior points of two of its edges is, combinatorially, the statement that
two distinct edges `g₁ ≠ g₂` of the cycle split the remaining edges into two arcs
(`Graph.IsCycleThrough.split_at_edges`): the closed walk reads

  `… ─g₁→ p ─W₁→ q ─g₂→ q' ─W₂→ p' ─g₁→ …`

and the two arcs are `W₁` and `W₂`, whose visited sets `S₁`, `S₂` are **disjoint** and
**cover** the vertices of the cycle. That pair of facts replaces the notion of a maximal
subpath entirely:

* "`a` and `b` lie on different maximal subpaths of `C ∩ Γ (j-1)`" becomes `a ∈ S₁`, `b ∈ S₂`;
* the property of maximal subpaths that the argument actually consumes — that no subpath of
  `C ∩ Γ (j-1)` joins two of them — becomes `Graph.exists_isCycleCrosscut`'s hypothesis
  `hpres`: *every edge of the cycle that `Γ (j-1)` also has keeps both of its ends on the same
  side*. That is immediate here, because the only cycle edges joining the two sides are `g₁`
  and `g₂`, and neither is an edge of `Γ (j-1)`.

With that, walking along cycle edges of `Γ (j-1)` cannot cross from `S₁` to `S₂`, and all four
minimality clauses of `Graph.IsCycleCrosscut` fall out of one minimisation: among all walks of
`Γ (j-1)` from `S₁` to `S₂`, take one of least length.

* it is a path, because any walk between its own two ends is a competitor
  (`Graph.IsWalk.isPath_of_minLength`);
* its internal vertices miss `C`, because a vertex of `C` on it lies in `S₁` or in `S₂`, and
  either way one of the two halves is a strictly shorter competitor;
* no edge of it is an edge of `C`: such an edge has both ends on `C`, hence both ends among
  `{a, b}` by the previous clause, hence joins `S₁` to `S₂` while lying in `Γ (j-1)`, which
  `hpres` forbids;
* each arc of `C` between `a` and `b` carries an edge outside `Γ (j-1)`, since otherwise the
  arc itself would be a walk of cycle edges of `Γ (j-1)` from `S₁` to `S₂`.

## Two general lemmas

`Graph.IsPath.split_at_edge` (cut a path at one of its edges, with the two freshness clauses
`Graph.IsCycleThrough.split_aux` asks for) and `Graph.IsCycleThrough.rotate` (present a cycle
through any one of its edges) are general facts about walks with nothing to do with this
development; they are the missing companions of `Graph.IsPath.split_meet` and
`Graph.IsCycleThrough.split_at` and belong in `Schoenflies/Graph/Walk.lean` and
`Schoenflies/FaceCyclesProof.lean` respectively.

## Blueprint

* `Graph.IsPath.split_at_edge`, `Graph.IsCycleThrough.rotate`,
  `Graph.IsCycleThrough.split_at_edges` — "choose points `a, b` in the relative interiors of
  these two edges. The two arcs of the cycle `C` from `a` to `b` are internally disjoint",
  read combinatorially (`lem:outer-chain`).
* `Graph.exists_isCycleCrosscut` — "since `Γ_{j-1}` is connected, there is a path in `Γ_{j-1}`
  from `P` to `C ∖ V(P)`. Choose such a path `R` of minimum length …", the whole minimality
  paragraph of `lem:outer-chain`, with the chain abstracted away into the two sides `S₁, S₂`.
* `Graph.IsPlaneChain.crosscutExists` — **`Graph.CrosscutExists`**, the combinatorial half of
  the descent step of `lem:outer-chain`.
-/

@[expose] public section

open Set Schoenflies
open scoped Graph

namespace Graph

/-! ## Cutting a path at an edge, and rotating a cycle -/

section General

variable {α β : Type*} {G : Graph α β}

/-- **A path cut at one of its edges.** The two extra clauses are exactly what
`Graph.IsCycleThrough.split_aux` asks for: the near half never returns to the far end of the
cut edge, and a vertex reached by both halves is the near end of it.

This is the edge-indexed companion of `Graph.IsPath.split_meet`, which cuts at a vertex. -/
theorem IsPath.split_at_edge {u v : α} {W : List β} {g : β} (h : G.IsPath u W v) (hg : g ∈ W) :
    ∃ (W₁ W₂ : List β) (c d : α), W = W₁ ++ g :: W₂ ∧ G.IsPath u W₁ c ∧ G.IsLink g c d ∧
      G.IsPath d W₂ v ∧ c ∉ G.walkVertices d W₂ ∧
      ∀ z ∈ G.walkVertices u W₁, z ∈ G.walkVertices c (g :: W₂) → z = c := by
  induction h with
  | nil => simp at hg
  | @cons u w v f W hl hW hfresh ih =>
    rcases List.mem_cons.1 hg with rfl | hg'
    · exact ⟨[], W, u, w, rfl, .nil hl.left_mem, hl, hW, hfresh, fun z hz _ => by simpa using hz⟩
    obtain ⟨W₁, W₂, c, d, hWeq, h₁, hlg, h₂, hcd, hmeet⟩ := ih hg'
    have hsub₁ : W₁ ⊆ W := by rw [hWeq]; exact List.subset_append_left _ _
    have hsub₂ : g :: W₂ ⊆ W := by rw [hWeq]; exact List.subset_append_right _ _
    refine ⟨f :: W₁, W₂, c, d, by rw [hWeq]; rfl,
      .cons hl h₁ fun hmem => hfresh (walkVertices_mono hsub₁ hmem), hlg, h₂, hcd,
      fun z hz hz' => ?_⟩
    rcases mem_walkVertices_cons hl hz with hzu | hz''
    · -- The source of the extended prefix is fresh, so it cannot be reached by the far half.
      exfalso
      subst hzu
      refine hfresh ?_
      rcases mem_walkVertices_iff.1 hz' with heq | hcov
      · rw [heq]; exact walkVertices_mono hsub₁ h₁.target_mem_walkVertices
      · exact mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov)
    · exact hmeet z hz'' hz'

/-- **A cycle presented through any one of its edges.** `Graph.IsCycleThrough` names one edge
and one path; this re-presents the same cycle with a different edge named, which is what an
argument that has to start walking at a *given* edge needs. -/
theorem IsCycleThrough.rotate {e g : β} {u v : α} {D : List β} (hc : G.IsCycleThrough e u v D)
    (hg : g ∈ e :: D) :
    ∃ (c d : α) (W : List β), G.IsCycleThrough g c d W ∧ (g :: W).Perm (e :: D) := by
  rcases List.mem_cons.1 hg with rfl | hgD
  · exact ⟨u, v, D, hc, List.Perm.refl _⟩
  obtain ⟨A, B, c, d, hD, hA, hlg, hB, hcd, hmeet⟩ := hc.isPath.split_at_edge hgD
  have hne : c ≠ d := fun hh => hcd (hh ▸ mem_walkVertices_self)
  have hY : G.IsPath c [g] d := IsPath.single hlg hne
  -- A vertex reached both by the cut edge and by the far half is the far end of the cut edge.
  have hM2 : ∀ z ∈ G.walkVertices c [g], z ∈ G.walkVertices d B → z = d := by
    intro z hz hz'
    rcases mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, hinc⟩
    · exact absurd hz' hcd
    obtain rfl : f = g := by simpa using hf
    rcases hinc.eq_or_eq_of_isLink hlg with rfl | rfl
    · exact absurd hz' hcd
    · rfl
  obtain ⟨hpath, hperm, -⟩ :=
    hc.split_aux (X := A) (Y := [g]) (Z := B) (by rw [hD]; rfl) hA hY hB hne hmeet hM2
  -- The rotated cycle does not reuse its own named edge.
  have hnodup : (A ++ g :: B).Nodup := hD ▸ hc.isPath.nodup
  obtain ⟨-, hnd, -⟩ := List.nodup_append.1 hnodup
  have hgB : g ∉ B := (List.nodup_cons.1 hnd).1
  have hgA : g ∉ A := fun hmem =>
    List.disjoint_of_nodup_append hnodup hmem List.mem_cons_self
  have hge : g ≠ e := fun hh => hc.notMem (hh ▸ hgD)
  refine ⟨d, c, B ++ e :: A, ⟨hlg.symm, hpath, ?_⟩, hperm⟩
  simp only [List.mem_append, List.mem_cons, not_or]
  exact ⟨hgB, hge, hgA⟩

/-- Both ends of an edge of a cycle are vertices of the cycle. -/
theorem IsCycleThrough.mem_walkVertices_of_inc {e f : β} {u v z : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) (hf : f ∈ e :: D) (hz : G.Inc f z) :
    z ∈ G.walkVertices u D := by
  rcases List.mem_cons.1 hf with rfl | hfD
  · rcases hz.eq_or_eq_of_isLink hc.isLink with rfl | rfl
    · exact mem_walkVertices_self
    · exact hc.isPath.target_mem_walkVertices
  · exact mem_walkVertices_of_mem_covered ⟨f, hfD, hz⟩

/-- **A cycle cut at two of its edges is two arcs.** This is the blueprint's "choose points
`a, b` in the relative interiors of these two edges; the two arcs of the cycle `C` from `a` to
`b` are internally disjoint", with the two interior points replaced by the two edges
themselves: the closed walk reads `… ─g₁→ p ─W₁→ q ─g₂→ q' ─W₂→ p' ─g₁→ …`, and the two arcs
`W₁, W₂` visit disjoint sets of vertices which together are all the vertices of the cycle. -/
theorem IsCycleThrough.split_at_edges {e g₁ g₂ : β} {u v : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) (hg₁ : g₁ ∈ e :: D) (hg₂ : g₂ ∈ e :: D) (hne : g₁ ≠ g₂) :
    ∃ (p p' q q' : α) (W₁ W₂ : List β),
      G.IsLink g₁ p' p ∧ G.IsPath p W₁ q ∧ G.IsLink g₂ q q' ∧ G.IsPath q' W₂ p' ∧
        (g₁ :: (W₁ ++ g₂ :: W₂)).Perm (e :: D) ∧
        Disjoint (G.walkVertices p W₁) (G.walkVertices q' W₂) ∧
        G.walkVertices u D = G.walkVertices p W₁ ∪ G.walkVertices q' W₂ := by
  obtain ⟨p, p', Wc, hrot, hrperm⟩ := hc.rotate hg₁
  have hg₂c : g₂ ∈ Wc := by
    rcases List.mem_cons.1 (hrperm.mem_iff.2 hg₂) with rfl | hmem
    · exact absurd rfl hne
    · exact hmem
  obtain ⟨W₁, W₂, q, q', hWc, hW₁, hlg₂, hW₂, hqfresh, hmeet⟩ := hrot.isPath.split_at_edge hg₂c
  have hperm : (g₁ :: (W₁ ++ g₂ :: W₂)).Perm (e :: D) := by rw [← hWc]; exact hrperm
  -- The far arc's vertices are among those the cut edge reaches, so a vertex of both arcs
  -- would be the near end of `g₂`, which the far arc misses.
  have hsub : G.walkVertices q' W₂ ⊆ G.walkVertices q (g₂ :: W₂) := by
    intro z hz
    rcases mem_walkVertices_iff.1 hz with rfl | hcov
    · exact mem_walkVertices_of_mem_covered ⟨g₂, List.mem_cons_self, hlg₂.inc_right⟩
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono (List.subset_cons_self _ _) hcov)
  have hdisj : Disjoint (G.walkVertices p W₁) (G.walkVertices q' W₂) := by
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    obtain rfl : z = q := hmeet z hz₁ (hsub hz₂)
    exact hqfresh hz₂
  -- Every vertex of the cycle lies on one of the two arcs, and conversely.
  have hmemC : ∀ (f : β) (z : α), f ∈ e :: D → G.Inc f z → z ∈ G.walkVertices u D :=
    fun _ _ hf hz => hc.mem_walkVertices_of_inc hf hz
  refine ⟨p, p', q, q', W₁, W₂, hrot.isLink.symm, hW₁, hlg₂, hW₂, hperm, hdisj,
    Set.Subset.antisymm (fun z hz => ?_) (Set.union_subset (fun z hz => ?_) fun z hz => ?_)⟩
  · -- A vertex of the cycle lies on an edge of it, hence on one of the two arcs.
    have hcov : z ∈ G.coveredVertices (e :: D) := by
      rcases mem_walkVertices_iff.1 hz with rfl | hcov
      · exact ⟨e, List.mem_cons_self, hc.isLink.inc_left⟩
      · exact coveredVertices_mono (List.subset_cons_self _ _) hcov
    obtain ⟨f, hf, hinc⟩ := hcov
    rcases List.mem_cons.1 (hperm.mem_iff.2 hf) with rfl | hf'
    · rcases hinc.eq_or_eq_of_isLink hrot.isLink with rfl | rfl
      · exact Or.inl mem_walkVertices_self
      · exact Or.inr hW₂.target_mem_walkVertices
    rcases List.mem_append.1 hf' with hf'' | hf''
    · exact Or.inl (mem_walkVertices_of_mem_covered ⟨f, hf'', hinc⟩)
    rcases List.mem_cons.1 hf'' with rfl | hf'''
    · rcases hinc.eq_or_eq_of_isLink hlg₂ with rfl | rfl
      · exact Or.inl hW₁.target_mem_walkVertices
      · exact Or.inr mem_walkVertices_self
    · exact Or.inr (mem_walkVertices_of_mem_covered ⟨f, hf''', hinc⟩)
  · rcases mem_walkVertices_iff.1 hz with heq | ⟨f, hf, hinc⟩
    · rw [heq]; exact hmemC g₁ p hg₁ hrot.isLink.inc_left
    · exact hmemC f z (hperm.mem_iff.1 (List.mem_cons_of_mem _ (List.mem_append_left _ hf))) hinc
  · rcases mem_walkVertices_iff.1 hz with heq | ⟨f, hf, hinc⟩
    · rw [heq]; exact hmemC g₂ q' hg₂ hlg₂.inc_right
    · exact hmemC f z (hperm.mem_iff.1
        (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hf)))) hinc

/-! ## The crosscut, from a two-sided cycle and a connected subgraph -/

/-- **The minimality paragraph of `lem:outer-chain`, with the chain abstracted away.**

The cycle `e :: D` of `H` has its vertices split into two disjoint sides `S₁, S₂` — in the
application, the two arcs cut off by an edge of `Γ j` and an edge of the earlier chain — in
such a way that no edge of the cycle lying in `F` joins the two sides (`hpres`). If `F` is
connected and has a vertex on each side, then a minimum-length path of `F` from one side to
the other is a crosscut of the cycle in the sense of `Graph.IsCycleCrosscut`.

`hpres` is what the blueprint's *maximal subpaths of `C ∩ Γ (j-1)`* are for: it is the only
property of them the argument uses, and here it is a one-line consequence of the two cut edges
being outside `F`. -/
theorem exists_isCycleCrosscut {H F : Graph α β} {e : β} {u v : α} {D : List β}
    (hcyc : H.IsCycleThrough e u v D) (hFH : F ≤ H) {S₁ S₂ : Set α}
    (hdisj : Disjoint S₁ S₂) (hcover : H.walkVertices u D = S₁ ∪ S₂)
    (hpres : ∀ f ∈ e :: D, f ∈ E(F) → ∀ z w, H.IsLink f z w → (z ∈ S₁ ↔ w ∈ S₁))
    (hconn : F.Connected) (ha : ∃ a ∈ S₁, a ∈ V(F)) (hb : ∃ b ∈ S₂, b ∈ V(F)) :
    ∃ (a b : α) (R D₁ D₂ : List β), IsCycleCrosscut H F e u v D a b R D₁ D₂ := by
  classical
  -- Walking along cycle edges that `F` also has never crosses from one side to the other.
  have hside : ∀ (a' b' : α) (T : List β), H.IsWalk a' T b' → (∀ f ∈ T, f ∈ E(F)) →
      (∀ f ∈ T, f ∈ e :: D) → a' ∈ S₁ → b' ∈ S₁ := by
    intro a' b' T hw
    induction hw with
    | nil => exact fun _ _ hm => hm
    | @cons z w b' f T hl hW ih =>
      intro hFe hCe hz
      exact ih (fun f' hf' => hFe f' (List.mem_cons_of_mem _ hf'))
        (fun f' hf' => hCe f' (List.mem_cons_of_mem _ hf'))
        ((hpres f (hCe f List.mem_cons_self) (hFe f List.mem_cons_self) z w hl).1 hz)
  -- **"Choose such a path `R` of minimum length."**
  obtain ⟨a₀, ha₀S, ha₀F⟩ := ha
  obtain ⟨b₀, hb₀S, hb₀F⟩ := hb
  have hex : ∃ k, ∃ (T : List β) (a b : α),
      T.length = k ∧ F.IsWalk a T b ∧ a ∈ S₁ ∧ b ∈ S₂ := by
    obtain ⟨T, hT⟩ := hconn.reaches ha₀F hb₀F
    exact ⟨T.length, T, a₀, b₀, rfl, hT, ha₀S, hb₀S⟩
  obtain ⟨T, a, b, hTlen, hTwalk, haS, hbS⟩ := Nat.find_spec hex
  have hmin : ∀ (T' : List β) (a' b' : α), F.IsWalk a' T' b' → a' ∈ S₁ → b' ∈ S₂ →
      T.length ≤ T'.length := by
    intro T' a' b' hw' h1 h2
    rw [hTlen]
    exact Nat.find_le ⟨T', a', b', rfl, hw', h1, h2⟩
  -- A shortest walk between its own two ends is a path.
  have hR : F.IsPath a T b := hTwalk.isPath_of_minLength fun W' hW' => hmin W' a b hW' haS hbS
  have hTedges : ∀ f ∈ T, f ∈ E(F) := fun f hf => hR.edge_mem hf
  have hab : a ≠ b := by
    rintro rfl
    exact Set.disjoint_left.1 hdisj haS hbS
  have haC : a ∈ H.walkVertices u D := by rw [hcover]; exact Or.inl haS
  have hbC : b ∈ H.walkVertices u D := by rw [hcover]; exact Or.inr hbS
  obtain ⟨D₁, D₂, harc₁, harc₂, hsplit, -⟩ := hcyc.split_at haC hbC hab
  -- **"Its internal vertices do not lie on `C`."**
  have hTvert : H.walkVertices a T = F.walkVertices a T := walkVertices_congr_of_le hFH hTedges
  have hinterior : ∀ y ∈ H.walkVertices a T, y ≠ a → y ≠ b → y ∉ H.walkVertices u D := by
    intro y hy hya hyb hyC
    rw [hTvert] at hy
    obtain ⟨T₁, T₂, hTcat, hT₁, hT₂, -⟩ := hR.split hy
    have hlen₁ : 1 ≤ T₁.length := by
      cases T₁ with
      | nil => exact absurd hT₁.isWalk.eq_of_nil.symm hya
      | cons _ _ => simp
    have hlen₂ : 1 ≤ T₂.length := by
      cases T₂ with
      | nil => exact absurd hT₂.isWalk.eq_of_nil hyb
      | cons _ _ => simp
    have hcat : T.length = T₁.length + T₂.length := by rw [hTcat, List.length_append]
    rw [hcover] at hyC
    rcases hyC with hy₁ | hy₂
    · have := hmin T₂ y b hT₂.isWalk hy₁ hbS
      omega
    · have := hmin T₁ a y hT₁.isWalk haS hy₂
      omega
  -- **"No edge of `R` is an edge of `C`."**
  have hedges_new : ∀ f ∈ T, f ∉ D ++ [e] := by
    intro f hf hfC
    have hfC' : f ∈ e :: D := by
      simp only [List.mem_append, List.mem_cons] at hfC ⊢
      tauto
    have hfF : f ∈ E(F) := hTedges f hf
    obtain ⟨z, w, hlfF⟩ := exists_isLink_of_mem_edgeSet hfF
    have hlf : H.IsLink f z w := hlfF.mono hFH
    have hz' : z = a ∨ z = b := by
      by_contra hcon
      push Not at hcon
      exact hinterior z (mem_walkVertices_of_mem_covered ⟨f, hf, hlf.inc_left⟩) hcon.1 hcon.2
        (hcyc.mem_walkVertices_of_inc hfC' hlf.inc_left)
    have hw' : w = a ∨ w = b := by
      by_contra hcon
      push Not at hcon
      exact hinterior w (mem_walkVertices_of_mem_covered ⟨f, hf, hlf.inc_right⟩) hcon.1 hcon.2
        (hcyc.mem_walkVertices_of_inc hfC' hlf.inc_right)
    have hzw : z ≠ w := by
      rintro rfl
      exact hR.not_isLoopAt hf z hlfF
    -- The edge would then join the two sides while lying in `F`.
    have hlink : H.IsLink f a b := by
      rcases hz' with rfl | rfl
      · rcases hw' with rfl | rfl
        · exact absurd rfl hzw
        · exact hlf
      · rcases hw' with rfl | rfl
        · exact hlf.symm
        · exact absurd rfl hzw
    refine Set.disjoint_left.1 hdisj (hside a b [f] (IsWalk.single hlink) ?_ ?_ haS) hbS
    · intro f' hf'
      rw [List.mem_singleton.1 hf']
      exact hfF
    · intro f' hf'
      rw [List.mem_singleton.1 hf']
      exact hfC'
  -- **"Each arc contains an edge outside `Γ (j-1)`."**
  have houtside : ∀ (T' : List β), H.IsWalk a T' b → (∀ f ∈ T', f ∈ e :: D) →
      ∃ f ∈ T', f ∉ E(F) := by
    intro T' hw hC
    by_contra hcon
    push Not at hcon
    exact Set.disjoint_left.1 hdisj (hside a b T' hw hcon hC haS) hbS
  have hD₁C : ∀ f ∈ D₁, f ∈ e :: D :=
    fun f hf => hsplit.mem_iff.1 (List.mem_append_left _ hf)
  have hD₂C : ∀ f ∈ D₂, f ∈ e :: D :=
    fun f hf => hsplit.mem_iff.1 (List.mem_append_right _ hf)
  obtain ⟨f₂, hf₂, hf₂F⟩ := houtside D₂.reverse harc₂.reverse.isWalk
    fun f hf => hD₂C f (List.mem_reverse.1 hf)
  exact ⟨a, b, T, D₁, D₂,
    { ne := hab
      arc₁ := harc₁
      arc₂ := harc₂
      split := hsplit
      isPath := hR.mono hFH
      mem_left := haC
      mem_right := hbC
      edges_mem := hTedges
      edges_new := hedges_new
      interior := hinterior
      outside₁ := houtside D₁ harc₁.isWalk hD₁C
      outside₂ := ⟨f₂, List.mem_reverse.1 hf₂, hf₂F⟩ }⟩

end General

/-! ## The descent step's crosscut -/

section Chain

variable {β : Type*} {Γ : ℕ → Graph Plane β} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {n : ℕ}

/-- **`Graph.CrosscutExists`, discharged.** From a cycle of the block
`Γ i ∪ ⋯ ∪ Γ (i+m+2)` carrying an edge of `Γ (i+m+2)` and an edge of the earlier chain, both
outside `Γ (i+m+1)`, build a crosscut of that cycle inside `Γ (i+m+1)`.

The two named edges cut the cycle into two arcs (`Graph.IsCycleThrough.split_at_edges`). Each
arc has a vertex in `Γ (i+m+1)`: walking along it from the edge of `Γ (i+m+2)` to the edge of
the earlier chain leaves `V(Γ (i+m+2))` at some edge, and that edge belongs neither to
`Γ (i+m+2)` (both its ends would stay inside) nor to the earlier chain (its end inside
`V(Γ (i+m+2))` would then lie on both, which
`Graph.IsPlaneChain.disjoint_block_far` forbids), so it belongs to `Γ (i+m+1)`. The rest is
`Graph.exists_isCycleCrosscut`. -/
theorem IsPlaneChain.crosscutExists (h : IsPlaneChain Γ drawing G n) {x : Plane} :
    CrosscutExists Γ drawing n x := by
  intro i m him e u v D hcyc _hin hA hB
  obtain ⟨gA, hgAC, hgAJ, hgAF⟩ := hA
  obtain ⟨gB, hgBC, hgBL, hgBF⟩ := hB
  -- The three pieces of the block, inside the block.
  have hFH : Γ (i + m + 1) ≤ chainUnion Γ i (m + 2) := h.le_block him (by omega) (by omega)
  have hJH : Γ (i + m + 2) ≤ chainUnion Γ i (m + 2) := h.le_block him (by omega) (by omega)
  have hLH : chainUnion Γ i m ≤ chainUnion Γ i (m + 2) :=
    chainUnion_le fun p hp _ => h.le_block him hp (by omega)
  -- Every edge of the block is an edge of one of the three.
  have hsplit : ∀ f ∈ E(chainUnion Γ i (m + 2)),
      f ∈ E(chainUnion Γ i m) ∨ f ∈ E(Γ (i + m + 1)) ∨ f ∈ E(Γ (i + m + 2)) := by
    intro f hf
    obtain ⟨p, hp, hp', hfp⟩ := mem_edgeSet_chainUnion.1 hf
    rcases Nat.lt_or_ge p (i + m + 1) with hlt | hge
    · exact Or.inl (mem_edgeSet_chainUnion.2 ⟨p, hp, by omega, hfp⟩)
    rcases Nat.lt_or_ge p (i + m + 2) with hlt' | hge'
    · obtain rfl : p = i + m + 1 := by omega
      exact Or.inr (Or.inl hfp)
    · obtain rfl : p = i + m + 2 := by omega
      exact Or.inr (Or.inr hfp)
  -- **"`Γ j` meets the earlier chain only through `Γ (j-1)`."** The only geometry used.
  have hVdisj : ∀ z : Plane, z ∈ V(chainUnion Γ i m) → z ∈ V(Γ (i + m + 2)) → False := by
    intro z hz hz'
    exact Set.disjoint_left.1 (h.disjoint_block_far (by omega))
      (vertexSet_subset_pointSet hz) (vertexSet_subset_pointSet hz')
  have hgAB : gA ≠ gB := by
    rintro rfl
    obtain ⟨p, hp, hp', hgp⟩ := mem_edgeSet_chainUnion.1 hgBL
    exact Set.disjoint_left.1
      (h.disjoint_edgeSet (p := p) (q := i + m + 2) (by omega) (by omega) (by omega)) hgp hgAJ
  obtain ⟨p₀, p₁, q₀, q₁, W₁, W₂, hlA, hW₁, hlB, hW₂, hperm, hdisj, hcover⟩ :=
    hcyc.split_at_edges hgAC hgBC hgAB
  have hlAJ : (Γ (i + m + 2)).IsLink gA p₁ p₀ := (hJH.isLink_iff hgAJ).2 hlA
  have hlBL : (chainUnion Γ i m).IsLink gB q₀ q₁ := (hLH.isLink_iff hgBL).2 hlB
  -- Neither cut edge is an edge of `Γ (i+m+1)`, so every cycle edge that is keeps its two
  -- ends on one arc.
  have hpres : ∀ f ∈ e :: D, f ∈ E(Γ (i + m + 1)) → ∀ z w : Plane,
      (chainUnion Γ i (m + 2)).IsLink f z w →
      (z ∈ (chainUnion Γ i (m + 2)).walkVertices p₀ W₁ ↔
        w ∈ (chainUnion Γ i (m + 2)).walkVertices p₀ W₁) := by
    intro f hfC hfF z w hlf
    have hfA : f ≠ gA := fun hh => hgAF (hh ▸ hfF)
    have hfB : f ≠ gB := fun hh => hgBF (hh ▸ hfF)
    have hfW : f ∈ W₁ ∨ f ∈ W₂ := by
      rcases List.mem_cons.1 (hperm.mem_iff.2 hfC) with rfl | hmem
      · exact absurd rfl hfA
      rcases List.mem_append.1 hmem with hmem' | hmem'
      · exact Or.inl hmem'
      rcases List.mem_cons.1 hmem' with rfl | hmem''
      · exact absurd rfl hfB
      · exact Or.inr hmem''
    rcases hfW with hfW | hfW
    · exact iff_of_true (mem_walkVertices_of_mem_covered ⟨f, hfW, hlf.inc_left⟩)
        (mem_walkVertices_of_mem_covered ⟨f, hfW, hlf.inc_right⟩)
    · refine iff_of_false (fun hz => ?_) fun hw => ?_
      · exact Set.disjoint_left.1 hdisj hz
          (mem_walkVertices_of_mem_covered ⟨f, hfW, hlf.inc_left⟩)
      · exact Set.disjoint_left.1 hdisj hw
          (mem_walkVertices_of_mem_covered ⟨f, hfW, hlf.inc_right⟩)
  -- **"Each of those two arcs must meet `Γ (j-1)`."** First arc.
  have hclaimA : ∃ a ∈ (chainUnion Γ i (m + 2)).walkVertices p₀ W₁, a ∈ V(Γ (i + m + 1)) := by
    have hwalk : (chainUnion Γ i (m + 2)).IsWalk p₁ (gA :: (W₁ ++ [gB])) q₁ :=
      .cons hlA (hW₁.isWalk.append (IsWalk.single hlB))
    obtain ⟨f, hf, z, w, hlf, hzJ, hwJ⟩ := hwalk.crossing (S := V(Γ (i + m + 2)))
      hlAJ.left_mem fun hh => hVdisj q₁ hlBL.right_mem hh
    have hfJ : f ∉ E(Γ (i + m + 2)) := fun hh => hwJ ((hJH.isLink_iff hh).2 hlf).right_mem
    have hfL : f ∉ E(chainUnion Γ i m) := fun hh =>
      hVdisj z ((hLH.isLink_iff hh).2 hlf).left_mem hzJ
    have hfF : f ∈ E(Γ (i + m + 1)) := by
      rcases hsplit f hlf.edge_mem with hh | hh | hh
      · exact absurd hh hfL
      · exact hh
      · exact absurd hh hfJ
    have hfW₁ : f ∈ W₁ := by
      rcases List.mem_cons.1 hf with rfl | hf'
      · exact absurd hfF hgAF
      rcases List.mem_append.1 hf' with hf'' | hf''
      · exact hf''
      · obtain rfl : f = gB := by simpa using hf''
        exact absurd hfF hgBF
    exact ⟨z, mem_walkVertices_of_mem_covered ⟨f, hfW₁, hlf.inc_left⟩,
      ((hFH.isLink_iff hfF).2 hlf).left_mem⟩
  -- Second arc, with the roles of the two ends of the chain exchanged.
  have hclaimB : ∃ b ∈ (chainUnion Γ i (m + 2)).walkVertices q₁ W₂, b ∈ V(Γ (i + m + 1)) := by
    have hwalk : (chainUnion Γ i (m + 2)).IsWalk q₁ (W₂ ++ [gA]) p₀ :=
      hW₂.isWalk.append (IsWalk.single hlA)
    obtain ⟨f, hf, z, w, hlf, hzL, hwL⟩ := hwalk.crossing (S := V(chainUnion Γ i m))
      hlBL.right_mem fun hh => hVdisj p₀ hh hlAJ.right_mem
    have hfL : f ∉ E(chainUnion Γ i m) := fun hh => hwL ((hLH.isLink_iff hh).2 hlf).right_mem
    have hfJ : f ∉ E(Γ (i + m + 2)) := fun hh =>
      hVdisj z hzL ((hJH.isLink_iff hh).2 hlf).left_mem
    have hfF : f ∈ E(Γ (i + m + 1)) := by
      rcases hsplit f hlf.edge_mem with hh | hh | hh
      · exact absurd hh hfL
      · exact hh
      · exact absurd hh hfJ
    have hfW₂ : f ∈ W₂ := by
      rcases List.mem_append.1 hf with hf' | hf'
      · exact hf'
      · obtain rfl : f = gA := by simpa using hf'
        exact absurd hfF hgAF
    exact ⟨z, mem_walkVertices_of_mem_covered ⟨f, hfW₂, hlf.inc_left⟩,
      ((hFH.isLink_iff hfF).2 hlf).left_mem⟩
  exact exists_isCycleCrosscut hcyc hFH hdisj hcover hpres
    (h.twoConnected _ (by omega)).connected hclaimA hclaimB

end Chain

end Graph
