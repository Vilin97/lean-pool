/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

import LeanPool.PDL.Interpolation.ClusterSatDownFacts

/-! # Interpolants for proper clusters (Lemma 9.3)

This file contains the interpolation step for proper clusters: given interpolants for all
exit nodes of a cluster, we build an interpolant for the root of the cluster.

The ingredients live in the files imported here:
`Pdl.InterpolationCluster` (the cluster `C`, its quasi-tableau `Q` of Def 9.8, the region
formulas `θ_Δ` of Def 9.13 and Lemma 9.14), `Pdl.QFormula` (Def 9.15, Def 9.16 and
Fact 9.17), `Pdl.PreInterpolant` (the pre-interpolants of Def 9.18), `Pdl.ClusterItp`
(Def 9.20 and Lemma 10.1), `Pdl.ClusterRho` (Def 10.2 and Lemma 10.3) and
`Pdl.ClusterSatDown` (Lemmas 10.6, 10.7 and 10.8).

The three conditions on the interpolant `θ_r := C.itp θ` of Definition 9.20 are exactly

* `LoadedCluster.itp_voc` (Lemma 10.1),
* `LoadedCluster.left_unsat_neg_itp` (Lemma 10.3), and
* `LoadedCluster.right_unsat_itp` (Lemma 10.8).

What this file adds is the *interface*: the interpolants `θ` used by those three results
are indexed by the **fine** exit nodes of the cluster, i.e. also by nodes *inside* a local
tableau, while `clusterInterpolationRight` is only given interpolants for the exits in the
coarse `PathIn` sense. The first half of the file bridges that gap, by pushing the
interpolants of the coarse exits upwards through the local tableaux with
`LocalTableau.interpolant`.
-/

namespace PDL

open HasSat

/-! ## Helpers for `endNodesOf`

Since `endNodesOf` now returns a `Finset Sequent`, this membership lemma replaces the
old `simp only [endNodesOf, List.mem_flatten, ...]` incantations. For the `byLocalRule`
case we use `mem_endNodesOf_byLocalRule_iff` from `Pdl/Interpolation/FinePath.lean`.
It would better belong in `Pdl/Local/Tableau.lean`, next to `endNodesOf`. -/

lemma mem_endNodesOf_sim {X : Sequent} {h : X.basic} {E : Sequent} :
    E ∈ endNodesOf (LocalTableau.sim h) ↔ E = X := by
  simp [endNodesOf]

variable {X : Sequent} {tab : Tableau .nil X}

/-! ## Flipping Interpolants -/

/-- When `X` is an interpolant for `X`, then `~θ` is an interpolant for `X.flip`. -/
lemma IsPartInterpolant.flip : isPartInterpolant X θ → isPartInterpolant X.flip (~θ) := by
  rintro ⟨voc, l_ip, r_ip⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp_all [HasSat.satisfiable]
  grind

/-- Transport an interpolant to the flipped tableau. -/
def PartInterpolant.flipPath {p : PathIn tab}
    (ip : PartInterpolant (nodeAt p)) : PartInterpolant (nodeAt p.flip) :=
  ⟨~ip.1, by rw [PathIn.nodeAt_flip]; exact IsPartInterpolant.flip ip.2⟩

/-- Transport an interpolant back from the flipped tableau. -/
def PartInterpolant.unflipPath {p : PathIn tab}
    (ip : PartInterpolant (nodeAt p.flip)) : PartInterpolant (nodeAt p) := by
  refine ⟨~ip.1, ?_⟩
  have h : (nodeAt p.flip).flip = nodeAt p := by rw [PathIn.nodeAt_flip, Sequent.flip_flip]
  exact h ▸ IsPartInterpolant.flip ip.2

/-! ## From the coarse exits to the fine exits

A fine exit of the cluster is either a coarse node — then it is an exit in the coarse sense
and we are given an interpolant for it — or a node inside a local tableau from which the
cluster is never re-entered. In the latter case all end nodes of the local tableau below it
are coarse exits, and we obtain an interpolant by local interpolation. -/

/-- Every end node of the local tableau at a local path is an end node of the whole local
tableau that is below that path. -/
lemma LocalPathIn.exists_mem_endNodesBelow {Y : Sequent} :
    ∀ {Z : Sequent} {lt : LocalTableau Z} (lp : LocalPathIn lt), Y ∈ endNodesOf lp.ltAt →
      ∃ hY : Y ∈ endNodesOf lt, (⟨Y, hY⟩ : {W : Sequent // W ∈ endNodesOf lt}) ∈ lp.endNodesBelow
  | _, lt, .nil, h => ⟨h, by simp [LocalPathIn.endNodesBelow]⟩
  | _, .byLocalRule lra X_def next, .cons Y_in tail, h => by
      obtain ⟨hY, hmem⟩ := LocalPathIn.exists_mem_endNodesBelow tail h
      refine ⟨?_, ?_⟩
      · exact mem_endNodesOf_byLocalRule_iff.mpr ⟨_, Y_in, hY⟩
      · simp only [LocalPathIn.endNodesBelow, List.mem_map, Subtype.exists]
        exact ⟨Y, hY, hmem, rfl⟩

/-- A coarse child below a fine node really is a child of the base of that fine node. -/
lemma FinePathIn.edge_of_mem_coarseChildrenBelow : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'), ∀ q ∈ f.coarseChildrenBelow, f.base ⋖_ q
  | _, _, _, .inLoc lp _, q, hq => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map, Subtype.exists] at hq
      obtain ⟨Y, Y_in, -, rfl⟩ := hq
      simp [FinePathIn.base]
  | _, _, _, .pdlHere, q, hq => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_singleton] at hq
      subst hq
      simp [FinePathIn.base]
  | _, _, _, .lrepHere, q, hq => by simp [FinePathIn.coarseChildrenBelow] at hq
  | _, _, _, .loc Y_in tail, q, hq => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      simpa [FinePathIn.base, loc_edge_loc_iff_edge] using
        FinePathIn.edge_of_mem_coarseChildrenBelow tail q' hq'
  | _, _, _, .pdl tail, q, hq => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      simpa [FinePathIn.base, pdl_edge_pdl_iff_edge] using
        FinePathIn.edge_of_mem_coarseChildrenBelow tail q' hq'

/-- A sharpening of `FinePathIn.base_of_mem_children`: a fine child that lies at a
different coarse node is a coarse node itself. -/
lemma FinePathIn.base_of_mem_children' : ∀ {H : History} {Z : Sequent} {tab' : Tableau H Z}
    (f : FinePathIn tab'), ∀ g ∈ f.children, g.base = f.base ∨ (f.base ⋖_ g.base ∧ g.atBigRoot)
  | _, _, _, .inLoc lp lp_int, g, hg => by
      simp only [FinePathIn.children, Finset.mem_image] at hg
      obtain ⟨lp', -, rfl⟩ := hg
      split
      · exact Or.inr ⟨by simp [FinePathIn.base], by simp [FinePathIn.atBigRoot]⟩
      · exact Or.inl rfl
  | _, _, _, .pdlHere, g, hg => by
      simp only [FinePathIn.children, Finset.mem_singleton] at hg
      subst hg
      exact Or.inr ⟨by simp [FinePathIn.base], by simp [FinePathIn.atBigRoot]⟩
  | _, _, _, .lrepHere, g, hg => by simp [FinePathIn.children] at hg
  | _, _, _, .loc Y_in tail, g, hg => by
      simp only [FinePathIn.children, Finset.mem_image] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      rcases FinePathIn.base_of_mem_children' tail g' hg' with h | ⟨h1, h2⟩
      · exact Or.inl (by simp [FinePathIn.base, h])
      · exact Or.inr ⟨by simpa [FinePathIn.base, loc_edge_loc_iff_edge] using h1,
          by simpa [FinePathIn.atBigRoot] using h2⟩
  | _, _, _, .pdl tail, g, hg => by
      simp only [FinePathIn.children, Finset.mem_image] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      rcases FinePathIn.base_of_mem_children' tail g' hg' with h | ⟨h1, h2⟩
      · exact Or.inl (by simp [FinePathIn.base, h])
      · exact Or.inr ⟨by simpa [FinePathIn.base, pdl_edge_pdl_iff_edge] using h1,
          by simpa [FinePathIn.atBigRoot] using h2⟩

/-- **Local interpolation at fine nodes.** If a fine node is not a coarse node, i.e. it
lies properly inside a local tableau, and we have interpolants for all coarse children
below it — these are the end nodes of that local tableau that are reachable from it — then
we have an interpolant for the fine node itself. This is `LocalTableau.interpolant` applied
to the part of the local tableau below the node. -/
lemma FinePathIn.exists_interpolant_of_coarse : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'), ¬ f.atBigRoot →
      (∀ q ∈ f.coarseChildrenBelow, ∃ θ, isPartInterpolant (nodeAt q) θ) →
      ∃ θ, isPartInterpolant f.label θ
  | _, _, _, .inLoc lp lp_int, _, h => by
      have endθs : ∀ Y ∈ endNodesOf lp.ltAt, PartInterpolant Y := by
        intro Y hY
        have hex : ∃ θ, isPartInterpolant Y θ := by
          obtain ⟨hY', hmem⟩ := lp.exists_mem_endNodesBelow hY
          have := h (PathIn.loc hY' .nil) (by
            simp only [FinePathIn.coarseChildrenBelow, List.mem_map, Subtype.exists]
            exact ⟨Y, hY', hmem, rfl⟩)
          rwa [nodeAt_loc_nil] at this
        exact ⟨hex.choose, hex.choose_spec⟩
      have := LocalTableau.interpolant lp.ltAt endθs
      exact ⟨this.1, this.2⟩
  | _, _, _, .pdlHere, hbr, _ => absurd (by simp [FinePathIn.atBigRoot]) hbr
  | _, _, _, .lrepHere, hbr, _ => absurd (by simp [FinePathIn.atBigRoot]) hbr
  | _, _, _, .loc Y_in tail, hbr, h => by
      refine FinePathIn.exists_interpolant_of_coarse tail
        (by simpa [FinePathIn.atBigRoot] using hbr) ?_
      intro q hq
      have := h (PathIn.loc Y_in q)
        (by simp only [FinePathIn.coarseChildrenBelow]; exact List.mem_map_of_mem hq)
      rwa [nodeAt_loc] at this
  | _, _, _, .pdl tail, hbr, h => by
      refine FinePathIn.exists_interpolant_of_coarse tail
        (by simpa [FinePathIn.atBigRoot] using hbr) ?_
      intro q hq
      have := h (PathIn.pdl q)
        (by simp only [FinePathIn.coarseChildrenBelow]; exact List.mem_map_of_mem hq)
      rwa [nodeAt_pdl] at this

open Classical in
/-- An interpolant for the label of a fine node, whenever one exists. This is the map `θ`
on the fine exit nodes that Definitions 9.13 and 9.18 need. -/
noncomputable def FinePathIn.itp {H : History} {Z : Sequent} {tab' : Tableau H Z}
    (f : FinePathIn tab') : Formula :=
  if h : ∃ θ, isPartInterpolant f.label θ then h.choose else ⊤

lemma FinePathIn.itp_spec {H : History} {Z : Sequent} {tab' : Tableau H Z} {f : FinePathIn tab'}
    (h : ∃ θ, isPartInterpolant f.label θ) : isPartInterpolant f.label f.itp := by
  rw [FinePathIn.itp, dite_eq_left h]
  exact h.choose_spec

namespace LoadedCluster

/-- Every coarse child below a fine exit of the cluster is a coarse exit of the cluster. -/
lemma mem_exits_of_mem_coarseChildrenBelow (C : LoadedCluster tab) {f : FinePathIn tab}
    (hbase : f.base ∈ C.CL) (hf : ¬ C.memFine f) :
    ∀ q ∈ f.coarseChildrenBelow, q ∈ C.exits := by
  intro q hq
  have hnot : ∀ q' ∈ f.coarseChildrenBelow, q' ∉ C.CL := by
    intro q' hq' hq'CL
    exact hf ⟨hbase, Or.inr ⟨q', hq', hq'CL⟩⟩
  rw [LoadedCluster.exits, Finset.mem_filter, Finset.mem_biUnion]
  refine ⟨⟨f.base, hbase, ?_⟩, hnot q hq⟩
  exact PathIn.children_spec.mp (f.edge_of_mem_coarseChildrenBelow q hq)

/-- A fine exit of the cluster that is a coarse node is a coarse exit of the cluster. -/
lemma mem_exits_base_of_mem_fineExits (C : LoadedCluster tab) {f : FinePathIn tab}
    (hf : f ∈ C.fineExits) (hbr : f.atBigRoot) : f.base ∈ C.exits := by
  simp only [fineExits, Finset.mem_filter, Finset.mem_sup, List.mem_toFinset,
    decide_eq_true_eq] at hf
  obtain ⟨⟨g, hg, hfg⟩, hnot⟩ := hf
  have hgCL : g.base ∈ C.CL := ((C.mem_fineCL g).mp hg).1
  have hfCL : f.base ∉ C.CL := fun hin => hnot ⟨hin, Or.inl hbr⟩
  have hedge : g.base ⋖_ f.base := by
    rcases g.base_of_mem_children' f hfg with h | ⟨h, -⟩
    · exact absurd (h ▸ hgCL) hfCL
    · exact h
  rw [LoadedCluster.exits, Finset.mem_filter, Finset.mem_biUnion]
  exact ⟨⟨g.base, hgCL, PathIn.children_spec.mp hedge⟩, hfCL⟩

/-- Interpolants for the coarse exits of the cluster give interpolants for all fine exits. -/
lemma exists_itp_of_mem_fineExits (C : LoadedCluster tab)
    (exitIPs : ∀ e ∈ C.exits, ∃ θ, isPartInterpolant (nodeAt e) θ) :
    ∀ f ∈ C.fineExits, ∃ θ, isPartInterpolant f.label θ := by
  intro f hf
  have hf' := hf
  simp only [fineExits, Finset.mem_filter, Finset.mem_sup, List.mem_toFinset,
    decide_eq_true_eq] at hf'
  obtain ⟨⟨g, hg, hfg⟩, hnot⟩ := hf'
  by_cases hbr : f.atBigRoot
  · -- `f` is a coarse node, hence a coarse exit.
    have := exitIPs _ (C.mem_exits_base_of_mem_fineExits hf hbr)
    rw [← PathIn.label_toFine, ← f.eq_toFine_base_of_atBigRoot hbr] at this
    exact this
  · -- `f` lies properly inside a local tableau; use local interpolation.
    have hbase : f.base = g.base := by
      rcases g.base_of_mem_children' f hfg with h | ⟨-, h⟩
      · exact h
      · exact absurd h hbr
    have hbaseCL : f.base ∈ C.CL := hbase ▸ ((C.mem_fineCL g).mp hg).1
    refine f.exists_interpolant_of_coarse hbr ?_
    intro q hq
    exact exitIPs q (C.mem_exits_of_mem_coarseChildrenBelow hbaseCL hnot q hq)

/-- The interpolants of the fine exit nodes of the cluster, given interpolants for the
coarse exits. This is the map `θ` of Definitions 9.13, 9.18 and 9.20. -/
lemma fineExits_itp_spec (C : LoadedCluster tab)
    (exitIPs : ∀ e ∈ C.exits, ∃ θ, isPartInterpolant (nodeAt e) θ) :
    ∀ f ∈ C.fineExits, isPartInterpolant f.label (FinePathIn.itp f) :=
  fun f hf => FinePathIn.itp_spec (C.exists_itp_of_mem_fineExits exitIPs f hf)

end LoadedCluster

/-! ### Vocabulary preservation

Lemma 9.2 of the paper: along the tableau the vocabulary of each of the two components
only shrinks.  "By inspection of the rules": for local rules this is
`localRule_does_not_increase_vocab_L` and `localRule_does_not_increase_vocab_R`, and for
the PDL rules we check the six cases directly. -/

section VocPreservation

/-- Membership in the vocabulary of a `Finset` of formulas.
This is `Finset.mem_fvoc` from `Pdl/Interpolation/Local.lean`. -/
lemma mem_fvoc_iff {L : Finset Formula} {x} : x ∈ L.pdlFvoc ↔ ∃ φ ∈ L, x ∈ φ.voc :=
  Finset.mem_fvoc

/-- Since sequents now use `Finset`s, being "set equal" is just being equal. -/
lemma Sequent.left_fvoc_eq_of_eq {X Y : Sequent} (h : X = Y) :
    X.left.pdlFvoc = Y.left.pdlFvoc := by rw [h]

/-- Since sequents now use `Finset`s, being "set equal" is just being equal. -/
lemma Sequent.right_fvoc_eq_of_eq {X Y : Sequent} (h : X = Y) :
    X.right.pdlFvoc = Y.right.pdlFvoc := by rw [h]

/-- A local rule application does not increase the vocabulary of the left component.
This is the left half of `localRuleApp_does_not_increase_jvoc`. -/
lemma LocalRuleApp.left_fvoc_subset (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, Y.left.pdlFvoc ⊆ lra.X.left.pdlFvoc := by
  match lra with
  | @LocalRuleApp.mk L R O Lcond Rcond Ocond ress lrule C hC preconditionProof =>
    subst hC
    rintro ⟨cL, cR, cO⟩ C_in
    simp only [applyLocalRule, Finset.mem_image] at C_in
    rcases C_in with ⟨⟨Lres, Rres, Ores⟩, res_in, def_c⟩
    simp only at def_c
    cases def_c
    have Lsub := localRule_does_not_increase_vocab_L lrule _ res_in
    simp only [Sequent.left_eq] at Lsub
    have hcond : ∀ y ∈ (Lcond ∪ Ocond.L).pdlFvoc, y ∈ L.pdlFvoc ∨ y ∈ O.L.pdlFvoc := by
      intro y hy
      rw [Finset.fvoc_union, Finset.mem_union] at hy
      rcases hy with h | h
      · exact Or.inl (Finset.fvoc_mono preconditionProof.1 h)
      · exact Or.inr (Finset.fvoc_mono (Olf.L_subset_of_subset preconditionProof.2.2) h)
    have hres : ∀ y ∈ (Lres ∪ Ores.L).pdlFvoc, y ∈ L.pdlFvoc ∨ y ∈ O.L.pdlFvoc :=
      fun y hy => hcond y (Lsub hy)
    intro x x_in
    simp only [LocalRuleApp.X, Sequent.left_eq, Finset.fvoc_union, Finset.mem_union] at x_in ⊢
    rcases x_in with (h | h) | h
    · exact Or.inl (Finset.fvoc_mono Finset.sdiff_subset h)
    · exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inl h)
    · rcases Ores with _ | z
      · refine Or.inr (Finset.fvoc_mono ?_ h)
        simpa only [Olf.change, Option.pdlOverwrite] using Olf.L_sdiff_subset
      · rw [Olf.change_some] at h
        exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inr h)

/-- A local rule application does not increase the vocabulary of the right component.
This is the right half of `localRuleApp_does_not_increase_jvoc`. -/
lemma LocalRuleApp.right_fvoc_subset (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, Y.right.pdlFvoc ⊆ lra.X.right.pdlFvoc := by
  match lra with
  | @LocalRuleApp.mk L R O Lcond Rcond Ocond ress lrule C hC preconditionProof =>
    subst hC
    rintro ⟨cL, cR, cO⟩ C_in
    simp only [applyLocalRule, Finset.mem_image] at C_in
    rcases C_in with ⟨⟨Lres, Rres, Ores⟩, res_in, def_c⟩
    simp only at def_c
    cases def_c
    have Rsub := localRule_does_not_increase_vocab_R lrule _ res_in
    simp only [Sequent.right_eq] at Rsub
    have hcond : ∀ y ∈ (Rcond ∪ Ocond.R).pdlFvoc, y ∈ R.pdlFvoc ∨ y ∈ O.R.pdlFvoc := by
      intro y hy
      rw [Finset.fvoc_union, Finset.mem_union] at hy
      rcases hy with h | h
      · exact Or.inl (Finset.fvoc_mono preconditionProof.2.1 h)
      · exact Or.inr (Finset.fvoc_mono (Olf.R_subset_of_subset preconditionProof.2.2) h)
    have hres : ∀ y ∈ (Rres ∪ Ores.R).pdlFvoc, y ∈ R.pdlFvoc ∨ y ∈ O.R.pdlFvoc :=
      fun y hy => hcond y (Rsub hy)
    intro x x_in
    simp only [LocalRuleApp.X, Sequent.right_eq, Finset.fvoc_union, Finset.mem_union] at x_in ⊢
    rcases x_in with (h | h) | h
    · exact Or.inl (Finset.fvoc_mono Finset.sdiff_subset h)
    · exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inl h)
    · rcases Ores with _ | z
      · refine Or.inr (Finset.fvoc_mono ?_ h)
        simpa only [Olf.change, Option.pdlOverwrite] using Olf.R_sdiff_subset
      · rw [Olf.change_some] at h
        exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inr h)

/-- Inside a local tableau the vocabulary of the left component only shrinks. -/
lemma LocalPathIn.last_left_fvoc_subset : ∀ {X : Sequent} {lt : LocalTableau X}
    (lp : LocalPathIn lt), lp.last.left.pdlFvoc ⊆ X.left.pdlFvoc
  | _, _, .nil => by simp [LocalPathIn.last]
  | _, .byLocalRule lra X_def next, .cons Y_in tail => by
      simp only [LocalPathIn.last]
      exact subset_trans (LocalPathIn.last_left_fvoc_subset tail)
        (X_def ▸ lra.left_fvoc_subset _ Y_in)

/-- Inside a local tableau the vocabulary of the right component only shrinks. -/
lemma LocalPathIn.last_right_fvoc_subset : ∀ {X : Sequent} {lt : LocalTableau X}
    (lp : LocalPathIn lt), lp.last.right.pdlFvoc ⊆ X.right.pdlFvoc
  | _, _, .nil => by simp [LocalPathIn.last]
  | _, .byLocalRule lra X_def next, .cons Y_in tail => by
      simp only [LocalPathIn.last]
      exact subset_trans (LocalPathIn.last_right_fvoc_subset tail)
        (X_def ▸ lra.right_fvoc_subset _ Y_in)

lemma endNodesOf_left_fvoc_subset : ∀ {X : Sequent} (lt : LocalTableau X),
    ∀ Y ∈ endNodesOf lt, Y.left.pdlFvoc ⊆ X.left.pdlFvoc
  | _, .sim _, Y, hY => by rw [mem_endNodesOf_sim] at hY; simp [hY]
  | _, .byLocalRule lra X_def next, Y, hY => by
      obtain ⟨Z, Z_in, hY⟩ := mem_endNodesOf_byLocalRule_iff.mp hY
      exact subset_trans (endNodesOf_left_fvoc_subset _ Y hY) (X_def ▸ lra.left_fvoc_subset _ Z_in)

lemma endNodesOf_right_fvoc_subset : ∀ {X : Sequent} (lt : LocalTableau X),
    ∀ Y ∈ endNodesOf lt, Y.right.pdlFvoc ⊆ X.right.pdlFvoc
  | _, .sim _, Y, hY => by rw [mem_endNodesOf_sim] at hY; simp [hY]
  | _, .byLocalRule lra X_def next, Y, hY => by
      obtain ⟨Z, Z_in, hY⟩ := mem_endNodesOf_byLocalRule_iff.mp hY
      exact subset_trans (endNodesOf_right_fvoc_subset _ Y hY)
        (X_def ▸ lra.right_fvoc_subset _ Z_in)

lemma projection_fvoc_subset (A : Nat) (L : Finset Formula) :
    (Finset.pdlProjection A L).pdlFvoc ⊆ L.pdlFvoc := by
  intro x hx
  rw [mem_fvoc_iff] at hx ⊢
  obtain ⟨ψ, hψ, hx⟩ := hx
  exact ⟨⌈·A⌉ψ, Finset.mem_projection.mp hψ, by simp; tauto⟩

/-- A PDL rule does not increase the vocabulary of the left component. -/
lemma PdlRule.left_fvoc_subset {X Y : Sequent} (r : PdlRule X Y) :
    Y.left.pdlFvoc ⊆ X.left.pdlFvoc := by
  intro x hx
  rw [mem_fvoc_iff] at hx ⊢
  obtain ⟨ψ, hψ, hx⟩ := hx
  cases r
  case loadR L R δ α φ hin hnb hY =>
    subst hY; simp only [Sequent.left_eq, Olf.L_none, Olf.L_inr, Finset.union_empty] at hψ ⊢
    exact ⟨ψ, hψ, hx⟩
  case freeR L R δ α φ hX hY =>
    subst hX; subst hY
    simp only [Sequent.left_eq, Olf.L_none, Olf.L_inr, Finset.union_empty] at hψ ⊢
    exact ⟨ψ, hψ, hx⟩
  case loadL L δ α φ R hin hnb hY =>
    subst hY
    simp only [Sequent.left_eq, Olf.L_none, Olf.L_inl, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hψ ⊢
    rcases hψ with hψ | rfl
    · exact ⟨ψ, Finset.mem_of_mem_erase hψ, hx⟩
    · exact ⟨_, hin, by simpa [LoadFormula.unload] using hx⟩
  case freeL L R δ α φ hX hY =>
    subst hX; subst hY
    simp only [Sequent.left_eq, Olf.L_none, Olf.L_inl, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hψ ⊢
    rcases hψ with hψ | rfl
    · exact ⟨ψ, Or.inl hψ, hx⟩
    · exact ⟨_, Or.inr rfl, by simpa [LoadFormula.unload] using hx⟩
  case modL L R A ξ hX hY =>
    subst hX
    cases ξ <;> subst hY <;>
      simp only [Sequent.left_eq, Olf.L_none, Olf.L_inl, Finset.union_empty,
        Finset.mem_union, Finset.mem_singleton] at hψ ⊢
    · rcases hψ with rfl | hψ
      · exact ⟨_, Or.inr rfl, by simp [LoadFormula.unload] at hx ⊢; tauto⟩
      · exact ⟨_, Or.inl (Finset.mem_projection.mp hψ), by simp; tauto⟩
    · rcases hψ with hψ | rfl
      · exact ⟨_, Or.inl (Finset.mem_projection.mp hψ), by simp; tauto⟩
      · exact ⟨_, Or.inr rfl, by simp [LoadFormula.unload] at hx ⊢; tauto⟩
  case modR L R A ξ hX hY =>
    subst hX
    cases ξ <;> subst hY <;>
      simp only [Sequent.left_eq, Olf.L_none, Olf.L_inr, Finset.union_empty] at hψ ⊢
    · exact ⟨_, Finset.mem_projection.mp hψ, by simp; tauto⟩
    · exact ⟨_, Finset.mem_projection.mp hψ, by simp; tauto⟩

/-- A PDL rule does not increase the vocabulary of the right component. -/
lemma PdlRule.right_fvoc_subset {X Y : Sequent} (r : PdlRule X Y) :
    Y.right.pdlFvoc ⊆ X.right.pdlFvoc := by
  intro x hx
  rw [mem_fvoc_iff] at hx ⊢
  obtain ⟨ψ, hψ, hx⟩ := hx
  cases r
  case loadL L δ α φ R hin hnb hY =>
    subst hY; simp only [Sequent.right_eq, Olf.R_none, Olf.R_inl, Finset.union_empty] at hψ ⊢
    exact ⟨ψ, hψ, hx⟩
  case freeL L R δ α φ hX hY =>
    subst hX; subst hY
    simp only [Sequent.right_eq, Olf.R_none, Olf.R_inl, Finset.union_empty] at hψ ⊢
    exact ⟨ψ, hψ, hx⟩
  case loadR R δ α φ L hin hnb hY =>
    subst hY
    simp only [Sequent.right_eq, Olf.R_none, Olf.R_inr, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hψ ⊢
    rcases hψ with hψ | rfl
    · exact ⟨ψ, Finset.mem_of_mem_erase hψ, hx⟩
    · exact ⟨_, hin, by simpa [LoadFormula.unload] using hx⟩
  case freeR L R δ α φ hX hY =>
    subst hX; subst hY
    simp only [Sequent.right_eq, Olf.R_none, Olf.R_inr, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hψ ⊢
    rcases hψ with hψ | rfl
    · exact ⟨ψ, Or.inl hψ, hx⟩
    · exact ⟨_, Or.inr rfl, by simpa [LoadFormula.unload] using hx⟩
  case modR L R A ξ hX hY =>
    subst hX
    cases ξ <;> subst hY <;>
      simp only [Sequent.right_eq, Olf.R_none, Olf.R_inr, Finset.union_empty,
        Finset.mem_union, Finset.mem_singleton] at hψ ⊢
    · rcases hψ with rfl | hψ
      · exact ⟨_, Or.inr rfl, by simp [LoadFormula.unload] at hx ⊢; tauto⟩
      · exact ⟨_, Or.inl (Finset.mem_projection.mp hψ), by simp; tauto⟩
    · rcases hψ with hψ | rfl
      · exact ⟨_, Or.inl (Finset.mem_projection.mp hψ), by simp; tauto⟩
      · exact ⟨_, Or.inr rfl, by simp [LoadFormula.unload] at hx ⊢; tauto⟩
  case modL L R A ξ hX hY =>
    subst hX
    cases ξ <;> subst hY <;>
      simp only [Sequent.right_eq, Olf.R_none, Olf.R_inl, Finset.union_empty] at hψ ⊢
    · exact ⟨_, Finset.mem_projection.mp hψ, by simp; tauto⟩
    · exact ⟨_, Finset.mem_projection.mp hψ, by simp; tauto⟩

lemma edge_left_fvoc_subset {H : History} {Z : Sequent} {tab' : Tableau H Z} {s t : PathIn tab'}
    (h : s ⋖_ t) : (nodeAt t).left.pdlFvoc ⊆ (nodeAt s).left.pdlFvoc := by
  rcases nodeAt_of_edge h with ⟨lt, hlt⟩ | hr
  · exact endNodesOf_left_fvoc_subset lt _ hlt
  · obtain ⟨r⟩ := hr
    exact r.left_fvoc_subset

lemma edge_right_fvoc_subset {H : History} {Z : Sequent} {tab' : Tableau H Z} {s t : PathIn tab'}
    (h : s ⋖_ t) : (nodeAt t).right.pdlFvoc ⊆ (nodeAt s).right.pdlFvoc := by
  rcases nodeAt_of_edge h with ⟨lt, hlt⟩ | hr
  · exact endNodesOf_right_fvoc_subset lt _ hlt
  · obtain ⟨r⟩ := hr
    exact r.right_fvoc_subset

lemma cEdge_left_fvoc_subset {s t : PathIn tab} (h : s ◃ t) :
    (nodeAt t).left.pdlFvoc ⊆ (nodeAt s).left.pdlFvoc := by
  rcases h with h | ⟨lpr, hs, rfl⟩
  · exact edge_left_fvoc_subset h
  · exact le_of_eq (Sequent.left_fvoc_eq_of_eq (nodeAt_companionOf_setEq s lpr hs))

lemma cEdge_right_fvoc_subset {s t : PathIn tab} (h : s ◃ t) :
    (nodeAt t).right.pdlFvoc ⊆ (nodeAt s).right.pdlFvoc := by
  rcases h with h | ⟨lpr, hs, rfl⟩
  · exact edge_right_fvoc_subset h
  · exact le_of_eq (Sequent.right_fvoc_eq_of_eq (nodeAt_companionOf_setEq s lpr hs))

/-- Lemma 9.2, left component: along `◃` the vocabulary only shrinks. -/
lemma cReach_left_fvoc_subset {s t : PathIn tab} (h : s ◃* t) :
    (nodeAt t).left.pdlFvoc ⊆ (nodeAt s).left.pdlFvoc := by
  induction h with
  | refl => exact subset_rfl
  | tail _ hst IH => exact subset_trans (cEdge_left_fvoc_subset hst) IH

/-- Lemma 9.2, right component: along `◃` the vocabulary only shrinks. -/
lemma cReach_right_fvoc_subset {s t : PathIn tab} (h : s ◃* t) :
    (nodeAt t).right.pdlFvoc ⊆ (nodeAt s).right.pdlFvoc := by
  induction h with
  | refl => exact subset_rfl
  | tail _ hst IH => exact subset_trans (cEdge_right_fvoc_subset hst) IH

/-- The label of a fine node has a smaller vocabulary than the coarse node it lies in. -/
lemma FinePathIn.label_left_fvoc_subset_base : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'),
    f.label.left.pdlFvoc ⊆ (nodeAt f.base).left.pdlFvoc
  | _, _, _, .inLoc lp _ => by
      simpa [FinePathIn.label, FinePathIn.base, nodeAt, tabAt] using
        LocalPathIn.last_left_fvoc_subset lp
  | _, _, _, .pdlHere => by simp [FinePathIn.label, FinePathIn.base, nodeAt, tabAt]
  | _, _, _, .lrepHere => by simp [FinePathIn.label, FinePathIn.base, nodeAt, tabAt]
  | _, _, _, .loc Y_in tail => by
      simpa [FinePathIn.label, FinePathIn.base, nodeAt, tabAt] using
        FinePathIn.label_left_fvoc_subset_base tail
  | _, _, _, .pdl tail => by
      simpa [FinePathIn.label, FinePathIn.base, nodeAt, tabAt] using
        FinePathIn.label_left_fvoc_subset_base tail

lemma FinePathIn.label_right_fvoc_subset_base : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'),
    f.label.right.pdlFvoc ⊆ (nodeAt f.base).right.pdlFvoc
  | _, _, _, .inLoc lp _ => by
      simpa [FinePathIn.label, FinePathIn.base, nodeAt, tabAt] using
        LocalPathIn.last_right_fvoc_subset lp
  | _, _, _, .pdlHere => by simp [FinePathIn.label, FinePathIn.base, nodeAt, tabAt]
  | _, _, _, .lrepHere => by simp [FinePathIn.label, FinePathIn.base, nodeAt, tabAt]
  | _, _, _, .loc Y_in tail => by
      simpa [FinePathIn.label, FinePathIn.base, nodeAt, tabAt] using
        FinePathIn.label_right_fvoc_subset_base tail
  | _, _, _, .pdl tail => by
      simpa [FinePathIn.label, FinePathIn.base, nodeAt, tabAt] using
        FinePathIn.label_right_fvoc_subset_base tail

end VocPreservation

/-! ### Right rules do not change the left component

The two "right" local rules only act on the right component and on a loaded formula on the
right, so they leave the left component of the sequent unchanged.  The `(M)` rule does
change the left component, but it is a `Tableau.pdl` step and hence only applies to a basic
sequent, whose right component is then basic as well. -/

section RightRules

lemma LocalRuleApp.left_eq_of_isRightRule (lra : LocalRuleApp) (h : lra.isRightRule) :
    ∀ Y ∈ lra.C, Y.left = lra.X.left := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  subst hC
  cases lr
  case oneSidedR Rres orule YS_def =>
    intro Y hY
    exact oneSidedR_preserves_left (LRO := (L,R,O)) pre.2.1 orule YS_def Y hY
  case loadedR χ lrule YS_def =>
    intro Y hY
    refine loadedR_preserves_left (LRO := (L,R,O)) χ ?_ lrule YS_def Y hY
    exact (Option.some_subseteq.mp pre.2.2).symm
  all_goals
    simp [LocalRuleApp.isRightRule, LocalRule.isRightRule] at h

/-- The right component of a basic sequent is basic. -/
lemma Sequent.basic_rightOnly {X : Sequent} (h : X.basic) : X.rightOnly.basic := by
  rcases X with ⟨L, R, O⟩
  obtain ⟨hb, hc⟩ := h
  constructor
  · intro f hf
    apply hb
    simp only [Sequent.rightOnly, Sequent.toFinset, Finset.empty_union, Finset.mem_union] at hf ⊢
    tauto
  · intro hcl
    apply hc
    rcases hcl with hbot | ⟨f, hf, hnf⟩
    · left
      revert hbot
      simp_all [Sequent.rightOnly, Sequent.L, Sequent.R]
    · right
      refine ⟨f, ?_, ?_⟩ <;>
        simp_all [Sequent.rightOnly, Sequent.L, Sequent.R]

/-- Where a right rule is applied, it is either a local rule or the node is basic (because
the `(M)` rule is only applied at basic nodes). -/
lemma FinePathIn.lra_or_basic_of_usesRightRule : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'), f.usesRightRule →
      (∃ lra, f.lraOpt = some lra ∧ lra.isRightRule) ∨ f.label.basic
  | _, _, _, .inLoc lp hint, h => by
      simp only [FinePathIn.usesRightRule, FinePathIn.lraOpt] at h ⊢
      rcases hlt : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
      · rw [hlt] at h
        exact Or.inl ⟨lra, rfl, h⟩
      · rw [hlt] at h; simp at h
  | _, _, .pdl _ bas _ _, .pdlHere, _ => Or.inr bas
  | _, _, _, .lrepHere, h => by simp [FinePathIn.usesRightRule] at h
  | _, _, _, .loc Y_in tail, h => by
      simp only [FinePathIn.usesRightRule] at h
      simpa [FinePathIn.lraOpt, FinePathIn.label] using
        FinePathIn.lra_or_basic_of_usesRightRule tail h
  | _, _, _, .pdl tail, h => by
      simp only [FinePathIn.usesRightRule] at h
      simpa [FinePathIn.lraOpt, FinePathIn.label] using
        FinePathIn.lra_or_basic_of_usesRightRule tail h

/-- At a node where a right rule is applied to a non-basic right component, all children
have the same left component as the node itself. -/
lemma FinePathIn.children_left_eq_of_usesRightRule {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab') (hr : f.usesRightRule)
    (hb : ¬ f.label.rightOnly.basic) : ∀ g ∈ f.children, g.label.left = f.label.left := by
  rcases f.lra_or_basic_of_usesRightRule hr with ⟨lra, hlra, hright⟩ | hbas
  · obtain ⟨hX, hC⟩ := f.lraOpt_spec hlra
    intro g hg
    have hmem : g.label ∈ lra.C := by
      rw [← hC]; exact Finset.mem_image_of_mem FinePathIn.label hg
    rw [hX]
    exact lra.left_eq_of_isRightRule hright _ hmem
  · exact absurd (Sequent.basic_rightOnly hbas) hb

/-- A right local rule cannot be applied when the right component of the sequent is basic:
the rule only looks at the right component and at a loaded formula on the right, so it
would also be applicable to the sequent with an empty left component. -/
lemma LocalRuleApp.not_rightOnly_basic_of_isRightRule (lra : LocalRuleApp)
    (h : lra.isRightRule) : ¬ lra.X.rightOnly.basic := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr
  case oneSidedR ress orule YS_def =>
    have := nonbasic_of_localRuleApp
      ⟨∅, R, O, ∅, Rcond, none, _, LocalRule.oneSidedR orule YS_def, _, rfl,
        ⟨Finset.empty_subset _, pre.2.1, by simp⟩⟩
    simpa [Sequent.rightOnly] using this
  case loadedR χ lrule YS_def =>
    have := nonbasic_of_localRuleApp
      ⟨∅, R, O, ∅, ∅, some (Sum.inr (~'χ)), _, LocalRule.loadedR χ lrule YS_def, _, rfl,
        ⟨Finset.empty_subset _, Finset.empty_subset _, pre.2.2⟩⟩
    simpa [Sequent.rightOnly] using this
  all_goals
    simp [LocalRuleApp.isRightRule, LocalRule.isRightRule] at h

/-- The right component of the child obtained by applying the modal rule `(M)` to a sequent
whose loaded formula `~⌊·A⌋ξ` is on the right. Note that it only depends on `A`, on `ξ` and
on the right component `R` of the sequent, and hence only on `Λ₂` of the node. -/
def modRChildRightOnly (A : Nat) (ξ : AnyFormula) (R : Finset Formula) : Sequent :=
  match ξ with
  | .normal φ => ⟨∅, {~φ} ∪ Finset.pdlProjection A R, none⟩
  | .loaded χ => ⟨∅, Finset.pdlProjection A R, some (Sum.inr (~'χ))⟩

/-- At a fine node with a *basic* right component where a right rule is applied, that rule
is one of the three `PdlRule`s acting on the right — and in particular the node is a node
in the coarse sense. The three cases are `(L+)`, where the node is free, `(L-)`, whose
unique child is free, and the modal rule `(M)`, whose unique child has the projected left
component and a right component determined by `Λ₂` of the node. -/
lemma FinePathIn.basicRightStep {H : History} {Z : Sequent} {tab' : Tableau H Z}
    (f : FinePathIn tab') (h : f.usesRightRule) (hb : f.label.rightOnly.basic) :
      (f.atBigRoot ∧ f.label.2.2 = none)
      ∨ (∃ g, f.children = {g} ∧ g.atBigRoot ∧ g.label.2.2 = none)
      ∨ (∃ A ξ, f.label.2.2 = some (Sum.inr (~'⌊·A⌋ξ)) ∧ ∃ g, f.children = {g} ∧ g.atBigRoot
          ∧ g.label.left = Finset.pdlProjection A f.label.left
          ∧ g.label.rightOnly = modRChildRightOnly A ξ f.label.2.1) := by
  induction f with
  | @inLoc Hist X nrep nbas lt next lp hint =>
    simp only [FinePathIn.usesRightRule] at h
    rcases hlt : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
    · rw [hlt] at h
      simp only [FinePathIn.label] at hb
      rw [X_def] at hb
      exact absurd hb (lra.not_rightOnly_basic_of_isRightRule h)
    · rw [hlt] at h; simp at h
  | @pdlHere Hist X Y nrep bas r next =>
    simp only [FinePathIn.usesRightRule] at h
    simp only [FinePathIn.label, FinePathIn.children, FinePathIn.atBigRoot]
    cases r with
    | loadR hmem hnb hY => exact Or.inl ⟨trivial, rfl⟩
    | freeR hX hY =>
      exact Or.inr (Or.inl ⟨_, rfl, by simp [FinePathIn.atBigRoot],
        by simp [FinePathIn.label, hY]⟩)
    | @modR Y' L R A X' ξ hX hY =>
      subst hX
      right; right
      refine ⟨A, ξ, rfl, _, rfl, by simp [FinePathIn.atBigRoot], ?_, ?_⟩ <;>
        cases ξ <;> simp_all [modRChildRightOnly, Sequent.rightOnly, FinePathIn.label]
    | _ => simp [PdlRule.isRightRule] at h
  | lrepHere => simp [FinePathIn.usesRightRule] at h
  | loc Y_in tail IH =>
    simp only [FinePathIn.usesRightRule] at h
    simp only [FinePathIn.label] at hb ⊢
    simp only [FinePathIn.children, FinePathIn.atBigRoot]
    rcases IH h hb with ⟨hbr, h1⟩ | ⟨g, hg, hgbr, hg2⟩ | ⟨A, ξ, hA, g, hg, hgbr, hg1, hg2⟩
    · exact Or.inl ⟨hbr, h1⟩
    · exact Or.inr (Or.inl ⟨.loc Y_in g, by simp [hg], by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg2⟩)
    · exact Or.inr (Or.inr ⟨A, ξ, hA, .loc Y_in g, by simp [hg],
        by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg1, by simpa [FinePathIn.label] using hg2⟩)
  | pdl tail IH =>
    simp only [FinePathIn.usesRightRule] at h
    simp only [FinePathIn.label] at hb ⊢
    simp only [FinePathIn.children, FinePathIn.atBigRoot]
    rcases IH h hb with ⟨hbr, h1⟩ | ⟨g, hg, hgbr, hg2⟩ | ⟨A, ξ, hA, g, hg, hgbr, hg1, hg2⟩
    · exact Or.inl ⟨hbr, h1⟩
    · exact Or.inr (Or.inl ⟨.pdl g, by simp [hg], by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg2⟩)
    · exact Or.inr (Or.inr ⟨A, ξ, hA, .pdl g, by simp [hg],
        by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg1, by simpa [FinePathIn.label] using hg2⟩)

/-- A fine node that is a node in the coarse sense has the label of that coarse node. -/
lemma FinePathIn.label_eq_nodeAt_base {H Z} {tab' : Tableau H Z} (f : FinePathIn tab')
    (h : f.atBigRoot) : f.label = nodeAt f.base := by
  have := congrArg FinePathIn.label (f.eq_toFine_base_of_atBigRoot h)
  rwa [PathIn.label_toFine] at this

/-! ### Left rules do not change the right component

Dually, a left local rule leaves the right component of the sequent unchanged, provided the
loaded formula is on the right (otherwise the `(¬)` rule for the loaded formula on the left
would change the `Olf`). The left `PdlRule`s `(L+)`, `(L-)` and `(M)` are all only
applicable when the loaded formula is *not* on the right. -/

lemma LocalRuleApp.rightOnly_eq_of_isLeftRule (lra : LocalRuleApp) (h : lra.isLeftRule)
    (hR : lra.O.isRight) : ∀ Y ∈ lra.C, Y.rightOnly = lra.X.rightOnly := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  subst hC
  replace hR : O.isRight := hR
  cases lr
  case oneSidedL ress orule YS_def =>
    subst YS_def
    intro Y hY
    simp only [applyLocalRule, Finset.mem_image] at hY
    obtain ⟨res, hres, rfl⟩ := hY
    obtain ⟨Ln, -, rfl⟩ := hres
    simp [Sequent.rightOnly, Olf.change]
  case loadedL χ lrule YS_def =>
    exfalso
    have hO := (Option.some_subseteq.mp pre.2.2).symm
    rw [hO] at hR
    simp at hR
  all_goals
    simp [LocalRuleApp.isLeftRule, LocalRule.isLeftRule] at h

/-- Where a left rule is applied, it is a local rule, unless the loaded formula is not on
the right (which for a node of a `LoadedCluster` cannot happen). -/
lemma FinePathIn.leftRuleStep {H : History} {Z : Sequent} {tab' : Tableau H Z}
    (f : FinePathIn tab') (h : f.usesLeftRule) :
    (∃ lra, f.lraOpt = some lra ∧ lra.isLeftRule) ∨ (f.atBigRoot ∧ ¬ f.label.2.2.isRight) := by
  induction f with
  | @inLoc Hist X nrep nbas lt next lp hint =>
    simp only [FinePathIn.usesLeftRule] at h
    rcases hlt : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
    · rw [hlt] at h
      exact Or.inl ⟨lra, by simp only [FinePathIn.lraOpt, hlt], h⟩
    · rw [hlt] at h; simp at h
  | @pdlHere Hist X Y nrep bas r next =>
    simp only [FinePathIn.usesLeftRule] at h
    right
    refine ⟨by simp [FinePathIn.atBigRoot], ?_⟩
    simp only [FinePathIn.label]
    cases r with
    | loadL hmem hnb hY => simp
    | freeL hX hY => subst hX; simp
    | modL hX hY => subst hX; simp
    | _ => simp [PdlRule.isLeftRule] at h
  | lrepHere => simp [FinePathIn.usesLeftRule] at h
  | loc Y_in tail IH =>
    simp only [FinePathIn.usesLeftRule] at h
    rcases IH h with ⟨lra, h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨lra, by simpa [FinePathIn.lraOpt] using h1, h2⟩
    · exact Or.inr ⟨by simpa [FinePathIn.atBigRoot] using h1, by simpa [FinePathIn.label] using h2⟩
  | pdl tail IH =>
    simp only [FinePathIn.usesLeftRule] at h
    rcases IH h with ⟨lra, h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨lra, by simpa [FinePathIn.lraOpt] using h1, h2⟩
    · exact Or.inr ⟨by simpa [FinePathIn.atBigRoot] using h1, by simpa [FinePathIn.label] using h2⟩

/-- Part of Lemma 9.7 (c): at a node with the loaded formula on the right where a left rule
is applied, all children have the same right component as the node itself. -/
lemma FinePathIn.children_rightOnly_eq_of_usesLeftRule {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab') (h : f.usesLeftRule) (hR : f.label.2.2.isRight) :
    ∀ g ∈ f.children, g.label.rightOnly = f.label.rightOnly := by
  rcases f.leftRuleStep h with ⟨lra, hlra, hleft⟩ | ⟨-, hno⟩
  · obtain ⟨hX, hC⟩ := f.lraOpt_spec hlra
    rw [hX] at hR
    intro g hg
    have hmem : g.label ∈ lra.C := by
      rw [← hC]; exact Finset.mem_image_of_mem FinePathIn.label hg
    rw [hX]
    exact lra.rightOnly_eq_of_isLeftRule hleft hR _ hmem
  · exact absurd hR hno

/-- Local invertibility of a left rule, for the left component only: if the left component
of the premise holds at a world, then so does the left component of one of the conclusions.

Note that `localRuleTruth` does not give this, since it also speaks about the right
component, which need not hold at the world in question. That the loaded formula is on the
right is needed to exclude the rule for a loaded formula on the left. -/
lemma LocalRuleApp.left_sat_of_isLeftRule {lra : LocalRuleApp} (hl : lra.isLeftRule)
    (hR : lra.O.isRight) {W : Type} {M : KripkeModel W} {w : W}
    (hw : ∀ φ ∈ lra.X.left, evaluate M w φ) :
    ∃ Y ∈ lra.C, ∀ φ ∈ Y.left, evaluate M w φ := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  simp only [LocalRuleApp.X, Sequent.left_eq] at hw hl hR ⊢
  cases lr
  case oneSidedL ress' orule YS_def =>
    subst YS_def
    subst hC
    have hcon : evaluate M w (con Lcond.pdlSort) :=
      conEval.mpr (fun f hf =>
        hw f (Finset.mem_union_left _ (pre.1 (Formula.mem_pdlSort.mp hf))))
    have hdis := (oneSidedLocalRuleTruth orule W M w).mp hcon
    rw [Finset.disconEval] at hdis
    obtain ⟨res, hres, hresw⟩ := hdis
    refine ⟨(L \ Lcond ∪ res, R \ ∅ ∪ ∅, Olf.change O none none), ?_, ?_⟩
    · simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply]
      exact ⟨res, hres, rfl⟩
    · intro f hf
      simp only [Sequent.left_eq, Finset.mem_union, Olf.change_old_none_none] at hf
      rcases hf with (hf | hf) | hf
      · exact hw f (Finset.mem_union_left _ (Finset.sdiff_subset hf))
      · exact hresw f hf
      · exact hw f (Finset.mem_union_right _ hf)
  case loadedL χ lrule YS_def =>
    exfalso
    have hO := (Option.some_subseteq.mp pre.2.2).symm
    rw [hO] at hR
    simp at hR
  all_goals
    simp [LocalRuleApp.isLeftRule, LocalRule.isLeftRule] at hl

/-- Local invertibility at a fine node where a left rule is applied, for the left component
only: if a formula follows from the left component of every child, then it follows from the
left component of the node itself. -/
lemma FinePathIn.leftEntails_of_children_of_usesLeftRule {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab') (h : f.usesLeftRule)
    (hR : f.label.2.2.isRight) {φ : Formula}
    (hch : ∀ g ∈ f.children, g.leftEntails φ) : f.leftEntails φ := by
  rcases f.leftRuleStep h with ⟨lra, hlra, hleft⟩ | ⟨-, hno⟩
  · obtain ⟨hX, hC⟩ := f.lraOpt_spec hlra
    intro W M w hw
    rw [hX] at hR hw
    obtain ⟨Y, hY, hYw⟩ := lra.left_sat_of_isLeftRule hleft hR hw
    have hmem : Y ∈ f.children.image FinePathIn.label := by
      rw [hC]; exact hY
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hmem
    exact hch g hg W M w hYw
  · exact absurd hR hno

end RightRules

/-! ### Loading on the right is inherited upwards, and rules with children are left or right

Two ingredients for the descent of Lemma 9.7 (d) below. First, a fine node that has a
coarse child loaded on the right is itself loaded on the right — this is what lets us apply
`FinePathIn.children_rightOnly_eq_of_usesLeftRule` at the fine nodes of a cluster. Second,
a fine node with children applies a left or a right rule: the only local rules that are
neither are the closing rules, and those have no children. -/

section UpwardsRight

/-- If a child of a local rule application is loaded on the right, then so is its premise.
The local rules for a loaded formula on the *left* never produce a loading on the right,
and the one-sided rules do not change the loaded formula at all. -/
lemma LocalRuleApp.isRight_of_mem_C (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, Y.2.2.isRight → lra.X.2.2.isRight := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  subst hC
  intro Y hY hYR
  cases lr
  case oneSidedL ress orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, Finset.mem_image] at hY
    obtain ⟨res, hres, rfl⟩ := hY
    obtain ⟨Ln, -, rfl⟩ := hres
    simpa [Olf.change] using hYR
  case oneSidedR ress orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, Finset.mem_image] at hY
    obtain ⟨res, hres, rfl⟩ := hY
    obtain ⟨Rn, -, rfl⟩ := hres
    simpa [Olf.change] using hYR
  case LRnegL => simp [applyLocalRule] at hY
  case LRnegR => simp [applyLocalRule] at hY
  case loadedL χ lrule YS_def =>
    exfalso
    subst YS_def
    have hO := (Option.some_subseteq.mp pre.2.2).symm
    subst hO
    simp only [applyLocalRule, Finset.mem_image] at hY
    obtain ⟨res, hres, rfl⟩ := hY
    obtain ⟨⟨Lnew, Onew⟩, -, rfl⟩ := hres
    rcases Onew with _ | o <;> simp_all [Olf.isRight, Olf.change]
  case loadedR χ lrule YS_def =>
    have hO := (Option.some_subseteq.mp pre.2.2).symm
    subst hO
    simp [Olf.isRight]

/-- If some end node of a local tableau is loaded on the right, then so is its root. -/
lemma LocalTableau.isRight_of_mem_endNodesOf : ∀ {Z : Sequent} (lt : LocalTableau Z),
    ∀ Y ∈ endNodesOf lt, Y.2.2.isRight → Z.2.2.isRight
  | _, .sim _, Y, hY, hYR => by
      rw [mem_endNodesOf_sim] at hY
      exact hY ▸ hYR
  | _, .byLocalRule lra X_def next, Y, hY, hYR => by
      subst X_def
      obtain ⟨W, W_in, hY⟩ := mem_endNodesOf_byLocalRule_iff.mp hY
      exact lra.isRight_of_mem_C W W_in
        (LocalTableau.isRight_of_mem_endNodesOf (next W W_in) Y hY hYR)

/-- The end nodes below a local path are end nodes of the local tableau at that path. -/
lemma LocalPathIn.mem_endNodesOf_ltAt {Z : Sequent} {lt : LocalTableau Z}
    (lp : LocalPathIn lt) :
    ∀ Yh ∈ lp.endNodesBelow, (Yh : Sequent) ∈ endNodesOf lp.ltAt := by
  induction lp with
  | nil => intro Yh _; exact Yh.2
  | cons Y_in tail IH =>
    intro Yh h
    simp only [LocalPathIn.endNodesBelow, List.mem_map, Subtype.exists] at h
    obtain ⟨Z, hZ, hmem, rfl⟩ := h
    exact IH ⟨Z, hZ⟩ hmem

/-- A fine node that is not a coarse node and has a coarse child loaded on the right is
itself loaded on the right. (For coarse nodes this is false: the `(L+)` rule loads a free
node.) -/
lemma FinePathIn.isRight_of_mem_coarseChildrenBelow : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'), ¬ f.atBigRoot →
      ∀ q ∈ f.coarseChildrenBelow, (nodeAt q).2.2.isRight → f.label.2.2.isRight
  | _, _, _, .inLoc lp _, _, q, hq, hqR => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map, Subtype.exists] at hq
      obtain ⟨Y, Y_in, hmem, rfl⟩ := hq
      rw [nodeAt_loc_nil] at hqR
      exact LocalTableau.isRight_of_mem_endNodesOf lp.ltAt Y
        (lp.mem_endNodesOf_ltAt ⟨Y, Y_in⟩ hmem) hqR
  | _, _, _, .pdlHere, hbr, _, _, _ => absurd (by simp [FinePathIn.atBigRoot]) hbr
  | _, _, _, .lrepHere, hbr, _, _, _ => absurd (by simp [FinePathIn.atBigRoot]) hbr
  | _, _, _, .loc Y_in tail, hbr, q, hq, hqR => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      rw [nodeAt_loc] at hqR
      exact tail.isRight_of_mem_coarseChildrenBelow
        (by simpa [FinePathIn.atBigRoot] using hbr) q' hq' hqR
  | _, _, _, .pdl tail, hbr, q, hq, hqR => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      rw [nodeAt_pdl] at hqR
      exact tail.isRight_of_mem_coarseChildrenBelow
        (by simpa [FinePathIn.atBigRoot] using hbr) q' hq' hqR

/-- A local rule application with at least one child is a left or a right rule: only the
closing rules `(¬)` are neither, and they have no results. -/
lemma LocalRuleApp.isLeftRule_or_isRightRule_of_C_ne_empty (lra : LocalRuleApp)
    (h : lra.C ≠ ∅) : lra.isLeftRule ∨ lra.isRightRule := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  subst hC
  cases lr
  case LRnegL => simp [applyLocalRule] at h
  case LRnegR => simp [applyLocalRule] at h
  all_goals
    simp [LocalRuleApp.isLeftRule, LocalRuleApp.isRightRule, LocalRule.isLeftRule,
      LocalRule.isRightRule]

/-- A fine node that has children applies a left or a right rule. -/
lemma FinePathIn.usesLeftRule_or_usesRightRule_of_children_ne_empty {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab') (h : f.children ≠ ∅) :
    f.usesLeftRule ∨ f.usesRightRule := by
  induction f with
  | @inLoc Hist Y nrep nbas lt next lp lp_int =>
    have hlp : lp.children ≠ ∅ := by
      intro hnil
      exact h (by simp [FinePathIn.children, hnil])
    have hlab : lp.ltAt.childLabels ≠ ∅ := by
      rw [← lp.map_last_children]
      simpa using hlp
    simp only [FinePathIn.usesLeftRule, FinePathIn.usesRightRule]
    rcases hlt : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
    · rw [hlt] at hlab
      exact lra.isLeftRule_or_isRightRule_of_C_ne_empty
        (by simpa [LocalTableau.childLabels] using hlab)
    · exfalso
      unfold LocalPathIn.isInternal at lp_int
      rw [hlt] at lp_int
      simp [LocalTableau.hasRule] at lp_int
  | @pdlHere _ _ _ _ _ r _ =>
    simp only [FinePathIn.usesLeftRule, FinePathIn.usesRightRule]
    cases r <;> simp [PdlRule.isLeftRule, PdlRule.isRightRule]
  | lrepHere => simp [FinePathIn.children] at h
  | loc Y_in tail IH =>
    simp only [FinePathIn.usesLeftRule, FinePathIn.usesRightRule]
    exact IH (by intro hnil; exact h (by simp [FinePathIn.children, hnil]))
  | pdl tail IH =>
    simp only [FinePathIn.usesLeftRule, FinePathIn.usesRightRule]
    exact IH (by intro hnil; exact h (by simp [FinePathIn.children, hnil]))

end UpwardsRight

/-! ### Loaded-path repeats and the Dershowitz-Manna measure

The three lemmas here are what replaces the paper's Fact `lprAreCritical` in the proof of
Lemma 9.7 (d) below: instead of showing that the modal rule is applied between a companion
and its repeat we show that going down along *left* rules strictly decreases the
Dershowitz-Manna measure of the label, while a companion carries exactly the same label as
its repeat. -/

section LrepAndMeasure

/-- A node where a rule is applied is not a loaded-path repeat.
This would better belong next to `edge` in `Pdl/TableauPath.lean`. -/
lemma PathIn.not_isLrep_of_edge {s t : PathIn tab} (h : s ⋖_ t) : ¬ s.isLrep := by
  unfold PathIn.isLrep
  rcases h with ⟨_, _, _, _, _, _, _, _, hs, -⟩ | ⟨_, _, _, _, _, _, _, hs, -⟩ <;>
    rw [hs] <;> simp [Tableau.isLrep]

/-- A fine node whose base is a loaded-path repeat is that coarse node itself, because a
loaded-path repeat is a leaf and hence has no local tableau with internal nodes.
This would better belong next to `atBigRoot` in `Pdl/Interpolation/FinePath.lean`. -/
lemma FinePathIn.atBigRoot_of_base_isLrep {H Z} {tab' : Tableau H Z} (f : FinePathIn tab')
    (h : f.base.isLrep) : f.atBigRoot := by
  induction f with
  | inLoc lp lp_int => simp [FinePathIn.base, PathIn.isLrep, tabAt, Tableau.isLrep] at h
  | pdlHere => simp [FinePathIn.base, PathIn.isLrep, tabAt, Tableau.isLrep] at h
  | lrepHere => simp [FinePathIn.atBigRoot]
  | loc Y_in tail IH =>
    simpa [FinePathIn.atBigRoot] using IH (by simpa [FinePathIn.base, PathIn.isLrep, tabAt] using h)
  | pdl tail IH =>
    simpa [FinePathIn.atBigRoot] using IH (by simpa [FinePathIn.base, PathIn.isLrep, tabAt] using h)

/-- Where a left rule is applied at a node with the loaded formula on the right, the labels
of all children are strictly smaller in the Dershowitz-Manna ordering: by
`FinePathIn.leftRuleStep` the rule applied there is a local rule, and local rules decrease
the measure. -/
lemma FinePathIn.children_lt_Sequent_of_usesLeftRule {H Z} {tab' : Tableau H Z}
    (f : FinePathIn tab') (h : f.usesLeftRule) (hR : f.label.2.2.isRight) :
    ∀ g ∈ f.children, ltSequent g.label f.label := by
  rcases f.leftRuleStep h with ⟨lra, hlra, -⟩ | ⟨-, hno⟩
  · obtain ⟨hX, hC⟩ := f.lraOpt_spec hlra
    intro g hg
    have hmem : g.label ∈ lra.C := by
      rw [← hC]; exact Finset.mem_image_of_mem FinePathIn.label hg
    rw [hX]
    exact localRuleApp.decreases_DM lra _ hmem
  · exact absurd hR hno

end LrepAndMeasure

/-! ### The two standing assumptions of the paper

The paper fixes a *uniform* closed tableau and a *proper* cluster in it, and both assumptions
are used in Section 9.  Neither of them holds for an arbitrary values of the `Tableau` type.

* the `Tableau` type does not force any coherence between the rules applied at different
  nodes, whereas uniformity (U1/U2) makes the rule applied at a node with a loaded,
  non-basic right component depend only on that component.

This is captured in the form needed here in `LoadedCluster.HasUniformSteps`.

Note that this file never *unfolds* `LoadedCluster.HasUniformSteps`: it is only used
opaquely, as the hypothesis of `LoadedCluster.stepOf_spec` and as the conclusion of
`LoadedCluster.uniformOfUniTab`.  So the definition of `HasUniformSteps` may still be
changed (for example from a `List` comparison to a `Finset.image` one) without affecting
anything here, as long as those two statements are kept.
-/

namespace LoadedCluster

/-! ### The vocabulary fields -/

/-- Every fine node of `C⁺` is `◃`-reachable from the root of the cluster. -/
lemma root_cReach_base_of_mem_fineCLplus (C : LoadedCluster tab) {f : FinePathIn tab}
    (hf : f ∈ C.fineCLplus) : C.root ◃* f.base := by
  rcases Finset.mem_union.mp hf with hf | hf
  · exact C.root_reaches_all _ ((C.mem_fineCL f).mp (List.mem_toFinset.mp hf)).1
  · simp only [fineExits, Finset.mem_filter, Finset.mem_sup, List.mem_toFinset] at hf
    obtain ⟨⟨g, hg, hfg⟩, -⟩ := hf
    have hgr : C.root ◃* g.base := C.root_reaches_all _ ((C.mem_fineCL g).mp hg).1
    rcases g.base_of_mem_children f hfg with h | h
    · exact h ▸ hgr
    · exact hgr.tail (Or.inl h)

/-- The `vocL` field of `PaperFacts`: the vocabulary of the left component only shrinks
below the root of the cluster. -/
lemma vocL_fineCLplus (C : LoadedCluster tab) :
    ∀ f ∈ C.fineCLplus, f.label.left.pdlFvoc ⊆ (nodeAt C.root).left.pdlFvoc := fun f hf =>
  subset_trans (FinePathIn.label_left_fvoc_subset_base f)
    (cReach_left_fvoc_subset (C.root_cReach_base_of_mem_fineCLplus hf))

/-- The `vocR` field of `PaperFacts`: the vocabulary of the right component only shrinks
below the root of the cluster. -/
lemma vocR_fineCLplus (C : LoadedCluster tab) :
    ∀ f ∈ C.fineCLplus, f.label.right.pdlFvoc ⊆ (nodeAt C.root).right.pdlFvoc := fun f hf =>
  subset_trans (FinePathIn.label_right_fvoc_subset_base f)
    (cReach_right_fvoc_subset (C.root_cReach_base_of_mem_fineCLplus hf))

/-! ### The remaining fields -/

/-- Lemma 9.7 (e): at a node `t` of `C^R_Δ` with `Δ` basic the rule applied is the modal
rule `(M)` for the loaded formula `~⌊·A⌋ξ` of `Δ`. Its unique child `u` satisfies
`Λ₁(u) = (Λ₁(t))_A`, and its right component only depends on `Δ`.

Properness is needed to exclude the two other right `PdlRule`s: `(L+)` is only applied at
a free node, while `(L-)` makes its unique child free, and both contradict Lemma 9.4 (a)
because by Lemma 9.4 (c) some child of `t` is again in the cluster. -/
lemma basicModalStepAt (C : LoadedCluster tab) {Δ : Sequent}
    (hb : Δ.basic) {t : FinePathIn tab} (ht : t ∈ C.nodesWithFineRight Δ) :
    ∃ A ξ, Δ.2.2 = some (Sum.inr (~'⌊·A⌋ξ)) ∧ ∃ g, t.children = {g} ∧ g.atBigRoot
      ∧ g.label.left = Finset.pdlProjection A t.label.left
      ∧ g.label.rightOnly = modRChildRightOnly A ξ Δ.2.1 := by
  simp only [nodesWithFineRight, nodesWithFine, List.mem_filter, decide_eq_true_eq] at ht
  obtain ⟨⟨ht_CL, ht_lab⟩, ht_right⟩ := ht
  have hmf : C.memFine t := (C.mem_fineCL t).mp ht_CL
  have hDl : Δ.2.2 = t.label.2.2 := by rw [← ht_lab]; rfl
  have hDr : Δ.2.1 = t.label.2.1 := by rw [← ht_lab]; rfl
  obtain ⟨c, hc, hcmf⟩ := C.exists_child_memFine_of_not_isLrep hmf
    (t.not_isLrep_base_of_usesRightRule ht_right)
  rcases t.basicRightStep ht_right (ht_lab ▸ hb) with
    ⟨hbr, hnone⟩ | ⟨g, hg, hgbr, hgnone⟩ | ⟨A, ξ, hA, g, hg, hgbr, hg1, hg2⟩
  · exfalso
    have hrl := C.all_right_loaded t.base hmf.1
    rw [← t.label_eq_nodeAt_base hbr, hnone] at hrl
    simp at hrl
  · exfalso
    rw [hg, Finset.mem_singleton] at hc
    subst hc
    have hrl := C.all_right_loaded c.base hcmf.1
    rw [← c.label_eq_nodeAt_base hgbr, hgnone] at hrl
    simp at hrl
  · exact ⟨A, ξ, by rw [hDl]; exact hA, g, hg, hgbr, hg1, by rw [hDr]; exact hg2⟩

/-- Every element of `stepOf Δ` is the right component of a child of some node of `C^R_Δ`,
namely of the first one. -/
lemma exists_child_rightOnly_of_mem_stepOf (C : LoadedCluster tab) {Δ Pi : Sequent}
    (hPi : Pi ∈ C.stepOf Δ) :
    ∃ f ∈ C.nodesWithFineRight Δ, ∃ g ∈ f.children, g.label.rightOnly = Pi := by
  unfold stepOf at hPi
  cases hh : (C.nodesWithFineRight Δ).head? with
  | none => rw [hh] at hPi; simp at hPi
  | some f =>
    rw [hh] at hPi
    simp only [Finset.mem_image] at hPi
    obtain ⟨g, hg, rfl⟩ := hPi
    exact ⟨f, List.mem_of_mem_head? hh, g, hg, rfl⟩

/-! ### The descent for Lemma 9.7 (d)

The paper picks a node `t ∈ C_Δ` that is minimal in the tree order and then follows
left-rule children downwards; by `FinePathIn.children_rightOnly_eq_of_usesLeftRule` this
stays inside `C_Δ`, and closing rules are excluded because they have no children while
Lemma 9.4 (c) (`nonLpr_some_child_in_C`, which needs properness) provides one.

The descent itself is `FinePathIn.descent` from `Pdl.FinePathDescent`: fine children are not
structurally smaller, so the recursion is justified by the well-foundedness of the flipped
fine child relation. -/

/-- Every fine node of the cluster is loaded on the right, i.e. Lemma 9.4 (a) at the fine
level. For nodes that are coarse nodes this is `all_right_loaded`; for the intermediate
nodes of a local tableau it follows because a coarse child of theirs is in the cluster and
loading on the right is inherited upwards inside a local tableau. -/
lemma memFine_label_isRight (C : LoadedCluster tab) {f : FinePathIn tab} (hf : C.memFine f) :
    f.label.2.2.isRight := by
  by_cases hbr : f.atBigRoot
  · rw [f.label_eq_nodeAt_base hbr]
    exact C.all_right_loaded _ hf.1
  · obtain ⟨q, hq, hqC⟩ := hf.2.resolve_left hbr
    exact f.isRight_of_mem_coarseChildrenBelow hbr q hq (C.all_right_loaded q hqC)

/-- Every label in `Λ₂[C]` is loaded on the right. -/
lemma isRight_of_mem_lambdaTwo (C : LoadedCluster tab) {Δ : Sequent} (hΔ : Δ ∈ C.lambdaTwo) :
    Δ.2.2.isRight := by
  simp only [lambdaTwo, Finset.mem_image, List.mem_toFinset] at hΔ
  obtain ⟨f, hf, rfl⟩ := hΔ
  exact C.memFine_label_isRight ((C.mem_fineCL f).mp hf)

/-- The descent of Lemma 9.7 (d): if `C_Δ` is non-empty then either `C^R_Δ` is non-empty,
or `C_Δ` contains a loaded-path repeat.

Starting from any node of `C_Δ` we follow children: as long as no right rule is applied and
no repeat is reached, the node has a child in the cluster (Lemma 9.4 (c), which needs
properness) with the same right component (Lemma 9.7 (c)), and the descent terminates by
`FinePathIn.descent` — but a childless node of the cluster which is not a repeat would
contradict Lemma 9.4 (c).

This is the paper's descent. It is no longer needed for Lemma 9.7 (d) below, which is now
proved via `isLrep_of_mem_nodesWithFine`, but it is kept as the direct formalisation of the
argument in the paper. -/
lemma exists_right_or_lrep (C : LoadedCluster tab) {Δ : Sequent}
    (hΔ : Δ ∈ C.lambdaTwo) :
    C.nodesWithFineRight Δ ≠ [] ∨ ∃ f ∈ C.nodesWithFine Δ, f.base.isLrep := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hR, hlrep⟩ := hcon
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ ((C.mem_lambdaTwo_iff Δ).mp hΔ)
  have hΔR : Δ.2.2.isRight := C.isRight_of_mem_lambdaTwo hΔ
  have down : ∀ u : FinePathIn tab, u ∈ C.nodesWithFine Δ → u.children ≠ ∅ →
      ∃ g ∈ u.children, g ∈ C.nodesWithFine Δ := by
    intro u hu hne
    have hu' := hu
    simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq] at hu'
    obtain ⟨hu_CL, hu_lab⟩ := hu'
    obtain ⟨g, hg, hgmf⟩ := C.exists_child_memFine_of_not_isLrep ((C.mem_fineCL u).mp hu_CL)
      (hlrep u hu)
    refine ⟨g, hg, ?_⟩
    have huleft : u.usesLeftRule := by
      rcases u.usesLeftRule_or_usesRightRule_of_children_ne_empty hne with h | h
      · exact h
      · exfalso
        have hmem : u ∈ C.nodesWithFineRight Δ := by
          simp only [nodesWithFineRight, List.mem_filter]
          exact ⟨hu, h⟩
        rw [hR] at hmem
        simp at hmem
    have huR : u.label.2.2.isRight := by rw [show u.label.2.2 = Δ.2.2 by rw [← hu_lab]; rfl]
                                         exact hΔR
    have hgl : g.label.rightOnly = u.label.rightOnly :=
      u.children_rightOnly_eq_of_usesLeftRule huleft huR g hg
    simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq]
    exact ⟨(C.mem_fineCL g).mpr hgmf, by rw [hgl, hu_lab]⟩
  obtain ⟨v, hv, hvnil⟩ := FinePathIn.descent down t ht
  have hv_CL : v ∈ C.fineCL := by
    simp only [nodesWithFine, List.mem_filter] at hv
    exact hv.1
  obtain ⟨g, hg, -⟩ :=
    C.exists_child_memFine_of_not_isLrep ((C.mem_fineCL v).mp hv_CL) (hlrep v hv)
  rw [hvnil] at hg
  simp at hg

/-- If a node of `C_Δ` is a loaded-path repeat then its companion is again a node of `C_Δ`,
it carries the same label, and it is *not* a loaded-path repeat itself.

That the companion is in the cluster is Lemma 9.4 (c) (`lpr_comp_in_C`); that it carries
the same label is `nodeAt_companionOf_setEq` — note that with `Finset` sequents this is
literal equality; and it is not a repeat because it is a proper ancestor of the repeat,
while a repeat is a leaf. -/
lemma exists_companion_mem_nodesWithFine (C : LoadedCluster tab) {Δ : Sequent}
    {f : FinePathIn tab} (hf : f ∈ C.nodesWithFine Δ) (hl : f.base.isLrep) :
    ∃ c : PathIn tab, c.toFine ∈ C.nodesWithFine Δ ∧ ¬ c.isLrep ∧ nodeAt c = f.label := by
  have hf' := hf
  simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq] at hf'
  obtain ⟨hf_CL, hf_lab⟩ := hf'
  have hmf : C.memFine f := (C.mem_fineCL f).mp hf_CL
  have hbase : f.label = nodeAt f.base :=
    f.label_eq_nodeAt_base (f.atBigRoot_of_base_isLrep hl)
  rcases h2 : (tabAt f.base).2.2 with _ | _ | lpr
  case lrep =>
    have heart : f.base ♥ (companionOf f.base lpr h2) := ⟨lpr, h2, rfl⟩
    have hc_CL : companionOf f.base lpr h2 ∈ C.CL := C.lpr_comp_in_C f.base hmf.1 heart
    have hc_node : nodeAt (companionOf f.base lpr h2) = f.label := by
      rw [nodeAt_companionOf_setEq f.base lpr h2, hbase]
    refine ⟨companionOf f.base lpr h2, ?_, ?_, hc_node⟩
    · simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq]
      refine ⟨(C.mem_fineCL _).mpr (C.memFine_toFine hc_CL), ?_⟩
      rw [PathIn.label_toFine, hc_node, hf_lab]
    · obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.mp (companion_lt heart)
      exact PathIn.not_isLrep_of_edge hb
  all_goals
    exfalso
    unfold PathIn.isLrep at hl
    rw [h2] at hl
    simp [Tableau.isLrep] at hl

/-- Every node of `C_Δ` is a loaded-path repeat, provided `C^R_Δ` is empty.

This is the key step for Lemma 9.7 (d). The proof is by well-founded induction on the label
along the Dershowitz-Manna ordering `ltSequent`: at a node of `C_Δ` that is not a repeat a
left rule is applied — a right rule is excluded by the assumption — so by Lemma 9.4 (c)
there is a child in the cluster, its right component is still `Δ` by Lemma 9.7 (c) and its
label is strictly smaller. Applying the induction hypothesis to that child makes it a
repeat, and then its companion is again in `C_Δ` with the *same*, hence still smaller,
label, but is not a repeat — contradicting the induction hypothesis. -/
lemma isLrep_of_mem_nodesWithFine (C : LoadedCluster tab) {Δ : Sequent}
    (hR : C.nodesWithFineRight Δ = []) : ∀ f ∈ C.nodesWithFine Δ, f.base.isLrep := by
  have key : ∀ Y : Sequent, ∀ f ∈ C.nodesWithFine Δ, f.label = Y → f.base.isLrep := by
    intro Y
    induction Y using WellFounded.induction instIsWellFoundedSequentLt with
    | _ Y IH =>
      intro f hf hlab
      by_contra hnl
      have hf' := hf
      simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq] at hf'
      obtain ⟨hf_CL, hf_lab⟩ := hf'
      have hmf : C.memFine f := (C.mem_fineCL f).mp hf_CL
      obtain ⟨g, hg, hgmf⟩ := C.exists_child_memFine_of_not_isLrep hmf hnl
      have hne : f.children ≠ ∅ := by
        intro hnil
        rw [hnil] at hg
        simp at hg
      have hleft : f.usesLeftRule := by
        rcases f.usesLeftRule_or_usesRightRule_of_children_ne_empty hne with h | h
        · exact h
        · exfalso
          have hmem : f ∈ C.nodesWithFineRight Δ := by
            simp only [nodesWithFineRight, List.mem_filter]
            exact ⟨hf, h⟩
          rw [hR] at hmem
          simp at hmem
      have hfR : f.label.2.2.isRight := C.memFine_label_isRight hmf
      have hgmem : g ∈ C.nodesWithFine Δ := by
        simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq]
        refine ⟨(C.mem_fineCL g).mpr hgmf, ?_⟩
        rw [f.children_rightOnly_eq_of_usesLeftRule hleft hfR g hg, hf_lab]
      have hglt : ltSequent g.label Y :=
        hlab ▸ f.children_lt_Sequent_of_usesLeftRule hleft hfR g hg
      have hglrep : g.base.isLrep := IH g.label hglt g hgmem rfl
      obtain ⟨c, hc_mem, hc_nl, hc_lab⟩ := C.exists_companion_mem_nodesWithFine hgmem hglrep
      exact hc_nl (by simpa using IH g.label hglt c.toFine hc_mem (by simp [hc_lab]))
  intro f hf
  exact key f.label f hf rfl

/-- Lemma 9.7 (d): if `C_Δ` is non-empty then so is `C^R_Δ`.

Where the paper uses its Fact `lprAreCritical` — on the path from a companion to its repeat
the modal rule is applied at least once — we argue with the Dershowitz-Manna measure
instead: if `C^R_Δ` were empty then by `isLrep_of_mem_nodesWithFine` all nodes of `C_Δ`
would be loaded-path repeats, but the companion of such a repeat is again in `C_Δ` and is
not a repeat. (Since `Sequent` now uses `Finset`s, a repeat carries exactly the same label
as its companion, cf. `nodeAt_companionOf_setEq`.) -/
lemma exists_right_of_proper (C : LoadedCluster tab) :
    ∀ Δ ∈ C.lambdaTwo, C.nodesWithFineRight Δ ≠ [] := by
  intro Δ hΔ hnil
  obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ ((C.mem_lambdaTwo_iff Δ).mp hΔ)
  obtain ⟨c, hc_mem, hc_nl, -⟩ :=
    C.exists_companion_mem_nodesWithFine hf (C.isLrep_of_mem_nodesWithFine hnil f hf)
  exact hc_nl (by simpa using C.isLrep_of_mem_nodesWithFine hnil _ hc_mem)

/-- The leading atomic program of a basic label of `Λ₂[C]` is in the joint vocabulary.

That it is in the vocabulary of `Γ₂` is vocabulary preservation. That it is in the
vocabulary of `Γ₁` — which the paper does not mention, but which its Lemma 10.1 needs —
uses Lemma 9.7 (e): the modal rule is applied at some `t ∈ C^R_Δ` and its child `u` is
again in `C`, so `Λ₁(u) = (Λ₁(t))_a` is non-empty by Lemma 9.5 (b), which forces a box
`⌈a⌉ψ` in `Λ₁(t)`.

The hypothesis `hER` is Lemma 9.7 (d), i.e. `exists_right_of_proper`. -/
lemma loadedProgVoc_of_proper (C : LoadedCluster tab)
    (hER : ∀ Δ ∈ C.lambdaTwo, C.nodesWithFineRight Δ ≠ []) :
    (nodeAt C.root).left ≠ {} → ∀ Δ ∈ C.lambdaTwo, Δ.basic →
      (Δ.loadedProg).voc ⊆ jvoc (nodeAt C.root) := by
  intro hG1 Δ hΔ hb
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ (hER Δ hΔ)
  obtain ⟨A, xi, hAxi, g, hg, hgbr, hgleft, -⟩ := C.basicModalStepAt hb ht
  have ht' := ht
  simp only [nodesWithFineRight, nodesWithFine, List.mem_filter, decide_eq_true_eq] at ht'
  obtain ⟨⟨ht_CL, ht_lab⟩, ht_right⟩ := ht'
  have hmf : C.memFine t := (C.mem_fineCL t).mp ht_CL
  obtain ⟨c, hc, hcmf⟩ := C.exists_child_memFine_of_not_isLrep hmf
    (t.not_isLrep_base_of_usesRightRule ht_right)
  rw [hg, Finset.mem_singleton] at hc
  have hgmf : C.memFine g := hc ▸ hcmf
  -- The left component of the root is non-empty, hence so is that of every node of `C`.
  have hroot1 : (nodeAt C.root).1 ≠ ∅ := by
    intro h
    apply hG1
    have hrr := C.root_loaded_right
    rcases hh : nodeAt C.root with ⟨L, R, O⟩
    rw [hh] at h hrr
    rcases O with _ | (o | o) <;> simp_all [Sequent.left]
  have hg1 : (nodeAt g.base).1 ≠ ∅ := fun h =>
    hroot1 ((C.left_empty_iff_root_left_empty g.base hgmf.1).mp h)
  have hgne : g.label.left ≠ ∅ := by
    rw [g.label_eq_nodeAt_base hgbr]
    intro h
    rcases hh : nodeAt g.base with ⟨L, R, O⟩
    rw [hh] at h hg1
    simp only [Sequent.left_eq, Finset.union_eq_empty] at h
    exact hg1 h.1
  -- Hence there is a box `⌈·A⌉ψ` in the left component of `t`.
  rw [hgleft] at hgne
  obtain ⟨ψ, hψ⟩ := Finset.nonempty_iff_ne_empty.mpr hgne
  have hbox : (⌈·A⌉ψ) ∈ t.label.left := Finset.mem_projection.mp hψ
  have htplus : t ∈ C.fineCLplus := Finset.mem_union_left _ (List.mem_toFinset.mpr ht_CL)
  have hAleft : (Sum.inr A : Sum Nat Nat) ∈ (nodeAt C.root).left.pdlFvoc := by
    apply C.vocL_fineCLplus t htplus
    exact mem_fvoc_iff.mpr ⟨_, hbox, by simp⟩
  have hAright : (Sum.inr A : Sum Nat Nat) ∈ (nodeAt C.root).right.pdlFvoc := by
    apply C.vocR_fineCLplus t htplus
    have hO : t.label.2.2 = some (Sum.inr (~'⌊·A⌋xi)) := by rw [← ht_lab] at hAxi; exact hAxi
    refine mem_fvoc_iff.mpr ⟨~(⌊·A⌋xi).unload, ?_, ?_⟩
    · rcases hh : t.label with ⟨L, R, O⟩
      rw [hh] at hO
      subst hO
      simp [Sequent.right, Olf.R]
    · cases xi <;> simp [LoadFormula.unload]
  have hlp : Δ.loadedProg = (·A : Program) := by
    obtain ⟨L, R, O⟩ := Δ
    simp only at hAxi
    subst hAxi
    cases xi <;> rfl
  rw [hlp]
  intro x hx
  simp only [Program.voc, Finset.mem_singleton] at hx
  subst hx
  simp only [jvoc, Finset.mem_inter]
  exact ⟨hAleft, hAright⟩

/-- The inner induction in the proof of Lemma 10.3, see `PaperFacts.leftPropagation`.

The argument is a descent along the children of `t`: an exit is covered by the second
hypothesis and a node of `C^R_Δ` by the first, while at a node of `C^L_Δ` all children stay
in `C⁺_Δ` (by `FinePathIn.children_rightOnly_eq_of_usesLeftRule` and
`LoadedCluster.mem_fineCLplus_of_child`) and the local invertibility of the left rule
applied there transfers the entailment back up. That last step is
`FinePathIn.leftEntails_of_children_of_usesLeftRule`; note that `FinePathIn.locally_sound`
is *not* enough here, because it speaks about the whole label while `leftEntails` only
assumes the left component, so we need the left-only invertibility
`LocalRuleApp.left_sat_of_isLeftRule`.

The descent is not along the fine child relation but, as in `isLrep_of_mem_nodesWithFine`,
by well-founded induction on the label along the Dershowitz-Manna ordering `ltSequent`:
left rules strictly decrease the label, and this makes the remaining case, a loaded-path
repeat in `C_Δ`, work out. At such a repeat no rule is applied, but by
`exists_companion_mem_nodesWithFine` its companion is again a node of `C_Δ` with exactly the
same label and is not a repeat, so the claim at the companion — which is the same claim,
since `leftEntails` only depends on the label — is obtained from the very same case
distinction, at the same label.

Properness of the cluster is used through `LoadedCluster.exists_child_memFine_of_not_isLrep`
(Lemma 9.4 (c)), which is why no separate properness hypothesis is needed. -/
lemma leftPropagation_of_proper (C : LoadedCluster tab) :
    ∀ Δ ∈ C.lambdaTwo, ∀ φ : Formula,
      (∀ u ∈ C.nodesWithFineRight Δ, u.leftEntails φ) →
      (∀ u ∈ C.exitsWithFine Δ, u.leftEntails φ) →
      ∀ t ∈ C.plusNodesWithFine Δ, t.leftEntails φ := by
  intro Δ _ φ hRight hExit
  -- The claim at a node of `C_Δ` that is *not* a loaded-path repeat, given the claim at
  -- all nodes of `C⁺_Δ` with a strictly smaller label.
  have step : ∀ Y : Sequent,
      (∀ Y', ltSequent Y' Y → ∀ t' ∈ C.plusNodesWithFine Δ, t'.label = Y' → t'.leftEntails φ) →
      ∀ u ∈ C.nodesWithFine Δ, ¬ u.base.isLrep → u.label = Y → u.leftEntails φ := by
    intro Y IH u hu hnl hlab
    have hu' := hu
    simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq] at hu'
    obtain ⟨hu_CL, hu_lab⟩ := hu'
    have hmf : C.memFine u := (C.mem_fineCL u).mp hu_CL
    have huR : u.label.2.2.isRight := C.memFine_label_isRight hmf
    obtain ⟨g0, hg0, -⟩ := C.exists_child_memFine_of_not_isLrep hmf hnl
    have hne : u.children ≠ ∅ := by
      intro hnil
      rw [hnil] at hg0
      simp at hg0
    rcases u.usesLeftRule_or_usesRightRule_of_children_ne_empty hne with hleft | hright
    · -- A left rule: all children are in `C⁺_Δ` and have a strictly smaller label, so the
      -- claim holds at them, and local invertibility transfers it to `u`.
      refine u.leftEntails_of_children_of_usesLeftRule hleft huR ?_
      intro g hg
      refine IH g.label (hlab ▸ u.children_lt_Sequent_of_usesLeftRule hleft huR g hg) g ?_ rfl
      simp only [plusNodesWithFine, Finset.mem_filter, decide_eq_true_eq]
      exact ⟨C.mem_fineCLplus_of_child hu_CL hg,
        by rw [u.children_rightOnly_eq_of_usesLeftRule hleft huR g hg, hu_lab]⟩
    · -- A right rule: this is the first hypothesis.
      exact hRight u (by simp only [nodesWithFineRight, List.mem_filter]; exact ⟨hu, hright⟩)
  -- The claim at all nodes of `C⁺_Δ`, by well-founded induction on the label.
  have key : ∀ Y : Sequent, ∀ t ∈ C.plusNodesWithFine Δ, t.label = Y → t.leftEntails φ := by
    intro Y
    induction Y using WellFounded.induction instIsWellFoundedSequentLt with
    | _ Y IH =>
      intro t ht hlab
      have ht' := (C.mem_plusNodesWithFine_iff Δ t).mp ht
      by_cases hmf : C.memFine t
      · have htf : t ∈ C.nodesWithFine Δ := by
          simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq]
          exact ⟨(C.mem_fineCL t).mpr hmf, ht'.2⟩
        by_cases hl : t.base.isLrep
        · -- A loaded-path repeat: its companion carries the same label, is again a node of
          -- `C_Δ` and is not a repeat, so the claim there is the claim here.
          obtain ⟨c, hc_mem, hc_nl, hc_lab⟩ := C.exists_companion_mem_nodesWithFine htf hl
          have hc := step Y IH c.toFine hc_mem (by rw [PathIn.base_toFine]; exact hc_nl)
            (by rw [PathIn.label_toFine, hc_lab, hlab])
          intro W M w hw
          exact hc W M w (by rw [PathIn.label_toFine, hc_lab]; exact hw)
        · exact step Y IH t htf hl hlab
      · -- Not a node of the cluster, hence an exit: this is the second hypothesis.
        refine hExit t ((C.mem_exitsWithFine_iff Δ t).mpr ⟨?_, ht'.2⟩)
        rcases Finset.mem_union.mp ht'.1 with h | h
        · exact absurd ((C.mem_fineCL t).mp (List.mem_toFinset.mp h)) hmf
        · exact h
  exact fun t ht => key t.label t ht rfl

/-- Lemma 9.7 (f): at a non-basic `Δ` the children of any `t ∈ C^R_Δ` are the `Λ₁(t);Π`
for `Π ∈ stepOf Δ`.  Here only the existence of a node of `C⁺_Π` with the same left
component as `t` is recorded, which is what the proof of Lemma 10.3 uses. -/
lemma rightRuleChildren_of_uniform (C : LoadedCluster tab) (hU : C.HasUniformSteps) :
    ∀ Δ ∈ C.lambdaTwo, ¬ Δ.basic → ∀ t ∈ C.nodesWithFineRight Δ,
      ∀ Pi ∈ C.stepOf Δ, ∃ u ∈ C.plusNodesWithFine Pi, u.label.left = t.label.left := by
  intro Δ _ hnb t ht Pi hPi
  have ht' := ht
  simp only [nodesWithFineRight, nodesWithFine, List.mem_filter, decide_eq_true_eq] at ht'
  obtain ⟨⟨ht_CL, ht_lab⟩, ht_right⟩ := ht'
  rw [← C.stepOf_spec hU Δ ht] at hPi
  simp only [Finset.mem_image] at hPi
  obtain ⟨u, hu, hlab⟩ := hPi
  refine ⟨u, ?_, ?_⟩
  · simp only [plusNodesWithFine, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨C.mem_fineCLplus_of_child ht_CL hu, hlab⟩
  · exact t.children_left_eq_of_usesRightRule ht_right (ht_lab ▸ hnb) u hu

/-- Lemma 9.7 (e), in the semantic form used in the proof of Lemma 10.3.

Note that no uniformity is needed here: by `basicModalStepAt` the right components of the
children of a node of `C^R_Δ` with `Δ` basic are determined by `Δ` alone, so the list
`stepOf Δ`, read off the first node of `C^R_Δ`, describes the children of every node of
`C^R_Δ`. -/
lemma modalStep_of (C : LoadedCluster tab) :
    ∀ Δ ∈ C.lambdaTwo, Δ.basic → ∀ t ∈ C.nodesWithFineRight Δ,
      ∀ Pi ∈ C.stepOf Δ, ∃ u ∈ C.plusNodesWithFine Pi,
        ∀ (W : Type) (M : KripkeModel W) (w v : W), (∀ ψ ∈ t.label.left, evaluate M w ψ) →
          relate M Δ.loadedProg w v → ∀ ψ ∈ u.label.left, evaluate M v ψ := by
  intro Δ _ hb t ht Pi hPi
  obtain ⟨f0, hf0, g0, hg0, hg0lab⟩ := C.exists_child_rightOnly_of_mem_stepOf hPi
  obtain ⟨A, xi, hAxi, g, hg, -, hgleft, hgright⟩ := C.basicModalStepAt hb ht
  obtain ⟨A', xi', hAxi', g0', hg0', -, -, hg0right⟩ := C.basicModalStepAt hb hf0
  have hAA : A' = A ∧ xi' = xi := by
    rw [hAxi] at hAxi'
    simp only [Option.some.injEq, Sum.inr.injEq] at hAxi'
    rcases xi' with φ | χ <;> rcases xi with φ' | χ' <;> simp_all
  rw [hAA.1, hAA.2] at hg0right
  rw [hg0', Finset.mem_singleton] at hg0
  subst hg0
  have hPi_eq : Pi = g.label.rightOnly := by rw [← hg0lab, hg0right, hgright]
  have ht' := ht
  simp only [nodesWithFineRight, nodesWithFine, List.mem_filter, decide_eq_true_eq] at ht'
  refine ⟨g, ?_, ?_⟩
  · simp only [plusNodesWithFine, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨C.mem_fineCLplus_of_child ht'.1.1 (by rw [hg]; simp), hPi_eq.symm⟩
  · have hlp : Δ.loadedProg = (·A : Program) := by
      obtain ⟨L, R, O⟩ := Δ
      simp only at hAxi
      subst hAxi
      cases xi <;> rfl
    intro W M w v hw hrel ψ hψ
    rw [hgleft] at hψ
    have hbox := hw _ (Finset.mem_projection.mp hψ)
    rw [hlp] at hrel
    exact hbox v hrel

/-- All facts of `PaperFacts`, from the two standing assumptions of the paper. -/
theorem paperFacts (C : LoadedCluster tab) (hA : C.HasUniformSteps) : C.PaperFacts where
  exists_right := C.exists_right_of_proper
  vocL := C.vocL_fineCLplus
  vocR := C.vocR_fineCLplus
  loadedProgVoc := C.loadedProgVoc_of_proper (C.exists_right_of_proper)
  leftPropagation := C.leftPropagation_of_proper
  rightRuleChildren := C.rightRuleChildren_of_uniform hA -- only field that needs uniformity
  modalStep := C.modalStep_of

end LoadedCluster

/-! ## Discharging the cluster facts

`LoadedCluster.paperFacts` derives the seven fields of `LoadedCluster.PaperFacts` from
cluster properness and tableau uniformity. The final interpolation theorem obtains a
uniform tableau using `Tableau.toUniformViaGame`; neither premise remains as an
assumption of that theorem.

* `vocL` and `vocR` are `vocL_fineCLplus` and `vocR_fineCLplus`, proved from vocabulary
  preservation along `◃` (section `VocPreservation`) together with the fact that every fine
  node of `C⁺` is `◃`-reachable from the root;
* `rightRuleChildren` is `rightRuleChildren_of_uniform`, proved from `stepOf_spec`, i.e.
  from the second assumption;
* `modalStep` is `modalStep_of`, proved from properness alone via `basicModalStepAt`, which
  is Lemma 9.7 (e): at a node of `C^R_Δ` with `Δ` basic the rule applied is the modal rule
  `(M)` for the loaded formula of `Δ`;
* `loadedProgVoc` is `loadedProgVoc_of_proper`, proved from properness and Lemma 9.7 (d);
* `exists_right` (Lemma 9.7 (d)) is `exists_right_of_proper` and `leftPropagation` is
  `leftPropagation_of_proper`, both proved from properness by well-founded induction on
  the label along the Dershowitz-Manna ordering `ltSequent`.

Where uniformity (conditions U1/U2, formalised as `LoadedCluster.HasUniformSteps` with
`LoadedCluster.stepOf_spec`) is needed can now be read off: in exactly **one** of the eight
fields, namely `rightRuleChildren`. The reason is that `C.stepOf Δ` reads the right
components of the children of the *first* node of `C^R_Δ`, while the fields of the two
records quantify over all nodes of `C^R_Δ`:

* `PaperFacts.rightRuleChildren` (used at non-basic type-3 nodes in the proof of Lemma
  10.3) says that for *every* `t ∈ C^R_Δ` and every `Π ∈ stepOf Δ` there is a node of
  `C⁺_Π` with the same left component as `t`. Its proof takes the children of `t`, so it
  needs the right components of those children to be the list `stepOf Δ` — which for a
  non-basic `Δ` is precisely `stepOf_spec`, i.e. uniformity.
* `PaperFacts.modalStep` and `SatDownFacts.basicStep` also quantify over `t ∈ C^R_Δ`, but
  only for *basic* `Δ`. There the rule applied is the modal rule for the unique loaded
  formula of `Δ` (Lemma 9.7 (e)), so the right components of the children are determined by
  `Δ` alone; this is what `basicModalStepAt` shows, and it is why `modalStep_of` needs no
  uniformity.
* The remaining fields (`SatDownFacts.nonBasicStep`, `SatDownFacts.stepLT`,
  `PaperFacts.leftPropagation`, `exists_right`, the vocabulary fields) speak about `Δ` and
  `stepOf Δ` only, or about local invertibility at a single node, and are independent of
  uniformity.
-/

/-! ## Interpolants for proper clusters -/

/-- Lemma 9.3 for the case where the loaded formula is on the right side:
given interpolants for all exits of the cluster `C`, interpolate the root of `C`.

The interpolant is `C.itp θ` from Definition 9.20, where `θ` gives the interpolants of the
*fine* exit nodes, obtained from the given interpolants of the coarse exits by
`LoadedCluster.fineExits_itp_spec`. Its three defining properties are Lemma 10.1
(`itp_voc`), Lemma 10.3 (`left_unsat_neg_itp`) and Lemma 10.8 (`right_unsat_itp`). -/
noncomputable def clusterInterpolationRight {tab : Tableau .nil X} (Xfree : X.isFree)
    (t_u : tab.isUniform)
    (C : LoadedCluster tab) (exitIPs : ∀ e ∈ C.exits, PartInterpolant (nodeAt e))
    : PartInterpolant (nodeAt C.root) := by
  classical
  -- Because we have a uniform tableay, also the fixed cluster C must have uniform steps.
  have hA : C.HasUniformSteps := LoadedCluster.uniformOfUniTab C t_u
  -- All facts of `PaperFacts` follow from these two.
  have hF : C.PaperFacts := C.paperFacts hA
  -- Get additional facts about the cluster (that used to be placeholders but are now proven).
  have hS : C.SatDownFacts := C.satDownFacts C.exists_right_of_proper
  have exitIPs' : ∀ e ∈ C.exits, ∃ θ, isPartInterpolant (nodeAt e) θ :=
    fun e he => ⟨(exitIPs e he).1, (exitIPs e he).2⟩
  have hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (FinePathIn.itp f) :=
    C.fineExits_itp_spec exitIPs'
  refine ⟨C.itp FinePathIn.itp, C.itp_voc hF _ hθ, C.left_unsat_neg_itp hF hθ, ?_⟩
  by_cases hΓ₁ : (nodeAt C.root).left = {}
  · rw [LoadedCluster.itp, ite_eq_left hΓ₁]
    have := tableauThenNotSat tab Xfree C.root
    exact Sequent.satisfiable_top_cons_right hΓ₁ this
  · exact C.right_unsat_itp hS hθ hΓ₁

/-- Lemma 9.3: Given a loaded node `s` that is the first node of its cluster, and given
interpolants for all exits of that cluster, we get an interpolant for `s`.
Note how `s_cr` is exactly what is needed to make a `LoadedCluster` here. -/
noncomputable def clusterInterpolation {tab : Tableau .nil X} (Xfree : X.isFree)
    (t_u : tab.isUniform) (s : PathIn tab)
    (s_cr : s.isClusterRoot) (s_proper : s ◃⁺ s) (s_loaded : (nodeAt s).isLoaded)
    (exitIPs : ∀ e : PathIn tab, isExitOf s e → PartInterpolant (nodeAt e))
    : PartInterpolant (nodeAt s) := by
  by_cases s_right : (nodeAt s).2.2.isRight
  case pos =>
    -- The loaded formula is on the right, so we can use `clusterInterpolationRight`.
    exact clusterInterpolationRight Xfree t_u (LoadedCluster.ofClusterRoot s s_cr s_proper s_right)
      (fun e e_in => exitIPs e ((LoadedCluster.mem_exits_iff _ e).mp e_in))
  case neg =>
    -- The loaded formula is on the left, so we "flip" the whole tableau.
    have s_flip_right : (nodeAt s.flip).2.2.isRight := by
      rw [PathIn.nodeAt_flip]
      rcases hh : nodeAt s with ⟨L, R, O⟩
      rw [hh] at s_right s_loaded
      cases O
      · simp [Sequent.isLoaded] at s_loaded
      case some val => cases val <;> simp_all [Sequent.flip, Olf.flip]
    have s_proper_flip := cEdgeTrans_flip_of_cEdgeTrans s_proper
    let C : LoadedCluster tab.flip :=
      LoadedCluster.ofClusterRoot s.flip (PathIn.isClusterRoot_flip s_cr) s_proper_flip s_flip_right
    have flipIPs : ∀ e ∈ C.exits, PartInterpolant (nodeAt e) := by
      intro e e_in
      have e_exit : isExitOf s.flip e := (LoadedCluster.mem_exits_iff _ e).mp e_in
      rw [← PathIn.flip_unflip e] at e_exit ⊢
      exact PartInterpolant.flipPath (exitIPs e.unflip (isExitOf_flip.mp e_exit))
    have : X.flip.isFree := by rw [Sequent.flip_isFree]; exact Xfree
    exact PartInterpolant.unflipPath (clusterInterpolationRight this t_u.flip C flipIPs)

end PDL
