/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

import LeanPool.PDL.Soundness

/-! ## Helpers for Lemma 9.4: single steps keep the loading on the right

The lemmas here say that a single step in a tableau, starting at a node that is loaded
on the right, can only lead to a node that is loaded on the right or free, and that no
rule adds formulas to an empty left component.
-/

namespace PDL

/-- A PDL rule applied to a sequent that is loaded on the right leads to a sequent that is
not loaded on the left, and it does not add formulas to an empty left component. -/
lemma pdlRule_inv {X Y : Sequent} (r : PdlRule X Y) (h : X.2.2.isRight) :
    ¬ Y.2.2.isLeft ∧ (X.1 = {} → Y.1 = {}) := by
  cases r
  case modR L R A ξ hX hY => rcases ξ with φ|χ <;> simp_all [Finset.pdlProjection]
  all_goals simp_all

/-- Local rules never load on the left: if the given sequent is not loaded on the left,
then neither are the results of applying a local rule to it. -/
lemma applyLocalRule_not_isLeft {Lcond Rcond Ocond ress}
    (lr : LocalRule (Lcond, Rcond, Ocond) ress)
    {L R O} (hO : Ocond ⊆ O) (hnl : ¬ O.isLeft) :
    ∀ c ∈ applyLocalRule lr (L, R, O), ¬ c.2.2.isLeft := by
  rcases lr with ⟨orule, rfl⟩|⟨orule, rfl⟩|_|_|⟨χ, lrule, rfl⟩|⟨χ, lrule, rfl⟩
  all_goals
    intro c hc
    try simp only [applyLocalRule, Finset.mem_image, exists_exists_and_eq_and] at hc
    try obtain ⟨z, hz, rfl⟩ := hc
    try obtain ⟨z, zo, hz, rfl⟩ := hc
    rcases O with _|(o|o)
    <;> (try rcases z with ⟨zl, _|zo⟩)
    <;> simp_all [Olf.change, Option.pdlOverwrite]

/-- Local rules do not add formulas to an empty left component,
provided the sequent is not loaded on the left. -/
lemma applyLocalRule_L_empty {Lcond Rcond Ocond ress} (lr : LocalRule (Lcond, Rcond, Ocond) ress)
    {L R O} (hL : L = {}) (hsub : Lcond ⊆ L) (hO : Ocond ⊆ O) (hnl : ¬ O.isLeft) :
    ∀ c ∈ applyLocalRule lr (L, R, O), c.1 = {} := by
  subst hL
  rw [Finset.subset_empty] at hsub
  rcases lr with ⟨orule, rfl⟩|⟨orule, rfl⟩|_|_|⟨χ, lrule, rfl⟩|⟨χ, lrule, rfl⟩
  · exact absurd hsub orule.precond_ne_nil
  all_goals
    intro c hc
    try simp only [applyLocalRule, Finset.mem_image, exists_exists_and_eq_and] at hc
    try obtain ⟨z, hz, rfl⟩ := hc
    try obtain ⟨z, zo, hz, rfl⟩ := hc
    try (rw [Option.some_subseteq] at hO; subst hO)
    simp_all

/-- End nodes of a local tableau for a sequent that is not loaded on the left are also not
loaded on the left, and they have an empty left component if the given sequent has. -/
lemma endNodesOf_inv {X : Sequent} (lt : LocalTableau X) (hnl : ¬ X.2.2.isLeft) :
    ∀ Y ∈ endNodesOf lt, ¬ Y.2.2.isLeft ∧ (X.1 = {} → Y.1 = {}) := by
  induction lt with
  | @byLocalRule X lra X_def next IH =>
    subst X_def
    intro Y Y_in
    obtain ⟨Z, Z_in, Y_in⟩ := endNodeIsEndNodeOfChild rfl Y_in
    obtain ⟨hL, -, hOsub⟩ := lra.preconditionProof
    rw [lra.hC] at Z_in
    have hZ : ¬ Z.2.2.isLeft := applyLocalRule_not_isLeft lra.lr hOsub hnl Z Z_in
    obtain ⟨h1, h2⟩ := IH Z (lra.hC ▸ Z_in) hZ Y Y_in
    refine ⟨h1, fun hXL => h2 ?_⟩
    exact applyLocalRule_L_empty lra.lr hXL (by simpa using hL) hOsub hnl Z Z_in
  | sim => simp_all

/-- A `⋖_` step from a node loaded on the right leads to a node that is not loaded on the
left, and it does not add formulas to an empty left component. -/
lemma edge_inv {Hist X} {tab : Tableau Hist X} {s t : PathIn tab} (h : s ⋖_ t)
    (hs : (nodeAt s).2.2.isRight) :
    ¬ (nodeAt t).2.2.isLeft ∧ ((nodeAt s).1 = {} → (nodeAt t).1 = {}) := by
  rcases nodeAt_of_edge h with ⟨lt, t_in⟩ | hr
  · refine endNodesOf_inv lt ?_ _ t_in
    rcases hh : (nodeAt s).2.2 with _|(o|o) <;> rw [hh] at hs <;> simp_all
  · obtain ⟨r⟩ := hr
    exact pdlRule_inv r hs

/-- A `◃` step from a node loaded on the right to a loaded node leads to a node that is
also loaded on the right, and it does not add formulas to an empty left component. -/
lemma cEdge_inv {X} {tab : Tableau .nil X} {s t : PathIn tab} (h : s ◃ t)
    (hs : (nodeAt s).2.2.isRight) (ht : (nodeAt t).isLoaded) :
    (nodeAt t).2.2.isRight ∧ ((nodeAt s).1 = {} → (nodeAt t).1 = {}) := by
  rcases h with h | ⟨lpr, h_lrep, rfl⟩
  · obtain ⟨h1, h2⟩ := edge_inv h hs
    exact ⟨Sequent.isRight_of_not_isLeft_isLoaded h1 ht, h2⟩
  · have same := nodeAt_companionOf_setEq s lpr h_lrep
    rw [same]
    exact ⟨hs, id⟩

/-- Along a `◃`-path where all nodes are loaded, the loading stays on the right and an
empty left component stays empty. -/
lemma cReach_inv {X} {tab : Tableau .nil X} {a b : PathIn tab} (hab : a ◃* b)
    (hloaded : ∀ v, a ◃* v → v ◃* b → (nodeAt v).isLoaded)
    (ha : (nodeAt a).2.2.isRight) :
    (nodeAt b).2.2.isRight ∧ ((nodeAt a).1 = {} → (nodeAt b).1 = {}) := by
  induction hab with
  | refl => exact ⟨ha, id⟩
  | @tail v b hav hvb IH =>
    obtain ⟨h1, h2⟩ := IH
      (fun w haw hwv => hloaded w haw (hwv.trans (Relation.ReflTransGen.single hvb)))
    obtain ⟨g1, g2⟩ := cEdge_inv hvb h1 (hloaded b (hav.tail hvb) Relation.ReflTransGen.refl)
    exact ⟨g1, fun hn => g2 (h2 hn)⟩

end PDL
