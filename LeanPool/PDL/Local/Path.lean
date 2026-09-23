/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Local.Tableau

/-! # Paths in Local Tableaux

Here we collect the paths of sequents within a `LocalTableau`, i.e. the lists of sequents
from the root to an end node, and show that they are saturated and locally consistent.

This is used for the pre-states in the completeness proof, see `BuildTree.lean`. -/

@[expose] public section

namespace PDL

/-! ## Formulas occurring along a list of sequents -/

/-- All formulas occurring in the sequents of a list, as a `Finset`. -/
def pathForms (L : List Sequent) : Finset Formula := (L.toFinset.image Sequent.toFinset).sup id

@[simp]
lemma mem_pathForms {L : List Sequent} {f : Formula} :
    f ∈ pathForms L ↔ ∃ Z ∈ L, f ∈ Z.toFinset := by
  simp [pathForms, Finset.mem_sup]

@[simp]
lemma pathForms_cons {Z : Sequent} {L : List Sequent} :
    pathForms (Z :: L) = Z.toFinset ∪ pathForms L := by
  ext f; simp

@[simp]
lemma pathForms_nil : pathForms [] = ∅ := by
  ext f; simp

/-- All `WhateverFormula`s occurring in the sequents of a list, as a `Finset`. -/
def pathWForms (L : List Sequent) : Finset WhateverFormula :=
  (L.toFinset.image Sequent.wForms).sup id

@[simp]
lemma mem_pathWForms {L : List Sequent} {f : WhateverFormula} :
    f ∈ pathWForms L ↔ ∃ Z ∈ L, f ∈ Z.wForms := by
  simp [pathWForms, Finset.mem_sup]

@[simp]
lemma pathWForms_cons {Z : Sequent} {L : List Sequent} :
    pathWForms (Z :: L) = Z.wForms ∪ pathWForms L := by
  ext f; simp

@[simp]
lemma pathWForms_nil : pathWForms [] = ∅ := by
  ext f; simp

/-! ## Paths -/

/-- The finite set of root-to-end paths of a local tableau. -/
def LocalTableau.paths : {X : _} → LocalTableau X → Finset (List Sequent)
  | .(_), (@byLocalRule X lra _ next) =>
      let tails := (lra.C.attach.image (fun ⟨Y, h⟩ => (next Y h).paths)).sup id
      tails.image (X :: ·)
  | .(_), (@sim X _) => {[X]}

lemma LocalTableau.paths_mem_nonempty {X} (lt : LocalTableau X) :
    ∀ L ∈ lt.paths, L ≠ [] := by
  intro L L_in; cases lt <;> grind [paths]

/-- Characterisation of membership in `paths` for the `byLocalRule` case. -/
lemma LocalTableau.mem_paths_byLocalRule {X} {lra : LocalRuleApp} {X_def : X = lra.X}
    {next : ∀ Y ∈ lra.C, LocalTableau Y} {L} :
    L ∈ (LocalTableau.byLocalRule lra X_def next).paths
    ↔ ∃ Y, ∃ h : Y ∈ lra.C, ∃ L' ∈ (next Y h).paths, L = X :: L' := by
  simp only [paths, Finset.mem_image, Finset.mem_sup, Finset.mem_attach, true_and,
    Subtype.exists, id_eq]
  constructor
  · rintro ⟨L', ⟨i, ⟨Y, h, rfl⟩, hL'⟩, rfl⟩
    exact ⟨Y, h, L', hL', rfl⟩
  · rintro ⟨Y, h, L', hL', rfl⟩
    exact ⟨L', ⟨_, ⟨Y, h, rfl⟩, hL'⟩, rfl⟩

@[simp]
lemma LocalTableau.mem_paths_sim {X} {bas : X.basic} {L} :
    L ∈ (LocalTableau.sim bas).paths ↔ L = [X] := by
  simp [paths]

lemma LocalTableau.pathsHead_eq_self {X} {lt : LocalTableau X} :
    ∀ {L}, (h : L ∈ lt.paths) → L.head (LocalTableau.paths_mem_nonempty lt _ h) = X := by
  intro L h
  cases lt
  case byLocalRule lra X_def next =>
    rw [LocalTableau.mem_paths_byLocalRule] at h
    rcases h with ⟨Y, hY, L', hL', rfl⟩
    simp
  case sim bas =>
    rw [LocalTableau.mem_paths_sim] at h
    subst h
    simp

lemma LocalTableau.pathsLast_eq_endNodes {X} {lt : LocalTableau X} :
    (lt.paths.attach.image
      (fun ⟨L,h⟩ => L.getLast (LocalTableau.paths_mem_nonempty lt L h)))
    = endNodesOf lt := by
  induction lt
  case byLocalRule X lra X_def next IH =>
    ext Z
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, endNodesOf,
      Finset.sup_image, Function.id_comp, Finset.mem_sup]
    constructor
    · rintro ⟨L, hL, rfl⟩
      rw [LocalTableau.mem_paths_byLocalRule] at hL
      rcases hL with ⟨Y, hY, L', hL', rfl⟩
      refine ⟨Y, hY, ?_⟩
      rw [← IH Y hY]
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      refine ⟨L', hL', ?_⟩
      exact (List.getLast_cons (LocalTableau.paths_mem_nonempty (next Y hY) L' hL')).symm
    · rintro ⟨Y, hY, hZ⟩
      rw [← IH Y hY] at hZ
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hZ
      rcases hZ with ⟨L', hL', rfl⟩
      refine ⟨X :: L', ?_, ?_⟩
      · rw [LocalTableau.mem_paths_byLocalRule]
        exact ⟨Y, hY, L', hL', rfl⟩
      · exact List.getLast_cons (LocalTableau.paths_mem_nonempty (next Y hY) L' hL')
  case sim X bas =>
    ext Z
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, endNodesOf,
      Finset.mem_singleton]
    constructor
    · rintro ⟨L, hL, rfl⟩
      rw [LocalTableau.mem_paths_sim] at hL
      subst hL
      simp
    · rintro rfl
      exact ⟨[Z], by simp, by simp⟩

/-- Any open local tableau has at least one path (from root to some end node).
Does not hold for `LocalTableau` which might end with "contradiction/closing" rule applications. -/
lemma OpenLocalTableau.paths_nonempty {X} (lt : OpenLocalTableau X) :
    lt.1.paths ≠ {} := by
  rcases lt with ⟨lt, lt_has_ends⟩
  have := @LocalTableau.pathsLast_eq_endNodes X lt
  grind

lemma LocalTableau.paths_last_basic {X} {lt : LocalTableau X} :
    ∀ L, (h : L ∈ lt.paths) → (L.getLast (LocalTableau.paths_mem_nonempty lt L h)).basic := by
  intro L L_in
  apply (@endNodesOf_basic _ _ lt)
  rw [← @LocalTableau.pathsLast_eq_endNodes _ lt]
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
  exact ⟨L, L_in, rfl⟩

lemma LocalTableau.paths_saturated {X} {lt : LocalTableau X} :
    ∀ L ∈ lt.paths, saturated (pathForms L) := by
  induction lt
  case byLocalRule X lra X_def next IH =>
    intro L L_in
    rw [LocalTableau.mem_paths_byLocalRule] at L_in
    rcases L_in with ⟨Y, Y_in, L', L'_in, rfl⟩
    have IH' := IH Y Y_in L' L'_in
    have Y_mem : Y ∈ L'.toFinset := by
      have := LocalTableau.pathsHead_eq_self L'_in
      rw [List.mem_toFinset, ← this]
      exact List.head_mem _
    have := lra.preserve_saturated_up Y Y_in L'.toFinset Y_mem IH'
    have union_eq : ({lra.X} ∪ L'.toFinset : Finset Sequent) = (X :: L').toFinset := by
      simp only [List.toFinset_cons, Finset.insert_eq, X_def]
    rw [union_eq] at this
    exact this
  case sim X bas =>
    intro L L_in
    rw [LocalTableau.mem_paths_sim] at L_in
    subst L_in
    simpa using Sequent.basic_then_saturated bas

/-! ## Formulas that survive to the end of a path -/

/-- General helper: anything that is preserved by all local rule applications and occurs
somewhere along a path also occurs at the end of the path. -/
lemma LocalTableau.mem_last_of_preserved {α} {X} {lt : LocalTableau X}
    (κ : Sequent → Finset α) (f : α)
    (pres : ∀ (lra : LocalRuleApp), ∀ Y ∈ lra.C, f ∈ κ lra.X → f ∈ κ Y) :
    ∀ L, (h : L ∈ lt.paths) → (∃ Z ∈ L, f ∈ κ Z) →
      f ∈ κ (L.getLast (LocalTableau.paths_mem_nonempty lt L h)) := by
  induction lt
  case byLocalRule X lra X_def next IH =>
    intro L L_in hf
    have L_in' := L_in
    rw [LocalTableau.mem_paths_byLocalRule] at L_in'
    rcases L_in' with ⟨Y, Y_in, L', L'_in, rfl⟩
    have L'_ne := LocalTableau.paths_mem_nonempty (next Y Y_in) L' L'_in
    have Y_mem : Y ∈ L' := by
      have := LocalTableau.pathsHead_eq_self L'_in
      rw [← this]
      exact List.head_mem _
    have hf' : ∃ Z ∈ L', f ∈ κ Z := by
      rcases hf with ⟨Z, Z_in, f_in⟩
      rcases List.mem_cons.mp Z_in with rfl | Z_in'
      · exact ⟨Y, Y_mem, pres lra Y Y_in (by rwa [← X_def])⟩
      · exact ⟨Z, Z_in', f_in⟩
    have := IH Y Y_in L' L'_in hf'
    rw [List.getLast_cons L'_ne]
    exact this
  case sim X bas =>
    intro L L_in hf
    have L_in' := L_in
    rw [LocalTableau.mem_paths_sim] at L_in'
    subst L_in'
    rcases hf with ⟨Z, Z_in, f_in⟩
    simp only [List.mem_singleton] at Z_in
    subst Z_in
    simpa using f_in

/-- An atomic formula anywhere in a local tableau path still occurs at the end of the path. -/
lemma LocalTableau.paths_local_atom_mem_last {X} {lt : LocalTableau X} {L} (L_in : L ∈ lt.paths) f :
    (f = ⊥ ∨ ∃ p : Nat, f = (Formula.atom_prop p) ∨ f = (~(Formula.atom_prop p))) →
      f ∈ pathForms L →
        f ∈ (L.getLast (LocalTableau.paths_mem_nonempty lt L L_in)).toFinset := by
  intro f_kind f_in
  refine LocalTableau.mem_last_of_preserved Sequent.toFinset f ?_ L L_in (mem_pathForms.mp f_in)
  intro lra Y Y_in hf
  exact lra.preserve_local_atom_down Y Y_in f f_kind hf

/-- A basic formula anywhere in a local tableau path still occurs at the end of the path. -/
lemma LocalTableau.paths_basic_mem_last {X} {lt : LocalTableau X} {L} (L_in : L ∈ lt.paths) f :
    f.basic → f ∈ pathForms L →
      f ∈ (L.getLast (LocalTableau.paths_mem_nonempty lt L L_in)).toFinset := by
  intro f_basic f_in
  refine LocalTableau.mem_last_of_preserved Sequent.toFinset f ?_ L L_in (mem_pathForms.mp f_in)
  intro lra Y Y_in hf
  exact lra.preserve_basic_down Y Y_in f f_basic hf

lemma LocalTableau.paths_locallyConsistent {X} {lt : LocalTableau X} :
    ∀ L ∈ lt.paths, locallyConsistent (pathForms L) := by
  intro L L_in
  have last_basic := LocalTableau.paths_last_basic L L_in
  have last_consistent := Sequent.basic_to_locallyConsistent last_basic
  unfold locallyConsistent at *
  constructor
  · intro bot_in
    exact last_consistent.1 <|
      LocalTableau.paths_local_atom_mem_last L_in ⊥ (Or.inl rfl) bot_in
  · intro p p_in neg_p_in
    refine last_consistent.2 p ?_ ?_
    · exact LocalTableau.paths_local_atom_mem_last L_in (Formula.atom_prop p)
        (Or.inr ⟨p, Or.inl rfl⟩) p_in
    · exact LocalTableau.paths_local_atom_mem_last L_in (~(Formula.atom_prop p))
        (Or.inr ⟨p, Or.inr rfl⟩) neg_p_in

/-! ## Unfolding of diamonds along paths -/

/-- Along any path in a local tableau, a non-atomic free diamond must be unfolded:
if `~⌈α⌉φ` occurs (unloaded) somewhere on the path and `α` is not atomic, then all formulas of
one of the unfoldings `Yset Fδ φ` occur (unloaded) on the path as well.
Analogous to `LocalTableau.paths_saturated`, but for `Sequent.wForms`. -/
lemma LocalTableau.paths_freeUnfoldDia {X} {lt : LocalTableau X} {α φ} (notAtom : ¬ α.isAtomic) :
    ∀ L ∈ lt.paths, (~⌈α⌉φ : WhateverFormula) ∈ pathWForms L →
      ∃ Fδ ∈ Dset α, (Yset Fδ φ).all
        (fun f => (f : WhateverFormula) ∈ pathWForms L) := by
  induction lt
  case byLocalRule X lra X_def next IH =>
    intro L L_in hmem
    rw [LocalTableau.mem_paths_byLocalRule] at L_in
    rcases L_in with ⟨Y, Y_in, L', L'_in, rfl⟩
    have Y_mem_L' : Y ∈ L' := by
      have := LocalTableau.pathsHead_eq_self L'_in
      rw [← this]
      exact List.head_mem _
    have sub : ∀ g : WhateverFormula, g ∈ pathWForms L' → g ∈ pathWForms (X :: L') := by
      intro g hg; simp only [pathWForms_cons, Finset.mem_union]; exact Or.inr hg
    have of_Y : ∀ g : WhateverFormula, g ∈ Y.wForms → g ∈ pathWForms L' := by
      intro g hg; exact mem_pathWForms.mpr ⟨Y, Y_mem_L', hg⟩
    -- If the diamond occurs in the tail of the path, then we can use the IH:
    have tail_case : (~⌈α⌉φ : WhateverFormula) ∈ pathWForms L' →
        ∃ Fδ ∈ Dset α, (Yset Fδ φ).all
          (fun f => (f : WhateverFormula) ∈ pathWForms (X :: L')) := by
      intro hin
      rcases IH Y Y_in L' L'_in hin with ⟨Fδ, Fδ_in, hall⟩
      refine ⟨Fδ, Fδ_in, ?_⟩
      simp only [List.all_eq_true, decide_eq_true_eq] at hall ⊢
      exact fun f f_in => sub _ (hall f f_in)
    simp only [pathWForms_cons, Finset.mem_union] at hmem
    rcases hmem with hX | htail
    · rcases lra.wForms_negBox_preserved_or_unfolded Y_in (by rwa [← X_def]) with
        hkeep | ⟨Fδ, Fδ_in, hall⟩
      · exact tail_case (of_Y _ hkeep)
      · refine ⟨Fδ, Fδ_in, ?_⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hall ⊢
        exact fun f f_in => sub _ (of_Y _ (hall f f_in))
    · exact tail_case htail
  case sim X bas =>
    intro L L_in hmem
    rw [LocalTableau.mem_paths_sim] at L_in
    subst L_in
    simp only [pathWForms_cons, pathWForms_nil, Finset.union_empty] at hmem
    exact absurd (Sequent.isAtomic_of_basic_of_negBox_mem_wForms bas hmem) notAtom

/-- Along any path in a local tableau, a non-atomic loaded diamond must be unfolded:
if `~'⌊α⌋ξ` occurs (loaded) somewhere on the path and `α` is not atomic, then the results of
one application of the corresponding `LoadRule` occur on the path as well.
This is the loaded analogue of `LocalTableau.paths_freeUnfoldDia`. -/
lemma LocalTableau.paths_loadUnfoldDia {X} {lt : LocalTableau X} {α} {ξ : AnyFormula}
    (notAtom : ¬ α.isAtomic) :
    ∀ L ∈ lt.paths, (WhateverFormula.negLoad (~'⌊α⌋ξ)) ∈ pathWForms L →
      ∃ ress, Nonempty (LoadRule (~'⌊α⌋ξ) ress) ∧ ∃ Fo ∈ ress,
        Fo.1.sort.all (fun f => (f : WhateverFormula) ∈ pathWForms L)
        ∧ Fo.2.toList.all
            (fun nl => (WhateverFormula.negLoad nl) ∈ pathWForms L) := by
  induction lt
  case byLocalRule X lra X_def next IH =>
    intro L L_in hmem
    rw [LocalTableau.mem_paths_byLocalRule] at L_in
    rcases L_in with ⟨Y, Y_in, L', L'_in, rfl⟩
    have Y_mem_L' : Y ∈ L' := by
      have := LocalTableau.pathsHead_eq_self L'_in
      rw [← this]
      exact List.head_mem _
    have sub : ∀ g : WhateverFormula, g ∈ pathWForms L' → g ∈ pathWForms (X :: L') := by
      intro g hg; simp only [pathWForms_cons, Finset.mem_union]; exact Or.inr hg
    have of_Y : ∀ g : WhateverFormula, g ∈ Y.wForms → g ∈ pathWForms L' := by
      intro g hg; exact mem_pathWForms.mpr ⟨Y, Y_mem_L', hg⟩
    -- If the diamond occurs in the tail of the path, then we can use the IH:
    have tail_case : (WhateverFormula.negLoad (~'⌊α⌋ξ)) ∈ pathWForms L' →
        ∃ ress, Nonempty (LoadRule (~'⌊α⌋ξ) ress) ∧ ∃ Fo ∈ ress,
          Fo.1.sort.all (fun f => (f : WhateverFormula) ∈ pathWForms (X :: L'))
          ∧ Fo.2.toList.all
              (fun nl => (WhateverFormula.negLoad nl) ∈ pathWForms (X :: L')) := by
      intro hin
      rcases IH Y Y_in L' L'_in hin with ⟨ress, hress, Fo, Fo_in, hall, hall2⟩
      refine ⟨ress, hress, Fo, Fo_in, ?_, ?_⟩
      all_goals
        simp only [List.all_eq_true, decide_eq_true_eq] at hall hall2 ⊢
      · exact fun f f_in => sub _ (hall f f_in)
      · exact fun f f_in => sub _ (hall2 f f_in)
    simp only [pathWForms_cons, Finset.mem_union] at hmem
    rcases hmem with hX | htail
    · rcases lra.wForms_negLoad_preserved_or_unfolded Y_in (by rwa [← X_def]) with
        hkeep | ⟨ress, hress, Fo, Fo_in, hall, hall2⟩
      · exact tail_case (of_Y _ hkeep)
      · refine ⟨ress, hress, Fo, Fo_in, ?_, ?_⟩
        all_goals
          simp only [List.all_eq_true, decide_eq_true_eq] at hall hall2 ⊢
        · exact fun f f_in => sub _ (of_Y _ (hall f f_in))
        · exact fun f f_in => sub _ (of_Y _ (hall2 f f_in))
    · exact tail_case htail
  case sim X bas =>
    intro L L_in hmem
    rw [LocalTableau.mem_paths_sim] at L_in
    subst L_in
    simp only [pathWForms_cons, pathWForms_nil, Finset.union_empty] at hmem
    exact absurd (Sequent.isAtomic_of_basic_of_negLoad_mem_wForms bas hmem) notAtom

/-! ## Paths ending at a given end node

In the completeness proof (see `Pdl/BuildTree.lean`) Builder picks one end node of a local
tableau, and only the paths ending at that end node should be used as pre-states. -/

/-- The paths of a local tableau that end at a given node. -/
def LocalTableau.pathsTo {X} (lt : LocalTableau X) (Y : Sequent) : Finset (List Sequent) :=
  lt.paths.filter (fun p => p.getLast? = some Y)

@[simp]
lemma LocalTableau.mem_pathsTo {X} {lt : LocalTableau X} {Y p} :
    p ∈ lt.pathsTo Y ↔ p ∈ lt.paths ∧ p.getLast? = some Y := by
  simp [pathsTo]

/-- There is at least one path to each end node. -/
lemma LocalTableau.pathsTo_ne_nil {X} {lt : LocalTableau X} {Y} (h : Y ∈ endNodesOf lt) :
    lt.pathsTo Y ≠ {} := by
  rw [← LocalTableau.pathsLast_eq_endNodes] at h
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at h
  rcases h with ⟨L, L_in, rfl⟩
  intro hcon
  have L_in_pathsTo : L ∈ lt.pathsTo (L.getLast (LocalTableau.paths_mem_nonempty lt L L_in)) := by
    simp only [LocalTableau.mem_pathsTo]
    exact ⟨L_in, List.getLast?_eq_some_getLast _⟩
  rw [hcon] at L_in_pathsTo
  simp at L_in_pathsTo

/-- All end nodes of a local tableau for a free sequent are free.
Consequence of `LocalRuleApp.preserve_free`. -/
lemma LocalTableau.endNodesOf_free {X} (lt : LocalTableau X) (hfree : X.O = none) :
    ∀ Y ∈ endNodesOf lt, Y.O = none := by
  induction lt
  case byLocalRule X lra X_def next IH =>
    intro Y hY
    rw [endNodesOf] at hY
    simp only [Finset.sup_image, Function.id_comp, Finset.mem_sup, Finset.mem_attach, true_and,
      Subtype.exists] at hY
    rcases hY with ⟨Z, Z_in, hY⟩
    have hO : lra.O = none := by rw [X_def] at hfree; simpa [LocalRuleApp.X] using hfree
    exact IH Z Z_in (lra.preserve_free hO Z Z_in) Y hY
  case sim X bas =>
    intro Y hY
    simp only [endNodesOf, Finset.mem_singleton] at hY
    subst hY
    exact hfree

/-! ## Atomic loaded diamonds are preserved

A loaded diamond `~'⌊·a⌋ξ` with an *atomic* program cannot be "used up" by a local rule:
the only `LoadRule` applicable to it gives back the very same loaded formula.
This is the counterpart of `LocalTableau.paths_loadUnfoldDia` for atomic programs. -/

/-- The only `LoadRule` result for an atomic loaded diamond is the loaded diamond itself. -/
lemma LoadRule.atomic_ress_eq {a : Nat} {ξ : AnyFormula} {ress}
    (lr : LoadRule (~'⌊·a⌋ξ) ress) : ress = {({}, some (~'⌊·a⌋ξ))} := by
  cases ξ
  case normal φ =>
    rw [lr.eq_unfoldDiamondLoaded']
    simp [unfoldDiamondLoaded', Dset, YsetLoad', splitLast]
  case loaded χ =>
    rw [lr.eq_unfoldDiamondLoaded]
    simp [unfoldDiamondLoaded, Dset, YsetLoad, LoadFormula.boxes]

/-- A local rule application preserves an atomic loaded diamond. -/
lemma LocalRuleApp.preserve_negLoad_atomic_down (lra : LocalRuleApp) {a : Nat} {ξ : AnyFormula}
    (h : (WhateverFormula.negLoad (~'⌊·a⌋ξ)) ∈ lra.X.wForms) :
    ∀ Y ∈ lra.C, (WhateverFormula.negLoad (~'⌊·a⌋ξ)) ∈ Y.wForms := by
  intro Y Y_in
  rcases lra.wForms_negLoad_preserved_or_unfolded Y_in h with hkeep | ⟨ress, ⟨lr⟩, Fo, Fo_in, _, h2⟩
  · exact hkeep
  · rw [lr.atomic_ress_eq] at Fo_in
    simp only [Finset.mem_singleton] at Fo_in
    subst Fo_in
    simpa using h2

/-- An atomic loaded diamond anywhere in a local tableau path still occurs at the end of it.
Analogous to `LocalTableau.paths_basic_mem_last`, but for the loaded formula. -/
lemma LocalTableau.paths_negLoad_atomic_mem_last {X} {lt : LocalTableau X} {L}
    (L_in : L ∈ lt.paths) {a : Nat} {ξ : AnyFormula}
    (hmem : (WhateverFormula.negLoad (~'⌊·a⌋ξ)) ∈ pathWForms L) :
    (WhateverFormula.negLoad (~'⌊·a⌋ξ))
      ∈ (L.getLast (LocalTableau.paths_mem_nonempty lt L L_in)).wForms := by
  refine LocalTableau.mem_last_of_preserved Sequent.wForms _ ?_ L L_in (mem_pathWForms.mp hmem)
  intro lra Y Y_in hf
  exact lra.preserve_negLoad_atomic_down hf Y Y_in

/-- The last node of a path in a local tableau for a *free* sequent is free.
Consequence of `LocalTableau.endNodesOf_free`. -/
lemma LocalTableau.paths_last_free {X} {lt : LocalTableau X} (hfree : X.O = none) {L}
    (L_in : L ∈ lt.paths) :
    (L.getLast (LocalTableau.paths_mem_nonempty lt L L_in)).O = none := by
  refine LocalTableau.endNodesOf_free lt hfree _ ?_
  rw [← LocalTableau.pathsLast_eq_endNodes]
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
  exact ⟨L, L_in, rfl⟩

end PDL
