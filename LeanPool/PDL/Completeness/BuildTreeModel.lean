/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

import LeanPool.PDL.Completeness.BuildTree

/-! # From winning strategies to model graphs, part 2: the model graph (Section 6.3)

This continues `Pdl/BuildTree.lean`. Here we define the model graph `BuildTree.toModel`
obtained from a `BuildTree` (Definition 6.17) and provide the infrastructure that is used
in `Pdl/BuildTreeExistence.lean` to prove the existence lemmas.
-/

namespace PDL

/-! ## Defining The Model Graph -/

/-- Definition 6.17 to get model graph from strategy tree. -/
@[simp]
def BuildTree.toModel {X} (bt : BuildTree [] X) :
    (Σ W : Finset (Finset Formula), KripkeModel W) :=
  ⟨ bt.collect.attach.image PreState.forms -- W -- NOTE .forms here, not .wforms
  , { val := fun X p => Formula.atom_prop p ∈ X.1 -- valuation V(p)
    , Rel := fun a X Y => -- relation Rₐ
        ∃ φ, (~⌈·a⌉φ) ∈ X.1 ∧ X.1.pdlProjection a ∪ {~φ} ⊆ Y.1 }⟩

/-- Helper lemma saying (the formula sets of) all pre-states are in the model graph. -/
lemma PreState.mem_toModel {X : Sequent} {bt : BuildTree [] X} {π : PreState bt} :
    π.forms ∈ bt.toModel.fst := by
  simp only [BuildTree.toModel]
  exact Finset.mem_image.mpr ⟨π, Finset.mem_attach _ _, rfl⟩

instance {bt : BuildTree [] X} : Coe (PreState bt) { w : Finset Formula // w ∈ bt.toModel.1 } :=
  ⟨fun π => ⟨π.forms, π.mem_toModel⟩⟩

/-! ## Infrastructure for the existence lemmas

The existence lemmas 6.18, 6.19 and 6.20 all have the same shape: given a pre-state `π` and a
(possibly loaded) diamond in it, find another pre-state `ρ` that is reached from `π` by the
corresponding `Q` relation. All of them are proven by *walking through the `BuildTree`*:
we go to the last node of `π` (which is basic), apply some `PdlRule`s there, and then pick a
pre-state collected at the node we arrive at. The lemmas in this section provide the tools
for these steps. -/

/-- The world of the model graph given by a pre-state. -/
def PreState.toW {X} {bt : BuildTree [] X} (π : PreState bt) :
    { w : Finset Formula // w ∈ bt.toModel.1 } := ⟨π.forms, π.mem_toModel⟩

@[simp]
lemma PreState.toW_val {X} {bt : BuildTree [] X} (π : PreState bt) : π.toW.val = π.forms := rfl

/-- Unfolding the atomic accessibility relation of `BuildTree.toModel`. -/
lemma PreState.rel_iff {X} {bt : BuildTree [] X} {π ρ : PreState bt} {a : Nat} :
    bt.toModel.2.Rel a π.toW ρ.toW
    ↔ ∃ φ, (~⌈·a⌉φ) ∈ π.forms ∧ π.forms.pdlProjection a ∪ {~φ} ⊆ ρ.forms :=
  Iff.rfl

/-! ### Set-equal sequents

Since the refactoring that makes `Sequent` use `Finset`s, being set-equal is the same as
being equal, so the two lemmas that used to be here are now trivial and hence removed:

- `Sequent.bothSides_toFinset_eq_of_setEqTo` is now just `congrArg Sequent.toFinset`.
- `AnyNegFormula.mem_Sequent_of_setEqTo` is now just rewriting with the equality.
-/

/-! ### Formulas of a pre-state -/

lemma PreState.mem_forms_of_mem {H X} {bt : BuildTree H X} {π : PreState bt} {Z : Sequent}
    (hZ : Z ∈ π.val) {f : Formula} (hf : f ∈ Z.toFinset) : f ∈ π.forms :=
  PreState.mem_forms.mpr ⟨Z, hZ, hf⟩

lemma PreState.mem_wForms_of_mem {H X} {bt : BuildTree H X} {π : PreState bt} {Z : Sequent}
    (hZ : Z ∈ π.val) {f : WhateverFormula} (hf : f ∈ Z.wForms) : f ∈ π.wForms :=
  PreState.mem_wForms.mpr ⟨Z, hZ, hf⟩

/-- The last sequent of a pre-state is one of its sequents. -/
lemma PreState.getLast_mem {H X} {bt : BuildTree H X} (π : PreState bt) :
    π.val.getLast PreState.nonempty ∈ π.val :=
  List.getLast_mem _

/-- A pre-state "has" an `AnyNegFormula` if one of its sequents contains it. -/
def PreState.hasAnf {H X} {bt : BuildTree H X} (π : PreState bt) (anf : AnyNegFormula) : Prop :=
  ∃ Z ∈ π.val, AnyNegFormula.memSequent Z anf

/-- If a pre-state has `~''ξ` then the *unloaded* formula `~ξ.unload` is among its formulas. -/
lemma PreState.mem_forms_of_hasAnf {H X} {bt : BuildTree H X} {π : PreState bt} {ξ : AnyFormula}
    (h : π.hasAnf (~''ξ)) : (~ ξ.unload) ∈ π.forms := by
  rcases h with ⟨Z, Z_in, hZ⟩
  refine PreState.mem_forms_of_mem Z_in ?_
  rcases Z with ⟨L, R, O⟩
  rcases ξ with φ | χ
  · unfold AnyNegFormula.memSequent at hZ
    simp only [Sequent.mem_def, Sequent.L_eq, Sequent.R_eq] at hZ
    simp only [AnyFormula.unload]
    rcases hZ with h | h <;> simp [Sequent.toFinset, h]
  · unfold AnyNegFormula.memSequent at hZ
    simp only at hZ
    simp only [AnyFormula.unload]
    rcases hZ with rfl | rfl <;> simp [Sequent.toFinset]

/-! ### Walking down the `BuildTree` -/

/-- The sub-`BuildTree` reached by a `Match` is not bigger than the whole tree. -/
lemma Match.btAt_size_le {H X} {bt : BuildTree H X} (m : Match bt) :
    m.btAt.2.2.size ≤ bt.size := by
  induction m with
  | nil => exact le_refl _
  | @loc H X nbas someLT next lt tail IH =>
    exact le_trans IH (le_of_lt (BuildTree.size_lt_loc H X nbas next lt someLT))
  | @pdl H X bas someR next Y r tail IH =>
    exact le_trans IH (le_of_lt (BuildTree.size_lt_pdl H X bas someR next Y r))

/-- If a `PdlRule` is applicable at the root of a `BuildTree` that is basic and not a free
repeat, then the tree has a corresponding child, reached by a one-step `Match`. -/
lemma BuildTree.exists_match_of_pdlRule {H Z} (bt : BuildTree H Z) (bas : Z.basic)
    (nfr : ¬ bt.isFreeRepeat) {Y} (r : PdlRule Z Y) :
    ∃ m : Match bt, m.btAt.2.1 = Y ∧ m.btAt.2.2.size < bt.size := by
  cases bt
  case loc nbas someLT next => exact absurd bas nbas
  case pdl bas' someR next =>
    exact ⟨Match.pdl (Y := Y) (r := r) Match.nil, rfl,
      BuildTree.size_lt_pdl H Z bas' someR next Y r⟩
  case freeRepeat fr => exact absurd trivial nfr
  case openLeaf bas' noRule =>
    exfalso
    have := PdlRule.all_spec bas r
    rw [noRule] at this
    simp at this

/-- Making a `PdlRule` step at the end of a `Match`: we get a longer `Match` that ends at the
child sequent, and the sub-`BuildTree` we reach is strictly smaller. -/
lemma Match.exists_step {H X} {bt : BuildTree H X} (m : Match bt) (bas : m.endSeq.basic)
    (nfr : ¬ m.btAt.2.2.isFreeRepeat) {Y} (r : PdlRule m.endSeq Y) :
    ∃ m' : Match bt, m'.endSeq = Y ∧ m'.btAt.2.2.size < m.btAt.2.2.size := by
  obtain ⟨m2, hm2, hsize⟩ := BuildTree.exists_match_of_pdlRule m.btAt.2.2 bas nfr r
  exact ⟨m.append m2, by rw [Match.endSeq, Match.btAt_append]; exact hm2,
    by rw [Match.btAt_append]; exact hsize⟩

/-- A `Match` ending in a *loaded* sequent is never at a free repeat. -/
lemma Match.not_isFreeRepeat_of_loaded {H X} {bt : BuildTree H X} {m : Match bt}
    (hl : m.endSeq.isLoaded) : ¬ m.btAt.2.2.isFreeRepeat := by
  intro h
  exact absurd hl (by simpa using! (BuildTree.getFreeRepeat h).2.2)

/-- Any `Match` can be replaced by one that ends at the same sequent and is not at a free
repeat: if we are at a free repeat we go to its companion, which is strictly shorter. -/
lemma Match.exists_setEqTo_not_freeRepeat {X} {bt : BuildTree [] X} (m : Match bt) :
    ∃ m' : Match bt, m'.endSeq = m.endSeq ∧ ¬ m'.btAt.2.2.isFreeRepeat := by
  by_cases h : m.isFreeRepeat
  · obtain ⟨m', h1, h2⟩ := (m.companionOf h).exists_setEqTo_not_freeRepeat
    exact ⟨m', h1.trans (m.companionOf_setEqTo_sequent h), h2⟩
  · exact ⟨m, rfl, fun hc => h (Match.isFreeRepeat_iff.mpr hc)⟩
termination_by m.length
decreasing_by exact m.companionOf_length_lt h

/-- At the end of a `Match` that is not a free repeat we find a pre-state that starts with the
sequent we are at, and whose own last sequent is reached by a `Match` that goes no higher up. -/
lemma Match.exists_preState_of_not_freeRepeat {X} {bt : BuildTree [] X} (m : Match bt)
    (nfr : ¬ m.btAt.2.2.isFreeRepeat) :
    ∃ ρ : PreState bt, m.endSeq ∈ ρ.val ∧ ∃ mρ : Match bt,
      mρ.endSeq = ρ.val.getLast PreState.nonempty
      ∧ mρ.btAt.2.2.size ≤ m.btAt.2.2.size := by
  obtain ⟨p, p_in, root_in⟩ := m.btAt.2.2.collect_contains_root_of_not_freeRepeat nfr
  refine ⟨⟨p, m.collect_btAt_subset p p_in⟩, root_in, ?_⟩
  obtain ⟨m2, hm2⟩ := PreState.exists_match_endSeq_eq_last (bt := m.btAt.2.2) ⟨p, p_in⟩
  refine ⟨m.append m2, ?_, ?_⟩
  · rw [Match.endSeq_append]; exact hm2
  · rw [Match.btAt_append]; exact m2.btAt_size_le

/-! ### Free pre-states -/

/-- Version of `BuildTree.collect_contains_root_of_not_freeRepeat` saying that the root sequent
is the *first* sequent of the collected pre-state. -/
lemma BuildTree.collect_contains_root_head_of_not_freeRepeat {H X} (bt : BuildTree H X)
    (h : ¬ bt.isFreeRepeat) : ∃ p ∈ bt.collect, p.head? = some X := by
  cases bt
  case loc nbas someLT next =>
    rcases List.exists_mem_of_ne_nil _ someLT with ⟨lt, lt_in⟩
    rcases Finset.nonempty_iff_ne_empty.mpr
      (LocalTableau.pathsTo_ne_nil (lt := lt.1) (Y := (next lt).4) BuildChoice.frth_mem)
      with ⟨p, p_in⟩
    refine ⟨p, BuildTree.mem_collect_loc.mpr ⟨lt, lt_in, Or.inl p_in⟩, ?_⟩
    rw [LocalTableau.mem_pathsTo] at p_in
    have hhead := @LocalTableau.pathsHead_eq_self X lt.1 p p_in.1
    rw [List.head?_eq_some_head (LocalTableau.paths_mem_nonempty lt.1 p p_in.1), hhead]
  case freeRepeat fr =>
    simp [BuildTree.isFreeRepeat] at h
  all_goals
    exact ⟨[X], by simp, by simp⟩

/-- If the first sequent of a pre-state is free then so is its last sequent.
(Generalised to an arbitrary history `H`, as needed for the recursion.) -/
lemma PreState.O_getLast_eq_none {H X} {bt : BuildTree H X} (π : PreState bt)
    (h : (π.val.head PreState.nonempty).O = none) :
    (π.val.getLast PreState.nonempty).O = none := by
  rcases π with ⟨p, p_in⟩
  cases bt <;> simp only [BuildTree.collect, ne_eq, Finset.mem_sup, List.mem_toFinset,
    Finset.mem_union, LocalTableau.mem_pathsTo, Finset.singleton_union, Finset.mem_insert,
    Sigma.exists, Finset.notMem_empty, Finset.mem_singleton] at p_in <;> rename_i p_in_old
  case loc nbas someLT next =>
    rcases p_in with ⟨lt, lt_in, p_in_lt | p_in_next⟩
    · have hhead := LocalTableau.pathsHead_eq_self p_in_lt.1
      exact LocalTableau.paths_last_free (by rw [← hhead]; exact h) p_in_lt.1
    · exact @PreState.O_getLast_eq_none _ _ (next lt).6 ⟨p, p_in_next⟩ h
  case pdl bas someR next =>
    rcases p_in with p_def | ⟨Y, r, in_rule, p_in_next⟩
    · subst p_def; simpa using h
    · exact @PreState.O_getLast_eq_none _ _ (next Y r) ⟨p, p_in_next⟩ h
  case openLeaf bas noRule =>
    subst p_in; simpa using h
termination_by
  bt.size
decreasing_by
  · subst_eqs
    apply @BuildTree.size_lt_loc H X
  · subst_eqs
    apply @BuildTree.size_lt_pdl H X

/-- Version of `Match.exists_preState_of_not_freeRepeat` where the pre-state *starts* at the
sequent we are at. -/
lemma Match.exists_preState_head_of_not_freeRepeat {X} {bt : BuildTree [] X} (m : Match bt)
    (nfr : ¬ m.btAt.2.2.isFreeRepeat) :
    ∃ ρ : PreState bt, ρ.val.head PreState.nonempty = m.endSeq ∧ ∃ mρ : Match bt,
      mρ.endSeq = ρ.val.getLast PreState.nonempty := by
  obtain ⟨p, p_in, hhead⟩ := m.btAt.2.2.collect_contains_root_head_of_not_freeRepeat nfr
  have hne : p ≠ [] := by intro hc; rw [hc] at hhead; simp at hhead
  refine ⟨⟨p, m.collect_btAt_subset p p_in⟩, ?_, ?_⟩
  · rw [List.head?_eq_some_head hne] at hhead
    exact Option.some.inj hhead
  · obtain ⟨m2, hm2⟩ := PreState.exists_match_endSeq_eq_last (bt := m.btAt.2.2) ⟨p, p_in⟩
    exact ⟨m.append m2, by rw [Match.endSeq_append]; exact hm2⟩

/-! ### The modal rule -/

/-- What the modal rule `(M)` gives us on the left: the child contains `~''ξ` and all
`a`-successors of the boxes in the parent, and it is loaded whenever `ξ` is. -/
lemma PdlRule.exists_modL {L R : Finset Formula} {a : Nat} {ξ : AnyFormula} :
    ∃ Y, Nonempty (PdlRule ⟨L, R, some (Sum.inl (~'⌊·a⌋ξ))⟩ Y)
      ∧ AnyNegFormula.memSequent Y (~''ξ)
      ∧ (∀ f, (⌈·a⌉f) ∈ L ∪ R → f ∈ Y.toFinset)
      ∧ (∀ χ, ξ = .loaded χ → Y.isLoaded) := by
  cases ξ
  case normal φ =>
    refine ⟨⟨{~φ} ∪ L.pdlProjection a, R.pdlProjection a, none⟩, ⟨PdlRule.modL rfl rfl⟩, ?_, ?_, ?_⟩
    · simp [AnyNegFormula.memSequent]
    · intro f hf
      simp only [Finset.mem_union] at hf
      simp only [Sequent.toFinset, Finset.mem_union]
      rcases hf with h | h
      · have h1 : f ∈ L.pdlProjection a := Finset.mem_projection.mpr h
        tauto
      · have h1 : f ∈ R.pdlProjection a := Finset.mem_projection.mpr h
        tauto
    · intro χ h; exact absurd h (by simp)
  case loaded χ =>
    refine ⟨⟨L.pdlProjection a, R.pdlProjection a, some (Sum.inl (~'χ))⟩, ⟨PdlRule.modL rfl rfl⟩,
      ?_, ?_, ?_⟩
    · exact Or.inl rfl
    · intro f hf
      simp only [Finset.mem_union] at hf
      simp only [Sequent.toFinset, Finset.mem_union]
      rcases hf with h | h
      · have h1 : f ∈ L.pdlProjection a := Finset.mem_projection.mpr h
        tauto
      · have h1 : f ∈ R.pdlProjection a := Finset.mem_projection.mpr h
        tauto
    · intro _ _; simp [Sequent.isLoaded]

/-- What the modal rule `(M)` gives us on the right. Mirrors `PdlRule.exists_modL`. -/
lemma PdlRule.exists_modR {L R : Finset Formula} {a : Nat} {ξ : AnyFormula} :
    ∃ Y, Nonempty (PdlRule ⟨L, R, some (Sum.inr (~'⌊·a⌋ξ))⟩ Y)
      ∧ AnyNegFormula.memSequent Y (~''ξ)
      ∧ (∀ f, (⌈·a⌉f) ∈ L ∪ R → f ∈ Y.toFinset)
      ∧ (∀ χ, ξ = .loaded χ → Y.isLoaded) := by
  cases ξ
  case normal φ =>
    refine ⟨⟨L.pdlProjection a, {~φ} ∪ R.pdlProjection a, none⟩, ⟨PdlRule.modR rfl rfl⟩, ?_, ?_, ?_⟩
    · simp [AnyNegFormula.memSequent]
    · intro f hf
      simp only [Finset.mem_union] at hf
      simp only [Sequent.toFinset, Finset.mem_union]
      rcases hf with h | h
      · have h1 : f ∈ L.pdlProjection a := Finset.mem_projection.mpr h
        tauto
      · have h1 : f ∈ R.pdlProjection a := Finset.mem_projection.mpr h
        tauto
    · intro χ h; exact absurd h (by simp)
  case loaded χ =>
    refine ⟨⟨L.pdlProjection a, R.pdlProjection a, some (Sum.inr (~'χ))⟩, ⟨PdlRule.modR rfl rfl⟩,
      ?_, ?_, ?_⟩
    · exact Or.inr rfl
    · intro f hf
      simp only [Finset.mem_union] at hf
      simp only [Sequent.toFinset, Finset.mem_union]
      rcases hf with h | h
      · have h1 : f ∈ L.pdlProjection a := Finset.mem_projection.mpr h
        tauto
      · have h1 : f ∈ R.pdlProjection a := Finset.mem_projection.mpr h
        tauto
    · intro χ' h; simp [Sequent.isLoaded]

/-- An atomic loaded diamond in a pre-state occurs already in its last sequent.
This is the loaded analogue of `PreState.mem_bothSides_getLast_of_basic` and the reason why
the modal rule is applicable at the end of the pre-state.
(Generalised from `bt : BuildTree [] X` to an arbitrary history `H`, as needed for the
recursion into sub-`BuildTree`s.) -/
lemma PreState.negLoad_atomic_mem_getLast {H X} {bt : BuildTree H X} {π : PreState bt}
    {a : Nat} {ξ : AnyFormula}
    (h : (WhateverFormula.negLoad (~'⌊·a⌋ξ)) ∈ π.wForms) :
    (WhateverFormula.negLoad (~'⌊·a⌋ξ)) ∈ (π.val.getLast PreState.nonempty).wForms := by
  rcases π with ⟨p, p_in⟩
  simp only [PreState.wForms] at h
  cases bt <;> simp only [BuildTree.collect, ne_eq, Finset.mem_sup, List.mem_toFinset,
    Finset.mem_union, LocalTableau.mem_pathsTo, Finset.singleton_union, Finset.mem_insert,
    Sigma.exists, Finset.notMem_empty, Finset.mem_singleton] at p_in <;> rename_i p_in_old
  case loc nbas someLT next =>
    rcases p_in with ⟨lt, lt_in, p_in_lt | p_in_next⟩
    · exact LocalTableau.paths_negLoad_atomic_mem_last p_in_lt.1 h
    · exact @PreState.negLoad_atomic_mem_getLast _ _ (next lt).6 ⟨p, p_in_next⟩ a ξ
        (by simpa [PreState.wForms] using h)
  case pdl bas someR next =>
    rcases p_in with p_def | ⟨Y, r, in_rule, p_in_next⟩
    · subst p_def
      simpa using h
    · exact @PreState.negLoad_atomic_mem_getLast _ _ (next Y r) ⟨p, p_in_next⟩ a ξ
        (by simpa [PreState.wForms] using h)
  case openLeaf bas noRule =>
    subst p_in
    simpa using h
termination_by
  bt.size
decreasing_by
  · subst_eqs
    apply @BuildTree.size_lt_loc H X
  · subst_eqs
    apply @BuildTree.size_lt_pdl H X

lemma PreState.exists_mem_of_mem_wForms {H X} {bt : BuildTree H X} {π : PreState bt}
    {f : WhateverFormula} (h : f ∈ π.wForms) : ∃ Z ∈ π.val, f ∈ Z.wForms := by
  exact PreState.mem_wForms.mp h

@[simp]
lemma PreState.hasAnf_loaded_iff {H X} {bt : BuildTree H X} {π : PreState bt} {χ : LoadFormula} :
    π.hasAnf (~''(AnyFormula.loaded χ)) ↔ (WhateverFormula.negLoad (~'χ)) ∈ π.wForms := by
  constructor
  · rintro ⟨Z, Z_in, hZ⟩
    refine PreState.mem_wForms_of_mem Z_in ?_
    rcases Z with ⟨L, R, O⟩
    rw [Sequent.mem_wForms_negLoad_iff]
    simpa using! hZ
  · intro h
    obtain ⟨Z, Z_in, hZ⟩ := PreState.exists_mem_of_mem_wForms h
    refine ⟨Z, Z_in, ?_⟩
    rcases Z with ⟨L, R, O⟩
    rw [Sequent.mem_wForms_negLoad_iff] at hZ
    simpa using! hZ

@[simp]
lemma PreState.hasAnf_normal_iff {H X} {bt : BuildTree H X} {π : PreState bt} {φ : Formula} :
    π.hasAnf (~''(AnyFormula.normal φ)) ↔ ((~φ : WhateverFormula) ∈ π.wForms) := by
  constructor
  · rintro ⟨Z, Z_in, hZ⟩
    refine PreState.mem_wForms_of_mem Z_in ?_
    rcases Z with ⟨L, R, O⟩
    rw [Sequent.mem_wForms_normal_iff]
    simpa using! hZ
  · intro h
    obtain ⟨Z, Z_in, hZ⟩ := PreState.exists_mem_of_mem_wForms h
    refine ⟨Z, Z_in, ?_⟩
    rcases Z with ⟨L, R, O⟩
    rw [Sequent.mem_wForms_normal_iff] at hZ
    simpa using! hZ

/-- A normal formula in `π.wForms` is also in `π.forms`. -/
lemma PreState.mem_forms_of_mem_wForms {H X} {bt : BuildTree H X} {π : PreState bt} {φ : Formula}
    (h : (φ : WhateverFormula) ∈ π.wForms) : φ ∈ π.forms :=
  PreState.mem_forms_iff.mpr (Or.inl h)

/-! ### The modal step -/

lemma Sequent.isLoaded_of_negLoad_mem {Z : Sequent} {nlf : NegLoadFormula}
    (h : NegLoadFormula.memSequent Z nlf) : Z.isLoaded := by
  rcases Z with ⟨L, R, O⟩
  simp only [NegLoadFormula.memSequent, Sequent.O_eq] at h
  rcases h with rfl | rfl <;> simp [Sequent.isLoaded]

/-- An atomic box in a sequent is on the left or on the right
(it cannot come from the loaded formula, which is always negated). -/
lemma Sequent.box_mem_LR_of_mem_toFinset {Z : Sequent} {a : Nat} {f : Formula}
    (h : (⌈·a⌉f) ∈ Z.toFinset) : (⌈·a⌉f) ∈ Z.L ∪ Z.R := by
  rcases Z with ⟨L, R, O⟩
  rcases O with _ | (⟨χ⟩ | ⟨χ⟩) <;>
    simp_all [Sequent.toFinset, negUnload]

lemma LoadFormula.box_unload {α : Program} {ξ : AnyFormula} :
    (LoadFormula.box α ξ).unload = ⌈α⌉ξ.unload := by
  cases ξ <;> simp [AnyFormula.unload]

/-- The modal step at the end of a `Match`: if the sequent we are at is basic and loaded with
an *atomic* diamond `~'⌊·a⌋ξ`, then we can go one step down, arriving at a sequent that
contains `~''ξ` and all `a`-successors of the boxes we had. Formal version of the base case
of Lemma 6.18. -/
lemma Match.atomicLoadedStep {X} {bt : BuildTree [] X} (m : Match bt)
    (bas : m.endSeq.basic) {a : Nat} {ξ : AnyFormula}
    (hload : NegLoadFormula.memSequent m.endSeq (~'⌊·a⌋ξ)) :
    ∃ m' : Match bt, m'.btAt.2.2.size < m.btAt.2.2.size
      ∧ AnyNegFormula.memSequent m'.endSeq (~''ξ)
      ∧ (∀ f, (⌈·a⌉f) ∈ m.endSeq.L ∪ m.endSeq.R → f ∈ m'.endSeq.toFinset)
      ∧ (∀ χ, ξ = .loaded χ → m'.endSeq.isLoaded) := by
  have nfr : ¬ m.btAt.2.2.isFreeRepeat :=
    Match.not_isFreeRepeat_of_loaded (Sequent.isLoaded_of_negLoad_mem hload)
  obtain ⟨Y, ⟨r⟩, h1, h2, h3⟩ :
      ∃ Y, Nonempty (PdlRule m.endSeq Y) ∧ AnyNegFormula.memSequent Y (~''ξ)
        ∧ (∀ f, (⌈·a⌉f) ∈ m.endSeq.L ∪ m.endSeq.R → f ∈ Y.toFinset)
        ∧ (∀ χ, ξ = .loaded χ → Y.isLoaded) := by
    rcases hE : m.endSeq with ⟨L, R, O⟩
    rw [hE] at hload
    simp only [NegLoadFormula.memSequent, Sequent.O_eq] at hload
    simp only [Sequent.L_eq, Sequent.R_eq]
    rcases hload with rfl | rfl
    · exact PdlRule.exists_modL
    · exact PdlRule.exists_modR
  obtain ⟨m', hm'eq, hm'size⟩ := m.exists_step bas nfr r
  exact ⟨m', hm'size, hm'eq ▸ h1, fun f hf => hm'eq ▸ (h2 f hf), fun χ hχ => hm'eq ▸ (h3 χ hχ)⟩

/-- After any `Match` there is a pre-state containing a sequent set-equal to the sequent we
are at. If that sequent is loaded then the pre-state is found without going back up, so its
last node is not higher up than where we are. -/
lemma Match.exists_preState_setEqTo {X} {bt : BuildTree [] X} (m : Match bt) :
    ∃ (ρ : PreState bt) (Z : Sequent), Z ∈ ρ.val ∧ Z = m.endSeq
      ∧ ∃ mρ : Match bt, mρ.endSeq = ρ.val.getLast PreState.nonempty
        ∧ (m.endSeq.isLoaded → mρ.btAt.2.2.size ≤ m.btAt.2.2.size) := by
  by_cases hl : m.endSeq.isLoaded
  · obtain ⟨ρ, hmem, mρ, hmρ, hsize⟩ :=
      m.exists_preState_of_not_freeRepeat (Match.not_isFreeRepeat_of_loaded hl)
    exact ⟨ρ, m.endSeq, hmem, rfl, mρ, hmρ, fun _ => hsize⟩
  · obtain ⟨m'', hset, nfr''⟩ := m.exists_setEqTo_not_freeRepeat
    obtain ⟨ρ, hmem, mρ, hmρ, _⟩ := m''.exists_preState_of_not_freeRepeat nfr''
    exact ⟨ρ, m''.endSeq, hmem, hset, mρ, hmρ, fun hc => absurd hc hl⟩

/-- Lemma 6.18 for an *atomic* program: the base case of the induction.
If the last sequent of the pre-state `π` is loaded with `~'⌊·a⌋ξ`, then there is a pre-state
`ρ` with `(Λ⁻(π), Λ⁻(ρ)) ∈ Rₐ` that has `~''ξ`. Unless `ξ` is a normal formula (in which case
we may have to go back to a companion) the new pre-state also ends strictly below `π`. -/
lemma PreState.atomicLoadedStep {X} {bt : BuildTree [] X} (π : PreState bt) (mπ : Match bt)
    (hmπ : mπ.endSeq = π.val.getLast PreState.nonempty)
    {a : Nat} {ξ : AnyFormula}
    (hload : NegLoadFormula.memSequent (π.val.getLast PreState.nonempty) (~'⌊·a⌋ξ)) :
    ∃ (ρ : PreState bt) (mρ : Match bt),
      mρ.endSeq = ρ.val.getLast PreState.nonempty
      ∧ (mρ.btAt.2.2.size < mπ.btAt.2.2.size ∨ ∃ φ, ξ = AnyFormula.normal φ)
      ∧ bt.toModel.2.Rel a π.toW ρ.toW
      ∧ ρ.hasAnf (~''ξ) := by
  have bas : (mπ.endSeq).basic := by rw [hmπ]; exact PreState.forms_last_basic
  have hload' : NegLoadFormula.memSequent mπ.endSeq (~'⌊·a⌋ξ) := by rw [hmπ]; exact hload
  obtain ⟨m', hsize, hanf, hproj, hloadedY⟩ := mπ.atomicLoadedStep bas hload'
  obtain ⟨ρ, Z, hZmem, hZset, mρ, hmρ, hsize2⟩ := m'.exists_preState_setEqTo
  subst hZset
  have hρanf : ρ.hasAnf (~''ξ) := ⟨_, hZmem, hanf⟩
  have hZsides : ∀ f, f ∈ m'.endSeq.toFinset → f ∈ ρ.forms :=
    fun _ hf => PreState.mem_forms_of_mem hZmem hf
  refine ⟨ρ, mρ, hmρ, ?_, ?_, hρanf⟩
  · cases ξ
    case normal φ => exact Or.inr ⟨φ, rfl⟩
    case loaded χ => exact Or.inl (lt_of_le_of_lt (hsize2 (hloadedY χ rfl)) hsize)
  · refine ⟨ξ.unload, ?_, ?_⟩
    · refine PreState.mem_forms_of_mem π.getLast_mem ?_
      rcases hE : π.val.getLast PreState.nonempty with ⟨L, R, O⟩
      rw [hE] at hload
      simp only [NegLoadFormula.memSequent, Sequent.O_eq] at hload
      rcases hload with rfl | rfl <;>
        simp [Sequent.toFinset, LoadFormula.box_unload]
    · intro f hf
      simp only [PreState.toW_val, Finset.mem_union, Finset.mem_singleton] at hf
      rcases hf with hf | rfl
      · have hbox : (⌈·a⌉f) ∈ π.forms := Finset.mem_projection.mp hf
        have hlast := PreState.mem_bothSides_getLast_of_basic (φ := ⌈·a⌉f) (by simp) hbox
        refine hZsides f (hproj f ?_)
        rw [hmπ]
        exact Sequent.box_mem_LR_of_mem_toFinset hlast
      · exact PreState.mem_forms_of_hasAnf hρanf

/-! ### Unfolding a loaded diamond in a pre-state -/

/-- Unified version of the *loaded* case of Lemma 6.15, for an arbitrary `AnyFormula` `xi`:
if `~'⌊α⌋ξ` occurs in the pre-state `π` and `α` is not atomic, then for one of the unfoldings
`(F,δ) ∈ Dset α` all test formulas in `F` occur in `π` and `π` also has `~''⌊⌊δ⌋⌋ξ`. -/
lemma PreState.loadUnfold_of_nonAtom {H X} {bt : BuildTree H X} {π : PreState bt} {α}
    {ξ : AnyFormula} (α_notAtom : ¬ α.isAtomic)
    (h : (WhateverFormula.negLoad (~'⌊α⌋ξ)) ∈ π.wForms) :
    ∃ Fδ ∈ Dset α, (∀ f ∈ Fδ.1, (f : WhateverFormula) ∈ π.wForms)
      ∧ π.hasAnf (~''(AnyFormula.loadBoxes Fδ.2 ξ)) := by
  cases ξ
  case loaded χ =>
    obtain ⟨⟨F, δ⟩, Fδ_in, h1, h2⟩ := PreState.loadUnfoldDiaMem_of_nonAtom χ α_notAtom h
    simp only [List.all_eq_true, decide_eq_true_eq] at h1 h2
    refine ⟨⟨F, δ⟩, Fδ_in, h1, ?_⟩
    rw [AnyFormula.loadBoxes_loaded_eq_loaded_boxes, PreState.hasAnf_loaded_iff]
    exact h2 _ (by simp [YsetLoad])
  case normal φ =>
    obtain ⟨ress, ⟨lr⟩, Fo, Fo_in, h1, h2⟩ := PreState.loadUnfoldMem_of_nonAtom α_notAtom h
    rw [lr.eq_unfoldDiamondLoaded'] at Fo_in
    simp only [List.pdlToFinFinOpt, List.mem_toFinset, List.mem_map] at Fo_in
    rcases Fo_in with ⟨FO, FO_in, hFo⟩
    simp only [unfoldDiamondLoaded', List.mem_map] at FO_in
    rcases FO_in with ⟨⟨F, δ⟩, Fδ_in, rfl⟩
    subst hFo
    simp only [List.all_eq_true, decide_eq_true_eq, Finset.mem_sort, List.mem_toFinset] at h1
    simp only [List.all_eq_true, decide_eq_true_eq] at h2
    refine ⟨⟨F, δ⟩, Fδ_in, ?_, ?_⟩
    · intro f hf
      refine h1 f ?_
      rcases hδ : splitLast δ with _ | ⟨δ', β⟩ <;> simp [YsetLoad', hδ] <;> tauto
    · rcases hδ : splitLast δ with _ | ⟨δ', β⟩
      · have hnil : δ = [] := nil_of_splitLast_none hδ
        subst hnil
        simp only [AnyFormula.boxes_nil, PreState.hasAnf_normal_iff]
        exact h1 (~φ) (by simp [YsetLoad'])
      · have hd : δ' ++ [β] = δ := splitLast_undo_of_some hδ
        rw [← hd, ← loadMulti_eq_loadBoxes, PreState.hasAnf_loaded_iff]
        exact h2 _ (by simp [YsetLoad', hδ])

/-- A nonempty list of boxes always gives a loaded formula. -/
lemma AnyFormula.loadBoxes_ne_normal {γs : List Program} (h : γs ≠ []) {ξ : AnyFormula} {φ} :
    AnyFormula.loadBoxes γs ξ ≠ AnyFormula.normal φ := by
  cases γs with
  | nil => exact absurd rfl h
  | cons c cs => simp

/-! ### The `Q` relation for pre-states -/

/-- A negated loaded formula is in `Z.wForms` iff it is "in" the sequent `Z`. -/
lemma Sequent.negLoad_mem_wForms_iff {Z : Sequent} {nlf : NegLoadFormula} :
    (WhateverFormula.negLoad nlf) ∈ Z.wForms ↔ NegLoadFormula.memSequent Z nlf := by
  rcases Z with ⟨L, R, O⟩
  rw [Sequent.mem_wForms_negLoad_iff]
  simp [NegLoadFormula.memSequent]

/-- If all test formulas of `F` are in the pre-state `π`, then `Qsteps` from `π` gives `Qcombo`. -/
lemma PreState.qcombo_of_qsteps {X} {bt : BuildTree [] X} {F : List Formula} {δ : List Program}
    {π ρ : PreState bt} (hF : ∀ f ∈ F, (f : WhateverFormula) ∈ π.wForms)
    (h : Qsteps bt.toModel.2.Rel δ π.toW ρ.toW) :
    Qcombo bt.toModel.2.Rel F δ π.toW ρ.toW :=
  ⟨π.toW, ⟨ReflBEq.rfl, fun τ hτ => ⟨rfl, PreState.mem_forms_of_mem_wForms (hF τ hτ)⟩⟩, h⟩

end PDL
