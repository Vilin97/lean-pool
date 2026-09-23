/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.FischerLadner
public import LeanPool.PDL.Tableau

/-! # Staying inside the Fischer-Ladner closure

Here we define what it means for a `Sequent` to be inside the `FL` closure of another, and then
prove several helper lemmas to show that all rules of our tableau system stay in the closure.

The main two results are `LocalTableau.stays_in_FL` and `PdlRule.stays_in_FL`.

Intuitively, we want to say that each step from (L,R,O) in a tableau to (L',R',O') stays in the
FL of (L,R,O). To be precise, each side left/right stays within its own FL closure.
However, this does *not* mean that `L'` must be in the FL of `L`, because the `O` may also
contribute to the left part. This makes `Sequent.subseteqFL` tricky to define.
-/

@[expose] public section

namespace PDL

/-- Sequent `Y` is a component-wise subset of the FL-closure of `X`.
Note that by component we mean left and right (and not L, R, O).

WORRY: Is using Sequent.O.L here a problem because it might not be injective?
(Because it calls `unload` where both ⌊a⌋⌊b⌋p and ⌊a⌋⌈b⌉p become ⌈a⌉⌈b⌉p.)
-/
def Sequent.subseteqFL (X : Sequent) (Y : Sequent) : Prop :=
      X.L   ⊆ (Y.L ∪ Y.O.L).FL
    ∧ X.O.L ⊆ (Y.L ∪ Y.O.L).FL
    ∧ X.R   ⊆ (Y.R ∪ Y.O.R).FL
    ∧ X.O.R ⊆ (Y.R ∪ Y.O.R).FL

@[simp]
lemma Sequent.subseteq_FL_refl (X : Sequent) : X.subseteqFL X := by
  rcases X with ⟨L,R,O⟩
  simp only [subseteqFL, L_eq, O_eq, Finset.FL_union_eq, R_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro φ φ_in <;> simp_all only [Finset.mem_union]
  · left; apply Finset.FL_refl_sub φ_in
  · right; apply Finset.FL_refl_sub φ_in
  · left; apply Finset.FL_refl_sub φ_in
  · right; apply Finset.FL_refl_sub φ_in

lemma Sequent.subseteq_FL_trans (X Y Z : Sequent) :
    X.subseteqFL Y → Y.subseteqFL Z → X.subseteqFL Z := by
  intro X_Y Y_Z
  rcases X with ⟨L,R,O⟩
  rcases Y with ⟨L',R',O'⟩
  rcases Z with ⟨L'',R'',O''⟩
  simp only [subseteqFL, L_eq, O_eq, R_eq] at *
  have := @Finset.FL_sub_FL_iff_sub_FL
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro φ φ_in
  · have : (L' ∪ O'.L) ⊆ (L'' ∪ O''.L).FL := by grind
    grind
  · have : (L' ∪ O'.L) ⊆ (L'' ∪ O''.L).FL := by grind
    grind
  · have : (R' ∪ O'.R) ⊆ (R'' ∪ O''.R).FL := by grind
    grind
  · have : (R' ∪ O'.R) ⊆ (R'' ∪ O''.R).FL := by grind
    grind

lemma testsOfProgram_in_FLb {φ α} (φ_in : φ ∈ testsOfProgram α) ψ : φ ∈ FLb α ψ := by
  cases α <;> simp only [testsOfProgram, List.not_mem_nil, List.mem_append, List.mem_cons,
    or_false] at *
  case sequence α β =>
    simp only [FLb, List.cons_append, List.nil_append, List.mem_cons, List.mem_append]
    right
    right
    rcases φ_in with h|h <;> have IH := testsOfProgram_in_FLb h <;> grind
  case union α β =>
    simp only [FLb, List.cons_append, List.nil_append, List.mem_cons, List.mem_append]
    right
    right
    rcases φ_in with h|h <;> have IH := testsOfProgram_in_FLb h <;> grind
  case star α =>
    have IH := testsOfProgram_in_FLb φ_in (⌈∗α⌉ψ)
    grind [FLb]
  case test τ =>
    simp_all [FLb]

lemma neg_testsOfProgram_in_FLb {φ α} (φ_in : φ ∈ testsOfProgram α) ψ : ~φ ∈ FLb α ψ := by
  cases α <;> simp only [testsOfProgram, List.not_mem_nil, List.mem_append, List.mem_cons,
    or_false] at *
  case sequence α β =>
    simp only [FLb, List.cons_append, List.nil_append, List.mem_cons, reduceCtorEq,
      Formula.neg.injEq, List.mem_append, false_or]
    right
    rcases φ_in with h|h <;> have IH := neg_testsOfProgram_in_FLb h <;> grind
  case union α β =>
    simp only [FLb, List.cons_append, List.nil_append, List.mem_cons, reduceCtorEq,
      Formula.neg.injEq, List.mem_append, false_or]
    right
    rcases φ_in with h|h <;> have IH := neg_testsOfProgram_in_FLb h <;> grind
  case star α =>
    have IH := neg_testsOfProgram_in_FLb φ_in (⌈∗α⌉ψ)
    grind [FLb]
  case test τ =>
    simp_all [FLb]

lemma Dset_tests_in_FL α F δ (in_D : (F, δ) ∈ Dset α) ψ : F ⊆ FLb α ψ := by
  cases α <;> simp only [Dset, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
    List.mem_flatMap, Prod.exists, List.mem_union_iff, List.empty_eq, List.cons_union,
    List.nil_union, List.mem_flatten, List.mem_map, ↓existsAndEq, and_true, List.mem_ite_nil_left,
    List.nil_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false, or_self, exists_const,
    not_false_eq_true, List.insert_of_not_mem, true_and] at *
  case atom_prog =>
    grind
  case sequence α β =>
    rcases in_D with ⟨G, γ, Gγ_in_D, Fδ_in⟩
    by_cases γ = []
    · subst_eqs
      simp only [↓reduceIte, List.mem_flatten, List.mem_map, Prod.exists, ↓existsAndEq, and_true,
        List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, exists_eq_right_right'] at *
      rcases Fδ_in with ⟨F', in_D', F_def⟩
      have IHα := Dset_tests_in_FL _ _ _ Gγ_in_D
      have IHβ := Dset_tests_in_FL _ _ _ in_D'
      grind [FLb]
    · simp_all only [↓reduceIte, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
      cases Fδ_in; subst_eqs
      have IH := Dset_tests_in_FL α F γ Gγ_in_D (⌈β⌉ψ)
      grind [FLb]
  case union α β =>
    rcases in_D with in_D|in_D
    all_goals
      have IHα := Dset_tests_in_FL _ _ _ in_D ψ
      grind [FLb]
  case star α =>
    rcases in_D with ⟨⟨_⟩,⟨_⟩⟩|in_D
    · simp
    · rcases in_D with ⟨γ, in_D, _, def_δ⟩
      subst def_δ
      have IH := Dset_tests_in_FL α F _ in_D (⌈∗α⌉ψ)
      grind [FLb]
  case test =>
    cases in_D
    subst_eqs
    simp [FLb]

lemma Dset_progs_in_FL F δ α (in_D : (F, δ) ∈ Dset α) ψ : δ ≠ [] → (~⌈⌈δ⌉⌉ψ) ∈ FLb α ψ := by
  cases α <;> simp only [Dset, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, ne_eq,
    FLb, reduceCtorEq, Formula.neg.injEq, false_or, List.mem_flatMap, Prod.exists,
    List.cons_append, List.nil_append, List.mem_append, List.mem_union_iff, List.empty_eq,
    List.cons_union, List.nil_union, List.mem_flatten, List.mem_map, ↓existsAndEq, and_true,
    List.mem_ite_nil_left, List.nil_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false,
    or_self, exists_const, not_false_eq_true, List.insert_of_not_mem, true_and] at * -- pfoei
  · cases in_D
    subst_eqs
    simp
  case sequence α β =>
    rcases in_D with ⟨G, γ, in_D, in_l⟩
    by_cases γ = []
    · subst_eqs
      simp only [↓reduceIte, List.mem_flatten, List.mem_map, Prod.exists] at in_l
      rcases in_l with ⟨l, ⟨F', δ', in_D', def_l⟩ , in_l⟩
      subst def_l
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at *
      cases in_l; subst_eqs
      have IHα := Dset_progs_in_FL _ _ _ in_D
      have IHβ := Dset_progs_in_FL _ _ _ in_D'
      grind [FLb]
    case neg γ_not_nil =>
      simp_all only [↓reduceIte, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
        List.append_eq_nil_iff, List.cons_ne_self, and_self, not_false_eq_true, forall_const]
      cases in_l; subst_eqs
      rw [boxes_append]
      right
      left
      exact Dset_progs_in_FL _ _ _ in_D (⌈β⌉ψ) γ_not_nil -- IH
  case union α β =>
    rcases in_D with in_D|in_D
    all_goals
      have IHα := Dset_progs_in_FL _ _ _ in_D ψ
      grind [FLb]
  case star α =>
    rcases in_D with ⟨⟨_⟩,⟨_⟩⟩|in_D
    · simp
    · rcases in_D with ⟨γ, in_D, γ_not_nil, def_δ⟩
      subst def_δ
      have IH := Dset_progs_in_FL _ _ _ in_D (⌈∗α⌉ψ) γ_not_nil
      simp_all only [List.append_eq_nil_iff, List.cons_ne_self, and_self, not_false_eq_true,
        forall_const]
      rw [boxes_append]
      right
      exact IH
  case test τ =>
    cases in_D
    subst_eqs
    simp

lemma unfoldDiamond_in_FL (α : Program) (ψ : Formula) (X : List Formula) :
    X ∈ unfoldDiamond α ψ → ∀ φ ∈ X, φ ∈ FL (⌈α⌉ψ) := by
  intro X_in φ φ_in
  rcases unfoldDiamondContent α ψ X X_in φ φ_in with φ_def|h|h
  · simp_all [FL]
  · rcases h with ⟨τ, τ_from_α, φ_def⟩
    subst φ_def
    simp only [FL, List.cons_append, List.nil_append, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr (Or.inl (testsOfProgram_in_FLb τ_from_α ψ)))
  · rcases h with ⟨a, δ, φ_def⟩
    subst φ_def
    rcases α with ⟨a⟩|⟨α,β⟩|⟨α,β⟩|⟨α⟩|⟨τ⟩
    case atom_prog =>
      simp only [unfoldDiamond, Yset, Dset, List.map_cons, Formula.boxes_cons, Formula.boxes_nil,
        List.nil_union, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at X_in
      subst X_in
      simp_all only [List.mem_cons, Formula.neg.injEq, Formula.box.injEq, Program.atom_prog.injEq,
        List.not_mem_nil, or_false]
      rcases φ_in with ⟨h1,h2⟩
      subst h1
      exact FL_single_neg_closed fun a => a
    case test =>
      simp only [unfoldDiamond, Yset, Dset, List.map_cons, Formula.boxes_nil, List.cons_union,
        List.nil_union, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at X_in
      subst X_in
      simp only [List.mem_insert_iff, List.mem_cons, Formula.neg.injEq, List.not_mem_nil,
        or_false] at *
      rcases φ_in with h|h
      · subst h
        simp [FL, FLb]
      · absurd h
        apply Formula.boxes_cons_neq_self
    all_goals -- sequence, union and star case work the same :-)
      simp only [unfoldDiamond, Yset, List.mem_map, Prod.exists] at X_in
      rcases X_in with ⟨F, δ, in_D, def_X⟩
      subst def_X
      simp only [List.mem_union_iff, List.mem_cons, Formula.neg.injEq, List.not_mem_nil, or_false]
        at φ_in
      rcases φ_in with φ_in|φ_def
      · simp only [FL, List.cons_append, List.nil_append, List.mem_cons, Formula.neg.injEq,
        Formula.box.injEq, reduceCtorEq, false_and, List.mem_append, false_or]
        right
        left
        exact Dset_tests_in_FL _ _ _ in_D ψ φ_in
      · rw [φ_def]
        simp only [FL, List.cons_append, List.nil_append, List.mem_cons, Formula.neg.injEq,
          List.mem_append]
        right
        right
        left
        apply Dset_progs_in_FL _ _ _ in_D ψ ?_
        intro hyp
        subst hyp
        rw [Formula.boxes_nil] at φ_def
        absurd φ_def
        apply Formula.boxes_cons_neq_self

/-- Helper for `LoadRule.stays_in_FL_left` and `LoadRule.stays_in_FL_right`. -/
theorem pairUnload.stays_in_FL (F oχ) {α : Program} {φ : Formula}
    (pU_in_unfD : pairUnload (F, oχ) ∈ unfoldDiamond α φ)
    : F ⊆ FL (~⌈α⌉φ)
    ∧ Olf.L (Option.map Sum.inl oχ) ⊆ (FL (~⌈α⌉φ)).toFinset
    ∧ Olf.R (Option.map Sum.inr oχ) ⊆ (FL (~⌈α⌉φ)).toFinset := by
  rcases oχ with _|nχ <;> simp only [pairUnload, FL, List.cons_append, List.nil_append,
    Option.map_none, Olf.L_none, List.toFinset_cons, List.toFinset_append, Finset.mem_insert,
    Formula.neg.injEq, Finset.mem_union, List.mem_toFinset, neg_mem_FLb, true_or, or_true,
    Finset.insert_eq_of_mem, Finset.empty_subset, Olf.R_none, and_self, and_true, negUnload,
    Option.map_some, Olf.L_inl, Finset.singleton_subset_iff, Olf.R_inr] at *
  · intro φ φ_in
    have := unfoldDiamond_in_FL _ _ _ pU_in_unfD _ φ_in
    grind [FL, unfoldDiamond_in_FL]
  · constructor
    · intro φ φ_in
      have := unfoldDiamond_in_FL _ _ _ pU_in_unfD
      grind [FL, unfoldDiamond_in_FL]
    · have := unfoldDiamond_in_FL _ _ _ pU_in_unfD (~nχ.1.unload)
      simp only [List.mem_union_iff, List.mem_cons, List.not_mem_nil, or_false, or_true,
        forall_const] at *
      simp only [FL, List.cons_append, List.nil_append, List.mem_cons, Formula.neg.injEq,
        List.mem_append] at this
      rcases this with h|h|h|h
      · exact Or.inr (Or.inl (h ▸ neg_mem_FLb))
      · tauto
      · tauto
      · tauto

/-- `Finset` version of `pairUnload.stays_in_FL`. -/
theorem pairUnloadSet.stays_in_FL {F : List Formula} {oχ} {α : Program} {φ : Formula}
    (pU_in_unfD : pairUnload (F, oχ) ∈ unfoldDiamond α φ)
    : F.toFinset ⊆ Finset.FL {~⌈α⌉φ}
    ∧ Olf.L (Option.map Sum.inl oχ) ⊆ Finset.FL {~⌈α⌉φ}
    ∧ Olf.R (Option.map Sum.inr oχ) ⊆ Finset.FL {~⌈α⌉φ} := by
  have h := pairUnload.stays_in_FL _ _ pU_in_unfD
  simp only [Finset.FL_singelton]
  refine ⟨?_, h.2.1, h.2.2⟩
  intro x hx
  simp only [List.mem_toFinset] at *
  exact h.1 hx

/-- Helper for `LocalRule.stays_in_FL`. -/
lemma LoadRule.stays_in_FL_left {χ ress} (lr : LoadRule (~'χ) ress) :
    ∀ Y ∈ ress, Sequent.subseteqFL (Y.1, ∅, Y.2.map Sum.inl) (∅, ∅, some (Sum.inl (~'χ))) := by
  simp only [Prod.forall]
  intro F oχ in_ress
  cases lr
  case dia α χ notAt =>
    obtain ⟨⟨F', o'⟩, hmem, hF, hoo⟩ : ∃ p ∈ unfoldDiamondLoaded α χ,
        p.1.toFinset = F ∧ p.2 = oχ := by
      simpa [Prod.ext_iff] using in_ress
    subst hF; subst hoo
    have pU_in_unfD : pairUnload (F', o') ∈ unfoldDiamond α χ.unload := by
      rw [← unfoldDiamondLoaded_eq]
      exact List.mem_map_of_mem hmem
    have := pairUnloadSet.stays_in_FL pU_in_unfD
    simp only [Sequent.subseteqFL, Sequent.L_eq, Sequent.O_eq, Sequent.R_eq, Olf.L_inl,
      Olf.R_inl, Olf.R_map_inl, Finset.empty_union, Finset.union_empty, LoadFormula.unload,
      Finset.empty_subset, and_true]
    tauto
  case dia' α φ notAt =>
    obtain ⟨⟨F', o'⟩, hmem, hF, hoo⟩ : ∃ p ∈ unfoldDiamondLoaded' α φ,
        p.1.toFinset = F ∧ p.2 = oχ := by
      simpa [Prod.ext_iff] using in_ress
    subst hF; subst hoo
    have pU_in_unfD : pairUnload (F', o') ∈ unfoldDiamond α φ := by
      rw [← unfoldDiamondLoaded'_eq]
      exact List.mem_map_of_mem hmem
    have := pairUnloadSet.stays_in_FL pU_in_unfD
    simp only [Sequent.subseteqFL, Sequent.L_eq, Sequent.O_eq, Sequent.R_eq, Olf.L_inl,
      Olf.R_inl, Olf.R_map_inl, Finset.empty_union, Finset.union_empty, LoadFormula.unload,
      Finset.empty_subset, and_true]
    tauto

/-- Helper for `LocalRule.stays_in_FL` -/
lemma LoadRule.stays_in_FL_right {ress} (lr : LoadRule (~'χ) ress) :
    ∀ Y ∈ ress, Sequent.subseteqFL (∅, Y.1, Y.2.map Sum.inr) (∅, ∅, some (Sum.inr (~'χ))) := by
  -- copy-pasta based on LoadRule.stays_in_FL_left
  simp only [Prod.forall]
  intro F oχ in_ress
  cases lr
  case dia α χ notAt =>
    obtain ⟨⟨F', o'⟩, hmem, hF, hoo⟩ : ∃ p ∈ unfoldDiamondLoaded α χ,
        p.1.toFinset = F ∧ p.2 = oχ := by
      simpa [Prod.ext_iff] using in_ress
    subst hF; subst hoo
    have pU_in_unfD : pairUnload (F', o') ∈ unfoldDiamond α χ.unload := by
      rw [← unfoldDiamondLoaded_eq]
      exact List.mem_map_of_mem hmem
    have := pairUnloadSet.stays_in_FL pU_in_unfD
    simp only [Sequent.subseteqFL, Sequent.L_eq, Sequent.O_eq, Sequent.R_eq, Olf.L_inr,
      Olf.R_inr, Olf.L_map_inr, Finset.empty_union, Finset.union_empty, LoadFormula.unload,
      Finset.empty_subset, true_and]
    tauto
  case dia' α φ notAt =>
    obtain ⟨⟨F', o'⟩, hmem, hF, hoo⟩ : ∃ p ∈ unfoldDiamondLoaded' α φ,
        p.1.toFinset = F ∧ p.2 = oχ := by
      simpa [Prod.ext_iff] using in_ress
    subst hF; subst hoo
    have pU_in_unfD : pairUnload (F', o') ∈ unfoldDiamond α φ := by
      rw [← unfoldDiamondLoaded'_eq]
      exact List.mem_map_of_mem hmem
    have := pairUnloadSet.stays_in_FL pU_in_unfD
    simp only [Sequent.subseteqFL, Sequent.L_eq, Sequent.O_eq, Sequent.R_eq, Olf.L_inr,
      Olf.R_inr, Olf.L_map_inr, Finset.empty_union, Finset.union_empty, LoadFormula.unload,
      Finset.empty_subset, true_and]
    tauto

lemma P_in_FL α δ ℓ ψ : δ ∈ P α ℓ → (⌈⌈δ⌉⌉ψ) ∈ FL (⌈α⌉ψ) := by
  cases α
  · simp_all [P]
  case sequence α β =>
    intro δ_in
    simp only [P, List.mem_union_iff, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq,
      List.mem_ite_nil_right] at δ_in
    rcases δ_in with δ_in|δ_in
    · rcases δ_in with ⟨σ, ⟨σ_in, σ_not_nil⟩, def_σ⟩
      subst def_σ
      simp [boxes_append]
      have IHα := P_in_FL α _ ℓ (⌈β⌉ψ) σ_in
      simp only [FL, FLb] at *
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
        List.append_assoc] at *
      aesop
    · rcases δ_in with ⟨nil_in, δ_in⟩
      have IHα := P_in_FL β _ ℓ ψ δ_in
      simp [FL, FLb] at *
      aesop
  case union α β =>
    intro δ_in
    simp only [P, List.mem_union_iff] at δ_in
    rcases δ_in with δ_in|δ_in
    · have IHα := P_in_FL α δ ℓ ψ δ_in
      simp only [FL, List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at *
      rcases IHα with h|h|h|h <;> grind [FLb, neg_mem_FLb]
    · have IHβ := P_in_FL β δ ℓ ψ δ_in
      simp only [FL, List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at *
      rcases IHβ with h|h|h|h <;> grind [FLb, neg_mem_FLb]
  case star α =>
    intro δ_in
    simp only [P, List.cons_union, List.nil_union, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq,
      List.append_eq_nil_iff, List.cons_ne_self, and_false, exists_const, not_false_eq_true,
      List.insert_of_not_mem, List.mem_cons] at δ_in
    rcases δ_in with bla|⟨σ, ⟨σ_in, σ_not_nil⟩ , def_δ⟩
    · subst_eqs
      simp [FL]
    · subst def_δ
      simp only [boxes_append, Formula.boxes_cons, Formula.boxes_nil]
      have IHα := P_in_FL α _ _ (⌈∗α⌉ψ) σ_in
      cases σ <;> simp_all only [not_true_eq_false, reduceCtorEq, not_false_eq_true,
        Formula.boxes_cons]
      case cons γ σ =>
        grind [FL, FLb]
  case test τ =>
    simp_all [P, FL]

lemma unfoldBox_in_FL (α : Program) (ψ : Formula) (X : List Formula) :
    X ∈ unfoldBox α ψ → ∀ φ ∈ X, φ ∈ FL (⌈α⌉ψ) := by
  intro X_in
  simp only [unfoldBox, List.mem_map] at X_in
  rcases X_in with ⟨ℓ, ℓ_in, def_X⟩
  subst def_X
  intro φ φ_in
  simp only [Bset, List.mem_append, List.mem_map] at φ_in
  rcases φ_in with φ_in|⟨δ, in_P, def_φ⟩
  · simp only [FL, List.cons_append, List.nil_append, List.mem_cons, List.mem_append]
    have := F_sub_testsOfProgram_map_neg α ℓ φ_in
    simp only [List.mem_map] at this
    rcases this with ⟨τ, τ_in, def_φ⟩
    subst def_φ
    have := @neg_testsOfProgram_in_FLb τ α τ_in ψ
    grind
  · subst def_φ
    have := P_in_FL _ _ _ ψ in_P
    grind [FL]

/-- Helper for `LocalRule.stays_in_FL` -/
theorem OneSidedLocalRule.stays_in_FL {precond ress}
    (rule : OneSidedLocalRule precond ress) :
    ∀ res ∈ ress, res ⊆ Finset.FL precond := by
  intro res res_in
  cases rule
  case bot => simp at res_in
  case not => simp at res_in
  case neg φ =>
    simp only [Finset.mem_singleton] at res_in
    subst res_in
    simp [FL]
  case con φ ψ =>
    simp only [Finset.mem_singleton] at res_in
    subst res_in
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl|rfl <;> simp [FL]
  case nCo φ ψ =>
    -- NOTE: Here it matters that FL is closed under (single) negation.
    simp only [Finset.mem_insert, Finset.mem_singleton] at res_in
    rcases res_in with rfl|rfl <;> simp [FL]
  case box α φ notAt =>
    obtain ⟨X, X_in, rfl⟩ : ∃ X ∈ unfoldBox α φ, X.toFinset = res := by simpa using res_in
    intro x hx
    simp only [List.mem_toFinset] at hx
    simpa using unfoldBox_in_FL _ _ _ X_in x hx
  case dia α φ notAt =>
    obtain ⟨X, X_in, rfl⟩ : ∃ X ∈ unfoldDiamond α φ, X.toFinset = res := by simpa using res_in
    intro x hx
    simp only [List.mem_toFinset] at hx
    have := unfoldDiamond_in_FL _ _ _ X_in x hx
    simp only [Finset.FL_singelton, List.mem_toFinset]
    simp only [FL, List.singleton_append, List.mem_cons]
    tauto

/-- Helper for `LocalTableau.stays_in_FL` -/
theorem LocalRule.stays_in_FL {X B}
    (rule : LocalRule X B) :
    ∀ Y ∈ B, Y.subseteqFL X := by
  intro Y Y_in_B
  cases rule
  case oneSidedL precond ress orule B_def =>
    subst B_def
    simp only [Finset.mem_image] at *
    rcases Y_in_B with ⟨res, res_in, def_Y⟩
    subst def_Y
    simp only [Sequent.subseteqFL, Sequent.L_eq, Sequent.O_eq, Olf.L_none, Finset.union_empty,
      Finset.empty_subset, Sequent.R_eq, Olf.R_none, Finset.union_idempotent, Finset.FL_nil,
      Std.le_refl, and_self, and_true]
    apply OneSidedLocalRule.stays_in_FL orule _ res_in
  case oneSidedR precond ress orule B_def =>
    subst B_def
    simp only [Finset.mem_image] at *
    rcases Y_in_B with ⟨res, res_in, def_Y⟩
    subst def_Y
    simp only [Sequent.subseteqFL, Sequent.L_eq, Sequent.O_eq, Olf.L_none,
      Finset.union_idempotent, Finset.FL_nil, Std.le_refl, Sequent.R_eq, Olf.R_none,
      Finset.union_empty, Finset.empty_subset, and_true, true_and]
    apply OneSidedLocalRule.stays_in_FL orule _ res_in
  case LRnegL =>
    absurd Y_in_B
    tauto
  case LRnegR =>
    absurd Y_in_B
    tauto
  case loadedL ress χ lorule B_def =>
    subst B_def
    obtain ⟨⟨l, o⟩, in_ress, rfl⟩ := Finset.mem_image.mp Y_in_B
    exact LoadRule.stays_in_FL_left lorule (l, o) in_ress
  case loadedR ress χ lorule B_def =>
    subst B_def
    obtain ⟨⟨l, o⟩, in_ress, rfl⟩ := Finset.mem_image.mp Y_in_B
    exact LoadRule.stays_in_FL_right lorule (l, o) in_ress

/-- Removing something from an `Olf` can only remove formulas on the left. -/
lemma Olf.sdiff_L_sub (O Ocond : Olf) : (O \ Ocond).L ⊆ O.L := by
  rcases O with _|o
  · simp
  rcases Ocond with _|oc
  · simp
  unfold Option.insHasSdiff
  by_cases h : o = oc <;> simp_all [Olf.L]

/-- Removing something from an `Olf` can only remove formulas on the right. -/
lemma Olf.sdiff_R_sub (O Ocond : Olf) : (O \ Ocond).R ⊆ O.R := by
  rcases O with _|o
  · simp
  rcases Ocond with _|oc
  · simp
  unfold Option.insHasSdiff
  by_cases h : o = oc <;> simp_all [Olf.R]

/-- If `Ocond ⊆ O` then the left part of `Ocond` is included in that of `O`. -/
lemma Olf.L_sub_of_sub {O Ocond : Olf} (h : Ocond ⊆ O) : Ocond.L ⊆ O.L := by
  rcases Ocond with _|oc
  · simp
  · rcases O with _|o <;> simp_all

/-- If `Ocond ⊆ O` then the right part of `Ocond` is included in that of `O`. -/
lemma Olf.R_sub_of_sub {O Ocond : Olf} (h : Ocond ⊆ O) : Ocond.R ⊆ O.R := by
  rcases Ocond with _|oc
  · simp
  · rcases O with _|o <;> simp_all

/-- Helper for `LocalTableau.stays_in_FL`: applying a local rule stays in the FL closure. -/
theorem LocalRuleApp.stays_in_FL (lra : LocalRuleApp) :
    ∀ W ∈ lra.C, W.subseteqFL lra.X := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, ⟨hL, hR, hO⟩⟩
  subst hC
  intro W W_in
  simp only [applyLocalRule, Finset.mem_image] at W_in
  obtain ⟨⟨Lnew, Rnew, Onew⟩, new_in, rfl⟩ := W_in
  have lem := LocalRule.stays_in_FL lr _ new_in
  simp only [Sequent.subseteqFL, Sequent.L_eq, Sequent.R_eq, Sequent.O_eq] at lem ⊢
  obtain ⟨lemL, lemLO, lemR, lemRO⟩ := lem
  have monoL : Finset.FL (Lcond ∪ Ocond.L) ⊆ Finset.FL (L ∪ O.L) :=
    Finset.FL_sub (Finset.union_subset_union hL (Olf.L_sub_of_sub hO))
  have monoR : Finset.FL (Rcond ∪ Ocond.R) ⊆ Finset.FL (R ∪ O.R) :=
    Finset.FL_sub (Finset.union_subset_union hR (Olf.R_sub_of_sub hO))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.FL_refl_sub (Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1)
    · exact monoL (lemL hx)
  · rcases Onew with _|onew
    · intro x hx
      simp only [Olf.change, Option.pdlOverwrite] at hx
      exact Finset.FL_refl_sub (Finset.mem_union_right _ (Olf.sdiff_L_sub O Ocond hx))
    · simp only [Olf.change_some]
      intro x hx
      exact monoL (lemLO hx)
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.FL_refl_sub (Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1)
    · exact monoR (lemR hx)
  · rcases Onew with _|onew
    · intro x hx
      simp only [Olf.change, Option.pdlOverwrite] at hx
      exact Finset.FL_refl_sub (Finset.mem_union_right _ (Olf.sdiff_R_sub O Ocond hx))
    · simp only [Olf.change_some]
      intro x hx
      exact monoR (lemRO hx)

/-- End nodes of a local tableau are FischerLadner-subsets of the root.
This is used for `move_inside_FL`. -/
theorem LocalTableau.stays_in_FL {X}
    (ltX : LocalTableau X) :
    ∀ Y ∈ endNodesOf ltX, Y.subseteqFL X := by
  induction ltX with
  | @byLocalRule X lra X_def next IH =>
    subst X_def
    intro Y Y_in
    simp only [endNodesOf, Finset.sup_image, Function.id_comp, Finset.mem_sup, Finset.mem_attach,
      true_and, Subtype.exists] at Y_in
    obtain ⟨W, W_in, Y_in⟩ := Y_in
    exact Sequent.subseteq_FL_trans _ _ _ (IH W W_in Y Y_in) (lra.stays_in_FL W W_in)
  | sim _ => intro Y Y_in; simp_all

lemma projection_sub_FLL {a L} : projection a L ⊆ FLL L := by
  intro φ φ_in
  rw [proj] at φ_in
  simp only [FLL, List.mem_flatMap]
  use ⌈·a⌉φ, φ_in
  simp [FL]

/-- Anything in the FL closure of a member of `X` is in the FL closure of `X`. -/
lemma Finset.mem_FL_of_mem {X : Finset Formula} {ψ x : Formula}
    (hψ : ψ ∈ X) (hx : x ∈ _root_.PDL.FL ψ) : x ∈ X.FL := by
  simp only [Finset.FL, Finset.mem_sup, List.mem_toFinset]
  exact ⟨ψ, hψ, hx⟩

lemma Finset.projection_sub_FL {a} {X : Finset Formula} : X.pdlProjection a ⊆ X.FL := by
  intro φ φ_in
  rw [Finset.mem_projection] at φ_in
  simp only [Finset.FL, Finset.mem_sup, List.mem_toFinset]
  exact ⟨⌈·a⌉φ, φ_in, by simp [_root_.PDL.FL]⟩

/-- Making a PDL rule step stays in the Fischer-Ladner closure.
This is used for `move_inside_FL`. -/
theorem PdlRule.stays_in_FL {X Y} (rule : PdlRule X Y) :
    Y.subseteqFL X := by
  cases rule
  case loadL L δ α φ R in_L notBox Y_def =>
    subst Y_def
    simp only [Sequent.subseteqFL, Sequent.L_eq, Sequent.O_eq, Olf.L_none, Finset.union_empty,
      Olf.L_inl, unload_boxes, LoadFormula.unload, Finset.singleton_subset_iff, Sequent.R_eq,
      Olf.R_none, Finset.FL_refl_sub, Olf.R_inl, Finset.empty_subset, and_self, and_true]
    exact ⟨(Finset.erase_subset _ _).trans Finset.FL_refl_sub, Finset.FL_refl_sub in_L⟩
  case loadR L δ α φ R in_L notBox Y_def =>
    subst Y_def
    simp only [Sequent.subseteqFL, Sequent.L_eq, Sequent.O_eq, Olf.L_none, Finset.union_empty,
      Finset.FL_refl_sub, Olf.L_inr, Finset.empty_subset, Sequent.R_eq, Olf.R_none, Olf.R_inr,
      unload_boxes, LoadFormula.unload, Finset.singleton_subset_iff, true_and]
    exact ⟨(Finset.erase_subset _ _).trans Finset.FL_refl_sub, Finset.FL_refl_sub in_L⟩
  case freeL L R δ α φ X_def Y_def =>
    subst X_def
    subst Y_def
    simp [Sequent.subseteqFL]
  case freeR L R δ α φ X_def Y_def =>
    subst X_def
    subst Y_def
    simp [Sequent.subseteqFL]
  case modL L R a ξ X_def Y_def =>
    subst X_def
    subst Y_def
    cases ξ <;> simp only [Sequent.subseteqFL, Finset.singleton_union, Sequent.L_eq,
      Sequent.O_eq, Olf.L_inl, LoadFormula.unload, Finset.union_singleton, Olf.L_none,
      Finset.empty_subset, Sequent.R_eq, Olf.R_inl, Finset.union_empty, Olf.R_none, and_true,
      true_and, Finset.singleton_subset_iff]
    case normal φ =>
      constructor
      · intro x x_in
        rcases Finset.mem_insert.mp x_in with rfl | x_in
        -- Note: here the closure under single negation matters.
        · exact Finset.mem_FL_of_mem (Finset.mem_insert_self _ _) (by simp [FL, FLb])
        · exact Finset.FL_sub (Finset.subset_insert _ _) (Finset.projection_sub_FL x_in)
      · exact Finset.projection_sub_FL
    case loaded χ =>
      refine ⟨?_, ?_, Finset.projection_sub_FL⟩
      · exact fun _ x_in => Finset.FL_sub (Finset.subset_insert _ _) (Finset.projection_sub_FL x_in)
      -- Note: here the closure under single negation matters.
      · exact Finset.mem_FL_of_mem (Finset.mem_insert_self _ _) (by simp [FL, FLb])
  case modR L R a ξ X_def Y_def => -- analogous to `modL` case
    subst X_def
    subst Y_def
    cases ξ <;> simp only [Sequent.subseteqFL, Finset.singleton_union, Sequent.L_eq,
      Sequent.O_eq, Olf.L_inr, Finset.union_empty, Olf.L_none, Finset.empty_subset, Sequent.R_eq,
      Olf.R_inr, LoadFormula.unload, Finset.union_singleton, Olf.R_none, and_true, true_and,
      Finset.singleton_subset_iff]
    case normal φ =>
      refine ⟨Finset.projection_sub_FL, ?_⟩
      intro x x_in
      rcases Finset.mem_insert.mp x_in with rfl | x_in
      -- Note: here the closure under single negation matters.
      · exact Finset.mem_FL_of_mem (Finset.mem_insert_self _ _) (by simp [FL, FLb])
      · exact Finset.FL_sub (Finset.subset_insert _ _) (Finset.projection_sub_FL x_in)
    case loaded χ =>
      refine ⟨Finset.projection_sub_FL, ?_, ?_⟩
      · exact fun _ x_in => Finset.FL_sub (Finset.subset_insert _ _) (Finset.projection_sub_FL x_in)
      -- Note: here the closure under single negation matters.
      · exact Finset.mem_FL_of_mem (Finset.mem_insert_self _ _) (by simp [FL, FLb])

end PDL
