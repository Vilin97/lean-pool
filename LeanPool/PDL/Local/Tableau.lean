/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Multiset.DershowitzManna

public import LeanPool.PDL.Local.Rules

/-! # Local Tableaux (Section 3) -/

@[expose] public section

namespace PDL

/-- Local tableau for `X`, maximal by definition. -/
inductive LocalTableau : (X : Sequent) → Type
  | byLocalRule {X} (lra : LocalRuleApp) (X_def : X = lra.X)
      (next : ∀ Y ∈ lra.C, LocalTableau Y) : LocalTableau X
  | sim {X} : X.basic → LocalTableau X

instance LocalTableau.instDecidableEq {lt1 lt2 : LocalTableau X} : Decidable (lt1 = lt2) := by
  rcases lt1 with (⟨lra1, X_def1, next1⟩|Xbas1)
  all_goals
    rcases lt2 with (⟨lra2, X_def2, next2⟩|Xbas2)
  · by_cases lra1.C = lra2.C
    · subst_eqs
      simp_all only [LocalRuleApp.X, byLocalRule.injEq]
      by_cases lra1 = lra2
      · subst_eqs
        simp only [true_and]
        have := fun (X : Sequent) (X_in : X ∈ _) =>
          @LocalTableau.instDecidableEq _ (next1 X X_in) (next2 X X_in)
        by_cases ∃ Z ∈ lra1.C, ∀ h, next1 Z h ≠ next2 Z h
        · apply isFalse
          aesop
        · apply isTrue
          aesop
      · apply isFalse
        aesop
    · apply isFalse
      aesop
  all_goals
    try simp_all only [reduceCtorEq]
    try exact instDecidableFalse
    try exact instDecidableTrue

/-! ## Termination of LocalTableau -/

theorem testsOfProgram_sizeOf_lt α : ∀ τ ∈ testsOfProgram α, sizeOf τ < sizeOf α := by
  intro τ τ_in
  cases α
  all_goals
    simp only [testsOfProgram, List.not_mem_nil, List.mem_append, Program.sequence.sizeOf_spec,
      Program.union.sizeOf_spec, Program.star.sizeOf_spec, List.mem_cons, or_false,
      Program.test.sizeOf_spec] at *
  case sequence α β =>
    rcases τ_in with τ_in | τ_in
    · have := testsOfProgram_sizeOf_lt α _ τ_in; linarith
    · have := testsOfProgram_sizeOf_lt β _ τ_in; linarith
  case union α β =>
    rcases τ_in with τ_in | τ_in
    · have := testsOfProgram_sizeOf_lt α _ τ_in; linarith
    · have := testsOfProgram_sizeOf_lt β _ τ_in; linarith
  case star β =>
    have := testsOfProgram_sizeOf_lt β _ τ_in; linarith
  case test τ =>
    subst_eqs
    linarith

open LocalTableau

/-- The local measure which together with D-M can be used to show that LocalTableau are finite.
Note that different from the paper here we also add `lmOfFormula (~φ)` in the `~⌈α⌉φ` case.
This is needed to get `lmOfFormula_lt_dia_of_nonAtom`. -/
@[simp]
def lmOfFormula : (f : Formula) → Nat
| ⊥ => 0
| ~⊥ => 0
| ·_ => 0
| ~·_ => 0
| ~~φ => 1 + lmOfFormula φ
| φ⋀ψ => 1 + lmOfFormula φ + lmOfFormula ψ
| ~(φ⋀ψ) => 1 + lmOfFormula (~φ) + lmOfFormula (~ψ)
| ⌈·_⌉ _ => 0 -- No more local steps
| ~⌈·_⌉ _ => 0 -- No more local steps
| ⌈α⌉φ => 1 + lmOfFormula φ -- unfoldBox
            + ((testsOfProgram α).attach.map (fun τ => lmOfFormula (~τ.1))).sum
| ~⌈α⌉φ => 1 + lmOfFormula (~φ)
             + ((testsOfProgram α).attach.map (fun τ => lmOfFormula τ.1)).sum
decreasing_by
  all_goals simp_wf
  all_goals try linarith
  all_goals
    have := testsOfProgram_sizeOf_lt _ _ τ.2
    linarith

theorem lmOfFormula_lt_box_of_nonAtom (h : ¬ α.isAtomic) :
    lmOfFormula φ < lmOfFormula (⌈α⌉φ) := by
  cases α <;> simp_all [Program.isAtomic, testsOfProgram] <;> linarith

theorem lmOfFormula_lt_dia_of_nonAtom (h : ¬ α.isAtomic) :
    lmOfFormula (~φ) < lmOfFormula (~⌈α⌉φ) := by
  cases α <;> simp_all [Program.isAtomic, testsOfProgram] <;> linarith


/-- The multiset of unloaded formulas represented by an optional loading. -/
def Olf.toForm : Olf → Multiset Formula
| none => {}
| some (Sum.inl (~'χ)) => {~χ.unload}
| some (Sum.inr (~'χ)) => {~χ.unload}

theorem Multiset_diff_append_of_le [DecidableEq α] {R Rcond Rnew : List α} :
    Multiset.ofList (R.diff Rcond ++ Rnew)
    = Multiset.ofList R - Multiset.ofList Rcond + Multiset.ofList Rnew := by
  rw [@Multiset.coe_sub]
  rw [Multiset.coe_add]

theorem List.Perm_diff_append_of_Subperm {α} [DecidableEq α] {L M : List α} (h : M.Subperm L) :
    L.Perm (L.diff M ++ M) := by
  rw [List.perm_iff_count]
  intro φ
  rw [← Multiset.coe_count, ← Multiset.coe_count]
  rw [@Multiset_diff_append_of_le α _ L M M]
  rw [tsub_add_cancel_of_le h]

theorem List.count_eq_diff_of_subperm [DecidableEq α] {L M : List α} (h : M.Subperm L) φ :
    List.count φ L = List.count φ (L.diff M) + List.count φ M := by
  suffices L.Perm (L.diff M ++ M) by
    rw [← List.count_append]
    have := @List.perm_iff_count _ _ _ L (L.diff M ++ M)
    tauto
  apply List.Perm_diff_append_of_Subperm h

theorem unfoldBox.decreases_lmOf_nonAtomic {α : Program} {φ : Formula} {X : List Formula}
    (α_non_atomic : ¬ α.isAtomic)
    (X_in : X ∈ unfoldBox α φ)
    (ψ_in_X : ψ ∈ X)
    : lmOfFormula ψ < lmOfFormula (⌈α⌉φ) := by
  have ubc := unfoldBoxContent (α) φ X X_in ψ ψ_in_X
  cases α <;> simp only [Program.isAtomic, not_true_eq_false, Bool.false_eq_true,
    not_false_eq_true, List.mem_cons, forall_eq_or_imp, lmOfFormula, List.map_subtype,
    List.unattach_attach, gt_iff_lt] at *
  case sequence α β =>
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ)
          < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (α;'β)).attach).sum.succ by
        simp_all
        linarith
      rw [@List.attach_map_val _ _ (testsOfProgram (α;'β)) (fun x => lmOfFormula (~↑x))]
      rw [Nat.lt_succ_iff]
      apply List.le_sum_of_mem
      simp only [List.mem_map]
      use τ
    · subst def_ψ
      simp [lmOfFormula]
  case union α β => -- based on sequence case
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ)
          < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (α⋓β)).attach).sum.succ by
        simp_all
        linarith
      rw [@List.attach_map_val _ _ (testsOfProgram (α⋓β)) (fun x => lmOfFormula (~↑x))]
      rw [Nat.lt_succ_iff]
      exact List.single_le_sum (by simp) _ (by rw [List.mem_map]; use τ)
    · subst def_ψ
      simp [lmOfFormula]
  case star β => -- based on sequence case
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ)
          < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (∗β)).attach).sum.succ by
        simp_all
        linarith
      rw [@List.attach_map_val _ _ (testsOfProgram (∗β)) (fun x => lmOfFormula (~↑x))]
      rw [Nat.lt_succ_iff]
      exact List.single_le_sum (by simp) _ (by rw [List.mem_map]; use τ)
    · subst def_ψ
      simp [lmOfFormula]
  case test τ0 => -- based on sequence case
    rcases ubc with one | ⟨τ, τ_in, def_ψ⟩ | ⟨a, δ, def_ψ, _⟩
    · subst_eqs; linarith
    · subst def_ψ
      suffices lmOfFormula (~τ)
          < (List.map (fun x => lmOfFormula (~ (x.1))) (testsOfProgram (?'τ0)).attach).sum.succ by
        simp_all
        linarith
      rw [@List.attach_map_val _ _ (testsOfProgram (?'τ0)) (fun x => lmOfFormula (~↑x))]
      rw [Nat.lt_succ_iff]
      exact List.single_le_sum (by simp) _ (by rw [List.mem_map]; use τ)
    · subst def_ψ
      simp [lmOfFormula]

theorem lmOfFormula.le_union_left α β φ : lmOfFormula (~⌈α⌉φ) ≤ lmOfFormula (~⌈α⋓β⌉φ) := by
  cases α <;> simp [lmOfFormula]
  all_goals
    simp [testsOfProgram]

theorem lmOfFormula.le_union_right α β φ : lmOfFormula (~⌈β⌉φ) ≤ lmOfFormula (~⌈α⋓β⌉φ) := by
  cases β <;> simp [lmOfFormula]
  all_goals
    simp [testsOfProgram]

theorem Dset_goes_down (α : Program) φ {Fs δ} (in_D : (Fs, δ) ∈ Dset α) {ψ} (in_Fs : ψ ∈ Fs) :
    lmOfFormula ψ < lmOfFormula (~⌈α⌉φ) := by
  cases α
  · simp_all [Dset]
  case sequence α β =>
    simp only [lmOfFormula]
    simp only [Dset, List.mem_flatMap, Prod.exists] at in_D
    rcases in_D with ⟨Fs', δ', in_D, Fs_in⟩
    · by_cases δ' = []
      · subst_eqs
        simp_all only [↓reduceIte, List.mem_flatten, List.mem_map, Prod.exists, ↓existsAndEq,
          and_true, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
          exists_eq_right_right', List.map_subtype, List.unattach_attach]
        rcases Fs_in with ⟨Fs'', Fs''_in, Fs_def⟩
        subst Fs_def
        simp only [List.mem_union_iff] at in_Fs
        rcases in_Fs with in_Fs'|in_Fs''
        · have IHα := Dset_goes_down α φ in_D in_Fs'
          cases α
          all_goals
            simp [lmOfFormula] at IHα
          all_goals
            simp_all [testsOfProgram]
            linarith
        · have IHβ := Dset_goes_down β φ Fs''_in in_Fs''
          cases β
          all_goals
            simp_all [Dset, testsOfProgram, lmOfFormula]
            try linarith
      · simp_all only [↓reduceIte, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
          testsOfProgram, List.attach_append, List.map_append, List.map_map, Function.comp_apply,
          List.map_subtype, List.unattach_attach, List.sum_append]
        have IHα := Dset_goes_down α φ in_D in_Fs
        cases α
        all_goals
          simp_all [Dset, testsOfProgram, lmOfFormula] <;> linarith
  case union α β =>
    simp only [Dset, List.mem_union_iff] at in_D
    rcases in_D with hyp|hyp
    · have IHα := Dset_goes_down α φ hyp in_Fs
      suffices lmOfFormula (~⌈α⌉φ) ≤ lmOfFormula (~⌈α⋓β⌉φ) by linarith
      apply lmOfFormula.le_union_left
    · have IHβ := Dset_goes_down β φ hyp in_Fs
      suffices lmOfFormula (~⌈β⌉φ) ≤ lmOfFormula (~⌈α⋓β⌉φ) by linarith
      apply lmOfFormula.le_union_right
  case star α =>
    simp only [lmOfFormula]
    simp only [Dset, List.empty_eq, List.cons_union, List.nil_union, List.mem_flatten,
      List.mem_map, Prod.exists, ↓existsAndEq, and_true, List.mem_ite_nil_left, List.mem_cons,
      Prod.mk.injEq, List.nil_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false,
      List.not_mem_nil, or_self, exists_const, not_false_eq_true, List.insert_of_not_mem,
      or_false, true_and] at in_D
    rcases in_D with _ | ⟨δ', in_D', in_l⟩
    · simp_all only [List.not_mem_nil]
    · by_cases δ' = []
      · simp_all
      · simp only [testsOfProgram]
        cases in_l
        subst_eqs
        have IHα := Dset_goes_down α φ in_D' in_Fs
        cases α <;> simp_all only [lmOfFormula, not_lt_zero]
  case test τ =>
    simp_all [Dset, testsOfProgram]

theorem unfoldDiamond.decreases_lmOf_nonAtomic {α : Program} {φ : Formula} {X : List Formula}
    (α_non_atomic : ¬ α.isAtomic)
    (X_in : X ∈ unfoldDiamond α φ)
    (ψ_in_X : ψ ∈ X)
    : lmOfFormula ψ < lmOfFormula (~⌈α⌉φ) := by
  have udc := unfoldDiamondContent _ _ _ X_in _ ψ_in_X
  rcases udc with ψ_def | ⟨τ, τ_in, ψ_def⟩ | ⟨a, δ, ψ_def⟩ <;> subst ψ_def
  · exact lmOfFormula_lt_dia_of_nonAtom α_non_atomic
  · cases α <;> simp_all only [Program.isAtomic, not_true_eq_false, Bool.false_eq_true,
    not_false_eq_true, testsOfProgram, List.mem_append, lmOfFormula, List.attach_append,
    List.map_append, List.map_map, Function.comp_apply, List.map_subtype, List.unattach_attach,
    List.sum_append, gt_iff_lt, List.mem_cons, List.not_mem_nil, or_false, List.attach_cons,
    List.attach_nil, List.map_nil, List.map_cons, List.sum_cons, List.sum_nil, add_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, true_or]
    case sequence α β =>
      suffices lmOfFormula ψ < (List.map lmOfFormula (testsOfProgram (α;'β))).sum.succ by
        simp_all [testsOfProgram]
        linarith
      suffices ∃ τ' ∈ testsOfProgram (α;'β), lmOfFormula ψ < 1 + lmOfFormula τ' by
        rw [Nat.lt_succ_iff]
        apply List.le_sum_of_mem
        simp_all [testsOfProgram]
        aesop
      simp_all [testsOfProgram]
      aesop
    case union α β =>
      suffices lmOfFormula ψ < (List.map lmOfFormula (testsOfProgram (α⋓β))).sum.succ by
        simp_all [testsOfProgram]
        linarith
      suffices ∃ τ' ∈ testsOfProgram (α;'β), lmOfFormula ψ < 1 + lmOfFormula τ' by
        rw [Nat.lt_succ_iff]
        apply List.le_sum_of_mem
        simp_all [testsOfProgram]
        aesop
      simp_all [testsOfProgram]
      aesop
    case star β =>
      suffices lmOfFormula ψ < (List.map lmOfFormula (testsOfProgram (∗β))).sum.succ by
        simp_all [testsOfProgram]
        linarith
      suffices ∃ τ' ∈ testsOfProgram (∗β), lmOfFormula ψ < 1 + lmOfFormula τ' by
        rw [Nat.lt_succ_iff]
        apply List.le_sum_of_mem
        simp_all [testsOfProgram]
        aesop
      simp_all [testsOfProgram]
      aesop
  · simp only [lmOfFormula, gt_iff_lt]
    cases α <;> simp_all [Program.isAtomic]

/-- This is a helper for `measureProp` parts (d) and (e).
If each element of a list `X` is either `a`, belongs to a list `bs`, or has `f` value 0,
then the sum of `f` over `X.toFinset` is at most `f a + (bs.map f).sum`. -/
lemma finset_sum_trichotomy {A : Type*} [DecidableEq A]
    (f : A → ℕ) (X : List A) (a : A) (bs : List A)
    (h : ∀ x ∈ X, x = a ∨ x ∈ bs ∨ f x = 0) :
    ∑ x ∈ X.toFinset, f x ≤ f a + (bs.map f).sum := by
  have h_sum_split : (∑ x ∈ X.toFinset, f x) ≤ (∑ x ∈ (X.toFinset.erase a), f x) + f a := by
    by_cases ha : a ∈ X.toFinset <;> simp_all +decide only [List.mem_toFinset, not_false_eq_true,
      Finset.erase_eq_of_notMem, le_add_iff_nonneg_right, zero_le]
    rw [← Finset.sum_erase_add _ _ (by aesop : a ∈ X.toFinset), add_comm]
  have h_sum_le : (∑ x ∈ X.toFinset.erase a, f x) ≤ (∑ x ∈ (bs.toFinset), f x) := by
    have h_sum_le' : (∑ x ∈ X.toFinset.erase a, f x) ≤
        (∑ x ∈ (X.toFinset.erase a ∩ bs.toFinset), f x) := by
      rw [← Finset.sum_subset (Finset.inter_subset_left)]
      intro x hx hx'; specialize h x; aesop
    exact h_sum_le'.trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.inter_subset_right) (fun _ _ _ => Nat.zero_le _))
  apply le_trans h_sum_split
  rw [add_comm]
  refine Nat.add_le_add_left (le_trans h_sum_le ?_) _
  have h_toFinset_le : ∀ (l : List A), (∑ x ∈ l.toFinset, f x) ≤ (l.map f).sum := by
    intro l; induction l <;> simp_all +decide only [List.toFinset_nil, Finset.sum_empty,
      List.map_nil, List.sum_nil, Std.le_refl, List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases hh : ‹A› ∈ ‹List A›.toFinset <;> simp_all +decide only [List.mem_toFinset,
      Finset.insert_eq_of_mem, not_false_eq_true, Finset.sum_insert, add_le_add_iff_left]; linarith!
  exact h_toFinset_le bs

/-- This is a summary lemma and not used as a whole anywhere.
Note that parts (d) and (e) are about the measure sum over `X` and not single formulas, so
for example (e) is not the same as `unfoldDiamond.decreases_lmOf_nonAtomic`.
Also note that we use `List.toFinset` here to ignore duplicates in the list `X`. -/
lemma measureProp {α : Program} {φ φ₁ φ₂ : Formula} :
      (lmOfFormula φ < lmOfFormula (~~φ)) -- a
    ∧ (lmOfFormula φ₁ + lmOfFormula φ₂ < lmOfFormula (φ₁ ⋀ φ₂)) -- b
    ∧ (lmOfFormula (~φ₁) < lmOfFormula (~(φ₁ ⋀ φ₂))) -- c i=1
    ∧ (lmOfFormula (~φ₂) < lmOfFormula (~(φ₁ ⋀ φ₂))) -- c i=2
    ∧ (¬ α.isAtomic → ∀ X ∈ unfoldBox α φ,
        ∑ ψ ∈ X.toFinset, lmOfFormula ψ < lmOfFormula (⌈α⌉φ)) -- d
    ∧ (¬ α.isAtomic → ∀ X ∈ unfoldDiamond α φ,
        ∑ ψ ∈ X.toFinset, lmOfFormula ψ < lmOfFormula (~⌈α⌉φ)) -- e
    := by
  refine ⟨?a, ?b, ?c1, ?c2, ?d, ?e⟩
  case a => simp
  case b => simp
  case c1 => simp; linarith
  case c2 => simp
  case d =>
    intro α_non_atomic X X_in
    cases α_def : α
    case atom_prog => exfalso; simp_all [Program.isAtomic]
    case test τ =>
      subst α_def
      simp_all [testsOfProgram, unfoldBox, allTP, Bset, F, P]
      cases h : X_in <;> subst h <;> simp_all [Finset.sum]; linarith
    all_goals
      simp only [lmOfFormula, List.map_subtype, List.unattach_attach]
      have tri : ∀ ψ ∈ X, ψ = φ ∨ ψ ∈ (testsOfProgram α).map (~·) ∨ lmOfFormula ψ = 0 := by
        have ubc := unfoldBoxContent _ φ X X_in
        intro ψ ψ_in; rcases ubc ψ ψ_in with rfl | ⟨τ, τ_in, rfl⟩ | ⟨a, δ, rfl, _⟩
        · left; rfl
        · right; left; exact List.mem_map_of_mem τ_in
        · right; right; simp [lmOfFormula]
      have := finset_sum_trichotomy lmOfFormula X φ ((testsOfProgram α).map (~·)) tri
      subst α_def
      simp only [List.mem_map, List.map_map, Function.comp_def, gt_iff_lt] at *
      linarith
  case e =>
    intro α_non_atomic X X_in
    have := @lmOfFormula_lt_dia_of_nonAtom φ _ α_non_atomic
    cases α_def : α
    case atom_prog =>
      simp_all [Program.isAtomic]
    case test τ =>
      simp_all [testsOfProgram, unfoldDiamond, Dset, Yset]
      subst X_in
      by_cases h : τ = ~φ <;> simp_all; grind
    all_goals
      have tri : ∀ ψ ∈ X, ψ = (~φ) ∨ ψ ∈ testsOfProgram α ∨ lmOfFormula ψ = 0 := by
        have udc := unfoldDiamondContent _ _ _ X_in
        intro ψ ψ_in
        rcases udc ψ ψ_in with rfl | ⟨τ, τ_in, rfl⟩ | ⟨a, δ, rfl⟩
        · left; rfl
        · right; left; exact τ_in
        · right; right; simp [lmOfFormula]
      have := finset_sum_trichotomy lmOfFormula X (~φ) (testsOfProgram α) tri
      subst α_def
      simp only [lmOfFormula, List.map_subtype, List.unattach_attach, gt_iff_lt] at *
      linarith

/-- The end sequents of a local tableau. -/
@[simp]
def endNodesOf : {X : _} → LocalTableau X → Finset Sequent
  | .(_), (@byLocalRule X lra _ next) =>
      (lra.C.attach.image (fun ⟨Y, h⟩ => endNodesOf (next Y h))).sup id
  | .(_), (@sim X _) => {X}
-- termination_by
--   X => X -- pick up instance WellFoundedRelation Sequent from above!
-- decreasing_by
--   subst_eqs
--   apply localRuleApp.decreases_DM lra Y h

/-- An open local tableau has at least one end node. -/
def OpenLocalTableau (X : Sequent) : Type := {lt : LocalTableau X // endNodesOf lt ≠ {}}
deriving DecidableEq

/-! ## The Dershowitz-Manna ordering on sequents -/

/-- All formulas of a sequent as a multiset, with the loaded formula (if any) unloaded. -/
def nodeToMultiset (X : Sequent) : Multiset Formula := X.L.val + X.R.val + X.O.toForm

/-- The multiset of the local measures of all formulas in a sequent. -/
def nodeMeasure (X : Sequent) : Multiset Nat := (nodeToMultiset X).map lmOfFormula

/-- The Dershowitz-Manna ordering on sequents: `X` is smaller than `Y` iff the multiset of
the `lmOfFormula` measures of the formulas of `X` is smaller than the one of `Y`. -/
def ltSequent (X Y : Sequent) : Prop :=
  Multiset.IsDershowitzMannaLT (nodeMeasure X) (nodeMeasure Y)

instance instIsWellFoundedSequentLt : WellFounded ltSequent :=
  InvImage.wf nodeMeasure Multiset.wellFounded_isDershowitzMannaLT

theorem ltSequent.trans {X Y Z : Sequent} (h1 : ltSequent X Y) (h2 : ltSequent Y Z) :
    ltSequent X Z :=
  Multiset.IsDershowitzMannaLT.trans h1 h2

/-! ## Local rules decrease the Dershowitz-Manna measure

The reuslts here are used for the construction of the canonical local tableau
 `uniLocalTab`.

The key facts are:

* `OneSidedLocalRule.lmOfFormula_lt`: every formula in a result of a one-sided local rule
  is smaller — in the local measure `lmOfFormula` — than one of the formulas the rule is
  applied to;
* `LoadRule.lmOfFormula_lt`: the same for the loaded rules, via `LoadRule.unload`;
* `localRuleApp.decreases_DM`: hence each child of a local rule application is strictly
  smaller than its parent in the Dershowitz-Manna ordering `ltSequent`.
-/

/-- The well-founded relation on sequents used for the termination of the recursive
definitions of local tableaux. This would also better belong to `Pdl/Local/Tableau.lean`,
where the commented-out `termination_by` of `endNodesOf` refers to it. -/
instance instWellFoundedRelationSequent : WellFoundedRelation Sequent :=
  ⟨ltSequent, instIsWellFoundedSequentLt⟩

/-- The multiset of a union of two disjoint finite sets is the sum of the two multisets. -/
lemma Finset.union_val_of_disjoint {α : Type*} [DecidableEq α] {A C : Finset α}
    (h : Disjoint A C) : (A ∪ C).val = A.val + C.val := by
  rw [← Finset.disjUnion_eq_union A C h, Finset.disjUnion_val]

/-- Splitting off the new elements of a union. -/
lemma Finset.union_val_sdiff {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∪ B).val = A.val + (B \ A).val := by
  rw [← Finset.union_val_of_disjoint (Finset.disjoint_sdiff)]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- Splitting off the condition of a rule from the sequent it is applied to. -/
lemma Finset.val_eq_sdiff_add_of_subset {α : Type*} [DecidableEq α] {A B : Finset α}
    (h : B ⊆ A) : A.val = (A \ B).val + B.val := by
  rw [← Finset.union_val_of_disjoint (Finset.sdiff_disjoint)]
  congr 1
  exact (Finset.sdiff_union_of_subset h).symm

/-- Every formula in a result of a one-sided local rule is smaller than one of the
formulas the rule is applied to. -/
lemma OneSidedLocalRule.lmOfFormula_lt {precond ress} (orule : OneSidedLocalRule precond ress) :
    ∀ res ∈ ress, ∀ ψ ∈ res, ∃ φ ∈ precond, lmOfFormula ψ < lmOfFormula φ := by
  cases orule
  case bot => simp
  case not => simp
  case neg φ =>
    intro res hres ψ hψ
    simp only [Finset.mem_singleton] at hres
    subst hres
    simp only [Finset.mem_singleton] at hψ
    subst hψ
    exact ⟨~~ψ, by simp, by simp⟩
  case con φ ψ =>
    intro res hres χ hχ
    simp only [Finset.mem_singleton] at hres
    subst hres
    simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
    refine ⟨φ ⋀ ψ, by simp, ?_⟩
    rcases hχ with rfl | rfl <;> (simp; try omega)
  case nCo φ ψ =>
    intro res hres χ hχ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hres
    refine ⟨~(φ ⋀ ψ), by simp, ?_⟩
    rcases hres with rfl | rfl <;>
      (simp only [Finset.mem_singleton] at hχ; subst hχ; simp; try omega)
  case box α φ notAtom =>
    intro res hres ψ hψ
    simp only [List.pdlToFinFin, List.mem_toFinset, List.mem_map] at hres
    obtain ⟨X, hX, rfl⟩ := hres
    rw [List.mem_toFinset] at hψ
    exact ⟨⌈α⌉φ, by simp, unfoldBox.decreases_lmOf_nonAtomic notAtom hX hψ⟩
  case dia α φ notAtom =>
    intro res hres ψ hψ
    simp only [List.pdlToFinFin, List.mem_toFinset, List.mem_map] at hres
    obtain ⟨X, hX, rfl⟩ := hres
    rw [List.mem_toFinset] at hψ
    exact ⟨~⌈α⌉φ, by simp, unfoldDiamond.decreases_lmOf_nonAtomic notAtom hX hψ⟩

/-- Every formula in a result of a loaded rule — including the new loaded formula — is
smaller than the formula the rule is applied to. -/
lemma LoadRule.lmOfFormula_lt {χ : LoadFormula} {ress} (lrule : LoadRule (~'χ) ress) :
    ∀ res ∈ ress, ∀ ψ ∈ pairUnloadSet res, lmOfFormula ψ < lmOfFormula (~χ.unload) := by
  intro res hres ψ hψ
  obtain ⟨φ, hφ, hlt⟩ := lrule.unload.lmOfFormula_lt (pairUnloadSet res)
    (Finset.mem_image_of_mem _ hres) ψ hψ
  rw [Finset.mem_singleton] at hφ
  exact hφ ▸ hlt

/-- A sufficient criterion for the Dershowitz-Manna ordering on sequents: the formulas of
`Y` are those of `X`, with a non-empty part `B` replaced by formulas that are smaller. -/
lemma lt_Sequent_of_split {X Y : Sequent} {Z A B : Multiset Formula}
    (hY : nodeToMultiset Y = Z + A) (hX : nodeToMultiset X = Z + B) (hB : B ≠ 0)
    (hlt : ∀ a ∈ A, ∃ b ∈ B, lmOfFormula a < lmOfFormula b) : ltSequent Y X := by
  refine ⟨Z.map lmOfFormula, A.map lmOfFormula, B.map lmOfFormula, ?_, ?_, ?_, ?_⟩
  · simpa using hB
  · rw [nodeMeasure, hY, Multiset.map_add]
  · rw [nodeMeasure, hX, Multiset.map_add]
  · intro y hy
    rw [Multiset.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, hlt'⟩ := hlt a ha
    exact ⟨lmOfFormula b, Multiset.mem_map_of_mem _ hb, hlt'⟩

/-- **Local rules decrease the Dershowitz-Manna measure.** -/
theorem localRuleApp.decreases_DM (lra : LocalRuleApp) (Y : Sequent) (hY : Y ∈ lra.C) :
    ltSequent Y lra.X := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  obtain ⟨preL, preR, preO⟩ := pre
  subst hC
  simp only [LocalRuleApp.X] at *
  cases lr
  case oneSidedL ress' orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply] at hY
    obtain ⟨res, hres, rfl⟩ := hY
    refine lt_Sequent_of_split (Z := (L \ Lcond).val + R.val + O.toForm)
      (A := (res \ (L \ Lcond)).val) (B := Lcond.val) ?_ ?_ ?_ ?_
    · simp only [nodeToMultiset, Sequent.L, Sequent.R, Sequent.O, Olf.change_old_none_none,
        Finset.sdiff_empty, Finset.union_empty]
      rw [Finset.union_val_sdiff]
      ac_rfl
    · simp only [nodeToMultiset, Sequent.L, Sequent.R, Sequent.O]
      rw [Finset.val_eq_sdiff_add_of_subset preL]
      ac_rfl
    · simpa using orule.precond_ne_nil
    · intro a ha
      rw [Finset.mem_val, Finset.mem_sdiff] at ha
      obtain ⟨φ, hφ, hlt⟩ := orule.lmOfFormula_lt res hres a ha.1
      exact ⟨φ, by simpa using hφ, hlt⟩
  case oneSidedR ress' orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply] at hY
    obtain ⟨res, hres, rfl⟩ := hY
    refine lt_Sequent_of_split (Z := L.val + (R \ Rcond).val + O.toForm)
      (A := (res \ (R \ Rcond)).val) (B := Rcond.val) ?_ ?_ ?_ ?_
    · simp only [nodeToMultiset, Sequent.L, Sequent.R, Sequent.O, Olf.change_old_none_none,
        Finset.sdiff_empty, Finset.union_empty]
      rw [Finset.union_val_sdiff]
      ac_rfl
    · simp only [nodeToMultiset, Sequent.L, Sequent.R, Sequent.O]
      rw [Finset.val_eq_sdiff_add_of_subset preR]
      ac_rfl
    · simpa using orule.precond_ne_nil
    · intro a ha
      rw [Finset.mem_val, Finset.mem_sdiff] at ha
      obtain ⟨φ, hφ, hlt⟩ := orule.lmOfFormula_lt res hres a ha.1
      exact ⟨φ, by simpa using hφ, hlt⟩
  case LRnegL φ => simp [applyLocalRule] at hY
  case LRnegR φ => simp [applyLocalRule] at hY
  case loadedL ress' χ lrule YS_def =>
    subst YS_def
    have hO : O = some (Sum.inl (~'χ)) := (Option.some_subseteq.mp preO).symm
    subst hO
    simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply] at hY
    obtain ⟨⟨Xn, o⟩, hres, rfl⟩ := hY
    refine lt_Sequent_of_split (Z := L.val + R.val)
      (A := (Xn \ L).val + (Olf.change (some (Sum.inl (~'χ))) (some (Sum.inl (~'χ)))
        (o.map Sum.inl)).toForm)
      (B := Olf.toForm (some (Sum.inl (~'χ)))) ?_ ?_ ?_ ?_
    · simp only [nodeToMultiset, Sequent.L, Sequent.R, Sequent.O, Finset.sdiff_empty,
        Finset.union_empty]
      rw [Finset.union_val_sdiff]
      ac_rfl
    · simp only [nodeToMultiset, Sequent.L, Sequent.R, Sequent.O]
    · simp [Olf.toForm]
    · intro a ha
      refine ⟨~χ.unload, by simp [Olf.toForm], ?_⟩
      rw [Multiset.mem_add] at ha
      refine lrule.lmOfFormula_lt (Xn, o) hres a ?_
      rcases ha with ha | ha
      · rw [Finset.mem_val, Finset.mem_sdiff] at ha
        rcases o with _ | nlf <;> simp [pairUnloadSet] <;> tauto
      · rcases o with _ | nlf
        · simp [Olf.change, Option.pdlOverwrite, Olf.toForm] at ha
        · rcases nlf with ⟨lf⟩
          simp only [Olf.change_some, Option.map_some, Olf.toForm, Multiset.mem_singleton] at ha
          subst ha
          simp [pairUnloadSet, negUnload]
  case loadedR ress' χ lrule YS_def =>
    subst YS_def
    have hO : O = some (Sum.inr (~'χ)) := (Option.some_subseteq.mp preO).symm
    subst hO
    simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply] at hY
    obtain ⟨⟨Xn, o⟩, hres, rfl⟩ := hY
    refine lt_Sequent_of_split (Z := L.val + R.val)
      (A := (Xn \ R).val + (Olf.change (some (Sum.inr (~'χ))) (some (Sum.inr (~'χ)))
        (o.map Sum.inr)).toForm)
      (B := Olf.toForm (some (Sum.inr (~'χ)))) ?_ ?_ ?_ ?_
    · simp only [nodeToMultiset, Sequent.L, Sequent.R, Sequent.O, Finset.sdiff_empty,
        Finset.union_empty]
      rw [Finset.union_val_sdiff]
      ac_rfl
    · simp only [nodeToMultiset, Sequent.L, Sequent.R, Sequent.O]
    · simp [Olf.toForm]
    · intro a ha
      refine ⟨~χ.unload, by simp [Olf.toForm], ?_⟩
      rw [Multiset.mem_add] at ha
      refine lrule.lmOfFormula_lt (Xn, o) hres a ?_
      rcases ha with ha | ha
      · rw [Finset.mem_val, Finset.mem_sdiff] at ha
        rcases o with _ | nlf <;> simp [pairUnloadSet] <;> tauto
      · rcases o with _ | nlf
        · simp [Olf.change, Option.pdlOverwrite, Olf.toForm] at ha
        · rcases nlf with ⟨lf⟩
          simp only [Olf.change_some, Option.map_some, Olf.toForm, Multiset.mem_singleton] at ha
          subst ha
          simp [pairUnloadSet, negUnload]

/-! ## Helper functions, relating end nodes and children -/

/-- Locate a child tableau containing a given end node of the parent tableau. -/
def endNodeToEndNodeOfChild {X lrA} def_X subTabs {E}
    (E_in : E ∈ endNodesOf (@LocalTableau.byLocalRule X lrA def_X subTabs)) :
    @Subtype Sequent (fun x => ∃ h, E ∈ endNodesOf (subTabs x h)) := by
  simp only [endNodesOf, Finset.sup_image, Function.id_comp, Finset.mem_sup, Finset.mem_attach,
    true_and, Subtype.exists] at E_in
  let A : Finset Sequent :=
    lrA.C.attach.filterMap
      (fun ⟨Y,Y_in⟩ => if E ∈ endNodesOf (subTabs Y Y_in) then some Y else none)
      (by intro _ _; grind)
  have A_ne : A ≠ {} := by
    unfold A; simp only [ne_eq]
    rcases E_in with ⟨Y, Y_in, E_in⟩
    push Not
    use Y
    exact (Finset.mem_filterMap _).mpr ⟨⟨Y, Y_in⟩, Finset.mem_attach _ _, by simp [E_in]⟩
  let L := A.pdlSeqSort
  have L_ne : L ≠ {} := by unfold L; simp_all
  let Y := L.head L_ne
  have head_in : Y ∈ _ := L.head_mem L_ne
  have Y_in_A : Y ∈ A := (Finset.mem_seqSort A).mp head_in
  refine ⟨Y , ?_, ?_⟩
  · unfold Y L at head_in ⊢
    suffices A ⊆ lrA.C by apply this; exact (Finset.mem_seqSort A).mp head_in
    grind
  · grind

theorem endNodeIsEndNodeOfChild {X} {lrA : LocalRuleApp}
    {subTabs : (Y : Sequent) → Y ∈ lrA.C → LocalTableau Y} (def_X : X = lrA.X)
  (E_in : E ∈ endNodesOf (@LocalTableau.byLocalRule X lrA def_X subTabs)) :
  ∃ Y h, E ∈ endNodesOf (subTabs Y h) := by
  have := endNodeToEndNodeOfChild def_X subTabs E_in
  use this
  aesop

theorem endNodeOfChild_to_endNode
    {Y : Sequent}
    (lrA : LocalRuleApp)
    {ltX : LocalTableau lrA.X}
    subTabs
    (h : ltX = LocalTableau.byLocalRule lrA rfl subTabs)
    (Y_in : Y ∈ lrA.C)
    {Z : Sequent}
    (Z_in : Z ∈ endNodesOf (subTabs Y Y_in))
    : Z ∈ endNodesOf ltX :=
  by
  cases h' : subTabs Y Y_in -- No induction needed for this!
  case sim Y_isSimp =>
    subst h
    simp only [endNodesOf, Finset.sup_image, Function.id_comp, Finset.mem_sup, Finset.mem_attach,
      true_and, Subtype.exists]
    grind
  case byLocalRule C' subTabs' lrA' =>
    subst h
    rw [h'] at Z_in
    simp only [endNodesOf, Finset.sup_image, Function.id_comp, Finset.mem_sup, Finset.mem_attach,
      true_and, Subtype.exists]
    grind

/-- Membership in the end nodes of a local tableau given by a local rule application. -/
lemma mem_endNodesOf_byLocalRule_iff {X} {lra : LocalRuleApp} {X_def : X = lra.X}
    {next : ∀ Y ∈ lra.C, LocalTableau Y} {Z} :
    Z ∈ endNodesOf (LocalTableau.byLocalRule lra X_def next)
      ↔ ∃ Y, ∃ h : Y ∈ lra.C, Z ∈ endNodesOf (next Y h) := by
  simp only [endNodesOf, Finset.sup_image, Function.id_comp, Finset.mem_sup, Finset.mem_attach,
    true_and, Subtype.exists]

/-! ## Overall Soundness and Invertibility of LocalTableau -/

theorem localTableauTruth {X} (lt : LocalTableau X) {W} (M : KripkeModel W) (w : W) :
    (M, w) ⊨ X  ↔ ∃ Y ∈ endNodesOf lt, (M, w) ⊨ Y := by
  induction lt
  case byLocalRule Y lrA X_def next IH  =>
    have := localRuleTruth lrA M w
    aesop
  case sim =>
    simp_all

open HasSat

theorem localTableauSat {X} (lt : LocalTableau X) :
    satisfiable X ↔ ∃ Y ∈ endNodesOf lt, satisfiable Y := by
  constructor
  · rintro ⟨W, M, w, w_X⟩
    rw [localTableauTruth lt M w] at w_X
    rcases w_X with ⟨Y, Y_in, w_Y⟩
    use Y, Y_in, W, M, w
  · rintro ⟨Y, Y_in, ⟨W, M, w, w_Y⟩⟩
    use W, M, w
    apply (localTableauTruth lt M w).2
    use Y

/-! ## Local Tableaux make progress

These lemmas are used to show soundness, in particular `loadedDiamondPaths`.
-/

/-- End nodes of any local tableau are basic. -/
lemma endNodesOf_basic {X Z} {ltZ : LocalTableau Z} : X ∈ endNodesOf ltZ → X.basic := by
  induction ltZ
  case byLocalRule B lrA next IH =>
    intro X_in
    simp [endNodesOf] at X_in
    aesop
  case sim X =>
    simp_all

/-- If `X` is not basic, then for all end nodes `Y` of a
local tableau `lt` for `X` we have that `Y ≠ X`. -/
theorem endNodesOf_nonbasic_non_eq {X Y} (lt : LocalTableau X) (X_nonbas : ¬ X.basic) :
    Y ∈ endNodesOf lt → Y ≠ X := by
  intro Y_in
  have := endNodesOf_basic Y_in
  grind

-- upstream me / Haitian?;-)
lemma IsDershowitzMannaLT.irrefl [Preorder α] [WellFoundedLT α] (X : Multiset α) :
    ¬ Multiset.IsDershowitzMannaLT X X := by
  apply (WellFounded.irrefl (?_)).1
  exact (@Multiset.instWellFoundedIsDershowitzMannaLT α _ _).2

end PDL
