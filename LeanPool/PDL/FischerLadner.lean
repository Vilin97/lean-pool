/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.List

public import LeanPool.PDL.Vocab

/-! # Fischer-Ladner Closure

Here we define a closure on sets (well, actually lists) of formulas.
Our main reference for this closure is Section 6.1 of [HKT2000]
which also was used in a Rocq formalization in [DB2018].
The code for that work can be found at
[github.com/chdoc/comp-dec-pdl](https://github.com/chdoc/comp-dec-pdl)
and their FL closure definition starts at
[line 472 of `PDL_def.v`](https://github.com/chdoc/comp-dec-pdl/blob/master/PDL/PDL_def.v#L472).

See also Definition 4.79 and Exercise 4.8.2 in [BRV2001].
An alternative version following the proof of Theorem 3.2 in [FL1979]
but unfinished is in `Unused/FischerLadnerViaPreForms.lean`.

-/

public section

namespace PDL

/-! ## Definition  -/

mutual
/-- The Fischer-Ladner closure of a formula.
See Section 6.1 of [HKT2000]. Note that there only implication is given.
For our `Formula` type we also need to cover conjunction and negation.
Also note that we are closing under single negations as well here.
The main work is done by `FLb`, which also ensures termination. -/
def FL : Formula → List Formula
| ⊥ => [⊥, ~⊥]
| ·p => [·p, ~·p]
| φ⋀ψ => [φ⋀ψ, ~(φ⋀ψ), ~φ, ~ψ] ++ FL φ ++ FL ψ -- ~φ and ~ψ needed for ~~ case.
| ⌈α⌉φ => [~⌈α⌉φ, ~φ] ++ FLb α φ ++ FL φ -- Note: `~⌈α⌉φ` seems needed for `FLb_trans`.
| ~φ => [~φ] ++ FL φ -- first element needed to deal with ~~φ, ~~~φ etc.

/-- The Fischer-Ladner closure of a box formula,
not recursing into the formula after the box. -/
@[expose] def FLb : Program → Formula → List Formula
| ·a, φ => [ ⌈·a⌉φ, ~⌈·a⌉φ ]
| α⋓β, φ => [ ⌈α⋓β⌉φ, ~⌈α⋓β⌉φ ] ++ FLb α φ ++ FLb β φ
| α;'β, φ => [ ⌈α;'β⌉φ, ~⌈α;'β⌉φ ] ++ FLb α (⌈β⌉φ) ++ FLb β φ
| ∗α, φ => [ ⌈∗α⌉φ, ~⌈∗α⌉φ ] ++ FLb α (⌈∗α⌉φ)
| ?'τ, φ => [ ⌈?'τ⌉φ, ~⌈?'τ⌉φ, ~τ ] ++ FL τ
end

-- Reopen namespaces after mutual blocks to keep source-based declaration audits aligned.
end PDL

namespace PDL

/-! ## Lemmas  -/

/-- Whether a formula has an outer negation constructor. -/
def isNeg : Formula → Prop
| ~_ => True
| _ => False

lemma FL_single_neg_closed {φ} :
    ¬ isNeg φ → ~φ ∈ FL φ := by
  cases φ <;> simp [FL, isNeg, Bot.bot]

@[simp]
lemma FL_refl {φ} :
    φ ∈ FL φ := by
  cases φ
  case box α φ =>
    cases α <;> simp [FL, FLb]
  all_goals
    simp [FL, Bot.bot]

@[simp]
lemma FLb_refl {α φ} :
    (⌈α⌉φ) ∈ FLb α φ := by
  cases α <;> simp [FLb]

@[simp]
lemma neg_mem_FLb : (~⌈α⌉ψ) ∈ FLb α ψ := by cases α <;> simp [FLb]

mutual
/-- Lemma 6.1(i) from [HKT2000] -/
lemma FL_trans {φ ψ} :
    ψ ∈ FL φ → FL ψ ⊆ FL φ := by
  intro ψ_in
  cases φ <;> simp only [FL, List.mem_cons, List.not_mem_nil, or_false, List.cons_append,
    List.nil_append, List.mem_append] at *
  · cases ψ_in <;> subst_eqs <;> simp [FL]
  · cases ψ_in <;> subst_eqs <;> simp [FL]
  · case neg φ =>
    cases ψ_in <;> subst_eqs
    · simp [FL]
    · have IH := @FL_trans φ
      aesop
  case and φ1 φ2 =>
    rcases ψ_in with h|h|h|h|h|h <;> subst_eqs
    · simp [FL]
    · simp [FL]
    · simp [FL]; grind
    · simp [FL]; grind
    · have IH1 := @FL_trans φ1 ψ h
      grind
    · have IH2 := @FL_trans φ2 ψ h
      grind
  case box α φ =>
    rcases ψ_in with h|h|h|h
    · subst_eqs
      simp [FL]
    · subst_eqs
      grind [FL]
    · have := FLb_trans h
      grind [FL]
    · have IH := @FL_trans φ ψ
      grind

/-- Lemma 6.1(ii) from [HKT2000] -/
lemma FLb_trans {α φ ψ} :
    ψ ∈ FLb α φ → FL ψ ⊆ FLb α φ ++ FL (~φ) := by
  intro ψ_in
  cases α <;> simp only [FLb, List.mem_cons, List.not_mem_nil, or_false, List.cons_append,
    List.nil_append, List.mem_append, List.append_assoc] at *
  · cases ψ_in <;> subst_eqs <;> grind [FL, FLb]
  case sequence α1 α2 =>
    rcases ψ_in with h|h|h|h
    · subst_eqs; grind [FL,FLb]
    · subst_eqs; grind [FL,FLb]
    · have IH1 := @FLb_trans α1 (⌈α2⌉φ) ψ h
      intro x x_in
      specialize IH1 x_in
      simp only [FL, List.cons_append, List.nil_append, List.mem_append, List.mem_cons,
        or_self_left] at *
      aesop
    · have IH2 := @FLb_trans α2 φ ψ h
      grind [FL]
  case union α1 α2 =>
    rcases ψ_in with h|h|h|h
    · subst_eqs; grind [FL,FLb]
    · subst_eqs; grind [FL,FLb]
    · have IH1 := @FLb_trans α1 φ ψ h
      intro x x_in
      specialize IH1 x_in
      aesop
    · have IH2 := @FLb_trans α2 φ ψ h
      intro x x_in
      specialize IH2 x_in
      aesop
  case star α =>
    rcases ψ_in with h|h|h
    · subst_eqs; grind [FL,FLb]
    · subst_eqs; grind [FL,FLb]
    · have IH := @FLb_trans α (⌈∗α⌉φ) ψ h
      intro x x_in
      specialize IH x_in
      simp only [FL, List.cons_append, List.nil_append, List.mem_append, List.mem_cons,
        or_self_left] at *
      rcases IH with h|h|h|h|h
      · aesop
      · aesop
      · aesop
      · grind [FLb]
      · aesop
  case test τ =>
    rcases ψ_in with h|h|h
    · subst_eqs; grind [FL, FLb]
    · subst_eqs; simp [FL, FLb]; grind
    · have := @FL_trans τ ψ
      grind [FL]
end

end PDL

namespace PDL

/- Lemma 6.2(i) -/
lemma FL_box_sub {φ α ψ} :
    (⌈α⌉ψ) ∈ FL φ → ψ ∈ FL φ := by
  intro hyp
  apply FL_trans hyp
  simp [FL]

/- A generalization of Lemma 6.2(i) -/
lemma FL_boxes_sub {φ δ ψ} :
    (⌈⌈δ⌉⌉ψ) ∈ FL φ → ψ ∈ FL φ := by
  intro hyp
  induction δ generalizing ψ
  · simp_all
  case cons γ δ IH =>
    simp only [Formula.boxes_cons] at hyp
    exact IH (FL_box_sub hyp)

/- Lemma 6.2(ii) -/
lemma FL_box_test {φ τ ψ} :
    (⌈?'τ⌉ψ) ∈ FL φ → τ ∈ FL φ := by
  intro hyp
  apply FL_trans hyp
  simp [FL, FLb]

/- Lemma 6.2(iii) -/
lemma FL_box_cup {φ α β ψ} :
    (⌈α ⋓ β⌉ψ) ∈ FL φ → (⌈α⌉ψ) ∈ FL φ ∧ (⌈β⌉ψ) ∈ FL φ := by
  intro hyp
  have := FL_trans hyp
  simp [FL, FLb] at this
  aesop

/- Lemma 6.2(iv) -/
lemma FL_box_seq {φ α β ψ} :
    (⌈α;' β⌉ψ) ∈ FL φ → (⌈α⌉⌈β⌉ψ) ∈ FL φ ∧ (⌈β⌉ψ) ∈ FL φ := by
  intro hyp
  have := FL_trans hyp
  simp [FL, FLb] at this
  aesop

/- Lemma 6.2(v) -/
lemma FL_box_star {φ α ψ} :
    (⌈∗α⌉ψ) ∈ FL φ → (⌈α⌉⌈∗α⌉ψ) ∈ FL φ := by
  intro hyp
  have := FL_trans hyp
  simp [FL, FLb] at this
  aesop

/-! ## Closure of a list -/

/-- Concatenate the Fischer-Ladner closures of every formula in a list. -/
@[expose] def FLL (L : List Formula) : List Formula := L.flatMap FL

@[simp]
lemma FLL_refl_sub {L} : L ⊆ FLL L := by induction L <;> simp_all [FLL]

lemma FLL_sub {L1 L2} : L1 ⊆ L2 → FLL L1 ⊆ FLL L2 := by
  unfold FLL
  intro h x x_in
  grind

@[simp]
lemma FLL_nil : FLL [] = [] := List.flatMap_nil

@[simp]
lemma FLL_singelton : FLL [φ] = FL φ := by simp [FLL]

@[simp]
lemma FLL_idem_ext {L φ} : φ ∈ FLL (FLL L) ↔ φ ∈ FLL L := by
  constructor
  · unfold FLL
    intro φ_in
    have := @FL_trans
    grind
  · intro φ_in
    have := @FLL_refl_sub (FLL L)
    grind

lemma FLL_sub_FLL_iff_sub_FLL {L K : List Formula} : L ⊆ FLL K ↔ FLL L ⊆ FLL K := by
  constructor
  · unfold FLL
    rintro h φ' φ'_in
    simp_all only [List.mem_flatMap]
    rcases φ'_in with ⟨φ, φ_in, φ'_in⟩
    specialize h φ_in
    simp only [List.mem_flatMap] at h
    rcases h with ⟨φ'', φ''_in, φ_in⟩
    use φ''
    have := @FL_trans
    grind
  · have := @FLL_refl_sub L
    grind

lemma FLL_append_eq {L K} : FLL (L ++ K) = FLL L ++ FLL K := by simp [FLL]

lemma FLL_diff_sub {L K} : FLL (L \ K) ⊆ FLL L := FLL_sub (List.diff_subset L K)

/-- Being a member of the FL closure of a list does not depend on the position. -/
lemma FLL_ext (h : ∀ φ, φ ∈ L1 ↔ φ ∈ L2) φ : φ ∈ FLL L1  ↔ φ ∈ FLL L2 := by
  simp [FLL] at *
  aesop

/-! ## FL Closure of a Finset of Formulas -/

end PDL

namespace Finset
open PDL

/-- The union of the Fischer-Ladner closures of every formula in a finset. -/
@[expose] def FL (X : Finset Formula) : Finset Formula :=
  X.sup (fun φ => (_root_.PDL.FL φ).toFinset)

@[simp]
lemma FL_refl_sub {X : Finset Formula} : X ⊆ X.FL := by
  intro φ φ_in
  simp_all only [FL, mem_sup, List.mem_toFinset]
  have := @FLL_refl_sub X.pdlSort
  have := @FL_refl φ
  use φ

lemma FL_sub {X Y : Finset Formula} : X ⊆ Y → FL X ⊆ FL Y := by
  unfold FL
  intro h x x_in
  aesop

@[simp]
lemma FL_nil : Finset.FL {} = {} := rfl

@[simp]
lemma FL_singelton {φ} : Finset.FL {φ} = (_root_.PDL.FL φ).toFinset := by simp [FL]

@[simp]
lemma FL_idem_ext {X : Finset Formula} {φ} : φ ∈ FL (FL X) ↔ φ ∈ FL X := by
  constructor
  · unfold FL
    intro φ_in
    simp only [mem_sup, List.mem_toFinset] at *
    rcases φ_in  with ⟨φ2, ⟨⟨φ3, φ3_in, φ2_in⟩, φ_in⟩⟩
    have := FL_trans φ2_in
    grind
  · unfold FL
    intro φ_in
    simp only [mem_sup, List.mem_toFinset] at *
    rcases φ_in with ⟨φ2, φ2_in, φ_in⟩
    use φ2
    simp_all only [and_true]
    have := @FL_refl φ2
    use φ2

lemma FL_sub_FL_iff_sub_FL {X Y : Finset Formula} : X ⊆ FL Y ↔ FL X ⊆ FL Y := by
  constructor
  · unfold FL
    rintro h φ' φ'_in
    simp_all only [mem_sup, List.mem_toFinset]
    rcases φ'_in with ⟨φ, φ_in, φ'_in⟩
    specialize h φ_in
    simp only [mem_sup, List.mem_toFinset] at h
    rcases h with ⟨φ'', φ''_in, φ_in⟩
    use φ''
    have := @FL_trans
    grind
  · intro X_U φ φ_in
    have := @FL_refl_sub
    grind

lemma FL_union_eq {X Y : Finset Formula} :
  FL (X ∪ Y) = FL X ∪ FL Y := by simp [FL]; grind

lemma FL_diff_sub {X Y : Finset Formula} : FL (X \ Y) ⊆ FL X := by
  simp only [FL,]
  intro φ φ_in
  aesop

end Finset

namespace PDL

/-! ## FL stays in the Vocabulary -/

mutual

lemma FL_stays_in_voc {φ ψ} (ψ_in_FL : ψ ∈ FL φ) : ψ.voc ⊆ φ.voc := by
  cases φ <;> simp_all only [FL, List.mem_cons, List.not_mem_nil, or_false, Formula.voc,
    Finset.subset_empty, Finset.subset_singleton_iff, List.cons_append, List.nil_append,
    List.mem_append]
  case neg φ =>
    rcases ψ_in_FL with _|h <;> subst_eqs
    · simp at *
    · exact FL_stays_in_voc h
  case and φ1 φ2 =>
    rcases ψ_in_FL with h|h|h|h|h|h
    · subst_eqs
      simp
    · subst_eqs
      simp
    · subst_eqs
      simp
    · subst_eqs
      simp
    · have IH := FL_stays_in_voc h
      grind
    · have IH := FL_stays_in_voc h
      grind
  case box α φ =>
    rcases ψ_in_FL with h|h|h|h
    · subst_eqs; simp
    · subst_eqs; simp
    · exact FLb_stays_in_voc h
    · have IH := FL_stays_in_voc h
      grind
  all_goals
    cases ψ_in_FL <;> simp_all

lemma FLb_stays_in_voc {α φ ψ} (ψ_in_FLb : ψ ∈ FLb α φ) : ψ.voc ⊆ α.voc ∪ φ.voc := by
  cases α <;> simp_all only [FLb, List.mem_cons, List.not_mem_nil, or_false, Program.voc,
    Finset.singleton_union, List.cons_append, List.nil_append, List.mem_append,
    Finset.union_assoc]
  case atom_prog =>
    aesop
  case sequence α1 α2 =>
    rcases ψ_in_FLb with h|h|h|h
    · subst_eqs; simp
    · subst_eqs; simp
    · have IH := FLb_stays_in_voc h
      aesop
    · have IH := FLb_stays_in_voc h
      grind
  case union α1 α2 =>
    rcases ψ_in_FLb with h|h|h|h
    · subst_eqs; simp
    · subst_eqs; simp
    · have IH := FLb_stays_in_voc h
      grind
    · have IH := FLb_stays_in_voc h
      grind
  case test τ =>
    rcases ψ_in_FLb with h|h|h|h
    · subst_eqs; simp
    · subst_eqs; simp
    · subst_eqs; simp
    · have IH := FL_stays_in_voc h
      grind
  case star α =>
    rcases ψ_in_FLb with h|h|h
    · subst_eqs; simp
    · subst_eqs; simp
    · have IH := FLb_stays_in_voc h
      aesop

end

end PDL

namespace PDL

end PDL
