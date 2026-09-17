/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Lattice.Fold

import LeanPool.PDL.Syntax

/-! # Vocabulary and other Syntax functions (part of Section 2.1) -/

namespace PDL

/-! ## Vocab -/

/-- The finite set of proposition and program indices occurring in syntax. -/
abbrev Vocab := Finset (Sum Nat Nat)

/-- The atomic proposition indices in a vocabulary. -/
def Vocab.atomProps : Vocab → Finset Nat :=
  fun X => X.biUnion (fun x => match x with | Sum.inl n => {n} | Sum.inr _ => {} )

/-- The atomic program indices in a vocabulary. -/
def Vocab.atomProgs : Vocab → Finset Nat :=
  fun X => X.biUnion (fun x => match x with | Sum.inl _ => {} | Sum.inr n => {n} )

mutual
  /-- The proposition and program vocabulary occurring in a program. -/
  @[simp]
  def Program.voc : Program → Vocab
    | ·n => {.inr n}
    | α;'β => α.voc ∪ β.voc
    | α ⋓ β => α.voc ∪ β.voc
    | ∗α => α.voc
    | ?' φ => φ.voc
  /-- The proposition and program vocabulary occurring in a formula. -/
  @[simp]
  def Formula.voc : Formula → Vocab
    | ⊥ => ∅
    | ·n => {.inl n}
    | ~φ => φ.voc
    | φ⋀ψ => φ.voc ∪ ψ.voc
    | ⌈α⌉ φ => α.voc ∪ φ.voc
end

-- Reopen namespaces after mutual blocks to keep source-based declaration audits aligned.
end PDL

namespace PDL

/-- The union of the vocabularies in a list. -/
@[simp]
def Vocab.fromList (L : List Vocab) : Vocab := L.toFinset.sup id

/-- The union of the vocabularies in a finset. -/
@[simp]
def Vocab.fromFinset (L : Finset Vocab) : Vocab := L.sup id

/-- The combined vocabulary of a list of formulas. -/
@[simp]
abbrev _root_.List.pdlFvoc (L : List Formula) := Vocab.fromList (L.map Formula.voc)

/-- The combined vocabulary of a list of programs. -/
@[simp]
abbrev _root_.List.pdlPvoc (L : List Program) := Vocab.fromList (L.map Program.voc)

/-- The combined vocabulary of a finset of formulas. -/
@[simp]
abbrev _root_.Finset.pdlFvoc (L : Finset Formula) := Vocab.fromFinset (L.image Formula.voc)

/-- The combined vocabulary of a finset of programs. -/
@[simp]
abbrev _root_.Finset.pdlPvoc (L : Finset Program) := Vocab.fromFinset (L.image Program.voc)

lemma Finset.mem_fvoc {X : Finset Formula} {x} : x ∈ X.pdlFvoc ↔ ∃ φ ∈ X, x ∈ φ.voc := by
  simp [Finset.pdlFvoc, Vocab.fromFinset, Finset.mem_sup]

lemma Finset.fvoc_union {X Y : Finset Formula} : (X ∪ Y).pdlFvoc = X.pdlFvoc ∪ Y.pdlFvoc := by
  simp [Finset.pdlFvoc, Vocab.fromFinset, Finset.image_union, Finset.sup_union]

lemma Finset.fvoc_mono {X Y : Finset Formula} (h : X ⊆ Y) : X.pdlFvoc ⊆ Y.pdlFvoc := by
  intro x x_in
  rw [Finset.mem_fvoc] at *
  rcases x_in with ⟨φ, φ_in, x_in⟩
  exact ⟨φ, h φ_in, x_in⟩

/-- The vocabulary of a finset of formulas only grows when we add formulas with larger
vocabularies. -/
lemma fvoc_subset_of_mem_voc {L L' : Finset Formula}
    (h : ∀ f ∈ L, ∃ g ∈ L', f.voc ⊆ g.voc) : L.pdlFvoc ⊆ L'.pdlFvoc := by
  intro x hx
  rw [Finset.mem_fvoc] at hx ⊢
  obtain ⟨f, hf, hxf⟩ := hx
  obtain ⟨g, hg, hsub⟩ := h f hf
  exact ⟨g, hg, hsub hxf⟩

theorem Vocab.fromList_append : Vocab.fromList (L ++ R) = Vocab.fromList L ∪ Vocab.fromList R := by
  induction L <;> induction R <;> simp_all

theorem Vocab.fromList_map_iff n (L : List α) f :
    n ∈ Vocab.fromList (L.map f)
    ↔ ∃ x ∈ L, n ∈ f x := by
  simp

theorem Vocab.fromListFormula_map_iff n (L : List Formula) :
    n ∈ Vocab.fromList (L.map Formula.voc)
    ↔ ∃ φ ∈ L, n ∈ Formula.voc φ := by apply fromList_map_iff

theorem Vocab.fromListProgram_map_iff {vocabOfProgram} n (L : List Program) :
    n ∈ Vocab.fromList (L.map vocabOfProgram)
    ↔ ∃ α ∈ L, n ∈ vocabOfProgram α := by
  simp

theorem Formula.voc_boxes : (⌈⌈δ⌉⌉φ).voc = δ.pdlPvoc ∪ φ.voc := by
  induction δ <;> simp_all

/-- The vocabulary of a loaded formula after erasing its loading annotations. -/
@[simp]
def LoadFormula.voc (lf : LoadFormula) : Vocab := (unload lf).voc

/-- The vocabulary of a negated loaded formula after erasing its loading annotations. -/
@[simp]
def NegLoadFormula.voc (nlf : NegLoadFormula) : Vocab := (negUnload nlf).voc

/-! ## Tests in a program -/

/-- Test(α) -/
@[implicit_reducible]
def testsOfProgram : Program → List Formula
| ·_ => []
| ?' τ => [τ] -- no sub-tests etc. needed?
| α;'β => testsOfProgram α ++ testsOfProgram β
| α ⋓ β => testsOfProgram α ++ testsOfProgram β
| ∗α => testsOfProgram α

theorem testsOfProgram.voc α {τ} (τ_in : τ ∈ testsOfProgram α) : τ.voc ⊆ α.voc := by
  cases α <;> simp_all only [testsOfProgram, List.not_mem_nil, List.mem_append, Program.voc,
    List.mem_cons, or_false, Std.le_refl]
  case sequence α β =>
    intro x x_in
    rcases τ_in with hyp | hyp
    all_goals
      have := testsOfProgram.voc _ hyp
      specialize this x_in
      simp only [Finset.mem_union]
      tauto
  case union α β =>
    intro x x_in
    rcases τ_in with hyp | hyp
    all_goals
      have := testsOfProgram.voc _ hyp
      specialize this x_in
      simp only [Finset.mem_union]
      tauto
  case star α =>
    intro x x_in
    have := testsOfProgram.voc _ τ_in
    exact this x_in

/-! ## Subprograms -/

/-- Prog(α) -/
def subprograms : Program → List Program
| ·a => [(·a : Program)]
| ?' φ => [?' φ]
| α;'β => [α;'β ] ++ subprograms α ++ subprograms β
| α ⋓ β => [α ⋓ β] ++ subprograms α ++ subprograms β
| ∗α => [∗α] ++ subprograms α

lemma subprograms_length {α β : Program} :
    β ∈ subprograms α → lengthOfProgram β ≤ lengthOfProgram α := by
  intro β_in
  cases α <;> simp_all only [subprograms, List.mem_cons, List.not_mem_nil, or_false,
    lengthOfProgram.eq_1, lengthOfProgram, Std.le_refl, List.cons_append, List.nil_append,
    List.mem_append, lengthOfProgram.eq_5]
  case sequence α1 α2 =>
    rcases β_in with _|h|h
    · subst_eqs
      simp
    · have IH1 := subprograms_length h
      omega
    · have IH2 := subprograms_length h
      omega
  case union α1 α2 =>
    rcases β_in with _|h|h
    · subst_eqs
      simp
    · have IH1 := subprograms_length h
      omega
    · have IH2 := subprograms_length h
      omega
  case star α =>
    rcases β_in with _|h
    · subst_eqs
      simp
    · have IH1 := subprograms_length h
      omega

lemma length_lt_of_mem_subprograms_erase {α β : Program} :
    β ∈ (subprograms α).erase α → lengthOfProgram β < lengthOfProgram α := by
  cases α <;> simp only [subprograms, List.erase_cons_head, List.not_mem_nil, lengthOfProgram,
    Nat.lt_one_iff, IsEmpty.forall_iff, List.cons_append, List.nil_append, List.mem_append]
  case star α1 =>
    have IH := @length_lt_of_mem_subprograms_erase α1
    grind
  all_goals
    next α1 α2 =>
    have IH := @length_lt_of_mem_subprograms_erase α1
    have IH := @length_lt_of_mem_subprograms_erase α2
    by_cases β = α1 <;> by_cases β = α2 <;> grind

@[simp]
theorem subprograms.refl : α ∈ subprograms α := by
  cases α <;> simp [subprograms]

lemma subprograms_voc {α β} : β ∈ subprograms α → β.voc ⊆ α.voc := by
  cases α <;> simp only [subprograms, List.mem_cons, List.not_mem_nil, or_false, Program.voc,
    Finset.subset_singleton_iff, List.cons_append, List.nil_append, List.mem_append]
  · simp_all
  case sequence α1 α2  =>
    rintro (β_def|β_in|β_in)
    · simp_all
    · have := @subprograms_voc α1 β; intro x x_in; aesop
    · have := @subprograms_voc α2 β; intro x x_in; aesop
  case union α1 α2  =>
    rintro (β_def|β_in|β_in)
    · simp_all
    · have := @subprograms_voc α1 β; intro x x_in; aesop
    · have := @subprograms_voc α2 β; intro x x_in; aesop
  case star α1  =>
    rintro (β_def|β_in)
    · simp_all
    · have := @subprograms_voc α1 β; intro x x_in; aesop
  · simp_all

/-! ## Fresh variables -/

mutual
  /-- Get a fresh atomic proposition `x` not occuring in `ψ`. -/
  def freshVarForm : Formula → Nat
    | ⊥ => 0
    | ·c => c + 1
    | ~φ => freshVarForm φ
    | φ1⋀φ2 => max (freshVarForm φ1) (freshVarForm φ2)
    | ⌈α⌉ φ => max (freshVarProg α) (freshVarForm φ)
  /-- Get a fresh atomic proposition `x` not occuring in `α`. -/
  def freshVarProg : Program → Nat
    | ·_ => 0 -- don't care!
    | α;'β  => max (freshVarProg α) (freshVarProg β)
    | α⋓β  =>  max (freshVarProg α) (freshVarProg β)
    | ∗α  => freshVarProg α
    | ?'φ  => freshVarForm φ
end

end PDL

namespace PDL

mutual
theorem freshVarForm_is_larger (φ) : ∀ n ∈ φ.voc.atomProps, n < freshVarForm φ := by
  cases φ
  all_goals simp only [Vocab.atomProps, Formula.voc, Finset.biUnion_empty, Finset.notMem_empty,
    freshVarForm, Nat.not_lt_zero, imp_self, implies_true, Finset.singleton_biUnion,
    Finset.mem_singleton, forall_eq, Nat.lt_add_one, Finset.mem_biUnion, Sum.exists,
    exists_eq_right', and_false, exists_const, or_false, Finset.mem_union, lt_sup_iff]
  case neg φ =>
    have IH := freshVarForm_is_larger φ
    simp only [Vocab.atomProps, Finset.mem_biUnion, Sum.exists, Finset.mem_singleton,
      exists_eq_right', Finset.notMem_empty, and_false, exists_const, or_false] at *
    assumption
  case and φ1 φ2 =>
    have IH1 := freshVarForm_is_larger φ1
    have IH2 := freshVarForm_is_larger φ2
    simp [Vocab.atomProps] at *
    aesop
  case box α φ =>
    have IHφ := freshVarForm_is_larger φ
    have IHα := freshVarProg_is_larger α
    simp [Vocab.atomProps] at *
    aesop

theorem freshVarProg_is_larger (α) : ∀ n ∈ α.voc.atomProps, n < freshVarProg α := by
  cases α
  all_goals simp only [Vocab.atomProps, Program.voc, Finset.singleton_biUnion,
    Finset.notMem_empty, freshVarProg, Nat.not_lt_zero, imp_self, implies_true,
    Finset.mem_biUnion, Finset.mem_union, Sum.exists, Finset.mem_singleton, exists_eq_right',
    and_false, exists_const, or_false, lt_sup_iff]
  case union α β =>
    have IHα := freshVarProg_is_larger α
    have IHβ := freshVarProg_is_larger β
    simp [Vocab.atomProps] at *
    aesop
  case sequence α β =>
    have IHα := freshVarProg_is_larger α
    have IHβ := freshVarProg_is_larger β
    simp [Vocab.atomProps] at *
    aesop
  case star α =>
    have IHα := freshVarProg_is_larger α
    simp [Vocab.atomProps] at *
    aesop
  case test φ =>
    have IHφ := freshVarForm_is_larger φ
    simp [Vocab.atomProps] at *
    aesop
end

end PDL

namespace PDL

theorem freshVarForm_is_fresh (φ) : Sum.inl (freshVarForm φ) ∉ φ.voc := by
  have := freshVarForm_is_larger φ
  simp only [Vocab.atomProps, Finset.mem_biUnion, Sum.exists, Finset.mem_singleton,
    exists_eq_right', Finset.notMem_empty, and_false, exists_const, or_false] at *
  by_contra hyp
  specialize this (freshVarForm φ)
  have := Nat.lt_irrefl (freshVarForm φ)
  tauto

theorem freshVarProg_is_fresh (α) : Sum.inl (freshVarProg α) ∉ α.voc := by
  have := freshVarProg_is_larger α
  simp only [Vocab.atomProps, Finset.mem_biUnion, Sum.exists, Finset.mem_singleton,
    exists_eq_right', Finset.notMem_empty, and_false, exists_const, or_false] at *
  by_contra hyp
  specialize this (freshVarProg α)
  have := Nat.lt_irrefl (freshVarProg α)
  tauto

end PDL
