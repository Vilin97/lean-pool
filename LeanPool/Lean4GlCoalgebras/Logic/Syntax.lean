/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import Mathlib.Data.Set.Defs
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Defs
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Basic
import Aesop
import Mathlib.Tactic.Linarith

/-! ## Syntax of Basic Modal Logic

Here we supply basic definitions, abbreviations, and lemmas about the syntax of BML.
-/

namespace Lean4GlCoalgebras

/-- Type of BML Formulas. -/
inductive Formula : Type
  | bottom : Formula
  | top : Formula
  | atom : Nat → Formula
  | negAtom : Nat → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | box : Formula → Formula
  | diamond : Formula → Formula
deriving Repr,DecidableEq

/-- A sequent is a finite set of formulas, read disjunctively. -/
abbrev Sequent := Finset Formula

namespace Formula

/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:70 "at" => atom
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:70 "na" => negAtom
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:70 "□" => box
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:70 "◇" => diamond
/-- Auxiliary declaration used in the GL coalgebra development. -/
infixr:6 "&" => and
/-- Auxiliary declaration used in the GL coalgebra development. -/
infixr:6 "v" => or

@[simp] instance instBot : Bot (Formula) where bot := Formula.bottom
@[simp] instance instTop : Top (Formula) where top := Formula.top

/-- Negation of a BML Formula. -/
@[simp] def neg : Formula → Formula
  | ⊥ => ⊤
  | ⊤ => ⊥
  | at n => na n
  | na n => at n
  | φ & ψ => (neg φ) v (neg ψ)
  | φ v ψ => (neg φ) & (neg ψ)
  | □ φ => ◇ (neg φ)
  | ◇ φ => □ (neg φ)

/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:50 "~" => Formula.neg
/-- Auxiliary declaration used in the GL coalgebra development. -/
notation:55 φ:56 " ↣ " ψ:55 => (~ φ) v ψ
/-- Auxiliary declaration used in the GL coalgebra development. -/
notation:55 φ:56 " ⟷ " ψ:55 => (φ ↣ ψ) & (ψ ↣ φ)
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:50 " ⊡ " => fun φ ↦ φ & (□ φ)

/-! # Basic operations and simp lemmas for Formulas -/

/-- Returns `true` if the formula is a propositional atom `at n`. -/
def isAtomic : Formula → Bool
  | at _ => true
  | _ => false

/-- Returns `true` if the formula is a negated atom `na n`. -/
def isNegAtomic : Formula → Bool
  | na _ => true
  | _ => false

/-- Returns `true` if the formula is a diamond formula `◇ φ`. -/
def isDiamond : Formula → Bool
  | ◇ _ => true
  | _ => false

/-- Returns `some φ` if the formula is `◇ φ`, otherwise `none`. -/
def opUnDi (φ : Formula) : Option Formula := match φ with
  | ◇ φ => Option.some φ
  | _ => none

@[simp] lemma opUnDi_eq {φ ψ : Formula} : φ.opUnDi = some ψ ↔ φ = ◇ ψ := by
  cases φ <;> simp [Formula.opUnDi]

/-- Extracts `φ` from `◇ φ`, given a proof that the formula is a diamond. -/
def unDi (φ : Formula) (h : φ.isDiamond) : Formula := match φ with
  | ◇ φ => φ

/-- Returns `true` if the formula is a box formula `□ φ`. -/
def isBox : Formula → Bool
  | □ _ => true
  | _ => false


/-- Negation is injective. -/
lemma neg_eq {φ ψ : Formula} : (~φ) = (~ψ) → φ = ψ := by
  intro mpp
  cases φ <;> cases ψ <;> simp [Formula.neg] at mpp <;> try grind
  case and.and φ₁ φ₂ φ₃ φ₄ =>
    have := neg_eq mpp.1
    have := neg_eq mpp.2
    grind
  case or.or φ₁ φ₂ φ₃ φ₄ =>
    have := neg_eq mpp.1
    have := neg_eq mpp.2
    grind
  case box.box φ₁ φ₂ =>
    have := neg_eq mpp
    grind
  case diamond.diamond φ₁ φ₂ =>
    have := neg_eq mpp
    grind

/-- Negation is involutive. -/
@[simp]
lemma neg_neg_eq (φ : Formula) : (~~φ) = φ := by
  induction φ <;> simp_all [Formula.neg]
  · rfl
  · rfl

/-- Length of a BML Formula. -/
def length : Formula → Nat
  | ⊥ => 0
  | ⊤ => 0
  | at _ => 1
  | na _ => 1
  | φ & ψ => length φ + length ψ + 1
  | φ v ψ => length φ + length ψ + 1
  | □ φ => length φ + 1
  | ◇ φ => length φ + 1


/-- Vocab of a BML Formula. Expressed as underlying natural numbers. -/
def vocab : Formula → Finset Nat
  | ⊥ => ∅
  | ⊤ => ∅
  | at n => {n}
  | na n => {n}
  | φ & ψ => vocab φ ∪ vocab ψ
  | φ v ψ => vocab φ ∪ vocab ψ
  | □ φ => vocab φ
  | ◇ φ => vocab φ

/-- Atoms of a BML Formula. Expressed as underlying natural numbers. -/
def atoms : Formula → Finset Nat
  | ⊥ => ∅
  | ⊤ => ∅
  | at n => {n}
  | na _ => ∅
  | φ & ψ => vocab φ ∪ vocab ψ
  | φ v ψ => vocab φ ∪ vocab ψ
  | □ φ => vocab φ
  | ◇ φ => vocab φ

/-- Literals of a BML Formula. Expressed as underlying natural numbers. -/
def lit : Formula → Finset (Nat ⊕ Nat)
  | ⊥ => ∅
  | ⊤ => ∅
  | at n => {Sum.inl n}
  | na n => {Sum.inr n}
  | φ & ψ => lit φ ∪ lit ψ
  | φ v ψ => lit φ ∪ lit ψ
  | □ φ => lit φ
  | ◇ φ => lit φ

/-- Get a fresh variable not occuring in a BML Formula. -/
def freshVar : Formula → Nat
  | ⊤  => 0
  | ⊥  => 0
  | at n  => n + 1
  | na n  => n + 1
  | φ & ψ  => max (freshVar φ) (freshVar ψ)
  | φ v ψ  =>  max (freshVar φ) (freshVar ψ)
  | □ φ  => freshVar φ
  | ◇ φ  => freshVar φ

/-- Fischer-Ladner closure of a BML Formula. -/
def FL : Formula → Sequent
  | ⊥ => {⊥}
  | ⊤ => {⊤}
  | at n => {at n}
  | na n => {na n}
  | φ v ψ => {φ v ψ} ∪ FL φ ∪ FL ψ
  | φ & ψ => {φ & ψ} ∪ FL φ ∪ FL ψ
  | □ φ => {□ φ} ∪ FL φ
  | ◇ φ => {◇ φ} ∪ FL φ

/-! # Lemmas about FL Closure of BML Formulas -/

/-- Fischer-Ladner closure is reflexive. -/
lemma FL_refl {φ : Formula} : φ ∈ FL φ := by
  cases φ <;> simp [FL]
  · rfl
  · rfl

/-- Fischer-Ladner closure is monotone. -/
lemma FL_mon {φ ψ : Formula} (ψ_sub_φ : ψ ∈ FL φ) : FL ψ ⊆ FL φ := by
  cases φ <;>
    simp only [FL, Finset.mem_singleton, Finset.mem_union, Finset.subset_iff] at ψ_sub_φ ⊢
  · intro x x_in
    subst ψ
    simpa only [FL, Finset.mem_singleton] using x_in
  · intro x x_in
    subst ψ
    simpa only [FL, Finset.mem_singleton] using x_in
  · intro x x_in
    subst ψ
    simpa only [FL, Finset.mem_singleton] using x_in
  · intro x x_in
    subst ψ
    simpa only [FL, Finset.mem_singleton] using x_in
  · intro x x_in
    rcases ψ_sub_φ with (rfl | ψ_sub) | ψ_sub
    · simpa only [FL, Finset.mem_singleton, Finset.mem_union] using x_in
    · exact Or.inl (Or.inr (FL_mon ψ_sub x_in))
    · exact Or.inr (FL_mon ψ_sub x_in)
  · intro x x_in
    rcases ψ_sub_φ with (rfl | ψ_sub) | ψ_sub
    · simpa only [FL, Finset.mem_singleton, Finset.mem_union] using x_in
    · exact Or.inl (Or.inr (FL_mon ψ_sub x_in))
    · exact Or.inr (FL_mon ψ_sub x_in)
  · intro x x_in
    rcases ψ_sub_φ with rfl | ψ_sub
    · simpa only [FL, Finset.mem_singleton, Finset.mem_union] using x_in
    · exact Or.inr (FL_mon ψ_sub x_in)
  · intro x x_in
    rcases ψ_sub_φ with rfl | ψ_sub
    · simpa only [FL, Finset.mem_singleton, Finset.mem_union] using x_in
    · exact Or.inr (FL_mon ψ_sub x_in)

end Formula

namespace Sequent

/-! # Basic operations and simp lemmas for Sequents -/
/-- Length of a sequent. -/
def length (Γ : Sequent) : Nat := Finset.sum Γ Formula.length

/- Vocabulary of a sequent. -/
/-- Auxiliary declaration used in the GL coalgebra development. -/
def vocab (Γ : Sequent) : Finset Nat := Finset.biUnion Γ Formula.vocab

/- Literals of a sequent. -/
/-- Auxiliary declaration used in the GL coalgebra development. -/
def lit (Γ : Sequent) : Finset (Nat ⊕ Nat) := Finset.biUnion Γ Formula.lit

/- Negation of a sequent. -/
/-- Auxiliary declaration used in the GL coalgebra development. -/
def neg (Γ : Sequent) : Finset Formula := Finset.biUnion Γ (fun φ ↦ {Formula.neg φ})

/- Given a sequent `Γ`, finds a variable not in `Γ`-/
/-- Auxiliary declaration used in the GL coalgebra development. -/
def freshVar (Γ : Finset Formula) : Nat :=
  if h : Γ = {} then 0 else Finset.max' (Γ.image (Formula.freshVar)) (by
    by_contra con
    simp_all)

/-- Auxiliary declaration used in the GL coalgebra development. -/
def D (Γ : Sequent) : Sequent := Finset.filter (
  fun x => decide (Formula.isDiamond x)) Γ
       ∪ Finset.filterMap Formula.opUnDi Γ (by
  intro A B C C_in_A C_in_B
  cases A <;> cases B
  all_goals
  simp_all [Formula.opUnDi])

lemma form_in_seq_size_le {A : Formula} {Δ : Sequent} : A ∈ Δ → A.length ≤ Δ.length :=
  fun A_in ↦ Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.2 A_in) (by simp)

/-- Fischer-Ladner closure of a sequent. -/
def FL : Sequent → Sequent := fun Δ ↦ Finset.biUnion Δ Formula.FL

/-! # Lemmas about FL Closure of Sequents -/

/- Fischer-Ladner closure is reflexive. -/
lemma FL_refl {Δ : Sequent} : Δ ⊆ FL Δ := by
  intro x x_in
  exact Finset.mem_biUnion.mpr ⟨x, x_in, Formula.FL_refl⟩

/- Fischer-Ladner closure is monotone. -/
lemma FL_mon {Δ Γ : Sequent} (Δ_sub_Γ : Δ ⊆ Γ) : FL Δ ⊆ FL Γ := by
  intro φ φ_in
  rcases Finset.mem_biUnion.mp φ_in with ⟨ψ, ψ_in_Δ, φ_sub_ψ⟩
  exact Finset.mem_biUnion.mpr ⟨ψ, Δ_sub_Γ ψ_in_Δ, φ_sub_ψ⟩

/- Fischer-Ladner closure is idempotent. -/
lemma FL_idem {Δ : Sequent} : FL (FL Δ) = FL Δ := by
  apply Finset.Subset.antisymm
  · intro φ φ_in
    rcases Finset.mem_biUnion.mp φ_in with ⟨ψ, ψ_in, φ_sub_ψ⟩
    rcases Finset.mem_biUnion.mp ψ_in with ⟨χ, χ_in_Δ, ψ_sub_χ⟩
    exact Finset.mem_biUnion.mpr ⟨χ, χ_in_Δ, Formula.FL_mon ψ_sub_χ φ_sub_ψ⟩
  · exact FL_mon FL_refl


end Sequent

/-- Auxiliary declaration used in the GL coalgebra development. -/
abbrev SplitFormula := Formula ⊕ Formula
/-- Auxiliary declaration used in the GL coalgebra development. -/
abbrev SplitSequent := Finset SplitFormula

/-! # Basic operations and simp lemmas for Split Sequents -/

namespace SplitFormula
/-- Auxiliary declaration used in the GL coalgebra development. -/
def isDiamond : SplitFormula → Bool
  | Sum.inl (◇ _) => true
  | Sum.inr (◇ _) => true
  | _ => false

/-- Auxiliary declaration used in the GL coalgebra development. -/
def opUnDi (φ : SplitFormula) : Option SplitFormula := match φ with
  | Sum.inl (◇ ψ) => Option.some (Sum.inl ψ)
  | Sum.inr (◇ ψ) => Option.some (Sum.inr ψ)
  | _ => none


/- Length of a Split Formula (i.e. length of underlying BML Fornula). -/
/-- Auxiliary declaration used in the GL coalgebra development. -/
def length : (Formula ⊕ Formula) → Nat
  | Sum.inl φ => φ.length
  | Sum.inr φ => φ.length

/- Fischer-Ladner closure of a Split Formula (preserving the formula annotation). -/
/-- Auxiliary declaration used in the GL coalgebra development. -/
def FL : SplitFormula → SplitSequent
  | Sum.inl ⊥ => {Sum.inl ⊥}
  | Sum.inr ⊥ => {Sum.inr ⊥}
  | Sum.inl ⊤ => {Sum.inl ⊤}
  | Sum.inr ⊤ => {Sum.inr ⊤}
  | Sum.inl (at n) => {Sum.inl (at n)}
  | Sum.inr (at n) => {Sum.inr (at n)}
  | Sum.inl (na n) => {Sum.inl (na n)}
  | Sum.inr (na n) => {Sum.inr (na n)}
  | Sum.inl (φ v ψ) => {Sum.inl (φ v ψ)} ∪ FL (Sum.inl φ) ∪ FL (Sum.inl ψ)
  | Sum.inr (φ v ψ) => {Sum.inr (φ v ψ)} ∪ FL (Sum.inr φ) ∪ FL (Sum.inr ψ)
  | Sum.inl (φ & ψ) => {Sum.inl (φ & ψ)} ∪ FL (Sum.inl φ) ∪ FL (Sum.inl ψ)
  | Sum.inr (φ & ψ) => {Sum.inr (φ & ψ)} ∪ FL (Sum.inr φ) ∪ FL (Sum.inr ψ)
  | Sum.inl (□ φ) => {Sum.inl (□ φ)} ∪ FL (Sum.inl φ)
  | Sum.inr (□ φ) => {Sum.inr (□ φ)} ∪ FL (Sum.inr φ)
  | Sum.inl (◇ φ) => {Sum.inl (◇ φ)} ∪ FL (Sum.inl φ)
  | Sum.inr (◇ φ) => {Sum.inr (◇ φ)} ∪ FL (Sum.inr φ)

/-! # Lemmas about FL Closure of Split Formulas -/

lemma FL_SplitFormula_left_eq_FL_Formula_map (φ : Formula) :
  FL (Sum.inl φ) = φ.FL.map ⟨Sum.inl, Sum.inl_injective⟩ := by
  induction φ <;> simp_all [FL, Formula.FL, Finset.map_union]

lemma FL_SplitFormula_right_eq_FL_Formula_map (φ : Formula) :
  FL (Sum.inr φ) = φ.FL.map ⟨Sum.inr, Sum.inr_injective⟩ := by
  induction φ <;> simp_all [FL, Formula.FL, Finset.map_union]

lemma in_FL_SplitFormula_left {φ : Formula} {ψ : SplitFormula}
  (ψ_sub_φ : ψ ∈ FL (Sum.inl φ)) : ψ.isLeft := by
  induction φ <;> simp_all [FL] <;> grind

lemma in_FL_SplitFormula_right {φ : Formula} {ψ : SplitFormula}
  (ψ_sub_φ : ψ ∈ FL (Sum.inr φ)) : ψ.isRight := by
  induction φ <;> simp_all [FL] <;> grind

lemma in_FL_of_in_FL_SplitFormula_left {φ : Formula} {ψ : SplitFormula}
  (ψ_sub_φ : ψ ∈ FL (Sum.inl φ)) : ψ.elim id id ∈ φ.FL := by
  rcases ψ with ψ | ψ <;> induction φ <;> simp_all [FL, Formula.FL] <;> grind

lemma in_FL_of_in_FL_SplitFormula_right {φ : Formula} {ψ : SplitFormula}
  (ψ_sub_φ : ψ ∈ FL (Sum.inr φ)) : ψ.elim id id ∈ φ.FL := by
  rcases ψ with ψ | ψ <;> induction φ <;> simp_all [FL, Formula.FL] <;> grind

/-- Fischer-Ladner Closure is reflexive. -/
lemma FL_refl {φ : SplitFormula} : φ ∈ FL φ := by
  rcases φ with φ | φ <;> cases φ <;> simp [FL]
  · rfl
  · rfl
  · rfl
  · rfl

/-- Fischer-Ladner Closure is monotone. -/
lemma FL_mon {φ ψ : SplitFormula} (ψ_sub_φ : ψ ∈ FL φ) : FL ψ ⊆ FL φ := by
  rcases φ with φ | φ
  · rcases ψ with ψ | ψ
    · rw [FL_SplitFormula_left_eq_FL_Formula_map φ, FL_SplitFormula_left_eq_FL_Formula_map ψ]
      intro x x_in
      rcases Finset.mem_map.mp x_in with ⟨χ, χ_in, rfl⟩
      exact Finset.mem_map.mpr
        ⟨χ, Formula.FL_mon (in_FL_of_in_FL_SplitFormula_left ψ_sub_φ) χ_in, rfl⟩
    · have is_left := in_FL_SplitFormula_left ψ_sub_φ
      change false = true at is_left
      cases is_left
  · rcases ψ with ψ | ψ
    · have is_right := in_FL_SplitFormula_right ψ_sub_φ
      change false = true at is_right
      cases is_right
    · rw [FL_SplitFormula_right_eq_FL_Formula_map φ, FL_SplitFormula_right_eq_FL_Formula_map ψ]
      intro x x_in
      rcases Finset.mem_map.mp x_in with ⟨χ, χ_in, rfl⟩
      exact Finset.mem_map.mpr
        ⟨χ, Formula.FL_mon (in_FL_of_in_FL_SplitFormula_right ψ_sub_φ) χ_in, rfl⟩

end SplitFormula

namespace SplitSequent

/-! # Lemmas about FL Closure of Split Sequents -/
/-- Auxiliary declaration used in the GL coalgebra development. -/
def FL : SplitSequent → SplitSequent := fun Δ ↦ Finset.biUnion Δ SplitFormula.FL

/-- Fischer-Ladner Closure is reflexive. -/
lemma FL_refl {Δ : SplitSequent} : Δ ⊆ FL Δ := by
  intro x x_in
  exact Finset.mem_biUnion.mpr ⟨x, x_in, SplitFormula.FL_refl⟩

/-- Fischer-Ladner Closure is monotone. -/
lemma FL_mon {Δ Γ : SplitSequent} (Δ_sub_Γ : Δ ⊆ Γ) : FL Δ ⊆ FL Γ := by
  intro φ φ_in
  rcases Finset.mem_biUnion.mp φ_in with ⟨ψ, ψ_in_Δ, φ_sub_ψ⟩
  exact Finset.mem_biUnion.mpr ⟨ψ, Δ_sub_Γ ψ_in_Δ, φ_sub_ψ⟩

/-- Fischer-Ladner Closure is idempotent. -/
lemma FL_idem {Δ : SplitSequent} : FL (FL Δ) = FL Δ := by
  apply Finset.Subset.antisymm
  · intro φ φ_in
    rcases Finset.mem_biUnion.mp φ_in with ⟨ψ, ψ_in, φ_sub_ψ⟩
    rcases Finset.mem_biUnion.mp ψ_in with ⟨χ, χ_in_Δ, ψ_sub_χ⟩
    exact Finset.mem_biUnion.mpr ⟨χ, χ_in_Δ, SplitFormula.FL_mon ψ_sub_χ φ_sub_ψ⟩
  · exact FL_mon FL_refl

/-- □₄⁻¹ operator for Split Sequents. -/
def D (Γ : SplitSequent) : SplitSequent
  := Finset.filter (fun x => decide (SplitFormula.isDiamond x)) Γ
                         ∪ Finset.filterMap SplitFormula.opUnDi Γ (by
  intro φ ψ C C_in_A C_in_B
  rcases φ with φ | φ <;> rcases ψ with ψ | ψ <;> rcases C with C | C
  all_goals
    simp_all
    cases φ <;> cases ψ
    all_goals
      simp_all [SplitFormula.opUnDi])

/-! # Basic operations and simp lemmas for Split Sequents -/

/-- Find underlying Sequent of a Split Sequent. -/
def toSequent (Δ : SplitSequent) : Sequent := Finset.image (Sum.elim id id) Δ

/-- Length of a Split Sequent. -/
def length (Δ : SplitSequent) : Nat := Finset.sum Δ (SplitFormula.length)

@[simp]
lemma opUnDi_eqₗₗ {φ ψ : Formula} :
    SplitFormula.opUnDi (Sum.inl φ) = some (Sum.inl ψ) ↔ φ = ◇ ψ := by
  cases φ <;> simp [SplitFormula.opUnDi]

@[simp]
lemma opUnDi_eqᵣᵣ {φ ψ : Formula} :
    SplitFormula.opUnDi (Sum.inr φ) = some (Sum.inr ψ) ↔ φ = ◇ ψ := by
  cases φ <;> simp [SplitFormula.opUnDi]

@[simp]
lemma opUnDi_eqₗᵣ {φ ψ : Formula} : ¬ (SplitFormula.opUnDi (Sum.inl φ) = some (Sum.inr ψ)) := by
  cases φ <;> simp [SplitFormula.opUnDi]

@[simp]
lemma opUnDi_eqᵣₗ {φ ψ : Formula} : ¬ (SplitFormula.opUnDi (Sum.inr φ) = some (Sum.inl ψ)) := by
  cases φ <;> simp [SplitFormula.opUnDi]

/-- Auxiliary declaration used in the GL coalgebra development. -/
@[simp]
noncomputable def filterLeft : SplitSequent → SplitSequent := @Finset.filter _
  (fun | Sum.inl _ => true | Sum.inr _ => false)
  (fun | Sum.inl _ => isTrue (by simp) | Sum.inr _ => isFalse (by simp))

/-- Auxiliary declaration used in the GL coalgebra development. -/
@[simp]
noncomputable def filterRight : SplitSequent → SplitSequent := @Finset.filter _
  (fun | Sum.inl _ => false | Sum.inr _ => true)
  (fun | Sum.inl _ => isFalse (by simp) | Sum.inr _ => isTrue (by simp))

/-- Auxiliary declaration used in the GL coalgebra development. -/
def left (Γ : SplitSequent) : Sequent := Γ.filterMap (Sum.getLeft?) (by aesop)
/-- Auxiliary declaration used in the GL coalgebra development. -/
def right (Γ : SplitSequent) : Sequent := Γ.filterMap (Sum.getRight?) (by aesop)

end SplitSequent

/-! # Properties of Substitutions -/

/-- Substiting `p` with `ψ` in `φ` (`φ[ψ/p]`). -/
def single (n : Nat) (ψ : Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at k => if k == n then ψ else at k
  | na k => if k == n then ~ ψ else na k
  | φ₁ & φ₂ => (single n ψ φ₁) & (single n ψ φ₂)
  | φ₁ v φ₂ => (single n ψ φ₁) v (single n ψ φ₂)
  | □ φ => □ (single n ψ φ)
  | ◇ φ => ◇ (single n ψ φ)

/- Single substitution preserves negation. -/
lemma single_neg (n : Nat) (φ ψ : Formula) : single n ψ (~φ) = (~ (single n ψ φ)) := by
  induction φ <;> simp [Formula.neg, single] <;> aesop

/- Single substitution preserves implication. -/
lemma single_imp (n : Nat) (C D E : Formula) :
    single n C (D ↣ E) = (single n C D) ↣ (single n C E) := by
  simp [single, single_neg]

/- Single substitution preserves bi-implication. -/
lemma single_iff (n : Nat) (C D E : Formula) :
    single n C (D ⟷ E) = (single n C D) ⟷ (single n C E) := by
  simp [single, single_neg]

@[simp]
lemma single_identity (n : ℕ) (φ : Formula) : (single n (at n) φ) = φ := by
  induction φ <;> simp_all [single]
  · rfl
  · rfl

/-- Simultaneous substitution for `p` meeting criteria `c`. -/
def partial_ {c : Nat → Prop} [DecidablePred c] (σ : Subtype c → Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => if h : c n then σ ⟨n, h⟩ else at n
  | na n => if h : c n then ~ σ ⟨n, h⟩ else na n
  | A & B => (partial_ σ A) & (partial_ σ B)
  | A v B => (partial_ σ A) v (partial_ σ B)
  | □ A => □ (partial_ σ A)
  | ◇ A => ◇ (partial_ σ A)

/-- Full substitution of all `p`. -/
def full (σ : Nat → Formula) (A : Formula) : Formula := match A with
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n => σ n
  | na n => ~ (σ n)
  | A & B => (full σ A) & (full σ B)
  | A v B => (full σ A) v (full σ B)
  | □ A => □ (full σ A)
  | ◇ A => ◇ (full σ A)
termination_by Formula.length A
decreasing_by
  all_goals
  simp [Formula.length]
  try linarith

/-! # Properties of Vocab -/

/- `p` is in the vocabulary of `φ` if and only if `p` is in the vocabulary of `~φ`. -/
@[simp] lemma in_neg_voc_iff {n : Nat} {φ : Formula} : n ∈ (~φ).vocab ↔ n ∈ φ.vocab := by
  induction φ <;> simp_all [Formula.vocab]

lemma in_single_voc (m n : Nat) (φ ψ : Formula) :
  m ∉ φ.vocab → (m ≠ n → m ∉ ψ.vocab) → n ∉ φ.vocab → m ∉ (single n φ ψ).vocab
  := by
    intro mp
    induction ψ <;>
      simp_all only [single, Formula.vocab, Finset.notMem_empty, Finset.mem_singleton,
        Finset.mem_union, not_or, beq_iff_eq, ne_eq]
    case atom k =>
      intro hψ hn m_in
      by_cases hk : k = n
      · subst k
        exact mp (by simpa only [if_true] using m_in)
      · by_cases hm : m = n
        · subst m
          exact (Ne.symm hk) (by
            simpa only [hk, if_false, Formula.vocab, Finset.mem_singleton] using m_in)
        · exact hψ hm (by
            simpa only [hk, if_false, Formula.vocab, Finset.mem_singleton] using m_in)
    case negAtom k =>
      intro hψ hn m_in
      by_cases hk : k = n
      · subst k
        exact mp (by simpa only [if_true, in_neg_voc_iff] using m_in)
      · by_cases hm : m = n
        · subst m
          exact (Ne.symm hk) (by
            simpa only [hk, if_false, Formula.vocab, Finset.mem_singleton] using m_in)
        · exact hψ hm (by
            simpa only [hk, if_false, Formula.vocab, Finset.mem_singleton] using m_in)
    all_goals aesop

lemma not_in_single_voc (n : Nat) (φ ψ : Formula) :
  n ∉ φ.vocab → (single n ψ φ) = φ := by
  intro h
  induction φ <;> simp_all [single, Formula.vocab] <;> aesop

lemma not_in_single_top_voc (n : ℕ) (φ : Formula) : n ∉ (single n ⊤ φ).vocab := by
  apply in_single_voc n n ⊤ φ
  · simpa only [Formula.instTop, Formula.vocab] using Finset.notMem_empty n
  · intro h
    exact False.elim (h rfl)
  · simpa only [Formula.instTop, Formula.vocab] using Finset.notMem_empty n

lemma not_in_single_bot_voc (n : ℕ) (φ : Formula) : n ∉ (single n ⊥ φ).vocab := by
  apply in_single_voc n n ⊥ φ
  · simpa only [Formula.instBot, Formula.vocab] using Finset.notMem_empty n
  · intro h
    exact False.elim (h rfl)
  · simpa only [Formula.instBot, Formula.vocab] using Finset.notMem_empty n

lemma in_single_voc' {m n : ℕ} {φ ψ : Formula} :
    m ∈ (single n φ ψ).vocab →
      (m ∈ φ.vocab ∧ n ∈ ψ.vocab) ∨ (m ∈ ψ.vocab ∧ m ≠ n) := by
  intro m_in
  induction ψ <;> simp_all [single] <;>
    try grind [Formula.vocab, in_neg_voc_iff, Formula.instTop, Formula.instBot]


/-! # Some very specific lemmas about Finset.sum

Ideally grind or aesop or some other tactic could sort out these simple helper lemmas, but I could
not figure out how.
-/

lemma sub_add_left {n m l : Nat} : n + m = l → n = l - m := by omega

lemma lt_and_le_imp_add_lt {a b c : ℕ} : b ≤ a → c < b → (a - b) + c < a := by omega

lemma Finset.sum_diff_singleton_lt {α : Type} [DecidableEq α] {A C : Finset α} {b : α} {f : α → Nat}
  : b ∈ A → C.sum f < f b → Finset.sum ((A \ {b}) ∪ C) f < Finset.sum A f := by
  intro b_in_A C_lt_B
  calc
    _ ≤ Finset.sum (A \ {b}) f + Finset.sum C f := by
      simp [sub_add_left <| @Finset.sum_union_inter _ _ (A \ {b}) C _ f _]
    _ = Finset.sum A f - Finset.sum {b} f + Finset.sum C f := by
      have singleton_subset : {b} ⊆ A := Finset.singleton_subset_iff.2 b_in_A
      simp [sub_add_left <| @Finset.sum_sdiff α Nat {b} A _ f _ singleton_subset]
    _ < Finset.sum A f := by
      apply lt_and_le_imp_add_lt
      · exact
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.singleton_subset_iff.2 b_in_A)
            (by simp)
      · exact C_lt_B
end Lean4GlCoalgebras
