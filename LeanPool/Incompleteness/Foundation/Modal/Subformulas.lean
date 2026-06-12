/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Formula

/-! # Subformulas -/



namespace LO
namespace Modal

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Formula.subformulas [DecidableEq α] : Formula α → FormulaFinset α
  | .atom a => {(.atom a)}
  | ⊥      => {⊥}
  | φ ==> ψ  => insert (φ ==> ψ) (φ.subformulas ∪ ψ.subformulas)
  | □φ     => insert (□φ) φ.subformulas

namespace Formula
namespace subformulas

variable [DecidableEq α]

@[simp] lemma mem_self {φ : Formula α} :
    φ ∈ φ.subformulas := by
  induction φ <;> { simp [subformulas]; try tauto; }

variable {φ ψ χ : Formula α}

lemma mem_imp (h : (ψ ==> χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ using Formula.rec' with
  | hfalsum =>
    simp only [subformulas, Finset.mem_singleton] at h
    cases h
  | hatom _ =>
    simp only [subformulas, Finset.mem_singleton] at h
    cases h
  | himp φ₁ φ₂ ihp₁ ihp₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h ⊢
    rcases h with h_eq | h₁ | h₂
    · cases h_eq
      exact ⟨Or.inr (Or.inl mem_self), Or.inr (Or.inr mem_self)⟩
    · have h_sub := ihp₁ h₁
      exact ⟨Or.inr (Or.inl h_sub.1), Or.inr (Or.inl h_sub.2)⟩
    · have h_sub := ihp₂ h₂
      exact ⟨Or.inr (Or.inr h_sub.1), Or.inr (Or.inr h_sub.2)⟩
  | hbox _ ihp =>
    simp only [subformulas, Finset.mem_insert] at h ⊢
    rcases h with h_eq | h_sub
    · cases h_eq
    · have h_sub := ihp h_sub
      exact ⟨Or.inr h_sub.1, Or.inr h_sub.2⟩

lemma mem_imp₁ (h : (ψ ==> χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas := mem_imp h |>.1

lemma mem_imp₂ (h : (ψ ==> χ) ∈ φ.subformulas) : χ ∈ φ.subformulas := mem_imp h |>.2

lemma mem_box (h : □ψ ∈ φ.subformulas) : ψ ∈ φ.subformulas := by
  induction φ using Formula.rec' with
  | hfalsum =>
    simp only [subformulas, Finset.mem_singleton] at h
    cases h
  | hatom _ =>
    simp only [subformulas, Finset.mem_singleton] at h
    cases h
  | himp _ _ ihp₁ ihp₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h ⊢
    rcases h with h_eq | h₁ | h₂
    · cases h_eq
    · exact Or.inr (Or.inl (ihp₁ h₁))
    · exact Or.inr (Or.inr (ihp₂ h₂))
  | hbox _ ihp =>
    simp only [subformulas, Finset.mem_insert] at h ⊢
    rcases h with h_eq | h_sub
    · cases h_eq
      exact Or.inr mem_self
    · exact Or.inr (ihp h_sub)

-- TODO: add tactic like `subformulas`.
attribute [aesop safe 5 forward]
  mem_imp₁
  mem_imp₂
  mem_box

@[simp]
lemma complexity_lower (h : ψ ∈ φ.subformulas) : ψ.complexity ≤ φ.complexity  := by
  induction φ using Formula.rec' with
  | himp φ₁ φ₂ ihp₁ ihp₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h
    rcases h with h_eq | h₁ | h₂
    · subst ψ
      exact le_rfl
    · have h_le := ihp₁ h₁
      change ψ.complexity ≤ max φ₁.complexity φ₂.complexity + 1
      exact le_trans h_le (le_trans (Nat.le_max_left _ _) (Nat.le_succ _))
    · have h_le := ihp₂ h₂
      change ψ.complexity ≤ max φ₁.complexity φ₂.complexity + 1
      exact le_trans h_le (le_trans (Nat.le_max_right _ _) (Nat.le_succ _))
  | hbox φ ihp =>
    simp only [subformulas, Finset.mem_insert] at h
    rcases h with h_eq | h₁
    · subst ψ
      exact le_rfl
    · have h_le := ihp h₁
      change ψ.complexity ≤ φ.complexity + 1
      exact le_trans h_le (Nat.le_succ _)
  | hatom =>
    simp only [subformulas, Finset.mem_singleton] at h
    subst ψ
    exact le_rfl
  | hfalsum =>
    simp only [subformulas, Finset.mem_singleton] at h
    subst ψ
    exact le_rfl

/-
@[simp]
lemma degree_lower (h : ψ ∈ φ.subformulas) : ψ.degree ≤ φ.degree := by
  induction φ using Formula.rec' with
  | himp φ₁ φ₂ ihp₁ ihp₂ =>
    simp_all [subformulas];
    rcases h with rfl | h₁ | h₂;
    · simp_all [Formula.degree];
    · have := ihp₁ h₁; simp [Formula.degree]; omega;
    · have := ihp₂ h₂; simp [Formula.degree]; omega;
  | hbox φ ihp =>
    simp_all [subformulae];
    rcases h with _ | h₁;
    · subst_vars; simp [Formula.degree];
    · have := ihp h₁; simp [Formula.degree]; omega;
  | hatom =>
    simp_all [subformulae];
    rcases h with rfl | rfl <;> simp [Formula.degree];
  | hfalsum => simp_all [subformulae, Formula.degree];
-/

end subformulas
end Formula


/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Modal.FormulaSet.SubformulaClosed (P : FormulaSet α) where
  imp_closed : ∀ {φ ψ}, φ ==> ψ ∈ P → φ ∈ P ∧ ψ ∈ P
  box_closed : ∀ {φ}, □φ ∈ P → φ ∈ P

namespace FormulaSet
namespace SubformulaClosed

variable {φ : Formula α} {P : FormulaSet α} [hP : P.SubformulaClosed]

lemma mem_imp₁ (h : φ ==> ψ ∈ P) : φ ∈ P := hP.imp_closed h |>.1
lemma mem_imp₂ (h : φ ==> ψ ∈ P) : ψ ∈ P := hP.imp_closed h |>.2
lemma mem_box (h : □φ ∈ P) : φ ∈ P := hP.box_closed h

instance {φ : Formula α} [DecidableEq α] :
    FormulaSet.SubformulaClosed (SetLike.coe (φ.subformulas)) where
  box_closed := by
    intro φ hφ;
    exact Formula.subformulas.mem_box hφ;
  imp_closed := by
    intro φ ψ hφ;
    exact Formula.subformulas.mem_imp hφ;

end SubformulaClosed
end FormulaSet

end Modal
end LO
