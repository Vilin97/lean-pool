/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Formula
import LeanPool.Incompleteness.Foundation.Modal.Subformulas

/-! # Complement -/



namespace LO
namespace Modal


namespace Formula

/-- Imported declaration from the Incompleteness formalization. -/
def complement : Formula α → Formula α
  | ∼φ => φ
  | φ  => ∼φ
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "-" => complement

namespace complement

variable {φ ψ : Formula α}

@[simp] lemma neg_def : -(∼φ) = φ := by
  induction φ using Formula.rec' <;> simp_all [complement]

@[simp] lemma bot_def : -(⊥ : Formula α) = ∼(⊥) := by simp only [complement]

@[simp] lemma box_def : -(□φ) = ∼(□φ) := by simp only [complement]

lemma imp_def₁ (hq : ψ ≠ ⊥) : -(φ ==> ψ) = ∼(φ ==> ψ) := by
  simp only [complement];
  split;
  · rename_i h; simp [imp_eq, falsum_eq, hq] at h;
  · rfl;

lemma imp_def₂ (hq : ψ = ⊥) : -(φ ==> ψ) = φ := by
  subst_vars;
  apply neg_def;

lemma resort_box (h : -φ = □ψ) : φ = ∼□ψ := by
  simp [complement] at h;
  split at h;
  · subst_vars; rfl;
  · contradiction;

lemma or (φ : Formula α) : -φ = ∼φ ∨ ∃ ψ, ∼ψ = φ := by
  classical
  induction φ using Formula.casesNeg with
  | himp _ _ hn => simp [imp_def₁ hn];
  | hfalsum => simp;
  | hneg => simp;
  | hatom a => simp [complement];
  | hbox φ => simp [complement]

end complement

end Formula


namespace FormulaFinset

variable [DecidableEq α]

/-- Imported declaration from the Incompleteness formalization. -/
def complementary (P : FormulaFinset α) : FormulaFinset α := P ∪ (P.image (Formula.complement))
/-- Imported declaration from the Incompleteness formalization. -/
postfix:80 "⁻" => complementary

variable {P P₁ P₂ : FormulaFinset α} {φ ψ χ : Formula α}

lemma complementary_mem (h : φ ∈ P) : φ ∈ P⁻ := by simp_all [complementary];

lemma complementary_comp (h : φ ∈ P) : -φ ∈ P⁻ := by simp [complementary]; tauto;

lemma mem_of (h : φ ∈ P⁻) : φ ∈ P ∨ ∃ ψ ∈ P, -ψ = φ := by simpa [complementary] using h;

lemma complementary_mem_box (hi : ∀ {ψ χ}, ψ ==> χ ∈ P → ψ ∈ P := by trivial) :
    □φ ∈ P⁻ → □φ ∈ P := by
  intro h;
  rcases (mem_of h) with (h | ⟨ψ, hq, eq⟩);
  · assumption;
  · replace eq := Formula.complement.resort_box eq;
    subst eq;
    exact hi hq;


/-- Imported declaration from the Incompleteness formalization. -/
class ComplementaryClosed (P : FormulaFinset α) (S : FormulaFinset α) : Prop where
  subset : P ⊆ S⁻
  either : ∀ φ ∈ S, φ ∈ P ∨ -φ ∈ P

/-- Imported declaration from the Incompleteness formalization. -/
def SubformulaeComplementaryClosed (P : FormulaFinset α) (φ : Formula α) :
    Prop :=
  P.ComplementaryClosed φ.subformulas

end FormulaFinset


section «lp_section_1»

variable {α : Type*}
variable {S} [Entailment (Formula α) S]
variable {𝓢 : S} [Entailment.ModusPonens 𝓢]

lemma complement_derive_bot (hp : 𝓢 ⊢! φ) (hcp : 𝓢 ⊢! -φ) : 𝓢 ⊢! ⊥ := by
  classical
  induction φ using Formula.casesNeg with
  | hfalsum => assumption;
  | hatom a => unfold Formula.complement at hcp; exact hcp ⨀ hp;
  | hneg => unfold Formula.complement at hcp; exact hp ⨀ hcp;
  | hbox φ => unfold Formula.complement at hcp; exact hcp ⨀ hp;
  | himp φ ψ h =>
    simp only [Formula.complement.imp_def₁ h] at hcp;
    exact hcp ⨀ hp;

lemma neg_complement_derive_bot (hp : 𝓢 ⊢! ∼φ) (hcp : 𝓢 ⊢! ∼(-φ)) : 𝓢 ⊢! ⊥ := by
  classical
  induction φ using Formula.casesNeg with
  | hfalsum =>
    unfold Formula.complement at hcp;
    exact hcp ⨀ hp;
  | hatom a =>
    unfold Formula.complement at hcp;
    exact hcp ⨀ hp;
  | hneg =>
    unfold Formula.complement at hcp;
    exact hp ⨀ hcp;
  | himp φ ψ h =>
    simp only [Formula.complement.imp_def₁ h] at hcp;
    exact hcp ⨀ hp;
  | hbox φ =>
    unfold Formula.complement at hcp;
    exact hcp ⨀ hp;

end «lp_section_1»

end Modal
end LO
