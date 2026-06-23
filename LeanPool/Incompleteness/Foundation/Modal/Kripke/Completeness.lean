/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.MaximalConsistentSet
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Basic

/-! # Completeness -/


namespace LO
namespace Modal

open Entailment
open Formula
open Kripke
open MaximalConsistentSet

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
abbrev canonicalFrame (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] : Kripke.Frame where
  World := MaximalConsistentSet 𝓢
  Rel X Y := □''⁻¹X.1 ⊆ Y.1

namespace canonicalFrame

variable {Ω₁ Ω₂ : (canonicalFrame 𝓢).World}

@[simp] lemma rel_def_box : Ω₁ ≺ Ω₂ ↔ ∀ {φ}, □φ ∈ Ω₁ → φ ∈ Ω₂ := by simp [Frame.Rel']; aesop;

lemma multirel_def_multibox : Ω₁ ≺^[n] Ω₂ ↔ ∀ {φ}, □^[n]φ ∈ Ω₁.1 → φ ∈ Ω₂.1 := by
  induction n generalizing Ω₁ Ω₂ with
  | zero =>
    simp_all only [Rel.iterate.iff_zero, Function.iterate_zero, id_eq];
    constructor;
    · intro h; tauto_set;
    · intro h;
      apply intro_equality;
      tauto_set;
  | succ n ih =>
    constructor;
    · intro h φ hp;
      obtain ⟨⟨Ω₃, _⟩, R₁₃, R₃₂⟩ := h;
      apply ih.mp R₃₂ <| rel_def_box.mp R₁₃ (by
        simp only [Function.iterate_succ_apply'] at hp; exact hp);
    · intro h;
      obtain ⟨Ω, hΩ⟩ := lindenbaum (𝓢 := 𝓢) (T := (□''⁻¹Ω₁.1 ∪ ◇''^[n]Ω₂.1)) <| by
        apply FormulaSet.intro_union_consistent;
        rintro Γ Δ ⟨hΓ, hΔ⟩ hC;
        replace hΓ : ∀ φ ∈ Γ, □φ ∈ Ω₁ := fun φ hpp => hΓ φ hpp;
        have dΓconj : Ω₁.1 *⊢[𝓢]! □⋀Γ := membership_iff.mp <| iff_mem_box_conj.mpr hΓ;
        have hΔ₂ : ∀ φ ∈ ◇'⁻¹^[n]Δ, φ ∈ Ω₂ := by
          intro φ hp;
          exact Set.iff_mem_multidia.mp <| hΔ (◇^[n]φ) (by simpa using hp);
        have hΔconj : ⋀◇'⁻¹^[n]Δ ∈ Ω₂ := iff_mem_conj.mpr hΔ₂;
        have : ⋀◇'⁻¹^[n]Δ ∉ Ω₂ := by {
          have d₁ : 𝓢 ⊢! ⋀Γ ==> ⋀Δ ==> ⊥ := and_imply_iff_imply_imply'!.mp hC;
          have : 𝓢 ⊢! ⋀(◇'^[n]◇'⁻¹^[n]Δ) ==> ⋀Δ := by
            apply conjconj_subset!;
            intro ψ hq;
            obtain ⟨χ, _, _⟩ := hΔ ψ hq;
            subst_vars;
            simpa;
          have : 𝓢 ⊢! ◇^[n]⋀◇'⁻¹^[n]Δ ==> ⋀Δ := imp_trans''! iff_conjmultidia_multidiaconj! <| this;
          have : 𝓢 ⊢! ∼(□^[n](∼⋀◇'⁻¹^[n]Δ)) ==> ⋀Δ := imp_trans''! (and₂'! multidia_duality!) this;
          have : 𝓢 ⊢! ∼⋀Δ ==> □^[n](∼⋀◇'⁻¹^[n]Δ) := contra₂'! this;
          have : 𝓢 ⊢! (⋀Δ ==> ⊥) ==> □^[n](∼⋀◇'⁻¹^[n]Δ) := imp_trans''! (and₂'! negEquiv!) this;
          have : 𝓢 ⊢! ⋀Γ ==> □^[n](∼⋀◇'⁻¹^[n]Δ) := imp_trans''! d₁ this;
          have : 𝓢 ⊢! □⋀Γ ==> □^[(n + 1)](∼⋀◇'⁻¹^[n]Δ) := by
            simpa using imply_box_distribute'! this;
          exact iff_mem_neg.mp <| h <| membership_iff.mpr <| (Context.of! this) ⨀ dΓconj;
        }
        contradiction;
      use Ω;
      constructor;
      · intro φ hp;
        apply hΩ;
        simp_all;
      · apply ih.mpr;
        apply multibox_multidia.mpr;
        intro φ hp;
        apply hΩ;
        simp_all;

lemma multirel_def_multibox' : Ω₁ ≺^[n] Ω₂ ↔ ∀ {φ}, φ ∈ (□''⁻¹^[n]Ω₁.1) → φ ∈ Ω₂.1 := by
  constructor;
  · intro h φ hp; exact multirel_def_multibox.mp h hp;
  · intro h; apply multirel_def_multibox.mpr; assumption;

lemma multirel_def_multidia : Ω₁ ≺^[n] Ω₂ ↔ ∀ {φ}, (φ ∈ Ω₂.1 → ◇^[n]φ ∈ Ω₁.1) :=
  Iff.trans multirel_def_multibox multibox_multidia

lemma rel_def_dia : Ω₁ ≺ Ω₂ ↔ ∀ {φ}, φ ∈ Ω₂.1 → ◇φ ∈ Ω₁.1 := by
  rw [rel_def_box]
  have h := multibox_multidia (n := 1) (Ω₁ := Ω₁) (Ω₂ := Ω₂)
  simp only [Function.iterate_one] at h
  exact h

end canonicalFrame


/-- Imported declaration from the Incompleteness formalization. -/
abbrev canonicalModel (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] : Model where
  toFrame := canonicalFrame 𝓢
  Val Ω a := (atom a) ∈ Ω.1

@[reducible]
instance : Semantics (Formula ℕ) (canonicalModel 𝓢).World :=
  Formula.Kripke.Satisfies.semantics (M := canonicalModel 𝓢)


section «lp_section_1»

variable {φ ψ : Formula ℕ}

lemma truthlemma : ∀ {Ω : (canonicalModel 𝓢).World}, Ω ⊧ φ ↔ (φ ∈ Ω.1) := by
  induction φ using Formula.rec' with
  | hatom => simp_all [Semantics.Realize, Kripke.Satisfies];
  | hfalsum =>
    simp only [Semantics.Realize, Satisfies, false_iff];
    exact not_mem_falsum;
  | hbox φ ih =>
    intro Ω;
    constructor;
    · intro h;
      apply iff_mem_box.mpr;
      intro Ω' hΩ';
      apply ih.mp;
      exact h Ω' hΩ';
    · intro h Ω' hΩ';
      apply ih.mpr;
      exact canonicalFrame.rel_def_box.mp hΩ' h;
  | himp φ ψ ihp ihq =>
    intro Ω;
    constructor;
    · intro h;
      apply iff_mem_imp.mpr;
      intro hp; replace hp := ihp.mpr hp;
      exact ihq.mp <| h hp;
    · intro h;
      have := iff_mem_imp.mp h;
      intro hp; replace hp := ihp.mp hp;
      exact ihq.mpr <| this hp


lemma iff_valid_on_canonicalModel_deducible : (canonicalModel 𝓢) ⊧ φ ↔ 𝓢 ⊢! φ := by
  constructor;
  · contrapose;
    intro h;
    have : FormulaSet.Consistent 𝓢 ({∼φ}) := by
      apply FormulaSet.def_consistent.mpr;
      intro Γ hΓ;
      by_contra hC;
      have : 𝓢 ⊢! φ := dne'! <| negEquiv'!.mpr <| replace_imply_left_conj! hΓ hC;
      contradiction;
    obtain ⟨Ω, hΩ⟩ := lindenbaum this;
    apply ValidOnModel.not_of_exists_world;
    use Ω;
    exact truthlemma.not.mpr <| iff_mem_neg.mp (by tauto_set);
  · intro h Ω;
    suffices φ ∈ Ω.1 by exact truthlemma.mpr this;
    by_contra hC;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := FormulaSet.iff_insert_inconsistent.mp <| (Ω.maximal' hC);
    have : Γ ⊢[𝓢]! ⊥ := FiniteContext.provable_iff.mpr <| and_imply_iff_imply_imply'!.mp hΓ₂ ⨀ h;
    have : Γ ⊬[𝓢] ⊥ := FormulaSet.def_consistent.mp (Ω.consistent) _ hΓ₁;
    contradiction;

end «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
class Canonical (𝓢 : S) [Entailment.Consistent 𝓢] [Entailment.K 𝓢] (C : FrameClass) : Prop where
  canonical : (Kripke.canonicalFrame 𝓢) ∈ C

instance [Canonical 𝓢 C] : Complete 𝓢 C := ⟨by
  intro φ hφ
  by_contra h
  exact
    (ValidOnFrameClass.not_of_exists_model (by
      use (canonicalModel 𝓢)
      constructor
      · exact Canonical.canonical
      · exact iff_valid_on_canonicalModel_deducible.not.mpr h)) hφ
⟩

end Kripke

end Modal
end LO
