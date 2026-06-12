/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Vorspiel.BinaryRelations
import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.K
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach

/-! # AxiomGrz -/


namespace LO
namespace Modal

namespace Kripke

open Entailment
open Kripke
open Formula.Kripke
open Relation (IrreflGen)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass :
    FrameClass :=
  { F | Std.Refl F.Rel ∧ IsTrans F.World F.Rel ∧ WeaklyConverseWellFounded F.Rel }
/-- Imported declaration from the Incompleteness formalization. -/
abbrev ReflexiveTransitiveAntiSymmetricFiniteFrameClass :
    FiniteFrameClass :=
  { F | Std.Refl F.Rel ∧ IsTrans F.World F.Rel ∧ Std.Antisymm F.Rel }

variable {F : Kripke.Frame}

lemma validate_Grz_of_refl_trans_wcwf
  (hRefl : Std.Refl F.Rel)
  (hTrans : IsTrans F.World F.Rel)
  (hWCWF : WeaklyConverseWellFounded F.Rel)
  : F ⊧ (Axioms.Grz (.atom 0)) := by
  intro V;
  let X :=
    { x | Satisfies ⟨F, V⟩ x (□(□((.atom 0) ==> □(.atom 0)) ==> (.atom 0))) ∧
      ¬(Satisfies ⟨F, V⟩ x (.atom 0)) };
  let Y :=
    { x | Satisfies ⟨F, V⟩ x (□(□((.atom 0) ==> □(.atom 0)) ==> (.atom 0))) ∧
      ¬(Satisfies ⟨F, V⟩ x (□(.atom 0))) ∧ (Satisfies ⟨F, V⟩ x (.atom 0)) };
  have : (X ∩ Y) = ∅ := by aesop;
  suffices ∀ x ∈ X ∪ Y, ∃ y ∈ X ∪ Y, (IrreflGen F.Rel) x y by
    have : (X ∪ Y) = ∅ := by
      by_contra hC;
      replace hC := Set.nonempty_iff_ne_empty.mpr hC;
      obtain ⟨z, z_sub, hz⟩ := hWCWF.has_min (X ∪ Y) hC;
      obtain ⟨x, x_sub, hx⟩ := this z z_sub;
      exact hz x x_sub hx;
    have : X = ∅ := by tauto_set;
    -- TODO: need more refactor
    have := Set.not_nonempty_iff_eq_empty.mpr this;
    have := Set.nonempty_def.not.mp this; push Not at this;
    simp only [X, Set.mem_setOf_eq, not_and, not_not] at this; exact this;
  rintro w (⟨hw₁, hw₂⟩ | ⟨hw₁, hw₂, hw₃⟩);
  · have := hw₁ _ (by exact hRefl.refl w);
    have := not_imp_not.mpr this hw₂;
    obtain ⟨x, Rwx, hx, ⟨y, Rxy, hy⟩⟩ := by simpa [Satisfies] using this;
    use x;
    constructor;
    · right;
      refine ⟨?_, ?_, by assumption⟩;
      · intro z Rxz hz;
        exact hw₁ z (hTrans.trans _ _ _ Rwx Rxz) hz;
      · simp only [Satisfies.box_def, not_forall];
        exact ⟨y, Rxy, hy⟩;
    · constructor;
      · by_contra hC;
        subst hC;
        simp [Satisfies] at hw₂;
        contradiction;
      · assumption;
  · obtain ⟨x, Rwx, hx⟩ := by simpa [Satisfies] using hw₂;
    use x;
    constructor;
    · left;
      refine ⟨?_, (by assumption)⟩;
      · intro y Rxy hy;
        exact hw₁ _ (hTrans.trans _ _ _ Rwx Rxy) hy;
    · constructor;
      · by_contra hC;
        subst hC;
        simp [Satisfies] at hw₃
        contradiction;
      · assumption;


lemma validate_T_Four_of_validate_Grz (h : F ⊧ Axioms.Grz (.atom 0)) :
    F ⊧ □(.atom 0) ==> ((.atom 0) ⋏ □□(.atom 0)) := by
  let ψ : Formula _ := (.atom 0) ⋏ (□(.atom 0) ==> □□(.atom 0));
  intro V x;
  simp only [Axioms.Grz, ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models,
    ValidOnModel] at h;
  suffices Satisfies { toFrame := F, Val := V } x (□(.atom 0) ==> ψ) by
    intro h₁;
    have h₂ := Satisfies.and_def.mp <| this h₁;
    apply Satisfies.and_def.mpr;
    constructor;
    · exact h₂.1;
    · exact h₂.2 h₁;
  intro h₁;
  have h₂ : Satisfies ⟨F, V⟩ x (□(.atom 0) ==> □(□(ψ ==> □ψ) ==> ψ)) :=
    @Hilbert.K.Kripke.sound.sound (□(.atom 0) ==> □(□(ψ ==> □ψ) ==>
        ψ)) lemmaGrz₁! F (by trivial) V x;
  have h₃ :
      Satisfies ⟨F, V⟩ x (□(□(ψ ==> □ψ) ==> ψ) ==> ψ) := Satisfies.iff_subst_self (s := fun a =>
    if a = 0 then ψ else a) |>.mp <| h _ _;
  exact h₃ <| h₂ <| h₁;

lemma validate_T_of_validate_Grz (h : F ⊧ Axioms.Grz (.atom 0)) : F ⊧ (Axioms.T (.atom 0)) := by
  intro V x hx;
  exact Satisfies.and_def.mp (validate_T_Four_of_validate_Grz h V x hx) |>.1;

lemma reflexive_of_validate_Grz (h : F ⊧ Axioms.Grz (.atom 0)) : Std.Refl F := by
  apply reflexive_of_validate_AxiomT;
  simpa using validate_T_of_validate_Grz h;

lemma validate_Four_of_validate_Grz (h : F ⊧ Axioms.Grz (.atom 0)) :
    F ⊧ (Axioms.Four (.atom 0))  := by
  intro V x hx;
  exact Satisfies.and_def.mp (validate_T_Four_of_validate_Grz h V x hx) |>.2;

lemma transitive_of_validate_Grz (h : F ⊧ Axioms.Grz (.atom 0)) : IsTrans F.World F.Rel := by
  apply transitive_of_validate_AxiomFour;
  simpa using validate_Four_of_validate_Grz h;

lemma WCWF_of_validate_Grz (h : F ⊧ Axioms.Grz (.atom 0)) : WCWF F := by
  have F_trans : IsTrans F.World F.Rel := transitive_of_validate_Grz h;
  have F_refl : Std.Refl F := reflexive_of_validate_Grz h;
  revert h;
  contrapose;
  intro hWCWF;
  replace hWCWF := ConverseWellFounded.iff_has_max.not.mp hWCWF;
  push Not at hWCWF;
  obtain ⟨f, hf⟩ := dependent_choice hWCWF; clear hWCWF;
  simp only [IrreflGen, ne_eq] at hf;
  apply ValidOnFrame.not_of_exists_valuation_world;
  by_cases H : ∀ j₁ j₂, (j₁ < j₂ → f j₂ ≠ f j₁)
  · use (fun v _ => ∀ i, v ≠ f (2 * i)), (f 0);
    apply Classical.not_imp.mpr
    constructor;
    · suffices Satisfies ⟨F, _⟩ (f 0) (□(∼(.atom 0) ==> ∼(□((.atom 0) ==> □(.atom 0))))) by
        intro x hx;
        exact not_imp_not.mp <| this _ hx;
      suffices ∀ y, f 0 ≺ y → ∀ j, y = f (2 * j) → ∃ x, y ≺ x ∧ (∀ i, ¬x =
        f (2 * i)) ∧ ∃ z, x ≺ z ∧ ∃ x, z = f (2 * x) by
        simpa [Satisfies];
      rintro v h0v j rfl;
      use f (2 * j + 1);
      refine ⟨?_, ?_, f ((2 * j) + 2), ?_, ?_⟩;
      · apply hf _ |>.2;
      · intro i;
        rcases (lt_trichotomy i j) with (hij | rfl | hij);
        · apply H;
          omega;
        · apply H;
          omega;
        · apply @H _ _ ?_ |>.symm;
          omega;
      · apply hf _ |>.2;
      · use (j + 1);
        rfl;
    · suffices ∃ x, f 0 = f (2 * x) by simpa [Satisfies];
      use 0;
  · push Not at H;
    obtain ⟨j, k, ljk, ejk⟩ := H;
    let V : Valuation F := (fun v _ => v ≠ f j);
    use V, (f j);
    apply Classical.not_imp.mpr;
    constructor;
    · have : Satisfies ⟨F, V⟩ (f (j + 1)) (∼((.atom 0) ==> □(.atom 0))) := by
        suffices f (j + 1) ≠ f j ∧ f (j + 1) ≺ f j by simp_all [Satisfies, V];
        constructor;
        · exact Ne.symm <| (hf j).1;
        · rw [←ejk];
          have H : ∀ {x y : ℕ}, x < y → F.Rel (f x) (f y) := by
            intro x y hxy;
            induction hxy with
            | refl => exact (hf x).2;
            | step _ ih => exact F_trans.trans _ _ _ ih (hf _).2;
          by_cases h : j + 1 = k;
          · subst_vars
            exact F_refl.refl (f (j + 1));
          · have : j + 1 < k := by omega;
            exact H this;
      intro x hx hbox
      by_cases hxj : x = f j
      · subst x
        exact False.elim (this (hbox (f (j + 1)) (hf j).2))
      · simpa [Satisfies, V] using hxj;
    · simp [Satisfies, V];

instance
    _root_.LO.Modal.Kripke.ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass.definedByAxiomGrz
  : ReflexiveTransitiveWeaklyConverseWellFoundedFrameClass.DefinedByFormula (Axioms.Grz (.atom 0))
    :=
    ⟨by
  intro F;
  constructor;
  · rintro ⟨hRefl, hTrans, hWCWF⟩;
    suffices ValidOnFrame F (Axioms.Grz (.atom 0)) by simpa;
    apply validate_Grz_of_refl_trans_wcwf <;> assumption;
  · rintro h;
    replace h : ValidOnFrame F (Axioms.Grz (.atom 0)) := by simpa using h;
    refine ⟨?_, ?_, ?_⟩;
    · exact reflexive_of_validate_Grz h;
    · exact transitive_of_validate_Grz h;
    · exact WCWF_of_validate_Grz h;
⟩

instance
  ReflexiveTransitiveAntiSymmetricFiniteFrameClass.definedByAxiomGrz
  : ReflexiveTransitiveAntiSymmetricFiniteFrameClass.DefinedByFormula (Axioms.Grz (.atom 0)) := ⟨by
  intro F;
  constructor;
  · rintro ⟨hRefl, hTrans, hAntisymm⟩;
    suffices ValidOnFiniteFrame F (Axioms.Grz (.atom 0)) by simpa;
    apply validate_Grz_of_refl_trans_wcwf;
    · assumption;
    · assumption;
    · apply WCWF_of_finite_trans_antisymm;
      · exact F.world_finite;
      · intro _ _ _
        exact hTrans.trans _ _ _;
      · exact hAntisymm.antisymm;
  · rintro h;
    replace h : ValidOnFiniteFrame F (Axioms.Grz (.atom 0)) := by simpa using h;
    refine ⟨?_, ?_, ?_⟩;
    · exact reflexive_of_validate_Grz h;
    · exact transitive_of_validate_Grz h;
    · exact ⟨antisymm_of_WCWF <| WCWF_of_validate_Grz h⟩;
⟩

end Kripke

end Modal
end LO
