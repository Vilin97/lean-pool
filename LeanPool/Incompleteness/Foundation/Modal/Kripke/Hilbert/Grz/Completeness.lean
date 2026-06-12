/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Grz.Soundness

/-! # Completeness -/


namespace LO
namespace Modal

namespace Formula

variable {α : Type u} [DecidableEq α]
variable {φ ψ : Formula ℕ}

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable abbrev subformulasGrz (φ :
    Formula α) :=
  φ.subformulas ∪ (φ.subformulas.prebox.image (fun ψ => □(ψ ==> □ψ)))

namespace subformulasGrz

@[simp 1100]
lemma mem_self : φ ∈ φ.subformulasGrz := by simp [subformulasGrz, subformulas.mem_self]

lemma mem_boximpbox (h : ψ ∈ φ.subformulas.prebox) :
    □(ψ ==> □ψ) ∈ φ.subformulasGrz := by
  simp_all [subformulasGrz];

lemma mem_origin (h : ψ ∈ φ.subformulas) : ψ ∈ φ.subformulasGrz := by simp_all [subformulasGrz];

lemma mem_imp (h : (ψ ==> χ) ∈ φ.subformulasGrz) : ψ ∈ φ.subformulasGrz ∧ χ ∈ φ.subformulasGrz := by
  simp_all [subformulasGrz];
  aesop;

lemma mem_imp₁ (h : (ψ ==> χ) ∈ φ.subformulasGrz) : ψ ∈ φ.subformulasGrz := mem_imp h |>.1

lemma mem_imp₂ (h : (ψ ==> χ) ∈ φ.subformulasGrz) : χ ∈ φ.subformulasGrz := mem_imp h |>.2

macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply mem_origin <| by assumption
    | apply mem_imp₁ <| by assumption
    | apply mem_imp₂ <| by assumption
  )

lemma mem_left (h : ψ ∈ φ.subformulas) : ψ ∈ φ.subformulasGrz := by
  unfold subformulasGrz;
  simp only [Finset.mem_union];
  left;
  tauto;



end subformulasGrz

end Formula



namespace Hilbert
namespace Grz
namespace Kripke

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open ComplementClosedConsistentFinset

variable {φ ψ : Formula ℕ}

/-- Imported declaration from the Incompleteness formalization. -/
abbrev miniCanonicalFrame (φ : Formula ℕ) : Kripke.FiniteFrame where
  World := ComplementClosedConsistentFinset (Hilbert.Grz) (φ.subformulasGrz)
  Rel X Y :=
    (∀ ψ ∈ □''⁻¹(φ.subformulasGrz), □ψ ∈ X → □ψ ∈ Y) ∧
    ((∀ ψ ∈ □''⁻¹(φ.subformulasGrz), □ψ ∈ Y → □ψ ∈ X) → X = Y)

namespace miniCanonicalFrame

lemma reflexive : Std.Refl (miniCanonicalFrame φ).Rel := by
  exact ⟨fun _ => by simp ⟩

lemma transitive : IsTrans (miniCanonicalFrame φ).World (miniCanonicalFrame φ).Rel := by
  constructor
  rintro X Y Z ⟨RXY₁, RXY₂⟩ ⟨RYZ₁, RYZ₂⟩;
  constructor;
  · rintro ψ hq₁ hq₂;
    exact RYZ₁ ψ hq₁ <| RXY₁ ψ hq₁ hq₂;
  · intro h;
    have eXY : X = Y := RXY₂ <| by
      intro ψ hs hq;
      exact h ψ hs <| RYZ₁ ψ hs hq;
    have eYZ : Y = Z := RYZ₂ <| by
      intro ψ hs hq;
      exact RXY₁ ψ hs <| h ψ hs hq;
    subst_vars;
    tauto;

lemma antisymm : Std.Antisymm (miniCanonicalFrame φ).Rel := by
  constructor
  rintro X Y ⟨_, h₁⟩ ⟨h₂, _⟩;
  exact h₁ h₂;

end miniCanonicalFrame


/-- Imported declaration from the Incompleteness formalization. -/
abbrev miniCanonicalModel (φ : Formula ℕ) : Kripke.Model where
  toFrame := miniCanonicalFrame φ |>.toFrame
  Val X a := (atom a) ∈ X


lemma truthlemma_lemma1
  {X : ComplementClosedConsistentFinset (Hilbert.Grz) (φ.subformulasGrz)} (hq : □ψ ∈ φ.subformulas)
  : ((X.1.prebox.modalBox) ∪ {□(ψ ==> □ψ), -ψ}) ⊆ (φ.subformulasGrz)⁻ := by
  simp only [FormulaFinset.complementary];
  intro χ hr;
  replace hr : χ = □(ψ ==> □ψ) ∨ χ = -ψ ∨ (∃ a, □a ∈ X ∧ □a = χ) := by
    simp at hr; tauto;
  apply Finset.mem_union.mpr;
  rcases hr with (rfl | rfl | ⟨χ, hr, rfl⟩);
  · left;
    simp;
    tauto;
  · right;
    simp only [Finset.mem_image, Finset.mem_union, Finset.eq_prebox_premultibox_one,
      Finset.mem_preimage, Function.iterate_one];
    use ψ;
    constructor;
    · left;
      exact subformulas.mem_box hq;
    · rfl;
  · have := X.closed.subset hr;
    left;
    exact FormulaFinset.complementary_mem_box subformulasGrz.mem_imp₁ this;

lemma truthlemma_lemma2
  {X : ComplementClosedConsistentFinset (Hilbert.Grz) (φ.subformulasGrz)} (hq₁ : □ψ ∈
    φ.subformulas) (hq₂ : □ψ ∉ X)
  : FormulaFinset.Consistent (Hilbert.Grz) ((X.1.prebox.modalBox) ∪ {□(ψ ==> □ψ), -ψ}) := by
    apply FormulaFinset.intro_union_consistent;
    rintro Γ₁ Γ₂ ⟨hΓ₁, hΓ₂⟩;
    replace hΓ₂ : ∀ χ ∈ Γ₂, χ = □(ψ ==> □ψ) ∨ χ = -ψ := by
      intro χ hr;
      simpa using hΓ₂ χ hr;
    by_contra hC;
    have : Γ₁ ⊢[(Hilbert.Grz)]! ⋀Γ₂ ==> ⊥ := and_imply_iff_imply_imply'!.mp hC;
    have : Γ₁ ⊢[(Hilbert.Grz)]! (□(ψ ==> □ψ) ⋏ -ψ) ==> ⊥ := imp_trans''! (by
      suffices Γ₁ ⊢[(Hilbert.Grz)]! ⋀[□(ψ ==> □ψ), -ψ] ==> ⋀Γ₂ by
        simpa only [ne_eq, List.cons_ne_self, not_false_eq_true, List.conj₂_cons_nonempty,
          List.conj₂_singleton];
      apply conjconj_subset!;
      simpa using hΓ₂;
    ) this;
    have : Γ₁ ⊢[(Hilbert.Grz)]! □(ψ ==> □ψ) ==> -ψ ==> ⊥ := and_imply_iff_imply_imply'!.mp this;
    have : Γ₁ ⊢[(Hilbert.Grz)]! □(ψ ==> □ψ) ==> ψ := by
      rcases Formula.complement.or (φ := ψ) with (hp | ⟨ψ, rfl⟩);
      · rw [hp] at this;
        exact imp_trans''! this dne!;
      · exact this;
    have : (□'Γ₁) ⊢[(Hilbert.Grz)]! □(□(ψ ==> □ψ) ==> ψ) := contextual_nec! this;
    have : (□'Γ₁) ⊢[(Hilbert.Grz)]! ψ := axiomGrz! ⨀ this;
    have : (Hilbert.Grz) ⊢! ⋀□'□'Γ₁ ==> □ψ := contextual_nec! this;
    have : (Hilbert.Grz) ⊢! □□⋀Γ₁ ==> □ψ :=
      imp_trans''! (imp_trans''! (distribute_multibox_conj! (n := 2)) <|
          conjconj_subset! (by simp)) this;
    have : (Hilbert.Grz) ⊢! □⋀Γ₁ ==> □ψ := imp_trans''! axiomFour! this;
    have : (Hilbert.Grz) ⊢! ⋀□'Γ₁ ==> □ψ := imp_trans''! collect_box_conj! this;
    have : (Hilbert.Grz) ⊢! ⋀□'(X.1.prebox.modalBox |>.toList) ==> □ψ :=
      imp_trans''! (conjconj_subset! (by
      simp only [List.eq_box_multibox_one, Finset.mem_toList, Finset.mem_image,
        List.mem_toFinset, Function.iterate_one, Finset.eq_prebox_premultibox_one,
        Finset.eq_box_multibox_one, Finset.toList_toFinset, Finset.mem_preimage,
        exists_exists_and_eq_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        Box.box_injective'];
      intro χ hr;
      have := hΓ₁ _ hr;
      simp at this;
      tauto;
    )) this;
    have : (Hilbert.Grz) ⊢! ⋀□'(X.1.prebox.toList) ==> □ψ := imp_trans''! (conjconj_provable! (by
      intro ψ hq;
      simp only [Finset.eq_prebox_premultibox_one, Finset.eq_box_multibox_one,
        List.eq_box_multibox_one, Finset.mem_toList, Finset.toList_toFinset,
        Finset.mem_image, Finset.mem_preimage, Function.iterate_one,
        exists_exists_and_eq_and] at hq;
      obtain ⟨χ, hr, rfl⟩ := hq;
      apply axiomFour'!;
      apply FiniteContext.by_axm!;
      simpa;
    )) this;
    have : X *⊢[(Hilbert.Grz)]! □ψ := by
      apply Context.provable_iff.mpr;
      use □'X.1.prebox.toList;
      constructor;
      · simp;
      · assumption;
    have : □ψ ∈ X := membership_iff (by trivial) |>.mpr this;
    contradiction;

-- TODO: syntactical proof
lemma truthlemma_lemma3 : (Hilbert.Grz) ⊢! (φ ⋏ □(φ ==> □φ)) ==> □φ := by
  apply KT_weakerThan_Grz.pbl;
  by_contra hC;
  have := (not_imp_not.mpr <| Hilbert.KT.Kripke.complete |>.complete) hC;
  simp only [ValidOnFrameClass.models_iff] at this;
  obtain ⟨F, F_refl, hF⟩ := ValidOnFrameClass.exists_frame_of_not this;
  simp only [Semantics.Realize, ValidOnFrame, ValidOnModel, Satisfies,
    LogicalConnective.Prop.arrow_eq, imp_false, not_forall, not_exists, not_not] at hF;
  obtain ⟨V, x, ⟨⟨h₁, h₂⟩, ⟨y, ⟨Rxy, h₃⟩⟩⟩⟩ := hF;
  have := h₂ x (F_refl.refl x);
  have := (this h₁) _ Rxy;
  contradiction;

lemma truthlemma {X : (miniCanonicalModel φ).World} (q_sub : ψ ∈ φ.subformulas) :
  Satisfies (miniCanonicalModel φ) X ψ ↔ ψ ∈ X := by
  induction ψ using Formula.rec' generalizing X with
  | hatom => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp ψ χ ihq ihr =>
    have := subformulas.mem_imp₁ q_sub;
    have := subformulas.mem_imp₂ q_sub;
    constructor;
    · contrapose;
      intro h;
      apply Satisfies.not_imp.mpr;
      apply Satisfies.and_def.mpr;
      constructor;
      · apply ihq (subformulas.mem_imp₁ q_sub) |>.mpr;
        exact iff_not_mem_imp
          (hsub_qr := subformulasGrz.mem_origin q_sub)
          (hsub_q := subformulasGrz.mem_left (by assumption))
          (hsub_r := subformulasGrz.mem_left (by assumption))
          |>.mp h |>.1;
      · apply ihr (subformulas.mem_imp₂ q_sub) |>.not.mpr;
        have := iff_not_mem_imp
          (hsub_qr := subformulasGrz.mem_origin q_sub)
          (hsub_q := subformulasGrz.mem_left (by assumption))
          (hsub_r := subformulasGrz.mem_left (by assumption))
          |>.mp h |>.2;
        exact iff_mem_compl (subformulasGrz.mem_left (by assumption)) |>.not.mpr
          (by simpa using this);
    · contrapose;
      intro h;
      replace h := Satisfies.and_def.mp <| Satisfies.not_imp.mp h;
      obtain ⟨hq, hr⟩ := h;
      replace hq := ihq (by assumption) |>.mp hq;
      replace hr := ihr (by assumption) |>.not.mp hr;
      apply iff_not_mem_imp
        (hsub_qr := subformulasGrz.mem_origin q_sub)
        (hsub_q := subformulasGrz.mem_left (by assumption))
        (hsub_r := subformulasGrz.mem_left (by assumption))
        |>.mpr;
      constructor;
      · assumption;
      · simpa using iff_mem_compl (subformulasGrz.mem_left (by assumption)) |>.not.mp
          (by assumption);
  | hbox ψ ih =>
    have := subformulas.mem_box q_sub;
    constructor;
    · contrapose;
      by_cases w : ψ ∈ X;
      · intro h;
        obtain ⟨Y, hY⟩ :=
          lindenbaum (𝓢 := Hilbert.Grz) (Ψ := φ.subformulasGrz)
            (truthlemma_lemma1 q_sub) (truthlemma_lemma2 q_sub h);
        simp only [Finset.union_subset_iff] at hY;
        simp only [Satisfies]; push Not;
        use Y;
        constructor;
        · constructor;
          · intro χ _ hr₂;
            apply hY.1;
            simpa;
          · apply imp_iff_not_or (b := X = Y) |>.mpr;
            left; push Not;
            use (ψ ==> □ψ);
            refine ⟨?_, ?_, ?_⟩;
            · simp_all;
            · apply hY.2; simp;
            · by_contra hC;
              have : ↑X *⊢[Hilbert.Grz]! ψ :=
                membership_iff (subformulasGrz.mem_left (by assumption)) |>.mp w;
              have : ↑X *⊢[(Hilbert.Grz)]! □(ψ ==> □ψ) :=
                membership_iff
                  (subformulasGrz.mem_boximpbox (by
                    simpa only [Finset.eq_prebox_premultibox_one, Finset.mem_preimage,
                      Function.iterate_one] using q_sub)) |>.mp hC;
              have : ↑X *⊢[(Hilbert.Grz)]! (ψ ⋏ □(ψ ==> □ψ)) ==> □ψ :=
                Context.of! <| truthlemma_lemma3;
              have : ↑X *⊢[(Hilbert.Grz)]! □ψ := this ⨀ and₃'! (by assumption) (by assumption);
              have : □ψ ∈ X :=
                membership_iff (subformulasGrz.mem_origin (by assumption)) |>.mpr this;
              contradiction;
        · apply ih (by aesop) |>.not.mpr;
          apply iff_mem_compl (subformulasGrz.mem_origin (by aesop)) |>.not.mpr;
          push Not;
          apply hY.2;
          simp;
      · intro _;
        simp only [Satisfies]; push Not;
        use X;
        constructor;
        · exact miniCanonicalFrame.reflexive.refl X;
        · exact ih (by aesop) |>.not.mpr w;
    · intro h Y RXY;
      apply ih (subformulas.mem_box q_sub) |>.mpr;
      have : ↑Y *⊢[(Hilbert.Grz)]! □ψ ==> ψ := Context.of! <| axiomT!;
      have : ↑Y *⊢[(Hilbert.Grz)]! ψ := this ⨀
        (membership_iff (by apply subformulasGrz.mem_left; assumption) |>.mp
          (RXY.1 ψ (by apply subformulasGrz.mem_left; tauto) h));
      exact membership_iff
        (by apply subformulasGrz.mem_left; exact subformulas.mem_box q_sub) |>.mpr this;

instance complete :
    Complete (Hilbert.Grz) (Kripke.ReflexiveTransitiveAntiSymmetricFiniteFrameClass) :=
  ⟨by
  intro φ;
  contrapose;
  intro h;
  apply ValidOnFiniteFrameClass.not_of_exists_frame;
  use (miniCanonicalFrame φ);
  constructor;
  · refine ⟨miniCanonicalFrame.reflexive, miniCanonicalFrame.transitive,
    miniCanonicalFrame.antisymm⟩;
  · apply ValidOnFiniteFrame.not_of_exists_valuation_world;
    obtain ⟨X, hX₁⟩ := lindenbaum (𝓢 := Hilbert.Grz) (Φ := {-φ}) (Ψ := φ.subformulasGrz)
      (by
        simp only [Finset.singleton_subset_iff];
        apply FormulaFinset.complementary_comp;
        exact subformulasGrz.mem_self
      )
      (FormulaFinset.unprovable_iff_singleton_compl_consistent.mpr h);
    use (miniCanonicalModel φ).Val, X;
    apply truthlemma (by simp) |>.not.mpr;
    exact iff_mem_compl (by simp) |>.not.mpr <| by
      push Not;
      apply hX₁;
      tauto;
⟩

end Kripke
end Grz
end Hilbert

end Modal
end LO
