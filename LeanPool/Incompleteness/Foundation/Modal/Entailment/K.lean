/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Entailment.Basic

/-! # K -/


namespace LO
namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.K 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def multiboxAxiomK : 𝓢 ⊢ □^[n](φ ==> ψ) ==> □^[n]φ ==> □^[n]ψ := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq]; apply impId;
  | succ n ih => simpa using impTrans'' (axiomK' <| nec ih) (by apply axiomK);
omit [DecidableEq F] in @[simp] lemma multiboxAxiomK! :
    𝓢 ⊢! □^[n](φ ==> ψ) ==> □^[n]φ ==> □^[n]ψ :=
  ⟨multiboxAxiomK⟩

/-- Imported declaration from the Incompleteness formalization. -/
def multiboxAxiomK' (h : 𝓢 ⊢ □^[n](φ ==> ψ)) : 𝓢 ⊢ □^[n]φ ==> □^[n]ψ := multiboxAxiomK ⨀ h
omit [DecidableEq F] in @[simp] lemma multiboxAxiomK'! (h :
    𝓢 ⊢! □^[n](φ ==> ψ)) : 𝓢 ⊢! □^[n]φ ==> □^[n]ψ :=
  ⟨multiboxAxiomK' h.some⟩

alias multiboxedImplyDistribute := multiboxAxiomK'
alias multiboxed_imply_distribute! := multiboxAxiomK'!


/-- Imported declaration from the Incompleteness formalization. -/
def boxIff' (h : 𝓢 ⊢ φ <=> ψ) : 𝓢 ⊢ (□φ <=> □ψ) := by
  apply iffIntro;
  · exact axiomK' <| nec <| and₁' h;
  · exact axiomK' <| nec <| and₂' h;
omit [DecidableEq F] in @[simp] lemma box_iff! (h : 𝓢 ⊢! φ <=> ψ) : 𝓢 ⊢! □φ <=> □ψ :=
  ⟨boxIff' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def multiboxIff' (h : 𝓢 ⊢ φ <=> ψ) : 𝓢 ⊢ □^[n]φ <=> □^[n]ψ := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using boxIff' ih;
omit [DecidableEq F] in @[simp] lemma multibox_iff! (h : 𝓢 ⊢! φ <=> ψ) : 𝓢 ⊢! □^[n]φ <=> □^[n]ψ :=
  ⟨multiboxIff' h.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def diaDualityMp : 𝓢 ⊢ ◇φ ==> ∼(□(∼φ)) := and₁' diaDuality
omit [DecidableEq F] in @[simp] lemma diaDualityMp! : 𝓢 ⊢! ◇φ ==> ∼(□(∼φ)) := by
  classical
  exact ⟨diaDualityMp⟩

/-- Imported declaration from the Incompleteness formalization. -/
def diaDualityMpr : 𝓢 ⊢ ∼(□(∼φ)) ==> ◇φ := and₂' diaDuality
omit [DecidableEq F] in @[simp] lemma diaDualityMpr! : 𝓢 ⊢! ∼(□(∼φ)) ==> ◇φ := by
  classical
  exact ⟨diaDualityMpr⟩

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.diaDuality'.mp (h : 𝓢 ⊢ ◇φ) : 𝓢 ⊢ ∼(□(∼φ)) := (and₁' diaDuality) ⨀ h
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.diaDuality'.mpr (h : 𝓢 ⊢ ∼(□(∼φ))) : 𝓢 ⊢ ◇φ := (and₂' diaDuality) ⨀ h

omit [DecidableEq F] in
lemma «dia_duality'!» : 𝓢 ⊢! ◇φ ↔ 𝓢 ⊢! ∼(□(∼φ)) := by
  classical
  exact ⟨
  fun h => ⟨diaDuality'.mp h.some⟩,
  fun h => ⟨diaDuality'.mpr h.some⟩
⟩

/-- Imported declaration from the Incompleteness formalization. -/
def multiDiaDuality : 𝓢 ⊢ ◇^[n]φ <=> ∼(□^[n](∼φ)) := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq]; apply dn;
  | succ n ih =>
    simp only [Dia.multidia_succ, Box.multibox_succ];
    apply iffTrans'' <| diaDuality (φ := ◇^[n]φ);
    apply negReplaceIff';
    apply boxIff';
    apply iffIntro;
    · exact contra₂' <| and₂' ih;
    · exact contra₁' <| and₁' ih;
omit [DecidableEq F] in
lemma «multidia_duality!» : 𝓢 ⊢! ◇^[n]φ <=> ∼(□^[n](∼φ)) := by
  classical
  exact ⟨multiDiaDuality⟩

omit [DecidableEq F] in
lemma «multidia_duality'!» : 𝓢 ⊢! ◇^[n]φ ↔ 𝓢 ⊢! ∼(□^[n](∼φ)) := by
  classical
  constructor;
  · intro h; exact (and₁'! multidia_duality!) ⨀ h;
  · intro h; exact (and₂'! multidia_duality!) ⨀ h;

/-- Imported declaration from the Incompleteness formalization. -/
def diaIff' (h : 𝓢 ⊢ φ <=> ψ) : 𝓢 ⊢ (◇φ <=> ◇ψ) := by
  apply iffTrans'' diaDuality;
  apply andComm';
  apply iffTrans'' diaDuality;
  apply negReplaceIff';
  apply boxIff';
  apply negReplaceIff';
  apply andComm';
  assumption;

omit [DecidableEq F] in
@[simp] lemma «dia_iff!» (h : 𝓢 ⊢! φ <=> ψ) : 𝓢 ⊢! ◇φ <=> ◇ψ := by
  classical
  exact ⟨diaIff' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def multidiaIff' (h : 𝓢 ⊢ φ <=> ψ) : 𝓢 ⊢ ◇^[n]φ <=> ◇^[n]ψ := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using diaIff' ih;
omit [DecidableEq F] in
@[simp] lemma «multidia_iff!» (h : 𝓢 ⊢! φ <=> ψ) : 𝓢 ⊢! ◇^[n]φ <=> ◇^[n]ψ := by
  classical
  exact ⟨multidiaIff' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def multiboxDuality : 𝓢 ⊢ □^[n]φ <=> ∼(◇^[n](∼φ)) := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq]; apply dn;
  | succ n ih =>
    simp only [Box.multibox_succ, Dia.multidia_succ];
    apply iffTrans'' (boxIff' ih);
    apply iffNegRightToLeft';
    exact iffComm' <| diaDuality;

omit [DecidableEq F] in
@[simp] lemma «multibox_duality!» : 𝓢 ⊢! □^[n]φ <=> ∼(◇^[n](∼φ)) := by
  classical
  exact ⟨multiboxDuality⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxDuality : 𝓢 ⊢ □φ <=> ∼(◇(∼φ)) := multiboxDuality (n := 1)
omit [DecidableEq F] in
@[simp] lemma «box_duality!» : 𝓢 ⊢! □φ <=> ∼(◇(∼φ)) := by
  classical
  exact ⟨boxDuality⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxDualityMp : 𝓢 ⊢ □φ ==> ∼(◇(∼φ)) := and₁' boxDuality
omit [DecidableEq F] in
@[simp] lemma «boxDualityMp!» : 𝓢 ⊢! □φ ==> ∼(◇(∼φ)) := by
  classical
  exact ⟨boxDualityMp⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxDualityMp' (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ ∼(◇(∼φ)) := boxDualityMp ⨀ h
omit [DecidableEq F] in
lemma «boxDualityMp'!» (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! ∼(◇(∼φ)) := by
  classical
  exact ⟨boxDualityMp' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxDualityMpr : 𝓢 ⊢ ∼(◇(∼φ)) ==> □φ := and₂' boxDuality
omit [DecidableEq F] in
@[simp] lemma «boxDualityMpr!» : 𝓢 ⊢! ∼(◇(∼φ)) ==> □φ := by
  classical
  exact ⟨boxDualityMpr⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxDualityMpr' (h : 𝓢 ⊢ ∼(◇(∼φ))) : 𝓢 ⊢ □φ := boxDualityMpr ⨀ h
omit [DecidableEq F] in
lemma «boxDualityMpr'!» (h : 𝓢 ⊢! ∼(◇(∼φ))) : 𝓢 ⊢! □φ := by
  classical
  exact ⟨boxDualityMpr' h.some⟩

omit [DecidableEq F] in
lemma «multibox_duality'!» : 𝓢 ⊢! □^[n]φ ↔ 𝓢 ⊢! ∼(◇^[n](∼φ)) := by
  classical
  constructor;
  · intro h; exact (and₁'! multibox_duality!) ⨀ h;
  · intro h; exact (and₂'! multibox_duality!) ⨀ h;

omit [DecidableEq F] in
lemma «box_duality'!» : 𝓢 ⊢! □φ ↔ 𝓢 ⊢! ∼(◇(∼φ)) := by
  classical
  exact multibox_duality'! (n := 1)

/-- Imported declaration from the Incompleteness formalization. -/
def boxDni : 𝓢 ⊢ □φ ==> □(∼∼φ) := axiomK' <| nec dni
omit [DecidableEq F] in
@[simp] lemma «boxDni!» : 𝓢 ⊢! □φ ==> □(∼∼φ) := by
  classical
  exact ⟨boxDni⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxDni' (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ □(∼∼φ) := boxDni ⨀ h
omit [DecidableEq F] in
lemma «boxDni'!» (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! □(∼∼φ) := by
  classical
  exact ⟨boxDni' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxDne : 𝓢 ⊢ □(∼∼φ) ==> □φ := axiomK' <| nec dne
omit [DecidableEq F] in @[simp] lemma boxDne! : 𝓢 ⊢! □(∼∼φ) ==> □φ := by
  classical
  exact ⟨boxDne⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxDne' (h : 𝓢 ⊢ □(∼∼φ)) : 𝓢 ⊢ □φ := boxDne ⨀ h
omit [DecidableEq F] in lemma boxDne'! (h : 𝓢 ⊢! □(∼∼φ)) : 𝓢 ⊢! □φ := by
  classical
  exact ⟨boxDne' h.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def multiboxverum : 𝓢 ⊢ (□^[n]⊤ : F) := multinec verum
omit [DecidableEq F] in @[simp] lemma multiboxverum! : 𝓢 ⊢! (□^[n]⊤ : F) := by
  classical
  exact ⟨multiboxverum⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxverum : 𝓢 ⊢ (□⊤ : F) := multiboxverum (n := 1)
omit [DecidableEq F] in @[simp] lemma boxverum! : 𝓢 ⊢! (□⊤ : F) := by
  classical
  exact ⟨boxverum⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxdotverum : 𝓢 ⊢ (⊡⊤ : F) := andIntro verum boxverum
omit [DecidableEq F] in @[simp] lemma boxdotverum! : 𝓢 ⊢! (⊡⊤ : F) := by
  classical
  exact ⟨boxdotverum⟩

/-- Imported declaration from the Incompleteness formalization. -/
def implyMultiboxDistribute' (h : 𝓢 ⊢ φ ==> ψ) :
    𝓢 ⊢ □^[n]φ ==> □^[n]ψ :=
  multiboxAxiomK' <| multinec h
omit [DecidableEq F] in lemma imply_multibox_distribute'! (h :
    𝓢 ⊢! φ ==> ψ) : 𝓢 ⊢! □^[n]φ ==> □^[n]ψ :=
  ⟨implyMultiboxDistribute' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxDistribute' (h : 𝓢 ⊢ φ ==> ψ) : 𝓢 ⊢ □φ ==> □ψ := implyMultiboxDistribute' (n := 1) h
omit [DecidableEq F] in lemma imply_box_distribute'! (h : 𝓢 ⊢! φ ==> ψ) : 𝓢 ⊢! □φ ==> □ψ :=
  ⟨implyBoxDistribute' h.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def distributeMultiboxAnd :
    𝓢 ⊢ □^[n](φ ⋏ ψ) ==> □^[n]φ ⋏ □^[n]ψ :=
  implyRightAnd (implyMultiboxDistribute' and₁) (implyMultiboxDistribute' and₂)
omit [DecidableEq F] in
@[simp] lemma «distributeMultiboxAnd!» :
    𝓢 ⊢! □^[n](φ ⋏ ψ) ==> □^[n]φ ⋏ □^[n]ψ :=
  by
  classical
  exact ⟨distributeMultiboxAnd⟩

/-- Imported declaration from the Incompleteness formalization. -/
def distributeBoxAnd : 𝓢 ⊢ □(φ ⋏ ψ) ==> □φ ⋏ □ψ := distributeMultiboxAnd (n := 1)
omit [DecidableEq F] in
@[simp] lemma «distributeBoxAnd!» : 𝓢 ⊢! □(φ ⋏ ψ) ==> □φ ⋏ □ψ := by
  classical
  exact ⟨distributeBoxAnd⟩

/-- Imported declaration from the Incompleteness formalization. -/
def distributeMultiboxAnd' (h : 𝓢 ⊢ □^[n](φ ⋏ ψ)) :
    𝓢 ⊢ □^[n]φ ⋏ □^[n]ψ :=
  distributeMultiboxAnd ⨀ h
omit [DecidableEq F] in
lemma «distributeMultiboxAnd'!» (d : 𝓢 ⊢! □^[n](φ ⋏ ψ)) :
    𝓢 ⊢! □^[n]φ ⋏ □^[n]ψ :=
  by
  classical
  exact ⟨distributeMultiboxAnd' d.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def distributeBoxAnd' (h : 𝓢 ⊢ □(φ ⋏ ψ)) : 𝓢 ⊢ □φ ⋏ □ψ := distributeMultiboxAnd' (n := 1) h
omit [DecidableEq F] in
lemma «distributeBoxAnd'!» (d : 𝓢 ⊢! □(φ ⋏ ψ)) : 𝓢 ⊢! □φ ⋏ □ψ := by
  classical
  exact ⟨distributeBoxAnd' d.some⟩

omit [DecidableEq F] in
lemma «conj_cons!» : 𝓢 ⊢! (φ ⋏ ⋀Γ) <=> ⋀(φ :: Γ) := by
  classical
  induction Γ using List.induction_with_singleton with
  | hnil =>
    simp only [List.conj₂_nil, List.conj₂_singleton];
    apply iff_intro!;
    · simp;
    · exact imply_right_and! (by simp) (by simp);
  | _ => simp;

@[simp]
lemma «distribute_multibox_conj!» : 𝓢 ⊢! □^[n]⋀Γ ==> ⋀□'^[n]Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ h ih =>
    simp_all only [ne_eq, not_false_eq_true, List.conj₂_cons_nonempty];
    have h₁ : 𝓢 ⊢! □^[n](φ ⋏ ⋀Γ) ==> □^[n]φ := imply_multibox_distribute'! <| and₁!;
    have h₂ : 𝓢 ⊢! □^[n](φ ⋏ ⋀Γ) ==> ⋀□'^[n]Γ :=
      imp_trans''! (imply_multibox_distribute'! <| and₂!) ih;
    have := imply_right_and! h₁ h₂;
    exact imp_trans''! this <| by
      apply imply_conj'!;
      intro ψ hq;
      simp only [Finset.mem_toList, List.toFinset_cons, Finset.image_insert, Finset.mem_insert,
        Finset.mem_image, List.mem_toFinset] at hq;
      rcases hq with (rfl | ⟨ψ, hq, rfl⟩)
      · apply and₁!;
      · suffices 𝓢 ⊢! ⋀□'^[n]Γ ==> □^[n]ψ by exact dhyp_and_left! this;
        apply generate_conj'!;
        simpa;

@[simp] lemma «distribute_box_conj!» : 𝓢 ⊢! □(⋀Γ) ==> ⋀(□'Γ) := distribute_multibox_conj! (n := 1)

/-- Imported declaration from the Incompleteness formalization. -/
def collectMultiboxAnd : 𝓢 ⊢ □^[n]φ ⋏ □^[n]ψ ==> □^[n](φ ⋏ ψ) := by
  have d₁ : 𝓢 ⊢ □^[n]φ ==> □^[n](ψ ==> φ ⋏ ψ) := implyMultiboxDistribute' and₃;
  have d₂ : 𝓢 ⊢ □^[n](ψ ==> φ ⋏ ψ) ==> (□^[n]ψ ==> □^[n](φ ⋏ ψ)) := multiboxAxiomK;
  exact (and₂' (andImplyIffImplyImply _ _ _)) ⨀ (impTrans'' d₁ d₂);
omit [DecidableEq F] in @[simp] lemma collectMultiboxAnd! :
    𝓢 ⊢! □^[n]φ ⋏ □^[n]ψ ==> □^[n](φ ⋏ ψ) :=
  ⟨collectMultiboxAnd⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectBoxAnd : 𝓢 ⊢ □φ ⋏ □ψ ==> □(φ ⋏ ψ) := collectMultiboxAnd (n := 1)
omit [DecidableEq F] in @[simp] lemma collectBoxAnd! : 𝓢 ⊢! □φ ⋏ □ψ ==> □(φ ⋏ ψ) :=
  ⟨collectBoxAnd⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectMultiboxAnd' (h : 𝓢 ⊢ □^[n]φ ⋏ □^[n]ψ) : 𝓢 ⊢ □^[n](φ ⋏ ψ) := collectMultiboxAnd ⨀ h
omit [DecidableEq F] in lemma collectMultiboxAnd'! (h :
    𝓢 ⊢! □^[n]φ ⋏ □^[n]ψ) : 𝓢 ⊢! □^[n](φ ⋏ ψ) :=
  ⟨collectMultiboxAnd' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectBoxAnd' (h : 𝓢 ⊢ □φ ⋏ □ψ) : 𝓢 ⊢ □(φ ⋏ ψ) := collectMultiboxAnd' (n := 1) h
omit [DecidableEq F] in lemma collectBoxAnd'! (h : 𝓢 ⊢! □φ ⋏ □ψ) : 𝓢 ⊢! □(φ ⋏ ψ) :=
  ⟨collectBoxAnd' h.some⟩


omit [DecidableEq F] in
lemma «multiboxConj'_iff!» : 𝓢 ⊢! □^[n]⋀Γ ↔ ∀ φ ∈ Γ, 𝓢 ⊢! □^[n]φ := by
  classical
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ h ih =>
    simp_all only [ne_eq, not_false_eq_true, List.conj₂_cons_nonempty, List.mem_cons,
      forall_eq_or_imp];
    constructor;
    · intro h;
      have := distributeMultiboxAnd'! h;
      constructor;
      · exact and₁'! this;
      · exact ih.mp (and₂'! this);
    · rintro ⟨h₁, h₂⟩;
      exact collectMultiboxAnd'! <| and₃'! h₁ (ih.mpr h₂);
  | _ => simp_all;
omit [DecidableEq F] in
lemma «boxConj'_iff!» : 𝓢 ⊢! □⋀Γ ↔ ∀ φ ∈ Γ, 𝓢 ⊢! □φ := by
  classical
  exact multiboxConj'_iff! (n := 1)

lemma «multiboxconj_of_conjmultibox!» (d : 𝓢 ⊢! ⋀□'^[n]Γ) : 𝓢 ⊢! □^[n]⋀Γ := by
  apply multiboxConj'_iff!.mpr;
  intro φ hp;
  exact iff_provable_list_conj.mp d (□^[n]φ) (by aesop);

@[simp]
lemma «multibox_cons_conjAux₁!» :  𝓢 ⊢! ⋀(□'^[n](φ :: Γ)) ==> ⋀□'^[n]Γ := by
  apply conjconj_subset!;
  simp_all;

@[simp]
lemma «multibox_cons_conjAux₂!» :  𝓢 ⊢! ⋀(□'^[n](φ :: Γ)) ==> □^[n]φ := by
  suffices 𝓢 ⊢! ⋀(□'^[n](φ :: Γ)) ==> ⋀□'^[n]([φ]) by simpa;
  apply conjconj_subset!;
  simp_all;


@[simp]
lemma «multibox_cons_conj!» :  𝓢 ⊢! ⋀(□'^[n](φ :: Γ)) ==> ⋀□'^[n]Γ ⋏ □^[n]φ :=
  imply_right_and! multibox_cons_conjAux₁! multibox_cons_conjAux₂!

@[simp]
lemma «collect_multibox_conj!» : 𝓢 ⊢! ⋀□'^[n]Γ ==> □^[n]⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simpa using imply₁'! multiboxverum!;
  | hsingle => simp;
  | hcons φ Γ h ih =>
    simp_all only [ne_eq, not_false_eq_true, List.conj₂_cons_nonempty];
    exact imp_trans''!
      (imply_right_and! (generalConj'! (by simp)) (imp_trans''! (by simp) ih))
      collectMultiboxAnd!;

@[simp]
lemma «collect_box_conj!» : 𝓢 ⊢! ⋀(□'Γ) ==> □(⋀Γ) := collect_multibox_conj! (n := 1)


/-- Imported declaration from the Incompleteness formalization. -/
def collectMultiboxOr :
    𝓢 ⊢ □^[n]φ ⋎ □^[n]ψ ==> □^[n](φ ⋎ ψ) :=
  or₃'' (multiboxAxiomK' <| multinec or₁) (multiboxAxiomK' <| multinec or₂)
omit [DecidableEq F] in @[simp] lemma collectMultiboxOr! :
    𝓢 ⊢! □^[n]φ ⋎ □^[n]ψ ==> □^[n](φ ⋎ ψ) :=
  ⟨collectMultiboxOr⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectBoxOr : 𝓢 ⊢ □φ ⋎ □ψ ==> □(φ ⋎ ψ) := collectMultiboxOr (n := 1)
omit [DecidableEq F] in @[simp] lemma collectBoxOr! : 𝓢 ⊢! □φ ⋎ □ψ ==> □(φ ⋎ ψ) :=
  ⟨collectBoxOr⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectMultiboxOr' (h : 𝓢 ⊢ □^[n]φ ⋎ □^[n]ψ) : 𝓢 ⊢ □^[n](φ ⋎ ψ) := collectMultiboxOr ⨀ h
omit [DecidableEq F] in lemma collectMultiboxOr'! (h :
    𝓢 ⊢! □^[n]φ ⋎ □^[n]ψ) : 𝓢 ⊢! □^[n](φ ⋎ ψ) :=
  ⟨collectMultiboxOr' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectBoxOr' (h : 𝓢 ⊢ □φ ⋎ □ψ) : 𝓢 ⊢ □(φ ⋎ ψ) := collectMultiboxOr' (n := 1) h
omit [DecidableEq F] in lemma collectBoxOr'! (h : 𝓢 ⊢! □φ ⋎ □ψ) : 𝓢 ⊢! □(φ ⋎ ψ) :=
  ⟨collectBoxOr' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def diaOrInst₁ : 𝓢 ⊢ ◇φ ==> ◇(φ ⋎ ψ) := by
  apply impTrans'' (and₁' diaDuality);
  apply impTrans'' ?h (and₂' diaDuality);
  apply contra₀';
  apply axiomK';
  apply nec;
  apply contra₀';
  exact or₁;
omit [DecidableEq F] in
@[simp] lemma «dia_or_inst₁!» : 𝓢 ⊢! ◇φ ==> ◇(φ ⋎ ψ) := by
  classical
  exact ⟨diaOrInst₁⟩

/-- Imported declaration from the Incompleteness formalization. -/
def diaOrInst₂ : 𝓢 ⊢ ◇ψ ==> ◇(φ ⋎ ψ) := by
  apply impTrans'' (and₁' diaDuality);
  apply impTrans'' ?h (and₂' diaDuality);
  apply contra₀';
  apply axiomK';
  apply nec;
  apply contra₀';
  exact or₂;
omit [DecidableEq F] in
@[simp] lemma «dia_or_inst₂!» : 𝓢 ⊢! ◇ψ ==> ◇(φ ⋎ ψ) := by
  classical
  exact ⟨diaOrInst₂⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectDiaOr : 𝓢 ⊢ ◇φ ⋎ ◇ψ ==> ◇(φ ⋎ ψ) := or₃'' diaOrInst₁ diaOrInst₂
omit [DecidableEq F] in
@[simp] lemma «collectDiaOr!» : 𝓢 ⊢! ◇φ ⋎ ◇ψ ==> ◇(φ ⋎ ψ) := by
  classical
  exact ⟨collectDiaOr⟩

/-- Imported declaration from the Incompleteness formalization. -/
def collectDiaOr' (h : 𝓢 ⊢ ◇φ ⋎ ◇ψ) : 𝓢 ⊢ ◇(φ ⋎ ψ) := collectDiaOr ⨀ h
omit [DecidableEq F] in
@[simp] lemma «collectDiaOr'!» (h : 𝓢 ⊢! ◇φ ⋎ ◇ψ) : 𝓢 ⊢! ◇(φ ⋎ ψ) := by
  classical
  exact ⟨collectDiaOr' h.some⟩

-- TODO: `distributeMultidiaAnd!` is computable but it's too slow, so leave it.
omit [DecidableEq F] in
@[simp] lemma «distribute_multidia_and!»: 𝓢 ⊢! ◇^[n](φ ⋏ ψ) ==> ◇^[n]φ ⋏ ◇^[n]ψ := by
  classical
  suffices h : 𝓢 ⊢! ∼(□^[n](∼(φ ⋏ ψ))) ==> ∼(□^[n](∼φ)) ⋏ ∼(□^[n](∼ψ)) by
    exact imp_trans''! (imp_trans''! (and₁'! multidia_duality!) h) <|
        and_replace! (and₂'! multidia_duality!) (and₂'! multidia_duality!);
  apply FiniteContext.deduct'!;
  apply demorgan₃'!;
  apply FiniteContext.deductInv'!;
  apply contra₀'!;
  apply imp_trans''! collectMultiboxOr! (imply_multibox_distribute'! demorgan₁!)

omit [DecidableEq F] in
@[simp] lemma «distribute_dia_and!» : 𝓢 ⊢! ◇(φ ⋏ ψ) ==> ◇φ ⋏ ◇ψ := by
  classical
  exact distribute_multidia_and! (n := 1)

-- TODO: `iffConjMultidiaMultidiaconj` is computable but it's too slow, so leave it.
@[simp] lemma «iff_conjmultidia_multidiaconj!» : 𝓢 ⊢! ◇^[n](⋀Γ) ==> ⋀(◇'^[n]Γ) := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ h ih =>
    simp_all only [ne_eq, not_false_eq_true, List.conj₂_cons_nonempty];
    exact imp_trans''! distribute_multidia_and! <| by
      apply deduct'!;
      apply iff_provable_list_conj.mpr;
      intro ψ hq;
      simp only [Finset.mem_toList, List.toFinset_cons, Finset.image_insert, Finset.mem_insert,
        Finset.mem_image, List.mem_toFinset] at hq;
      cases hq with
      | inl => subst_vars; exact and₁'! id!;
      | inr hq =>
        obtain ⟨χ, hr₁, hr₂⟩ := hq;
        exact (iff_provable_list_conj.mp <| (of'! ih) ⨀ (and₂'! <| id!)) ψ (by aesop);
  | _ => simp

-- def distributeDiaAnd' (h : 𝓢 ⊢ ◇(φ ⋏ ψ)) : 𝓢 ⊢ ◇φ ⋏ ◇ψ := distributeDiaAnd ⨀ h
omit [DecidableEq F] in
lemma «distribute_dia_and'!» (h : 𝓢 ⊢! ◇(φ ⋏ ψ)) : 𝓢 ⊢! ◇φ ⋏ ◇ψ := by
  classical
  exact distribute_dia_and! ⨀ h

/-- Imported declaration from the Incompleteness formalization. -/
def boxdotAxiomK : 𝓢 ⊢ ⊡(φ ==> ψ) ==> (⊡φ ==> ⊡ψ) := by
  apply deduct';
  apply deduct;
  have d : [φ ⋏ □φ, (φ ==> ψ) ⋏ □(φ ==> ψ)] ⊢[𝓢] (φ ==> ψ) ⋏ □(φ ==> ψ) := FiniteContext.byAxm;
  exact and₃' ((and₁' d) ⨀ (and₁' (ψ := □φ) (FiniteContext.byAxm))) <|
    (axiomK' <| and₂' d) ⨀ (and₂' (φ := φ) (FiniteContext.byAxm));
omit [DecidableEq F] in
@[simp 1100] lemma «boxdot_axiomK!» : 𝓢 ⊢! ⊡(φ ==> ψ) ==> (⊡φ ==> ⊡ψ) := by
  classical
  exact ⟨boxdotAxiomK⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxdotAxiomT : 𝓢 ⊢ ⊡φ ==> φ := by exact and₁;
omit [DecidableEq F] in @[simp 1100] lemma boxdot_axiomT! : 𝓢 ⊢! ⊡φ ==> φ := by
  classical
  exact ⟨boxdotAxiomT⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxdotNec (d : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊡φ := and₃' d (nec d)
omit [DecidableEq F] in lemma boxdot_nec! (d : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊡φ := by
  classical
  exact ⟨boxdotNec d.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxdotBox : 𝓢 ⊢ ⊡φ ==> □φ := by exact and₂;
omit [DecidableEq F] in lemma boxdot_box! : 𝓢 ⊢! ⊡φ ==> □φ := by
  classical
  exact ⟨boxdotBox⟩

/-- Imported declaration from the Incompleteness formalization. -/
def BoxBoxdotBoxDotbox : 𝓢 ⊢ □⊡φ ==> ⊡□φ := impTrans'' distributeBoxAnd (impId _)
omit [DecidableEq F] in
lemma boxboxdot_boxdotbox : 𝓢 ⊢! □⊡φ ==> ⊡□φ := by
  classical
  exact ⟨BoxBoxdotBoxDotbox⟩


/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def lemmaGrz₁ :
    𝓢 ⊢ □φ ==> □(□((φ ⋏ (□φ ==> □□φ)) ==> □(φ ⋏ (□φ ==> □□φ))) ==> (φ ⋏ (□φ ==> □□φ))) := by
  let ψ := φ ⋏ (□φ ==> □□φ);
  have    : 𝓢 ⊢ ((□φ ==> □□φ) ==> □φ) ==> □φ := peirce
  have    : 𝓢 ⊢ (φ ==> ((□φ ==> □□φ) ==> □φ)) ==> (φ ==> □φ) := dhypImp' this;
  have d₁ : 𝓢 ⊢ (ψ ==> □φ) ==> φ ==> □φ :=
    impTrans'' (and₁' <| andImplyIffImplyImply φ (□φ ==> □□φ) (□φ)) this;
  have    : 𝓢 ⊢ ψ ==> φ := and₁;
  have    : 𝓢 ⊢ □ψ ==> □φ := implyBoxDistribute' this;
  have d₂ : 𝓢 ⊢ (ψ ==> □ψ) ==> (ψ ==> □φ) := dhypImp' this;
  have    : 𝓢 ⊢ (ψ ==> □ψ) ==> φ ==> □φ := impTrans'' d₂ d₁;
  have    : 𝓢 ⊢ □(ψ ==> □ψ) ==> □(φ ==> □φ) := implyBoxDistribute' this;
  have    : 𝓢 ⊢ □(ψ ==> □ψ) ==> (□φ ==> □□φ) := impTrans'' this axiomK;
  have    : 𝓢 ⊢ (φ ==> □(ψ ==> □ψ)) ==> (φ ==> (□φ ==> □□φ)) := dhypImp' this;
  have    : 𝓢 ⊢ φ ==> (□(ψ ==> □ψ) ==> (φ ⋏ (□φ ==> □□φ))) := by
    apply deduct';
    apply deduct;
    apply and₃';
    · exact FiniteContext.byAxm;
    · exact (of this) ⨀ (imply₁' FiniteContext.byAxm) ⨀ (FiniteContext.byAxm);
  have    : 𝓢 ⊢ φ ==> (□(ψ ==> □ψ) ==> ψ) := this;
  exact implyBoxDistribute' this;

omit [DecidableEq F] in
lemma «lemmaGrz₁!» :
    𝓢 ⊢! (□φ ==> □(□((φ ⋏ (□φ ==> □□φ)) ==> □(φ ⋏ (□φ ==> □□φ))) ==> (φ ⋏ (□φ ==> □□φ)))) :=
  by
  classical
  exact ⟨lemmaGrz₁⟩


lemma «contextual_nec!» (h : Γ ⊢[𝓢]! φ) : (□'Γ) ⊢[𝓢]! □φ :=
  provable_iff.mpr <| imp_trans''! collect_box_conj! <| imply_box_distribute'! <| provable_iff.mp h


namespace Context

variable {X : Set F}

lemma provable_iff_boxed : (□''X) *⊢[𝓢]! φ ↔ ∃ Δ :
    List F, (∀ ψ ∈ □'Δ, ψ ∈ □''X) ∧ (□'Δ) ⊢[𝓢]! φ := by
  constructor;
  · intro h;
    obtain ⟨Γ,sΓ, hΓ⟩ := Context.provable_iff.mp h;
    use □'⁻¹Γ;
    constructor;
    · rintro ψ hq;
      apply sΓ ψ;
      simp only [List.eq_prebox_premultibox_one, List.eq_box_multibox_one, Finset.mem_toList,
        Finset.toList_toFinset, Finset.mem_image, Finset.mem_preimage, Function.iterate_one,
        List.mem_toFinset] at hq;
      obtain ⟨χ, _, rfl⟩ := hq;
      assumption;
    · apply FiniteContext.provable_iff.mpr;
      apply imp_trans''! ?_ (FiniteContext.provable_iff.mp hΓ);
      apply conjconj_subset!;
      intro ψ hq;
      have := sΓ ψ hq;
      obtain ⟨χ, _, rfl⟩ := this;
      simp_all;
  · rintro ⟨Δ, hΔ, h⟩;
    apply Context.provable_iff.mpr;
    use □'Δ;

end Context

end Entailment
end LO
