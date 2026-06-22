/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Logic.Entailment
import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Context

/-! # Supplemental -/


namespace LO
namespace Entailment

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Minimal 𝓢]
         {φ ψ χ : F}
         {Γ Δ : List F}

open NegationEquiv
open FiniteContext
open List

/-- Imported declaration from the Incompleteness formalization. -/
def mdpIn : 𝓢 ⊢ φ ⋏ (φ ==> ψ) ==> ψ := by
  apply deduct';
  have hp  : [φ, φ ==> ψ] ⊢[𝓢] φ := FiniteContext.byAxm;
  have hpq : [φ, φ ==> ψ] ⊢[𝓢] φ ==> ψ := FiniteContext.byAxm;
  exact hpq ⨀ hp;
omit [DecidableEq F] in
lemma «mdpIn!» : 𝓢 ⊢! φ ⋏ (φ ==> ψ) ==> ψ := by
  classical
  exact ⟨mdpIn⟩

/-- Imported declaration from the Incompleteness formalization. -/
def botOfMemEither (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢] ⊥ := by
  have hp : Γ ⊢[𝓢] φ := FiniteContext.byAxm h₁;
  have hnp : Γ ⊢[𝓢] φ ==> ⊥ := negEquiv'.mp <| FiniteContext.byAxm h₂;
  exact hnp ⨀ hp

omit [DecidableEq F] in
lemma «botOfMemEither!» (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢]! ⊥ := by
  classical
  exact ⟨botOfMemEither h₁ h₂⟩


/-- Imported declaration from the Incompleteness formalization. -/
def efqOfMemEither [HasAxiomEFQ 𝓢] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) :
    Γ ⊢[𝓢] ψ :=
  efq' <| botOfMemEither h₁ h₂
omit [DecidableEq F] in
lemma «efqOfMemEither!» [HasAxiomEFQ 𝓢] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) :
    Γ ⊢[𝓢]! ψ := by
  classical
  exact ⟨efqOfMemEither h₁ h₂⟩

/-- Imported declaration from the Incompleteness formalization. -/
def efqImplyNot₁ [HasAxiomEFQ 𝓢] : 𝓢 ⊢ ∼φ ==> φ ==> ψ :=
  deduct' <| deduct <| efqOfMemEither (φ := φ) (by simp) (by simp)
omit [DecidableEq F] in
@[simp] lemma «efqImplyNot₁!» [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ∼φ ==> φ ==> ψ := by
  classical
  exact ⟨efqImplyNot₁⟩

/-- Imported declaration from the Incompleteness formalization. -/
def efqImplyNot₂ [HasAxiomEFQ 𝓢] : 𝓢 ⊢ φ ==> ∼φ ==> ψ :=
  deduct' <| deduct <| efqOfMemEither (φ := φ) (by simp) (by simp)
omit [DecidableEq F] in
@[simp] lemma «efqImplyNot₂!» [HasAxiomEFQ 𝓢] : 𝓢 ⊢! φ ==> ∼φ ==> ψ := by
  classical
  exact ⟨efqImplyNot₂⟩

omit [DecidableEq F] in
lemma «efq_of_neg!» [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! ∼φ) : 𝓢 ⊢! φ ==> ψ := by
  classical
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have dnp : [φ] ⊢[𝓢]! φ ==> ⊥ := of'! <| negEquiv'!.mp h;
  exact efq'! (dnp ⨀ FiniteContext.id!);

omit [DecidableEq F] in
lemma «efq_of_neg₂!» [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ∼φ ==> ψ := by
  classical
  exact efqImplyNot₂! ⨀ h

/-- Imported declaration from the Incompleteness formalization. -/
def negMdp (hnp : 𝓢 ⊢ ∼φ) (hn : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊥ := (negEquiv'.mp hnp) ⨀ hn
-- infixl:90 "⨀" => negMdp

omit [DecidableEq F] in
lemma negMdp! (hnp : 𝓢 ⊢! ∼φ) (hn : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊥ := by
  classical
  exact ⟨negMdp hnp.some hn.some⟩
-- infixl:90 "⨀" => negMdp!

/-- Imported declaration from the Incompleteness formalization. -/
def dneOr [HasAxiomDNE 𝓢] (d : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ) :
    𝓢 ⊢ φ ⋎ ψ :=
  or₃''' (impTrans'' dne or₁) (impTrans'' dne or₂) d
omit [DecidableEq F] in
lemma «dne_or!» [HasAxiomDNE 𝓢] (d : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢! φ ⋎ ψ := by
  classical
  exact ⟨dneOr d.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def implyLeftOr' (h : 𝓢 ⊢ φ ==> χ) : 𝓢 ⊢ φ ==> (χ ⋎ ψ) :=
  deduct' <| or₁' <| deductInv <| of h
omit [DecidableEq F] in
lemma «imply_left_or'!» (h : 𝓢 ⊢! φ ==> χ) : 𝓢 ⊢! φ ==> (χ ⋎ ψ) := by
  classical
  exact ⟨implyLeftOr' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def implyRightOr' (h : 𝓢 ⊢ ψ ==> χ) : 𝓢 ⊢ ψ ==> (φ ⋎ χ) :=
  deduct' <| or₂' <| deductInv <| of h
omit [DecidableEq F] in
lemma «imply_right_or'!» (h : 𝓢 ⊢! ψ ==> χ) : 𝓢 ⊢! ψ ==> (φ ⋎ χ) := by
  classical
  exact ⟨implyRightOr' h.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def implyRightAnd (hq : 𝓢 ⊢ φ ==> ψ) (hr : 𝓢 ⊢ φ ==> χ) : 𝓢 ⊢ φ ==> ψ ⋏ χ := by
  apply deduct';
  replace hq : [] ⊢[𝓢] φ ==> ψ := of hq;
  replace hr : [] ⊢[𝓢] φ ==> χ := of hr;
  exact and₃' (mdp' hq FiniteContext.id) (mdp' hr FiniteContext.id)
omit [DecidableEq F] in
lemma «imply_right_and!» (hq : 𝓢 ⊢! φ ==> ψ) (hr : 𝓢 ⊢! φ ==> χ) :
    𝓢 ⊢! φ ==> ψ ⋏ χ := by
  classical
  exact ⟨implyRightAnd hq.some hr.some⟩

omit [DecidableEq F] in
lemma «imply_left_and_comm'!» (d : 𝓢 ⊢! φ ⋏ ψ ==> χ) : 𝓢 ⊢! ψ ⋏ φ ==> χ := by
  classical
  exact imp_trans''! and_comm! d

omit [DecidableEq F] in
lemma «dhyp_and_left!» (h : 𝓢 ⊢! φ ==> χ) : 𝓢 ⊢! (ψ ⋏ φ) ==> χ := by
  classical
  apply and_imply_iff_imply_imply'!.mpr;
  apply deduct'!;
  exact FiniteContext.of'! (Γ := [ψ]) h;

omit [DecidableEq F] in
lemma «dhyp_and_right!» (h : 𝓢 ⊢! φ ==> χ) :
    𝓢 ⊢! (φ ⋏ ψ) ==> χ := by
  classical
  exact imp_trans''! and_comm! (dhyp_and_left! h)

omit [DecidableEq F] in
lemma «cut!» (d₁ : 𝓢 ⊢! φ₁ ⋏ c ==> ψ₁) (d₂ : 𝓢 ⊢! φ₂ ==> c ⋎ ψ₂) : 𝓢 ⊢! φ₁ ⋏ φ₂ ==> ψ₁ ⋎ ψ₂ := by
  classical
  apply deduct'!;
  exact or₃'''! (imply_left_or'! <|
      of'! (and_imply_iff_imply_imply'!.mp d₁) ⨀ (and₁'! id!)) or₂! (of'! d₂ ⨀ and₂'! id!);


/-- Imported declaration from the Incompleteness formalization. -/
def orComm : 𝓢 ⊢ φ ⋎ ψ ==> ψ ⋎ φ :=
  deduct' <| or₃''' or₂ or₁ FiniteContext.id
omit [DecidableEq F] in
lemma «or_comm!» : 𝓢 ⊢! φ ⋎ ψ ==> ψ ⋎ φ := by
  classical
  exact ⟨orComm⟩

/-- Imported declaration from the Incompleteness formalization. -/
def orComm' (h : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ψ ⋎ φ := orComm ⨀ h
omit [DecidableEq F] in
lemma «or_comm'!» (h : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ψ ⋎ φ := by
  classical
  exact ⟨orComm' h.some⟩


omit [DecidableEq F] in
lemma «or_assoc'!» : 𝓢 ⊢! φ ⋎ (ψ ⋎ χ) ↔ 𝓢 ⊢! (φ ⋎ ψ) ⋎ χ := by
  classical
  constructor;
  · intro h;
    exact or₃'''!
      (imply_left_or'! <| imply_left_or'! imp_id!)
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact or₃'''! (imply_left_or'! <| imply_right_or'! imp_id!) (imply_right_or'! imp_id!) id!;
      )
      h;
  · intro h;
    exact or₃'''!
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact or₃'''! (imply_left_or'! imp_id!) (imply_right_or'! <| imply_left_or'! imp_id!) id!;
      )
      (imply_right_or'! <| imply_right_or'! imp_id!)
      h;


omit [DecidableEq F] in
lemma «and_assoc!» : 𝓢 ⊢! (φ ⋏ ψ) ⋏ χ <=> φ ⋏ (ψ ⋏ χ) := by
  classical
  apply iff_intro!;
  · apply FiniteContext.deduct'!;
    have hp : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢]! φ := and₁'! <| and₁'! id!;
    have hq : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢]! ψ := and₂'! <| and₁'! id!;
    have hr : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢]! χ := and₂'! id!;
    exact and₃'! hp (and₃'! hq hr);
  · apply FiniteContext.deduct'!;
    have hp : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢]! φ := and₁'! id!;
    have hq : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢]! ψ := and₁'! <| and₂'! id!;
    have hr : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢]! χ := and₂'! <| and₂'! id!;
    apply and₃'!;
    · exact and₃'! hp hq;
    · exact hr;

/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceLeft' (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ φ ==> χ) :
    𝓢 ⊢ χ ⋏ ψ :=
  and₃' (h ⨀ and₁' hc) (and₂' hc)
omit [DecidableEq F] in
lemma «and_replace_left'!» (hc :
    𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! φ ==> χ) : 𝓢 ⊢! χ ⋏ ψ := by
  classical
  exact ⟨andReplaceLeft' hc.some h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceLeft (h : 𝓢 ⊢ φ ==> χ) : 𝓢 ⊢ φ ⋏ ψ ==> χ ⋏ ψ :=
  deduct' <| andReplaceLeft' FiniteContext.id (of h)
omit [DecidableEq F] in
lemma «and_replace_left!» (h : 𝓢 ⊢! φ ==> χ) : 𝓢 ⊢! φ ⋏ ψ ==> χ ⋏ ψ := by
  classical
  exact ⟨andReplaceLeft h.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceRight' (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ ψ ==> χ) :
    𝓢 ⊢ φ ⋏ χ :=
  and₃' (and₁' hc) (h ⨀ and₂' hc)
omit [DecidableEq F] in
lemma andReplaceRight'! (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! ψ ==> χ) : 𝓢 ⊢! φ ⋏ χ := by
  classical
  exact ⟨andReplaceRight' hc.some h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceRight (h : 𝓢 ⊢ ψ ==> χ) : 𝓢 ⊢ φ ⋏ ψ ==> φ ⋏ χ :=
  deduct' <| andReplaceRight' FiniteContext.id (of h)
omit [DecidableEq F] in
lemma «and_replace_right!» (h : 𝓢 ⊢! ψ ==> χ) : 𝓢 ⊢! φ ⋏ ψ ==> φ ⋏ χ := by
  classical
  exact ⟨andReplaceRight h.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def andReplace' (hc : 𝓢 ⊢ φ ⋏ ψ) (h₁ : 𝓢 ⊢ φ ==> χ) (h₂ : 𝓢 ⊢ ψ ==> s) :
    𝓢 ⊢ χ ⋏ s :=
  andReplaceRight' (andReplaceLeft' hc h₁) h₂
omit [DecidableEq F] in
lemma «and_replace'!» (hc :
    𝓢 ⊢! φ ⋏ ψ) (h₁ : 𝓢 ⊢! φ ==> χ) (h₂ : 𝓢 ⊢! ψ ==> s) : 𝓢 ⊢! χ ⋏ s := by
  classical
  exact ⟨andReplace' hc.some h₁.some h₂.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def andReplace (h₁ : 𝓢 ⊢ φ ==> χ) (h₂ : 𝓢 ⊢ ψ ==> s) : 𝓢 ⊢ φ ⋏ ψ ==> χ ⋏ s :=
  deduct' <| andReplace' FiniteContext.id (of h₁) (of h₂)
omit [DecidableEq F] in
lemma «and_replace!» (h₁ : 𝓢 ⊢! φ ==> χ) (h₂ : 𝓢 ⊢! ψ ==> s) :
    𝓢 ⊢! φ ⋏ ψ ==> χ ⋏ s := by
  classical
  exact ⟨andReplace h₁.some h₂.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceLeft' (hc : 𝓢 ⊢ φ ⋎ ψ) (hp : 𝓢 ⊢ φ ==> χ) :
    𝓢 ⊢ χ ⋎ ψ :=
  or₃''' (impTrans'' hp or₁) (or₂) hc
omit [DecidableEq F] in
lemma «or_replace_left'!» (hc :
    𝓢 ⊢! φ ⋎ ψ) (hp : 𝓢 ⊢! φ ==> χ) : 𝓢 ⊢! χ ⋎ ψ := by
  classical
  exact ⟨orReplaceLeft' hc.some hp.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceLeft (hp : 𝓢 ⊢ φ ==> χ) : 𝓢 ⊢ φ ⋎ ψ ==> χ ⋎ ψ :=
  deduct' <| orReplaceLeft' FiniteContext.id (of hp)
omit [DecidableEq F] in
lemma «or_replace_left!» (hp : 𝓢 ⊢! φ ==> χ) : 𝓢 ⊢! φ ⋎ ψ ==> χ ⋎ ψ := by
  classical
  exact ⟨orReplaceLeft hp.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceRight' (hc : 𝓢 ⊢ φ ⋎ ψ) (hq : 𝓢 ⊢ ψ ==> χ) :
    𝓢 ⊢ φ ⋎ χ :=
  or₃''' (or₁) (impTrans'' hq or₂) hc
omit [DecidableEq F] in
lemma «or_replace_right'!» (hc :
    𝓢 ⊢! φ ⋎ ψ) (hq : 𝓢 ⊢! ψ ==> χ) : 𝓢 ⊢! φ ⋎ χ := by
  classical
  exact ⟨orReplaceRight' hc.some hq.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceRight (hq : 𝓢 ⊢ ψ ==> χ) : 𝓢 ⊢ φ ⋎ ψ ==> φ ⋎ χ :=
  deduct' <| orReplaceRight' FiniteContext.id (of hq)
omit [DecidableEq F] in
lemma «or_replace_right!» (hq : 𝓢 ⊢! ψ ==> χ) : 𝓢 ⊢! φ ⋎ ψ ==> φ ⋎ χ := by
  classical
  exact ⟨orReplaceRight hq.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def orReplace' (h : 𝓢 ⊢ φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢ φ₁ ==> φ₂) (hq : 𝓢 ⊢ ψ₁ ==> ψ₂) :
    𝓢 ⊢ φ₂ ⋎ ψ₂ :=
  orReplaceRight' (orReplaceLeft' h hp) hq

omit [DecidableEq F] in
lemma «or_replace'!» (h :
    𝓢 ⊢! φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢! φ₁ ==> φ₂) (hq : 𝓢 ⊢! ψ₁ ==> ψ₂) : 𝓢 ⊢! φ₂ ⋎ ψ₂ := by
  classical
  exact ⟨orReplace' h.some hp.some hq.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def orReplace (hp : 𝓢 ⊢ φ₁ ==> φ₂) (hq : 𝓢 ⊢ ψ₁ ==> ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ ==> φ₂ ⋎ ψ₂ :=
  deduct' <| orReplace' FiniteContext.id (of hp) (of hq)
omit [DecidableEq F] in
lemma «or_replace!» (hp : 𝓢 ⊢! φ₁ ==> φ₂) (hq : 𝓢 ⊢! ψ₁ ==> ψ₂) :
    𝓢 ⊢! φ₁ ⋎ ψ₁ ==> φ₂ ⋎ ψ₂ := by
  classical
  exact ⟨orReplace hp.some hq.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceIff (hp : 𝓢 ⊢ φ₁ <=> φ₂) (hq : 𝓢 ⊢ ψ₁ <=> ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ <=> φ₂ ⋎ ψ₂ :=
  iffIntro (orReplace (and₁' hp) (and₁' hq)) (orReplace (and₂' hp) (and₂' hq))
omit [DecidableEq F] in
lemma «or_replace_iff!» (hp : 𝓢 ⊢! φ₁ <=> φ₂) (hq : 𝓢 ⊢! ψ₁ <=> ψ₂) :
    𝓢 ⊢! φ₁ ⋎ ψ₁ <=> φ₂ ⋎ ψ₂ := by
  classical
  exact ⟨orReplaceIff hp.some hq.some⟩

omit [DecidableEq F] in
lemma «or_assoc!» : 𝓢 ⊢! φ ⋎ (ψ ⋎ χ) <=> (φ ⋎ ψ) ⋎ χ := by
  classical
  apply iff_intro!;
  · exact deduct'! <| or_assoc'!.mp id!;
  · exact deduct'! <| or_assoc'!.mpr id!;

omit [DecidableEq F] in
lemma «or_replace_right_iff!» (d : 𝓢 ⊢! ψ <=> χ) : 𝓢 ⊢! φ ⋎ ψ <=> φ ⋎ χ := by
  classical
  exact iff_intro! (or_replace_right! <| and₁'! d) (or_replace_right! <| and₂'! d)

omit [DecidableEq F] in
lemma «or_replace_left_iff!» (d : 𝓢 ⊢! φ <=> χ) : 𝓢 ⊢! φ ⋎ ψ <=> χ ⋎ ψ := by
  classical
  exact iff_intro! (or_replace_left! <| and₁'! d) (or_replace_left! <| and₂'! d)


/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceIff (hp : 𝓢 ⊢ φ₁ <=> φ₂) (hq : 𝓢 ⊢ ψ₁ <=> ψ₂) : 𝓢 ⊢ φ₁ ⋏ ψ₁ <=> φ₂ ⋏ ψ₂ :=
  iffIntro (andReplace (and₁' hp) (and₁' hq)) (andReplace (and₂' hp) (and₂' hq))
omit [DecidableEq F] in
lemma «and_replace_iff!» (hp : 𝓢 ⊢! φ₁ <=> φ₂) (hq : 𝓢 ⊢! ψ₁ <=> ψ₂) :
    𝓢 ⊢! φ₁ ⋏ ψ₁ <=> φ₂ ⋏ ψ₂ := by
  classical
  exact ⟨andReplaceIff hp.some hq.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def impReplaceIff (hp : 𝓢 ⊢ φ₁ <=> φ₂) (hq : 𝓢 ⊢ ψ₁ <=> ψ₂) : 𝓢 ⊢ (φ₁ ==> ψ₁) <=> (φ₂ ==> ψ₂) := by
  apply iffIntro;
  · apply deduct'; exact impTrans'' (of <| and₂' hp) <| impTrans'' (FiniteContext.id) (of <|
      and₁' hq);
  · apply deduct'; exact impTrans'' (of <| and₁' hp) <| impTrans'' (FiniteContext.id) (of <|
      and₂' hq);
omit [DecidableEq F] in
lemma «imp_replace_iff!» (hp : 𝓢 ⊢! φ₁ <=> φ₂) (hq : 𝓢 ⊢! ψ₁ <=> ψ₂) :
    𝓢 ⊢! (φ₁ ==> ψ₁) <=> (φ₂ ==> ψ₂) := by
  classical
  exact ⟨impReplaceIff hp.some hq.some⟩

omit [DecidableEq F] in
lemma «imp_replace_iff!'» (hp : 𝓢 ⊢! φ₁ <=> φ₂) (hq : 𝓢 ⊢! ψ₁ <=> ψ₂) :
    𝓢 ⊢! φ₁ ==> ψ₁ ↔ 𝓢 ⊢! φ₂ ==> ψ₂ := by
  classical
  exact provable_iff_of_iff (imp_replace_iff! hp hq)

/-- Imported declaration from the Incompleteness formalization. -/
def dni : 𝓢 ⊢ φ ==> ∼∼φ :=
  deduct' <| negEquiv'.mpr <| deduct <| botOfMemEither (φ := φ) (by simp) (by simp)
omit [DecidableEq F] in
@[simp] lemma «dni!» : 𝓢 ⊢! φ ==> ∼∼φ := by
  classical
  exact ⟨dni⟩

/-- Imported declaration from the Incompleteness formalization. -/
def dni' (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ∼∼φ := dni ⨀ b
omit [DecidableEq F] in
lemma «dni'!» (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ∼∼φ := by
  classical
  exact ⟨dni' b.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def dniOr' (d : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ := or₃''' (impTrans'' dni or₁) (impTrans'' dni or₂) d
omit [DecidableEq F] in
lemma «dni_or'!» (d : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ := by
  classical
  exact ⟨dniOr' d.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def dniAnd' (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ∼∼φ ⋏ ∼∼ψ := and₃' (dni' <| and₁' d) (dni' <| and₂' d)
omit [DecidableEq F] in
lemma «dni_and'!» (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ∼∼φ ⋏ ∼∼ψ := by
  classical
  exact ⟨dniAnd' d.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def falsumDNE : 𝓢 ⊢ ∼∼⊥ ==> ⊥ := by
  apply deduct'
  have d₁ : [∼∼⊥] ⊢[𝓢] ∼⊥ ==> ⊥ := negEquiv'.mp byAxm₀
  have d₂ : [∼∼⊥] ⊢[𝓢] ∼⊥ := negEquiv'.mpr (impId ⊥)
  exact d₁ ⨀ d₂

/-- Imported declaration from the Incompleteness formalization. -/
def falsumDN : 𝓢 ⊢ ∼∼⊥ <=> ⊥ := andIntro falsumDNE dni

/-- Imported declaration from the Incompleteness formalization. -/
def dn [HasAxiomDNE 𝓢] : 𝓢 ⊢ φ <=> ∼∼φ := iffIntro dni dne
omit [DecidableEq F] in
@[simp] lemma «dn!» [HasAxiomDNE 𝓢] : 𝓢 ⊢! φ <=> ∼∼φ := by
  classical
  exact ⟨dn⟩


/-- Imported declaration from the Incompleteness formalization. -/
def contra₀ : 𝓢 ⊢ (φ ==> ψ) ==> (∼ψ ==> ∼φ) := by
  apply deduct';
  apply deduct;
  apply negEquiv'.mpr;
  apply deduct;
  have dp  : [φ, ∼ψ, φ ==> ψ] ⊢[𝓢] φ := FiniteContext.byAxm;
  have dpq : [φ, ∼ψ, φ ==> ψ] ⊢[𝓢] φ ==> ψ := FiniteContext.byAxm;
  have dq  : [φ, ∼ψ, φ ==> ψ] ⊢[𝓢] ψ := dpq ⨀ dp;
  have dnq : [φ, ∼ψ, φ ==> ψ] ⊢[𝓢] ψ ==> ⊥ := negEquiv'.mp <| FiniteContext.byAxm;
  exact dnq ⨀ dq;
omit [DecidableEq F] in
/-- Imported declaration from the Incompleteness formalization. -/
@[simp] lemma «contra₀!» : 𝓢 ⊢! (φ ==> ψ) ==> (∼ψ ==> ∼φ) := by
  classical
  exact ⟨contra₀⟩

/-- Imported declaration from the Incompleteness formalization. -/
def contra₀' (b : 𝓢 ⊢ φ ==> ψ) : 𝓢 ⊢ ∼ψ ==> ∼φ := contra₀ ⨀ b
omit [DecidableEq F] in
lemma «contra₀'!» (b : 𝓢 ⊢! φ ==> ψ) : 𝓢 ⊢! ∼ψ ==> ∼φ := by
  classical
  exact ⟨contra₀' b.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def contra₀x2' (b : 𝓢 ⊢ φ ==> ψ) : 𝓢 ⊢ ∼∼φ ==> ∼∼ψ := contra₀' <| contra₀' b
omit [DecidableEq F] in
lemma «contra₀x2'!» (b : 𝓢 ⊢! φ ==> ψ) : 𝓢 ⊢! ∼∼φ ==> ∼∼ψ := by
  classical
  exact ⟨contra₀x2' b.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def contra₀x2 : 𝓢 ⊢ (φ ==> ψ) ==> (∼∼φ ==> ∼∼ψ) := deduct' <| contra₀x2' FiniteContext.id
omit [DecidableEq F] in
@[simp] lemma «contra₀x2!» : 𝓢 ⊢! (φ ==> ψ) ==> (∼∼φ ==> ∼∼ψ) := by
  classical
  exact ⟨contra₀x2⟩


/-- Imported declaration from the Incompleteness formalization. -/
def contra₁' (b : 𝓢 ⊢ φ ==> ∼ψ) : 𝓢 ⊢ ψ ==> ∼φ := impTrans'' dni (contra₀' b)
omit [DecidableEq F] in
lemma «contra₁'!» (b : 𝓢 ⊢! φ ==> ∼ψ) : 𝓢 ⊢! ψ ==> ∼φ := by
  classical
  exact ⟨contra₁' b.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def contra₁ : 𝓢 ⊢ (φ ==> ∼ψ) ==> (ψ ==> ∼φ) := deduct' <| contra₁' FiniteContext.id
omit [DecidableEq F] in
lemma «contra₁!» : 𝓢 ⊢! (φ ==> ∼ψ) ==> (ψ ==> ∼φ) := by
  classical
  exact ⟨contra₁⟩


/-- Imported declaration from the Incompleteness formalization. -/
def contra₂' [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼φ ==> ψ) : 𝓢 ⊢ ∼ψ ==> φ := impTrans'' (contra₀' b) dne
omit [DecidableEq F] in
lemma «contra₂'!» [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼φ ==> ψ) : 𝓢 ⊢! ∼ψ ==> φ := by
  classical
  exact ⟨contra₂' b.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def contra₂ [HasAxiomDNE 𝓢] : 𝓢 ⊢ (∼φ ==> ψ) ==> (∼ψ ==> φ) := deduct' <| contra₂' FiniteContext.id
omit [DecidableEq F] in
@[simp] lemma «contra₂!» [HasAxiomDNE 𝓢] : 𝓢 ⊢! (∼φ ==> ψ) ==> (∼ψ ==> φ) := by
  classical
  exact ⟨contra₂⟩


/-- Imported declaration from the Incompleteness formalization. -/
def contra₃' [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼φ ==> ∼ψ) : 𝓢 ⊢ ψ ==> φ := impTrans'' dni (contra₂' b)
omit [DecidableEq F] in
lemma «contra₃'!» [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼φ ==> ∼ψ) : 𝓢 ⊢! ψ ==> φ := by
  classical
  exact ⟨contra₃' b.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def contra₃ [HasAxiomDNE 𝓢] : 𝓢 ⊢ (∼φ ==> ∼ψ) ==> (ψ ==> φ) :=  deduct' <| contra₃' FiniteContext.id
omit [DecidableEq F] in
@[simp 1100] lemma «contra₃!» [HasAxiomDNE 𝓢] : 𝓢 ⊢! (∼φ ==> ∼ψ) ==> (ψ ==> φ) := by
  classical
  exact ⟨contra₃⟩


/-- Imported declaration from the Incompleteness formalization. -/
def negReplaceIff' (b : 𝓢 ⊢ φ <=> ψ) :
    𝓢 ⊢ ∼φ <=> ∼ψ :=
  iffIntro (contra₀' <| and₂' b) (contra₀' <| and₁' b)
omit [DecidableEq F] in
lemma «neg_replace_iff'!» (b : 𝓢 ⊢! φ <=> ψ) : 𝓢 ⊢! ∼φ <=> ∼ψ := by
  classical
  exact ⟨negReplaceIff' b.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def iffNegLeftToRight' [HasAxiomDNE 𝓢] (h : 𝓢 ⊢ φ <=> ∼ψ) : 𝓢 ⊢ ∼φ <=> ψ :=
  iffIntro (contra₂' <| and₂' h) (contra₁' <| and₁' h)
omit [DecidableEq F] in
lemma «iff_neg_left_to_right'!» [HasAxiomDNE 𝓢] (h : 𝓢 ⊢! φ <=> ∼ψ) :
    𝓢 ⊢! ∼φ <=> ψ := by
  classical
  exact ⟨iffNegLeftToRight' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def iffNegRightToLeft' [HasAxiomDNE 𝓢] (h : 𝓢 ⊢ ∼φ <=> ψ) :
    𝓢 ⊢ φ <=> ∼ψ :=
  iffComm' <| iffNegLeftToRight' <| iffComm' h
omit [DecidableEq F] in
lemma «iff_neg_right_to_left'!» [HasAxiomDNE 𝓢] (h : 𝓢 ⊢! ∼φ <=> ψ) :
    𝓢 ⊢! φ <=> ∼ψ := by
  classical
  exact ⟨iffNegRightToLeft' h.some⟩

section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
def negnegEquiv : 𝓢 ⊢ ∼∼φ <=> ((φ ==> ⊥) ==> ⊥) := by
  apply iffIntro;
  · exact impTrans'' (by apply contra₀'; exact and₂' negEquiv) (and₁' negEquiv)
  · exact impTrans'' (and₂' negEquiv) (by apply contra₀'; exact and₁' negEquiv)
omit [DecidableEq F] in
@[simp] lemma «negnegEquiv!» : 𝓢 ⊢! ∼∼φ <=> ((φ ==> ⊥) ==> ⊥) := by
  classical
  exact ⟨negnegEquiv⟩

/-- Imported declaration from the Incompleteness formalization. -/
def negnegEquivDne [HasAxiomDNE 𝓢] : 𝓢 ⊢ φ <=> ((φ ==> ⊥) ==> ⊥) := iffTrans'' dn negnegEquiv
omit [DecidableEq F] in
lemma «negnegEquivDne!» [HasAxiomDNE 𝓢] : 𝓢 ⊢! φ <=> ((φ ==> ⊥) ==> ⊥) := by
  classical
  exact ⟨negnegEquivDne⟩

end «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
def elimContraNeg [HasAxiomElimContra 𝓢] : 𝓢 ⊢ ((ψ ==> ⊥) ==> (φ ==> ⊥)) ==> (φ ==> ψ) := by
  refine impTrans'' ?_ elimContra;
  apply deduct';
  exact impTrans'' (impTrans'' (and₁' negEquiv) FiniteContext.byAxm) (and₂' negEquiv);
omit [DecidableEq F] in
@[simp] lemma «elimContraNeg!» [HasAxiomElimContra 𝓢] :
    𝓢 ⊢! ((ψ ==> ⊥) ==> (φ ==> ⊥)) ==> (φ ==> ψ) := by
  classical
  exact ⟨elimContraNeg⟩


/-- Imported declaration from the Incompleteness formalization. -/
def tne : 𝓢 ⊢ ∼(∼∼φ) ==> ∼φ := contra₀' dni
omit [DecidableEq F] in
@[simp] lemma «tne!» : 𝓢 ⊢! ∼(∼∼φ) ==> ∼φ := by
  classical
  exact ⟨tne⟩

/-- Imported declaration from the Incompleteness formalization. -/
def tne' (b : 𝓢 ⊢ ∼(∼∼φ)) : 𝓢 ⊢ ∼φ := tne ⨀ b
omit [DecidableEq F] in
lemma «tne'!» (b : 𝓢 ⊢! ∼(∼∼φ)) : 𝓢 ⊢! ∼φ := by
  classical
  exact ⟨tne' b.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def tneIff : 𝓢 ⊢ ∼∼∼φ <=> ∼φ := andIntro tne dni

/-- Imported declaration from the Incompleteness formalization. -/
def implyLeftReplace (h : 𝓢 ⊢ ψ ==> φ) : 𝓢 ⊢ (φ ==> χ) ==> (ψ ==> χ) :=
  deduct' <| impTrans'' (of h) id
omit [DecidableEq F] in
lemma «replace_imply_left!» (h : 𝓢 ⊢! ψ ==> φ) :
    𝓢 ⊢! (φ ==> χ) ==> (ψ ==> χ) := by
  classical
  exact ⟨implyLeftReplace h.some⟩

omit [DecidableEq F] in
lemma «replace_imply_left_by_iff'!» (h : 𝓢 ⊢! φ <=> ψ) : 𝓢 ⊢! φ ==> χ ↔ 𝓢 ⊢! ψ ==> χ := by
  classical
  constructor;
  · exact imp_trans''! <| and₂'! h;
  · exact imp_trans''! <| and₁'! h;

omit [DecidableEq F] in
lemma «replace_imply_right_by_iff'!» (h : 𝓢 ⊢! φ <=> ψ) : 𝓢 ⊢! χ ==> φ ↔ 𝓢 ⊢! χ ==> ψ := by
  classical
  constructor;
  · intro hrp; exact imp_trans''! hrp <| and₁'! h;
  · intro hrq; exact imp_trans''! hrq <| and₂'! h;


/-- Imported declaration from the Incompleteness formalization. -/
def impSwap' (h : 𝓢 ⊢ φ ==> ψ ==> χ) : 𝓢 ⊢ ψ ==> φ ==> χ :=
  deduct' <| deduct <| (of (Γ := [φ, ψ]) h) ⨀ FiniteContext.byAxm ⨀ FiniteContext.byAxm
omit [DecidableEq F] in
lemma «imp_swap'!» (h : 𝓢 ⊢! (φ ==> ψ ==> χ)) : 𝓢 ⊢! (ψ ==> φ ==> χ) := by
  classical
  exact ⟨impSwap' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def impSwap : 𝓢 ⊢ (φ ==> ψ ==> χ) ==> (ψ ==> φ ==> χ) := deduct' <| impSwap' FiniteContext.id
omit [DecidableEq F] in
@[simp] lemma «imp_swap!» : 𝓢 ⊢! (φ ==> ψ ==> χ) ==> (ψ ==> φ ==> χ) := by
  classical
  exact ⟨impSwap⟩

/-- Imported declaration from the Incompleteness formalization. -/
def ppq (h : 𝓢 ⊢ φ ==> φ ==> ψ) : 𝓢 ⊢ φ ==> ψ :=
  deduct' <| of (Γ := [φ]) h ⨀ FiniteContext.byAxm ⨀ FiniteContext.byAxm
omit [DecidableEq F] in
lemma «ppq!» (h : 𝓢 ⊢! φ ==> φ ==> ψ) : 𝓢 ⊢! φ ==> ψ := by
  classical
  exact ⟨ppq h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def pPqQ : 𝓢 ⊢ φ ==> (φ ==> ψ) ==> ψ := impSwap' <| impId _
omit [DecidableEq F] in
lemma «pPqQ!» : 𝓢 ⊢! φ ==> (φ ==> ψ) ==> ψ := by
  classical
  exact ⟨pPqQ⟩

/-- Imported declaration from the Incompleteness formalization. -/
def dhypImp' (h : 𝓢 ⊢ φ ==> ψ) : 𝓢 ⊢ (χ ==> φ) ==> (χ ==> ψ) := imply₂ ⨀ (imply₁' h)
omit [DecidableEq F] in
lemma dhypImp'! (h : 𝓢 ⊢! φ ==> ψ) : 𝓢 ⊢! (χ ==> φ) ==> (χ ==> ψ) := by
  classical
  exact ⟨dhypImp' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def revDhypImp' (h : 𝓢 ⊢ ψ ==> φ) : 𝓢 ⊢ (φ ==> χ) ==> (ψ ==> χ) := impSwap' <| impTrans'' h pPqQ
omit [DecidableEq F] in
lemma «revDhypImp'!» (h : 𝓢 ⊢! ψ ==> φ) : 𝓢 ⊢! (φ ==> χ) ==> (ψ ==> χ) := by
  classical
  exact ⟨revDhypImp' h.some⟩

-- TODO: Actually this can be computable but it's too slow.
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def dnDistributeImply : 𝓢 ⊢ ∼∼(φ ==> ψ) ==> (∼∼φ ==> ∼∼ψ) :=
  impSwap' <| deduct' <| impTrans'' (contra₀x2' <| deductInv <| of <| impSwap' <| contra₀x2) tne
omit [DecidableEq F] in
@[simp] lemma «dn_distribute_imply!» : 𝓢 ⊢! ∼∼(φ ==> ψ) ==> (∼∼φ ==> ∼∼ψ) := by
  classical
  exact ⟨dnDistributeImply⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def dnDistributeImply' (b : 𝓢 ⊢ ∼∼(φ ==> ψ)) :
    𝓢 ⊢ ∼∼φ ==> ∼∼ψ :=
  dnDistributeImply ⨀ b
omit [DecidableEq F] in
lemma «dn_distribute_imply'!» (b : 𝓢 ⊢! ∼∼(φ ==> ψ)) :
    𝓢 ⊢! ∼∼φ ==> ∼∼ψ := by
  classical
  exact ⟨dnDistributeImply' b.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def introFalsumOfAnd' (h : 𝓢 ⊢ φ ⋏ ∼φ) : 𝓢 ⊢ ⊥ := (negEquiv'.mp <| and₂' h) ⨀ (and₁' h)
omit [DecidableEq F] in
lemma «intro_falsum_of_and'!» (h : 𝓢 ⊢! φ ⋏ ∼φ) : 𝓢 ⊢! ⊥ := by
  classical
  exact ⟨introFalsumOfAnd' h.some⟩
/-- Law of contradiction -/
alias lac'! := intro_falsum_of_and'!

/-- Imported declaration from the Incompleteness formalization. -/
def introFalsumOfAnd : 𝓢 ⊢ φ ⋏ ∼φ ==> ⊥ :=
  deduct' <| introFalsumOfAnd' (φ := φ) FiniteContext.id
omit [DecidableEq F] in
@[simp] lemma «intro_bot_of_and!» : 𝓢 ⊢! φ ⋏ ∼φ ==> ⊥ := by
  classical
  exact ⟨introFalsumOfAnd⟩
/-- Law of contradiction -/
alias lac! := intro_bot_of_and!



/-- Imported declaration from the Incompleteness formalization. -/
def implyOfNotOr [HasAxiomEFQ 𝓢] : 𝓢 ⊢ (∼φ ⋎ ψ) ==> (φ ==> ψ) := or₃'' (by
    apply emptyPrf;
    apply deduct;
    apply deduct;
    exact efqOfMemEither (φ := φ) (by simp) (by simp)
  ) imply₁
omit [DecidableEq F] in
@[simp] lemma «imply_of_not_or!» [HasAxiomEFQ 𝓢] : 𝓢 ⊢! (∼φ ⋎ ψ) ==> (φ ==> ψ) := by
  classical
  exact ⟨implyOfNotOr⟩

/-- Imported declaration from the Incompleteness formalization. -/
def implyOfNotOr' [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢ ∼φ ⋎ ψ) : 𝓢 ⊢ φ ==> ψ := implyOfNotOr ⨀ b
omit [DecidableEq F] in
lemma «imply_of_not_or'!» [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢! ∼φ ⋎ ψ) : 𝓢 ⊢! φ ==> ψ := by
  classical
  exact ⟨implyOfNotOr' b.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def demorgan₁ : 𝓢 ⊢ (∼φ ⋎ ∼ψ) ==> ∼(φ ⋏ ψ) := or₃'' (contra₀' and₁) (contra₀' and₂)
omit [DecidableEq F] in
@[simp] lemma «demorgan₁!» : 𝓢 ⊢! (∼φ ⋎ ∼ψ) ==> ∼(φ ⋏ ψ) := by
  classical
  exact ⟨demorgan₁⟩

/-- Imported declaration from the Incompleteness formalization. -/
def demorgan₁' (d : 𝓢 ⊢ ∼φ ⋎ ∼ψ) : 𝓢 ⊢ ∼(φ ⋏ ψ)  := demorgan₁ ⨀ d
omit [DecidableEq F] in
lemma «demorgan₁'!» (d : 𝓢 ⊢! ∼φ ⋎ ∼ψ) : 𝓢 ⊢! ∼(φ ⋏ ψ) := by
  classical
  exact ⟨demorgan₁' d.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def demorgan₂ : 𝓢 ⊢ (∼φ ⋏ ∼ψ) ==> ∼(φ ⋎ ψ) := by
  apply andImplyIffImplyImply'.mpr;
  apply deduct';
  apply deduct;
  apply negEquiv'.mpr;
  apply deduct;
  exact or₃''' (negEquiv'.mp FiniteContext.byAxm) (negEquiv'.mp FiniteContext.byAxm)
    (FiniteContext.byAxm (φ :=
    φ ⋎ ψ));
omit [DecidableEq F] in
@[simp] lemma «demorgan₂!» : 𝓢 ⊢! ∼φ ⋏ ∼ψ ==> ∼(φ ⋎ ψ) := by
  classical
  exact ⟨demorgan₂⟩

/-- Imported declaration from the Incompleteness formalization. -/
def demorgan₂' (d : 𝓢 ⊢ ∼φ ⋏ ∼ψ) : 𝓢 ⊢ ∼(φ ⋎ ψ) := demorgan₂ ⨀ d
omit [DecidableEq F] in
lemma «demorgan₂'!» (d : 𝓢 ⊢! ∼φ ⋏ ∼ψ) : 𝓢 ⊢! ∼(φ ⋎ ψ) := by
  classical
  exact ⟨demorgan₂' d.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def demorgan₃ : 𝓢 ⊢ ∼(φ ⋎ ψ) ==> (∼φ ⋏ ∼ψ) :=
  deduct' <| and₃' (deductInv <| contra₀' or₁) (deductInv <| contra₀' or₂)
omit [DecidableEq F] in
@[simp] lemma «demorgan₃!» : 𝓢 ⊢! ∼(φ ⋎ ψ) ==> (∼φ ⋏ ∼ψ) := by
  classical
  exact ⟨demorgan₃⟩

/-- Imported declaration from the Incompleteness formalization. -/
def demorgan₃' (b : 𝓢 ⊢ ∼(φ ⋎ ψ)) : 𝓢 ⊢ ∼φ ⋏ ∼ψ := demorgan₃ ⨀ b
omit [DecidableEq F] in
lemma «demorgan₃'!» (b : 𝓢 ⊢! ∼(φ ⋎ ψ)) : 𝓢 ⊢! ∼φ ⋏ ∼ψ := by
  classical
  exact ⟨demorgan₃' b.some⟩


-- TODO: Actually this can be computable but it's too slow.
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def demorgan₄ [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼(φ ⋏ ψ) ==> (∼φ ⋎ ∼ψ) :=
  contra₂' <| deduct' <| andReplace' (demorgan₃' FiniteContext.id) dne dne
omit [DecidableEq F] in
@[simp] lemma «demorgan₄!» [HasAxiomDNE 𝓢] : 𝓢 ⊢! ∼(φ ⋏ ψ) ==> (∼φ ⋎ ∼ψ) := by
  classical
  exact ⟨demorgan₄⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def demorgan₄' [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼(φ ⋏ ψ)) : 𝓢 ⊢ ∼φ ⋎ ∼ψ := demorgan₄ ⨀ b
omit [DecidableEq F] in
lemma «demorgan₄'!» [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼(φ ⋏ ψ)) : 𝓢 ⊢! ∼φ ⋎ ∼ψ := by
  classical
  exact ⟨demorgan₄' b.some⟩

-- TODO: Actually this can be computable but it's too slow.
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def NotOrOfImply' [HasAxiomDNE 𝓢] (d : 𝓢 ⊢ φ ==> ψ) : 𝓢 ⊢ ∼φ ⋎ ψ := by
  apply dne';
  apply negEquiv'.mpr;
  apply deduct';
  have d₁ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼∼φ ⋏ ∼ψ := demorgan₃' <| FiniteContext.id;
  have d₂ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼φ ==> ⊥ := negEquiv'.mp <| and₁' d₁;
  have d₃ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼φ := (of (Γ := [∼(∼φ ⋎ ψ)]) <| contra₀' d) ⨀ (and₂' d₁);
  exact d₂ ⨀ d₃;
omit [DecidableEq F] in
lemma «not_or_of_imply'!» [HasAxiomDNE 𝓢] (d : 𝓢 ⊢! φ ==> ψ) : 𝓢 ⊢! ∼φ ⋎ ψ := by
  classical
  exact ⟨NotOrOfImply' d.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def NotOrOfImply [HasAxiomDNE 𝓢] : 𝓢 ⊢ (φ ==> ψ) ==> (∼φ ⋎ ψ) :=
  deduct' <| NotOrOfImply' FiniteContext.byAxm
omit [DecidableEq F] in
lemma «not_or_of_imply!» [HasAxiomDNE 𝓢] : 𝓢 ⊢! (φ ==> ψ) ==> ∼φ ⋎ ψ := by
  classical
  exact ⟨NotOrOfImply⟩

-- TODO: Actually this can be computable but it's too slow.
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def dnCollectImply [HasAxiomEFQ 𝓢] : 𝓢 ⊢ (∼∼φ ==> ∼∼ψ) ==> ∼∼(φ ==> ψ) := by
  apply deduct';
  apply negEquiv'.mpr;
  exact impTrans''
    (by
      apply deductInv;
      apply andImplyIffImplyImply'.mp;
      apply deduct;
      have d₁ : [(∼∼φ ==> ∼∼ψ) ⋏ ∼(φ ==> ψ)] ⊢[𝓢] ∼∼φ ==> ∼∼ψ :=
        and₁' (ψ := ∼(φ ==> ψ)) <| FiniteContext.id;
      have d₂ : [(∼∼φ ==> ∼∼ψ) ⋏ ∼(φ ==> ψ)] ⊢[𝓢] ∼∼φ ⋏ ∼ψ :=
        demorgan₃' <| (contra₀' implyOfNotOr) ⨀ (and₂' (φ := (∼∼φ ==> ∼∼ψ)) <| FiniteContext.id)
      exact and₃' (and₂' d₂) (d₁ ⨀ (and₁' d₂))
    )
    (introFalsumOfAnd (φ := ∼ψ));

omit [DecidableEq F] in
@[simp] lemma «dn_collect_imply!» [HasAxiomEFQ 𝓢] :
    𝓢 ⊢! (∼∼φ ==> ∼∼ψ) ==> ∼∼(φ ==> ψ) := by
  classical
  exact ⟨dnCollectImply⟩

-- TODO: Actually this can be computable but it's too slow.
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def dnCollectImply' [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢ ∼∼φ ==> ∼∼ψ) :
    𝓢 ⊢ ∼∼(φ ==> ψ) :=
  dnCollectImply ⨀ b
omit [DecidableEq F] in
lemma «dn_collect_imply'!» [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢! ∼∼φ ==> ∼∼ψ) :
    𝓢 ⊢! ∼∼(φ ==> ψ) := by
  classical
  exact ⟨dnCollectImply' b.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def andImplyAndOfImply {φ ψ φ' ψ' : F} (bp : 𝓢 ⊢ φ ==> φ') (bq : 𝓢 ⊢ ψ ==> ψ') :
    𝓢 ⊢ φ ⋏ ψ ==> φ' ⋏ ψ' :=
  deduct' <| andIntro
    (deductInv' <| impTrans'' and₁ bp)
    (deductInv' <| impTrans'' and₂ bq)

/-- Imported declaration from the Incompleteness formalization. -/
def andIffAndOfIff {φ ψ φ' ψ' : F} (bp : 𝓢 ⊢ φ <=> φ') (bq : 𝓢 ⊢ ψ <=> ψ') :
    𝓢 ⊢ φ ⋏ ψ <=> φ' ⋏ ψ' :=
  iffIntro (andImplyAndOfImply (andLeft bp) (andLeft bq)) (andImplyAndOfImply (andRight bp)
    (andRight bq))


section «lp_section_2»

omit [DecidableEq F] in
instance [HasAxiomDNE 𝓢] : HasAxiomEFQ 𝓢 where
  efq φ := by
    classical
    apply contra₃';
    exact impTrans'' (and₁' negEquiv) <| impTrans'' (impSwap' imply₁) (and₂' negEquiv);


-- TODO: Actually this can be computable but it's too slow.
omit [DecidableEq F] in
noncomputable instance [HasAxiomDNE 𝓢] : HasAxiomLEM 𝓢 where
  lem _ := by
    classical
    exact dneOr <| NotOrOfImply' dni

omit [DecidableEq F] in
instance [HasAxiomEFQ 𝓢] [HasAxiomLEM 𝓢] : HasAxiomDNE 𝓢 where
  dne φ := by
    classical
    apply deduct';
    exact or₃''' (impId _) (by
      apply deduct;
      have nnp : [∼φ, ∼∼φ] ⊢[𝓢] ∼φ ==> ⊥ := negEquiv'.mp <| FiniteContext.byAxm;
      have np : [∼φ, ∼∼φ] ⊢[𝓢] ∼φ := FiniteContext.byAxm;
      exact efq' <| nnp ⨀ np;
    ) <| of lem;;

omit [DecidableEq F] in
instance [HasAxiomLEM 𝓢] : HasAxiomWeakLEM 𝓢 where
  wlem φ := by
    classical
    exact lem (φ := ∼φ);

omit [DecidableEq F] in
instance [HasAxiomEFQ 𝓢] [HasAxiomLEM 𝓢] : HasAxiomDummett 𝓢 where
  dummett φ ψ := by
    classical
    have d₁ : 𝓢 ⊢ φ ==> ((φ ==> ψ) ⋎ (ψ ==> φ)) := impTrans'' imply₁ or₂;
    have d₂ : 𝓢 ⊢ ∼φ ==> ((φ ==> ψ) ⋎ (ψ ==> φ)) := impTrans'' efqImplyNot₁ or₁;
    exact or₃''' d₁ d₂ lem;

omit [DecidableEq F] in
instance [HasAxiomDummett 𝓢] : HasAxiomWeakLEM 𝓢 where
  wlem φ := by
    classical
    haveI : 𝓢 ⊢ (φ ==> ∼φ) ⋎ (∼φ ==> φ) := dummett;
    exact or₃''' (by
      apply deduct';
      apply or₁';
      apply negEquiv'.mpr;
      apply deduct;
      haveI d₁ : [φ, φ ==> ∼φ] ⊢[𝓢] φ := FiniteContext.byAxm;
      haveI d₂ : [φ, φ ==> ∼φ] ⊢[𝓢] φ ==> ∼φ := FiniteContext.byAxm;
      have := negEquiv'.mp <| d₂ ⨀ d₁;
      exact this ⨀ d₁;
    ) (by
      apply deduct';
      apply or₂';
      apply negEquiv'.mpr;
      apply deduct;
      haveI d₁ : [∼φ, ∼φ ==> φ] ⊢[𝓢] ∼φ := FiniteContext.byAxm;
      haveI d₂ : [∼φ, ∼φ ==> φ] ⊢[𝓢] ∼φ ==> φ := FiniteContext.byAxm;
      haveI := d₂ ⨀ d₁;
      exact (negEquiv'.mp d₁) ⨀ this;
    ) this;

omit [DecidableEq F] in
noncomputable instance [HasAxiomDNE 𝓢] : HasAxiomPeirce 𝓢 where
  peirce φ ψ := by
    classical
    refine or₃''' imply₁ ?_ lem;
    apply deduct';
    apply deduct;
    refine (FiniteContext.byAxm (φ := (φ ==> ψ) ==> φ)) ⨀ ?_;
    apply deduct;
    apply efqOfMemEither (by aesop) (by aesop)

omit [DecidableEq F] in
instance [HasAxiomDNE 𝓢] : HasAxiomElimContra 𝓢 where
  elimContra φ ψ := by
    classical
    apply deduct';
    have : [∼ψ ==> ∼φ] ⊢[𝓢] ∼ψ ==> ∼φ := FiniteContext.byAxm;
    exact contra₃' this;

end «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def implyIffNotOr [HasAxiomDNE 𝓢] : 𝓢 ⊢ (φ ==> ψ) <=> (∼φ ⋎ ψ) := iffIntro
  NotOrOfImply (deduct' (orCases efqImplyNot₁ imply₁ byAxm₀))

omit [DecidableEq F] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma «imply_iff_not_or!» [HasAxiomDNE 𝓢] : 𝓢 ⊢! (φ ==> ψ) <=> (∼φ ⋎ ψ) := by
  classical
  exact ⟨implyIffNotOr⟩

/-- Imported declaration from the Incompleteness formalization. -/
def conjIffConj : (Γ : List F) → 𝓢 ⊢ ⋀Γ <=> Γ.conj
  | []          => iffId ⊤
  | [_]         => iffIntro (deduct' <| andIntro FiniteContext.id verum) and₁
  | φ :: ψ :: Γ => andIffAndOfIff (iffId φ) (conjIffConj (ψ :: Γ))
omit [DecidableEq F] in
@[simp] lemma «conjIffConj!» : 𝓢 ⊢! ⋀Γ <=> Γ.conj := by
  classical
  exact ⟨conjIffConj Γ⟩


omit [DecidableEq F] in
lemma «implyLeft_conj_eq_conj!» :
    𝓢 ⊢! Γ.conj ==> φ ↔ 𝓢 ⊢! ⋀Γ ==> φ := by
  classical
  exact replace_imply_left_by_iff'! <| iff_comm'! conjIffConj!


omit [DecidableEq F] in
lemma «generalConj'!» (h : φ ∈ Γ) :
    𝓢 ⊢! ⋀Γ ==> φ := by
  classical
  exact replace_imply_left_by_iff'! conjIffConj! |>.mpr (generalConj! h)
omit [DecidableEq F] in
lemma «generalConj'₂!» (h : φ ∈ Γ) (d : 𝓢 ⊢! ⋀Γ) : 𝓢 ⊢! φ := by
  classical
  exact (generalConj'! h) ⨀ d

section «lp_section_3»

omit [DecidableEq F] in
lemma iff_provable_list_conj {Γ : List F} : (𝓢 ⊢! ⋀Γ) ↔ (∀ φ ∈ Γ, 𝓢 ⊢! φ) := by
  classical
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, conj₂_cons_nonempty, mem_cons, forall_eq_or_imp]
    constructor;
    · intro h;
      constructor;
      · exact and₁'! h;
      · exact ih.mp (and₂'! h);
    · rintro ⟨h₁, h₂⟩;
      exact and₃'! h₁ (ih.mpr h₂);

omit [DecidableEq F] in
lemma «conjconj_subset!» (h : ∀ φ, φ ∈ Γ → φ ∈ Δ) : 𝓢 ⊢! ⋀Δ ==> ⋀Γ := by
  classical
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle =>
    simp_all only [mem_cons, not_mem_nil, or_false, forall_eq, conj₂_singleton]
    exact generalConj'! h;
  | hcons φ Γ hne ih =>
    simp_all only [ne_eq, mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp,
      not_false_eq_true, conj₂_cons_nonempty]
    exact imply_right_and! (generalConj'! h.1) ih;

omit [DecidableEq F] in
lemma «conjconj_provable!» (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢]! φ) : 𝓢 ⊢! ⋀Δ ==> ⋀Γ := by
  classical
  exact by induction Γ using List.induction_with_singleton with
  | hnil => exact imply₁'! verum!;
  | hsingle =>
    simp_all only [mem_cons, not_mem_nil, or_false, forall_eq, conj₂_singleton]
    exact provable_iff.mp h;
  | hcons φ Γ hne ih =>
    simp_all only [ne_eq, mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp,
      not_false_eq_true, conj₂_cons_nonempty]
    exact imply_right_and! (provable_iff.mp h.1) ih;

omit [DecidableEq F] in
lemma «conjconj_provable₂!» (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢]! φ) :
    Δ ⊢[𝓢]! ⋀Γ := by
  classical
  exact provable_iff.mpr <| conjconj_provable! h

omit [DecidableEq F] in
lemma «id_conj!» (he : ∀ g ∈ Γ, g = φ) : 𝓢 ⊢! φ ==> ⋀Γ := by
  classical
  induction Γ using List.induction_with_singleton with
  | hcons χ Γ h ih =>
    simp_all only [ne_eq, not_false_eq_true, conj₂_cons_nonempty, mem_cons, forall_eq_or_imp]
    have ⟨he₁, he₂⟩ := he; subst he₁;
    exact imply_right_and! imp_id! (ih he₂);
  | _ => simp_all;

omit [DecidableEq F] in
lemma «replace_imply_left_conj!» (he : ∀ g ∈ Γ, g = φ) (hd : 𝓢 ⊢! ⋀Γ ==> ψ) :
    𝓢 ⊢! φ ==> ψ := by
  classical
  exact imp_trans''! (id_conj! he) hd

omit [DecidableEq F] in
lemma «iff_imply_left_cons_conj'!» : 𝓢 ⊢! ⋀(φ :: Γ) ==> ψ ↔ 𝓢 ⊢! φ ⋏ ⋀Γ ==> ψ := by
  classical
  induction Γ with
  | nil =>
    simp only [conj₂_singleton, conj₂_nil, and_imply_iff_imply_imply'!]
    constructor;
    · intro h; apply imp_swap'!; exact imply₁'! h;
    · intro h; exact imp_swap'! h ⨀ verum!;
  | cons ψ ih => simp;

omit [DecidableEq F] in
@[simp]
lemma «imply_left_concat_conj!» : 𝓢 ⊢! ⋀(Γ ++ Δ) ==> ⋀Γ ⋏ ⋀Δ := by
  classical
  apply FiniteContext.deduct'!;
  have : [⋀(Γ ++ Δ)] ⊢[𝓢]! ⋀(Γ ++ Δ) := id!;
  have d := iff_provable_list_conj.mp this;
  apply and₃'!;
  · apply iff_provable_list_conj.mpr;
    intro φ hp;
    exact d φ (by simpa only [List.mem_append] using Or.inl hp);
  · apply iff_provable_list_conj.mpr;
    intro φ hp;
    exact d φ (by simpa only [List.mem_append] using Or.inr hp);

@[simp]
lemma «forthback_conj_remove!» : 𝓢 ⊢! ⋀(Γ.remove φ) ⋏ φ ==> ⋀Γ := by
  apply deduct'!;
  apply iff_provable_list_conj.mpr;
  intro ψ hq;
  by_cases e : ψ = φ;
  · subst e; exact and₂'! id!;
  · exact iff_provable_list_conj.mp (and₁'! id!) ψ (by apply List.mem_remove_iff.mpr; simp_all);

lemma «imply_left_remove_conj!» (b : 𝓢 ⊢! ⋀Γ ==> ψ) :
    𝓢 ⊢! ⋀(Γ.remove φ) ⋏ φ ==> ψ :=
  imp_trans''! forthback_conj_remove! b

omit [DecidableEq F] in
lemma «iff_concat_conj'!» : 𝓢 ⊢! ⋀(Γ ++ Δ) ↔ 𝓢 ⊢! ⋀Γ ⋏ ⋀Δ := by
  classical
  constructor;
  · intro h;
    replace h := iff_provable_list_conj.mp h;
    apply and₃'!;
    · apply iff_provable_list_conj.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; left; simpa);
    · apply iff_provable_list_conj.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; right; simpa);
  · intro h;
    apply iff_provable_list_conj.mpr;
    simp only [List.mem_append];
    rintro φ (hp₁ | hp₂);
    · exact (iff_provable_list_conj.mp <| and₁'! h) φ hp₁;
    · exact (iff_provable_list_conj.mp <| and₂'! h) φ hp₂;

omit [DecidableEq F] in
@[simp]
lemma «iff_concat_conj!» : 𝓢 ⊢! ⋀(Γ ++ Δ) <=> ⋀Γ ⋏ ⋀Δ := by
  classical
  apply iff_intro!;
  · apply deduct'!; apply iff_concat_conj'!.mp; exact id!;
  · apply deduct'!; apply iff_concat_conj'!.mpr; exact id!;

omit [DecidableEq F] in
lemma «imply_left_conj_concat!» : 𝓢 ⊢! ⋀(Γ ++ Δ) ==> φ ↔ 𝓢 ⊢! (⋀Γ ⋏ ⋀Δ) ==> φ := by
  classical
  constructor;
  · intro h; exact imp_trans''! (and₂'! iff_concat_conj!) h;
  · intro h; exact imp_trans''! (and₁'! iff_concat_conj!) h;

end «lp_section_3»


section «lp_section_4»

omit [DecidableEq F] in
lemma «iff_concact_disj!» [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁(Γ ++ Δ) <=> ⋁Γ ⋎ ⋁Δ := by
  classical
  induction Γ using List.induction_with_singleton generalizing Δ <;>
    induction Δ using List.induction_with_singleton;
  case hnil.hnil =>
    simp_all only [append_nil, disj₂_nil]
    apply iff_intro!;
    · simp;
    · exact or₃''! efq! efq!;
  case hnil.hsingle =>
    simp_all only [nil_append, disj₂_singleton, disj₂_nil]
    apply iff_intro!;
    · simp;
    · exact or₃''! efq! imp_id!;
  case hsingle.hnil =>
    simp_all only [append_nil, disj₂_nil, disj₂_singleton]
    apply iff_intro!;
    · simp;
    · exact or₃''! imp_id! efq!;
  case hcons.hnil =>
    simp_all only [ne_eq, append_nil, not_false_eq_true, disj₂_cons_nonempty, disj₂_nil]
    apply iff_intro!;
    · simp;
    · exact or₃''! imp_id! efq!;
  case hnil.hcons =>
    simp_all only [ne_eq, nil_append, disj₂_nil, not_false_eq_true, disj₂_cons_nonempty]
    apply iff_intro!;
    · simp;
    · exact or₃''! efq! imp_id!;
  case hsingle.hsingle => simp_all;
  case hsingle.hcons => simp_all;
  case hcons.hsingle φ ps hps ihp ψ =>
    simp_all only [ne_eq, cons_append, append_eq_nil_iff, cons_ne_self, and_self,
      not_false_eq_true, disj₂_cons_nonempty, disj₂_singleton]
    apply iff_trans''! (by
      apply or_replace_right_iff!;
      simpa using @ihp [ψ];
    ) or_assoc!;
  case hcons.hcons φ ps hps ihp ψ qs hqs ihq =>
    simp_all only [ne_eq, cons_append, append_eq_nil_iff, and_self, not_false_eq_true,
      disj₂_cons_nonempty, reduceCtorEq]
    exact iff_trans''! (by
      apply or_replace_right_iff!;
      exact iff_trans''! (@ihp (ψ :: qs)) (by
        apply or_replace_right_iff!;
        simp_all;
      )
    ) or_assoc!;

omit [DecidableEq F] in
lemma «iff_concact_disj'!» [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁(Γ ++ Δ) ↔ 𝓢 ⊢! ⋁Γ ⋎ ⋁Δ := by
  classical
  constructor;
  · intro h; exact (and₁'! iff_concact_disj!) ⨀ h;
  · intro h; exact (and₂'! iff_concact_disj!) ⨀ h;

omit [DecidableEq F] in
lemma «implyRight_cons_disj!» [HasAxiomEFQ 𝓢] : 𝓢 ⊢! φ ==> ⋁(ψ :: Γ) ↔ 𝓢 ⊢! φ ==> ψ ⋎ ⋁Γ := by
  classical
  induction Γ with
  | nil =>
    simp only [disj₂_singleton, disj₂_nil];
    constructor;
    · intro h; exact imp_trans''! h or₁!;
    · intro h; exact imp_trans''! h <| or₃''! imp_id! efq!;
  | cons ψ ih => simp;

@[simp]
lemma forthback_disj_remove [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁Γ ==> φ ⋎ ⋁(Γ.remove φ) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle ψ =>
    simp only [disj₂_singleton];
    by_cases h: ψ = φ;
    · subst_vars; simp;
    · simp [(List.remove_singleton_of_ne h)];
  | hcons ψ Γ h ih =>
    simp_all only [ne_eq, not_false_eq_true, disj₂_cons_nonempty]
    by_cases hpq : ψ = φ;
    · simp_all only [List.remove_cons_self]; exact or₃''! or₁! ih;
    · rw [List.remove_cons_of_ne Γ hpq];
      by_cases hqΓ : Γ.remove φ = [];
      · simp_all only [disj₂_nil, disj₂_singleton]
        exact or₃''! or₂! (imp_trans''! ih <| or_replace_right! efq!);
      · simp_all only [ne_eq, not_false_eq_true, disj₂_cons_nonempty]
        exact or₃''! (imp_trans''! or₁! or₂!) (imp_trans''! ih (or_replace_right! or₂!));

omit [DecidableEq F] in
lemma «disj_allsame!» [HasAxiomEFQ 𝓢] (hd : ∀ ψ ∈ Γ, ψ = φ) : 𝓢 ⊢! ⋁Γ ==> φ := by
  classical
  induction Γ using List.induction_with_singleton with
  | hcons ψ Δ hΔ ih =>
    simp_all only [ne_eq, not_false_eq_true, disj₂_cons_nonempty, mem_cons, forall_eq_or_imp]
    have ⟨hd₁, hd₂⟩ := hd; subst hd₁;
    apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    exact or₃'''! (by simp) (weakening! (by simp) <| provable_iff_provable.mp <| ih hd₂) id!
  | _ => simp_all;

omit [DecidableEq F] in
lemma «disj_allsame'!» [HasAxiomEFQ 𝓢] (hd : ∀ ψ ∈ Γ, ψ = φ) (h : 𝓢 ⊢! ⋁Γ) :
    𝓢 ⊢! φ := by
  classical
  exact (disj_allsame! hd) ⨀ h

end «lp_section_4»

section «lp_section_5»

variable [HasAxiomEFQ 𝓢]

omit [DecidableEq F] in
lemma inconsistent_of_provable_of_unprovable {φ : F}
    (hp : 𝓢 ⊢! φ) (hn : 𝓢 ⊢! ∼φ) : Inconsistent 𝓢 := by
  classical
  have : 𝓢 ⊢! φ ==> ⊥ := negEquiv'!.mp hn
  intro ψ; exact efq! ⨀ (this ⨀ hp)

end «lp_section_5»

end Entailment
end LO
