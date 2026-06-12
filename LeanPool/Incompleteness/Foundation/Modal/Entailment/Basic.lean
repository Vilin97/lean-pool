/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Logic.Disjunctive
import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental
import LeanPool.Incompleteness.Foundation.Modal.Axioms

/-! # Basic -/


namespace LO
namespace Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S}


/-- Imported declaration from the Incompleteness formalization. -/
class Necessitation (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  nec {φ : F} : 𝓢 ⊢ φ → 𝓢 ⊢ □φ

section «lp_section_1»

variable [Necessitation 𝓢]
alias nec := Necessitation.nec

lemma «nec!» : 𝓢 ⊢! φ → 𝓢 ⊢! □φ := by rintro ⟨hp⟩; exact ⟨nec hp⟩

/-- Imported declaration from the Incompleteness formalization. -/
def multinec : 𝓢 ⊢ φ → 𝓢 ⊢ □^[n]φ := by
  intro h;
  induction n with
  | zero => simpa;
  | succ n ih => simpa using nec ih;
lemma «multinec!» : 𝓢 ⊢! φ → 𝓢 ⊢! □^[n]φ := by rintro ⟨hp⟩; exact ⟨multinec hp⟩

end «lp_section_1»


/-- Imported declaration from the Incompleteness formalization. -/
class Unnecessitation (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  unnec {φ : F} : 𝓢 ⊢ □φ → 𝓢 ⊢ φ

section «lp_section_2»

variable [Unnecessitation 𝓢]

alias unnec := Unnecessitation.unnec
lemma «unnec!» : 𝓢 ⊢! □φ → 𝓢 ⊢! φ := by rintro ⟨hp⟩; exact ⟨unnec hp⟩

/-- Imported declaration from the Incompleteness formalization. -/
def multiunnec : 𝓢 ⊢ □^[n]φ → 𝓢 ⊢ φ := by
  intro h;
  induction n generalizing φ with
  | zero => simpa;
  | succ n ih => exact unnec <| @ih (□φ) h;
lemma «multiunnec!» : 𝓢 ⊢! □^[n]φ → 𝓢 ⊢! φ := by rintro ⟨hp⟩; exact ⟨multiunnec hp⟩

end «lp_section_2»


/-- Imported declaration from the Incompleteness formalization. -/
class LoebRule [LogicalConnective F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  loeb {φ : F} : 𝓢 ⊢ □φ ==> φ → 𝓢 ⊢ φ

section «lp_section_3»

variable [LoebRule 𝓢]

alias loeb := LoebRule.loeb
lemma «loeb!» : 𝓢 ⊢! □φ ==> φ → 𝓢 ⊢! φ := by rintro ⟨hp⟩; exact ⟨loeb hp⟩

end «lp_section_3»


/-- Imported declaration from the Incompleteness formalization. -/
class HenkinRule [LogicalConnective F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  henkin {φ : F} : 𝓢 ⊢ □φ <=> φ → 𝓢 ⊢ φ

section «lp_section_4»

variable [HenkinRule 𝓢]

alias henkin := HenkinRule.henkin
lemma «henkin!» : 𝓢 ⊢! □φ <=> φ → 𝓢 ⊢! φ := by rintro ⟨hp⟩; exact ⟨henkin hp⟩

end «lp_section_4»



/-- Imported declaration from the Incompleteness formalization. -/
class HasDiaDuality (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  diaDual (φ : F) : 𝓢 ⊢ Axioms.DiaDuality φ

section «lp_section_5»

variable [HasDiaDuality 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def diaDuality : 𝓢 ⊢ ◇φ <=> ∼(□(∼φ)) := HasDiaDuality.diaDual _
@[simp] lemma «dia_duality!» : 𝓢 ⊢! ◇φ <=> ∼(□(∼φ)) := ⟨diaDuality⟩

end «lp_section_5»



/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomK [LogicalConnective F] [Box F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  K (φ ψ : F) : 𝓢 ⊢ Axioms.K φ ψ

section «lp_section_6»

variable [HasAxiomK 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomK : 𝓢 ⊢ □(φ ==> ψ) ==> □φ ==> □ψ := HasAxiomK.K _ _
@[simp] lemma «axiomK!» : 𝓢 ⊢! □(φ ==> ψ) ==> □φ ==> □ψ := ⟨axiomK⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomK Γ := ⟨fun _ _ ↦ FiniteContext.of axiomK⟩
instance (Γ : Context F 𝓢) : HasAxiomK Γ := ⟨fun _ _ ↦ Context.of axiomK⟩

/-- Imported declaration from the Incompleteness formalization. -/
def axiomK' (h : 𝓢 ⊢ □(φ ==> ψ)) : 𝓢 ⊢ □φ ==> □ψ := axiomK ⨀ h
@[simp 1100] lemma «axiomK'!» (h : 𝓢 ⊢! □(φ ==> ψ)) : 𝓢 ⊢! □φ ==> □ψ := ⟨axiomK' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def axiomK'' (h₁ : 𝓢 ⊢ □(φ ==> ψ)) (h₂ : 𝓢 ⊢ □φ) : 𝓢 ⊢ □ψ := axiomK' h₁ ⨀ h₂
lemma «axiomK''!» (h₁ : 𝓢 ⊢! □(φ ==> ψ)) (h₂ : 𝓢 ⊢! □φ) : 𝓢 ⊢! □ψ := ⟨axiomK'' h₁.some h₂.some⟩

end «lp_section_6»


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomT (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  T (φ : F) : 𝓢 ⊢ Axioms.T φ

section «lp_section_7»

variable [HasAxiomT 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomT : 𝓢 ⊢ □φ ==> φ := HasAxiomT.T _
@[simp] lemma «axiomT!» : 𝓢 ⊢! □φ ==> φ := ⟨axiomT⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomT Γ := ⟨fun _ ↦ FiniteContext.of axiomT⟩
instance (Γ : Context F 𝓢) : HasAxiomT Γ := ⟨fun _ ↦ Context.of axiomT⟩

/-- Imported declaration from the Incompleteness formalization. -/
def axiomT' (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ φ := axiomT ⨀ h
@[simp] lemma «axiomT'!» (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! φ := ⟨axiomT' h.some⟩

end «lp_section_7»

/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomDiaTc (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  diaTc (φ : F) : 𝓢 ⊢ Axioms.DiaTc φ

section «lp_section_8»

variable [HasAxiomDiaTc 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def diaTc : 𝓢 ⊢ φ ==> ◇φ := HasAxiomDiaTc.diaTc _
@[simp] lemma «diaTc!» : 𝓢 ⊢! φ ==> ◇φ := ⟨diaTc⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomDiaTc Γ := ⟨fun _ ↦ FiniteContext.of diaTc⟩
instance (Γ : Context F 𝓢) : HasAxiomDiaTc Γ := ⟨fun _ ↦ Context.of diaTc⟩

/-- Imported declaration from the Incompleteness formalization. -/
def diaTc' (h : 𝓢 ⊢ φ) : 𝓢 ⊢ ◇φ := diaTc ⨀ h
lemma «diaTc'!» (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ◇φ := ⟨diaTc' h.some⟩

end «lp_section_8»


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomD [Dia F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  D (φ : F) : 𝓢 ⊢ Axioms.D φ

section «lp_section_9»

variable [HasAxiomD 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomD : 𝓢 ⊢ □φ ==> ◇φ := HasAxiomD.D _
@[simp] lemma «axiomD!» : 𝓢 ⊢! □φ ==> ◇φ := ⟨axiomD⟩


variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomD Γ := ⟨fun _ ↦ FiniteContext.of axiomD⟩
instance (Γ : Context F 𝓢) : HasAxiomD Γ := ⟨fun _ ↦ Context.of axiomD⟩

/-- Imported declaration from the Incompleteness formalization. -/
def axiomD' (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ ◇φ := axiomD ⨀ h
lemma «axiomD'!» (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! ◇φ := ⟨axiomD' h.some⟩

end «lp_section_9»



/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomP (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  P : 𝓢 ⊢ Axioms.P

section «lp_section_10»

variable [HasAxiomP 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomP : 𝓢 ⊢ ∼□⊥  := HasAxiomP.P
@[simp] lemma «axiomP!» : 𝓢 ⊢! ∼□⊥ := ⟨axiomP⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomP Γ := ⟨FiniteContext.of axiomP⟩
instance (Γ : Context F 𝓢) : HasAxiomP Γ := ⟨Context.of axiomP⟩

end «lp_section_10»



/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomB [Dia F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  B (φ : F) : 𝓢 ⊢ Axioms.B φ

section «lp_section_11»

variable [HasAxiomB 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomB : 𝓢 ⊢ φ ==> □◇φ := HasAxiomB.B _
@[simp] lemma «axiomB!» : 𝓢 ⊢! φ ==> □◇φ := ⟨axiomB⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomB Γ := ⟨fun _ ↦ FiniteContext.of axiomB⟩
instance (Γ : Context F 𝓢) : HasAxiomB Γ := ⟨fun _ ↦ Context.of axiomB⟩

/-- Imported declaration from the Incompleteness formalization. -/
def axiomB' (h : 𝓢 ⊢ φ) : 𝓢 ⊢ □◇φ := axiomB ⨀ h
@[simp] lemma «axiomB'!» (h : 𝓢 ⊢! φ) : 𝓢 ⊢! □◇φ := ⟨axiomB' h.some⟩

end «lp_section_11»


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomFour (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Four (φ : F) : 𝓢 ⊢ Axioms.Four φ

section «lp_section_12»

variable [HasAxiomFour 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomFour : 𝓢 ⊢ □φ ==> □□φ := HasAxiomFour.Four _
@[simp] lemma «axiomFour!» : 𝓢 ⊢! □φ ==> □□φ := ⟨axiomFour⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomFour Γ := ⟨fun _ ↦ FiniteContext.of axiomFour⟩
instance (Γ : Context F 𝓢) : HasAxiomFour Γ := ⟨fun _ ↦ Context.of axiomFour⟩

/-- Imported declaration from the Incompleteness formalization. -/
def axiomFour' (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ □□φ := axiomFour ⨀ h
/-- Imported declaration from the Incompleteness formalization. -/
lemma «axiomFour'!» (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! □□φ := ⟨axiomFour' h.some⟩

end «lp_section_12»


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomFive [Dia F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Five (φ : F) : 𝓢 ⊢ Axioms.Five φ

section «lp_section_13»

variable [HasAxiomFive 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomFive : 𝓢 ⊢ ◇φ ==> □◇φ := HasAxiomFive.Five _
@[simp] lemma «axiomFive!» : 𝓢 ⊢! ◇φ ==> □◇φ := ⟨axiomFive⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomFive Γ := ⟨fun _ ↦ FiniteContext.of axiomFive⟩
instance (Γ : Context F 𝓢) : HasAxiomFive Γ := ⟨fun _ ↦ Context.of axiomFive⟩

end «lp_section_13»



/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomL (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  L (φ : F) : 𝓢 ⊢ Axioms.L φ

section «lp_section_14»

variable [HasAxiomL 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomL : 𝓢 ⊢ □(□φ ==> φ) ==> □φ := HasAxiomL.L _
@[simp] lemma «axiomL!» : 𝓢 ⊢! □(□φ ==> φ) ==> □φ := ⟨axiomL⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomL Γ := ⟨fun _ ↦ FiniteContext.of axiomL⟩
instance (Γ : Context F 𝓢) : HasAxiomL Γ := ⟨fun _ ↦ Context.of axiomL⟩

end «lp_section_14»

/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomDot2 [Dia F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Dot2 (φ : F) : 𝓢 ⊢ Axioms.Dot2 φ

section «lp_section_15»

variable [HasAxiomDot2 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomDot2 : 𝓢 ⊢ ◇□φ ==> □◇φ := HasAxiomDot2.Dot2 _
@[simp] lemma «axiomDot2!» : 𝓢 ⊢! ◇□φ ==> □◇φ := ⟨axiomDot2⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomDot2 Γ := ⟨fun _ ↦ FiniteContext.of axiomDot2⟩
instance (Γ : Context F 𝓢) : HasAxiomDot2 Γ := ⟨fun _ ↦ Context.of axiomDot2⟩

end «lp_section_15»


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomDot3 (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Dot3 (φ ψ : F) : 𝓢 ⊢ Axioms.Dot3 φ ψ

section «lp_section_16»

variable [HasAxiomDot3 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomDot3 : 𝓢 ⊢ □(□φ ==> ψ) ⋎ □(□ψ ==> φ) := HasAxiomDot3.Dot3 _ _
@[simp] lemma «axiomDot3!» : 𝓢 ⊢! □(□φ ==> ψ) ⋎ □(□ψ ==> φ) := ⟨axiomDot3⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomDot3 Γ := ⟨fun _ _ ↦ FiniteContext.of axiomDot3⟩
instance (Γ : Context F 𝓢) : HasAxiomDot3 Γ := ⟨fun _ _ ↦ Context.of axiomDot3⟩

end «lp_section_16»


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomGrz (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Grz (φ : F) : 𝓢 ⊢ Axioms.Grz φ

section «lp_section_17»

variable [HasAxiomGrz 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomGrz : 𝓢 ⊢ □(□(φ ==> □φ) ==> φ) ==> φ := HasAxiomGrz.Grz _
@[simp] lemma «axiomGrz!» : 𝓢 ⊢! □(□(φ ==> □φ) ==> φ) ==> φ := ⟨axiomGrz⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomGrz Γ := ⟨fun _ ↦ FiniteContext.of axiomGrz⟩
instance (Γ : Context F 𝓢) : HasAxiomGrz Γ := ⟨fun _ ↦ Context.of axiomGrz⟩

end «lp_section_17»


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomTc (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Tc (φ : F) : 𝓢 ⊢ Axioms.Tc φ

section «lp_section_18»

variable [HasAxiomTc 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomTc : 𝓢 ⊢ φ ==> □φ := HasAxiomTc.Tc _
@[simp] lemma «axiomTc!» : 𝓢 ⊢! φ ==> □φ := ⟨axiomTc⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomTc Γ := ⟨fun _ ↦ FiniteContext.of axiomTc⟩
instance (Γ : Context F 𝓢) : HasAxiomTc Γ := ⟨fun _ ↦ Context.of axiomTc⟩

end «lp_section_18»


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomDiaT (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  diaT (φ : F) : 𝓢 ⊢ Axioms.DiaT φ

section «lp_section_19»

variable [HasAxiomDiaT 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def diaT : 𝓢 ⊢ ◇φ ==> φ := HasAxiomDiaT.diaT _
@[simp] lemma «diaT!» : 𝓢 ⊢! ◇φ ==> φ := ⟨diaT⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomDiaT Γ := ⟨fun _ ↦ FiniteContext.of diaT⟩
instance (Γ : Context F 𝓢) : HasAxiomDiaT Γ := ⟨fun _ ↦ Context.of diaT⟩

/-- Imported declaration from the Incompleteness formalization. -/
def diaT' (h : 𝓢 ⊢ ◇φ) : 𝓢 ⊢ φ := diaT ⨀ h
lemma «diaT'!» (h : 𝓢 ⊢! ◇φ) : 𝓢 ⊢! φ := ⟨diaT' h.some⟩

end «lp_section_19»


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomVer (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Ver (φ : F) : 𝓢 ⊢ Axioms.Ver φ

section «lp_section_20»

variable [HasAxiomVer 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomVer : 𝓢 ⊢ □φ := HasAxiomVer.Ver _
@[simp] lemma «axiomVer!» : 𝓢 ⊢! □φ := ⟨axiomVer⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomVer Γ := ⟨fun _ ↦ FiniteContext.of axiomVer⟩
instance (Γ : Context F 𝓢) : HasAxiomVer Γ := ⟨fun _ ↦ Context.of axiomVer⟩

end «lp_section_20»



/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomH (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  H (φ : F) : 𝓢 ⊢ Axioms.H φ

section «lp_section_21»

variable [HasAxiomH 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomH : 𝓢 ⊢ □(□φ <=> φ) ==> □φ := HasAxiomH.H _
@[simp] lemma «axiomH!» : 𝓢 ⊢! □(□φ <=> φ) ==> □φ := ⟨axiomH⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomH Γ := ⟨fun _ ↦ FiniteContext.of axiomH⟩
instance (Γ : Context F 𝓢) : HasAxiomH Γ := ⟨fun _ ↦ Context.of axiomH⟩

end «lp_section_21»


section «lp_section_22»

variable [DecidableEq F]
variable {φ ψ χ : F} {Γ Δ : List F}
variable {𝓢 : S}

instance [Entailment.Minimal 𝓢] [ModalDeMorgan F] : HasDiaDuality 𝓢 := ⟨by
  intro φ;
  simp only [Axioms.DiaDuality, ModalDeMorgan.box, DeMorgan.neg];
  apply iffId;
⟩

instance [Entailment.Minimal 𝓢] [DiaAbbrev F] : HasDiaDuality 𝓢 := ⟨by
  intro φ;
  simp only [Axioms.DiaDuality, DiaAbbrev.dia_abbrev];
  apply iffId;
⟩

instance [ModusPonens 𝓢] [HasAxiomT 𝓢] : Unnecessitation 𝓢 := ⟨by
  intro φ hp;
  exact axiomT ⨀ hp;
⟩

end «lp_section_22»


section «lp_section_23»

variable (𝓢 : S)

/-- Imported declaration from the Incompleteness formalization. -/
protected class K extends Entailment.Classical 𝓢, Necessitation 𝓢, HasAxiomK 𝓢, HasDiaDuality 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class KD extends Entailment.K 𝓢, HasAxiomD 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class KP extends Entailment.K 𝓢, HasAxiomP 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class KB extends Entailment.K 𝓢, HasAxiomB 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class KT extends Entailment.K 𝓢, HasAxiomT 𝓢
/-- Imported declaration from the Incompleteness formalization. -/
protected class KT' extends Entailment.K 𝓢, HasAxiomDiaTc 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class KTc extends Entailment.K 𝓢, HasAxiomTc 𝓢
/-- Imported declaration from the Incompleteness formalization. -/
protected class KTc' extends Entailment.K 𝓢, HasAxiomDiaT 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class KTB extends Entailment.K 𝓢, HasAxiomT 𝓢, HasAxiomB 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class KD45 extends Entailment.K 𝓢, HasAxiomD 𝓢, HasAxiomFour 𝓢, HasAxiomFive 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class KB4 extends Entailment.K 𝓢, HasAxiomB 𝓢, HasAxiomFour 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class KB5 extends Entailment.K 𝓢, HasAxiomB 𝓢, HasAxiomFive 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class KDB extends Entailment.K 𝓢, HasAxiomD 𝓢, HasAxiomB 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class KD4 extends Entailment.K 𝓢, HasAxiomD 𝓢, HasAxiomFour 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class KD5 extends Entailment.K 𝓢, HasAxiomD 𝓢, HasAxiomFive 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class K45 extends Entailment.K 𝓢, HasAxiomFour 𝓢, HasAxiomFive 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class Triv extends Entailment.K 𝓢, HasAxiomT 𝓢, HasAxiomTc 𝓢
instance [Entailment.Triv 𝓢] : Entailment.KT 𝓢 where
instance [Entailment.Triv 𝓢] : Entailment.KTc 𝓢 where

/-- Imported declaration from the Incompleteness formalization. -/
protected class Ver extends Entailment.K 𝓢, HasAxiomVer 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class K4 extends Entailment.K 𝓢, HasAxiomFour 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class K5 extends Entailment.K 𝓢, HasAxiomFive 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class S4 extends Entailment.K 𝓢, HasAxiomT 𝓢, HasAxiomFour 𝓢
instance [Entailment.S4 𝓢] : Entailment.K4 𝓢 where
instance [Entailment.S4 𝓢] : Entailment.KT 𝓢 where

/-- Imported declaration from the Incompleteness formalization. -/
protected class S4Dot2 extends Entailment.S4 𝓢, HasAxiomDot2 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class S4Dot3 extends Entailment.S4 𝓢, HasAxiomDot3 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class S5 extends Entailment.K 𝓢, HasAxiomT 𝓢, HasAxiomFive 𝓢
instance [Entailment.S5 𝓢] : Entailment.KT 𝓢 where
instance [Entailment.S5 𝓢] : Entailment.K5 𝓢 where

/-- Imported declaration from the Incompleteness formalization. -/
protected class GL extends Entailment.K 𝓢, HasAxiomL 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class Grz extends Entailment.K 𝓢, HasAxiomGrz 𝓢

end «lp_section_23»


section «lp_section_24»

/-- Imported declaration from the Incompleteness formalization. -/
class ModalDisjunctive (𝓢 : S) : Prop where
  modal_disjunctive : ∀ {φ ψ : F}, 𝓢 ⊢! □φ ⋎ □ψ → 𝓢 ⊢! φ ∨ 𝓢 ⊢! ψ

alias modal_disjunctive := ModalDisjunctive.modal_disjunctive

variable {𝓢 : S} [Entailment.Minimal 𝓢]

instance [Disjunctive 𝓢] [Unnecessitation 𝓢] : ModalDisjunctive 𝓢 where
  modal_disjunctive h := by
    rcases disjunctive h with (h | h);
    · left; exact unnec! h;
    · right; exact unnec! h;

private lemma unnec_of_mdp_aux [ModalDisjunctive 𝓢] (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! φ := by
    have : 𝓢 ⊢! □φ ⋎ □φ := or₁'! h;
    rcases modal_disjunctive this with (h | h) <;> tauto;

noncomputable instance unnecessitationOfModalDisjunctive [ModalDisjunctive 𝓢] :
    Unnecessitation 𝓢 where
  unnec h := (unnec_of_mdp_aux ⟨h⟩).some

end «lp_section_24»

end Entailment
end LO
