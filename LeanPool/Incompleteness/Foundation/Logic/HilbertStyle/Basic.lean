/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Logic.Entailment
import LeanPool.Incompleteness.Foundation.Logic.Axioms

/-! # Basic -/


namespace LO
namespace Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment F S]
variable {𝓢 : S} {φ ψ χ : F}


/-- Imported declaration from the Incompleteness formalization. -/
def cast (e : φ = ψ) (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ := e ▸ b
omit [LogicalConnective F] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma «cast!» (e : φ = ψ) (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ := ⟨cast e b.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
class ModusPonens (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  mdp {φ ψ : F} : 𝓢 ⊢ φ ==> ψ → 𝓢 ⊢ φ → 𝓢 ⊢ ψ

alias mdp := ModusPonens.mdp
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀" => mdp

lemma «mdp!» [ModusPonens 𝓢] : 𝓢 ⊢! φ ==> ψ → 𝓢 ⊢! φ → 𝓢 ⊢! ψ := by
  rintro ⟨hpq⟩ ⟨hp⟩;
  exact ⟨hpq ⨀ hp⟩
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀" => mdp!

/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomVerum (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  verum : 𝓢 ⊢ Axioms.Verum

/-- Imported declaration from the Incompleteness formalization. -/
def verum [HasAxiomVerum 𝓢] : 𝓢 ⊢ ⊤ := HasAxiomVerum.verum
@[simp] lemma «verum!» [HasAxiomVerum 𝓢] : 𝓢 ⊢! ⊤ := ⟨verum⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomImply₁ (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  imply₁ (φ ψ : F) : 𝓢 ⊢ Axioms.Imply₁ φ ψ

/-- Imported declaration from the Incompleteness formalization. -/
def imply₁ [HasAxiomImply₁ 𝓢] : 𝓢 ⊢ φ ==> ψ ==> φ := HasAxiomImply₁.imply₁ _ _
@[simp] lemma «imply₁!» [HasAxiomImply₁ 𝓢] : 𝓢 ⊢! φ ==> ψ ==> φ := ⟨imply₁⟩

/-- Imported declaration from the Incompleteness formalization. -/
def imply₁' [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (h : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ ==> φ := imply₁ ⨀ h
lemma «imply₁'!» [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (d : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ ==> φ := ⟨imply₁' d.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
@[deprecated imply₁' (since := "2026-05-27")]
def dhyp [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (ψ : F) (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ ==> φ := imply₁' b


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomImply₂ (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  imply₂ (φ ψ χ : F) : 𝓢 ⊢ Axioms.Imply₂ φ ψ χ

/-- Imported declaration from the Incompleteness formalization. -/
def imply₂ [HasAxiomImply₂ 𝓢] : 𝓢 ⊢ (φ ==> ψ ==> χ) ==> (φ ==> ψ) ==> φ ==> χ :=
  HasAxiomImply₂.imply₂ _ _ _
@[simp] lemma «imply₂!» [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! (φ ==> ψ ==> χ) ==> (φ ==> ψ) ==> φ ==> χ :=
  ⟨imply₂⟩

/-- Imported declaration from the Incompleteness formalization. -/
def imply₂' [ModusPonens 𝓢] [HasAxiomImply₂ 𝓢] (d₁ : 𝓢 ⊢ φ ==> ψ ==> χ) (d₂ : 𝓢 ⊢ φ ==> ψ) (d₃ :
    𝓢 ⊢ φ) : 𝓢 ⊢ χ :=
  imply₂ ⨀ d₁ ⨀ d₂ ⨀ d₃
lemma «imply₂'!»
    [ModusPonens 𝓢] [HasAxiomImply₂ 𝓢] (d₁ : 𝓢 ⊢! φ ==> ψ ==> χ) (d₂ : 𝓢 ⊢! φ ==> ψ) (d₃ : 𝓢 ⊢! φ) :
    𝓢 ⊢! χ :=
  ⟨imply₂' d₁.some d₂.some d₃.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomAndElim (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  and₁ (φ ψ : F) : 𝓢 ⊢ Axioms.AndElim₁ φ ψ
  /-- Imported declaration from the Incompleteness formalization. -/
  and₂ (φ ψ : F) : 𝓢 ⊢ Axioms.AndElim₂ φ ψ

/-- Imported declaration from the Incompleteness formalization. -/
def and₁ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ==> φ := HasAxiomAndElim.and₁ _ _
@[simp] lemma «and₁!» [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⋏ ψ ==> φ := ⟨and₁⟩

/-- Imported declaration from the Incompleteness formalization. -/
def and₁' [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ φ := and₁ ⨀ d
alias andLeft := and₁'

lemma «and₁'!» [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! (φ ⋏ ψ)) : 𝓢 ⊢! φ := ⟨and₁' d.some⟩
alias and_left! := and₁'!

/-- Imported declaration from the Incompleteness formalization. -/
def and₂ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ==> ψ := HasAxiomAndElim.and₂ _ _
@[simp] lemma «and₂!» [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⋏ ψ ==> ψ := ⟨and₂⟩

/-- Imported declaration from the Incompleteness formalization. -/
def and₂' [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ := and₂ ⨀ d
alias andRight := and₂'

lemma «and₂'!»  [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! (φ ⋏ ψ)) : 𝓢 ⊢! ψ := ⟨and₂' d.some⟩
alias and_right! := and₂'!


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomAndInst (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  and₃ (φ ψ : F) : 𝓢 ⊢ Axioms.AndInst φ ψ

/-- Imported declaration from the Incompleteness formalization. -/
def and₃ [HasAxiomAndInst 𝓢] : 𝓢 ⊢ φ ==> ψ ==> φ ⋏ ψ := HasAxiomAndInst.and₃ _ _
@[simp] lemma «and₃!» [HasAxiomAndInst 𝓢] : 𝓢 ⊢! φ ==> ψ ==> φ ⋏ ψ := ⟨and₃⟩

/-- Imported declaration from the Incompleteness formalization. -/
def and₃' [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢ φ) (d₂ : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋏ ψ :=
  and₃ ⨀ d₁ ⨀ d₂
alias andIntro := and₃'

lemma «and₃'!»  [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢! φ) (d₂ : 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋏ ψ :=
  ⟨and₃' d₁.some d₂.some⟩
alias and_intro! := and₃'!


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomOrInst (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  or₁ (φ ψ : F) : 𝓢 ⊢ Axioms.OrInst₁ φ ψ
  /-- Imported declaration from the Incompleteness formalization. -/
  or₂ (φ ψ : F) : 𝓢 ⊢ Axioms.OrInst₂ φ ψ

/-- Imported declaration from the Incompleteness formalization. -/
def or₁ [HasAxiomOrInst 𝓢] : 𝓢 ⊢ φ ==> φ ⋎ ψ := HasAxiomOrInst.or₁ _ _
@[simp] lemma «or₁!» [HasAxiomOrInst 𝓢] : 𝓢 ⊢! φ ==> φ ⋎ ψ := ⟨or₁⟩

/-- Imported declaration from the Incompleteness formalization. -/
def or₁' [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ φ) : 𝓢 ⊢ φ ⋎ ψ := or₁ ⨀ d
lemma «or₁'!» [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! φ) : 𝓢 ⊢! φ ⋎ ψ := ⟨or₁' d.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def or₂ [HasAxiomOrInst 𝓢] : 𝓢 ⊢ ψ ==> φ ⋎ ψ := HasAxiomOrInst.or₂ _ _
@[simp] lemma «or₂!» [HasAxiomOrInst 𝓢] : 𝓢 ⊢! ψ ==> φ ⋎ ψ := ⟨or₂⟩

/-- Imported declaration from the Incompleteness formalization. -/
def or₂' [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋎ ψ := or₂ ⨀ d
lemma «or₂'!» [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋎ ψ := ⟨or₂' d.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomOrElim (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  or₃ (φ ψ χ : F) : 𝓢 ⊢ Axioms.OrElim φ ψ χ

/-- Imported declaration from the Incompleteness formalization. -/
def or₃ [HasAxiomOrElim 𝓢] : 𝓢 ⊢ (φ ==> χ) ==> (ψ ==> χ) ==> (φ ⋎ ψ) ==> χ :=
  HasAxiomOrElim.or₃ _ _ _
@[simp] lemma «or₃!» [HasAxiomOrElim 𝓢] : 𝓢 ⊢! (φ ==> χ) ==> (ψ ==> χ) ==> (φ ⋎ ψ) ==> χ := ⟨or₃⟩

/-- Imported declaration from the Incompleteness formalization. -/
def or₃'' [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ==> χ) (d₂ : 𝓢 ⊢ ψ ==> χ) :
    𝓢 ⊢ φ ⋎ ψ ==> χ :=
  or₃ ⨀ d₁ ⨀ d₂
lemma «or₃''!» [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ==> χ) (d₂ : 𝓢 ⊢! ψ ==> χ) :
    𝓢 ⊢! φ ⋎ ψ ==> χ :=
  ⟨or₃'' d₁.some d₂.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def or₃''' [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ==> χ) (d₂ : 𝓢 ⊢ ψ ==> χ) (d₃ :
    𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ χ :=
  or₃ ⨀ d₁ ⨀ d₂ ⨀ d₃
alias orCases := or₃'''

lemma «or₃'''!» [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ==> χ) (d₂ : 𝓢 ⊢! ψ ==> χ) (d₃ :
    𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! χ :=
  ⟨or₃''' d₁.some d₂.some d₃.some⟩
alias or_cases! := or₃'''!


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomEFQ (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  efq (φ : F) : 𝓢 ⊢ Axioms.EFQ φ

/-- Imported declaration from the Incompleteness formalization. -/
def efq [HasAxiomEFQ 𝓢] : 𝓢 ⊢ ⊥ ==> φ := HasAxiomEFQ.efq _
@[simp] lemma «efq!» [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⊥ ==> φ := ⟨efq⟩

/-- Imported declaration from the Incompleteness formalization. -/
def efq' [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢ ⊥) : 𝓢 ⊢ φ := efq ⨀ b
lemma «efq'!» [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! ⊥) : 𝓢 ⊢! φ := ⟨efq' h.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomLEM (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  lem (φ : F) : 𝓢 ⊢ Axioms.LEM φ

/-- Imported declaration from the Incompleteness formalization. -/
def lem [HasAxiomLEM 𝓢] : 𝓢 ⊢ φ ⋎ ∼φ := HasAxiomLEM.lem φ
@[simp] lemma «lem!» [HasAxiomLEM 𝓢] : 𝓢 ⊢! φ ⋎ ∼φ := ⟨lem⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomDNE (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  dne (φ : F) : 𝓢 ⊢ Axioms.DNE φ

/-- Imported declaration from the Incompleteness formalization. -/
def dne [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼∼φ ==> φ := HasAxiomDNE.dne _
@[simp] lemma «dne!» [HasAxiomDNE 𝓢] : 𝓢 ⊢! ∼∼φ ==> φ := ⟨dne⟩

/-- Imported declaration from the Incompleteness formalization. -/
def dne' [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼∼φ) : 𝓢 ⊢ φ := dne ⨀ b
lemma «dne'!» [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (h : 𝓢 ⊢! ∼∼φ) : 𝓢 ⊢! φ := ⟨dne' h.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomWeakLEM (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  wlem (φ : F) : 𝓢 ⊢ Axioms.WeakLEM φ

/-- Imported declaration from the Incompleteness formalization. -/
def wlem [HasAxiomWeakLEM 𝓢] : 𝓢 ⊢ ∼φ ⋎ ∼∼φ := HasAxiomWeakLEM.wlem φ
@[simp] lemma «wlem!» [HasAxiomWeakLEM 𝓢] : 𝓢 ⊢! ∼φ ⋎ ∼∼φ := ⟨wlem⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomDummett (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  dummett (φ ψ : F) : 𝓢 ⊢ Axioms.Dummett φ ψ

/-- Imported declaration from the Incompleteness formalization. -/
def dummett [HasAxiomDummett 𝓢] : 𝓢 ⊢ (φ ==> ψ) ⋎ (ψ ==> φ) := HasAxiomDummett.dummett φ ψ
@[simp] lemma «dummett!» [HasAxiomDummett 𝓢] : 𝓢 ⊢! Axioms.Dummett φ ψ := ⟨dummett⟩


/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomPeirce (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  peirce (φ ψ : F) : 𝓢 ⊢ Axioms.Peirce φ ψ

/-- Imported declaration from the Incompleteness formalization. -/
def peirce [HasAxiomPeirce 𝓢] : 𝓢 ⊢ ((φ ==> ψ) ==> φ) ==> φ := HasAxiomPeirce.peirce _ _
@[simp] lemma «peirce!» [HasAxiomPeirce 𝓢] : 𝓢 ⊢! ((φ ==> ψ) ==> φ) ==> φ := ⟨peirce⟩


/-- Negation `∼φ` is equivalent to `φ ==> ⊥` on **system**.

This is weaker asssumption than _"introducing `∼φ` as an abbreviation of `φ ==> ⊥`" (`NegAbbrev`)_.
-/
class NegationEquiv (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  negEquiv (φ : F) : 𝓢 ⊢ Axioms.NegEquiv φ

/-- Imported declaration from the Incompleteness formalization. -/
def negEquiv [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ <=> (φ ==> ⊥) := NegationEquiv.negEquiv _
@[simp] lemma «negEquiv!» [NegationEquiv 𝓢] : 𝓢 ⊢! ∼φ <=> (φ ==> ⊥) := ⟨negEquiv⟩

/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomElimContra (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  elimContra (φ ψ : F) : 𝓢 ⊢ Axioms.ElimContra φ ψ

/-- Imported declaration from the Incompleteness formalization. -/
def elimContra [HasAxiomElimContra 𝓢] : 𝓢 ⊢ ((∼ψ) ==> (∼φ)) ==> (φ ==> ψ) :=
  HasAxiomElimContra.elimContra _ _
@[simp] lemma «elimContra!» [HasAxiomElimContra 𝓢] : 𝓢 ⊢! (∼ψ ==> ∼φ) ==> (φ ==> ψ)  := ⟨elimContra⟩

/-- Imported declaration from the Incompleteness formalization. -/
protected class Minimal (𝓢 : S) extends
              ModusPonens 𝓢,
              NegationEquiv 𝓢,
              HasAxiomVerum 𝓢,
              HasAxiomImply₁ 𝓢, HasAxiomImply₂ 𝓢,
              HasAxiomAndElim 𝓢, HasAxiomAndInst 𝓢,
              HasAxiomOrInst 𝓢, HasAxiomOrElim 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class Intuitionistic (𝓢 : S) extends Entailment.Minimal 𝓢, HasAxiomEFQ 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
protected class Classical (𝓢 : S) extends Entailment.Minimal 𝓢, HasAxiomDNE 𝓢


section «lp_section_1»

variable [ModusPonens 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.negEquiv'.mp [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] :
    𝓢 ⊢ ∼φ → 𝓢 ⊢ φ ==> ⊥ :=
  fun h => (and₁' negEquiv) ⨀ h
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.negEquiv'.mpr [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] :
    𝓢 ⊢ φ ==> ⊥ → 𝓢 ⊢ ∼φ :=
  fun h => (and₂' negEquiv) ⨀ h
lemma «negEquiv'!» [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢! ∼φ ↔ 𝓢 ⊢! φ ==> ⊥ :=
  ⟨fun ⟨h⟩ => ⟨negEquiv'.mp h⟩, fun ⟨h⟩ => ⟨negEquiv'.mpr h⟩⟩

/-- Imported declaration from the Incompleteness formalization. -/
def iffIntro [HasAxiomAndInst 𝓢] (b₁ : 𝓢 ⊢ φ ==> ψ) (b₂ : 𝓢 ⊢ ψ ==> φ) : 𝓢 ⊢ φ <=> ψ :=
  andIntro b₁ b₂
/-- Imported declaration from the Incompleteness formalization. -/
lemma «iff_intro!» [HasAxiomAndInst 𝓢] (h₁ : 𝓢 ⊢! φ ==> ψ) (h₂ : 𝓢 ⊢! ψ ==> φ) : 𝓢 ⊢! φ <=> ψ :=
  ⟨andIntro h₁.some h₂.some⟩

lemma and_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! φ ⋏ ψ ↔ 𝓢 ⊢! φ ∧ 𝓢 ⊢! ψ :=
  ⟨fun h ↦ ⟨and_left! h, and_right! h⟩, fun h ↦ and_intro! h.1 h.2⟩

lemma iff_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] :
    𝓢 ⊢! φ <=> ψ ↔ 𝓢 ⊢! φ ==> ψ ∧ 𝓢 ⊢! ψ ==> φ :=
  ⟨fun h ↦ ⟨and_left! h, and_right! h⟩, fun h ↦ and_intro! h.1 h.2⟩

lemma provable_iff_of_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢! φ <=> ψ) :
    𝓢 ⊢! φ ↔ 𝓢 ⊢! ψ :=
  ⟨fun hp ↦ and_left! h ⨀ hp, fun hq ↦ and_right! h ⨀ hq⟩

/-- Imported declaration from the Incompleteness formalization. -/
def impId [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ : F) : 𝓢 ⊢ φ ==> φ :=
  imply₂ (φ := φ) (ψ := (φ ==> φ)) (χ := φ) ⨀ imply₁ ⨀ imply₁
/-- Imported declaration from the Incompleteness formalization. -/
@[simp] lemma «imp_id!» [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! φ ==> φ := ⟨impId φ⟩

/-- Imported declaration from the Incompleteness formalization. -/
def iffId [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ : F) : 𝓢 ⊢ φ <=> φ :=
  and₃' (impId φ) (impId φ)
/-- Imported declaration from the Incompleteness formalization. -/
@[simp] lemma «iff_id!» [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : 𝓢 ⊢! φ <=> φ :=
  ⟨iffId φ⟩

instance [NegAbbrev F] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [HasAxiomAndInst 𝓢] :
    Entailment.NegationEquiv 𝓢 where
  negEquiv := by
    intro φ
    simpa only [Axioms.NegEquiv, NegAbbrev.neg] using iffId _


/-- Imported declaration from the Incompleteness formalization. -/
def notbot [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ ∼⊥ :=
  negEquiv'.mpr (impId ⊥)
@[simp] lemma «notbot!»
    [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢! ∼⊥ :=
  ⟨notbot⟩

/-- Imported declaration from the Incompleteness formalization. -/
def mdp₁ [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ==> ψ ==> χ) (bq : 𝓢 ⊢ φ ==> ψ) : 𝓢 ⊢ φ ==> χ :=
  imply₂ ⨀ bqr ⨀ bq
lemma «mdp₁!» [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ==> ψ ==> χ) (hq : 𝓢 ⊢! φ ==> ψ) : 𝓢 ⊢! φ ==> χ :=
  ⟨mdp₁ hqr.some hq.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₁" => mdp₁
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₁" => mdp₁!

/-- Imported declaration from the Incompleteness formalization. -/
def mdp₂ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ==> ψ ==> χ ==> s) (bq :
    𝓢 ⊢ φ ==> ψ ==> χ) : 𝓢 ⊢ φ ==> ψ ==> s :=
  imply₁' (imply₂) ⨀₁ bqr ⨀₁ bq
lemma «mdp₂!» [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ==> ψ ==> χ ==> s) (hq :
    𝓢 ⊢! φ ==> ψ ==> χ) : 𝓢 ⊢! φ ==> ψ ==> s :=
  ⟨mdp₂ hqr.some hq.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₂" => mdp₂
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₂" => mdp₂!

/-- Imported declaration from the Incompleteness formalization. -/
def mdp₃ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ==> ψ ==> χ ==> s ==> t) (bq :
    𝓢 ⊢ φ ==> ψ ==> χ ==> s) : 𝓢 ⊢ φ ==> ψ ==> χ ==> t :=
  (imply₁' <| imply₁' <| imply₂) ⨀₂ bqr ⨀₂ bq
lemma «mdp₃!» [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ==> ψ ==> χ ==> s ==> t) (hq :
    𝓢 ⊢! φ ==> ψ ==> χ ==> s) : 𝓢 ⊢! φ ==> ψ ==> χ ==> t :=
  ⟨mdp₃ hqr.some hq.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₃" => mdp₃
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₃" => mdp₃!

/-- Imported declaration from the Incompleteness formalization. -/
def mdp₄ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bqr : 𝓢 ⊢ φ ==> ψ ==> χ ==> s ==> t ==> u) (bq :
    𝓢 ⊢ φ ==> ψ ==> χ ==> s ==> t) : 𝓢 ⊢ φ ==> ψ ==> χ ==> s ==> u :=
  (imply₁' <| imply₁' <| imply₁' <| imply₂) ⨀₃ bqr ⨀₃ bq
lemma «mdp₄!»
    [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hqr : 𝓢 ⊢! φ ==> ψ ==> χ ==> s ==> t ==> u) (hq :
    𝓢 ⊢! φ ==> ψ ==> χ ==> s ==> t) : 𝓢 ⊢! φ ==> ψ ==> χ ==> s ==> u :=
  ⟨mdp₄ hqr.some hq.some⟩
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₄" => mdp₄
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₄" => mdp₄!

/-- Imported declaration from the Incompleteness formalization. -/
def impTrans'' [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bpq : 𝓢 ⊢ φ ==> ψ) (bqr : 𝓢 ⊢ ψ ==> χ) :
    𝓢 ⊢ φ ==> χ :=
  imply₂ ⨀ imply₁' bqr ⨀ bpq
lemma «imp_trans''!» [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hpq : 𝓢 ⊢! φ ==> ψ) (hqr :
    𝓢 ⊢! ψ ==> χ) : 𝓢 ⊢! φ ==> χ :=
  ⟨impTrans'' hpq.some hqr.some⟩

lemma «unprovable_imp_trans''!» [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hpq : 𝓢 ⊢! φ ==> ψ) :
    𝓢 ⊬ φ ==> χ → 𝓢 ⊬ ψ ==> χ := by
  intro hp hq
  exact hp (imp_trans''! hpq hq)

/-- Imported declaration from the Incompleteness formalization. -/
def iffTrans''
    [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (h₁ : 𝓢 ⊢ φ <=> ψ) (h₂ : 𝓢 ⊢ ψ <=> χ) : 𝓢 ⊢ φ <=> χ :=
  iffIntro (impTrans'' (and₁' h₁) (and₁' h₂)) (impTrans'' (and₂' h₂) (and₂' h₁))
lemma «iff_trans''!»
    [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (h₁ : 𝓢 ⊢! φ <=> ψ) (h₂ : 𝓢 ⊢! ψ <=> χ) : 𝓢 ⊢! φ <=> χ :=
  ⟨iffTrans'' h₁.some h₂.some⟩

lemma «unprovable_iff!»
    [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (H :
    𝓢 ⊢! φ <=> ψ) : 𝓢 ⊬ φ ↔ 𝓢 ⊬ ψ := by
  constructor;
  · intro hp hq; have := and₂'! H ⨀ hq; contradiction;
  · intro hq hp; have := and₁'! H ⨀ hp; contradiction;

/-- Imported declaration from the Incompleteness formalization. -/
def imply₁₁ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) : 𝓢 ⊢ φ ==> ψ ==> χ ==> φ :=
  impTrans'' imply₁ imply₁
@[simp] lemma «imply₁₁!» [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) :
    𝓢 ⊢! φ ==> ψ ==> χ ==> φ :=
  ⟨imply₁₁ φ ψ χ⟩

/-- Imported declaration from the Incompleteness formalization. -/
def implyAnd [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bq : 𝓢 ⊢ φ ==> ψ) (br :
    𝓢 ⊢ φ ==> χ) : 𝓢 ⊢ φ ==> ψ ⋏ χ :=
  imply₁' and₃ ⨀₁ bq ⨀₁ br
lemma «imply_and!»
    [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hq : 𝓢 ⊢! φ ==> ψ) (hr :
    𝓢 ⊢! φ ==> χ) : 𝓢 ⊢! φ ==> ψ ⋏ χ :=
  ⟨implyAnd hq.some hr.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def andComm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ :
    F) : 𝓢 ⊢ φ ⋏ ψ ==> ψ ⋏ φ :=
  implyAnd and₂ and₁
lemma «and_comm!» [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] :
    𝓢 ⊢! φ ⋏ ψ ==> ψ ⋏ φ :=
  ⟨andComm φ ψ⟩

/-- Imported declaration from the Incompleteness formalization. -/
def andComm' [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h :
    𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ ⋏ φ :=
  andComm _ _ ⨀ h
lemma «and_comm'!»
    [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h : 𝓢 ⊢! φ ⋏ ψ) :
    𝓢 ⊢! ψ ⋏ φ :=
  ⟨andComm' h.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def iffComm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ :
    F) : 𝓢 ⊢ (φ <=> ψ) ==> (ψ <=> φ) :=
  andComm _ _
lemma «iff_comm!»  [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] :
    𝓢 ⊢! (φ <=> ψ) ==> (ψ <=> φ) :=
  ⟨iffComm φ ψ⟩

/-- Imported declaration from the Incompleteness formalization. -/
def iffComm' [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h :
    𝓢 ⊢ φ <=> ψ) : 𝓢 ⊢ ψ <=> φ :=
  iffComm _ _ ⨀ h
lemma «iff_comm'!»
    [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (h :
    𝓢 ⊢! φ <=> ψ) : 𝓢 ⊢! ψ <=> φ :=
  ⟨iffComm' h.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def andImplyIffImplyImply
    [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) :
    𝓢 ⊢ (φ ⋏ ψ ==> χ) <=> (φ ==> ψ ==> χ) := by
  let b₁ : 𝓢 ⊢ (φ ⋏ ψ ==> χ) ==> φ ==> ψ ==> χ :=
    imply₁₁ (φ ⋏ ψ ==> χ) φ ψ ⨀₃ imply₁' (ψ := φ ⋏ ψ ==> χ) and₃
  let b₂ : 𝓢 ⊢ (φ ==> ψ ==> χ) ==> φ ⋏ ψ ==> χ :=
    imply₁ ⨀₂ (imply₁' (ψ := φ ==> ψ ==> χ) and₁) ⨀₂ (imply₁' (ψ := φ ==> ψ ==> χ) and₂);
  exact iffIntro b₁ b₂
lemma «and_imply_iff_imply_imply!»
    [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] :
    𝓢 ⊢! (φ ⋏ ψ ==> χ) <=> (φ ==> ψ ==> χ) :=
  ⟨andImplyIffImplyImply φ ψ χ⟩

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.andImplyIffImplyImply'.mp
    [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (d :
    𝓢 ⊢ φ ⋏ ψ ==> χ) : 𝓢 ⊢ φ ==> ψ ==> χ :=
  (and₁' <| andImplyIffImplyImply φ ψ χ) ⨀ d
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.andImplyIffImplyImply'.mpr
    [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (d :
    𝓢 ⊢ φ ==> ψ ==> χ) : 𝓢 ⊢ φ ⋏ ψ ==> χ :=
  (and₂' <| andImplyIffImplyImply φ ψ χ) ⨀ d

lemma «and_imply_iff_imply_imply'!»
    [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]: (𝓢 ⊢! φ ⋏ ψ ==>
        χ) ↔ (𝓢 ⊢! φ ==> ψ ==> χ) :=
  ⟨fun ⟨h⟩ => ⟨andImplyIffImplyImply'.mp h⟩, fun ⟨h⟩ => ⟨andImplyIffImplyImply'.mpr h⟩⟩

/-- Imported declaration from the Incompleteness formalization. -/
def implyLeftVerum [HasAxiomVerum 𝓢] [HasAxiomImply₁ 𝓢] : 𝓢 ⊢ φ ==> ⊤ := imply₁' verum
@[simp] lemma «implyLeftVerum!» [HasAxiomImply₁ 𝓢] [HasAxiomVerum 𝓢] : 𝓢 ⊢! φ ==> ⊤ :=
  ⟨implyLeftVerum⟩



instance [(𝓢 : S) → ModusPonens 𝓢] [(𝓢 : S) → HasAxiomEFQ 𝓢] : DeductiveExplosion S :=
  ⟨fun b _ ↦ efq ⨀ b⟩


end «lp_section_1»

section «lp_section_2»

variable [Entailment.Minimal 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def conj₂Nth : (Γ : List F) → (n : ℕ) → (hn : n < Γ.length) → 𝓢 ⊢ ⋀Γ ==> Γ[n]
  | [],          _,     hn => by simp at hn
  | [ψ],         0,     _  => impId ψ
  | φ :: ψ :: Γ, 0,     _  => and₁
  | φ :: ψ :: Γ, n + 1, hn =>
    impTrans'' (and₂ (φ := φ)) (conj₂Nth (ψ :: Γ) n (Nat.succ_lt_succ_iff.mp hn))

/-- Imported declaration from the Incompleteness formalization. -/
lemma «conj₂_nth!» (Γ : List F) (n : ℕ) (hn : n < Γ.length) : 𝓢 ⊢! ⋀Γ ==> Γ[n] := ⟨conj₂Nth Γ n hn⟩

variable [DecidableEq F]
variable {Γ Δ : List F}

/-- Imported declaration from the Incompleteness formalization. -/
def generalConj {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢ Γ.conj ==> φ :=
  match Γ with
  | []     => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ
    then cast (by simp [e]) (and₁ (φ := φ) (ψ := Γ.conj))
    else
      have : φ ∈ Γ := by simpa [e] using h
      impTrans'' and₂ (generalConj this)
omit [DecidableEq F] in
lemma «generalConj!» (h : φ ∈ Γ) : 𝓢 ⊢! Γ.conj ==> φ := by
  classical
  exact ⟨generalConj h⟩

/-- Imported declaration from the Incompleteness formalization. -/
def conjIntro (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ Γ.conj :=
  match Γ with
  | []     => verum
  | ψ :: Γ => andIntro (b ψ (by simp)) (conjIntro Γ (fun ψ hq ↦ b ψ (by simp [hq])))

/-- Imported declaration from the Incompleteness formalization. -/
def implyConj (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ ==> ψ) : 𝓢 ⊢ φ ==> Γ.conj :=
  match Γ with
  | []     => imply₁' verum
  | ψ :: Γ => implyAnd (b ψ (by simp)) (implyConj φ Γ (fun ψ hq ↦ b ψ (by simp [hq])))

/-- Imported declaration from the Incompleteness formalization. -/
def conjImplyConj (h : Δ ⊆ Γ) : 𝓢 ⊢ Γ.conj ==> Δ.conj :=
  implyConj _ _ (fun _ hq ↦ generalConj (h hq))

/-- Imported declaration from the Incompleteness formalization. -/
def generalConj' {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢ ⋀Γ ==> φ :=
  have : Γ.idxOf φ < Γ.length := List.idxOf_lt_length_iff.mpr h
  have : Γ[Γ.idxOf φ] = φ := List.getElem_idxOf this
  cast (by rw[this]) <| conj₂Nth Γ (Γ.idxOf φ) (by assumption)
omit [DecidableEq F] in
lemma «generate_conj'!» (h : φ ∈ Γ) : 𝓢 ⊢! ⋀Γ ==> φ := by
  classical
  exact ⟨generalConj' h⟩

/-- Imported declaration from the Incompleteness formalization. -/
def conjIntro' (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ ⋀Γ :=
  match Γ with
  | []     => verum
  | [ψ]    => by apply b; simp;
  | ψ :: χ :: Γ => by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.conj₂_cons_nonempty];
    exact andIntro (b ψ (by simp)) (conjIntro' _ (by aesop))
omit [DecidableEq F] in
lemma «conj_intro'!» (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢! φ) : 𝓢 ⊢! ⋀Γ :=
  ⟨conjIntro' Γ (fun φ hp => (b φ hp).some)⟩

/-- Imported declaration from the Incompleteness formalization. -/
def implyConj' (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ ==> ψ) : 𝓢 ⊢ φ ==> ⋀Γ :=
  match Γ with
  | []     => imply₁' verum
  | [ψ]    => by apply b; simp;
  | ψ :: χ :: Γ => by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.conj₂_cons_nonempty];
    apply implyAnd (b ψ (by simp)) (implyConj' φ _ (fun ψ hq ↦ b ψ (by simp [hq])));
omit [DecidableEq F] in
lemma «imply_conj'!» (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! φ ==> ψ) : 𝓢 ⊢! φ ==> ⋀Γ :=
  ⟨implyConj' φ Γ (fun ψ hq => (b ψ hq).some)⟩

/-- Imported declaration from the Incompleteness formalization. -/
def conjImplyConj' {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢ ⋀Γ ==> ⋀Δ :=
  implyConj' _ _ (fun _ hq ↦ generalConj' (h hq))

end «lp_section_2»


section «lp_section_3»

variable {G T : Type*} [Entailment G T] [LogicalConnective G] {𝓣 : T}

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def _root_.LO.Entailment.Minimal.ofEquiv
    (𝓢 : S) [Entailment.Minimal 𝓢] (𝓣 : T) (f : G →ˡᶜ F) (e : (φ : G) → 𝓢 ⊢ f φ ≃ 𝓣 ⊢ φ) :
    Entailment.Minimal 𝓣 where
  mdp {φ ψ dpq dp} := (e ψ) (
    let d : 𝓢 ⊢ f φ ==> f ψ := by simpa using (e (φ ==> ψ)).symm dpq
    d ⨀ ((e φ).symm dp))
  negEquiv φ := e _ (by simpa using negEquiv)
  verum := e _ (by simpa using verum)
  imply₁ φ ψ := e _ (by simpa using imply₁)
  imply₂ φ ψ χ := e _ (by simpa using imply₂)
  and₁ φ ψ := e _ (by simpa using and₁)
  and₂ φ ψ := e _ (by simpa using and₂)
  and₃ φ ψ := e _ (by simpa using and₃)
  or₁ φ ψ := e _ (by simpa using or₁)
  or₂ φ ψ := e _ (by simpa using or₂)
  or₃ φ ψ χ := e _ (by simpa using or₃)

/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def _root_.LO.Entailment.Classical.ofEquiv
    (𝓢 : S) [Entailment.Classical 𝓢] (𝓣 : T) (f : G →ˡᶜ F) (e : (φ : G) → 𝓢 ⊢ f φ ≃ 𝓣 ⊢ φ) :
    Entailment.Classical 𝓣 where
  mdp {φ ψ dpq dp} := (e ψ) (
    let d : 𝓢 ⊢ f φ ==> f ψ := by simpa using (e (φ ==> ψ)).symm dpq
    d ⨀ ((e φ).symm dp))
  negEquiv φ := e _ (by simpa using negEquiv)
  verum := e _ (by simpa using verum)
  imply₁ φ ψ := e _ (by simpa using imply₁)
  imply₂ φ ψ χ := e _ (by simpa using imply₂)
  and₁ φ ψ := e _ (by simpa using and₁)
  and₂ φ ψ := e _ (by simpa using and₂)
  and₃ φ ψ := e _ (by simpa using and₃)
  or₁ φ ψ := e _ (by simpa using or₁)
  or₂ φ ψ := e _ (by simpa using or₂)
  or₃ φ ψ χ := e _ (by simpa using or₃)
  dne φ := e _ (by simpa using dne)

end «lp_section_3»

end Entailment
end LO
