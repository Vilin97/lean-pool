/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Basic

/-! # Lukasiewicz -/


namespace LO

section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
class LukasiewiczAbbrev (F : Type*) [LogicalConnective F] where
  top : ⊤ = ∼(⊥ : F)
  neg {φ : F} : ∼φ = φ ==> ⊥
  or {φ ψ : F} : φ ⋎ ψ = ∼φ ==> ψ
  and {φ ψ : F} : φ ⋏ ψ = ∼(φ ==> ∼ψ)

instance [LogicalConnective F] [LukasiewiczAbbrev F] : NegAbbrev F := ⟨LukasiewiczAbbrev.neg⟩

end «lp_section_1»


namespace Entailment

attribute [local simp]
  LukasiewiczAbbrev.top
  LukasiewiczAbbrev.neg
  LukasiewiczAbbrev.or
  LukasiewiczAbbrev.and

variable {S F : Type*} [LogicalConnective F] [LukasiewiczAbbrev F] [Entailment F S]

variable (𝓢 : S)

/-- Imported declaration from the Incompleteness formalization. -/
protected class Lukasiewicz [LukasiewiczAbbrev F]
  extends ModusPonens 𝓢,
          HasAxiomImply₁ 𝓢,
          HasAxiomImply₂ 𝓢,
          HasAxiomElimContra 𝓢

namespace Lukasiewicz

variable {𝓢 : S} {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ s t : F}

variable [Entailment.Lukasiewicz 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def verum : 𝓢 ⊢ ⊤ := by simp only [LukasiewiczAbbrev.top, LukasiewiczAbbrev.neg]; exact impId ⊥;
instance : HasAxiomVerum 𝓢 := ⟨Lukasiewicz.verum⟩

/-- Imported declaration from the Incompleteness formalization. -/
def dne : 𝓢 ⊢ ∼∼φ ==> φ := by
  have d₁ : 𝓢 ⊢ ∼∼φ ==> (∼∼(∼∼φ) ==> ∼∼φ) ==> ∼φ ==> ∼(∼∼φ) := imply₁' <| elimContra;
  have d₂ : 𝓢 ⊢ ∼∼φ ==> ∼∼(∼∼φ) ==> ∼∼φ := imply₁;
  have d₃ : 𝓢 ⊢ ∼∼φ ==> (∼φ ==> ∼(∼∼φ)) ==> ∼∼φ ==> φ := imply₁' <| elimContra;
  have d₄ : 𝓢 ⊢ ∼∼φ ==> ∼φ ==> ∼(∼∼φ) := d₁ ⨀₁ d₂;
  have d₅ : 𝓢 ⊢ ∼∼φ ==> ∼∼φ ==> φ := d₃ ⨀₁ d₄;
  have d₆ : 𝓢 ⊢ ∼∼φ ==> ∼∼φ := impId _;
  exact d₅ ⨀₁ d₆;
instance : HasAxiomDNE 𝓢 := ⟨fun φ => Lukasiewicz.dne (φ := φ)⟩

/-- Imported declaration from the Incompleteness formalization. -/
def dni : 𝓢 ⊢ φ ==> ∼∼φ := by
  have d₁ : 𝓢 ⊢ (∼(∼∼φ) ==> ∼φ) ==> φ ==> ∼∼φ := elimContra;
  have d₂ : 𝓢 ⊢ ∼(∼∼φ) ==> ∼φ := dne (φ := ∼φ);
  exact d₁ ⨀ d₂;

/-- Imported declaration from the Incompleteness formalization. -/
def explode (h₁ : 𝓢 ⊢ φ) (h₂ : 𝓢 ⊢ ∼φ) : 𝓢 ⊢ ψ := by
  have d₁ := imply₁ (𝓢 := 𝓢) (φ := ∼φ) (ψ := ∼ψ);
  have := d₁ ⨀ h₂;
  exact elimContra ⨀ this ⨀ h₁;

/-- Imported declaration from the Incompleteness formalization. -/
def explodeHyp (h₁ : 𝓢 ⊢ φ ==> ψ) (h₂ : 𝓢 ⊢ φ ==> ∼ψ) : 𝓢 ⊢ φ ==> χ := by
  have : 𝓢 ⊢ φ ==> ∼ψ ==> ∼χ ==> ∼ψ := imply₁' imply₁ (ψ := φ)
  have : 𝓢 ⊢ φ ==> ∼χ ==> ∼ψ := this ⨀₁ h₂;
  have : 𝓢 ⊢ φ ==> ψ ==> χ := (imply₁' elimContra (ψ := φ)) ⨀₁ this;
  exact this ⨀₁ h₁;

/-- Imported declaration from the Incompleteness formalization. -/
def explodeHyp₂ (h₁ : 𝓢 ⊢ φ ==> ψ ==> χ) (h₂ : 𝓢 ⊢ φ ==> ψ ==> ∼χ) : 𝓢 ⊢ φ ==> ψ ==> s := by
  have : 𝓢 ⊢ φ ==> ψ ==> ∼χ ==> ∼s ==> ∼χ := imply₁' (imply₁' imply₁ (ψ := ψ)) (ψ := φ)
  have : 𝓢 ⊢ φ ==> ψ ==> ∼(s) ==> ∼χ := this ⨀₂ h₂;
  have : 𝓢 ⊢ φ ==> ψ ==> χ ==> s := (imply₁' (imply₁' elimContra (ψ := ψ)) (ψ := φ)) ⨀₂ this;
  exact this ⨀₂ h₁;

/-- Imported declaration from the Incompleteness formalization. -/
def efq : 𝓢 ⊢ ⊥ ==> φ := by
  have := explodeHyp (𝓢 := 𝓢) (φ := ⊥) (ψ := ⊤) (χ := φ);
  exact this
    (by simp only [LukasiewiczAbbrev.top, LukasiewiczAbbrev.neg]; exact imply₁)
    (by simp only [LukasiewiczAbbrev.top, LukasiewiczAbbrev.neg]; exact imply₁);
instance : HasAxiomEFQ 𝓢 := ⟨fun φ => Lukasiewicz.efq (φ := φ)⟩

/-- Imported declaration from the Incompleteness formalization. -/
def impSwap (h : 𝓢 ⊢ φ ==> ψ ==> χ) : 𝓢 ⊢ ψ ==> φ ==> χ := by
  refine mdp₂ (χ := ψ) ?_ ?_;
  · exact imply₁' h;
  · exact imply₁;

/-- Imported declaration from the Incompleteness formalization. -/
def mdpIn₁ : 𝓢 ⊢ (φ ==> ψ) ==> φ ==> ψ := impId _

/-- Imported declaration from the Incompleteness formalization. -/
def mdpIn₂ : 𝓢 ⊢ φ ==> (φ ==> ψ) ==> ψ := impSwap mdpIn₁

/-- Imported declaration from the Incompleteness formalization. -/
def mdp₂In₁ : 𝓢 ⊢ (φ ==> ψ ==> χ) ==> (φ ==> ψ) ==> (φ ==> χ) := imply₂

/-- Imported declaration from the Incompleteness formalization. -/
def mdp₂In₂ : 𝓢 ⊢ (φ ==> ψ) ==> (φ ==> ψ ==> χ) ==> (φ ==> χ) := impSwap mdp₂In₁

/-- Imported declaration from the Incompleteness formalization. -/
def impTrans'₁ (bpq : 𝓢 ⊢ φ ==> ψ) : 𝓢 ⊢ (ψ ==> χ) ==> (φ ==> χ) :=
  impSwap (impTrans'' bpq mdpIn₂)

/-- Imported declaration from the Incompleteness formalization. -/
def impTrans'₂ (bqr : 𝓢 ⊢ ψ ==> χ) : 𝓢 ⊢ (φ ==> ψ) ==> (φ ==> χ) := imply₂ ⨀ (imply₁' bqr)

/-- Imported declaration from the Incompleteness formalization. -/
def impTrans₂ : 𝓢 ⊢ (ψ ==> χ) ==> (φ ==> ψ) ==> (φ ==> χ) :=
  impTrans'' (impSwap (imply₁' (impId (ψ ==> χ)))) mdp₂In₁

/-- Imported declaration from the Incompleteness formalization. -/
def impTrans₁ : 𝓢 ⊢ (φ ==> ψ) ==> (ψ ==> χ) ==> (φ ==> χ) := impSwap impTrans₂

/-- Imported declaration from the Incompleteness formalization. -/
def dhypBoth (h : 𝓢 ⊢ ψ ==> χ) : 𝓢 ⊢ (φ ==> ψ) ==> (φ ==> χ) := imply₂ ⨀ (imply₁' <| h)

/-- Imported declaration from the Incompleteness formalization. -/
def explode₂₁ : 𝓢 ⊢ ∼φ ==> φ ==> ψ := by
  simp only [LukasiewiczAbbrev.neg];
  exact dhypBoth efq;

/-- Imported declaration from the Incompleteness formalization. -/
def explode₁₂ : 𝓢 ⊢ φ ==> ∼φ ==> ψ := impSwap explode₂₁

/-- Imported declaration from the Incompleteness formalization. -/
def contraIntro : 𝓢 ⊢ (φ ==> ψ) ==> (∼ψ ==> ∼φ):= by simpa using impTrans₁;

/-- Imported declaration from the Incompleteness formalization. -/
def contraIntro' : 𝓢 ⊢ (φ ==> ψ) → 𝓢 ⊢ (∼ψ ==> ∼φ) := fun h => contraIntro ⨀ h

/-- Imported declaration from the Incompleteness formalization. -/
def andElim₁ : 𝓢 ⊢ φ ⋏ ψ ==> φ := by
  simp only [LukasiewiczAbbrev.and];
  have : 𝓢 ⊢ ∼φ ==> φ ==> ∼ψ := explodeHyp₂ explode₂₁ imply₁;
  have : 𝓢 ⊢ ∼(φ ==> ∼ψ) ==> ∼∼φ := contraIntro' explode₂₁
  exact impTrans'' this dne;

/-- Imported declaration from the Incompleteness formalization. -/
def andElim₂ : 𝓢 ⊢ φ ⋏ ψ ==> ψ := by
  simp only [LukasiewiczAbbrev.and];
  have : 𝓢 ⊢ ∼ψ ==> φ ==> ∼ψ := imply₁ (φ := ∼ψ) (ψ := φ);
  have : 𝓢 ⊢ ∼(φ ==> ∼ψ) ==> ∼∼ψ := contraIntro' this;
  exact impTrans'' this dne;
instance : HasAxiomAndElim 𝓢 :=
  ⟨fun φ ψ => Lukasiewicz.andElim₁ (φ := φ) (ψ := ψ),
    fun φ ψ => Lukasiewicz.andElim₂ (φ := φ) (ψ := ψ)⟩

/-- Imported declaration from the Incompleteness formalization. -/
def andImplyLeft : 𝓢 ⊢ (φ₁ ==> ψ) ==> φ₁ ⋏ φ₂ ==> ψ :=
  (impSwap <| imply₁' (impId _)) ⨀₂ (imply₁' andElim₁)
/-- Imported declaration from the Incompleteness formalization. -/
def andImplyLeft' (h : 𝓢 ⊢ (φ₁ ==> ψ)) : 𝓢 ⊢ φ₁ ⋏ φ₂ ==> ψ := andImplyLeft ⨀ h

/-- Imported declaration from the Incompleteness formalization. -/
def andImplyRight : 𝓢 ⊢ (φ₂ ==> ψ) ==> φ₁ ⋏ φ₂ ==> ψ :=
  (impSwap <| imply₁' (impId _)) ⨀₂ (imply₁' andElim₂)
/-- Imported declaration from the Incompleteness formalization. -/
def andImplyRight' (h : 𝓢 ⊢ (φ₂ ==> ψ)) : 𝓢 ⊢ φ₁ ⋏ φ₂ ==> ψ := andImplyRight ⨀ h

/-- Imported declaration from the Incompleteness formalization. -/
def andInst'' (hp : 𝓢 ⊢ φ) (hq : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋏ ψ := by
  simp only [LukasiewiczAbbrev.and];
  have : 𝓢 ⊢ (φ ==> ∼ψ) ==> φ ==> ∼ψ := impId _
  have : 𝓢 ⊢ (φ ==> ∼ψ) ==> ∼ψ := this ⨀₁ imply₁' hp;
  have : 𝓢 ⊢ ψ ==> ∼(φ ==> ∼ψ) := impTrans'' dni <| contraIntro' this;
  exact this ⨀ hq;

/-- Imported declaration from the Incompleteness formalization. -/
def andInst : 𝓢 ⊢ φ ==> ψ ==> φ ⋏ ψ := by
  have d₁ : 𝓢 ⊢ φ ==> ψ ==> (φ ==> ∼ψ) ==> φ ==> ∼ψ := imply₁' <| imply₁' <| impId (φ ==> ∼ψ);
  have d₂ : 𝓢 ⊢ φ ==> ψ ==> (φ ==> ∼ψ) ==> φ := imply₁₁ (φ := φ) (ψ := ψ) (χ := (φ ==> ∼ψ));
  have d₃ : 𝓢 ⊢ φ ==> ψ ==> (φ ==> ∼ψ) ==> ψ := imply₁' <| imply₁;
  have d₄ : 𝓢 ⊢ φ ==> ψ ==> (φ ==> ∼ψ) ==> ∼ψ := d₁ ⨀₃ d₂;
  have d₄ : 𝓢 ⊢ φ ==> ψ ==> (φ ==> ∼ψ) ==> ψ ==> ⊥ := by simpa using d₄;
  simpa using d₄ ⨀₃ d₃;

instance : HasAxiomAndInst 𝓢 := ⟨fun φ ψ => Lukasiewicz.andInst (φ := φ) (ψ := ψ)⟩


/-- Imported declaration from the Incompleteness formalization. -/
def orInst₁ : 𝓢 ⊢ φ ==> φ ⋎ ψ := by
  simp only [LukasiewiczAbbrev.or];
  exact explode₁₂;

/-- Imported declaration from the Incompleteness formalization. -/
def orInst₂ : 𝓢 ⊢ ψ ==> φ ⋎ ψ := by
  simp only [LukasiewiczAbbrev.or, LukasiewiczAbbrev.neg];
  exact imply₁;

instance : HasAxiomOrInst 𝓢 :=
  ⟨fun φ ψ => Lukasiewicz.orInst₁ (φ := φ) (ψ := ψ),
    fun φ ψ => Lukasiewicz.orInst₂ (φ := φ) (ψ := ψ)⟩

-- or_imply
/-- Imported declaration from the Incompleteness formalization. -/
def orElim : 𝓢 ⊢ (φ ==> χ) ==> (ψ ==> χ) ==> (φ ⋎ ψ ==> χ) := by
  simp only [LukasiewiczAbbrev.or];
  have d₁ : 𝓢 ⊢ (φ ==> χ) ==> (ψ ==> χ) ==> (∼φ ==> ψ) ==> (φ ==> χ) ==> ∼χ ==> ∼φ
    :=
      (imply₁' (ψ := φ ==> χ) <| imply₁' (ψ := ψ ==> χ) <| imply₁' (ψ := ∼φ ==> ψ) <|
          contraIntro (φ := φ) (ψ := χ));
  have d₂ : 𝓢 ⊢ (φ ==> χ) ==> (ψ ==> χ) ==> (∼φ ==> ψ) ==> ∼χ ==> ∼φ
    := d₁ ⨀₃ (imply₁₁ (φ ==> χ) (ψ ==> χ) (∼φ ==> ψ));
  have d₃ : 𝓢 ⊢ (φ ==> χ) ==> (ψ ==> χ) ==> (∼φ ==> ψ) ==> ∼χ ==> ψ
    := (imply₁' (ψ := φ ==> χ) <| imply₁' (ψ := ψ ==> χ) <| imply₁ (φ := ∼φ ==> ψ) (ψ := ∼χ)) ⨀₄ d₂;
  have d₄ : 𝓢 ⊢ (φ ==> χ) ==> (ψ ==> χ) ==> (∼φ ==> ψ) ==> ∼χ ==> χ
    := (imply₁' (ψ := φ ==> χ) <| imply₁₁ (φ := ψ ==> χ) (ψ := ∼φ ==> ψ) (χ := ∼χ)) ⨀₄ d₃;
  have d₅ : 𝓢 ⊢ (φ ==> χ) ==> (ψ ==> χ) ==> (∼φ ==> ψ) ==> ∼χ ==> χ ==> ⊥
    := by
      simpa using imply₁' (ψ := φ ==> χ) <| imply₁' (ψ := ψ ==> χ) <| imply₁' (ψ := ∼φ ==> ψ) <|
          impId (φ := ∼χ);
  have d₆ : 𝓢 ⊢ (φ ==> χ) ==> (ψ ==> χ) ==> (∼φ ==> ψ) ==> ∼∼χ
    := by simpa using d₅ ⨀₄ d₄;
  have d₇ : 𝓢 ⊢ (φ ==> χ) ==> (ψ ==> χ) ==> (∼φ ==> ψ) ==> ∼∼χ ==> χ
    := imply₁' (ψ := φ ==> χ) <| imply₁' (ψ := ψ ==> χ) <| imply₁' (ψ := ∼φ ==> ψ) <| dne (φ := χ);
  exact d₇ ⨀₃ d₆;

instance : HasAxiomOrElim 𝓢 := ⟨fun φ ψ χ => Lukasiewicz.orElim (φ := φ) (ψ := ψ) (χ := χ)⟩

instance : Entailment.Classical 𝓢 where

end Lukasiewicz

end Entailment

end LO
