/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Logic.Entailment

/-! # Axioms -/


namespace LO
namespace Axioms

section «lp_section_1»

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Verum : F := ⊤
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Verum.set : Set F := { Axioms.Verum }

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Imply₁ := φ ==> ψ ==> φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Imply₁.set : Set F := { Axioms.Imply₁ φ ψ | (φ) (ψ) }

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Imply₂ := (φ ==> ψ ==> χ) ==> (φ ==> ψ) ==> φ ==> χ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Imply₂.set : Set F := { Axioms.Imply₂ φ ψ χ | (φ) (ψ) (χ) }

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev ElimContra := (∼ψ ==> ∼φ) ==> (φ ==> ψ)
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.ElimContra.set : Set F := { Axioms.ElimContra φ ψ | (φ) (ψ) }

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev AndElim₁ := φ ⋏ ψ ==> φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.AndElim₁.set : Set F := { Axioms.AndElim₁ φ ψ | (φ) (ψ) }

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev AndElim₂ := φ ⋏ ψ ==> ψ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.AndElim₂.set : Set F := { Axioms.AndElim₂ φ ψ | (φ) (ψ) }

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev AndInst := φ ==> ψ ==> φ ⋏ ψ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.AndInst.set : Set F := { Axioms.AndInst φ ψ | (φ) (ψ) }

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev OrInst₁ := φ ==> φ ⋎ ψ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.OrInst₁.set : Set F := { Axioms.OrInst₁ φ ψ | (φ) (ψ) }

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev OrInst₂ := ψ ==> φ ⋎ ψ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.OrInst₂.set : Set F := { Axioms.OrInst₂ φ ψ | (φ) (ψ) }

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev OrElim := (φ ==> χ) ==> (ψ ==> χ) ==> (φ ⋎ ψ ==> χ)
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.OrElim.set : Set F := { Axioms.OrElim φ ψ χ | (φ) (ψ) (χ) }

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev NegEquiv := ∼φ <=> (φ ==> ⊥)
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.NegEquiv.set : Set F := { Axioms.NegEquiv φ | (φ) }

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev EFQ := ⊥ ==> φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.EFQ.set : Set F := { Axioms.EFQ φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation "EFQAx" => EFQ.set

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev LEM := φ ⋎ ∼φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.LEM.set : Set F := { Axioms.LEM φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation "LEMAx" => LEM.set

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev WeakLEM := ∼φ ⋎ ∼∼φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.WeakLEM.set : Set F := { Axioms.WeakLEM φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation "WLEMAx" => WeakLEM.set

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Dummett := (φ ==> ψ) ⋎ (ψ ==> φ)
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Dummett.set : Set F := { Axioms.Dummett φ ψ | (φ) (ψ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation "DummettAx" => Dummett.set

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev DNE := ∼∼φ ==> φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.DNE.set : Set F := { Axioms.DNE φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation "DNEAx" => DNE.set

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Peirce := ((φ ==> ψ) ==> φ) ==> φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Peirce.set : Set F := { Axioms.Peirce φ ψ | (φ) (ψ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation "PeirceAx" => Peirce.set

end «lp_section_1»

end Axioms
end LO
