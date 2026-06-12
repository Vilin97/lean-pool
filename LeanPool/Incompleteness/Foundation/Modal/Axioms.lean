/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.LogicSymbol
import LeanPool.Incompleteness.Foundation.Modal.Geachean

/-! # Axioms -/


namespace LO
namespace Axioms

variable {F : Type*} [BasicModalLogicalConnective F]
variable (φ ψ χ : F)


section «lp_section_1»

/-- `◇` is duality of `□`. -/
protected abbrev DiaDuality := ◇φ <=> ∼(□(∼φ))
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.DiaDuality.set : Set F := { Axioms.DiaDuality φ | (φ) }

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K := □(φ ==> ψ) ==> □φ ==> □ψ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.K.set : Set F := { Axioms.K φ ψ | (φ) (ψ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "KAx" => K.set

/-- Axiom for reflexive -/
protected abbrev T := □φ ==> φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.T.set : Set F := { Axioms.T φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "TAx" => T.set

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev DiaTc := φ ==> ◇φ

/-- Axiom for symmetric -/
protected abbrev B := φ ==> □◇φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.B.set : Set F := { Axioms.B φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "BAx" => B.set

/-- `□`-only version of axiom `BAx`. -/
protected abbrev B₂ := □φ ==> □(∼□(∼φ))
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.B₂.set : Set F := { Axioms.B₂ φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "BBoxAx" => B₂.set

/-- Axiom for serial -/
protected abbrev D := □φ ==> ◇φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.D.set : Set F := { Axioms.D φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "DAx" => D.set


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev P : F := ∼(□⊥)
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.P.set : Set F := { Axioms.P | }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "PAx" => P.set
@[simp 1100] lemma _root_.LO.Axioms.P.set.def : PAx = {(∼(□⊥) : F)} := by ext; simp;

/-- Axiom for transivity -/
protected abbrev Four := □φ ==> □□φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Four.set : Set F := { Axioms.Four φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "𝟰" => Four.set

/-- Axiom for euclidean -/
protected abbrev Five := ◇φ ==> □◇φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Five.set : Set F := { Axioms.Five φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "𝟱" => Five.set

/-- `□`-only version of axiom `𝟱`. -/
protected abbrev Five₂ := ∼□φ ==> □(∼□(∼φ))
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Five₂.set : Set F := { Axioms.Five₂ φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "𝟱(□)" => Five₂.set

/-- Axiom for confluency -/
protected abbrev Dot2 := ◇□φ ==> □◇φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Dot2.set : Set F := { Axioms.Dot2 φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max ".𝟮" => Dot2.set

/-- Axiom for density -/
protected abbrev C4 := □□φ ==> □φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.C4.set : Set F := { Axioms.C4 φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "C4Ax" => C4.set

/-- Axiom for functionality -/
protected abbrev CD := ◇φ ==> □φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.CD.set : Set F := { Axioms.CD φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "CDAx" => CD.set

/-- Axiom for coreflexivity -/
protected abbrev Tc := φ ==> □φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Tc.set : Set F := { Axioms.Tc φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "TcAx" => Tc.set

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev DiaT := ◇φ ==> φ

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Ver := □φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Ver.set : Set F := { Axioms.Ver φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "VerAx" => Ver.set

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Dot3 := □(□φ ==> ψ) ⋎ □(□ψ ==> φ)
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Dot3.set : Set F := { Axioms.Dot3 φ ψ | (φ) (ψ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max ".𝟯" => Dot3.set

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Grz := □(□(φ ==> □φ) ==> φ) ==> φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Grz.set : Set F := { Axioms.Grz φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "GrzAx" => Grz.set

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev M := (□◇φ ==> ◇□φ)
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.M.set : Set F := { Axioms.M φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "MAx" => M.set

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev L := □(□φ ==> φ) ==> □φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.L.set : Set F := { Axioms.L φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "LAx" => L.set

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev H := □(□φ <=> φ) ==> □φ
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.H.set : Set F := { Axioms.H φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "HAx" => H.set

end «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Geach (t : Geachean.Taple) (φ : F) := ◇^[t.i](□^[t.m]φ) ==> □^[t.j](◇^[t.n]φ)
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Geach.set (t : Geachean.Taple) : Set F := { Axioms.Geach t φ | (φ) }
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "GeachAx(" t ")" => Geach.set t

end Axioms
end LO
