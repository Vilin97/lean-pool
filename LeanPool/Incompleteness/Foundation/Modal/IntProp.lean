/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.IntProp.Formula
import LeanPool.Incompleteness.Foundation.Modal.Formula

/-! # IntProp -/


namespace LO
namespace IntProp

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.IntProp.Formula.toModalFormula : Formula α → Modal.Formula α
  | .atom a => Modal.Formula.atom a
  | ⊥ => ⊥
  | φ ==> ψ => (toModalFormula φ) ==> (toModalFormula ψ)
  | φ ⋏ ψ => (toModalFormula φ) ⋏ (toModalFormula ψ)
  | φ ⋎ ψ => (toModalFormula φ) ⋎ (toModalFormula ψ)
/-- Imported declaration from the Incompleteness formalization. -/
postfix:75 "ᴹ" => Formula.toModalFormula

namespace Formula
namespace toModalFormula

@[simp] lemma def_top : (⊤ : Formula α)ᴹ = ⊤ := by rfl

@[simp] lemma def_bot : (⊥ : Formula α)ᴹ = ⊥ := by rfl

@[simp] lemma def_atom (a : α) : (atom a)ᴹ = .atom a := by rfl

@[simp] lemma def_not (φ : Formula α) : (∼φ)ᴹ = ∼(φᴹ) := by rfl

@[simp] lemma def_imp (φ ψ : Formula α) : (φ ==> ψ)ᴹ = (φᴹ) ==> (ψᴹ) := by rfl

@[simp] lemma def_and (φ ψ : Formula α) : (φ ⋏ ψ)ᴹ = (φᴹ) ⋏ (ψᴹ) := by rfl

@[simp] lemma def_or (φ ψ : Formula α) : (φ ⋎ ψ)ᴹ = (φᴹ) ⋎ (ψᴹ) := by rfl

end toModalFormula
end Formula

end IntProp
end LO


namespace LO
namespace Modal

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Formula.toPropFormula (φ : Formula α) (_ : φ.degree = 0 :=
  by simp_all [Formula.degree, Formula.degree_neg, Formula.degree_imp]) :
    IntProp.Formula α :=
  match φ with
  | .atom a => IntProp.Formula.atom a
  | ⊥ => ⊥
  | φ ==> ψ => φ.toPropFormula ==> ψ.toPropFormula
/-- Imported declaration from the Incompleteness formalization. -/
postfix:75 "ᴾ" => Formula.toPropFormula

end Modal
end LO
