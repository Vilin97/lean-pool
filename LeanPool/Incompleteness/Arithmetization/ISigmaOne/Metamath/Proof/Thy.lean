/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.ISigmaOne.Metamath.Formula.Functions
import LeanPool.Incompleteness.Arithmetization.ISigmaOne.Metamath.Formula.Iteration

/-! # Thy -/


noncomputable section «lp_nc_section_1»

namespace LO
namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

section «lp_section_1»

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.FirstOrder.Arith.LDef.TDef (pL : LDef) where
  /-- Imported declaration from the Incompleteness formalization. -/
  ch : Dlt1.Semisentence 1

/-- Imported declaration from the Incompleteness formalization. -/
protected structure _root_.LO.Arith.Language.Theory (L : Arith.Language V) {pL :
    LDef} [Arith.Language.Defined L pL] where
  /-- Imported declaration from the Incompleteness formalization. -/
  set : Set V

instance : Membership V L.Theory := ⟨fun T x ↦ x ∈ T.set⟩

instance : HasSubset L.Theory := ⟨fun T U ↦ T.set ⊆ U.set⟩

lemma _root_.LO.Arith.Language.Theory.mem_def {T : L.Theory} {p} : p ∈ T ↔ p ∈ T.set := by rfl

variable {L}

namespace Language
namespace Theory

/-- Imported declaration from the Incompleteness formalization. -/
protected class Defined (T : L.Theory) (pT : outParam pL.TDef) where
  defined : Dlt1-Predicate (· ∈ T.set) via pT.ch

variable (T : L.Theory) {pT : pL.TDef} [T.Defined pT]

/-- Imported declaration from the Incompleteness formalization. -/
lemma mem_defined : Dlt1-Predicate (· ∈ T) via pT.ch := Defined.defined

instance mem_definable : Dlt1-Predicate (· ∈ T) := (mem_defined T).to_definable

end Theory
end Language

end «lp_section_1»
end Arith
end LO
