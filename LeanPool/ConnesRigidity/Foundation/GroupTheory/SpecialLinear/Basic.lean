/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finsupp.Encodable
import LeanPool.ConnesRigidity.Core

/-!
# The special-linear carrier in Zhou's construction
-/

namespace Connes
namespace SpecialLinear

/-- Characteristic-two scalar field. Paper: §§2, 4. -/
abbrev F := ZMod 2
/-- Polynomial coefficient ring. Paper: §2. -/
abbrev R := Polynomial F
/-- Special-linear group carrier. Paper: §§2, 4. -/
abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) R

/-- Countability of the polynomial ring. Paper: §4. -/
noncomputable instance : Countable R := by
  exact Countable.of_equiv (ℕ →₀ F)
    (AddMonoidAlgebra.coeffEquiv.symm.trans (Polynomial.toFinsuppIso F).toEquiv.symm)

/-- Countability of the matrix carrier. Paper: §4. -/
noncomputable instance : Countable (Matrix (Fin 3) (Fin 3) R) := by
  change Countable (Fin 3 → Fin 3 → R)
  infer_instance

/-- Countability of the special-linear carrier. Paper: §4. -/
noncomputable instance : Countable SL3 := by
  change Countable {A : Matrix (Fin 3) (Fin 3) R // A.det = 1}
  infer_instance

/-- Countable discrete acting-group carrier. Paper: §§4, 5. -/
noncomputable def sl3Group : CountableDiscreteGroup where
  Carrier := SL3
  group := inferInstance
  countable := by infer_instance

end SpecialLinear
end Connes
