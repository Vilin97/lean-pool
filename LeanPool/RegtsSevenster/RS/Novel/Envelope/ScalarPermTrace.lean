/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.PermTrace
import LeanPool.RegtsSevenster.RS.Novel.Envelope.ScalarTrace

/-!
# The scalar cycle-trace formula

The categorical cycle-trace formula read through the scalar unit.
This is the common trace input to the factorial obstruction and to
the Frobenius formula. Fixed points can be recorded separately
from the nontrivial cycles.
-/

namespace RS

open CategoryTheory CategoryTheory.MonoidalCategory

universe v u

variable {A : Type u}

/-- The complex trace of a permutation against a tensor power is
the product of the complex cycle traces over the full cycle type. -/
theorem scalarTrace_permMor_powHom
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) (X : A)
    (g : End X) {n : ℕ} (π : Equiv.Perm (Fin n)) :
    scalarTrace hu (tensorPow A X n)
        (permMor X n π ≫ powHom X g n) =
      ((fullCycleType π).map
        (fun c => scalarTrace hu X (g ^ c))).prod := by
  show unitScalar hu (catTrace (permMor X n π ≫ powHom X g n)) = _
  rw [catTrace_permMor_powHom, map_multiset_prod, Multiset.map_map]
  rfl

/-- The full cycle type splits the product into the cycle type and
the fixed points. -/
theorem prod_fullCycleType {n : ℕ} (π : Equiv.Perm (Fin n))
    (t : ℕ → ℂ) :
    ((fullCycleType π).map t).prod =
      (π.cycleType.map t).prod * t 1 ^ (n - π.cycleType.sum) := by
  rw [fullCycleType, Multiset.map_add, Multiset.prod_add,
    Multiset.map_replicate, Multiset.prod_replicate]

end RS
