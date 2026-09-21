/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassSubgroupExistence
/-!
# Ray class reciprocity

For a modulus `m`, there exists a finite abelian extension whose Galois group
is the ideal-theoretic ray class group modulo `m`, compatibly with finite
global reciprocity.  No global choice of ray class field is exposed.
-/

open scoped Classical NumberField

noncomputable section

namespace ClassFieldTheory

/-- A ray class field realization exists for every modulus. -/
theorem rayClassField_reciprocity
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K) :
    Nonempty (RayClassFieldRealization K m) := by
  obtain ⟨R⟩ := rayClassSubgroup_existence K m ⊥
  have hinj : Function.Injective R.artin :=
    (MonoidHom.ker_eq_bot_iff R.artin).mp R.artin_ker
  let e : RayClassGroup m ≃* (R.extension ≃ₐ[K] R.extension) :=
    MulEquiv.ofBijective R.artin ⟨hinj, R.artin_surjective⟩
  refine ⟨{
    extension := R.extension
    unramifiedOutsideModulus := R.unramifiedOutsideModulus
    artinEquiv := e
    artin_frobenius := ?_ }⟩
  intro v hv w hlie
  exact R.artin_frobenius v hv w hlie

end ClassFieldTheory
