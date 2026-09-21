/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Narrow
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLattice
/-!
# The big Hilbert class field

The big Hilbert class field is the ray class field of modulus one (the
zero finite modulus in the exponent-valued representation).  This file
identifies its defining norm quotient with the narrow class group.  The
maximal-unramified field statement follows from this input together with
the narrow finite conductor/ramification criterion.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The norm subgroup defining the big Hilbert class field. -/
def bigHilbertClassFieldNormSubgroup :
    Subgroup (IdeleClassGroup K) :=
  (RayClass.Modulus.narrowOfFinite
    (0 : RayClass.FiniteModulus K)).congruenceSubgroup

instance bigHilbertClassFieldNormSubgroup_normal :
    (bigHilbertClassFieldNormSubgroup (K := K)).Normal := by
  let : IsMulCommutative (IdeleClassGroup K) :=
    IsMulCommutative.of_comm (fun a b => mul_comm a b)
  exact Subgroup.normal_of_isMulCommutative _

/-- The norm subgroup defining the big Hilbert class field is closed. -/
theorem bigHilbertClassFieldNormSubgroup_isClosed :
    IsClosed
      ((bigHilbertClassFieldNormSubgroup (K := K) :
        Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) :=
  RayClass.isClosed_congruenceSubgroup
    (RayClass.Modulus.narrowOfFinite
      (0 : RayClass.FiniteModulus K))

/-- The reciprocity quotient for the big Hilbert class field is the narrow
ideal class group. -/
def bigHilbertClassFieldQuotientEquivNarrowClassGroup :
    IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K) ≃*
      RayClass.NarrowClassGroup K :=
  RayClass.rayClassGroupNarrowZeroEquivNarrowClassGroup

/-- The narrow modulus with zero finite part is a defining modulus for the
big-Hilbert norm subgroup. -/
theorem bigHilbertClassFieldNormSubgroup_isDefiningModulus :
    IsDefiningModulus
      (bigHilbertClassFieldNormSubgroup (K := K))
      (RayClass.Modulus.narrowOfFinite
        (0 : RayClass.FiniteModulus K)) := by
  exact le_rfl

/-- The conductorial subgroup supplied by the intrinsic big-Hilbert norm
subgroup and its narrow zero-finite defining modulus. -/
noncomputable def bigHilbertClassFieldConductorialSubgroup :
    ConductorialSubgroup K :=
  ⟨bigHilbertClassFieldNormSubgroup (K := K),
    ⟨RayClass.Modulus.narrowOfFinite (0 : RayClass.FiniteModulus K),
      bigHilbertClassFieldNormSubgroup_isDefiningModulus (K := K)⟩⟩

/-- Among conductorial idèle-class subgroups, containing the big-Hilbert
norm subgroup is equivalent to having narrow finite conductor zero. -/
theorem
    bigHilbertClassFieldNormSubgroup_le_iff_narrowFiniteConductor_eq_zero
    (H : ConductorialSubgroup K) :
    bigHilbertClassFieldNormSubgroup (K := K) ≤ H.1 ↔
      H.narrowFiniteConductor = 0 := by
  constructor
  · intro hH
    have hdef :
        IsDefiningModulus H.1
          (RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus K)) := by
      simpa only [IsDefiningModulus,
        bigHilbertClassFieldNormSubgroup] using hH
    apply le_antisymm
    · exact H.narrowFiniteConductor_le hdef
    · exact bot_le
  · intro hconductor
    have hdef := H.narrowFiniteConductor_isDefiningModulus
    rw [hconductor] at hdef
    simpa only [IsDefiningModulus,
      bigHilbertClassFieldNormSubgroup] using hdef

/-- The narrow finite conductor of the big-Hilbert norm subgroup is zero. -/
@[simp]
theorem bigHilbertClassField_narrowFiniteConductor :
    (bigHilbertClassFieldConductorialSubgroup
      (K := K)).narrowFiniteConductor = 0 := by
  apply le_antisymm
  · exact
      (bigHilbertClassFieldConductorialSubgroup
        (K := K)).narrowFiniteConductor_le
        (bigHilbertClassFieldNormSubgroup_isDefiningModulus (K := K))
  · exact bot_le

end GlobalClassFields
end GlobalClassFieldTheory
