/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicField
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.Torsion
/-!
# The torsion fixed field in the rational cyclotomic extension

The rational cyclotomic construction takes the fixed field of the closure
of the torsion subgroup in `Gal(ℚ(μ∞)/ℚ)`.  This file defines that actual closed subgroup
and fixed field.  No copy of the Galois group is replaced definitionally by
`ℤ̂ˣ`; the comparison with profinite units is a later theorem.
-/

noncomputable section

namespace KummerTheory

open scoped IsMulCommutative

/-- The closure of the torsion subgroup in the actual Krull-topological
Galois group of `ℚ(μ∞)/ℚ`. -/
def rationalCyclotomicTorsionClosure :
    ClosedSubgroup
      (rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField) where
  toSubgroup :=
    (CommGroup.torsion
      (rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField)).topologicalClosure
  isClosed' :=
    Subgroup.isClosed_topologicalClosure _

/-- The actual subfield of `ℚ(μ∞)` fixed by the closure of all
finite-order cyclotomic automorphisms. -/
def rationalCyclotomicTorsionFixedField :
    IntermediateField ℚ rationalCyclotomicField :=
  IntermediateField.fixedField
    rationalCyclotomicTorsionClosure.toSubgroup

/-- The torsion fixed field is integral over `ℚ`, since it is an
intermediate field of the rational cyclotomic extension. -/
noncomputable instance
    rationalCyclotomicTorsionFixedField_isIntegral :
    Algebra.IsIntegral ℚ rationalCyclotomicTorsionFixedField := by
  rw [Algebra.isIntegral_def]
  intro x
  exact IntermediateField.isIntegral_iff.mpr
    (Algebra.IsIntegral.isIntegral
      (x : rationalCyclotomicField))

/-- The torsion fixed field is normal over `ℚ`: its defining closed subgroup
is normal in the abelian cyclotomic Galois group. -/
noncomputable instance
    rationalCyclotomicTorsionFixedField_normal :
    Normal ℚ rationalCyclotomicTorsionFixedField := by
  let : Subgroup.Normal rationalCyclotomicTorsionClosure.toSubgroup :=
    inferInstance
  apply IntermediateField.normal_iff_forall_map_le'.mpr
  rintro σ x ⟨a, ha, rfl⟩ τ
  exact
    (AlgEquiv.symm_apply_eq σ).mp
      (ha
        ⟨σ⁻¹ * τ * σ,
          Subgroup.Normal.conj_mem'
            (H := rationalCyclotomicTorsionClosure.toSubgroup)
            inferInstance τ.1 τ.2 σ⟩)

/-- The torsion-fixed cyclotomic field is Galois over `ℚ`. -/
noncomputable instance
    rationalCyclotomicTorsionFixedField_isGalois :
    IsGalois ℚ rationalCyclotomicTorsionFixedField :=
  isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

/-- The torsion-fixed subextension of the abelian rational cyclotomic
extension is itself abelian Galois. -/
noncomputable instance
    rationalCyclotomicTorsionFixedField_isAbelianGalois :
    IsAbelianGalois ℚ rationalCyclotomicTorsionFixedField :=
  IsAbelianGalois.tower_bot ℚ rationalCyclotomicTorsionFixedField
    rationalCyclotomicField

end KummerTheory
