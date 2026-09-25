/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianNormConductor
/-!
# Ramification support of abelian narrow finite norm conductors

For a finite abelian extension, the modulus constructed from the actual
local norm groups is zero exactly when every chosen finite completion is
unramified.  Its support therefore gives the exact chosen-completion
ramification locus, while the minimal narrow finite conductor has support
contained in that locus.
-/

@[expose] public section

open scoped NumberField
noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

open scoped Classical in
/-- The locally constructed norm modulus vanishes exactly when every
chosen completed extension is unramified. -/
theorem
    ideleClassNormDefiningModulus_eq_zero_iff_all_chosenFinitePlaces_unramified :
    ideleClassNormDefiningModulus (K := K) (L := L) = 0 ↔
      ∀ v : HeightOneSpectrum (𝓞 K),
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := L) v := by
  constructor
  · intro hzero v
    apply
      (ideleClassNormLocalHigherUnitExponent_eq_zero_iff_chosenFinitePlaceIsUnramified
        (K := K) (L := L) v).1
    rw [← ideleClassNormDefiningModulus_apply
      (K := K) (L := L) v, hzero]
    rfl
  · intro hunramified
    ext v
    rw [ideleClassNormDefiningModulus_apply,
      (ideleClassNormLocalHigherUnitExponent_eq_zero_iff_chosenFinitePlaceIsUnramified
        (K := K) (L := L) v).2
          (hunramified v)]
    rfl

open scoped Classical in
/-- The locally constructed norm modulus is nonzero exactly when some
chosen completed extension is ramified. -/
theorem
    ideleClassNormDefiningModulus_ne_zero_iff_exists_chosenFinitePlace_ramified :
    ideleClassNormDefiningModulus (K := K) (L := L) ≠ 0 ↔
      ∃ v : HeightOneSpectrum (𝓞 K),
        ¬ _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := L) v := by
  rw [ne_eq,
    ideleClassNormDefiningModulus_eq_zero_iff_all_chosenFinitePlaces_unramified]
  push Not
  rfl

open scoped Classical in
/-- Every prime in the minimal narrow finite norm conductor is ramified
in the chosen completed extension above that prime. -/
theorem
    mem_ideleClassNorm_narrowFiniteConductor_support_imp_chosenFinitePlace_ramified
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∈ (ideleClassNormNarrowFiniteConductor
        (K := K) (L := L)).support) :
    ¬ _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v := by
  have hvLocal :
      v ∈ (ideleClassNormDefiningModulus
        (K := K) (L := L)).support :=
    ideleClassNorm_narrowFiniteConductor_support_subset_normDefiningModulus_support
      (K := K) (L := L) hv
  exact
    (mem_ideleClassNormDefiningModulus_support_iff_not_chosenFinitePlaceIsUnramified
      (K := K) (L := L) v).1 hvLocal

open scoped Classical in
/-- If every chosen finite completion is unramified, then the minimal
narrow finite conductor of the actual idèle-class norm subgroup is zero. -/
theorem
    ideleClassNorm_narrowFiniteConductor_eq_zero_of_all_chosenFinitePlaces_unramified
    (hunramified :
      ∀ v : HeightOneSpectrum (𝓞 K),
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := L) v) :
    ideleClassNormNarrowFiniteConductor (K := K) (L := L) = 0 := by
  have hmodulus :
      ideleClassNormDefiningModulus
          (K := K) (L := L) = 0 :=
    (ideleClassNormDefiningModulus_eq_zero_iff_all_chosenFinitePlaces_unramified
      (K := K) (L := L)).2 hunramified
  apply le_antisymm
  · simpa only [hmodulus] using
      (ideleClassNorm_narrowFiniteConductor_le_normDefiningModulus
        (K := K) (L := L))
  · exact bot_le

end GlobalClassFields
end GlobalClassFieldTheory
