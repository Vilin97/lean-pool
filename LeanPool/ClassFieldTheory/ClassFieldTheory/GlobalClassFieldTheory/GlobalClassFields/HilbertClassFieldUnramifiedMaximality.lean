/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.EverywhereUnramifiedTower
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.Transport
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.BigActual
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.SmallActual
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.BigOriginal
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.SmallOriginal
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteLocalGlobalArtinCompatibility
/-!
# Unramifiedness and maximality of Hilbert class fields

The selected big and small Hilbert class fields have the prescribed
idele-class norm ranges.  Exact local--global narrow finite conductor
compatibility therefore turns the vanishing of their intrinsic finite conductors into actual
unramifiedness at every finite prime.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Any actual finite abelian realization of the intrinsic big-Hilbert
norm subgroup is unramified at every finite prime. -/
theorem isUnramifiedAtFinitePlaces_of_normRange_eq_bigHilbertNormSubgroup
    (hnorm :
      (_root_.ideleClassNorm K L).range =
        bigHilbertClassFieldNormSubgroup (K := K)) :
    IsUnramifiedAtFinitePlaces K L := by
  apply
    (ideleClassNorm_narrowFiniteConductor_eq_zero_iff_all_finitePlaces_unramified
      (K := K) (L := L)).1
  change
    (ideleClassNormConductorialSubgroup
      (K := K) (L := L)).narrowFiniteConductor = 0
  have hsub :
      ideleClassNormConductorialSubgroup (K := K) (L := L) =
        bigHilbertClassFieldConductorialSubgroup (K := K) :=
    Subtype.ext hnorm
  rw [hsub]
  exact bigHilbertClassField_narrowFiniteConductor (K := K)

/-- Any actual finite abelian realization of the intrinsic
small-Hilbert norm subgroup is unramified at every finite prime. -/
theorem isUnramifiedAtFinitePlaces_of_normRange_eq_smallHilbertNormSubgroup
    (hnorm :
      (_root_.ideleClassNorm K L).range =
        smallHilbertClassFieldNormSubgroup (K := K)) :
    IsUnramifiedAtFinitePlaces K L := by
  apply
    (ideleClassNorm_narrowFiniteConductor_eq_zero_iff_all_finitePlaces_unramified
      (K := K) (L := L)).1
  change
    (ideleClassNormConductorialSubgroup
      (K := K) (L := L)).narrowFiniteConductor = 0
  have hsub :
      ideleClassNormConductorialSubgroup (K := K) (L := L) =
        smallHilbertClassFieldConductorialSubgroup (K := K) :=
    Subtype.ext hnorm
  rw [hsub]
  exact smallHilbertClassField_narrowFiniteConductor (K := K)

/-- Any actual finite abelian realization of the intrinsic
small-Hilbert norm subgroup splits every infinite place completely. -/
theorem isUnramifiedAtInfinitePlaces_of_normRange_eq_smallHilbertNormSubgroup
    (hnorm :
      (_root_.ideleClassNorm K L).range =
        smallHilbertClassFieldNormSubgroup (K := K)) :
    IsUnramifiedAtInfinitePlaces K L := by
  apply
    (infiniteTensorNormSubgroups_eq_top_iff_isUnramifiedAtInfinitePlaces
      (K := K) (L := L)).1
  intro v
  apply top_unique
  intro x _hx
  apply
    (Reciprocity.infinitePlaceIdeleClass_mem_ideleClassNorm_range_iff
        (K := K) (L := L) v x).1
  have hxSmall :
      IdeleGroup.infinitePlaceIdeleClass v x ∈
        smallHilbertClassFieldNormSubgroup (K := K) := by
    refine
      ⟨IdeleGroup.infinitePlaceIdele v x, ?_, rfl⟩
    apply Subgroup.mem_sup_left
    refine
      (FiniteIdeleGroup.mem_integralSubgroup_iff
        (IdeleGroup.infinitePlaceIdele v x).2).2 ?_
    intro w
    exact
      (IdeleGroup.infinitePlaceIdele_finiteComponent v w x).symm ▸
        (w.adicCompletionIntegers K).units.one_mem
  rw [hnorm]
  exact hxSmall

/-- Any actual finite abelian realization of the intrinsic
small-Hilbert norm subgroup is everywhere unramified. -/
theorem isEverywhereUnramified_of_normRange_eq_smallHilbertNormSubgroup
    (hnorm :
      (_root_.ideleClassNorm K L).range =
        smallHilbertClassFieldNormSubgroup (K := K)) :
    IsEverywhereUnramified K L where
  finitePlaces :=
    isUnramifiedAtFinitePlaces_of_normRange_eq_smallHilbertNormSubgroup
      hnorm
  infinitePlaces :=
    isUnramifiedAtInfinitePlaces_of_normRange_eq_smallHilbertNormSubgroup
      hnorm

omit [FiniteDimensional K L] [IsAbelianGalois K L] in
private theorem ramifiedBaseFinitePlaces_eq_empty_of_isUnramifiedAtFinitePlaces
    (hunramified : IsUnramifiedAtFinitePlaces K L) :
    _root_.ramifiedBaseFinitePlaces (K := K) (L := L) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨P, _hP, hP⟩ :=
    (_root_.mem_ramifiedBaseFinitePlaces_iff
      (K := K) (L := L) v).1 hv
  exact hP (hunramified P)

variable (K : Type) [Field K] [NumberField K]

/-- The selected big Hilbert class field is unramified at every finite
prime of the original number field. -/
theorem bigHilbertClassField_isUnramifiedAtFinitePlaces :
    IsUnramifiedAtFinitePlaces K (bigHilbertClassField K) := by
  apply
    isUnramifiedAtFinitePlaces_of_normRange_eq_bigHilbertNormSubgroup
      (K := K) (L := bigHilbertClassField K)
  exact bigHilbertClassField_ideleClassNorm_range_over_original

/-- The selected small Hilbert class field is unramified at every
finite prime of the original number field. -/
theorem smallHilbertClassField_isUnramifiedAtFinitePlaces :
    IsUnramifiedAtFinitePlaces K (smallHilbertClassField K) := by
  apply
    isUnramifiedAtFinitePlaces_of_normRange_eq_smallHilbertNormSubgroup
      (K := K) (L := smallHilbertClassField K)
  exact smallHilbertClassField_ideleClassNorm_range_over_original

/-- Every infinite place splits completely in the selected small
Hilbert class field.  Indeed, an idele supported at an infinite place
is integral at every finite place, hence belongs to the intrinsic
small-Hilbert norm subgroup; infinite-place local--global compatibility
then identifies its component with an actual local norm. -/
theorem smallHilbertClassField_isUnramifiedAtInfinitePlaces :
    IsUnramifiedAtInfinitePlaces K (smallHilbertClassField K) := by
  apply
    isUnramifiedAtInfinitePlaces_of_normRange_eq_smallHilbertNormSubgroup
      (K := K) (L := smallHilbertClassField K)
  exact smallHilbertClassField_ideleClassNorm_range_over_original

/-- The selected small Hilbert class field is everywhere unramified
over the original number field. -/
theorem smallHilbertClassField_isEverywhereUnramified :
    IsEverywhereUnramified K (smallHilbertClassField K) :=
  isEverywhereUnramified_of_normRange_eq_smallHilbertNormSubgroup
    (smallHilbertClassField_ideleClassNorm_range_over_original
      (K := K))

/-- Equivalently, the actual finite ramification set of the selected
big Hilbert class field is empty. -/
theorem bigHilbertClassField_ramifiedBaseFinitePlaces_eq_empty :
    _root_.ramifiedBaseFinitePlaces
        (K := K) (L := bigHilbertClassField K) = ∅ := by
  exact
    ramifiedBaseFinitePlaces_eq_empty_of_isUnramifiedAtFinitePlaces
      (K := K) (L := bigHilbertClassField K)
      (bigHilbertClassField_isUnramifiedAtFinitePlaces K)

/-- Equivalently, the actual finite ramification set of the selected
small Hilbert class field is empty. -/
theorem smallHilbertClassField_ramifiedBaseFinitePlaces_eq_empty :
    _root_.ramifiedBaseFinitePlaces
        (K := K) (L := smallHilbertClassField K) = ∅ := by
  exact
    ramifiedBaseFinitePlaces_eq_empty_of_isUnramifiedAtFinitePlaces
      (K := K) (L := smallHilbertClassField K)
      (smallHilbertClassField_isUnramifiedAtFinitePlaces K)

end GlobalClassFields
end GlobalClassFieldTheory
