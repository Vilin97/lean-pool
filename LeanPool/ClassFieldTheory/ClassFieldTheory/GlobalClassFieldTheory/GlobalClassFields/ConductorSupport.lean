/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLocalComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.OnePlaceNormKernel
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlace
/-!
# Support of the narrow finite conductor

There are two source statements in the ramification criterion:

* a prime belongs to the support of the narrow finite conductor exactly
  when its one-place finite local conductor exponent is nonzero;
* a finite abelian local extension is ramified exactly when its concrete
  local conductor exponent is nonzero.

The local conductor criterion itself is public in
`LocalClassFieldTheory.Finite.UnramifiedConductor`.  The global
reciprocity identity `N(C_L) ∩ K_vˣ = N(L_vˣ)` identifies the two
exponents for a global extension, yielding the global conductor-support
corollary.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

namespace ConductorialSubgroup

/-- A finite prime divides the narrow finite conductor exactly when its
finite local conductor exponent is nonzero. -/
theorem mem_narrowFiniteConductor_support_iff_narrowFiniteLocalConductorExponent_ne_zero
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ H.narrowFiniteConductor.support ↔
      H.narrowFiniteLocalConductorExponent v ≠ 0 := by
  rw [Finsupp.mem_support_iff,
    H.narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent v]

/-- A finite prime divides the narrow finite conductor exactly when its full
integral-unit class subgroup is not contained in the defining subgroup. -/
theorem
    mem_narrowFiniteConductor_support_iff_not_localHigherUnitClassSubgroup_zero_le
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ H.narrowFiniteConductor.support ↔
      ¬ RayClass.localHigherUnitClassSubgroup v 0 ≤ H.1 := by
  rw [H.mem_narrowFiniteConductor_support_iff_narrowFiniteLocalConductorExponent_ne_zero
      v,
    ne_eq,
    H.narrowFiniteLocalConductorExponent_eq_zero_iff v]

end ConductorialSubgroup

/-- At an unramified chosen completion, the zeroth local higher-unit
class subgroup consists of global idele-class norms. -/
theorem localHigherUnitClassSubgroup_zero_le_ideleClassNorm_range_of_chosenUnramified
    {L : Type}
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    RayClass.localHigherUnitClassSubgroup v 0 ≤
      (_root_.ideleClassNorm K L).range := by
  rintro _ ⟨x, hx, rfl⟩
  apply
    Reciprocity.finitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_chosenLocalNorm
      (K := K) (L := L) v x
  apply
    _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v hunram
  rw [← RayClass.localHigherUnitGroup_zero]
  exact hx

/-- Algebraic unramifiedness at a finite prime forces the zeroth local
higher-unit class subgroup into the global norm subgroup. -/
theorem localHigherUnitClassSubgroup_zero_le_ideleClassNorm_range_of_isUnramifiedAt
    {L : Type}
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v)).asIdeal) :
    RayClass.localHigherUnitClassSubgroup v 0 ≤
      (_root_.ideleClassNorm K L).range :=
  localHigherUnitClassSubgroup_zero_le_ideleClassNorm_range_of_chosenUnramified
    (K := K) (L := L) v
    (_root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := L) v hunram)

/-- Complete splitting at a finite prime puts the whole one-place idele
class image inside the global norm subgroup. -/
theorem finitePlaceIdeleClass_range_le_ideleClassNorm_range_of_splitsCompletely
    {L : Type}
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    (IdeleGroup.finitePlaceIdeleClass v).range ≤
      (_root_.ideleClassNorm K L).range := by
  rintro _ ⟨x, rfl⟩
  apply
    Reciprocity.finitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_chosenLocalNorm
      (K := K) (L := L) v x
  rw [
    _root_.chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely
      (K := K) (L := L) v hsplit]
  exact Subgroup.mem_top x

end GlobalClassFields
end GlobalClassFieldTheory
