/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayArtinModulusProjection
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayArtin
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealModulusProjection
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.PrimeGeneration
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayFrobeniusRigidity
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
/-!
# Existence of a modulus-compatible ray class field embedding

Reducing the modulus yields an embedding of ray class field realizations
that intertwines their Artin maps.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

private theorem rayArtin_prime_eq_arithmeticPrimeArtin
    {K : Type} [Field K] [NumberField K]
    {m : RayClassModulus K} (R : RayClassFieldRealization K m)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    R.rayArtin (rayClassOfFinitePrime m v hv) =
      GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := R.extension) v := by
  let w₀ := _root_.chosenFinitePlaceExtension (L := R.extension) v
  let w := _root_.finitePlaceExtensionCentre (K := K) (L := R.extension) v w₀
  have hw : w.asIdeal.LiesOver v.asIdeal :=
    _root_.finitePlaceExtensionCentre_liesOver
      (K := K) (L := R.extension) v w₀
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    (R.unramifiedOutsideModulus.1 v hv) w.asIdeal inferInstance hw
  calc
    R.rayArtin (rayClassOfFinitePrime m v hv) =
        arithmeticFrobeniusAt (K := K) w := R.artin_frobenius v hv w hw
    _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := R.extension) v :=
      (GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
        (K := K) (L := R.extension) v w hw hunram).symm

private theorem rayClassFieldRealization_norm_range
    {K : Type} [Field K] [NumberField K]
    {m : RayClassModulus K} (R : RayClassFieldRealization K m) :
    (_root_.ideleClassNorm K R.extension).range =
      (GlobalClassFieldComparison.rayClassModulusToOriginal K m).congruenceSubgroup := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let e : RayClass.RayClassGroup m' ≃*
      (R.extension ≃ₐ[K] R.extension) :=
    (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm.trans
      R.artinEquiv
  apply GlobalClassFieldTheory.GlobalClassFields.rayModulus_normSubgroup_eq_of_arithmeticPrimeArtinEquiv
    m' e
  intro v hv
  have hvm : v ∉ m.finitePart.support := hv
  calc
    e (QuotientGroup.mk' m'.congruenceSubgroup
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
          (IdeleGroup.finitePrimeIdele v))) =
        R.rayArtin (rayClassOfFinitePrime m v hvm) := by
      change R.artinEquiv
        ((GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm
          (QuotientGroup.mk' m'.congruenceSubgroup
            (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
              (IdeleGroup.finitePrimeIdele v)))) = _
      rw [← GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime K m v hvm]
      exact congrArg R.artinEquiv
        ((GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm_apply_apply _)
    _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := R.extension) v :=
      rayArtin_prime_eq_arithmeticPrimeArtin R v hvm

/-- A reduction of the modulus yields an embedding of any two ray-class-field
realizations, and this embedding intertwines their Artin maps. -/
theorem exists_rayArtin_modulusProjection
    {K : Type} [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n)
    (Rm : RayClassFieldRealization K m)
    (Rn : RayClassFieldRealization K n) :
    ∃ f : Rm.extension →ₐ[K] Rn.extension,
      ∀ (x : RayClassGroup n) (y : Rm.extension),
        Rn.rayArtin x (f y) =
          f (Rm.rayArtin (rayClassIdealModulusProjection K hmn x) y) := by
  have hnorm : (_root_.ideleClassNorm K Rn.extension).range ≤
      (_root_.ideleClassNorm K Rm.extension).range := by
    rw [rayClassFieldRealization_norm_range Rn,
      rayClassFieldRealization_norm_range Rm]
    exact RayClass.Modulus.congruenceSubgroup_antitone hmn
  obtain ⟨f⟩ :=
    GlobalClassFieldTheory.GlobalClassFields.finiteAbelianExtension_nonempty_algHom_of_normRange_le
      (K := K) Rm.extension Rn.extension hnorm
  exact ⟨f, rayArtin_modulusProjection hmn Rm Rn f⟩

end ClassFieldTheory
