/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPowerBasis
/-!
# The completed theta-intertwining theorem: coefficient descent in the completed fixed field

Expansion in the direct-theta power basis turns Frobenius fixedness into
coefficientwise fixedness.  The coefficients therefore descend from the
completed unramified field to the original Laurent base.
-/

@[expose] public section

noncomputable
section

open scoped LaurentSeries Polynomial PowerSeries


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The completed base is a Laurent-series algebra through coefficient extension in the
fixed-field coefficient descent. -/
noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedFieldCoefficientDescentBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

/-- The completed level is a Laurent-series algebra through the base tower in the fixed-field
coefficient descent. -/
noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedFieldCoefficientDescentLevelAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  RingHom.toAlgebra
    ((algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)).comp
      (algebraMap F.residueField⸨X⸩
        (equalCharacteristicCompletedUnramifiedField F.residueField)))

local instance
    equalCharacteristicCompletedFrobeniusFixedFieldCoefficientDescentScalarTower
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- States the theorem `equalCharacteristicCompletedFrobenius_fixed_mem_adjoin_directTheta`. -/
theorem equalCharacteristicCompletedFrobenius_fixed_mem_adjoin_directTheta
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicCompletedLevelField F n)
    (hx : equalCharacteristicCompletedFrobeniusAlgEquiv F a n x = x) :
    x ∈ IntermediateField.adjoin F.residueField⸨X⸩
      ({(equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
        equalCharacteristicCompletedLevelField F n)} :
        Set (equalCharacteristicCompletedLevelField F n)) := by
  let A := equalCharacteristicCompletedUnramifiedField F.residueField
  let E := equalCharacteristicCompletedLevelField F n
  let phi := equalCharacteristicCompletedUnramifiedFrobenius F.residueField
  let delta := equalCharacteristicCompletedFrobeniusAlgEquiv F a n
  let y : E := equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n
  let pb : PowerBasis A E :=
    equalCharacteristicDirectThetaCompletedPowerBasis F a n
  let S : IntermediateField F.residueField⸨X⸩ E :=
    IntermediateField.adjoin F.residueField⸨X⸩ ({y} : Set E)
  have hdeltaCoeff (c : A) :
      delta (algebraMap A E c) = algebraMap A E (phi c) := by
    change equalCharacteristicCompletedFrobeniusLiftEquiv F n a⁻¹
        (algebraMap A E c) = algebraMap A E
          (equalCharacteristicCompletedUnramifiedFrobenius F.residueField c)
    exact equalCharacteristicCompletedFrobeniusLiftEquiv_algebraMap F n a⁻¹ c
  have hdeltaY : delta y = y := by
    change equalCharacteristicCompletedFrobeniusAlgEquiv F a n
        (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n : E) = _
    rw [equalCharacteristicCompletedFrobeniusAlgEquiv_apply]
    exact equalCharacteristicCompletedFrobeniusLift_directThetaFixed F a n
  have hdeltaBasis (i : Fin pb.dim) :
      delta (pb.basis i) = pb.basis i := by
    rw [pb.coe_basis, map_pow, show pb.gen = y by
      exact equalCharacteristicDirectThetaCompletedPowerBasis_gen F a n, hdeltaY]
  have hsemisum :
      (∑ i : Fin pb.dim, phi (pb.basis.repr x i) • pb.basis i) = x := by
    calc
      (∑ i : Fin pb.dim, phi (pb.basis.repr x i) • pb.basis i) =
          delta (∑ i : Fin pb.dim, pb.basis.repr x i • pb.basis i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Algebra.smul_def, Algebra.smul_def, map_mul,
          hdeltaCoeff, hdeltaBasis]
      _ = delta x := by rw [pb.basis.sum_repr]
      _ = x := hx
  have hcoeff (i : Fin pb.dim) :
      phi (pb.basis.repr x i) = pb.basis.repr x i := by
    have hrepr := congrArg pb.basis.repr hsemisum
    have hi := congrArg (fun c ↦ c i) hrepr
    simp only [map_sum, map_smul, Module.Basis.repr_self,
      Finsupp.smul_single', mul_one] at hi
    rw [Finsupp.finsetSum_apply] at hi
    rw [Finset.sum_eq_single i] at hi
    · simpa only [Finsupp.single_eq_same] using hi
    · intro j hj hji
      exact Finsupp.single_eq_of_ne hji.symm
    · simp
  change x ∈ S
  rw [← pb.basis.sum_repr x]
  apply S.sum_mem
  intro i hi
  rw [pb.coe_basis, Algebra.smul_def]
  apply S.mul_mem
  · rcases
      (equalCharacteristicCompletedUnramifiedFrobenius_fixed_iff
        (k := F.residueField) (pb.basis.repr x i)).1 (hcoeff i) with
      ⟨c, hc⟩
    change algebraMap A E (pb.basis.repr x i) ∈ S
    rw [← hc]
    exact S.algebraMap_mem c
  · have hgen : pb.gen ∈ S := by
      rw [show pb.gen = y by
        exact equalCharacteristicDirectThetaCompletedPowerBasis_gen F a n]
      exact IntermediateField.mem_adjoin_simple_self F.residueField⸨X⸩ y
    simpa using S.pow_mem hgen i.val

end EqualCharacteristic
end LubinTate
