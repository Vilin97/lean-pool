/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteLevelCore
/-!
# Tensor comparison and injectivity at finite rational levels

This endpoint leaf contains the tensor-unflattening comparisons and the
resulting injectivity theorems.  The finite-level normal-closure maps and
their tower compatibility live in the reusable core leaf.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CyclicCohomology

attribute [local instance]
  relativeAdeleRingIntermediateAlgebra

local instance rationalFiniteLevelEndpointNumberField
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] : NumberField K :=
  NumberField.of_module_finite ℚ K
/-- Rational relative-adele scalar extension agrees with unflattening
the corresponding fixed-bottom tensor tower. -/
theorem rationalRelativeAdeleEmbedding_unflatten
    {K N : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    (hKN : K ≤ N)
    (a : RelativeAdeleRing ℚ K) :
    letI : Algebra K N :=
      (IntermediateField.inclusion hKN).toRingHom.toAlgebra
    letI : IsScalarTower ℚ K N :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional K N :=
      FiniteDimensional.right ℚ K N
    towerRelativeAdeleUnflatten ℚ K N
        (RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) a) =
      a ⊗ₜ[K] (1 : N) := by
  let : Algebra K N :=
    (IntermediateField.inclusion hKN).toRingHom.toAlgebra
  let : IsScalarTower ℚ K N :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional K N :=
    FiniteDimensional.right ℚ K N
  have hflatten :
      towerRelativeAdeleFlatten ℚ K N
          (towerRelativeAdeleUnflatten ℚ K N
            (RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
              (IntermediateField.inclusion hKN) a)) =
        RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) a :=
    (towerRelativeAdeleRingEquiv ℚ K N).apply_symm_apply
      (RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
        (IntermediateField.inclusion hKN) a)
  apply
    (towerRelativeAdeleRingEquiv ℚ K N).injective
  change
    towerRelativeAdeleFlatten ℚ K N
        (towerRelativeAdeleUnflatten ℚ K N
          (RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
            (IntermediateField.inclusion hKN) a)) =
      towerRelativeAdeleFlatten ℚ K N
        (a ⊗ₜ[K] (1 : N))
  rw [hflatten]
  rw [towerRelativeAdeleFlatten_tmul]
  simp only [map_one, mul_one]
  rfl

/-- Rational relative-idele scalar extension agrees with unflattening
the corresponding fixed-bottom tensor tower. -/
theorem rationalRelativeIdeleEmbedding_unflatten
    {K N : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    (hKN : K ≤ N)
    (a : RelativeIdeleGroup ℚ K) :
    letI : Algebra K N :=
      (IntermediateField.inclusion hKN).toRingHom.toAlgebra
    letI : IsScalarTower ℚ K N :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional K N :=
      FiniteDimensional.right ℚ K N
    letI : Algebra K (RelativeAdeleRing ℚ K) :=
      relativeAdeleRingIntermediateAlgebra ℚ K
    (towerRelativeIdeleEquiv ℚ K N).symm
        (RelativeIdeleGroup.ideleEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) a) =
      (Units.map
        (@Algebra.TensorProduct.includeLeft
          K K (RelativeAdeleRing ℚ K) N
          inferInstance inferInstance
          (relativeAdeleRingIntermediateAlgebra ℚ K)
          inferInstance
          ((IntermediateField.inclusion hKN).toRingHom.toAlgebra)
          inferInstance
          (relativeAdeleRingIntermediateAlgebra ℚ K)
          (@smulCommClass_self K (RelativeAdeleRing ℚ K) inferInstance
            (@Algebra.toModule K (RelativeAdeleRing ℚ K) inferInstance inferInstance
              (relativeAdeleRingIntermediateAlgebra ℚ
                K)).toDistribMulAction.toMulAction)).toMonoidHom a :
        TowerRelativeIdeleGroup ℚ K N) := by
  let : Algebra K N :=
    (IntermediateField.inclusion hKN).toRingHom.toAlgebra
  let : IsScalarTower ℚ K N :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional K N :=
    FiniteDimensional.right ℚ K N
  let : Algebra K (RelativeAdeleRing ℚ K) :=
    relativeAdeleRingIntermediateAlgebra ℚ K
  apply Units.ext
  exact
    rationalRelativeAdeleEmbedding_unflatten
      hKN (a : RelativeAdeleRing ℚ K)

/-- Rational relative idele-class scalar extension agrees with the
fixed-bottom tower base-change equivalence. -/
theorem
    rationalRelativeIdeleClassEmbedding_towerBaseChange
    {K N : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    (hKN : K ≤ N)
    (c : RelativeIdeleGroup.ClassGroup ℚ K) :
    letI : Algebra K N :=
      (IntermediateField.inclusion hKN).toRingHom.toAlgebra
    letI : IsScalarTower ℚ K N :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional K N :=
      FiniteDimensional.right ℚ K N
    towerRelativeIdeleClassBaseChangeMulEquiv ℚ K N
        ((TowerRelativeIdeleGroup.classGroupEquiv ℚ K N).symm
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
            (IntermediateField.inclusion hKN) c)) =
      RelativeIdeleGroup.classInclusion K N
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) c) := by
  let : Algebra K N :=
    (IntermediateField.inclusion hKN).toRingHom.toAlgebra
  let : IsScalarTower ℚ K N :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional K N :=
    FiniteDimensional.right ℚ K N
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K N)
        (towerRelativeIdeleBaseChangeMulEquiv ℚ K N
          ((towerRelativeIdeleEquiv ℚ K N).symm
            (RelativeIdeleGroup.ideleEmbedding (K := ℚ) (L := K) (M := N)
              (IntermediateField.inclusion hKN) a))) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K N)
        (RelativeIdeleGroup.inclusion K N
          (relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K) a))
  apply congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K N))
  rw [rationalRelativeIdeleEmbedding_unflatten hKN a]
  exact
    towerRelativeIdeleBaseChangeMulEquiv_includeLeft
      ℚ K N a

/-- Scalar extension between finite rational relative idele class groups
is injective. -/
theorem rationalRelativeIdeleClassEmbedding_injective
    {K N : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    (hKN : K ≤ N) :
    Function.Injective
      (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
        (IntermediateField.inclusion hKN)) := by
  let : Algebra K N :=
    (IntermediateField.inclusion hKN).toRingHom.toAlgebra
  let : IsScalarTower ℚ K N :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional K N :=
    FiniteDimensional.right ℚ K N
  intro a b hab
  have htransport :=
    congrArg
      (fun c : RelativeIdeleGroup.ClassGroup ℚ N =>
        towerRelativeIdeleClassBaseChangeMulEquiv ℚ K N
          ((TowerRelativeIdeleGroup.classGroupEquiv ℚ K N).symm c))
      hab
  rw [rationalRelativeIdeleClassEmbedding_towerBaseChange hKN a,
    rationalRelativeIdeleClassEmbedding_towerBaseChange hKN b]
      at htransport
  apply
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := K)).injective
  exact
    RelativeIdeleGroup.classInclusion_injective K N htransport

/-- Each finite-level relative idele class group embeds into the rational
idele-class direct limit. -/
theorem rationalRelativeIdeleClassToDirectLimit_injective
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    Function.Injective
      (rationalRelativeIdeleClassToDirectLimit E) := by
  exact
    DirectLimit.mk_injective
      (F := fun E :
        FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) =>
          RelativeIdeleGroup.ClassGroup ℚ E)
      (f := fun _ _ h =>
        rationalRelativeIdeleClassTransition h)
      (fun _ _ h =>
        rationalRelativeIdeleClassEmbedding_injective h)
      E

end Reciprocity
end GlobalClassFieldTheory
