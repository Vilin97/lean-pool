/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFiniteSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringTensor
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportScalarTensor

import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Domain

/-!
# Localization of the degree-graded ring

Let `P̂` be the subring of principal elements and let `RV̂` be the degree-graded ring.
Using the tensor decomposition `RV̂ ≃ P̂ ⊗[K] K(ℝ^{≤ 0})`, extension of the principal
factor to `Frac(P̂)` gives the canonical map

`RV̂ → Frac(P̂)(ℝ^{≤ 0})`.

The two evaluation theorems identify its restrictions to the finite-support and principal graded
factors. They are the concrete form of the localization identification used in LM24, Corollary
6.3.6.
-/

open scoped HahnSeries TensorProduct

universe v

namespace Berarducci

public noncomputable section

open HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- The coefficient-field algebra structure on principal-subring fractions used in localization. -/
local instance principalSubringFractionAlgebraLocalization :
    Algebra K (PrincipalSubringFractionField K) :=
  principalSubringFractionAlgebra K

variable (K) in
/-- Extend the principal factor of `P̂ ⊗[K] K(ℝ^{≤ 0})` to `Frac(P̂)` while leaving the
finite-support factor unchanged. -/
def principalSubringTensorToFractionTensor :
    PrincipalSubring K ⊗[K] FiniteSupportRing (K := K) →ₐ[K]
      PrincipalSubringFractionField K ⊗[K] FiniteSupportRing (K := K) := by
  letI : Algebra (PrincipalSubring K)
      (PrincipalSubringFractionField K) :=
    principalSubringFractionSelfAlgebra K
  letI : IsScalarTower K (PrincipalSubring K)
      (PrincipalSubringFractionField K) :=
    principalSubringFraction_isScalarTower K
  exact Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom K (PrincipalSubring K)
      (PrincipalSubringFractionField K))
    (AlgHom.id K (FiniteSupportRing (K := K)))

/-- Extension of the principal tensor factor sends a pure tensor to the tensor of the canonical
fraction-field image and the unchanged finite-support factor. -/
@[simp]
theorem principalSubringTensorToFractionTensor_tmul
    (x : PrincipalSubring K) (p : FiniteSupportRing (K := K)) :
    principalSubringTensorToFractionTensor K (x ⊗ₜ p) =
      principalSubringToFraction K x ⊗ₜ p := by
  rw [principalSubringTensorToFractionTensor, Algebra.TensorProduct.map_tmul]
  congr 1
  exact (principalSubringToFraction_apply x).symm

variable (K) in
/-- The canonical map from the degree-graded ring `RV̂` to finite-support series over
`Frac(P̂)`. -/
def principalSubringLocalizationMap :
    DegreeGraded K →+*
      PrincipalSubringFractionFiniteSupportRing K := by
  let e := HahnSeries.Nonpositive.finiteSupportScalarTensorEquiv
    (G := ℝ) (K := K) (L := PrincipalSubringFractionField K)
  let f := principalSubringTensorToFractionTensor K
  let g := (principalSubringTensorEquiv K).symm
  exact e.toRingEquiv.toRingHom.comp (f.toRingHom.comp g.toRingEquiv.toRingHom)

/-- The graded localization map is the composite of the inverse tensor decomposition, extension
of the principal factor to its fraction field, and finite-support scalar base change. -/
theorem principalSubringLocalizationMap_apply (x : DegreeGraded K) :
    principalSubringLocalizationMap K x =
      HahnSeries.Nonpositive.finiteSupportScalarTensorEquiv
        (G := ℝ) (K := K) (L := PrincipalSubringFractionField K)
        (principalSubringTensorToFractionTensor K
          ((principalSubringTensorEquiv K).symm x)) :=
  (rfl)

/-- The graded localization map restricts to coefficientwise scalar extension on the
finite-support factor. -/
theorem principalSubringLocalizationMap_finiteSupport (p : FiniteSupportRing (K := K)) :
    principalSubringLocalizationMap K
        (finiteSupportGradedEmbedding K p) =
      principalSubringFractionScalarExtension K p := by
  rw [principalSubringLocalizationMap_apply,
    principalSubringTensorEquiv_symm_finiteSupportGradedEmbedding,
    principalSubringTensorToFractionTensor_tmul,
    HahnSeries.Nonpositive.finiteSupportScalarTensorEquiv_tmul]
  rw [(principalSubringToFraction K).map_one,
    (HahnSeries.Nonpositive.finiteSupportScalarHom
      (G := ℝ) (K := PrincipalSubringFractionField K)).map_one,
    one_mul]
  apply HahnSeries.Nonpositive.finiteSupportFinsuppEquiv.injective
  ext g
  rw [HahnSeries.Nonpositive.finiteSupportFinsuppEquiv_apply,
    HahnSeries.Nonpositive.finiteSupportFinsuppEquiv_apply]
  rw [HahnSeries.Nonpositive.finiteSupportScalarExtension_coeff,
    principalSubringFractionScalarExtension_coeff]
  rw [principalSubringFraction_algebraMap_apply,
    principalSubringFractionCoefficientMap_apply]

/-- The graded localization map sends the principal factor to the corresponding constant series
over `Frac(P̂)`. -/
@[simp]
theorem principalSubringLocalizationMap_principal (x : PrincipalSubring K) :
    principalSubringLocalizationMap K
        (principalSubringEmbedding K x) =
      HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ)
        (principalSubringToFraction K x) := by
  rw [principalSubringLocalizationMap_apply,
    principalSubringTensorEquiv_symm_principalGradedEmbedding,
    principalSubringTensorToFractionTensor_tmul,
    HahnSeries.Nonpositive.finiteSupportScalarTensorEquiv_tmul]
  change HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ)
      (principalSubringToFraction K x) *
        HahnSeries.Nonpositive.finiteSupportScalarExtension 1 = _
  rw [map_one, mul_one]

variable (K) in
/-- The submonoid of nonzero principal graded factors inverted by the graded localization map. -/
def principalSubringDenominators :
    Submonoid (DegreeGraded K) :=
  (nonZeroDivisors (PrincipalSubring K)).map
    (principalSubringEmbedding K).toRingHom

/-- A graded element is a localization denominator exactly when it is the image of a nonzero
principal graded element. -/
theorem mem_principalGradedDenominators_iff (x : DegreeGraded K) :
    x ∈ principalSubringDenominators K ↔
      ∃ y : PrincipalSubring K,
        y ≠ 0 ∧ principalSubringEmbedding K y = x := by
  rw [principalSubringDenominators]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, (mem_nonZeroDivisors_iff_ne_zero.mp hy), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, mem_nonZeroDivisors_iff_ne_zero.mpr hy, rfl⟩

/-- The canonical algebra structure induced by the graded localization map. -/
noncomputable instance principalSubringLocalizationAlgebra :
    Algebra (DegreeGraded K)
      (PrincipalSubringFractionFiniteSupportRing K) :=
  (principalSubringLocalizationMap K).toAlgebra

/-- The algebra map of the graded localization is the explicitly constructed localization map. -/
@[simp]
theorem principalSubringLocalization_algebraMap_apply (x : DegreeGraded K) :
    algebraMap (DegreeGraded K)
        (PrincipalSubringFractionFiniteSupportRing K) x =
      principalSubringLocalizationMap K x :=
  (rfl)

variable (K) in
private abbrev PrincipalTensor :=
  PrincipalSubring K ⊗[K] FiniteSupportRing (K := K)

variable (K) in
private abbrev FractionTensor :=
  PrincipalSubringFractionField K ⊗[K] FiniteSupportRing (K := K)

/-- The principal-subring algebra structure on its fraction field used in tensor localization. -/
local instance principalSubringFractionSelfAlgebraLocalization :
    Algebra (PrincipalSubring K) (PrincipalSubringFractionField K) :=
  principalSubringFractionSelfAlgebra K

local instance principalSubringFractionScalarTowerLocalization :
    IsScalarTower K (PrincipalSubring K)
      (PrincipalSubringFractionField K) :=
  principalSubringFraction_isScalarTower K

local instance principalSubringFractionIsLocalizationLocalization :
    IsFractionRing (PrincipalSubring K)
      (PrincipalSubringFractionField K) :=
  IsFractionRing.of_algEquiv (principalSubringFractionAlgEquiv K)

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free in
variable (K) in
/-- Extending the principal tensor factor to `Frac(P̂)` is injective. -/
theorem principalSubringTensorToFractionTensor_injective :
    Function.Injective (principalSubringTensorToFractionTensor K) := by
  change Function.Injective
    (TensorProduct.map
      (IsScalarTower.toAlgHom K (PrincipalSubring K)
        (PrincipalSubringFractionField K)).toLinearMap
      (AlgHom.id K (FiniteSupportRing (K := K))).toLinearMap)
  apply TensorProduct.map_injective_of_flat_flat
  · intro x y hxy
    apply principalSubringToFraction_injective K
    calc
      principalSubringToFraction K x =
          (IsScalarTower.toAlgHom K (PrincipalSubring K)
            (PrincipalSubringFractionField K)) x :=
        principalSubringToFraction_apply x
      _ = (IsScalarTower.toAlgHom K (PrincipalSubring K)
            (PrincipalSubringFractionField K)) y := hxy
      _ = principalSubringToFraction K y :=
        (principalSubringToFraction_apply y).symm
  · exact Function.injective_id

/-- The canonical map from the degree-graded ring `RV̂` to its principal localization is
injective. -/
theorem principalSubringLocalizationMap_injective {x y : DegreeGraded K}
    (hxy : principalSubringLocalizationMap K x =
      principalSubringLocalizationMap K y) :
    x = y := by
  apply (principalSubringTensorEquiv K).symm.injective
  apply principalSubringTensorToFractionTensor_injective K
  apply (HahnSeries.Nonpositive.finiteSupportScalarTensorEquiv
    (G := ℝ) (K := K) (L := PrincipalSubringFractionField K)).injective
  calc
    _ = principalSubringLocalizationMap K x :=
      (principalSubringLocalizationMap_apply x).symm
    _ = principalSubringLocalizationMap K y := hxy
    _ = _ := principalSubringLocalizationMap_apply y

private instance principalTensorFractionTensorAlgebra :
    Algebra (PrincipalTensor K) (FractionTensor K) :=
  (principalSubringTensorToFractionTensor K).toAlgebra

private instance principalTensorPrincipalAlgebra :
    Algebra (PrincipalSubring K) (PrincipalTensor K) :=
  inferInstance

private instance fractionTensorPrincipalAlgebra :
    Algebra (PrincipalSubring K) (FractionTensor K) :=
  inferInstance

private instance principalTensorPrincipalSMul :
    SMul (PrincipalSubring K) (PrincipalTensor K) :=
  principalTensorPrincipalAlgebra.toSMul

private instance fractionTensorPrincipalSMul :
    SMul (PrincipalSubring K) (FractionTensor K) :=
  fractionTensorPrincipalAlgebra.toSMul

private instance principalTensorFractionTensorTower :
    IsScalarTower (PrincipalSubring K)
      (PrincipalTensor K) (FractionTensor K) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change principalSubringTensorToFractionTensor K
      (algebraMap (PrincipalSubring K) (PrincipalTensor K) x) =
    algebraMap (PrincipalSubring K) (FractionTensor K) x
  change principalSubringTensorToFractionTensor K (x ⊗ₜ 1) = _
  rw [principalSubringTensorToFractionTensor_tmul]
  simp

variable (K) in
private def principalTensorDenominators : Submonoid (PrincipalTensor K) :=
  Algebra.algebraMapSubmonoid (PrincipalTensor K)
    (nonZeroDivisors (PrincipalSubring K))

private instance fractionTensorIsLocalization :
    IsLocalization (principalTensorDenominators K) (FractionTensor K) := by
  apply IsLocalization.tensorProduct_tensorProduct K
    (FiniteSupportRing (K := K))
    (nonZeroDivisors (PrincipalSubring K))
    (PrincipalSubringFractionField K)
  ext p
  change principalSubringTensorToFractionTensor K (1 ⊗ₜ p) = 1 ⊗ₜ p
  rw [principalSubringTensorToFractionTensor_tmul]
  simp

variable (K) in
private theorem principalSubringDenominators_eq_map :
    principalSubringDenominators K =
      (principalTensorDenominators K).map
        (principalSubringTensorEquiv K).toRingEquiv.toMonoidHom := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨algebraMap (PrincipalSubring K) (PrincipalTensor K) x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · change principalSubringTensorEquiv K (x ⊗ₜ 1) =
        principalSubringEmbedding K x
      exact principalSubringTensorEquiv_tmul_one x
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    change principalSubringEmbedding K x =
      principalSubringTensorEquiv K (x ⊗ₜ 1)
    exact (principalSubringTensorEquiv_tmul_one x).symm

private instance gradedFractionTensorAlgebra :
    Algebra (DegreeGraded K) (FractionTensor K) :=
  ((algebraMap (PrincipalTensor K) (FractionTensor K)).comp
    (principalSubringTensorEquiv K).symm.toRingEquiv.toRingHom).toAlgebra

private instance gradedFractionTensorIsLocalization :
    IsLocalization (principalSubringDenominators K) (FractionTensor K) := by
  rw [principalSubringDenominators_eq_map]
  exact IsLocalization.isLocalization_of_base_ringEquiv
    (principalTensorDenominators K) (FractionTensor K)
      (principalSubringTensorEquiv K).toRingEquiv

variable (K) in
private def fractionTensorFiniteSupportAlgEquiv :
    FractionTensor K ≃ₐ[DegreeGraded K]
      PrincipalSubringFractionFiniteSupportRing K where
  toRingEquiv :=
    (HahnSeries.Nonpositive.finiteSupportScalarTensorEquiv
      (G := ℝ) (K := K) (L := PrincipalSubringFractionField K)).toRingEquiv
  commutes' _ := rfl

/-- Finite-support series over `Frac(P̂)` are the localization of the degree-graded ring `RV̂` at
the nonzero principal graded factors. -/
noncomputable instance principalSubringLocalizationIsLocalization :
    IsLocalization (principalSubringDenominators K)
      (PrincipalSubringFractionFiniteSupportRing K) :=
  IsLocalization.isLocalization_of_algEquiv
    (principalSubringDenominators K)
    (fractionTensorFiniteSupportAlgEquiv K)

/-- Every element of the graded localization has a numerator in `RV̂` and a nonzero principal
graded denominator. The equation is the denominator-cleared form of `z = x / d`. -/
theorem principalSubringLocalization_exists_mul_principalDenominator
    (z : PrincipalSubringFractionFiniteSupportRing K) :
    ∃ x : DegreeGraded K,
      ∃ d : PrincipalSubring K,
        d ≠ 0 ∧
          z * principalSubringLocalizationMap K
              (principalSubringEmbedding K d) =
            principalSubringLocalizationMap K x := by
  obtain ⟨⟨x, s⟩, hs⟩ :=
    IsLocalization.surj (principalSubringDenominators K) z
  obtain ⟨d, hd, hds⟩ :=
    (mem_principalGradedDenominators_iff (s : DegreeGraded K)).mp s.2
  refine ⟨x, d, hd, ?_⟩
  rw [hds]
  simpa only [principalSubringLocalization_algebraMap_apply] using hs

/-- A localized divisibility relation by an embedded finite-support series can be cleared by a
nonzero principal graded denominator. -/
theorem principalSubringLocalization_exists_finiteSupport_dvd_mul_principal
    {p : FiniteSupportRing (K := K)}
    {B : DegreeGraded K}
    (hp : principalSubringFractionScalarExtension K p ∣
      principalSubringLocalizationMap K B) :
    ∃ X : DegreeGraded K,
      ∃ d : PrincipalSubring K,
        d ≠ 0 ∧
          B * principalSubringEmbedding K d =
            finiteSupportGradedEmbedding K p * X := by
  obtain ⟨z, hz⟩ := hp
  obtain ⟨X, d, hd, hclear⟩ :=
    principalSubringLocalization_exists_mul_principalDenominator z
  refine ⟨X, d, hd, ?_⟩
  apply principalSubringLocalizationMap_injective
  calc
    principalSubringLocalizationMap K
        (B * principalSubringEmbedding K d) =
        principalSubringLocalizationMap K B *
          principalSubringLocalizationMap K
            (principalSubringEmbedding K d) :=
      (principalSubringLocalizationMap K).map_mul _ _
    _ = (principalSubringFractionScalarExtension K p * z) *
        principalSubringLocalizationMap K
          (principalSubringEmbedding K d) := by
      rw [hz]
    _ = principalSubringFractionScalarExtension K p *
        (z * principalSubringLocalizationMap K
          (principalSubringEmbedding K d)) :=
      mul_assoc _ _ _
    _ = principalSubringFractionScalarExtension K p *
        principalSubringLocalizationMap K X := by
      rw [hclear]
    _ = principalSubringLocalizationMap K
          (finiteSupportGradedEmbedding K p) *
        principalSubringLocalizationMap K X := by
      rw [principalSubringLocalizationMap_finiteSupport]
    _ = principalSubringLocalizationMap K
        (finiteSupportGradedEmbedding K p * X) :=
      ((principalSubringLocalizationMap K).map_mul _ _).symm

/-- The graded localization map preserves divisibility by an embedded finite-support series. -/
theorem principalSubringLocalizationMap_finiteSupport_dvd {p : FiniteSupportRing (K := K)}
    {B : DegreeGraded K}
    (hp : finiteSupportGradedEmbedding K p ∣ B) :
    principalSubringFractionScalarExtension K p ∣
      principalSubringLocalizationMap K B := by
  simpa only [principalSubringLocalizationMap_finiteSupport] using
    map_dvd (principalSubringLocalizationMap K) hp

/-- The localization image of an embedded finite-support divisor of a product divides the
product of the two localization images. -/
theorem principalSubringLocalizationMap_finiteSupport_dvd_mul {p : FiniteSupportRing (K := K)}
    {B C : DegreeGraded K}
    (hp : finiteSupportGradedEmbedding K p ∣ B * C) :
    principalSubringFractionScalarExtension K p ∣
      principalSubringLocalizationMap K B *
        principalSubringLocalizationMap K C := by
  simpa only [(principalSubringLocalizationMap K).map_mul] using
    principalSubringLocalizationMap_finiteSupport_dvd hp

end

end Berarducci
