/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneRegularPointCount
public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneSmoothPointNormalization
public import LeanPool.MarkoffModP.BGS.HasseWeil.RationalPlace
public import Mathlib.Tactic

/-!
# Affine plane points and rational normalization places

For an irreducible plane curve with both coordinates separating, every affine
point that is regular in the second-coordinate direction determines a
degree-one finite place of the function field.  Distinct regular affine points
give distinct places.  Consequently the regular affine locus injects into the
rational finite places, and adding the explicit critical locus compares all
affine rational points with the full rational-place count.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section


variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {f : MvPolynomial (Fin 2) K}

/-- Send a second-coordinate regular affine point to its selected degree-one
finite normalization place. -/
def affineSecondCoordinateRegularPointToRationalFinitePlace
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (z : AffineSecondCoordinateRegularPoint f) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    FiniteExtensionRationalFinitePlace K (PlaneCurveFunctionField f) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  letI : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  exact ⟨affinePointExhaustiveFinitePlace
      hf hpartialFirst hpartialSecond z.1,
    affinePointExhaustiveFinitePlace_degree_eq_one_of_partialY
      K hf hpartialFirst hpartialSecond z.1 z.2⟩

/-- Distinct second-coordinate regular affine points determine distinct
degree-one finite normalization places. -/
theorem affineSecondCoordinateRegularPointToRationalFinitePlace_injective
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    Function.Injective
      (affineSecondCoordinateRegularPointToRationalFinitePlace
        hf hpartialFirst hpartialSecond) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : DecidableEq (RatFunc K) := Classical.decEq _
  dsimp only
  intro z w hzw
  apply Subtype.ext
  apply affinePointExhaustiveFinitePlace_injective
    hf hpartialFirst hpartialSecond
  exact congrArg Subtype.val hzw

/-- The regular affine locus has cardinality at most the number of degree-one
finite places. -/
theorem affineSecondCoordinateRegularPoint_card_le_rationalFinitePlace
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    Fintype.card (AffineSecondCoordinateRegularPoint f) ≤
      Nat.card (FiniteExtensionRationalFinitePlace K
        (PlaneCurveFunctionField f)) := by
  classical
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : DecidableEq (RatFunc K) := Classical.decEq _
  dsimp only
  let toPlace := affineSecondCoordinateRegularPointToRationalFinitePlace
    hf hpartialFirst hpartialSecond
  have hcard := Nat.card_le_card_of_injective toPlace
    (affineSecondCoordinateRegularPointToRationalFinitePlace_injective
      hf hpartialFirst hpartialSecond)
  simpa only [Nat.card_eq_fintype_card] using hcard

/-- The regular affine locus has cardinality at most the total rational-place
count, which also includes places above infinity. -/
theorem affineSecondCoordinateRegularPoint_card_le_rationalPlaceCount
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    Fintype.card (AffineSecondCoordinateRegularPoint f) ≤
      finiteExtensionRationalPlaceCount K (PlaneCurveFunctionField f) := by
  classical
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : DecidableEq (RatFunc K) := Classical.decEq _
  dsimp only
  calc
    Fintype.card (AffineSecondCoordinateRegularPoint f) ≤
        Nat.card (FiniteExtensionRationalFinitePlace K
          (PlaneCurveFunctionField f)) :=
      affineSecondCoordinateRegularPoint_card_le_rationalFinitePlace
        hf hpartialFirst hpartialSecond
    _ ≤ Nat.card (FiniteExtensionRationalPlace K
          (PlaneCurveFunctionField f)) :=
      Nat.card_le_card_of_injective
        (fun Q : FiniteExtensionRationalFinitePlace K
            (PlaneCurveFunctionField f) =>
          (Sum.inl Q : FiniteExtensionRationalPlace K
            (PlaneCurveFunctionField f)))
        Sum.inl_injective
    _ = finiteExtensionRationalPlaceCount K
          (PlaneCurveFunctionField f) := rfl

/-- The first affine-normalization comparison: all affine rational points are
bounded by the rational places of the normalization plus the explicit
second-coordinate critical locus. -/
theorem affinePlaneCurvePoint_card_le_rationalPlaceCount_add_critical
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    Fintype.card (AffinePlaneCurvePoint f) ≤
      finiteExtensionRationalPlaceCount K (PlaneCurveFunctionField f) +
        (affineSecondCoordinateCriticalPoints K f).card := by
  classical
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : DecidableEq (RatFunc K) := Classical.decEq _
  dsimp only
  rw [affinePlaneCurvePoint_card_eq_regular_add_critical f]
  exact Nat.add_le_add_right
    (affineSecondCoordinateRegularPoint_card_le_rationalPlaceCount
      hf hpartialFirst hpartialSecond)
    (affineSecondCoordinateCriticalPoints K f).card

end

end BGS.HasseWeil
