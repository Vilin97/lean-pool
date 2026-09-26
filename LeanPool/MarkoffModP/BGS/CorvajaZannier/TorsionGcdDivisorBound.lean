/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.TorsionPointNormalization

/-!
# Torsion points contribute to the normalization gcd divisor

This file upgrades the pointwise normalization result to a finite divisor
inequality.  For any Dedekind normalization model of the plane-curve function
field, one branch is chosen over each rational torsion point.  Distinct points
give distinct branches, both torsion functions have positive order there, and
therefore the number of torsion points is bounded by the sum of the local gcd
multiplicities.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open IsDedekindDomain

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {f : MvPolynomial (Fin 2) K}
variable [IsDomain (PlaneCurveCoordinateRing f)]

/-- Choose a branch in an arbitrary Dedekind integral-closure model above the
maximal ideal defined by a torsion point. -/
def liftedTorsionPointNormalizationBranch
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [Algebra.IsIntegral (PlaneCurveCoordinateRing f) B]
    [FaithfulSMul (PlaneCurveCoordinateRing f) B]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)]
    (firstOrder secondOrder : ℕ)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    MaximalSpectrum B := by
  let hex := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := B) (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩

omit [IsDomain (PlaneCurveCoordinateRing f)] in
theorem liftedTorsionPointNormalizationBranch_liesOver
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [Algebra.IsIntegral (PlaneCurveCoordinateRing f) B]
    [FaithfulSMul (PlaneCurveCoordinateRing f) B]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)]
    (firstOrder secondOrder : ℕ)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    (liftedTorsionPointNormalizationBranch (f := f) (B := B)
      firstOrder secondOrder z).asIdeal.LiesOver
      (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal := by
  let hex := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := B) (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal
  exact (Classical.choose_spec hex).2

omit [IsDomain (PlaneCurveCoordinateRing f)] in
/-- Chosen branches above distinct torsion points are distinct because their
contractions to the affine coordinate ring are distinct. -/
theorem liftedTorsionPointNormalizationBranch_injective
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [Algebra.IsIntegral (PlaneCurveCoordinateRing f) B]
    [FaithfulSMul (PlaneCurveCoordinateRing f) B]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)]
    (firstOrder secondOrder : ℕ) :
    Function.Injective
      (liftedTorsionPointNormalizationBranch (f := f) (B := B)
        firstOrder secondOrder) := by
  intro z w hzw
  apply torsionPointMaximalIdeal_injective f firstOrder secondOrder
  apply MaximalSpectrum.ext
  let hz :
      (liftedTorsionPointNormalizationBranch (f := f) (B := B)
        firstOrder secondOrder z).asIdeal.LiesOver
        (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal :=
    liftedTorsionPointNormalizationBranch_liesOver (f := f) firstOrder secondOrder z
  let hw :
      (liftedTorsionPointNormalizationBranch (f := f) (B := B)
        firstOrder secondOrder w).asIdeal.LiesOver
        (torsionPointMaximalIdeal f firstOrder secondOrder w).asIdeal :=
    liftedTorsionPointNormalizationBranch_liesOver (f := f) firstOrder secondOrder w
  calc
    (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal =
        (liftedTorsionPointNormalizationBranch (f := f) (B := B)
          firstOrder secondOrder z).asIdeal.under (PlaneCurveCoordinateRing f) :=
      Ideal.over_def
        (P := (liftedTorsionPointNormalizationBranch (f := f) (B := B)
          firstOrder secondOrder z).asIdeal)
        (p := (torsionPointMaximalIdeal f firstOrder secondOrder z).asIdeal)
    _ = (liftedTorsionPointNormalizationBranch (f := f) (B := B)
          firstOrder secondOrder w).asIdeal.under (PlaneCurveCoordinateRing f) := by
      rw [hzw]
    _ = (torsionPointMaximalIdeal f firstOrder secondOrder w).asIdeal :=
      (Ideal.over_def
        (P := (liftedTorsionPointNormalizationBranch (f := f) (B := B)
          firstOrder secondOrder w).asIdeal)
        (p := (torsionPointMaximalIdeal f firstOrder secondOrder w).asIdeal)).symm

/-- The finite place selected above a torsion point.  It is obtained from the
positive-order branch theorem, so its defining prime is the chosen branch. -/
def torsionPointFinitePlace
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [Algebra.IsIntegral (PlaneCurveCoordinateRing f) B]
    [FaithfulSMul (PlaneCurveCoordinateRing f) B]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)]
    (firstOrder secondOrder : ℕ)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    HeightOneSpectrum B :=
  Classical.choose (liftedNormalizationBranch_torsion_orders_positive
    f firstOrder secondOrder hfirstNonzero hsecondNonzero z
    (liftedTorsionPointNormalizationBranch (f := f) (B := B)
      firstOrder secondOrder z)
    (liftedTorsionPointNormalizationBranch_liesOver (f := f) firstOrder secondOrder z))

theorem torsionPointFinitePlace_spec
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [Algebra.IsIntegral (PlaneCurveCoordinateRing f) B]
    [FaithfulSMul (PlaneCurveCoordinateRing f) B]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)]
    (firstOrder secondOrder : ℕ)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    (torsionPointFinitePlace (B := B) firstOrder secondOrder
        hfirstNonzero hsecondNonzero z).asIdeal =
        (liftedTorsionPointNormalizationBranch (f := f) (B := B)
          firstOrder secondOrder z).asIdeal ∧
      (1 : ℤ) ≤ finitePlaceOrder
        (torsionPointFinitePlace (B := B) firstOrder secondOrder
          hfirstNonzero hsecondNonzero z)
        (planeCurveFunction f 0 ^ firstOrder - 1) ∧
      (1 : ℤ) ≤ finitePlaceOrder
        (torsionPointFinitePlace (B := B) firstOrder secondOrder
          hfirstNonzero hsecondNonzero z)
        (planeCurveFunction f 1 ^ secondOrder - 1) ∧
      (1 : ℤ) ≤ min
        (finitePlaceOrder
          (torsionPointFinitePlace (B := B) firstOrder secondOrder
            hfirstNonzero hsecondNonzero z)
          (planeCurveFunction f 0 ^ firstOrder - 1))
        (finitePlaceOrder
          (torsionPointFinitePlace (B := B) firstOrder secondOrder
            hfirstNonzero hsecondNonzero z)
          (planeCurveFunction f 1 ^ secondOrder - 1)) :=
  Classical.choose_spec (liftedNormalizationBranch_torsion_orders_positive
    f firstOrder secondOrder hfirstNonzero hsecondNonzero z
    (liftedTorsionPointNormalizationBranch (f := f) (B := B)
      firstOrder secondOrder z)
    (liftedTorsionPointNormalizationBranch_liesOver (f := f) firstOrder secondOrder z))

theorem torsionPointFinitePlace_injective
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [Algebra.IsIntegral (PlaneCurveCoordinateRing f) B]
    [FaithfulSMul (PlaneCurveCoordinateRing f) B]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)]
    (firstOrder secondOrder : ℕ)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0) :
    Function.Injective (torsionPointFinitePlace (B := B) firstOrder secondOrder
      hfirstNonzero hsecondNonzero) := by
  intro z w hzw
  apply liftedTorsionPointNormalizationBranch_injective
    (f := f) (B := B) firstOrder secondOrder
  apply MaximalSpectrum.ext
  rw [← (torsionPointFinitePlace_spec (f := f) (B := B) firstOrder secondOrder
      hfirstNonzero hsecondNonzero z).1,
    ← (torsionPointFinitePlace_spec (f := f) (B := B) firstOrder secondOrder
      hfirstNonzero hsecondNonzero w).1,
    hzw]

/-- The finite support containing every chosen torsion place. -/
def torsionGcdPlaceSupport
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsFractionRing B (PlaneCurveFunctionField f)]
    (firstOrder secondOrder : ℕ) : Finset (HeightOneSpectrum B) := by
  classical
  exact (finitePrincipalDivisor (R := B)
      (planeCurveFunction f 0 ^ firstOrder - 1)).support ∪
    (finitePrincipalDivisor (R := B)
      (planeCurveFunction f 1 ^ secondOrder - 1)).support

theorem torsionPointFinitePlace_mem_torsionGcdPlaceSupport
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [Algebra.IsIntegral (PlaneCurveCoordinateRing f) B]
    [FaithfulSMul (PlaneCurveCoordinateRing f) B]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)]
    [IsFractionRing B (PlaneCurveFunctionField f)]
    (firstOrder secondOrder : ℕ)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    torsionPointFinitePlace (B := B) firstOrder secondOrder
        hfirstNonzero hsecondNonzero z ∈
      torsionGcdPlaceSupport (f := f) (B := B) firstOrder secondOrder := by
  classical
  apply Finset.mem_union_left
  rw [Finsupp.mem_support_iff, finitePrincipalDivisor_apply]
  have h := (torsionPointFinitePlace_spec (f := f) (B := B)
    firstOrder secondOrder hfirstNonzero hsecondNonzero z).2.1
  omega

/-- The natural-number local gcd multiplicity of the two torsion functions. -/
def torsionGcdMultiplicity
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsFractionRing B (PlaneCurveFunctionField f)]
    (firstOrder secondOrder : ℕ) (v : HeightOneSpectrum B) : ℕ :=
  Int.toNat (min
    (finitePlaceOrder v (planeCurveFunction f 0 ^ firstOrder - 1))
    (finitePlaceOrder v (planeCurveFunction f 1 ^ secondOrder - 1)))

/-- Every chosen torsion branch contributes at least one to the local gcd
multiplicity. -/
theorem one_le_torsionGcdMultiplicity_torsionPointFinitePlace
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [Algebra.IsIntegral (PlaneCurveCoordinateRing f) B]
    [FaithfulSMul (PlaneCurveCoordinateRing f) B]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)]
    [IsFractionRing B (PlaneCurveFunctionField f)]
    (firstOrder secondOrder : ℕ)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0)
    (z : TorusCurveTorsionPoint f firstOrder secondOrder) :
    1 ≤ torsionGcdMultiplicity (f := f) (B := B) firstOrder secondOrder
      (torsionPointFinitePlace (B := B) firstOrder secondOrder
        hfirstNonzero hsecondNonzero z) := by
  unfold torsionGcdMultiplicity
  have h := (torsionPointFinitePlace_spec (f := f) (B := B) firstOrder secondOrder
    hfirstNonzero hsecondNonzero z).2.2.2
  omega

/-- The torsion-point count is bounded by the finite sum of local gcd
multiplicities on any Dedekind normalization model. -/
theorem torsionPoint_card_le_torsionGcdMultiplicity_sum
    {B : Type*} [CommRing B] [IsDedekindDomain B]
    [Algebra (PlaneCurveCoordinateRing f) B]
    [Algebra B (PlaneCurveFunctionField f)]
    [IsScalarTower (PlaneCurveCoordinateRing f) B (PlaneCurveFunctionField f)]
    [Algebra.IsIntegral (PlaneCurveCoordinateRing f) B]
    [FaithfulSMul (PlaneCurveCoordinateRing f) B]
    [IsIntegralClosure B (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)]
    [IsFractionRing B (PlaneCurveFunctionField f)]
    (firstOrder secondOrder : ℕ)
    (hfirstNonzero : planeCurveFunction f 0 ^ firstOrder - 1 ≠ 0)
    (hsecondNonzero : planeCurveFunction f 1 ^ secondOrder - 1 ≠ 0) :
    Fintype.card (TorusCurveTorsionPoint f firstOrder secondOrder) ≤
      ∑ v ∈ torsionGcdPlaceSupport (f := f) (B := B) firstOrder secondOrder,
        torsionGcdMultiplicity (f := f) (B := B) firstOrder secondOrder v := by
  classical
  let place : TorusCurveTorsionPoint f firstOrder secondOrder → HeightOneSpectrum B :=
    torsionPointFinitePlace (B := B) firstOrder secondOrder
      hfirstNonzero hsecondNonzero
  have hPlaceInjective : Function.Injective place :=
    torsionPointFinitePlace_injective (B := B) firstOrder secondOrder
      hfirstNonzero hsecondNonzero
  have hImageSubset : Finset.univ.image place ⊆
      torsionGcdPlaceSupport (f := f) (B := B) firstOrder secondOrder := by
    intro v hv
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hv
    exact torsionPointFinitePlace_mem_torsionGcdPlaceSupport (f := f) firstOrder secondOrder
      hfirstNonzero hsecondNonzero z
  calc
    Fintype.card (TorusCurveTorsionPoint f firstOrder secondOrder) =
        (Finset.univ.image place).card := by
      rw [Finset.card_image_of_injective _ hPlaceInjective,
        Finset.card_univ]
    _ = ∑ v ∈ Finset.univ.image place, 1 := by simp
    _ ≤ ∑ v ∈ Finset.univ.image place,
        torsionGcdMultiplicity (f := f) (B := B) firstOrder secondOrder v := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hv
      exact one_le_torsionGcdMultiplicity_torsionPointFinitePlace
        firstOrder secondOrder hfirstNonzero hsecondNonzero z
    _ ≤ ∑ v ∈ torsionGcdPlaceSupport (f := f) (B := B)
        firstOrder secondOrder,
        torsionGcdMultiplicity (f := f) (B := B) firstOrder secondOrder v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hImageSubset (by omega)

end

end BGS.CorvajaZannier
