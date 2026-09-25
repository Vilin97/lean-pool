/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Function fields of irreducible affine plane curves

This file constructs the affine coordinate domain and its fraction field directly from an
irreducible polynomial in two variables.  It also records the two coordinate functions and their
defining relation.  These are the algebraic objects used in the plane-curve specialization of the
Corvaja--Zannier argument.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K]

/-- The affine coordinate ring of the plane curve cut out by `f`. -/
abbrev PlaneCurveCoordinateRing (f : MvPolynomial (Fin 2) K) :=
  MvPolynomial (Fin 2) K ⧸ Ideal.span {f}

/-- The quotient map from the polynomial ring to the affine coordinate ring. -/
abbrev planeCurveQuotientMap (f : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 2) K →+* PlaneCurveCoordinateRing f :=
  Ideal.Quotient.mk (Ideal.span {f})

/-- The two affine coordinate classes in the coordinate ring. -/
def planeCurveCoordinate (f : MvPolynomial (Fin 2) K) (i : Fin 2) :
    PlaneCurveCoordinateRing f :=
  planeCurveQuotientMap f (MvPolynomial.X i)

/-- Evaluation at the coordinate classes is the quotient map. -/
theorem eval₂_planeCurveCoordinate (f : MvPolynomial (Fin 2) K) :
    MvPolynomial.eval₂Hom
        (algebraMap K (PlaneCurveCoordinateRing f)) (planeCurveCoordinate f) =
      planeCurveQuotientMap f := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [MvPolynomial.eval₂Hom_C]
    change algebraMap K (PlaneCurveCoordinateRing f) c =
      Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.C c)
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  · intro i
    simp [planeCurveCoordinate, planeCurveQuotientMap]

/-- The coordinate classes satisfy the equation defining the curve. -/
theorem eval₂_planeCurveCoordinate_eq_zero (f : MvPolynomial (Fin 2) K) :
    MvPolynomial.eval₂ (algebraMap K (PlaneCurveCoordinateRing f))
        (planeCurveCoordinate f) f = 0 := by
  change (MvPolynomial.eval₂Hom
    (algebraMap K (PlaneCurveCoordinateRing f)) (planeCurveCoordinate f)) f = 0
  rw [eval₂_planeCurveCoordinate]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f))

/-- Irreducibility of the equation makes its affine coordinate ring a domain. -/
theorem planeCurveCoordinateRing_isDomain
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f) :
    IsDomain (PlaneCurveCoordinateRing f) := by
  have hprime : (Ideal.span {f} : Ideal (MvPolynomial (Fin 2) K)).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
  exact (Ideal.Quotient.isDomain_iff_prime (Ideal.span {f})).mpr hprime

/-- The rational function field of the affine plane curve. -/
abbrev PlaneCurveFunctionField (f : MvPolynomial (Fin 2) K) :=
  FractionRing (PlaneCurveCoordinateRing f)

/-- A coordinate function in the fraction field of the curve. -/
def planeCurveFunction (f : MvPolynomial (Fin 2) K) (i : Fin 2) :
    PlaneCurveFunctionField f :=
  algebraMap (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)
    (planeCurveCoordinate f i)

/-- The quotient map followed by passage to the fraction field is evaluation at the two
coordinate functions. -/
theorem eval₂_planeCurveFunction
    (f : MvPolynomial (Fin 2) K) :
    MvPolynomial.eval₂Hom
        (algebraMap K (PlaneCurveFunctionField f)) (planeCurveFunction f) =
      (algebraMap (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)).comp
        (planeCurveQuotientMap f) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    change algebraMap K (PlaneCurveFunctionField f) c =
      algebraMap (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)
        (Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.C c))
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap,
      ← IsScalarTower.algebraMap_apply]
  · intro i
    simp [planeCurveFunction, planeCurveCoordinate, planeCurveQuotientMap]

/-- The two rational coordinate functions satisfy the equation of the curve. -/
theorem eval₂_planeCurveFunction_eq_zero
    (f : MvPolynomial (Fin 2) K) :
    MvPolynomial.eval₂ (algebraMap K (PlaneCurveFunctionField f))
        (planeCurveFunction f) f = 0 := by
  change (MvPolynomial.eval₂Hom
    (algebraMap K (PlaneCurveFunctionField f)) (planeCurveFunction f)) f = 0
  rw [eval₂_planeCurveFunction f, RingHom.comp_apply]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f)), map_zero]

/-- Every affine regular function, viewed in the fraction field, belongs to the field generated by
the two coordinate functions. -/
theorem algebraMap_coordinateRing_mem_adjoin_coordinates
    {f : MvPolynomial (Fin 2) K} [IsDomain (PlaneCurveCoordinateRing f)]
    (a : PlaneCurveCoordinateRing f) :
    algebraMap (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f) a ∈
      IntermediateField.adjoin K (Set.range (planeCurveFunction f)) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change
    ((algebraMap (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)).comp
      (planeCurveQuotientMap f)) p ∈
        IntermediateField.adjoin K (Set.range (planeCurveFunction f))
  rw [← eval₂_planeCurveFunction f]
  exact MvPolynomial.eval₂_mem
    (fun _ _ ↦ (IntermediateField.adjoin K
      (Set.range (planeCurveFunction f))).algebraMap_mem _)
    (fun i ↦ IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)

/-- The fraction field is generated, as a field over `K`, by its two coordinate functions. -/
theorem adjoin_planeCurveFunctions_eq_top
    {f : MvPolynomial (Fin 2) K} [IsDomain (PlaneCurveCoordinateRing f)] :
    IntermediateField.adjoin K (Set.range (planeCurveFunction f)) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨a, b, _hb, hz⟩ :=
    IsFractionRing.div_surjective (PlaneCurveCoordinateRing f) z
  rw [← hz]
  exact div_mem (algebraMap_coordinateRing_mem_adjoin_coordinates a)
    (algebraMap_coordinateRing_mem_adjoin_coordinates b)

/-- Irreducibility supplies the domain instance needed by
`adjoin_planeCurveFunctions_eq_top`. -/
theorem adjoin_planeCurveFunctions_eq_top_of_irreducible
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f) :
    letI := planeCurveCoordinateRing_isDomain hf
    IntermediateField.adjoin K (Set.range (planeCurveFunction f)) = ⊤ := by
  let : IsDomain (PlaneCurveCoordinateRing f) := planeCurveCoordinateRing_isDomain hf
  exact adjoin_planeCurveFunctions_eq_top

/-- Embed a univariate polynomial in the first coordinate of the affine plane. -/
def polynomialInFirstCoordinate (P : Polynomial K) : MvPolynomial (Fin 2) K :=
  P.sum fun n c ↦ MvPolynomial.C c * MvPolynomial.X 0 ^ n

/-- Evaluating a polynomial embedded in the first coordinate is ordinary univariate evaluation. -/
theorem eval₂_polynomialInFirstCoordinate
    {S : Type*} [CommSemiring S] (P : Polynomial K) (phi : K →+* S) (x y : S) :
    MvPolynomial.eval₂ phi ![x, y] (polynomialInFirstCoordinate P) =
      P.eval₂ phi x := by
  classical
  simp [polynomialInFirstCoordinate, Polynomial.sum_def, Polynomial.eval₂_eq_sum]

/-- The embedding in the first coordinate is injective. -/
theorem polynomialInFirstCoordinate_ne_zero {P : Polynomial K} (hP : P ≠ 0) :
    polynomialInFirstCoordinate P ≠ 0 := by
  intro hzero
  have heval := eval₂_polynomialInFirstCoordinate P Polynomial.C
    Polynomial.X (0 : Polynomial K)
  rw [hzero, MvPolynomial.eval₂_zero] at heval
  apply hP
  simpa using heval.symm

private theorem planeCurve_degreeOf_finset_sum_le
    {R ι : Type*} [CommSemiring R]
    (coordinate : Fin 2) (terms : ι → MvPolynomial (Fin 2) R)
    (indices : Finset ι) (bound : ℕ)
    (hterms : ∀ i ∈ indices, MvPolynomial.degreeOf coordinate (terms i) ≤ bound) :
    MvPolynomial.degreeOf coordinate (∑ i ∈ indices, terms i) ≤ bound := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert i indices hi ih =>
      rw [Finset.sum_insert hi]
      exact (MvPolynomial.degreeOf_add_le _ _ _).trans
        (max_le (hterms i (Finset.mem_insert_self i indices))
          (ih fun j hj ↦ hterms j (Finset.mem_insert_of_mem hj)))

/-- A polynomial embedded in the first coordinate has degree zero in the second coordinate. -/
theorem polynomialInFirstCoordinate_degreeOf_second_le (P : Polynomial K) :
    MvPolynomial.degreeOf (1 : Fin 2) (polynomialInFirstCoordinate P) ≤ 0 := by
  classical
  rw [polynomialInFirstCoordinate, Polynomial.sum_def]
  apply planeCurve_degreeOf_finset_sum_le (1 : Fin 2) _ P.support 0
  intro n _hn
  calc
    MvPolynomial.degreeOf (1 : Fin 2)
        (MvPolynomial.C (P.coeff n) * MvPolynomial.X 0 ^ n) ≤
        MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.C (P.coeff n)) +
          MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 0 ^ n) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ 0 := by
      have hpow : MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.X 0 ^ n : MvPolynomial (Fin 2) K) ≤ 0 := by
        calc
          _ ≤ n * MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 0) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = 0 := by rw [MvPolynomial.degreeOf_X]; norm_num
      rw [MvPolynomial.degreeOf_C]
      simpa using hpow

/-- On an irreducible plane curve of positive second-coordinate degree, the first coordinate
function is transcendental over the constant field. -/
theorem firstCoordinate_transcendental
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hsecond : 0 < MvPolynomial.degreeOf 1 f) :
    letI := planeCurveCoordinateRing_isDomain hf
    Transcendental K (planeCurveFunction f 0) := by
  let : IsDomain (PlaneCurveCoordinateRing f) := planeCurveCoordinateRing_isDomain hf
  rw [transcendental_iff]
  intro P hPzero
  by_contra hP
  have hembedded : polynomialInFirstCoordinate P ≠ 0 :=
    polynomialInFirstCoordinate_ne_zero hP
  have hquotient : planeCurveQuotientMap f (polynomialInFirstCoordinate P) = 0 := by
    apply IsFractionRing.injective (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)
    rw [map_zero]
    change
      ((algebraMap (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)).comp
        (planeCurveQuotientMap f)) (polynomialInFirstCoordinate P) = 0
    rw [← eval₂_planeCurveFunction f]
    have hcoordinates : planeCurveFunction f =
        ![planeCurveFunction f 0, planeCurveFunction f 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hcoordinates]
    change MvPolynomial.eval₂ (algebraMap K (PlaneCurveFunctionField f))
      ![planeCurveFunction f 0, planeCurveFunction f 1]
        (polynomialInFirstCoordinate P) = 0
    rw [eval₂_polynomialInFirstCoordinate]
    simpa [Polynomial.aeval_def] using hPzero
  have hdvd : f ∣ polynomialInFirstCoordinate P :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hquotient)
  obtain ⟨g, hg⟩ := hdvd
  have hgzero : g ≠ 0 := by
    intro hzero
    apply hembedded
    rw [hg, hzero, mul_zero]
  have hdegree : MvPolynomial.degreeOf 1 f ≤
      MvPolynomial.degreeOf 1 (polynomialInFirstCoordinate P) := by
    rw [hg, MvPolynomial.degreeOf_mul_eq hf.ne_zero hgzero]
    exact Nat.le_add_right _ _
  have hzeroDegree := polynomialInFirstCoordinate_degreeOf_second_le P
  omega

/-- The intermediate field generated by the first coordinate function. -/
abbrev FirstCoordinateSubfield
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)] :=
  IntermediateField.adjoin K ({planeCurveFunction f 0} : Set (PlaneCurveFunctionField f))

/-- The first coordinate function, regarded as an element of its generated subfield. -/
def firstCoordinateInSubfield
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)] :
    FirstCoordinateSubfield f :=
  ⟨planeCurveFunction f 0,
    IntermediateField.mem_adjoin_simple_self K (planeCurveFunction f 0)⟩

/-- Regard the plane equation as a polynomial in the second coordinate, with coefficients in the
field generated by the first coordinate. -/
def polynomialOverFirstCoordinate
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)] :
    Polynomial (FirstCoordinateSubfield f) :=
  MvPolynomial.eval₂ (algebraMap K (Polynomial (FirstCoordinateSubfield f)))
    ![Polynomial.C (firstCoordinateInSubfield f), Polynomial.X] f

/-- The same change of viewpoint before specializing the remaining coefficient variable.  The
outer polynomial variable is the original second coordinate. -/
def polynomialInSecondCoordinate (f : MvPolynomial (Fin 2) K) :
    Polynomial (MvPolynomial {i : Fin 2 // i ≠ 1} K) :=
  MvPolynomial.optionEquivLeft K {i : Fin 2 // i ≠ 1}
    (MvPolynomial.rename (Equiv.optionSubtypeNe (1 : Fin 2)).symm f)

/-- The iterated-polynomial presentation preserves nonzeroness. -/
theorem polynomialInSecondCoordinate_ne_zero
    {f : MvPolynomial (Fin 2) K} (hf : f ≠ 0) :
    polynomialInSecondCoordinate f ≠ 0 := by
  intro hzero
  apply hf
  apply MvPolynomial.rename_injective
    (Equiv.optionSubtypeNe (1 : Fin 2)).symm
    (Equiv.optionSubtypeNe (1 : Fin 2)).symm.injective
  apply (MvPolynomial.optionEquivLeft K {i : Fin 2 // i ≠ 1}).injective
  simpa [polynomialInSecondCoordinate] using hzero

/-- Evaluate the sole coefficient variable at the first coordinate function. -/
def firstCoordinateCoefficientEval
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)] :
    MvPolynomial {i : Fin 2 // i ≠ 1} K →+* FirstCoordinateSubfield f :=
  MvPolynomial.eval₂Hom (algebraMap K (FirstCoordinateSubfield f))
    (fun _ ↦ firstCoordinateInSubfield f)

/-- Positive degree in the second coordinate makes coefficient evaluation at the first coordinate
injective. -/
theorem firstCoordinateCoefficientEval_injective
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hsecond : 0 < MvPolynomial.degreeOf 1 f) :
    letI := planeCurveCoordinateRing_isDomain hf
    Function.Injective (firstCoordinateCoefficientEval f) := by
  let : IsDomain (PlaneCurveCoordinateRing f) := planeCurveCoordinateRing_isDomain hf
  let remaining := {i : Fin 2 // i ≠ 1}
  have remaining_value_zero (i : remaining) : i.1 = 0 := by
    omega
  let : Subsingleton remaining :=
    ⟨fun i j ↦ Subtype.ext ((remaining_value_zero i).trans (remaining_value_zero j).symm)⟩
  let i0 : remaining := ⟨0, by decide⟩
  have hIndependent : AlgebraicIndependent K
      (fun _ : remaining ↦ planeCurveFunction f 0) := by
    rw [algebraicIndependent_singleton_iff i0]
    exact firstCoordinate_transcendental hf hsecond
  let composed : MvPolynomial remaining K →+* PlaneCurveFunctionField f :=
    (algebraMap (FirstCoordinateSubfield f) (PlaneCurveFunctionField f)).comp
      (firstCoordinateCoefficientEval f)
  let evaluated : MvPolynomial remaining K →+* PlaneCurveFunctionField f :=
    MvPolynomial.eval₂Hom (algebraMap K (PlaneCurveFunctionField f))
      (fun _ ↦ planeCurveFunction f 0)
  have hhom : composed = evaluated := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [composed, evaluated, firstCoordinateCoefficientEval]
    · intro i
      simp [composed, evaluated, firstCoordinateCoefficientEval,
        firstCoordinateInSubfield]
  intro a b hab
  apply (algebraicIndependent_iff_injective_aeval.mp hIndependent)
  change evaluated a = evaluated b
  rw [← hhom]
  exact congrArg (algebraMap (FirstCoordinateSubfield f) (PlaneCurveFunctionField f)) hab

/-- The direct two-variable specialization agrees with the standard
`MvPolynomial.optionEquivLeft` presentation. -/
theorem polynomialOverFirstCoordinate_eq_map_polynomialInSecondCoordinate
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)] :
    polynomialOverFirstCoordinate f =
      (polynomialInSecondCoordinate f).map (firstCoordinateCoefficientEval f) := by
  let lhs : MvPolynomial (Fin 2) K →+* Polynomial (FirstCoordinateSubfield f) :=
    MvPolynomial.eval₂Hom (algebraMap K (Polynomial (FirstCoordinateSubfield f)))
      ![Polynomial.C (firstCoordinateInSubfield f), Polynomial.X]
  let rhs : MvPolynomial (Fin 2) K →+* Polynomial (FirstCoordinateSubfield f) :=
    (Polynomial.mapRingHom (firstCoordinateCoefficientEval f)).comp
      ((MvPolynomial.optionEquivLeft K {i : Fin 2 // i ≠ 1}).toRingEquiv.toRingHom.comp
        (MvPolynomial.rename (Equiv.optionSubtypeNe (1 : Fin 2)).symm).toRingHom)
  change lhs f = rhs f
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [lhs, rhs, firstCoordinateCoefficientEval]
  · intro i
    fin_cases i <;>
      simp [lhs, rhs, firstCoordinateCoefficientEval, firstCoordinateInSubfield]

/-- Irreducibility and positive degree in the second variable ensure that the equation remains
nonzero after passing to the field generated by the first coordinate. -/
theorem polynomialOverFirstCoordinate_ne_zero_of_irreducible
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hsecond : 0 < MvPolynomial.degreeOf 1 f) :
    letI := planeCurveCoordinateRing_isDomain hf
    polynomialOverFirstCoordinate f ≠ 0 := by
  let : IsDomain (PlaneCurveCoordinateRing f) := planeCurveCoordinateRing_isDomain hf
  rw [polynomialOverFirstCoordinate_eq_map_polynomialInSecondCoordinate]
  exact (Polynomial.map_ne_zero_iff
      (firstCoordinateCoefficientEval_injective hf hsecond)).mpr
    (polynomialInSecondCoordinate_ne_zero hf.ne_zero)

/-- Specializing the coefficient variable cannot increase the degree in the second coordinate. -/
theorem natDegree_polynomialOverFirstCoordinate_le_degreeOf_second
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)] :
    (polynomialOverFirstCoordinate f).natDegree ≤ MvPolynomial.degreeOf 1 f := by
  rw [polynomialOverFirstCoordinate_eq_map_polynomialInSecondCoordinate]
  calc
    ((polynomialInSecondCoordinate f).map
        (firstCoordinateCoefficientEval f)).natDegree ≤
        (polynomialInSecondCoordinate f).natDegree := Polynomial.natDegree_map_le
    _ = MvPolynomial.degreeOf 1 f :=
      (MvPolynomial.degreeOf_eq_natDegree (1 : Fin 2) f).symm

/-- Substituting the second coordinate function into `polynomialOverFirstCoordinate` recovers the
defining plane-curve relation. -/
theorem eval₂_polynomialOverFirstCoordinate_eq_zero
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)] :
    Polynomial.eval₂
        (algebraMap (FirstCoordinateSubfield f) (PlaneCurveFunctionField f))
        (planeCurveFunction f 1) (polynomialOverFirstCoordinate f) = 0 := by
  let lhs : MvPolynomial (Fin 2) K →+* PlaneCurveFunctionField f :=
    (Polynomial.eval₂RingHom
      (algebraMap (FirstCoordinateSubfield f) (PlaneCurveFunctionField f))
      (planeCurveFunction f 1)).comp
        (MvPolynomial.eval₂Hom
          (algebraMap K (Polynomial (FirstCoordinateSubfield f)))
          ![Polynomial.C (firstCoordinateInSubfield f), Polynomial.X])
  let rhs : MvPolynomial (Fin 2) K →+* PlaneCurveFunctionField f :=
    MvPolynomial.eval₂Hom (algebraMap K (PlaneCurveFunctionField f))
      (planeCurveFunction f)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs]
    · intro i
      fin_cases i <;>
        simp [lhs, rhs, firstCoordinateInSubfield]
  change lhs f = 0
  rw [hhom]
  exact eval₂_planeCurveFunction_eq_zero f

/-- If the specialized equation is nonzero, the second coordinate is algebraic over the field
generated by the first coordinate. -/
theorem secondCoordinate_isAlgebraic_over_first
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)]
    (hpoly : polynomialOverFirstCoordinate f ≠ 0) :
    IsAlgebraic (FirstCoordinateSubfield f) (planeCurveFunction f 1) := by
  refine ⟨polynomialOverFirstCoordinate f, hpoly, ?_⟩
  simpa [Polynomial.aeval_def] using eval₂_polynomialOverFirstCoordinate_eq_zero f

/-- The range of the coordinate-function family is exactly the two-element set of affine
coordinates. -/
theorem range_planeCurveFunction
    (f : MvPolynomial (Fin 2) K) :
    Set.range (planeCurveFunction f) =
      ({planeCurveFunction f 0, planeCurveFunction f 1} :
        Set (PlaneCurveFunctionField f)) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hz
    rcases hz with (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- After adjoining the first coordinate to `K`, adjoining the second coordinate generates the
entire plane-curve function field. -/
theorem adjoin_secondCoordinate_over_first_eq_top
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)] :
    IntermediateField.adjoin (FirstCoordinateSubfield f) {planeCurveFunction f 1} = ⊤ := by
  have hpair :
      IntermediateField.adjoin K
          ({planeCurveFunction f 0, planeCurveFunction f 1} :
            Set (PlaneCurveFunctionField f)) = ⊤ := by
    rw [← range_planeCurveFunction f]
    exact adjoin_planeCurveFunctions_eq_top
  apply IntermediateField.restrictScalars_injective K
  rw [IntermediateField.restrictScalars_top]
  change
    (IntermediateField.adjoin
        (IntermediateField.adjoin K {planeCurveFunction f 0})
        {planeCurveFunction f 1}).restrictScalars K = ⊤
  rw [IntermediateField.adjoin_adjoin_left]
  simpa only [Set.singleton_union] using hpair

/-- A nonzero specialization of the plane equation makes the function field finite-dimensional
over the field generated by the first coordinate. -/
theorem finiteDimensional_over_firstCoordinate
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)]
    (hpoly : polynomialOverFirstCoordinate f ≠ 0) :
    FiniteDimensional (FirstCoordinateSubfield f) (PlaneCurveFunctionField f) := by
  have halg := secondCoordinate_isAlgebraic_over_first f hpoly
  let : FiniteDimensional (FirstCoordinateSubfield f)
      (IntermediateField.adjoin (FirstCoordinateSubfield f) {planeCurveFunction f 1}) :=
    IntermediateField.adjoin.finiteDimensional halg.isIntegral
  let : FiniteDimensional (FirstCoordinateSubfield f)
      (⊤ : IntermediateField (FirstCoordinateSubfield f) (PlaneCurveFunctionField f)) := by
    rw [← adjoin_secondCoordinate_over_first_eq_top f]
    infer_instance
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

/-- The extension degree over the first-coordinate field is at most the degree of the plane
equation in the second coordinate. -/
theorem finrank_over_firstCoordinate_le_degreeOf_second
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)]
    (hpoly : polynomialOverFirstCoordinate f ≠ 0) :
    Module.finrank (FirstCoordinateSubfield f) (PlaneCurveFunctionField f) ≤
      MvPolynomial.degreeOf 1 f := by
  let : FiniteDimensional (FirstCoordinateSubfield f) (PlaneCurveFunctionField f) :=
    finiteDimensional_over_firstCoordinate f hpoly
  have halg := secondCoordinate_isAlgebraic_over_first f hpoly
  have hroot : Polynomial.aeval (planeCurveFunction f 1)
      (polynomialOverFirstCoordinate f) = 0 := by
    simpa [Polynomial.aeval_def] using eval₂_polynomialOverFirstCoordinate_eq_zero f
  calc
    Module.finrank (FirstCoordinateSubfield f) (PlaneCurveFunctionField f) =
        Module.finrank (FirstCoordinateSubfield f)
          (⊤ : IntermediateField (FirstCoordinateSubfield f)
            (PlaneCurveFunctionField f)) :=
      by rw [IntermediateField.finrank_top']
    _ = Module.finrank (FirstCoordinateSubfield f)
          (IntermediateField.adjoin (FirstCoordinateSubfield f)
            {planeCurveFunction f 1}) := by
      rw [adjoin_secondCoordinate_over_first_eq_top f]
    _ = (minpoly (FirstCoordinateSubfield f) (planeCurveFunction f 1)).natDegree :=
      IntermediateField.adjoin.finrank halg.isIntegral
    _ ≤ (polynomialOverFirstCoordinate f).natDegree :=
      Polynomial.natDegree_le_of_dvd
        (minpoly.dvd (FirstCoordinateSubfield f) (planeCurveFunction f 1) hroot) hpoly
    _ ≤ MvPolynomial.degreeOf 1 f :=
      natDegree_polynomialOverFirstCoordinate_le_degreeOf_second f

/-- A nonzero partial derivative in the second coordinate forces positive degree in that
coordinate. -/
theorem degreeOf_second_pos_of_pderiv_ne_zero
    {f : MvPolynomial (Fin 2) K} (hderiv : MvPolynomial.pderiv 1 f ≠ 0) :
    0 < MvPolynomial.degreeOf 1 f := by
  apply Nat.pos_of_ne_zero
  apply MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp
  by_contra hmem
  exact hderiv (MvPolynomial.pderiv_eq_zero_of_notMem_vars hmem)

/-- For an irreducible plane equation depending on the second coordinate, the function field is
finite over the field generated by the first coordinate. -/
theorem finiteDimensional_over_firstCoordinate_of_irreducible
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hderiv : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    FiniteDimensional (FirstCoordinateSubfield f) (PlaneCurveFunctionField f) := by
  let : IsDomain (PlaneCurveCoordinateRing f) := planeCurveCoordinateRing_isDomain hf
  exact finiteDimensional_over_firstCoordinate f
    (polynomialOverFirstCoordinate_ne_zero_of_irreducible hf
      (degreeOf_second_pos_of_pderiv_ne_zero hderiv))

/-- The degree of the plane-curve function field over the first-coordinate rational subfield is
bounded by the degree of the defining equation in the second coordinate. -/
theorem finrank_over_firstCoordinate_le_degreeOf_second_of_irreducible
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hderiv : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (FirstCoordinateSubfield f) (PlaneCurveFunctionField f) ≤
      MvPolynomial.degreeOf 1 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) := planeCurveCoordinateRing_isDomain hf
  exact finrank_over_firstCoordinate_le_degreeOf_second f
    (polynomialOverFirstCoordinate_ne_zero_of_irreducible hf
      (degreeOf_second_pos_of_pderiv_ne_zero hderiv))

end

end BGS.CorvajaZannier
