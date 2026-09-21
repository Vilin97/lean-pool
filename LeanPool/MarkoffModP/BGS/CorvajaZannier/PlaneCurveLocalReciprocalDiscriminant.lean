/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.LocalReciprocalDiscriminant
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveRatFuncModel
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveDiscriminantBound
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Polynomial.ContentIdeal

/-!
# Local reciprocal normalization for an irreducible plane curve

This file specializes `LocalReciprocalDiscriminant` to the first-coordinate
model of an irreducible plane curve.  When the second-coordinate degree is
smaller than the cardinality of the constant field, at each finite prime of
`K[X]` it selects a local center at which the defining polynomial has unit
value.  This includes explicit finite-field and infinite-field interfaces.  It
also proves the defining relation, primitive generation, and the exact
extension degree over `K(X)`.  The final theorem identifies the minimal
polynomial of the reciprocal local parameter with the unit-normalized
reciprocal translate of the localized plane equation.
-/

namespace BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K]

/-- Coordinate `0` becomes the coefficient variable in the iterated plane
curve presentation. -/
@[simp] theorem planeCurvePolynomialInSecondCoordinate_X_zero :
    planeCurvePolynomialInSecondCoordinate (K := K) (MvPolynomial.X 0) =
      Polynomial.C Polynomial.X := by
  rw [planeCurvePolynomialInSecondCoordinate]
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv K 1
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.X 0))) = _
  rw [MvPolynomial.rename_X]
  have hswap : Equiv.swap (0 : Fin 2) 1 0 = 1 := by decide
  rw [hswap]
  have hinner :
      MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 1) =
        Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by decide]
    rfl
  rw [hinner]
  simp [MvPolynomial.uniqueAlgEquiv]

/-- Coordinate `1` becomes the outer polynomial variable. -/
@[simp] theorem planeCurvePolynomialInSecondCoordinate_X_one :
    planeCurvePolynomialInSecondCoordinate (K := K) (MvPolynomial.X 1) =
      Polynomial.X := by
  rw [planeCurvePolynomialInSecondCoordinate]
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv K 1
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.X 1))) = _
  rw [MvPolynomial.rename_X]
  have hswap : Equiv.swap (0 : Fin 2) 1 1 = 0 := by decide
  rw [hswap]
  have hinner :
      MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 0) =
        (Polynomial.X : Polynomial (MvPolynomial (Fin 1) K)) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp
  rw [hinner]
  simp

/-- Constants remain constants in both polynomial variables. -/
@[simp] theorem planeCurvePolynomialInSecondCoordinate_C (c : K) :
    planeCurvePolynomialInSecondCoordinate (MvPolynomial.C c) =
      Polynomial.C (Polynomial.C c) := by
  rw [planeCurvePolynomialInSecondCoordinate]
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv K 1
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.C c))) = _
  rw [MvPolynomial.rename_C]
  have hinner :
      MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C c) =
        Polynomial.C (MvPolynomial.C c) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp
  rw [hinner]
  simp [MvPolynomial.uniqueAlgEquiv]

/-- The plane-curve presentation agrees with Mathlib's standard bivariate
polynomial equivalence. -/
theorem planeCurvePolynomialInSecondCoordinate_eq_bivariateEquiv
    (f : MvPolynomial (Fin 2) K) :
    planeCurvePolynomialInSecondCoordinate f =
      (Polynomial.Bivariate.equivMvPolynomial K).symm f := by
  change planeCurvePolynomialInSecondCoordinate.toAlgHom f =
    (Polynomial.Bivariate.equivMvPolynomial K).symm.toAlgHom f
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp
  · simp

/-- Evaluation of the iterated polynomial is ordinary two-coordinate
evaluation of the original multivariate polynomial. -/
theorem eval₂_planeCurvePolynomialInSecondCoordinate
    {A : Type*} [CommSemiring A] [Algebra K A]
    (f : MvPolynomial (Fin 2) K) (x y : A) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K A) x) y
        (planeCurvePolynomialInSecondCoordinate f) =
      MvPolynomial.eval₂ (algebraMap K A) ![x, y] f := by
  let lhs : MvPolynomial (Fin 2) K →+* A :=
    (Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (algebraMap K A) x) y).comp
        planeCurvePolynomialInSecondCoordinate.toRingEquiv.toRingHom
  let rhs : MvPolynomial (Fin 2) K →+* A :=
    MvPolynomial.eval₂Hom (algebraMap K A) ![x, y]
  change lhs f = rhs f
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [lhs, rhs, planeCurvePolynomialInSecondCoordinate_C]
  · intro i
    fin_cases i
    · simp [lhs, rhs,
        planeCurvePolynomialInSecondCoordinate_X_zero]
    · simp [lhs, rhs,
        planeCurvePolynomialInSecondCoordinate_X_one]

open IsDedekindDomain Polynomial
open scoped nonZeroDivisors

/-- The canonical inclusion of the local ring of `K[X]` at a finite prime
into its fraction field `K(X)`. -/
noncomputable def localizationAtPrimeToRatFunc
    (p : HeightOneSpectrum (Polynomial K)) :
    Localization.AtPrime p.asIdeal →+* RatFunc K :=
  IsLocalization.lift (S := Localization.AtPrime p.asIdeal)
    (M := p.asIdeal.primeCompl)
    (g := algebraMap (Polynomial K) (RatFunc K)) fun
      (y : p.asIdeal.primeCompl) =>
      IsLocalization.map_units (RatFunc K)
        ⟨y.1, p.asIdeal.primeCompl_le_nonZeroDivisors y.2⟩

/-- The local inclusion extends the standard polynomial inclusion in
`RatFunc K`. -/
@[simp] theorem localizationAtPrimeToRatFunc_comp_algebraMap
    (p : HeightOneSpectrum (Polynomial K)) :
    (localizationAtPrimeToRatFunc p).comp
        (algebraMap (Polynomial K) (Localization.AtPrime p.asIdeal)) =
      algebraMap (Polynomial K) (RatFunc K) := by
  simp only [localizationAtPrimeToRatFunc]
  exact IsLocalization.lift_comp _

/-- A primitive polynomial over `K[X]` has a unit value at some center in
every finite localization when its degree is smaller than the cardinality of
the constant field. -/
theorem exists_localized_center_eval_isUnit_of_natDegree_lt_card
    (F : Polynomial (Polynomial K)) (hF : F.IsPrimitive)
    (hcardK : (F.natDegree : Cardinal) < Cardinal.mk K)
    (p : HeightOneSpectrum (Polynomial K)) :
    ∃ a : Polynomial K,
      IsUnit ((F.map
        (algebraMap (Polynomial K) (Localization.AtPrime p.asIdeal))).eval
          (algebraMap (Polynomial K) (Localization.AtPrime p.asIdeal) a)) := by
  let k := (Polynomial K) ⧸ p.asIdeal
  let π : Polynomial K →+* k := Ideal.Quotient.mk p.asIdeal
  have hFbar : F.map π ≠ 0 := by
    intro hzero
    have hcoeff : ∀ i, F.coeff i ∈ p.asIdeal := by
      intro i
      have hi := congrArg (fun q : Polynomial k => q.coeff i) hzero
      rw [Polynomial.coeff_map, Polynomial.coeff_zero] at hi
      exact Ideal.Quotient.eq_zero_iff_mem.mp hi
    have hcontent : F.contentIdeal ≤ p.asIdeal := by
      rw [Polynomial.contentIdeal_def, Ideal.span_le]
      intro x hx
      obtain ⟨i, _hi, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
      exact hcoeff i
    have htop : F.contentIdeal = ⊤ :=
      (Polynomial.isPrimitive_iff_contentIdeal_eq_top F).mp hF
    apply p.isPrime.ne_top
    apply top_unique
    simpa [htop] using hcontent
  have hcard : (F.map π).natDegree < Cardinal.mk k := by
    have hdegree : ((F.map π).natDegree : Cardinal) ≤ F.natDegree := by
      exact_mod_cast Polynomial.natDegree_map_le
    exact (hdegree.trans_lt hcardK).trans_le
      (Cardinal.mk_le_of_injective
        (RingHom.injective (algebraMap K k)))
  obtain ⟨c, hc⟩ :=
    Polynomial.exists_eval_ne_zero_of_natDegree_lt_card (F.map π) hFbar hcard
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨a, ?_⟩
  rw [Polynomial.eval_map_apply]
  apply (IsLocalization.AtPrime.isUnit_to_map_iff
    (Localization.AtPrime p.asIdeal) p.asIdeal (F.eval a)).2
  change F.eval a ∉ p.asIdeal
  intro hmem
  apply hc
  rw [Polynomial.eval_map_apply]
  change π (F.eval a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

/-- Infinite constant fields automatically satisfy the cardinality hypothesis
for a primitive polynomial of finite degree. -/
theorem exists_localized_center_eval_isUnit
    [Infinite K] (F : Polynomial (Polynomial K)) (hF : F.IsPrimitive)
    (p : HeightOneSpectrum (Polynomial K)) :
    ∃ a : Polynomial K,
      IsUnit ((F.map
        (algebraMap (Polynomial K) (Localization.AtPrime p.asIdeal))).eval
          (algebraMap (Polynomial K) (Localization.AtPrime p.asIdeal) a)) := by
  apply exists_localized_center_eval_isUnit_of_natDegree_lt_card F hF
  exact (show (F.natDegree : Cardinal) < Cardinal.aleph0 from
    Cardinal.natCast_lt_aleph0).trans_le (Cardinal.aleph0_le_mk K)

/-- Finite constant fields satisfy the local center hypothesis as soon as the
polynomial degree is smaller than the field cardinality. -/
theorem exists_localized_center_eval_isUnit_of_natDegree_lt_fintypeCard
    [Fintype K] (F : Polynomial (Polynomial K)) (hF : F.IsPrimitive)
    (hcardK : F.natDegree < Fintype.card K)
    (p : HeightOneSpectrum (Polynomial K)) :
    ∃ a : Polynomial K,
      IsUnit ((F.map
        (algebraMap (Polynomial K) (Localization.AtPrime p.asIdeal))).eval
          (algebraMap (Polynomial K) (Localization.AtPrime p.asIdeal) a)) := by
  apply exists_localized_center_eval_isUnit_of_natDegree_lt_card F hF
  simpa only [Cardinal.mk_fintype, Nat.cast_lt] using hcardK

/-- The irreducible plane equation admits a unit-valued center at every
finite first-coordinate prime when its second-coordinate degree is smaller
than the cardinality of the constant field. -/
theorem exists_planeCurve_localized_center_eval_isUnit_of_degreeOf_second_lt_card
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hsecond : 0 < MvPolynomial.degreeOf 1 f)
    (hcardK : (MvPolynomial.degreeOf 1 f : Cardinal) < Cardinal.mk K)
    (p : HeightOneSpectrum (Polynomial K)) :
    ∃ a : Polynomial K,
      IsUnit (((planeCurvePolynomialInSecondCoordinate f).map
        (algebraMap (Polynomial K) (Localization.AtPrime p.asIdeal))).eval
          (algebraMap (Polynomial K) (Localization.AtPrime p.asIdeal) a)) := by
  let F : Polynomial (Polynomial K) :=
    planeCurvePolynomialInSecondCoordinate f
  have hFirreducible : Irreducible F :=
    hf.map planeCurvePolynomialInSecondCoordinate
  have hFdegree : F.natDegree ≠ 0 := by
    simpa [F] using hsecond.ne'
  apply exists_localized_center_eval_isUnit_of_natDegree_lt_card F
    (hFirreducible.isPrimitive hFdegree) _ p
  simpa [F] using hcardK

/-- Over an infinite constant field, every finite first-coordinate prime has
a unit-valued plane-curve center. -/
theorem exists_planeCurve_localized_center_eval_isUnit
    [Infinite K] {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hsecond : 0 < MvPolynomial.degreeOf 1 f)
    (p : HeightOneSpectrum (Polynomial K)) :
    ∃ a : Polynomial K,
      IsUnit (((planeCurvePolynomialInSecondCoordinate f).map
        (algebraMap (Polynomial K) (Localization.AtPrime p.asIdeal))).eval
          (algebraMap (Polynomial K) (Localization.AtPrime p.asIdeal) a)) := by
  apply exists_planeCurve_localized_center_eval_isUnit_of_degreeOf_second_lt_card
    hf hsecond
  exact (show (MvPolynomial.degreeOf 1 f : Cardinal) < Cardinal.aleph0 from
    Cardinal.natCast_lt_aleph0).trans_le (Cardinal.aleph0_le_mk K)

/-- Over a finite constant field, the plane-curve center exists under the
literal degree-versus-cardinality inequality. -/
theorem exists_planeCurve_localized_center_eval_isUnit_of_degreeOf_second_lt_fintypeCard
    [Fintype K] {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hsecond : 0 < MvPolynomial.degreeOf 1 f)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K)
    (p : HeightOneSpectrum (Polynomial K)) :
    ∃ a : Polynomial K,
      IsUnit (((planeCurvePolynomialInSecondCoordinate f).map
        (algebraMap (Polynomial K) (Localization.AtPrime p.asIdeal))).eval
          (algebraMap (Polynomial K) (Localization.AtPrime p.asIdeal) a)) := by
  apply exists_planeCurve_localized_center_eval_isUnit_of_degreeOf_second_lt_card
    hf hsecond _ p
  simpa only [Cardinal.mk_fintype, Nat.cast_lt] using hcardK

/-- The second coordinate is a root of the defining equation after extending
the first-coordinate coefficients to `K(X)`. -/
theorem aeval_planeCurvePolynomialInSecondCoordinate_ratFunc_eq_zero
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    Polynomial.aeval (planeCurveFunction f 1)
      ((planeCurvePolynomialInSecondCoordinate f).map
        (algebraMap (Polynomial K) (RatFunc K))) = 0 := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  have hcoeff :
      (algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)) =
        Polynomial.eval₂RingHom
          (algebraMap K (PlaneCurveFunctionField f))
          (planeCurveFunction f 0) := by
    exact ratFuncSpecialization_comp_polynomial_algebraMap
      (planeCurveFunction f 0) hx
  calc
    Polynomial.aeval (planeCurveFunction f 1)
        ((planeCurvePolynomialInSecondCoordinate f).map
          (algebraMap (Polynomial K) (RatFunc K))) =
        Polynomial.eval₂
          ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
            (algebraMap (Polynomial K) (RatFunc K)))
          (planeCurveFunction f 1)
          (planeCurvePolynomialInSecondCoordinate f) := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    _ = Polynomial.eval₂
          (Polynomial.eval₂RingHom
            (algebraMap K (PlaneCurveFunctionField f))
            (planeCurveFunction f 0))
          (planeCurveFunction f 1)
          (planeCurvePolynomialInSecondCoordinate f) := by rw [hcoeff]
    _ = MvPolynomial.eval₂
          (algebraMap K (PlaneCurveFunctionField f))
          ![planeCurveFunction f 0, planeCurveFunction f 1] f :=
      eval₂_planeCurvePolynomialInSecondCoordinate f
        (planeCurveFunction f 0) (planeCurveFunction f 1)
    _ = 0 := by
      have hcoordinates : planeCurveFunction f =
          ![planeCurveFunction f 0, planeCurveFunction f 1] := by
        funext i
        fin_cases i <;> rfl
      rw [← hcoordinates]
      exact eval₂_planeCurveFunction_eq_zero f

/-- The defining equation remains irreducible over `K(X)`. -/
theorem planeCurvePolynomialInSecondCoordinate_ratFunc_irreducible
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    Irreducible ((planeCurvePolynomialInSecondCoordinate f).map
      (algebraMap (Polynomial K) (RatFunc K))) := by
  let F : Polynomial (Polynomial K) :=
    planeCurvePolynomialInSecondCoordinate f
  have hFirreducible : Irreducible F :=
    hf.map planeCurvePolynomialInSecondCoordinate
  have hFdegree : F.natDegree ≠ 0 := by
    simpa [F] using
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond).ne'
  exact (hFirreducible.isPrimitive hFdegree
    |>.irreducible_iff_irreducible_map_fraction_map).mp hFirreducible

/-- The second coordinate primitively generates the plane function field over
the first-coordinate copy of `K(X)`. -/
theorem adjoin_secondCoordinate_over_firstRatFunc_eq_top
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    Algebra.adjoin (RatFunc K) {planeCurveFunction f 1} = ⊤ := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let F : Polynomial (RatFunc K) :=
    (planeCurvePolynomialInSecondCoordinate f).map
      (algebraMap (Polynomial K) (RatFunc K))
  have hFirreducible : Irreducible F :=
    planeCurvePolynomialInSecondCoordinate_ratFunc_irreducible
      hf hpartialSecond
  have hFroot : Polynomial.aeval (planeCurveFunction f 1) F = 0 :=
    aeval_planeCurvePolynomialInSecondCoordinate_ratFunc_eq_zero
      hf hpartialSecond
  have heq := minpoly.eq_of_irreducible hFirreducible hFroot
  have hminDegree :
      (minpoly (RatFunc K) (planeCurveFunction f 1)).natDegree =
        F.natDegree := by
    calc
      (minpoly (RatFunc K) (planeCurveFunction f 1)).natDegree =
          (F * Polynomial.C F.leadingCoeff⁻¹).natDegree := by rw [heq]
      _ = F.natDegree := Polynomial.natDegree_mul_C
        (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr
          hFirreducible.ne_zero))
  have hFdegree : F.natDegree =
      MvPolynomial.degreeOf 1 f := by
    change ((planeCurvePolynomialInSecondCoordinate f).map
      (algebraMap (Polynomial K) (RatFunc K))).natDegree = _
    rw [Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective (Polynomial K) (RatFunc K)),
      planeCurvePolynomialInSecondCoordinate_natDegree]
  have hfinrank : Module.finrank (RatFunc K)
      (PlaneCurveFunctionField f) = MvPolynomial.degreeOf 1 f :=
    finrank_planeCurveFunctionField_over_ratFunc_eq_degreeOf_second
      hf hpartialSecond
  have hprimitiveField :
      IntermediateField.adjoin (RatFunc K) {planeCurveFunction f 1} =
        (⊤ : IntermediateField (RatFunc K) (PlaneCurveFunctionField f)) :=
    (Field.primitive_element_iff_minpoly_natDegree_eq
      (RatFunc K) (planeCurveFunction f 1)).mpr (by
        rw [hminDegree, hFdegree, hfinrank])
  exact (IntermediateField.adjoin_eq_top_iff).mp hprimitiveField

/-- All local hypotheses for reciprocal normalization, packaged with an
explicit center and unit, under the exact cardinality hypothesis needed for
center selection. -/
theorem planeCurve_local_reciprocal_certificate_of_degreeOf_second_lt_card
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcardK : (MvPolynomial.degreeOf 1 f : Cardinal) < Cardinal.mk K)
    (p : HeightOneSpectrum (Polynomial K)) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let A := Localization.AtPrime p.asIdeal
    let ι := localizationAtPrimeToRatFunc p
    let G := (planeCurvePolynomialInSecondCoordinate f).map
      (algebraMap (Polynomial K) A)
    ∃ (a : Polynomial K) (u : Aˣ),
      let c := algebraMap (Polynomial K) A a
      G.eval c = (u : A) ∧
      G.eval₂ ((algebraMap (RatFunc K)
        (PlaneCurveFunctionField f)).comp ι)
          (planeCurveFunction f 1) = 0 ∧
      planeCurveFunction f 1 ≠
        algebraMap (RatFunc K) (PlaneCurveFunctionField f) (ι c) ∧
      Algebra.adjoin (RatFunc K) {planeCurveFunction f 1} = ⊤ ∧
      G.natDegree = Module.finrank (RatFunc K)
        (PlaneCurveFunctionField f) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let A := Localization.AtPrime p.asIdeal
  let ι := localizationAtPrimeToRatFunc p
  let F := planeCurvePolynomialInSecondCoordinate f
  let G := F.map (algebraMap (Polynomial K) A)
  have hsecond : 0 < MvPolynomial.degreeOf 1 f :=
    degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond
  obtain ⟨a, haUnit⟩ :=
    exists_planeCurve_localized_center_eval_isUnit_of_degreeOf_second_lt_card
      (K := K) hf hsecond hcardK p
  obtain ⟨u, hu⟩ := haUnit
  let c : A := algebraMap (Polynomial K) A a
  have hrootRat :=
    aeval_planeCurvePolynomialInSecondCoordinate_ratFunc_eq_zero
      hf hpartialSecond
  have hroot :
      G.eval₂ ((algebraMap (RatFunc K)
        (PlaneCurveFunctionField f)).comp ι)
          (planeCurveFunction f 1) = 0 := by
    change (F.map (algebraMap (Polynomial K) A)).eval₂
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp ι)
        (planeCurveFunction f 1) = 0
    rw [Polynomial.eval₂_map]
    rw [RingHom.comp_assoc,
      localizationAtPrimeToRatFunc_comp_algebraMap]
    rw [← Polynomial.eval₂_map]
    simpa [Polynomial.aeval_def, F] using hrootRat
  have hvc : planeCurveFunction f 1 ≠
      algebraMap (RatFunc K) (PlaneCurveFunctionField f) (ι c) := by
    intro heq
    have hzeroMap :
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp ι)
          (G.eval c) = 0 := by
      rw [← Polynomial.eval₂_at_apply]
      change planeCurveFunction f 1 =
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp ι) c at heq
      rw [← heq]
      exact hroot
    have hmapUnit : IsUnit
        (((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp ι)
          (G.eval c)) := by
      rw [← hu]
      exact u.isUnit.map _
    exact hmapUnit.ne_zero hzeroMap
  have hprimitive :=
    adjoin_secondCoordinate_over_firstRatFunc_eq_top
      hf hpartialSecond
  have hdegree : G.natDegree = Module.finrank (RatFunc K)
      (PlaneCurveFunctionField f) := by
    have hmapDegree : G.natDegree = F.natDegree := by
      change (F.map (algebraMap (Polynomial K) A)).natDegree = F.natDegree
      exact Polynomial.natDegree_map_eq_of_injective
        (IsLocalization.injective A p.asIdeal.primeCompl_le_nonZeroDivisors) F
    calc
      G.natDegree = F.natDegree := hmapDegree
      _ = MvPolynomial.degreeOf 1 f := by simp [F]
      _ = Module.finrank (RatFunc K) (PlaneCurveFunctionField f) :=
        (finrank_planeCurveFunctionField_over_ratFunc_eq_degreeOf_second
          hf hpartialSecond).symm
  refine ⟨a, u, ?_, hroot, hvc, hprimitive, hdegree⟩
  exact hu.symm

/-- Finite-field form of the full reciprocal-normalization certificate. -/
theorem planeCurve_local_reciprocal_certificate_of_degreeOf_second_lt_fintypeCard
    [Fintype K] {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K)
    (p : HeightOneSpectrum (Polynomial K)) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let A := Localization.AtPrime p.asIdeal
    let ι := localizationAtPrimeToRatFunc p
    let G := (planeCurvePolynomialInSecondCoordinate f).map
      (algebraMap (Polynomial K) A)
    ∃ (a : Polynomial K) (u : Aˣ),
      let c := algebraMap (Polynomial K) A a
      G.eval c = (u : A) ∧
      G.eval₂ ((algebraMap (RatFunc K)
        (PlaneCurveFunctionField f)).comp ι)
          (planeCurveFunction f 1) = 0 ∧
      planeCurveFunction f 1 ≠
        algebraMap (RatFunc K) (PlaneCurveFunctionField f) (ι c) ∧
      Algebra.adjoin (RatFunc K) {planeCurveFunction f 1} = ⊤ ∧
      G.natDegree = Module.finrank (RatFunc K)
        (PlaneCurveFunctionField f) := by
  apply planeCurve_local_reciprocal_certificate_of_degreeOf_second_lt_card
    hf hpartialSecond _ p
  simpa only [Cardinal.mk_fintype, Nat.cast_lt] using hcardK

/-- At every finite first-coordinate prime, a reciprocal translate of the
localized plane equation is exactly the minimal polynomial of the reciprocal
local parameter, under the exact cardinality hypothesis needed to select its
center. -/
theorem planeCurve_minpoly_reciprocal_local_normalization_of_degreeOf_second_lt_card
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcardK : (MvPolynomial.degreeOf 1 f : Cardinal) < Cardinal.mk K)
    (p : HeightOneSpectrum (Polynomial K)) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let A := Localization.AtPrime p.asIdeal
    let ι := localizationAtPrimeToRatFunc p
    ∃ (a : Polynomial K) (u : Aˣ),
      let c := algebraMap (Polynomial K) A a
      let G := (planeCurvePolynomialInSecondCoordinate f).map
        (algebraMap (Polynomial K) A)
      minpoly (RatFunc K)
          ((planeCurveFunction f 1 -
            algebraMap (RatFunc K) (PlaneCurveFunctionField f) (ι c))⁻¹) =
        (unitNormalizedReciprocalTranslate G c u).map ι := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let algRL : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : Algebra (RatFunc K) (PlaneCurveFunctionField f) := algRL
  let A := Localization.AtPrime p.asIdeal
  let ι := localizationAtPrimeToRatFunc p
  obtain ⟨a, u, hu, hroot, hvc, hprimitive, hdegree⟩ :=
    planeCurve_local_reciprocal_certificate_of_degreeOf_second_lt_card
      (K := K) hf hpartialSecond hcardK p
  let c : A := algebraMap (Polynomial K) A a
  let G : Polynomial A :=
    (planeCurvePolynomialInSecondCoordinate f).map
      (algebraMap (Polynomial K) A)
  let algRA : Algebra (Polynomial K) A := inferInstance
  let algRR : Algebra (Polynomial K) (RatFunc K) := inferInstance
  let algAR : Algebra A (RatFunc K) := ι.toAlgebra
  letI : Algebra (Polynomial K) A := algRA
  letI : Algebra (Polynomial K) (RatFunc K) := algRR
  letI : Algebra A (RatFunc K) := algAR
  letI : SMul (Polynomial K) A := algRA.toSMul
  letI : SMul (Polynomial K) (RatFunc K) := algRR.toSMul
  letI : SMul A (RatFunc K) := algAR.toSMul
  letI : IsScalarTower (Polynomial K) A (RatFunc K) := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (localizationAtPrimeToRatFunc_comp_algebraMap p).symm
  letI : IsFractionRing A (RatFunc K) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      p.asIdeal.primeCompl A (RatFunc K)
  let algAL : Algebra A (PlaneCurveFunctionField f) :=
    ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp ι).toAlgebra
  letI : SMul (RatFunc K) (PlaneCurveFunctionField f) := algRL.toSMul
  letI : Algebra A (PlaneCurveFunctionField f) := algAL
  letI : SMul A (PlaneCurveFunctionField f) := algAL.toSMul
  letI : IsScalarTower A (RatFunc K) (PlaneCurveFunctionField f) := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  have hroot' : Polynomial.aeval (planeCurveFunction f 1) G = 0 := by
    simpa [Polynomial.aeval_def, algAL, RingHom.algebraMap_toAlgebra,
      G] using hroot
  have hvc' : planeCurveFunction f 1 ≠
      algebraMap A (PlaneCurveFunctionField f) c := by
    simpa [algAL, RingHom.algebraMap_toAlgebra, RingHom.comp_apply, c] using hvc
  have hmin := minpoly_inv_sub_eq_map_unitNormalizedReciprocalTranslate
    (A := A) (K := RatFunc K) (L := PlaneCurveFunctionField f)
    G c u (planeCurveFunction f 1) hu hvc' hroot' hprimitive hdegree
  refine ⟨a, u, ?_⟩
  simpa [c, G, algAL, algAR, RingHom.algebraMap_toAlgebra,
    RingHom.comp_apply] using hmin

/-- Finite-field form of the reciprocal minimal-polynomial normalization. -/
theorem planeCurve_minpoly_reciprocal_local_normalization_of_degreeOf_second_lt_fintypeCard
    [Fintype K] {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcardK : MvPolynomial.degreeOf 1 f < Fintype.card K)
    (p : HeightOneSpectrum (Polynomial K)) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let A := Localization.AtPrime p.asIdeal
    let ι := localizationAtPrimeToRatFunc p
    ∃ (a : Polynomial K) (u : Aˣ),
      let c := algebraMap (Polynomial K) A a
      let G := (planeCurvePolynomialInSecondCoordinate f).map
        (algebraMap (Polynomial K) A)
      minpoly (RatFunc K)
          ((planeCurveFunction f 1 -
            algebraMap (RatFunc K) (PlaneCurveFunctionField f) (ι c))⁻¹) =
        (unitNormalizedReciprocalTranslate G c u).map ι := by
  apply
    planeCurve_minpoly_reciprocal_local_normalization_of_degreeOf_second_lt_card
      hf hpartialSecond _ p
  simpa only [Cardinal.mk_fintype, Nat.cast_lt] using hcardK

end
end BGS.CorvajaZannier
