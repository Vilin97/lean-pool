/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneMonomialSpace
public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneCoordinatePoleAtInfinity
public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneConstantField
public import LeanPool.MarkoffModP.BGS.HasseWeil.RiemannSpaceEffectiveIncrement
public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointStrictLevels

/-!
# One-point Riemann-space lower bounds for plane curves

For an absolutely irreducible affine plane equation `f`, choose an infinity
place `P` where the first coordinate has a pole.  The rectangular monomial
grid

`{x^i y^j | 0 ≤ i ≤ n, 0 ≤ j < degreeOf 1 f}`

lies in the Riemann space of a controlled effective pole divisor.  Removing
all components away from `P` and comparing divisor degrees gives the coarse
one-point estimate

`m * degree(P) + 1 ≤ finrank L(m P) +
  (degreeOf 0 f - 1) * (degreeOf 1 f - 1)`

along an explicit arithmetic progression of pole levels `m`.  The final
theorem combines this estimate with the one-place increment bound and the
exact constant field to force at least `m - g` strict levels in the one-point
Riemann filtration, where `g` is the displayed bidegree budget.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped nonZeroDivisors Polynomial BigOperators

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- The effective pole divisor containing the rectangular monomial grid
`x^i y^j` with `i ≤ n` and `j < b`. -/
def planeMonomialPoleBudget (x y : L) (n b : ℕ) :
    FiniteExtensionDivisor K L :=
  n • finiteExtensionPoleDivisor K L x +
    (b - 1) • finiteExtensionPoleDivisor K L y

/-- The coefficient of the monomial pole budget at a selected place. -/
def planeMonomialPoleLevel (x y : L) (n b : ℕ)
    (P : FiniteExtensionPlace K L) : ℕ :=
  (planeMonomialPoleBudget K L x y n b P).toNat

/-- The selected pole level is an explicit arithmetic progression in `n`. -/
theorem planeMonomialPoleLevel_eq (x y : L) (n b : ℕ)
    (P : FiniteExtensionPlace K L) :
    planeMonomialPoleLevel K L x y n b P =
      n * (finiteExtensionPoleDivisor K L x P).toNat +
        (b - 1) * (finiteExtensionPoleDivisor K L y P).toNat := by
  have hx := finiteExtensionPoleDivisor_effective K L x P
  have hy := finiteExtensionPoleDivisor_effective K L y P
  simp only [planeMonomialPoleLevel, planeMonomialPoleBudget,
    Finsupp.add_apply, Finsupp.nsmul_apply, nsmul_eq_mul]
  rw [Int.toNat_add
      (mul_nonneg (Int.natCast_nonneg n) hx)
      (mul_nonneg (Int.natCast_nonneg (b - 1)) hy),
    Int.toNat_mul (Int.natCast_nonneg n) hx,
    Int.toNat_mul (Int.natCast_nonneg (b - 1)) hy]
  simp

/-- The coarse bidegree genus budget used by the monomial argument.  It is an
upper-bound budget and does not assert that the affine plane model is smooth. -/
def planeCurveBidegreeGenusBudget
    {K : Type*} [CommSemiring K] (f : MvPolynomial (Fin 2) K) : ℕ :=
  (MvPolynomial.degreeOf 0 f - 1) * (MvPolynomial.degreeOf 1 f - 1)

variable {K}

theorem planeCurveSecondCoordinate_height_le_degreeOf_first
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    finiteExtensionHeight K (PlaneCurveFunctionField f)
        (planeCurveFunction f 1) ≤ MvPolynomial.degreeOf 0 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let y : L := planeCurveFunction f 1
  have hyTrans : Transcendental K y :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hy0 : y ≠ 0 := by
    intro hy
    apply hyTrans
    rw [hy]
    exact isAlgebraic_zero
  let : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change finiteExtensionHeight K L y ≤ MvPolynomial.degreeOf 0 f
  rw [← finiteExtensionPositiveDegree_eq_height K L y hy0]
  exact finiteExtensionPositiveDegree_planeCurveSecondCoordinate_le_degreeOf_first
    hf hpartialFirst hpartialSecond

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] in
private theorem planeCurve_monomialGrid_linearIndependent_firstRatFunc
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (a b : ℕ) (hb : b ≤ MvPolynomial.degreeOf 1 f) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let constantAlg : Algebra K (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap K (RatFunc K)))
    letI : Algebra K (PlaneCurveFunctionField f) := constantAlg
    letI : SMul K (PlaneCurveFunctionField f) := constantAlg.toSMul
    letI : Module K (PlaneCurveFunctionField f) := constantAlg.toModule
    LinearIndependent K
      (planeMonomialGrid (planeCurveFunction f 0)
        (planeCurveFunction f 1) a b) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let y : L := planeCurveFunction f 1
  let : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let constantAlg : Algebra K L :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
      (algebraMap K (RatFunc K)))
  let : Algebra K L := constantAlg
  let : SMul K L := constantAlg.toSMul
  let : Module K L := constantAlg.toModule
  let : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let F : Polynomial (RatFunc K) :=
    (planeCurvePolynomialInSecondCoordinate f).map
      (algebraMap (Polynomial K) (RatFunc K))
  have hFirreducible : Irreducible F :=
    planeCurvePolynomialInSecondCoordinate_ratFunc_irreducible
      hf hpartialSecond
  have hFroot : Polynomial.aeval y F = 0 := by
    simpa only [L, y] using
      aeval_planeCurvePolynomialInSecondCoordinate_ratFunc_eq_zero
        hf hpartialSecond
  have heq := minpoly.eq_of_irreducible hFirreducible hFroot
  have hminDegree : (minpoly (RatFunc K) y).natDegree =
      MvPolynomial.degreeOf 1 f := by
    calc
      (minpoly (RatFunc K) y).natDegree =
          (F * Polynomial.C F.leadingCoeff⁻¹).natDegree := by rw [heq]
      _ = F.natDegree := Polynomial.natDegree_mul_C
        (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr
          hFirreducible.ne_zero))
      _ = MvPolynomial.degreeOf 1 f := by
        change ((planeCurvePolynomialInSecondCoordinate f).map
          (algebraMap (Polynomial K) (RatFunc K))).natDegree = _
        rw [Polynomial.natDegree_map_eq_of_injective
          (IsFractionRing.injective (Polynomial K) (RatFunc K)),
          planeCurvePolynomialInSecondCoordinate_natDegree]
  have hb' : b ≤ (minpoly (RatFunc K) y).natDegree := by
    rw [hminDegree]
    exact hb
  have hLI :=
    planeMonomialGrid_linearIndependent_of_transcendental_minpoly
      (RatFunc.X : RatFunc K) y a b RatFunc.transcendental_X hb'
  rw [planeCurveFirstCoordinateRatFuncAlgebra_X f hx] at hLI
  simpa only [L, y] using hLI

theorem planeCurveMonomialPoleBudget_finrank_lower
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (n : ℕ) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    (n + 1) * MvPolynomial.degreeOf 1 f ≤
      Module.finrank K (finiteExtensionRiemannSpace K
        (PlaneCurveFunctionField f)
        (planeMonomialPoleBudget K (PlaneCurveFunctionField f)
          (planeCurveFunction f 0) (planeCurveFunction f 1) n
          (MvPolynomial.degreeOf 1 f))) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  let b := MvPolynomial.degreeOf 1 f
  have hx0 : x ≠ 0 := by
    intro h
    apply hx
    change IsAlgebraic K x
    rw [h]
    exact isAlgebraic_zero
  have hyTrans : Transcendental K y :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hy0 : y ≠ 0 := by
    intro h
    apply hyTrans
    rw [h]
    exact isAlgebraic_zero
  let : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let constantAlg : Algebra K L :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
      (algebraMap K (RatFunc K)))
  let : Algebra K L := constantAlg
  let : SMul K L := constantAlg.toSMul
  let : Module K L := constantAlg.toModule
  let : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hD : ∀ v, 0 ≤
      (n • finiteExtensionPoleDivisor K L x +
        (b - 1) • finiteExtensionPoleDivisor K L y) v := by
    intro v
    simp only [Finsupp.add_apply, Finsupp.nsmul_apply]
    exact add_nonneg
      (nsmul_nonneg (finiteExtensionPoleDivisor_effective K L x v) n)
      (nsmul_nonneg (finiteExtensionPoleDivisor_effective K L y v) (b - 1))
  have hfinite : Module.Finite K (finiteExtensionRiemannSpace K L
      (n • finiteExtensionPoleDivisor K L x +
        (b - 1) • finiteExtensionPoleDivisor K L y)) :=
    finiteExtensionRiemannSpace_effective_moduleFinite K L
      (n • finiteExtensionPoleDivisor K L x +
        (b - 1) • finiteExtensionPoleDivisor K L y) hD
  change (n + 1) * b ≤ Module.finrank K
    (finiteExtensionRiemannSpace K L
      (n • finiteExtensionPoleDivisor K L x +
        (b - 1) • finiteExtensionPoleDivisor K L y))
  apply add_one_mul_le_finrank_poleDivisorBudget
    K L x y hx0 hy0 n b
  · simpa only [L, x, y, b] using
      planeCurve_monomialGrid_linearIndependent_firstRatFunc
        hf hpartialSecond (n + 1) b le_rfl
  · exact hfinite

private theorem exists_planeCurve_onePointRiemannSpace_progression_lower_bound_irreducible
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    ∃ P : FiniteExtensionInfinityPlace K (PlaneCurveFunctionField f),
      let Q : FiniteExtensionPlace K (PlaneCurveFunctionField f) := .inr P
      0 < finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
          (planeCurveFunction f 0) Q ∧
        0 < finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) Q ∧
        finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) Q ≤
          MvPolynomial.degreeOf 1 f ∧
        ∀ n : ℕ,
          let m := planeMonomialPoleLevel K (PlaneCurveFunctionField f)
            (planeCurveFunction f 0) (planeCurveFunction f 1) n
            (MvPolynomial.degreeOf 1 f) Q
          m = n * (finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
              (planeCurveFunction f 0) Q).toNat +
                (MvPolynomial.degreeOf 1 f - 1) *
                  (finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
                    (planeCurveFunction f 1) Q).toNat ∧
            Module.Finite K (finiteExtensionOnePointRiemannSpace K
              (PlaneCurveFunctionField f) Q m) ∧
            m * finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) Q + 1 ≤
              Module.finrank K (finiteExtensionOnePointRiemannSpace K
                (PlaneCurveFunctionField f) Q m) +
                planeCurveBidegreeGenusBudget f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  let a := MvPolynomial.degreeOf 0 f
  let b := MvPolynomial.degreeOf 1 f
  let g := planeCurveBidegreeGenusBudget f
  let : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let constantAlg : Algebra K L :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
      (algebraMap K (RatFunc K)))
  let : Algebra K L := constantAlg
  let : SMul K L := constantAlg.toSMul
  let : Module K L := constantAlg.toModule
  let : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨P, hPpole, hPdegreePositive, hPdegreeBound⟩ :=
    exists_planeCurveFirstCoordinate_infinityPolePlace hf hpartialSecond
  let Q : FiniteExtensionPlace K L := .inr P
  refine ⟨P, hPpole, hPdegreePositive, hPdegreeBound, ?_⟩
  intro n
  let D : FiniteExtensionDivisor K L :=
    planeMonomialPoleBudget K L x y n b
  let m := (D Q).toNat
  have hD : ∀ v, 0 ≤ D v := by
    intro v
    dsimp only [D]
    simp only [planeMonomialPoleBudget, Finsupp.add_apply,
      Finsupp.nsmul_apply]
    exact add_nonneg
      (nsmul_nonneg (finiteExtensionPoleDivisor_effective K L x v) n)
      (nsmul_nonneg (finiteExtensionPoleDivisor_effective K L y v) (b - 1))
  have hm : m = n * (finiteExtensionPoleDivisor K L x Q).toNat +
      (b - 1) * (finiteExtensionPoleDivisor K L y Q).toNat := by
    simpa only [m, D, planeMonomialPoleLevel] using
      planeMonomialPoleLevel_eq K L x y n b Q
  have hmCast : (m : ℤ) = D Q := by
    exact Int.toNat_of_nonneg (hD Q)
  have hfiniteOne : Module.Finite K
      (finiteExtensionOnePointRiemannSpace K L Q m) := by
    change Module.Finite K (finiteExtensionRiemannSpace K L
      (Finsupp.single Q (m : ℤ)))
    apply finiteExtensionRiemannSpace_effective_moduleFinite K L
    intro v
    by_cases hv : v = Q
    · subst v
      simp
    · simp [Finsupp.single_eq_of_ne hv]
  let : Module.Finite K
      (finiteExtensionOnePointRiemannSpace K L Q m) := hfiniteOne
  have hfullLower : (n + 1) * b ≤
      Module.finrank K (finiteExtensionRiemannSpace K L D) := by
    simpa only [D, L, x, y, b] using
      planeCurveMonomialPoleBudget_finrank_lower
        hf hpartialFirst hpartialSecond n
  have hsplit : Module.finrank K (finiteExtensionRiemannSpace K L D) ≤
      Module.finrank K (finiteExtensionOnePointRiemannSpace K L Q m) +
        (finiteExtensionDivisorDegree K L
          (finiteExtensionDivisorAway K L D Q)).toNat := by
    exact finiteExtensionRiemannSpace_finrank_le_onePoint_add_degreeAway
      K L D hD Q
  have hxHeight : finiteExtensionHeight K L x = b := by
    simpa only [L, x, b] using
      finiteExtensionHeight_planeCurveFirstCoordinate hf hpartialSecond
  have hyHeight : finiteExtensionHeight K L y ≤ a := by
    simpa only [L, y, a] using
      planeCurveSecondCoordinate_height_le_degreeOf_first
        hf hpartialFirst hpartialSecond
  have hDdegree : finiteExtensionDivisorDegree K L D ≤
      (n * b + (b - 1) * a : ℕ) := by
    dsimp only [D, planeMonomialPoleBudget]
    rw [finiteExtensionDivisorDegree_pow_mul_pow_budget, hxHeight]
    have hyCast : (finiteExtensionHeight K L y : ℤ) ≤ (a : ℤ) := by
      exact_mod_cast hyHeight
    calc
      (n : ℤ) * (b : ℤ) + ((b - 1 : ℕ) : ℤ) *
          (finiteExtensionHeight K L y : ℤ) ≤
          (n : ℤ) * (b : ℤ) + ((b - 1 : ℕ) : ℤ) * (a : ℤ) := by
        gcongr
      _ = (n * b + (b - 1) * a : ℕ) := by push_cast; ring
  have hAwayEffective : ∀ v, 0 ≤ finiteExtensionDivisorAway K L D Q v :=
    finiteExtensionDivisorAway_effective K L D Q hD
  have hAwayDegreeNonnegative : 0 ≤ finiteExtensionDivisorDegree K L
      (finiteExtensionDivisorAway K L D Q) :=
    finiteExtensionDivisorDegree_nonnegative_of_effective K L
      (finiteExtensionDivisorAway K L D Q) hAwayEffective
  have hAwayPlusSelected :
      (finiteExtensionDivisorDegree K L
          (finiteExtensionDivisorAway K L D Q)).toNat +
          m * finiteExtensionPlaceDegree K L Q ≤
        n * b + (b - 1) * a := by
    have hcast :
        (((finiteExtensionDivisorDegree K L
            (finiteExtensionDivisorAway K L D Q)).toNat +
            m * finiteExtensionPlaceDegree K L Q : ℕ) : ℤ) ≤
          ((n * b + (b - 1) * a : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg hAwayDegreeNonnegative, hmCast]
      calc
        finiteExtensionDivisorDegree K L
              (finiteExtensionDivisorAway K L D Q) +
            D Q * (finiteExtensionPlaceDegree K L Q : ℤ) =
            finiteExtensionDivisorDegree K L D := by
              rw [finiteExtensionDivisorDegree_away]
              ring
        _ ≤ ((n * b + (b - 1) * a : ℕ) : ℤ) := hDdegree
    exact_mod_cast hcast
  have haPos : 0 < a := degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst
  have hbPos : 0 < b := degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond
  have hgenusIdentity :
      n * b + (b - 1) * a + 1 = (n + 1) * b + g := by
    dsimp only [g, planeCurveBidegreeGenusBudget, a, b]
    have haEq : MvPolynomial.degreeOf 0 f - 1 + 1 =
        MvPolynomial.degreeOf 0 f := by omega
    have hbEq : MvPolynomial.degreeOf 1 f - 1 + 1 =
        MvPolynomial.degreeOf 1 f := by omega
    nlinarith
  refine ⟨hm, hfiniteOne, ?_⟩
  change m * finiteExtensionPlaceDegree K L Q + 1 ≤
    Module.finrank K (finiteExtensionOnePointRiemannSpace K L Q m) + g
  have hdim := hfullLower.trans hsplit
  omega

/-- An absolutely irreducible plane curve admits a controlled infinity place
and an explicit arithmetic progression of one-point pole levels satisfying
the coarse Riemann lower bound

`m * degree(P) + 1 ≤ finrank L(m P) + g`,

where `g = (degreeOf 0 f - 1) * (degreeOf 1 f - 1)`.  The first-partial
hypothesis supplies the second-coordinate height bound used by the monomial
budget; the second-partial hypothesis makes the first coordinate separating. -/
theorem exists_planeCurve_onePointRiemannSpace_progression_lower_bound
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    ∃ P : FiniteExtensionInfinityPlace K (PlaneCurveFunctionField f),
      let Q : FiniteExtensionPlace K (PlaneCurveFunctionField f) := .inr P
      0 < finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
          (planeCurveFunction f 0) Q ∧
        0 < finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) Q ∧
        finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) Q ≤
          MvPolynomial.degreeOf 1 f ∧
        ∀ n : ℕ,
          let m := planeMonomialPoleLevel K (PlaneCurveFunctionField f)
            (planeCurveFunction f 0) (planeCurveFunction f 1) n
            (MvPolynomial.degreeOf 1 f) Q
          m = n * (finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
              (planeCurveFunction f 0) Q).toNat +
                (MvPolynomial.degreeOf 1 f - 1) *
                  (finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
                    (planeCurveFunction f 1) Q).toNat ∧
            Module.Finite K (finiteExtensionOnePointRiemannSpace K
              (PlaneCurveFunctionField f) Q m) ∧
            m * finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) Q + 1 ≤
              Module.finrank K (finiteExtensionOnePointRiemannSpace K
                (PlaneCurveFunctionField f) Q m) +
                planeCurveBidegreeGenusBudget f := by
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure habsolute
  exact exists_planeCurve_onePointRiemannSpace_progression_lower_bound_irreducible
    hf hpartialFirst hpartialSecond

/-- Along the progression from
`exists_planeCurve_onePointRiemannSpace_progression_lower_bound`, every level
`m ≥ g` contains at least `m - g` strict inclusions in the one-point Riemann
filtration.  Exact constants give the initial dimension one, while adding the
selected place raises dimension by at most its residue degree. -/
theorem exists_planeCurve_onePointRiemannSpace_progression_strictLevels_lower_bound
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let constantAlg : Algebra K (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap K (RatFunc K)))
    letI : Algebra K (PlaneCurveFunctionField f) := constantAlg
    letI : SMul K (PlaneCurveFunctionField f) := constantAlg.toSMul
    letI : Module K (PlaneCurveFunctionField f) := constantAlg.toModule
    ∃ P : FiniteExtensionInfinityPlace K (PlaneCurveFunctionField f),
      let Q : FiniteExtensionPlace K (PlaneCurveFunctionField f) := .inr P
      0 < finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
          (planeCurveFunction f 0) Q ∧
        0 < finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) Q ∧
        finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) Q ≤
          MvPolynomial.degreeOf 1 f ∧
        ∀ n : ℕ,
          let m := planeMonomialPoleLevel K (PlaneCurveFunctionField f)
            (planeCurveFunction f 0) (planeCurveFunction f 1) n
            (MvPolynomial.degreeOf 1 f) Q
          planeCurveBidegreeGenusBudget f ≤ m →
            m - planeCurveBidegreeGenusBudget f ≤
              (strictFiltrationLevels
                (fun k => finiteExtensionOnePointRiemannSpace K
                  (PlaneCurveFunctionField f) Q k) m).card := by
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure habsolute
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  let b := MvPolynomial.degreeOf 1 f
  let g := planeCurveBidegreeGenusBudget f
  let : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let canonicalAlg : Algebra K L := inferInstance
  let constantAlg : Algebra K L :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
      (algebraMap K (RatFunc K)))
  have hconstantAlg : constantAlg = canonicalAlg := by
    apply Algebra.algebra_ext
    intro c
    change (@ratFuncSpecialization K L _ _ canonicalAlg x hx) (RatFunc.C c) =
      @algebraMap K L _ _ canonicalAlg c
    have h := DFunLike.congr_fun
      (@ratFuncSpecialization_comp_polynomial_algebraMap
        K L _ _ canonicalAlg x hx)
      (Polynomial.C c)
    simpa using h
  let : Algebra K L := constantAlg
  let : SMul K L := constantAlg.toSMul
  let : Module K L := constantAlg.toModule
  let : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨P, hPpole, hPdegreePositive, hPdegreeBound, hprogress⟩ :=
    exists_planeCurve_onePointRiemannSpace_progression_lower_bound
      habsolute hpartialFirst hpartialSecond
  let Q : FiniteExtensionPlace K L := .inr P
  refine ⟨P, hPpole, hPdegreePositive, hPdegreeBound, ?_⟩
  have hconstantsCanonical :
      @algebraicClosure K L _ _ canonicalAlg = ⊥ := by
    simpa only [L] using
      planeCurveFunctionField_algebraicClosure_eq_bot
        f habsolute hpartialSecond
  have hconstants :
      @algebraicClosure K L _ _ constantAlg = ⊥ := by
    rw [hconstantAlg]
    exact hconstantsCanonical
  have hzeroFinrank : Module.finrank K
      (finiteExtensionOnePointRiemannSpace K L Q 0) = 1 := by
    change Module.finrank K (finiteExtensionRiemannSpace K L
      (Finsupp.single Q (0 : ℤ))) = 1
    have hzeroDivisor : Finsupp.single Q (0 : ℤ) =
        (0 : FiniteExtensionDivisor K L) := by
      ext v
      by_cases hv : v = Q <;> simp [hv]
    rw [hzeroDivisor]
    exact finiteExtensionRiemannSpace_zero_finrank K L hconstants
  have hnested : ∀ k,
      finiteExtensionOnePointRiemannSpace K L Q k ≤
        finiteExtensionOnePointRiemannSpace K L Q (k + 1) := by
    intro k
    exact finiteExtensionOnePointRiemannSpace_mono K L Q (by omega)
  have hjump : ∀ k, Module.finrank K
      (finiteExtensionOnePointRiemannSpace K L Q (k + 1)) ≤
        Module.finrank K (finiteExtensionOnePointRiemannSpace K L Q k) +
          finiteExtensionPlaceDegree K L Q := by
    intro k
    let Dk : FiniteExtensionDivisor K L := Finsupp.single Q (k : ℤ)
    have hDk : ∀ v, 0 ≤ Dk v := by
      intro v
      by_cases hv : v = Q
      · subst v
        simp [Dk]
      · simp [Dk, Finsupp.single_eq_of_ne hv]
    have hfiniteK : Module.Finite K
        (finiteExtensionRiemannSpace K L Dk) :=
      finiteExtensionRiemannSpace_effective_moduleFinite K L Dk hDk
    let : Module.Finite K
        (finiteExtensionRiemannSpace K L Dk) := hfiniteK
    have hstep := finiteExtensionRiemannSpace_place_increment K L Dk hDk Q
    have hdivisor : Dk + Finsupp.single Q 1 =
        Finsupp.single Q ((k + 1 : ℕ) : ℤ) := by
      ext v
      by_cases hv : v = Q
      · subst v
        simp only [Dk, Finsupp.add_apply, Finsupp.single_eq_same]
        push_cast
        ring
      · simp [Dk, Finsupp.single_eq_of_ne hv]
    change Module.finrank K (finiteExtensionRiemannSpace K L
        (Finsupp.single Q ((k + 1 : ℕ) : ℤ))) ≤
      Module.finrank K (finiteExtensionRiemannSpace K L
        (Finsupp.single Q (k : ℤ))) + finiteExtensionPlaceDegree K L Q
    rw [← hdivisor]
    exact hstep.2
  intro n
  let m := planeMonomialPoleLevel K L x y n b Q
  change g ≤ m → m - g ≤
    (strictFiltrationLevels
      (fun k => finiteExtensionOnePointRiemannSpace K L Q k) m).card
  intro hgm
  obtain ⟨_hm, _hfinite, hlowerRaw⟩ := hprogress n
  have hlower : m * finiteExtensionPlaceDegree K L Q + 1 ≤
      Module.finrank K (finiteExtensionOnePointRiemannSpace K L Q m) + g := by
    simpa only [m, L, x, y, b, Q, g] using hlowerRaw
  have hdegreeGenus : g ≤ finiteExtensionPlaceDegree K L Q * g :=
    Nat.le_mul_of_pos_left g hPdegreePositive
  have hscaled : 1 + finiteExtensionPlaceDegree K L Q * (m - g) ≤
      Module.finrank K (finiteExtensionOnePointRiemannSpace K L Q m) := by
    have hmDecomp : m = (m - g) + g :=
      (Nat.sub_add_cancel hgm).symm
    have hmulDecomp : finiteExtensionPlaceDegree K L Q * m =
        finiteExtensionPlaceDegree K L Q * (m - g) +
          finiteExtensionPlaceDegree K L Q * g := by
      calc
        finiteExtensionPlaceDegree K L Q * m =
            finiteExtensionPlaceDegree K L Q * ((m - g) + g) :=
          congrArg (fun t => finiteExtensionPlaceDegree K L Q * t) hmDecomp
        _ = finiteExtensionPlaceDegree K L Q * (m - g) +
            finiteExtensionPlaceDegree K L Q * g := by
          rw [Nat.mul_add]
    rw [Nat.mul_comm m (finiteExtensionPlaceDegree K L Q)] at hlower
    omega
  apply le_card_strictFiltrationLevels_of_initial_add_mul_le_finrank
    (fun k => finiteExtensionOnePointRiemannSpace K L Q k)
    hPdegreePositive hnested hjump
  rw [hzeroFinrank]
  exact hscaled

end


end BGS.HasseWeil
