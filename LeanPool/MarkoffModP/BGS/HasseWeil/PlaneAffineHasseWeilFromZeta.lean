/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionStandardZetaRationality
import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaHasseBound
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneAffineCountTransfer
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneAffineFiberBound
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneAffineRationalPlaceComparison
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneRationalPlaceAffineComparison
import Mathlib.Tactic

/-!
# Affine plane Hasse bounds from the standard zeta package

This module composes the two-sided affine/normalization comparison with the
formal zeta Hasse bound.  In the separating-coordinate case it gives the
external affine-plane estimate with the explicit universal coefficient `8`.

The final theorem retains only the standard zeta numerator package and its
even-extension square-root estimate.  Constructing those data, and removing
the separating-coordinate restriction without losing the original bidegree
scale, remain separate upstream tasks.
-/

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open Filter Asymptotics


section ClosedPlaceLevelOne

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- At extension level one, the closed-place point count is exactly the
number of degree-one places. -/
theorem finiteExtensionClosedPlaceExtensionCount_one_eq_rationalPlaceCount :
    finiteExtensionClosedPlaceExtensionCount K L 1 =
      finiteExtensionRationalPlaceCount K L := by
  classical
  let := finiteExtensionPlaceDegreeLEFintype K L 1
  rw [finiteExtensionClosedPlaceExtensionCount]
  have hdegree : ∀ P : {P : FiniteExtensionPlace K L //
      finiteExtensionPlaceDegree K L P ≤ 1},
      finiteExtensionPlaceDegree K L P.1 = 1 := by
    intro P
    have hpos := finiteExtensionPlaceDegree_pos K L P.1
    omega
  simp_rw [hdegree]
  simp only [dvd_refl, ↓reduceIte, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [finiteExtensionRationalPlaceCount_eq_natCard_subtype]
  let e : {P : FiniteExtensionPlace K L //
        finiteExtensionPlaceDegree K L P ≤ 1} ≃
      {P : FiniteExtensionPlace K L //
        finiteExtensionPlaceDegree K L P = 1} :=
    { toFun := fun P => ⟨P.1, hdegree P⟩
      invFun := fun P => ⟨P.1, P.2.le⟩
      left_inv := by intro P; cases P; rfl
      right_inv := by intro P; cases P; rfl }
  calc
    ↑(Fintype.card {P : FiniteExtensionPlace K L //
        finiteExtensionPlaceDegree K L P ≤ 1}) =
        Nat.card {P : FiniteExtensionPlace K L //
          finiteExtensionPlaceDegree K L P ≤ 1} := by
      rw [Nat.card_eq_fintype_card]
    _ = Nat.card {P : FiniteExtensionPlace K L //
          finiteExtensionPlaceDegree K L P = 1} := Nat.card_congr e

end ClosedPlaceLevelOne

section FunctionFieldZeta

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance affineHasseZetaConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance affineHasseZetaConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Exact constants, divisor index one, a genus budget, and the even-extension
square-root estimate give the corresponding rational-place Hasse bound. -/
theorem abs_finiteExtensionRationalPlaceCount_sub_card_sub_one_le_of_index_one_and_evenError_isBigO
    (budget : ℕ)
    (hconstants : algebraicClosure K L =
      (⊥ : IntermediateField K L))
    (hindex : finiteExtensionDivisorDegreeIndex K L = 1)
    (hgenus : FunctionField.genus K L ≤ budget)
    (herror :
      (fun n : ℕ ↦
        (finiteExtensionClosedPlaceExtensionCount K L (2 * n) : ℂ) -
          (Fintype.card K : ℂ) ^ (2 * n) - 1) =O[atTop]
        fun n : ℕ ↦ (Fintype.card K : ℝ) ^ n) :
    |(finiteExtensionRationalPlaceCount K L : ℝ) -
        (Fintype.card K : ℝ) - 1| ≤
      ((2 * budget + 1 : ℕ) : ℝ) *
        Real.sqrt (Fintype.card K : ℝ) := by
  obtain ⟨P, hPzero, _hPone, hPdegree, hPform, _hPtrace⟩ :=
    exists_finiteExtensionClosedPlaceZeta_trace_with_degree_budget
      K L budget hconstants hindex hgenus
  have herror' :
      (fun n : ℕ ↦
        (finiteExtensionClosedPlaceExtensionCount K L (2 * n) : ℂ) -
          (Nat.card K : ℂ) ^ (2 * n) - 1) =O[atTop]
        fun n : ℕ ↦ (Nat.card K : ℝ) ^ n := by
    simpa only [Fintype.card_eq_nat_card] using herror
  have hhasse :=
    abs_pointCount_sub_card_sub_one_le_of_formalPointCountZeta_rational_and_evenError_isBigO
      (Nat.card K) (finiteExtensionClosedPlaceExtensionCount K L)
      P hPzero hPform herror'
  rw [finiteExtensionClosedPlaceExtensionCount_one_eq_rationalPlaceCount K L]
    at hhasse
  simpa only [Fintype.card_eq_nat_card] using hhasse.trans (by
    have hdegreeReal : (P.natDegree : ℝ) ≤ (2 * budget + 1 : ℕ) := by
      exact_mod_cast hPdegree
    exact mul_le_mul_of_nonneg_right hdegreeReal (Real.sqrt_nonneg _))

end FunctionFieldZeta

/-- The rational-place count of a separating plane model, with all
projection-dependent instances packaged into a stable natural number. -/
def separatingPlaneCurveRationalPlaceCount
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) : ℕ :=
  letI := planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  letI : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  finiteExtensionRationalPlaceCount K (PlaneCurveFunctionField f)

section AffineTransfer

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- A rational-place Hasse estimate with the standard bidegree numerator
budget transfers to the affine plane count with universal coefficient `8`.

The large-`secondDegree` branch uses the elementary first-coordinate fiber
bound.  In the small branch the new reverse comparison and the existing
forward critical-locus comparison give a common error bounded by four
square-root bidegree units; the zeta term costs three and the affine/projective
constant costs one. -/
theorem abs_affinePlaneCurvePoint_card_sub_card_le_eight_mul_bidegree_of_rationalPlaceHasse
    {f : MvPolynomial (Fin 2) K}
    {firstDegree secondDegree zetaDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hfirst : 0 < firstDegree)
    (hsecond : 0 < secondDegree)
    (hzetaDegree : zetaDegree ≤
      2 * ((firstDegree - 1) * (secondDegree - 1)) + 1)
    (hnormalization :
      |(separatingPlaneCurveRationalPlaceCount
          f hf hpartialSecond : ℝ) -
          (Fintype.card K : ℝ) - 1| ≤
        (zetaDegree : ℝ) * Real.sqrt (Fintype.card K : ℝ)) :
    |(Fintype.card (AffinePlaneCurvePoint f) : ℝ) -
        (Fintype.card K : ℝ)| ≤
      8 * Real.sqrt (Fintype.card K : ℝ) *
        (firstDegree : ℝ) * (secondDegree : ℝ) := by
  classical
  by_cases hlarge : Real.sqrt (Fintype.card K : ℝ) ≤ secondDegree
  · have hcount := affinePlaneCurvePoint_card_le_card_mul_firstDegree
      hdegree hf hpartialFirst
    exact (abs_pointCount_sub_card_le_two_mul_sqrt_of_fiber_bound
      (Fintype.card (AffinePlaneCurvePoint f)) (Fintype.card K)
      firstDegree secondDegree hfirst hcount hlarge).trans (by
        have hscale : 0 ≤ Real.sqrt (Fintype.card K : ℝ) *
            (firstDegree : ℝ) * (secondDegree : ℝ) := by positivity
        nlinarith)
  · have hsecondSmall : (secondDegree : ℝ) ≤
        Real.sqrt (Fintype.card K : ℝ) := (lt_of_not_ge hlarge).le
    let error :=
      (firstDegree + (2 * secondDegree - 1) * firstDegree) *
          secondDegree + secondDegree
    have hcritical := affineSecondCoordinateCriticalPoints_card_le
      hdegree hf hpartialSecond
    have hupperRaw : Fintype.card (AffinePlaneCurvePoint f) ≤
        separatingPlaneCurveRationalPlaceCount f hf hpartialSecond +
          (affineSecondCoordinateCriticalPoints K f).card := by
      simpa only [separatingPlaneCurveRationalPlaceCount] using
        affinePlaneCurvePoint_card_le_rationalPlaceCount_add_critical
          hf hpartialFirst hpartialSecond
    have hupper : Fintype.card (AffinePlaneCurvePoint f) ≤
        separatingPlaneCurveRationalPlaceCount f hf hpartialSecond +
          error := by
      apply hupperRaw.trans
      apply Nat.add_le_add_left
      dsimp only [error]
      calc
        (affineSecondCoordinateCriticalPoints K f).card ≤
            ((2 * secondDegree - 1) * firstDegree) * secondDegree := hcritical
        _ ≤ (firstDegree + (2 * secondDegree - 1) * firstDegree) *
              secondDegree := Nat.mul_le_mul_right secondDegree
                (Nat.le_add_left _ _)
        _ ≤ (firstDegree + (2 * secondDegree - 1) * firstDegree) *
              secondDegree + secondDegree := Nat.le_add_right _ _
    have hlower :
        separatingPlaneCurveRationalPlaceCount f hf hpartialSecond ≤
          Fintype.card (AffinePlaneCurvePoint f) + error := by
      simpa only [separatingPlaneCurveRationalPlaceCount, error,
        Nat.add_assoc] using
        finiteExtensionRationalPlaceCount_le_affine_add_exceptional
          hdegree hf hpartialSecond
    have htransfer := abs_affine_sub_card_le_of_two_sided_count_comparison
      (Fintype.card (AffinePlaneCurvePoint f))
      (separatingPlaneCurveRationalPlaceCount f hf hpartialSecond)
      (Fintype.card K) error hupper hlower
      ((zetaDegree : ℝ) * Real.sqrt (Fintype.card K : ℝ)) hnormalization
    apply htransfer.trans
    have hzeta := zetaDegree_mul_sqrt_le_three_mul_bidegree
      zetaDegree (Fintype.card K) firstDegree secondDegree
      hfirst hsecond hzetaDegree
    have hfield : 1 ≤ Fintype.card K :=
      (Fintype.one_lt_card : 1 < Fintype.card K).le
    have hone := one_le_sqrt_mul_bidegree
      (Fintype.card K) firstDegree secondDegree hfield hfirst hsecond
    have herror : (error : ℝ) ≤
        4 * Real.sqrt (Fintype.card K : ℝ) *
          (firstDegree : ℝ) * (secondDegree : ℝ) := by
      dsimp only [error]
      push_cast
      have hfirstReal : (1 : ℝ) ≤ firstDegree := by exact_mod_cast hfirst
      have hsecondReal : (1 : ℝ) ≤ secondDegree := by exact_mod_cast hsecond
      have hsqrt : (1 : ℝ) ≤ Real.sqrt (Fintype.card K : ℝ) :=
        Real.one_le_sqrt.mpr (by exact_mod_cast hfield)
      have hsub : ((2 * secondDegree - 1 : ℕ) : ℝ) ≤
          2 * (secondDegree : ℝ) := by
        exact_mod_cast Nat.sub_le (2 * secondDegree) 1
      have hterm1 : (firstDegree : ℝ) * secondDegree ≤
          Real.sqrt (Fintype.card K : ℝ) * firstDegree * secondDegree := by
        have hxle : (firstDegree : ℝ) ≤
            Real.sqrt (Fintype.card K : ℝ) * firstDegree := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hsqrt
              (by positivity : (0 : ℝ) ≤ firstDegree)
        exact mul_le_mul_of_nonneg_right hxle (by positivity)
      have hterm2 : 2 * (firstDegree : ℝ) * secondDegree * secondDegree ≤
          2 * Real.sqrt (Fintype.card K : ℝ) * firstDegree * secondDegree := by
        have hmul := mul_le_mul_of_nonneg_left hsecondSmall
          (show (0 : ℝ) ≤ 2 * firstDegree * secondDegree by positivity)
        nlinarith
      have hterm3 : (secondDegree : ℝ) ≤
          Real.sqrt (Fintype.card K : ℝ) * firstDegree * secondDegree := by
        have honeProduct : (1 : ℝ) ≤
            Real.sqrt (Fintype.card K : ℝ) * firstDegree :=
          one_le_mul_of_one_le_of_one_le hsqrt hfirstReal
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right honeProduct
            (show (0 : ℝ) ≤ secondDegree by positivity)
      calc
        ((firstDegree : ℝ) + ↑(2 * secondDegree - 1) * firstDegree) *
              secondDegree + secondDegree ≤
            (firstDegree + 2 * secondDegree * firstDegree) *
              secondDegree + secondDegree := by gcongr
        _ = (firstDegree : ℝ) * secondDegree +
              2 * firstDegree * secondDegree * secondDegree + secondDegree := by
            ring
        _ ≤ Real.sqrt (Fintype.card K : ℝ) * firstDegree * secondDegree +
              2 * Real.sqrt (Fintype.card K : ℝ) * firstDegree * secondDegree +
              Real.sqrt (Fintype.card K : ℝ) * firstDegree * secondDegree := by
            exact add_le_add (add_le_add hterm1 hterm2) hterm3
        _ = 4 * Real.sqrt (Fintype.card K : ℝ) * firstDegree * secondDegree := by
            ring
    nlinarith

end AffineTransfer

section PlaneZetaComposition

/-- Standard zeta rationality and the even-extension square-root estimate
imply the exact affine-plane shape required by
`GeneralBivariateAffineHasseWeilTheorem`, with coefficient `8`, whenever both
coordinate projections are separating.

The conclusion is stated using the external finite-set presentation.  Thus
the remaining gap to the unrestricted external proposition is explicit: the
two partial-derivative hypotheses and the upstream zeta package. -/
theorem abs_affinePlaneCurveZeros_card_sub_card_le_eight_mul_bidegree_of_standardZeta
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hfirst : 0 < firstDegree)
    (hsecond : 0 < secondDegree)
    (hdegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (P : Polynomial ℂ)
    (hPzero : P.coeff 0 = 1)
    (hPdegree : P.natDegree ≤
      2 * ((firstDegree - 1) * (secondDegree - 1)) + 1) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let L := PlaneCurveFunctionField f
    let ratAlg : Algebra (RatFunc K) L :=
      planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (RatFunc K) L := ratAlg
    letI : SMul (RatFunc K) L := ratAlg.toSMul
    letI : Module (RatFunc K) L := ratAlg.toModule
    letI : FiniteDimensional (RatFunc K) L :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) L :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    HasCurveZetaRationalForm
        (formalPointCountZeta
          (finiteExtensionClosedPlaceExtensionCount K L))
        (Nat.card K) P →
      ((fun n : ℕ ↦
          (finiteExtensionClosedPlaceExtensionCount K L (2 * n) : ℂ) -
            (Nat.card K : ℂ) ^ (2 * n) - 1) =O[atTop]
          fun n : ℕ ↦ (Nat.card K : ℝ) ^ n) →
      |((BGS.External.affinePlaneCurveZeros K f).card : ℝ) -
          (Fintype.card K : ℝ)| ≤
        8 * Real.sqrt (Fintype.card K : ℝ) *
          (firstDegree : ℝ) * (secondDegree : ℝ) := by
  classical
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure habsolute
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let ratAlg : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (RatFunc K) L := ratAlg
  let : SMul (RatFunc K) L := ratAlg.toSMul
  let : Module (RatFunc K) L := ratAlg.toModule
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : DecidableEq (RatFunc K) := Classical.decEq _
  dsimp only
  intro hPform herror
  have hhasse :=
    abs_pointCount_sub_card_sub_one_le_of_formalPointCountZeta_rational_and_evenError_isBigO
      (Nat.card K) (finiteExtensionClosedPlaceExtensionCount K L)
      P hPzero hPform herror
  rw [finiteExtensionClosedPlaceExtensionCount_one_eq_rationalPlaceCount K L]
    at hhasse
  have hnormalization :
      |(separatingPlaneCurveRationalPlaceCount f hf hpartialSecond : ℝ) -
          (Fintype.card K : ℝ) - 1| ≤
        (P.natDegree : ℝ) * Real.sqrt (Fintype.card K : ℝ) := by
    change
      |(@finiteExtensionRationalPlaceCount K _ _ L _ ratAlg
          (Classical.decEq (RatFunc K)) : ℝ) -
          (Fintype.card K : ℝ) - 1| ≤
        (P.natDegree : ℝ) * Real.sqrt (Fintype.card K : ℝ)
    simpa only [Fintype.card_eq_nat_card] using hhasse
  rw [affinePlaneCurveZeros_card_eq_affinePlaneCurvePoint_card]
  exact
    abs_affinePlaneCurvePoint_card_sub_card_le_eight_mul_bidegree_of_rationalPlaceHasse
      hdegree hf hpartialFirst hpartialSecond hfirst hsecond hPdegree
      hnormalization

end PlaneZetaComposition

end

end BGS.HasseWeil
