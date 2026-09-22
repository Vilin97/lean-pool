/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneSmoothPointNormalization
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneSquareFieldStepanovCount
import Mathlib.Tactic

/-!
# The square-field Stepanov bound on the smooth affine chart

The smooth-point normalization theorem proves that the selected finite place
above every affine point where the second partial is nonzero has degree one.
This module uses that fact to discharge the sole normalization hypothesis of
the conditional plane square-field Stepanov count.

Exact constants and the large-field inequality remain explicit mathematical
hypotheses.  The resulting error term is honestly `(2 * genusBudget + 1) *
#K`, together with the second-coordinate critical locus; no sharp Hasse--Weil
constant is claimed here.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section


variable (K S : Type*) [Field K] [Fintype K]
  [Field S] [Fintype S] [DecidableEq S] [Algebra K S]
  [DecidableEq (RatFunc S)]

/-- Square-field Stepanov bound with the regular-point degree-one condition
discharged by smooth normalization. -/
theorem planeCurve_affinePoint_card_le_squareField
    {f : MvPolynomial (Fin 2) S} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcard : Fintype.card S = (Fintype.card K) ^ 2)
    (hlarge :
      (planeCurveBidegreeGenusBudget f + 1) *
          (planeCurveBidegreeGenusBudget f + 2) ≤ Fintype.card K) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let constantAlg : Algebra S (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc S) (PlaneCurveFunctionField f)).comp
          (algebraMap S (RatFunc S)))
    letI : Algebra S (PlaneCurveFunctionField f) := constantAlg
    letI : SMul S (PlaneCurveFunctionField f) := constantAlg.toSMul
    letI : Module S (PlaneCurveFunctionField f) := constantAlg.toModule
    letI : IsScalarTower S (RatFunc S) (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    algebraicClosure S (PlaneCurveFunctionField f) = ⊥ →
    Fintype.card (AffinePlaneCurvePoint f) ≤
      Fintype.card S +
        (2 * planeCurveBidegreeGenusBudget f + 1) * Fintype.card K +
        (affineSecondCoordinateCriticalPoints S f).card := by
  classical
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let E := PlaneCurveFunctionField f
  let : Algebra (RatFunc S) E :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc S) E :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let constantAlg : Algebra S E :=
    RingHom.toAlgebra ((algebraMap (RatFunc S) E).comp
      (algebraMap S (RatFunc S)))
  let : Algebra S E := constantAlg
  let : SMul S E := constantAlg.toSMul
  let : Module S E := constantAlg.toModule
  let : IsScalarTower S (RatFunc S) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro hconstants
  apply planeCurve_affinePoint_card_le_of_regularPlace_degree_one
    K S hf hpartialFirst hpartialSecond hcard hlarge hconstants
  intro z
  exact affinePointExhaustiveFinitePlace_degree_eq_one_of_partialY
    (K := S) hf hpartialFirst hpartialSecond z.1 z.2

/-- Explicit bidegree version of `planeCurve_affinePoint_card_le_squareField`.
The resultant estimate replaces the critical-locus cardinal by
`((2 * secondDegree - 1) * firstDegree) * secondDegree`. -/
theorem planeCurve_affinePoint_card_le_squareField_bidegree
    {f : MvPolynomial (Fin 2) S} {firstDegree secondDegree : Nat}
    (hdegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (hcard : Fintype.card S = (Fintype.card K) ^ 2)
    (hlarge :
      (planeCurveBidegreeGenusBudget f + 1) *
          (planeCurveBidegreeGenusBudget f + 2) ≤ Fintype.card K) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let constantAlg : Algebra S (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc S) (PlaneCurveFunctionField f)).comp
          (algebraMap S (RatFunc S)))
    letI : Algebra S (PlaneCurveFunctionField f) := constantAlg
    letI : SMul S (PlaneCurveFunctionField f) := constantAlg.toSMul
    letI : Module S (PlaneCurveFunctionField f) := constantAlg.toModule
    letI : IsScalarTower S (RatFunc S) (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    algebraicClosure S (PlaneCurveFunctionField f) = ⊥ →
    Fintype.card (AffinePlaneCurvePoint f) ≤
      Fintype.card S +
        (2 * planeCurveBidegreeGenusBudget f + 1) * Fintype.card K +
        ((2 * secondDegree - 1) * firstDegree) * secondDegree := by
  classical
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let E := PlaneCurveFunctionField f
  let : Algebra (RatFunc S) E :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc S) E :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let constantAlg : Algebra S E :=
    RingHom.toAlgebra ((algebraMap (RatFunc S) E).comp
      (algebraMap S (RatFunc S)))
  let : Algebra S E := constantAlg
  let : SMul S E := constantAlg.toSMul
  let : Module S E := constantAlg.toModule
  let : IsScalarTower S (RatFunc S) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro hconstants
  apply planeCurve_affinePoint_card_le_bidegree_of_regularPlace_degree_one
    K S hdegree hf hpartialFirst hpartialSecond hcard hlarge hconstants
  intro z
  exact affinePointExhaustiveFinitePlace_degree_eq_one_of_partialY
    (K := S) hf hpartialFirst hpartialSecond z.1 z.2

end

end BGS.HasseWeil
