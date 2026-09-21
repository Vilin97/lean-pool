/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneRegularPointCount
import LeanPool.MarkoffModP.BGS.HasseWeil.SquareFieldResidue
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneFinitePlaceRiemannLower
import LeanPool.MarkoffModP.BGS.HasseWeil.SquareFieldStepanovAuxiliary
import LeanPool.MarkoffModP.BGS.HasseWeil.SquareFieldStepanovZeroCount
import Mathlib.Tactic

/-!
# A conditional square-field Stepanov bound for plane curves

Let `S` be the full finite constant field and let `K` supply a half-Frobenius
scale, with `#S = (#K)^2`.  For an irreducible plane curve with both
coordinate partials nonzero, exact constants and the standard large-field
condition produce a one-point Stepanov auxiliary at any degree-one selected
place.

We choose the pole place above one affine point that is regular in the second
coordinate direction.  Every other such point gives a distinct finite place
away from the pole.  Assuming these selected regular-point places have degree
one, their residue fields satisfy the quadratic half-Frobenius identity, so
the generic square-field zero count applies.  Adding back the pole point and
the explicit second-coordinate critical locus gives the affine point bound.

The degree-one hypothesis is deliberately explicit.  It is precisely the
normalization input that must later be discharged by the local smooth-point
theorem; no degree-one assertion is made for arbitrary singular points.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section


variable (K S : Type*) [Field K] [Fintype K]
  [Field S] [Fintype S] [DecidableEq S] [Algebra K S]
  [DecidableEq (RatFunc S)]

/-- Conditional affine plane-curve upper bound from the square-field
Stepanov construction.

The final summand is the actual finite critical locus, rather than its
bidegree upper bound.  This keeps the geometric loss visible at the theorem
boundary. -/
theorem planeCurve_affinePoint_card_le_of_regularPlace_degree_one
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
    (∀ z : AffineSecondCoordinateRegularPoint f,
      finiteExtensionPlaceDegree S (PlaneCurveFunctionField f)
        (.inl (affinePointExhaustiveFinitePlace
          hf hpartialFirst hpartialSecond z.1)) = 1) →
    Fintype.card (AffinePlaneCurvePoint f) ≤
      Fintype.card S +
        (2 * planeCurveBidegreeGenusBudget f + 1) * Fintype.card K +
        (affineSecondCoordinateCriticalPoints S f).card := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let E := PlaneCurveFunctionField f
  letI : Algebra (RatFunc S) E :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc S) E :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let constantAlg : Algebra S E :=
    RingHom.toAlgebra ((algebraMap (RatFunc S) E).comp
      (algebraMap S (RatFunc S)))
  letI : Algebra S E := constantAlg
  letI : SMul S E := constantAlg.toSMul
  letI : Module S E := constantAlg.toModule
  letI : IsScalarTower S (RatFunc S) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro hconstants hregularDegree
  let g := planeCurveBidegreeGenusBudget f
  let s := Fintype.card K
  let ell := stepanovEll s
  let m := stepanovM g s
  have hs : 0 < s := Fintype.card_pos
  have hbudget : ell + s * m + 1 =
      Fintype.card S + (2 * g + 1) * s := by
    calc
      ell + s * m + 1 = (s - 1) + s * (s + 2 * g) + 1 := by
        rfl
      _ = s + s * (s + 2 * g) := by omega
      _ = s ^ 2 + (2 * g + 1) * s := by ring
      _ = Fintype.card S + (2 * g + 1) * s := by rw [hcard]
  by_cases hregularCard :
      Fintype.card (AffineSecondCoordinateRegularPoint f) = 0
  · rw [affinePlaneCurvePoint_card_eq_regular_add_critical f,
      hregularCard]
    omega
  · have hregularNonempty :
        Nonempty (AffineSecondCoordinateRegularPoint f) :=
      Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hregularCard)
    let z0 : AffineSecondCoordinateRegularPoint f :=
      Classical.choice hregularNonempty
    let q0 : FiniteExtensionFinitePlace S E :=
      affinePointExhaustiveFinitePlace
        hf hpartialFirst hpartialSecond z0.1
    let P : FiniteExtensionPlace S E := .inl q0
    have hdegreeP : finiteExtensionPlaceDegree S E P = 1 := by
      simpa only [P, q0, E] using hregularDegree z0
    have hriemann : ∀ N,
        N + 1 ≤ Module.finrank S
          (finiteExtensionOnePointRiemannSpace S E P N) + g := by
      intro N
      have h := planeCurve_finitePlace_riemann_lower
        (K := S) hf hpartialFirst hpartialSecond q0 N
      simpa only [E, P, g, hdegreeP, Nat.mul_one] using h
    obtain ⟨u, du, v, dv, c, hu, hv, _hc, hsecond, hfirst⟩ :=
      exists_squareField_onePointStepanovAuxiliary_of_degree_one
        K S E P g hconstants hdegreeP hriemann hlarge
    let point :
        {z : AffineSecondCoordinateRegularPoint f // z ≠ z0} →
          AffinePlaneCurvePoint f := fun z => z.1.1
    let place :
        {z : AffineSecondCoordinateRegularPoint f // z ≠ z0} →
          FiniteExtensionFinitePlace S E := fun z =>
      affinePointExhaustiveFinitePlace
        hf hpartialFirst hpartialSecond (point z)
    have hpointInjective : Function.Injective point := by
      intro z w hzw
      apply Subtype.ext
      apply Subtype.ext
      exact hzw
    have hplaceInjective : Function.Injective place := by
      exact (affinePointExhaustiveFinitePlace_injective
        hf hpartialFirst hpartialSecond).comp hpointInjective
    have haway : ∀ z,
        (Sum.inl (place z) : FiniteExtensionPlace S E) ≠ P := by
      intro z heq
      apply z.2
      apply Subtype.ext
      apply affinePointExhaustiveFinitePlace_injective
        hf hpartialFirst hpartialSecond
      exact Sum.inl.inj heq
    have hplaceDegree : ∀ z,
        finiteExtensionPlaceDegree S E (.inl (place z)) = 1 := by
      intro z
      simpa only [place, point, E] using hregularDegree z.1
    have hsquare : ∀ (z :
        {z : AffineSecondCoordinateRegularPoint f // z ≠ z0})
        (a : (place z).asIdeal.ResidueField),
        a ^ (Fintype.card K) ^ 2 = a := by
      intro z
      exact finiteExtensionFinitePlace_residue_squareFrobenius_of_degree_one
        K S E hcard (place z) (hplaceDegree z)
    have hpunctured :
        Fintype.card
            {z : AffineSecondCoordinateRegularPoint f // z ≠ z0} ≤
          ell + s * m := by
      exact Fintype.card_le_of_squareFieldStepanovAuxiliary
        K S E P ell m u du v dv c hu hv hdegreeP place
          hplaceInjective haway hsquare hsecond hfirst
    have hregular := regularPoint_card_eq_punctured_add_one z0
    rw [affinePlaneCurvePoint_card_eq_regular_add_critical f,
      hregular]
    calc
      Fintype.card
            {z : AffineSecondCoordinateRegularPoint f // z ≠ z0} +
            1 + (affineSecondCoordinateCriticalPoints S f).card ≤
          (ell + s * m) + 1 +
            (affineSecondCoordinateCriticalPoints S f).card := by omega
      _ = Fintype.card S + (2 * g + 1) * s +
            (affineSecondCoordinateCriticalPoints S f).card := by
        rw [hbudget]

/-- Bidegree specialization of
`planeCurve_affinePoint_card_le_of_regularPlace_degree_one`.

Only the critical-locus summand is replaced by its explicit resultant bound;
the Stepanov error remains `(2 * genusBudget + 1) * #K`. -/
theorem planeCurve_affinePoint_card_le_bidegree_of_regularPlace_degree_one
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
    (∀ z : AffineSecondCoordinateRegularPoint f,
      finiteExtensionPlaceDegree S (PlaneCurveFunctionField f)
        (.inl (affinePointExhaustiveFinitePlace
          hf hpartialFirst hpartialSecond z.1)) = 1) →
    Fintype.card (AffinePlaneCurvePoint f) ≤
      Fintype.card S +
        (2 * planeCurveBidegreeGenusBudget f + 1) * Fintype.card K +
        ((2 * secondDegree - 1) * firstDegree) * secondDegree := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let E := PlaneCurveFunctionField f
  letI : Algebra (RatFunc S) E :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc S) E :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let constantAlg : Algebra S E :=
    RingHom.toAlgebra ((algebraMap (RatFunc S) E).comp
      (algebraMap S (RatFunc S)))
  letI : Algebra S E := constantAlg
  letI : SMul S E := constantAlg.toSMul
  letI : Module S E := constantAlg.toModule
  letI : IsScalarTower S (RatFunc S) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro hconstants hregularDegree
  have hcount := planeCurve_affinePoint_card_le_of_regularPlace_degree_one
    K S hf hpartialFirst hpartialSecond hcard hlarge
      hconstants hregularDegree
  have hcritical := affineSecondCoordinateCriticalPoints_card_le
    hdegree hf hpartialSecond
  omega

end

end BGS.HasseWeil
