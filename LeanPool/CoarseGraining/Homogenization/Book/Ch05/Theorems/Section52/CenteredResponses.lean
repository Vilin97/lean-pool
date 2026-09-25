/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.ScalarPreliminaries

/-! # Centered Responses -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section
/-!
# Section 5.2 internals: CenteredResponses

Centered primal and adjoint response identities.
-/

theorem expectedJScalarFormula_sub_scalarizedResponseCenteringTerm_eq_centeredResponseExpectationFormula
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (p q : Vec d) :
    expectedJScalarFormula hP hStruct m p q -
      scalarizedResponseCenteringTerm hP hStruct m p q =
        centeredResponseExpectationFormula hP hStruct m p q := by
  simp [expectedJScalarFormula, scalarizedResponseCenteringTerm,
    centeredResponseExpectationFormula, sub_eq_add_neg,
    vecDot_add_right, vecDot_neg_right, vecDot_smul_right,
    vecDot_comm, thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale]
  ring_nf

theorem integrable_restrictionCenteredResponseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d} [IsFiniteMeasure P]
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (Q : TriadicCube d) (p q : Vec d)
    (hJ : Integrable (Ch04.restrictionResponseJObservableCubeSet Q p q) P) :
    Integrable (restrictionCenteredResponseJObservableCubeSet hP hStruct m Q p q) P := by
  simpa [restrictionCenteredResponseJObservableCubeSet] using!
    hJ.sub (integrable_const _)

theorem integrable_restrictionCenteredResponseJStarObservableCubeSet
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d} [IsFiniteMeasure P]
    (hAdj : Ch04.RestrictionAdjointInvariantLaw P)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (Q : TriadicCube d) (p q : Vec d)
    (hJ : Integrable (Ch04.restrictionResponseJObservableCubeSet Q p q) P) :
    Integrable (restrictionCenteredResponseJStarObservableCubeSet hP hStruct m Q p q) P := by
  have hJAdj :
      Integrable
        (fun a : RegCoeffField d =>
          Ch04.restrictionResponseJObservableCubeSet Q p q (adjointReg a)) P :=
    by
      have hFmap : Integrable (Ch04.restrictionResponseJObservableCubeSet Q p q)
          (Measure.map (adjointReg (d := d)) P) := by rwa [hAdj]
      simpa [Function.comp_def] using
        hFmap.comp_measurable (measurable_adjointReg (d := d))
  simpa [restrictionCenteredResponseJStarObservableCubeSet] using!
    hJAdj.sub (integrable_const _)

theorem integral_restrictionCenteredResponseJObservableCubeSet_eq_expectedResponseJCubeSet_sub
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (Q : TriadicCube d) (p q : Vec d)
    (hJ : Integrable (Ch04.restrictionResponseJObservableCubeSet Q p q) P) :
    ∫ a, restrictionCenteredResponseJObservableCubeSet hP hStruct m Q p q a ∂P =
      Ch04.expectedResponseJCubeSet P Q p q -
        scalarizedResponseCenteringTerm hP hStruct m p q := by
  have hConst :
      Integrable
        (fun _ : RegCoeffField d =>
          scalarizedResponseCenteringTerm hP hStruct m p q) P :=
    integrable_const _
  calc
    ∫ a, restrictionCenteredResponseJObservableCubeSet hP hStruct m Q p q a ∂P
        =
      ∫ a,
        Ch04.restrictionResponseJObservableCubeSet Q p q a -
          scalarizedResponseCenteringTerm hP hStruct m p q ∂P := by
          rfl
    _ =
      ∫ a, Ch04.restrictionResponseJObservableCubeSet Q p q a ∂P -
        ∫ _a : RegCoeffField d,
          scalarizedResponseCenteringTerm hP hStruct m p q ∂P := by
          rw [integral_sub hJ hConst]
    _ =
      Ch04.expectedResponseJCubeSet P Q p q -
        scalarizedResponseCenteringTerm hP hStruct m p q := by
          rw [integral_const]
          simp [Ch04.expectedResponseJCubeSet, Measure.real,
            IsProbabilityMeasure.measure_univ]

theorem integral_restrictionCenteredResponseJStarObservableCubeSet_eq_expectedResponseJCubeSet_sub
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    (hAdj : Ch04.RestrictionAdjointInvariantLaw P)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (Q : TriadicCube d) (p q : Vec d)
    (hJ : Integrable (Ch04.restrictionResponseJObservableCubeSet Q p q) P) :
    ∫ a, restrictionCenteredResponseJStarObservableCubeSet hP hStruct m Q p q a ∂P =
      Ch04.expectedResponseJCubeSet P Q p q -
        scalarizedResponseCenteringTerm hP hStruct m p q := by
  have hJAdj :
      Integrable
        (fun a : RegCoeffField d =>
          Ch04.restrictionResponseJObservableCubeSet Q p q (adjointReg a)) P :=
    by
      have hFmap : Integrable (Ch04.restrictionResponseJObservableCubeSet Q p q)
          (Measure.map (adjointReg (d := d)) P) := by rwa [hAdj]
      simpa [Function.comp_def] using
        hFmap.comp_measurable (measurable_adjointReg (d := d))
  have hConst :
      Integrable
        (fun _ : RegCoeffField d =>
          scalarizedResponseCenteringTerm hP hStruct m p q) P :=
    integrable_const _
  calc
    ∫ a, restrictionCenteredResponseJStarObservableCubeSet hP hStruct m Q p q a ∂P
        =
      ∫ a,
        Ch04.restrictionResponseJObservableCubeSet Q p q (adjointReg a) -
          scalarizedResponseCenteringTerm hP hStruct m p q ∂P := by
          rfl
    _ =
      ∫ a, Ch04.restrictionResponseJObservableCubeSet Q p q (adjointReg a) ∂P -
        ∫ _a : RegCoeffField d,
          scalarizedResponseCenteringTerm hP hStruct m p q ∂P := by
          rw [integral_sub hJAdj hConst]
    _ =
      ∫ a, Ch04.restrictionResponseJObservableCubeSet Q p q a ∂P -
        scalarizedResponseCenteringTerm hP hStruct m p q := by
          rw [hAdj.integral_comp_adjointReg (Ch04.restrictionResponseJObservableCubeSet Q p q) hJ.aestronglyMeasurable]
          rw [integral_const]
          simp [Measure.real, IsProbabilityMeasure.measure_univ]
    _ =
      Ch04.expectedResponseJCubeSet P Q p q -
        scalarizedResponseCenteringTerm hP hStruct m p q := by
          rfl

theorem expectedCenteredResponseJAtScale_eq_annealedResponseJAtScale_sub
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (p q : Vec d)
    (hJ : Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P) :
    expectedCenteredResponseJAtScale hP hStruct m p q =
      Ch04.annealedResponseJAtScale P m p q -
        scalarizedResponseCenteringTerm hP hStruct m p q := by
  simpa [expectedCenteredResponseJAtScale, Ch04.annealedResponseJAtScale,
    Ch04.responseJAtScale, Ch04.restrictionResponseJObservableCubeSet] using!
      integral_restrictionCenteredResponseJObservableCubeSet_eq_expectedResponseJCubeSet_sub
        hP hStruct m (originCube d m) p q hJ

theorem expectedCenteredResponseJStarAtScale_eq_annealedResponseJAtScale_sub
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    (hAdj : Ch04.RestrictionAdjointInvariantLaw P)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (p q : Vec d)
    (hJ : Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P) :
    expectedCenteredResponseJStarAtScale hP hStruct m p q =
      Ch04.annealedResponseJAtScale P m p q -
        scalarizedResponseCenteringTerm hP hStruct m p q := by
  simpa [expectedCenteredResponseJStarAtScale, Ch04.annealedResponseJAtScale,
    Ch04.responseJAtScale, Ch04.restrictionResponseJObservableCubeSet] using!
      integral_restrictionCenteredResponseJStarObservableCubeSet_eq_expectedResponseJCubeSet_sub
        hAdj hP hStruct m (originCube d m) p q hJ

/-- Note-facing primal centered-response expectation formula. -/
theorem expectedCenteredResponseJAtScale_eq_centeredResponseExpectationFormula
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (m : ℤ) (p q : Vec d)
    (hBlock : Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d m)) P) :
    expectedCenteredResponseJAtScale hP hStruct m p q =
      centeredResponseExpectationFormula hP hStruct m p q := by
  let : IsProbabilityMeasure P := hP.isProbability
  have hJ :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P :=
    hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
      (originCube d m) p q hBlock
  calc
    expectedCenteredResponseJAtScale hP hStruct m p q =
        Ch04.annealedResponseJAtScale P m p q -
          scalarizedResponseCenteringTerm hP hStruct m p q :=
      expectedCenteredResponseJAtScale_eq_annealedResponseJAtScale_sub
        hP hStruct m p q hJ
    _ =
        expectedJScalarFormula hP hStruct m p q -
          scalarizedResponseCenteringTerm hP hStruct m p q := by
        rw [annealedResponseJAtScale_eq_expectedJScalarFormula
          hP hStruct m p q hBlock]
    _ = centeredResponseExpectationFormula hP hStruct m p q :=
      expectedJScalarFormula_sub_scalarizedResponseCenteringTerm_eq_centeredResponseExpectationFormula
        hP hStruct m p q

/-- Note-facing adjoint centered-response expectation formula. -/
theorem expectedCenteredResponseJStarAtScale_eq_centeredResponseExpectationFormula
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (m : ℤ) (p q : Vec d)
    (hBlock : Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d m)) P) :
    expectedCenteredResponseJStarAtScale hP hStruct m p q =
      centeredResponseExpectationFormula hP hStruct m p q := by
  let : IsProbabilityMeasure P := hP.isProbability
  have hJ :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P :=
    hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
      (originCube d m) p q hBlock
  calc
    expectedCenteredResponseJStarAtScale hP hStruct m p q =
        Ch04.annealedResponseJAtScale P m p q -
          scalarizedResponseCenteringTerm hP hStruct m p q :=
      expectedCenteredResponseJStarAtScale_eq_annealedResponseJAtScale_sub
        hStruct.adjoint_invariant hP hStruct m p q hJ
    _ =
        expectedJScalarFormula hP hStruct m p q -
          scalarizedResponseCenteringTerm hP hStruct m p q := by
        rw [annealedResponseJAtScale_eq_expectedJScalarFormula
          hP hStruct m p q hBlock]
    _ = centeredResponseExpectationFormula hP hStruct m p q :=
      expectedJScalarFormula_sub_scalarizedResponseCenteringTerm_eq_centeredResponseExpectationFormula
        hP hStruct m p q

/-- Manuscript Lemma `l.centered.responses.homogenization.scale`, expectation
identity part: the centered primal and adjoint responses have the same
scalarized expectation. -/
theorem centeredResponses_homogenizationScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (p q : Vec d) :
    expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p q =
      centeredResponseExpectationFormula hP hStruct (m : ℤ) p q ∧
    expectedCenteredResponseJStarAtScale hP hStruct (m : ℤ) p q =
      centeredResponseExpectationFormula hP hStruct (m : ℤ) p q := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  constructor
  · exact expectedCenteredResponseJAtScale_eq_centeredResponseExpectationFormula
      hP hStruct (m : ℤ) p q hBlock
  · exact expectedCenteredResponseJStarAtScale_eq_centeredResponseExpectationFormula
      hP hStruct (m : ℤ) p q hBlock

end

end Section52
end Ch05
end Book
end Homogenization
