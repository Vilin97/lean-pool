/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.Supersolution
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.SupStability

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Perron method core assembly

Core Perron existence assembly from upper and lower envelope hypotheses.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/--
Assembly form of Perron's method.

The analytic Perron work splits into two inputs:

* the upper envelope of the Perron candidate is a Dirichlet subsolution;
* the lower envelope of the Perron candidate is a Dirichlet supersolution.

Once those are available, comparison gives the reverse inequality between the
two envelopes. If the standard envelope order supplies the forward
inequality on the Dirichlet domain and boundary, the upper envelope is a
Dirichlet solution. Later files should discharge the two analytic inputs via
supremum stability and the bump lemma.
-/
theorem PerronMethodExistenceTheorem
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hupper : DirichletSubsolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlower : DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (henvelopeOrder : ∀ x : Point n, x ∈ C ∪ boundary ->
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <=
        upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  let W : Point n -> Real := perronEnvelope C boundary F g B.lower B.upper
  have hupper_le_lower : ∀ x : Point n, x ∈ C ∪ boundary ->
      upperEnvelope C W x <= lowerEnvelope C W x := by
    intro x hx
    exact hcomparison hupper hlower x hx
  have hEqUnion : Set.EqOn (lowerEnvelope C W) (upperEnvelope C W) (C ∪ boundary) := by
    intro x hx
    exact le_antisymm (henvelopeOrder x hx) (hupper_le_lower x hx)
  have hEqC : Set.EqOn (lowerEnvelope C W) (upperEnvelope C W) C := by
    intro x hx
    exact hEqUnion (Or.inl hx)
  have hEqBoundary : Set.EqOn (lowerEnvelope C W) (upperEnvelope C W) boundary := by
    intro x hx
    exact hEqUnion (Or.inr hx)
  have hsuperUpper : DirichletSupersolutionOn C boundary F g (upperEnvelope C W) :=
    hlower.congr_eqOn hEqC hEqBoundary
  refine ⟨⟨hupper.viscosity, hsuperUpper.viscosity⟩, ?_⟩
  intro x hx
  exact le_antisymm (hupper.boundary_le hx) (hsuperUpper.boundary_le hx)

/--
Perron's method after the envelope boundary traces have been inherited from the
barriers.

Compared with `PerronMethodExistenceTheorem`, this statement asks only for the
interior viscosity properties of `W^*` and `W_*`. The Dirichlet boundary
inequalities are derived from the lower/upper barrier traces and the pointwise
Perron bounds.
-/
theorem PerronMethodExistenceTheorem.of_viscosityEnvelopes
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hupperVisc : ViscositySubsolution C F
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hupperSemi : UpperSemicontinuousOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) (C ∪ boundary))
    (hlowerVisc : ViscositySupersolution C F
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerSemi : LowerSemicontinuousOn
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) (C ∪ boundary))
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hperronCobddBelowOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsCoboundedUnder (· <= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hupperBddAboveOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelowOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hperronCobddAboveOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsCoboundedUnder (· >= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (henvelopeOrder : ∀ x : Point n, x ∈ C ∪ boundary ->
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <=
        upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem B hcomparison ?_ ?_ henvelopeOrder
  · exact ⟨hupperVisc,
      B.perronUpperEnvelope_boundarySubsolution hupperTrace
        hperronCobddBelowOnBoundary hupperBddAboveOnBoundary,
      hupperSemi⟩
  · exact ⟨hlowerVisc,
      B.perronLowerEnvelope_boundarySupersolution hlowerTrace
        hlowerBddBelowOnBoundary hperronCobddAboveOnBoundary,
      hlowerSemi⟩

/--
Variant of Perron's method where the elementary order `W_* <= W^*` is supplied
by local boundedness of the Perron envelope on every relevant `nhdsWithin`
filter.
-/
theorem PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_localBounded
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hupperVisc : ViscositySubsolution C F
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerVisc : ViscositySupersolution C F
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hperronCobddBelowOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsCoboundedUnder (· <= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hupperBddAboveOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelowOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hperronCobddAboveOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsCoboundedUnder (· >= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hperronBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hperronBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·)
        (perronEnvelope C boundary F g B.lower B.upper)) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  have hupperSemi := upperSemicontinuousOn_upperEnvelope_on
    hperronBddAbove (fun x hx => by
      let : (nhdsWithin x C).NeBot := hne x hx
      exact (hperronBddBelow x hx).isCoboundedUnder_le)
  have hlowerSemi := lowerSemicontinuousOn_lowerEnvelope_on
    hperronBddBelow (fun x hx => by
      let : (nhdsWithin x C).NeBot := hne x hx
      exact (hperronBddAbove x hx).isCoboundedUnder_ge)
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes B hcomparison
    hupperVisc hupperSemi hlowerVisc hlowerSemi hlowerTrace hupperTrace
    hperronCobddBelowOnBoundary hupperBddAboveOnBoundary
    hlowerBddBelowOnBoundary hperronCobddAboveOnBoundary ?_
  intro x hx
  let : (nhdsWithin x C).NeBot := hne x hx
  exact lowerEnvelope_le_upperEnvelope (hperronBddAbove x hx) (hperronBddBelow x hx)

/--
Perron's method with local boundedness supplied by the barrier pair.

For every `x ∈ C ∪ boundary`, if the upper barrier is locally bounded above
and the lower barrier is locally bounded below relative to `C`, then the
pointwise Perron envelope inherits the local boundedness needed for the
elementary envelope order `W_* <= W^*`. On boundary points the same hypotheses
also provide the coboundedness assumptions needed to pass the barrier trace
inequalities through `limsup` and `liminf`.
-/
theorem PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hupperVisc : ViscositySubsolution C F
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerVisc : ViscositySupersolution C F
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_localBounded
    B hcomparison hupperVisc hlowerVisc hlowerTrace hupperTrace
    ?_ ?_ ?_ ?_ hne ?_ ?_
  · intro x hx
    let : (nhdsWithin x C).NeBot := hne x (Or.inr hx)
    exact B.perronEnvelope_isCoboundedUnder_le (hlowerBddBelow x (Or.inr hx))
  · intro x hx
    exact hupperBddAbove x (Or.inr hx)
  · intro x hx
    exact hlowerBddBelow x (Or.inr hx)
  · intro x hx
    let : (nhdsWithin x C).NeBot := hne x (Or.inr hx)
    exact B.perronEnvelope_isCoboundedUnder_ge (hupperBddAbove x (Or.inr hx))
  · intro x hx
    exact B.perronEnvelope_isBoundedUnder_le (hupperBddAbove x hx)
  · intro x hx
    exact B.perronEnvelope_isBoundedUnder_ge (hlowerBddBelow x hx)

/--
After the upper Perron envelope has been certified as a Dirichlet
subsolution, comparison with the upper barrier places it back in the Perron
class.

This is the formal version of the first maximality step in the source proof:
`W^*` is admissible, hence it cannot lie above the Perron supremum.
-/
theorem DirichletBarrierPair.upperEnvelope_perronEnvelope_mem_perronClass
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hupper : DirichletSubsolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    PerronClass C boundary F g B.lower B.upper
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine ⟨hupper, ?_, ?_⟩
  · intro x hx
    rcases hx with hxC | hxBoundary
    · exact (B.lower_le_perronEnvelope (Or.inl hxC)).trans
        (le_upperEnvelope hxC
          (B.perronEnvelope_isBoundedUnder_le
            (hupperBddAbove x (Or.inl hxC))))
    · have hlower_le_g : B.lower x <= g x :=
        B.lower_dirichlet.boundary_le hxBoundary
      let : (nhdsWithin x C).NeBot := hne x (Or.inr hxBoundary)
      have hlowerEnv_le :
          lowerEnvelope C B.lower x <=
            lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x :=
        B.lowerEnvelope_le_perronEnvelope_lowerEnvelope
          (hlowerBddBelow x (Or.inr hxBoundary))
          (B.perronEnvelope_isCoboundedUnder_ge
            (hupperBddAbove x (Or.inr hxBoundary)))
      have henvOrder :
          lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <=
            upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x :=
        lowerEnvelope_le_upperEnvelope
          (B.perronEnvelope_isBoundedUnder_le
            (hupperBddAbove x (Or.inr hxBoundary)))
          (B.perronEnvelope_isBoundedUnder_ge
            (hlowerBddBelow x (Or.inr hxBoundary)))
      have hg_le_upper :
          g x <= upperEnvelope C
            (perronEnvelope C boundary F g B.lower B.upper) x := by
        calc
          g x = lowerEnvelope C B.lower x := (hlowerTrace x hxBoundary).symm
          _ <= lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x :=
            hlowerEnv_le
          _ <= upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x :=
            henvOrder
      exact hlower_le_g.trans hg_le_upper
  · intro x hx
    exact hcomparison hupper B.upper_dirichlet x hx

/--
The admissibility of `W^*` forces equality between the pointwise Perron
envelope `W` and its upper envelope on the PDE domain.
-/
theorem DirichletBarrierPair.upperEnvelope_perronEnvelope_eqOn_domain
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hupper : DirichletSubsolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    Set.EqOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
      (perronEnvelope C boundary F g B.lower B.upper) C := by
  intro x hx
  have hmem : PerronClass C boundary F g B.lower B.upper
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
    B.upperEnvelope_perronEnvelope_mem_perronClass hcomparison hupper
      hlowerTrace hne hupperBddAbove hlowerBddBelow
  exact le_antisymm
    (B.perronClass_le_perronEnvelope hmem (Or.inl hx))
    (le_upperEnvelope hx
      (B.perronEnvelope_isBoundedUnder_le (hupperBddAbove x (Or.inl hx))))

/--
Perron's method with the upper-envelope Dirichlet subsolution supplied by
half-relaxed-limit stability.

This discharges the `W^*` subsolution input from
`PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded`.
The remaining analytic input is the viscosity supersolution property of
`W_*`, which is the role of the Perron bump argument.
-/
theorem PerronMethodExistenceTheorem.of_upperHalfRelaxed_and_lowerViscosity_of_barrierLocalBounded
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    {ι : Type*} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hEq : upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) =
      ViscositySolns.upperHalfRelaxedLimit uᵢ l C)
    (hlowerVisc : ViscositySupersolution C F
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem B hcomparison ?_ ?_ ?_
  · refine B.perronUpperEnvelope_dirichletSubsolution_of_barrierLocalBounded
      hF hsub hbddAbove hcobddBelow hEq hupperTrace ?_ ?_ ?_ ?_
    · intro x hx
      exact hne x (Or.inr hx)
    · intro x hx
      exact hlowerBddBelow x (Or.inr hx)
    · intro x hx
      exact hupperBddAbove x (Or.inr hx)
    · exact B.perronUpperEnvelope_upperSemicontinuousOn hne
        hupperBddAbove hlowerBddBelow
  · refine ⟨hlowerVisc,
      B.perronLowerEnvelope_boundarySupersolution hlowerTrace ?_ ?_, ?_⟩
    · intro x hx
      exact hlowerBddBelow x (Or.inr hx)
    · intro x hx
      let : (nhdsWithin x C).NeBot := hne x (Or.inr hx)
      exact B.perronEnvelope_isCoboundedUnder_ge (hupperBddAbove x (Or.inr hx))
    · exact B.perronLowerEnvelope_lowerSemicontinuousOn hne
        hupperBddAbove hlowerBddBelow
  · intro x hx
    let : (nhdsWithin x C).NeBot := hne x hx
    exact lowerEnvelope_le_upperEnvelope
      (B.perronEnvelope_isBoundedUnder_le (hupperBddAbove x hx))
      (B.perronEnvelope_isBoundedUnder_ge (hlowerBddBelow x hx))

/--
Perron's method with both analytic envelope inputs exposed in the form produced
by the Perron construction.

The upper envelope is supplied by half-relaxed-limit stability. The lower
envelope is supplied by the subjet inequality that the localized bump argument
is meant to prove.
-/
theorem PerronMethodExistenceTheorem.of_upperHalfRelaxed_and_bumpInequality
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    {ι : Type*} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hEq : upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) =
      ViscositySolns.upperHalfRelaxedLimit uᵢ l C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hineq : PerronLowerEnvelopeSubjetInequality C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem B hcomparison ?_ ?_ ?_
  · refine B.perronUpperEnvelope_dirichletSubsolution_of_barrierLocalBounded
      hF hsub hbddAbove hcobddBelow hEq hupperTrace ?_ ?_ ?_ ?_
    · intro x hx
      exact hne x (Or.inr hx)
    · intro x hx
      exact hlowerBddBelow x (Or.inr hx)
    · intro x hx
      exact hupperBddAbove x (Or.inr hx)
    · exact B.perronUpperEnvelope_upperSemicontinuousOn hne
        hupperBddAbove hlowerBddBelow
  · exact B.perronLowerEnvelope_dirichletSupersolution_of_bumpInequality
      hlowerTrace hne hupperBddAbove hlowerBddBelow hineq
  · intro x hx
    let : (nhdsWithin x C).NeBot := hne x hx
    exact lowerEnvelope_le_upperEnvelope
      (B.perronEnvelope_isBoundedUnder_le (hupperBddAbove x hx))
      (B.perronEnvelope_isBoundedUnder_ge (hlowerBddBelow x hx))

/--
Perron's method with the lower-envelope supersolution supplied by the formal
bump contradiction.

This is the final assembly interface before the analytic localized bump
construction itself: the only lower-side hypothesis is that a failed subjet
inequality produces an impossible Perron-class function above the envelope.
-/
theorem PerronMethodExistenceTheorem.of_upperHalfRelaxed_and_bumpContradiction
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    {ι : Type*} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hEq : upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) =
      ViscositySolns.upperHalfRelaxedLimit uᵢ l C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hbump : PerronLowerEnvelopeBumpContradiction C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem B hcomparison ?_ ?_ ?_
  · refine B.perronUpperEnvelope_dirichletSubsolution_of_barrierLocalBounded
      hF hsub hbddAbove hcobddBelow hEq hupperTrace ?_ ?_ ?_ ?_
    · intro x hx
      exact hne x (Or.inr hx)
    · intro x hx
      exact hlowerBddBelow x (Or.inr hx)
    · intro x hx
      exact hupperBddAbove x (Or.inr hx)
    · exact B.perronUpperEnvelope_upperSemicontinuousOn hne
        hupperBddAbove hlowerBddBelow
  · exact B.perronLowerEnvelope_dirichletSupersolution_of_bumpContradiction
      hlowerTrace hne hupperBddAbove hlowerBddBelow hbump
  · intro x hx
    let : (nhdsWithin x C).NeBot := hne x hx
    exact lowerEnvelope_le_upperEnvelope
      (B.perronEnvelope_isBoundedUnder_le (hupperBddAbove x hx))
      (B.perronEnvelope_isBoundedUnder_ge (hlowerBddBelow x hx))

/--
Perron's method from the source-shaped strict patch form of Lemma 4.2.

The lower-side analytic input says that each failed lower-envelope subjet
inequality produces an admissible Perron-class member that is strictly above a
level greater than `W_* x` on a relative neighborhood of the failed contact.
-/
theorem PerronMethodExistenceTheorem.of_upperHalfRelaxed_and_strictPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    {ι : Type*} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hEq : upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) =
      ViscositySolns.upperHalfRelaxedLimit uᵢ l C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeStrictPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_upperHalfRelaxed_and_bumpContradiction
    B hcomparison hF hsub hbddAbove hcobddBelow hEq hlowerTrace hupperTrace
    hne hupperBddAbove hlowerBddBelow ?_
  exact B.perronLowerEnvelope_bumpContradiction_of_strictPatch
    (fun x hx => hne x (Or.inl hx))
    (fun x hx => hupperBddAbove x (Or.inl hx))
    hpatch

/--
Perron's method from the source-shaped bumped-subsolution form of Lemma 4.2.

Here the bump lemma only has to construct a Dirichlet subsolution patch above
the lower barrier. The upper-barrier bound needed for Perron-class membership
is obtained from the same explicit `DirichletComparisonPrinciple` hypothesis
used by the final Perron argument.
-/
theorem PerronMethodExistenceTheorem.of_upperHalfRelaxed_and_strictSubsolutionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    {ι : Type*} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hEq : upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) =
      ViscositySolns.upperHalfRelaxedLimit uᵢ l C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeStrictSubsolutionPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_upperHalfRelaxed_and_strictPatch
    B hcomparison hF hsub hbddAbove hcobddBelow hEq hlowerTrace hupperTrace
    hne hupperBddAbove hlowerBddBelow ?_
  exact B.strictPatch_of_strictSubsolutionPatch hcomparison hpatch

end ViscositySolns
