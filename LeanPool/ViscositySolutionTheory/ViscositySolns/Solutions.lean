/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Operators.Continuity
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Semijets.Closure

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Viscosity subsolutions, supersolutions, and solutions

This file contains viscosity solution predicates, their test-function
formulation, closed-semijet consequences, and solution-level negation duality.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

theorem upperSemicontinuousOn_neg {C : Set (Point n)} {u : Point n -> Real}
    (hu : UpperSemicontinuousOn u C) :
    LowerSemicontinuousOn (fun x => -u x) C := by
  simpa [Function.comp_def] using
    (continuous_neg.comp_upperSemicontinuousOn_antitone hu
      (fun _ _ h => neg_le_neg h))

theorem lowerSemicontinuousOn_neg {C : Set (Point n)} {u : Point n -> Real}
    (hu : LowerSemicontinuousOn u C) :
    UpperSemicontinuousOn (fun x => -u x) C := by
  simpa [Function.comp_def] using
    (continuous_neg.comp_lowerSemicontinuousOn_antitone hu
      (fun _ _ h => neg_le_neg h))

/-- Viscosity subsolution of `F = 0` on `C`, using superjets. -/
def ViscositySubsolution (C : Set (Point n)) (F : Operator n) (u : Point n -> Real) : Prop :=
  UpperSemicontinuousOn u C /\
    forall x : Point n, x ∈ C -> forall J : Jet n, J ∈ Superjet C u x ->
      F x (u x) J.gradient J.hessian <= 0

/-- Viscosity supersolution of `F = 0` on `C`, using subjets. -/
def ViscositySupersolution (C : Set (Point n)) (F : Operator n) (u : Point n -> Real) : Prop :=
  LowerSemicontinuousOn u C /\
    forall x : Point n, x ∈ C -> forall J : Jet n, J ∈ Subjet C u x ->
      0 <= F x (u x) J.gradient J.hessian

/--
The test-function formulation of viscosity subsolutions, using functions with a
second-order expansion such that `{y | u y <= φ y}` is a relative neighborhood
of the contact point in `C`.
-/
def TestFunctionSubsolution (C : Set (Point n)) (F : Operator n) (u : Point n -> Real) :
    Prop :=
  UpperSemicontinuousOn u C /\
    forall x : Point n, x ∈ C -> forall J : Jet n, forall φ : Point n -> Real,
      Filter.Eventually (fun y : Point n => u y <= φ y) (nhdsWithin x C) ->
        HasSecondOrderExpansionWithinAtValue C φ x (u x) J ->
          F x (u x) J.gradient J.hessian <= 0

/--
The test-function formulation of viscosity supersolutions, using functions with
a second-order expansion such that `{y | φ y <= u y}` is a relative
neighborhood of the contact point in `C`.
-/
def TestFunctionSupersolution (C : Set (Point n)) (F : Operator n) (u : Point n -> Real) :
    Prop :=
  LowerSemicontinuousOn u C /\
    forall x : Point n, x ∈ C -> forall J : Jet n, forall φ : Point n -> Real,
      Filter.Eventually (fun y : Point n => φ y <= u y) (nhdsWithin x C) ->
        HasSecondOrderExpansionWithinAtValue C φ x (u x) J ->
          0 <= F x (u x) J.gradient J.hessian

/-- The jet and abstract test-function formulations of subsolutions are equivalent. -/
theorem viscositySubsolution_iff_testFunctionSubsolution
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} :
    ViscositySubsolution C F u <-> TestFunctionSubsolution C F u := by
  constructor
  · rintro ⟨husc, hjet⟩
    refine ⟨husc, ?_⟩
    intro x hx J φ h_le hφ
    exact hjet x hx J
      (superjet_of_eventually_le_of_hasSecondOrderExpansionWithinAtValue h_le hφ)
  · rintro ⟨husc, htest⟩
    refine ⟨husc, ?_⟩
    intro x hx J hJ
    rcases
      (superjet_iff_exists_eventually_le_hasSecondOrderExpansionWithinAtValue.mp hJ) with
      ⟨φ, h_le, hφ⟩
    exact htest x hx J φ h_le hφ

/-- The jet and abstract test-function formulations of supersolutions are equivalent. -/
theorem viscositySupersolution_iff_testFunctionSupersolution
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} :
    ViscositySupersolution C F u <-> TestFunctionSupersolution C F u := by
  constructor
  · rintro ⟨hlsc, hjet⟩
    refine ⟨hlsc, ?_⟩
    intro x hx J φ h_le hφ
    exact hjet x hx J
      (subjet_of_eventually_le_of_hasSecondOrderExpansionWithinAtValue h_le hφ)
  · rintro ⟨hlsc, htest⟩
    refine ⟨hlsc, ?_⟩
    intro x hx J hJ
    rcases
      (subjet_iff_exists_eventually_le_hasSecondOrderExpansionWithinAtValue.mp hJ) with
      ⟨φ, h_le, hφ⟩
    exact htest x hx J φ h_le hφ

/--
A viscosity subsolution satisfies the expected inequality for every touching
test function with a second-order expansion.
-/
theorem ViscositySubsolution.of_touchesAbove_hasSecondOrderExpansionWithin
    {C : Set (Point n)} {F : Operator n} {u φ : Point n -> Real} {x : Point n} {J : Jet n}
    (hu : ViscositySubsolution C F u) (hx : x ∈ C)
    (htouch : TouchesAboveOn C u φ x)
    (hφ : HasSecondOrderExpansionWithin C φ x J) :
    F x (u x) J.gradient J.hessian <= 0 :=
  hu.2 x hx J (superjet_of_touchesAbove_hasSecondOrderExpansionWithin htouch hφ)

/--
A viscosity supersolution satisfies the expected inequality for every touching
test function with a second-order expansion.
-/
theorem ViscositySupersolution.of_touchesBelow_hasSecondOrderExpansionWithin
    {C : Set (Point n)} {F : Operator n} {u φ : Point n -> Real} {x : Point n} {J : Jet n}
    (hu : ViscositySupersolution C F u) (hx : x ∈ C)
    (htouch : TouchesBelowOn C u φ x)
    (hφ : HasSecondOrderExpansionWithin C φ x J) :
    0 <= F x (u x) J.gradient J.hessian :=
  hu.2 x hx J (subjet_of_touchesBelow_hasSecondOrderExpansionWithin htouch hφ)

theorem ViscositySubsolution.closedSuperjet_le_of_isClosed
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hu : ViscositySubsolution C F u)
    (hclosed : IsClosed {z : (Point n × Real) × Jet n | operatorGraphEval F z <= 0})
    (hJ : J ∈ ClosedSuperjet C u x) :
    F x (u x) J.gradient J.hessian <= 0 :=
  closedSuperjet_induction hclosed
    (fun y hy K hK => hu.2 y hy K hK) hJ

theorem ViscositySupersolution.closedSubjet_nonneg_of_isClosed
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hu : ViscositySupersolution C F u)
    (hclosed : IsClosed {z : (Point n × Real) × Jet n | 0 <= operatorGraphEval F z})
    (hJ : J ∈ ClosedSubjet C u x) :
    0 <= F x (u x) J.gradient J.hessian :=
  closedSubjet_induction hclosed
    (fun y hy K hK => hu.2 y hy K hK) hJ

theorem ViscositySubsolution.closedSuperjet_le_of_continuous
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hu : ViscositySubsolution C F u)
    (hF : Continuous (operatorGraphEval F))
    (hJ : J ∈ ClosedSuperjet C u x) :
    F x (u x) J.gradient J.hessian <= 0 :=
  hu.closedSuperjet_le_of_isClosed (isClosed_Iic.preimage hF) hJ

theorem ViscositySubsolution.closedSuperjet_le_of_operatorContinuous
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hu : ViscositySubsolution C F u)
    (hF : OperatorContinuous F)
    (hJ : J ∈ ClosedSuperjet C u x) :
    F x (u x) J.gradient J.hessian <= 0 :=
  hu.closedSuperjet_le_of_isClosed hF.isClosed_le_zero hJ

theorem ViscositySupersolution.closedSubjet_nonneg_of_continuous
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hu : ViscositySupersolution C F u)
    (hF : Continuous (operatorGraphEval F))
    (hJ : J ∈ ClosedSubjet C u x) :
    0 <= F x (u x) J.gradient J.hessian :=
  hu.closedSubjet_nonneg_of_isClosed (isClosed_Ici.preimage hF) hJ

theorem ViscositySupersolution.closedSubjet_nonneg_of_operatorContinuous
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hu : ViscositySupersolution C F u)
    (hF : OperatorContinuous F)
    (hJ : J ∈ ClosedSubjet C u x) :
    0 <= F x (u x) J.gradient J.hessian :=
  hu.closedSubjet_nonneg_of_isClosed hF.isClosed_zero_le hJ

/-- Viscosity solution of `F = 0` on `C`. -/
def ViscositySolution (C : Set (Point n)) (F : Operator n) (u : Point n -> Real) : Prop :=
  ViscositySubsolution C F u /\ ViscositySupersolution C F u

theorem ViscositySolution.subsolution {C : Set (Point n)} {F : Operator n}
    {u : Point n -> Real} (hu : ViscositySolution C F u) :
    ViscositySubsolution C F u :=
  hu.1

theorem ViscositySolution.supersolution {C : Set (Point n)} {F : Operator n}
    {u : Point n -> Real} (hu : ViscositySolution C F u) :
    ViscositySupersolution C F u :=
  hu.2

/--
Neg duality for subsolutions (CIL Remark 2.6): `u` is a viscosity subsolution
of `F = 0` if and only if `-u` is a viscosity supersolution of
`negOperator F = 0`.
-/
theorem viscositySubsolution_neg_iff {C : Set (Point n)} {F : Operator n}
    {u : Point n -> Real} :
    ViscositySubsolution C F u ↔
      ViscositySupersolution C (negOperator F) (fun y => -u y) := by
  constructor
  · rintro ⟨husc, hjet⟩
    refine ⟨upperSemicontinuousOn_neg husc, fun x hx J hJ => ?_⟩
    have hJ' : J.neg ∈ Superjet C u x := by
      have h := (subjet_neg_iff_superjet (J := J)).mp hJ
      simpa [neg_neg] using h
    have h := hjet x hx J.neg hJ'
    simp only [Jet.neg_gradient, Jet.neg_hessian] at h
    simp only [negOperator, neg_neg]
    linarith
  · rintro ⟨hlsc, hjet⟩
    refine ⟨?_, fun x hx J hJ => ?_⟩
    · simpa [neg_neg] using lowerSemicontinuousOn_neg hlsc
    · have hJ' : J.neg ∈ Subjet C (fun y => -u y) x :=
        (superjet_neg_iff_subjet (J := J)).mp hJ
      have h := hjet x hx J.neg hJ'
      simp only [negOperator, Jet.neg_gradient, Jet.neg_hessian, neg_neg] at h
      linarith

/--
Neg duality for supersolutions: `u` is a viscosity supersolution of `F = 0`
if and only if `-u` is a viscosity subsolution of `negOperator F = 0`.
-/
theorem viscositySupersolution_neg_iff {C : Set (Point n)} {F : Operator n}
    {u : Point n -> Real} :
    ViscositySupersolution C F u ↔
      ViscositySubsolution C (negOperator F) (fun y => -u y) := by
  constructor
  · rintro ⟨hlsc, hjet⟩
    refine ⟨lowerSemicontinuousOn_neg hlsc, fun x hx J hJ => ?_⟩
    have hJ' : J.neg ∈ Subjet C u x := by
      have h := (superjet_neg_iff_subjet (J := J) (u := fun y => -u y)).mp hJ
      simpa [neg_neg] using h
    have h := hjet x hx J.neg hJ'
    simp only [Jet.neg_gradient, Jet.neg_hessian] at h
    simp only [negOperator, neg_neg]
    linarith
  · rintro ⟨husc, hjet⟩
    refine ⟨?_, fun x hx J hJ => ?_⟩
    · simpa [neg_neg] using upperSemicontinuousOn_neg husc
    · have hJ' : J.neg ∈ Superjet C (fun y => -u y) x :=
        (subjet_neg_iff_superjet (J := J)).mp hJ
      have h := hjet x hx J.neg hJ'
      simp only [negOperator, Jet.neg_gradient, Jet.neg_hessian, neg_neg] at h
      linarith

/--
Neg duality for viscosity solutions: `u` solves `F = 0` exactly when `-u`
solves `negOperator F = 0`.
-/
theorem viscositySolution_neg_iff {C : Set (Point n)} {F : Operator n}
    {u : Point n -> Real} :
    ViscositySolution C F u ↔
      ViscositySolution C (negOperator F) (fun y => -u y) := by
  constructor
  · intro hu
    exact ⟨viscositySupersolution_neg_iff.mp hu.2,
      viscositySubsolution_neg_iff.mp hu.1⟩
  · intro hu
    exact ⟨viscositySubsolution_neg_iff.mpr hu.2,
      viscositySupersolution_neg_iff.mpr hu.1⟩

end ViscositySolns
