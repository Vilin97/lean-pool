/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftFinite
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyPressureParity

@[expose] public section

/-! Actual common pressure and a canonically normalized scalar graph pressure
constructed from all-order drift-aware input budgets. -/

noncomputable section

namespace EulerAllOrderDriftCorrection

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerAllOrderCorrectionData EulerCorrectionAssembly EulerGraphPressurePotential
  EulerMetricTransport EulerCylinderReflection EulerSobolevReflection EulerCorrectionOperators
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The actual signed L² pressure of the family constructed from drift-aware budgets. -/
def Budget.commonPressure (B : Budget period hT A) :
    C(Icc (0 : ℝ) T, LiftL2 period) :=
  (B.family period).commonPressure period

/-- Every constructed finite signed pressure realizes this same common L² pressure. -/
theorem Budget.signedPressurePath_value_common (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period ((B.family period).signedPressurePath period q hq t) =
      B.commonPressure period t :=
  (B.family period).signedPressurePath_value_common period (B.comparisonData period) q hq t

/-- The constructed pressure lies in the genuine closed lifted gradient space. -/
theorem Budget.commonPressure_gradient (B : Budget period hT A) (t : Icc (0 : ℝ) T) :
    B.commonPressure period t ∈ gradientSpace period A.κ A.direction :=
  (B.family period).commonPressure_gradient period t

/-- Actual continuous Sobolev realizations at every order of the same constructed pressure. -/
def Budget.pressureTower (B : Budget period hT A) : FieldTower period T :=
  (B.family period).pressureTower period (B.comparisonData period)

/-- The all-order tower represents exactly the pressure selected from the finite construction. -/
theorem Budget.pressureTower_value (B : Budget period hT A)
    (q : ℕ) (t : Icc (0 : ℝ) T) :
    value period ((B.pressureTower period).realization q t) = B.commonPressure period t :=
  (B.pressureTower period).value_eq q t

/-- Evaluating the genuine finite-order pressure solver on the constructed correction
gives exactly the corresponding realization of the common pressure tower. -/
theorem Budget.pressure_eq_realization (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    (A.atOrder period q).pressure period hq t (B.solution period q hq t) =
      (B.pressureTower period).realization q t :=
  congrArg (fun f => f t)
    ((B.family period).signedPressurePath_eq_realization period (B.comparisonData period) q hq)

/-- Bounded Sobolev evaluation fixes a canonical pointwise representative of the pressure. -/
def Budget.pointPressure (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Vector3 :=
  (B.family period).pointPressure period t x

/-- The canonical representative agrees almost everywhere with the actual constructed pressure. -/
theorem Budget.pointPressure_ae (B : Budget period hT A) (t : Icc (0 : ℝ) T) :
    (B.commonPressure period t : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      B.pointPressure period t :=
  (B.family period).pointPressure_ae period t

/-- The selected actual pressure representative is jointly continuous, including endpoint times. -/
theorem Budget.pointPressure_joint_continuous (B : Budget period hT A) :
    Continuous (B.pointPressure period).uncurry :=
  (B.family period).pointPressure_joint_continuous period

/-- The same pressure representative is smooth in all cylinder coordinates at every time. -/
theorem Budget.pointPressure_smooth (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (B.pointPressure period t) x) :=
  (B.family period).pointPressure_smooth period (B.comparisonData period) t x

/-- The actual graph pressure-gradient vector field of the constructed correction. -/
def Budget.graphPressure (B : Budget period hT A) (k : ℝ)
    (t : Icc (0 : ℝ) T) (x : Vector3) : Vector3 :=
  A.κ • B.pointPressure period t (cylinderGraph period k A.direction x)

/-- The actual graph vector field is jointly continuous in time and space. -/
theorem Budget.graphPressure_joint_continuous (B : Budget period hT A) (k : ℝ) :
    Continuous (B.graphPressure period k).uncurry :=
  (B.family period).graphPressure_joint_continuous period k

/-- Reciprocal-frequency graph restriction of the actual pressure has a genuine smooth potential. -/
theorem Budget.graphPressure_has_potential (B : Budget period hT A)
    (k : ℝ) (hk : k * A.κ = 1) (t : Icc (0 : ℝ) T) :
    ∃ q : Vector3 → ℝ, ContDiff ℝ ∞ q ∧
      ∀ x, gradient q x = B.graphPressure period k t x :=
  (B.family period).graphPressure_has_potential period (B.comparisonData period) k hk t

/-- The scalar graph pressure constructed by radial integration, with its additive gauge fixed at zero. -/
def Budget.normalizedGraphPotential (B : Budget period hT A) (k : ℝ)
    (t : Icc (0 : ℝ) T) (x : Vector3) : ℝ :=
  (B.family period).normalizedGraphPotential period k t x

/-- The constructed scalar pressure vanishes at the origin at every time. -/
theorem Budget.normalizedGraphPotential_zero (B : Budget period hT A)
    (k : ℝ) (t : Icc (0 : ℝ) T) : B.normalizedGraphPotential period k t 0 = 0 :=
  (B.family period).normalizedGraphPotential_zero period k t

/-- Fixing the gauge by the same radial formula at every time preserves joint continuity. -/
theorem Budget.normalizedGraphPotential_joint_continuous (B : Budget period hT A) (k : ℝ) :
    Continuous (B.normalizedGraphPotential period k).uncurry :=
  (B.family period).normalizedGraphPotential_joint_continuous period k

/-- The actual normalized scalar pressure is spatially smooth on each time slice. -/
theorem Budget.normalizedGraphPotential_smooth (B : Budget period hT A)
    (k : ℝ) (hk : k * A.κ = 1) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (B.normalizedGraphPotential period k t) :=
  (B.family period).normalizedGraphPotential_smooth period (B.comparisonData period) k hk t

/-- Its actual scalar gradient is precisely the signed pressure from the constructed correction. -/
theorem Budget.normalizedGraphPotential_gradient (B : Budget period hT A)
    (k : ℝ) (hk : k * A.κ = 1) (t : Icc (0 : ℝ) T) (x : Vector3) :
    gradient (B.normalizedGraphPotential period k t) x =
      A.κ • B.pointPressure period t (cylinderGraph period k A.direction x) :=
  (B.family period).normalizedGraphPotential_gradient period (B.comparisonData period) k hk t x

/-- No second normalized smooth potential can represent the same actual graph pressure. -/
theorem Budget.normalizedGraphPotential_unique (B : Budget period hT A)
    (k : ℝ) (t : Icc (0 : ℝ) T) (q : Vector3 → ℝ)
    (hq : ContDiff ℝ ∞ q)
    (hgrad : ∀ x, gradient q x = B.graphPressure period k t x) (hq0 : q 0 = 0) :
    B.normalizedGraphPotential period k t = q :=
  (B.family period).normalizedGraphPotential_unique period k t q hq hgrad hq0

/-- Prescribed odd data produce an odd actual common pressure gradient. -/
theorem Budget.commonPressure_odd (B : Budget period hT A) (P : ParityData period A)
    (t : Icc (0 : ℝ) T) :
    -reflection period (B.commonPressure period t) = B.commonPressure period t :=
  (B.family period).commonPressure_odd period (B.comparisonData period) P t

/-- Oddness holds pointwise for the canonical pressure representative. -/
theorem Budget.pointPressure_odd (B : Budget period hT A) (P : ParityData period A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    B.pointPressure period t (-x) = -B.pointPressure period t x :=
  (B.family period).pointPressure_odd period (B.comparisonData period) P t x

/-- The signed pressure gradient remains odd after physical phase-graph restriction. -/
theorem Budget.graphPressure_odd (B : Budget period hT A) (P : ParityData period A)
    (k : ℝ) (t : Icc (0 : ℝ) T) (x : Vector3) :
    B.graphPressure period k t (-x) = -B.graphPressure period k t x :=
  (B.family period).graphPressure_odd period (B.comparisonData period) P k t x

/-- The same canonical normalization makes the scalar graph pressure exactly even. -/
theorem Budget.normalizedGraphPotential_even (B : Budget period hT A) (P : ParityData period A)
    (k : ℝ) (t : Icc (0 : ℝ) T) (x : Vector3) :
    B.normalizedGraphPotential period k t (-x) = B.normalizedGraphPotential period k t x :=
  (B.family period).normalizedGraphPotential_even period (B.comparisonData period) P k t x

/-- The all-order drift-aware input budget constructs a common actual pressure,
a jointly continuous smooth spatial representative, and a canonically normalized
smooth scalar graph potential. No correction solution or pressure is assumed. -/
theorem exists_normalized_pressure (B : Budget period hT A) (k : ℝ) (hk : k * A.κ = 1) :
    ∃ (p : Icc (0 : ℝ) T → LiftDomain period → Vector3)
      (Q : Icc (0 : ℝ) T → Vector3 → ℝ),
      (∀ t, (B.commonPressure period t : LiftDomain period → Vector3) =ᵐ[liftMeasure period] p t) ∧
      Continuous p.uncurry ∧
      (∀ t x, ContDiff ℝ ∞ (localFieldLift period (p t) x)) ∧
      Continuous Q.uncurry ∧ (∀ t, Q t 0 = 0) ∧
      (∀ t, ContDiff ℝ ∞ (Q t)) ∧
      ∀ t x, gradient (Q t) x = A.κ • p t (cylinderGraph period k A.direction x) :=
  ⟨B.pointPressure period, B.normalizedGraphPotential period k,
    B.pointPressure_ae period, B.pointPressure_joint_continuous period,
    B.pointPressure_smooth period, B.normalizedGraphPotential_joint_continuous period k,
    B.normalizedGraphPotential_zero period k, B.normalizedGraphPotential_smooth period k hk,
    B.normalizedGraphPotential_gradient period k hk⟩

/-- With parity of the prescribed data, the same constructed pressure representative
is odd and its canonically normalized scalar graph potential is even. -/
theorem exists_odd_normalized_pressure (B : Budget period hT A) (P : ParityData period A)
    (k : ℝ) (hk : k * A.κ = 1) :
    ∃ (p : Icc (0 : ℝ) T → LiftDomain period → Vector3)
      (Q : Icc (0 : ℝ) T → Vector3 → ℝ),
      (∀ t, (B.commonPressure period t : LiftDomain period → Vector3) =ᵐ[liftMeasure period] p t) ∧
      Continuous p.uncurry ∧
      (∀ t x, ContDiff ℝ ∞ (localFieldLift period (p t) x)) ∧
      (∀ t x, p t (-x) = -p t x) ∧
      Continuous Q.uncurry ∧ (∀ t, Q t 0 = 0) ∧
      (∀ t, ContDiff ℝ ∞ (Q t)) ∧ (∀ t x, Q t (-x) = Q t x) ∧
      ∀ t x, gradient (Q t) x = A.κ • p t (cylinderGraph period k A.direction x) :=
  ⟨B.pointPressure period, B.normalizedGraphPotential period k,
    B.pointPressure_ae period, B.pointPressure_joint_continuous period,
    B.pointPressure_smooth period, B.pointPressure_odd period P,
    B.normalizedGraphPotential_joint_continuous period k, B.normalizedGraphPotential_zero period k,
    B.normalizedGraphPotential_smooth period k hk, B.normalizedGraphPotential_even period P k,
    B.normalizedGraphPotential_gradient period k hk⟩

end EulerAllOrderDriftCorrection
