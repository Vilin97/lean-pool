/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionEquation
public import LeanPool.NavierStokesAndEuler.Euler.SobolevReflection
import LeanPool.NavierStokesAndEuler.Euler.SobolevParityOperators

/-! Joint odd symmetry of the actual correction source and its coercive pressure. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionParity

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace
  EulerSobolevCoefficientPressure EulerSobolevTransport EulerCorrectionOperators
  EulerCylinderReflection  EulerSobolevReflection EulerSobolevParityOperators

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Exact equivariance of the residual plus the linearized quadratic increment. -/
theorem linearized_source_equivariant (R : X →L[ℝ] X) (S : Y →L[ℝ] Y)
    (B : X →L[ℝ] X →L[ℝ] Y) (C : X →L[ℝ] Y) (z : X) (r : Y)
    (hB : ∀ u v, S (B u v) = B (R u) (R v)) (hC : ∀ u, S (C u) = C (R u))
    (hz : R z = z) (hr : S r = r) (e : X) :
    S (r + linearize B C z e + B e e) = r + linearize B C z (R e) + B (R e) (R e) := by
  simp only [linearize_apply, map_add, hB, hC, hz, hr]

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited Sobolev additive normed-group instance. -/
local instance correctionParityGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- The inherited real Sobolev module instance. -/
local instance correctionParitySpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) :=
    inferInstance

/-- Signed reflection on Sobolev fields has the literal signed L² value. -/
theorem value_oddReflection {q : ℕ} (u : SobolevSpace period q) :
    value period (oddReflection period q u) = -reflection period (value period u) := by
  change -value period (sobolevReflection period q u) = _
  rw [value_sobolevReflection]

/-- Actual almost-everywhere odd parity is precisely a fixed point of signed reflection. -/
theorem oddReflection_fixed_of_ae {q : ℕ} (u : SobolevSpace period q)
    (hu : ∀ᵐ x ∂liftMeasure period, value period u (-x) = -value period u x) :
    oddReflection period q u = u := by
  apply value_injective period
  rw [value_oddReflection]
  have hh : reflection period (value period u) = -value period u := by
    apply Lp.ext
    filter_upwards [reflection_ae period (value period u), Lp.coeFn_neg (value period u), hu]
      with x h1 h2 h3
    rw [h1, h2]
    exact h3
  rw [hh, neg_neg]

/-- Signed reflection commutes with restriction to the next Sobolev order. -/
theorem truncate_oddReflection {q : ℕ} (u : SobolevSpace period (q + 1)) :
    truncateOperator period q (oddReflection period (q+1) u) =
      oddReflection period q (truncateOperator period q u) := by
  simp only [oddReflection_apply, map_neg]
  exact congrArg Neg.neg (truncate_reflection period u)

/-- An actual even coefficient commutes with signed reflection. -/
theorem coefficient_oddReflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x) (u : SobolevSpace period q) :
    oddReflection period q (coefficientSobolevOperator period K u) =
      coefficientSobolevOperator period K (oddReflection period q u) := by
  simp only [oddReflection_apply, map_neg]
  exact congrArg Neg.neg (coefficient_reflection period K hA u)

/-- The actual pressure inverse commutes with signed reflection for an even metric. -/
theorem pressure_oddReflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    oddReflection period q (pressureSobolevOperator period K κ m c hc hpos u) =
      pressureSobolevOperator period K κ m c hc hpos (oddReflection period q u) := by
  simp only [oddReflection_apply, map_neg]
  exact congrArg Neg.neg (pressureSobolev_reflection period K hA κ m c hc hpos u)

/-- The actual pressure-corrected source commutes with signed reflection. -/
theorem projectedSource_oddReflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    oddReflection period q (projectedSourceOperator period K κ m c hc hpos u) =
      projectedSourceOperator period K κ m c hc hpos (oddReflection period q u) := by
  simp only [oddReflection_apply, map_neg]
  exact congrArg Neg.neg (projectedSource_reflection period K hA κ m c hc hpos u)

/-- The literal non-pressure correction source has odd-reflection symmetry
under the source's actual even linear and odd quadratic coefficients. -/
theorem rawSource_oddReflection {q : ℕ} (hq : 6 ≤ q) {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (t : T)
    (hL : ∀ x, (D.linear.coefficient t).coefficient (-x) = (D.linear.coefficient t).coefficient x)
    (hQ : ∀ i x, ((D.quadratic i).coefficient t).coefficient (-x) = -((D.quadratic i).coefficient
        t).coefficient x)
    (hz : oddReflection period (q + 1) (D.approximation t) = D.approximation t)
    (hr : oddReflection period q (D.residual t) = D.residual t)
    (e : SobolevSpace period (q + 1)) :
    oddReflection period q (D.rawSource period hq t e) =
      D.rawSource period hq t (oddReflection period (q+1) e) := by
  let L := velocityComponents D.κ D.direction
  let hLnorm := velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound
  let F := eulerBilinear period hq L hLnorm (fun i => coefficientSobolevOperator period
      ((D.quadratic i).jet t))
  let C := (coefficientSobolevOperator period (D.linear.jet t)).comp (truncateOperator period q)
  have hF (u v : SobolevSpace period (q+1)) : oddReflection period q (F u v) =
      F (oddReflection period (q+1) u) (oddReflection period (q+1) v) :=
    eulerBilinear_oddReflection period hq L hLnorm (fun i => (D.quadratic i).coefficient t)
      (fun i => (D.quadratic i).jet t) hQ u v
  have hC (u : SobolevSpace period (q+1)) : oddReflection period q (C u) = C (oddReflection period
      (q+1) u) :=
    (coefficient_oddReflection period (D.linear.jet t) hL (truncateOperator period q u)).trans
      (congrArg (coefficientSobolevOperator period (D.linear.jet t)) (truncate_oddReflection period
          u).symm)
  exact linearized_source_equivariant (oddReflection period (q+1)) (oddReflection period q) F C
    (D.approximation t) (D.residual t) hF hC hz hr e

/-- The genuine correction pressure transforms by signed reflection,
with its sign fixed by the actual pressure definition. -/
theorem correction_pressure_oddReflection {q : ℕ} (hq : 6 ≤ q) {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (t : T)
    (hG : ∀ x, (D.metric.coefficient t).coefficient (-x) = (D.metric.coefficient t).coefficient x)
    (hL : ∀ x, (D.linear.coefficient t).coefficient (-x) = (D.linear.coefficient t).coefficient x)
    (hQ : ∀ i x, ((D.quadratic i).coefficient t).coefficient (-x) = -((D.quadratic i).coefficient
        t).coefficient x)
    (hz : oddReflection period (q + 1) (D.approximation t) = D.approximation t)
    (hr : oddReflection period q (D.residual t) = D.residual t)
    (e : SobolevSpace period (q + 1)) :
    oddReflection period q (D.pressure period hq t e) =
      D.pressure period hq t (oddReflection period (q+1) e) := by
  change oddReflection period q (-(pressureSobolevOperator period (D.metric.jet t) D.κ D.direction
    D.coercivity D.coercivity_pos (D.metric_pos t) (D.rawSource period hq t e))) = _
  rw [map_neg]
  exact congrArg Neg.neg ((pressure_oddReflection period (D.metric.jet t) hG D.κ D.direction
    D.coercivity D.coercivity_pos (D.metric_pos t) (D.rawSource period hq t e)).trans
    (congrArg (pressureSobolevOperator period (D.metric.jet t) D.κ D.direction D.coercivity
        D.coercivity_pos
      (D.metric_pos t)) (rawSource_oddReflection period hq D t hL hQ hz hr e)))

/-- The literal projected nonlinear correction equation has the required
odd symmetry, derived from the concrete parity of its prescribed fields. -/
theorem correction_source_oddReflection {q : ℕ} (hq : 6 ≤ q) {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (t : T)
    (hG : ∀ x, (D.metric.coefficient t).coefficient (-x) = (D.metric.coefficient t).coefficient x)
    (hL : ∀ x, (D.linear.coefficient t).coefficient (-x) = (D.linear.coefficient t).coefficient x)
    (hQ : ∀ i x, ((D.quadratic i).coefficient t).coefficient (-x) = -((D.quadratic i).coefficient
        t).coefficient x)
    (hz : oddReflection period (q + 1) (D.approximation t) = D.approximation t)
    (hr : oddReflection period q (D.residual t) = D.residual t)
    (e : SobolevSpace period (q + 1)) :
    oddReflection period q ((D.coefficients period hq).apply t e) =
      (D.coefficients period hq).apply t (oddReflection period (q+1) e) := by
  change oddReflection period q (-(projectedSourceOperator period (D.metric.jet t) D.κ D.direction
    D.coercivity D.coercivity_pos (D.metric_pos t) (D.rawSource period hq t e))) = _
  rw [map_neg]
  exact congrArg Neg.neg ((projectedSource_oddReflection period (D.metric.jet t) hG D.κ D.direction
    D.coercivity D.coercivity_pos (D.metric_pos t) (D.rawSource period hq t e)).trans
    (congrArg (projectedSourceOperator period (D.metric.jet t) D.κ D.direction D.coercivity
        D.coercivity_pos
      (D.metric_pos t)) (rawSource_oddReflection period hq D t hL hQ hz hr e)))

end EulerCorrectionParity
