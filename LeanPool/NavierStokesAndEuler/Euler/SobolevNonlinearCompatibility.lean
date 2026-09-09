/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AsymmetricTransport
public import LeanPool.NavierStokesAndEuler.Euler.SobolevPressureResolvent

@[expose] public section

/-! Exact consistency of actual products, transport, and pressure across the Sobolev scale. -/

noncomputable section

namespace EulerSobolevNonlinearCompatibility

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevL2Product EulerSobolevTransport EulerAsymmetricTransport
  EulerSobolevCoefficientPressure EulerGevreyOrderZero EulerCorrectionOperators EulerVectorCylinder
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

local instance nonlinearCompatGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
  inferInstance
local instance nonlinearCompatSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance
local instance nonlinearCompatBilinearGroup (q : ℕ) : SeminormedAddCommGroup
    (SobolevSpace period q →L[ℝ] SobolevSpace period q →L[ℝ] SobolevSpace period q) := inferInstance

/-- Actual Sobolev products restrict to the same pointwise product at every lower algebra level. -/
theorem restrict_productHq {p q : ℕ} (hp : 6 ≤ p) (hq : 6 ≤ q) (hqp : q ≤ p)
    (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (u v : SobolevSpace period p) :
    restrictOperator period hqp (productHq period hp L hL u v) =
      productHq period hq L hL (restrictOperator period hqp u) (restrictOperator period hqp v) := by
  apply value_injective period
  rw [value_restrictOperator, productHq_value, productHq_value, value_restrictOperator]
  exact scalarProduct_of_value_eq period (by omega : 3 ≤ p) (by omega : 3 ≤ q) L u
    (restrictOperator period hqp u) rfl (value period v)

/-- Actual asymmetric transport restricts to the identical lower-order nonlinear field. -/
theorem restrict_asymmetricTransport {p q : ℕ} (hp : 6 ≤ p) (hq : 6 ≤ q) (hqp : q ≤ p)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u : SobolevSpace period p) (v : SobolevSpace period (p+1)) :
    restrictOperator period hqp (asymmetricTransport period hp L hL u v) =
      asymmetricTransport period hq L hL (restrictOperator period hqp u)
        (restrictOperator period (Nat.succ_le_succ hqp) v) := by
  simp only [asymmetricTransport_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [restrict_productHq period hp hq hqp (L i) (hL i) u (derivativeOperator period p i v),
    restrictOperator_derivative period hqp i v]

/-- The genuine pointwise coefficient action is independent of the chosen Sobolev order. -/
theorem restrict_coefficient {p q : ℕ} (hqp : q ≤ p) {A : SmoothCoefficient period}
    (KP : CoefficientJet period standardDirection p A) (KQ : CoefficientJet period
      standardDirection q A)
    (u : SobolevSpace period p) :
    restrictOperator period hqp (coefficientSobolevOperator period KP u) =
      coefficientSobolevOperator period KQ (restrictOperator period hqp u) := by
  apply value_injective period
  rw [value_restrictOperator, coefficientSobolevOperator_value, coefficientSobolevOperator_value,
    value_restrictOperator]

/-- The actual coercive pressure solve agrees at every Sobolev order by its unique L² value. -/
theorem restrict_pressure {p q : ℕ} (hqp : q ≤ p) {A : SmoothCoefficient period}
    (KP : CoefficientJet period standardDirection p A) (KQ : CoefficientJet period
      standardDirection q A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ) (u : SobolevSpace period p) :
    restrictOperator period hqp (pressureSobolevOperator period KP κ m c hc hpos u) =
      pressureSobolevOperator period KQ κ m c hc hpos (restrictOperator period hqp u) := by
  apply value_injective period
  rw [value_restrictOperator, pressureSobolevOperator_value, pressureSobolevOperator_value,
    value_restrictOperator]

/-- The projected Euler forcing is exactly consistent across the finite Sobolev scale. -/
theorem restrict_projectedSource {p q : ℕ} (hqp : q ≤ p) {A : SmoothCoefficient period}
    (KP : CoefficientJet period standardDirection p A) (KQ : CoefficientJet period
      standardDirection q A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ) (u : SobolevSpace period p) :
    restrictOperator period hqp (projectedSourceOperator period KP κ m c hc hpos u) =
      projectedSourceOperator period KQ κ m c hc hpos (restrictOperator period hqp u) := by
  apply value_injective period
  rw [value_restrictOperator, projectedSourceOperator_value, projectedSourceOperator_value,
    value_restrictOperator]

/-- The actual order-zero algebraic term as a bilinear map on one complete Sobolev level. -/
def algebraicAtBilinear {s : ℕ} (hs : 6 ≤ s)
    (C : Fin 3 → SobolevSpace period s →L[ℝ] SobolevSpace period s) :
    SobolevSpace period s →L[ℝ] SobolevSpace period s →L[ℝ] SobolevSpace period s :=
  ∑ i : Fin 3, postcompose (C i) (productHqBilinear period hs (coordinate 3 i) (coordinate_norm_le
    3 i))

/-- This bilinear map is precisely the already bounded order-zero Euler term. -/
theorem algebraicAtBilinear_apply {s : ℕ} (hs : 6 ≤ s)
    (C : Fin 3 → SobolevSpace period s →L[ℝ] SobolevSpace period s) (u v : SobolevSpace period s) :
    algebraicAtBilinear period hs C u v = algebraicAt period hs C u v := by
  simp only [algebraicAtBilinear, sum_apply, postcompose_apply, productHqBilinear_apply,
    algebraicAt]

end EulerSobolevNonlinearCompatibility
