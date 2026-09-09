/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevCoefficientPressure

/-! Exact resolvent identities for the actual coercive pressure operators on complete Sobolev
spaces. -/

@[expose] public section


noncomputable section

namespace EulerSobolevCoefficientPressure

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Underlying L² evaluation respects addition of complete Sobolev elements. -/
@[simp]
theorem value_add {q : ℕ} (u v : SobolevSpace period q) : value period (u + v) = value period u +
    value period v := rfl

/-- Underlying L² evaluation respects subtraction of complete Sobolev elements. -/
@[simp]
theorem value_sub {q : ℕ} (u v : SobolevSpace period q) : value period (u - v) = value period u -
    value period v := rfl

/-- Every actual Sobolev pressure takes values in the closed lifted gradient space. -/
theorem pressureSobolev_mem_gradient {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    value period (pressureSobolevOperator period K κ m c hc hpos u) ∈ gradientSpace period κ m := by
  rw [pressureSobolevOperator_value]
  exact liftedPressure_mem period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos _

/-- The actual Sobolev pressure solves the original projected coefficient equation. -/
theorem pressureSobolev_equation {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    gradientProjection period κ m
      (A.operator (value period (pressureSobolevOperator period K κ m c hc hpos u))) =
        gradientProjection period κ m (value period u) := by
  rw [pressureSobolevOperator_value]
  exact liftedPressure_equation period κ m A.coefficient A.measurable A.bound A.norm_bound c hc
      hpos _

/-- Uniqueness of the Lax–Milgram solution gives uniqueness in the complete Sobolev space. -/
theorem pressureSobolev_unique {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (u p : SobolevSpace period q) (hp : value period p ∈ gradientSpace period κ m)
    (heq : gradientProjection period κ m (A.operator (value period p)) =
      gradientProjection period κ m (value period u)) :
    p = pressureSobolevOperator period K κ m c hc hpos u := by
  apply value_injective period
  rw [pressureSobolevOperator_value]
  exact liftedPressure_unique period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos
    (value period u) (value period p) hp heq

/-- The actual projected forcing lies in the lifted divergence-free space. -/
theorem projectedSource_divergenceFree {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    value period (projectedSourceOperator period K κ m c hc hpos u) ∈ divergenceFreeSpace period κ
        m := by
  apply (gradientSpace period κ m).orthogonalProjectionOnto_eq_zero_iff.mp
  apply Subtype.ext
  exact projectedSource_gradient_zero period K κ m c hc hpos u

/-- The difference of actual coefficient multipliers has the expected underlying L² action. -/
theorem coefficientDifference_value {q : ℕ} {A B : SmoothCoefficient period}
    (KA : CoefficientJet period standardDirection q A) (KB : CoefficientJet period
        standardDirection q B)
    (u : SobolevSpace period q) :
    value period ((coefficientSobolevOperator period KB - coefficientSobolevOperator period KA) u) =
      (B.operator - A.operator) (value period u) := by
  change value period (coefficientSobolevOperator period KB u - coefficientSobolevOperator period
      KA u) = _
  rw [value_sub, coefficientSobolevOperator_value period KB u, coefficientSobolevOperator_value
      period KA u]
  rfl

/-- The coercive L² pressure satisfies the exact resolvent formula by uniqueness of its projected
equation. -/
theorem pressureL2_resolvent_apply (A B : SmoothCoefficient period) (κ : ℝ) (m : Vector3)
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hA : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hB : ∀ x v, d * ‖v‖ ^ 2 ≤ ⟪B.coefficient x v, v⟫_ℝ) (f : LiftL2 period) :
    A.pressure κ m c hc hA f - B.pressure κ m d hd hB f =
      A.pressure κ m c hc hA ((B.operator - A.operator) (B.pressure κ m d hd hB f)) := by
  apply liftedPressure_unique period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hA
  · exact (gradientSpace period κ m).sub_mem
      (liftedPressure_mem period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hA f)
      (liftedPressure_mem period κ m B.coefficient B.measurable B.bound B.norm_bound d hd hB f)
  · have hPA := liftedPressure_equation period κ m A.coefficient A.measurable A.bound A.norm_bound
      c hc hA f
    have hPB := liftedPressure_equation period κ m B.coefficient B.measurable B.bound B.norm_bound
        d hd hB f
    change gradientProjection period κ m (A.operator (A.pressure κ m c hc hA f)) =
      gradientProjection period κ m f at hPA
    change gradientProjection period κ m (B.operator (B.pressure κ m d hd hB f)) =
      gradientProjection period κ m f at hPB
    change gradientProjection period κ m (A.operator
      (A.pressure κ m c hc hA f - B.pressure κ m d hd hB f)) =
      gradientProjection period κ m ((B.operator - A.operator) (B.pressure κ m d hd hB f))
    rw [map_sub, map_sub, sub_apply, map_sub, hPA, hPB]

/-- The genuine Sobolev pressure inverses obey the exact resolvent identity on every forcing. -/
theorem pressure_resolvent_apply {q : ℕ} {A B : SmoothCoefficient period}
    (KA : CoefficientJet period standardDirection q A) (KB : CoefficientJet period
        standardDirection q B)
    (κ : ℝ) (m : Vector3) (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hA : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hB : ∀ x v, d * ‖v‖ ^ 2 ≤ ⟪B.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    pressureSobolevOperator period KA κ m c hc hA u - pressureSobolevOperator period KB κ m d hd hB
        u =
      pressureSobolevOperator period KA κ m c hc hA
        ((coefficientSobolevOperator period KB - coefficientSobolevOperator period KA)
          (pressureSobolevOperator period KB κ m d hd hB u)) := by
  apply value_injective period
  rw [value_sub, pressureSobolevOperator_value period KA κ m c hc hA u,
    pressureSobolevOperator_value period KB κ m d hd hB u,
    pressureSobolevOperator_value period KA κ m c hc hA,
    coefficientDifference_value period KA KB,
    pressureSobolevOperator_value period KB κ m d hd hB u]
  exact pressureL2_resolvent_apply period A B κ m c d hc hd hA hB (value period u)

/-- The genuine pressure resolvent identity as an equality of Sobolev continuous linear maps. -/
theorem pressure_resolvent {q : ℕ} {A B : SmoothCoefficient period}
    (KA : CoefficientJet period standardDirection q A) (KB : CoefficientJet period
        standardDirection q B)
    (κ : ℝ) (m : Vector3) (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hA : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hB : ∀ x v, d * ‖v‖ ^ 2 ≤ ⟪B.coefficient x v, v⟫_ℝ) :
    pressureSobolevOperator period KA κ m c hc hA - pressureSobolevOperator period KB κ m d hd hB =
      (pressureSobolevOperator period KA κ m c hc hA).comp
        ((coefficientSobolevOperator period KB - coefficientSobolevOperator period KA).comp
          (pressureSobolevOperator period KB κ m d hd hB)) := by
  apply ContinuousLinearMap.ext
  intro u
  exact pressure_resolvent_apply period KA KB κ m c d hc hd hA hB u

/-- The norm of the genuine pressure difference is controlled by the coefficient multiplier
difference. -/
theorem pressure_resolvent_bound {q : ℕ} {A B : SmoothCoefficient period}
    (KA : CoefficientJet period standardDirection q A) (KB : CoefficientJet period
        standardDirection q B)
    (κ : ℝ) (m : Vector3) (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hA : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hB : ∀ x v, d * ‖v‖ ^ 2 ≤ ⟪B.coefficient x v, v⟫_ℝ) :
    ‖pressureSobolevOperator period KA κ m c hc hA - pressureSobolevOperator period KB κ m d hd hB‖
        ≤
      ‖pressureSobolevOperator period KA κ m c hc hA‖ *
        ‖coefficientSobolevOperator period KB - coefficientSobolevOperator period KA‖ *
          ‖pressureSobolevOperator period KB κ m d hd hB‖ := by
  rw [pressure_resolvent period KA KB κ m c d hc hd hA hB]
  exact ContinuousLinearMap.opNorm_comp_le _ _ |>.trans
    ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans_eq
      (mul_assoc _ _ _).symm)

end EulerSobolevCoefficientPressure
