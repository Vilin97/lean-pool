/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevReflection
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionOperators

@[expose] public section

/-! Reflection covariance of the literal Sobolev product, transport and pressure operators. -/

noncomputable section

namespace EulerSobolevParityOperators

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace
  EulerSobolevCoefficientPressure EulerSobolevL2Product EulerSobolevTransport
    EulerCorrectionOperators
  EulerCylinderReflection EulerGradientReflection EulerSobolevReflection

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited Sobolev additive normed-group instance. -/
local instance paritySobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
  inferInstance
/-- The inherited real Sobolev module instance. -/
local instance paritySobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance
/-- The inherited normed-group instance on the actual bilinear operator space. -/
local instance parityBilinearGroup (q : ℕ) : SeminormedAddCommGroup
    (SobolevSpace period (q+1) →L[ℝ] SobolevSpace period (q+1) →L[ℝ] SobolevSpace period q) :=
      inferInstance

/-- Reflection of the actual Sobolev product is the product of reflected fields. -/
theorem product_reflection {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period q) :
    sobolevReflection period q (productHq period hq L hL u v) =
      productHq period hq L hL (sobolevReflection period q u) (sobolevReflection period q v) := by
  apply value_injective period
  rw [value_sobolevReflection]
  apply Lp.ext
  have hp := productHq_ae period hq L hL (sobolevReflection period q u) (sobolevReflection period q
    v)
  simp only [value_sobolevReflection] at hp
  filter_upwards [reflection_ae period (value period (productHq period hq L hL u v)),
    (measurePreserving_reflection period).quasiMeasurePreserving.ae (productHq_ae period hq L hL u
      v),
    hp, reflection_ae period (value period u), reflection_ae period (value period v)]
    with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5]

/-- The actual bilinear Sobolev product changes sign in its second input. -/
theorem product_neg_right {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period q) :
    productHq period hq L hL u (-v) = -productHq period hq L hL u v :=
  map_neg (productHqBilinear period hq L hL u) v

/-- The literal transport operator reverses under joint pullback reflection. -/
theorem transport_reflection {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (q+1)) :
    transportBilinear period hq L hL (sobolevReflection period (q+1) u) (sobolevReflection period
      (q+1) v) =
      -sobolevReflection period q (transportBilinear period hq L hL u v) := by
  have hi (i : Fin 4) :
      productHq period hq (L i) (hL i) (truncateOperator period q (sobolevReflection period (q+1)
        u))
        (derivativeOperator period q i (sobolevReflection period (q+1) v)) =
      -sobolevReflection period q (productHq period hq (L i) (hL i)
        (truncateOperator period q u) (derivativeOperator period q i v)) := by
    rw [truncate_reflection period u, derivative_reflection period i v,
      product_neg_right period hq (L i) (hL i)]
    exact congrArg Neg.neg (product_reflection period hq (L i) (hL i)
      (truncateOperator period q u) (derivativeOperator period q i v)).symm
  have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 4))) rfl (fun i _ => hi i)
  simpa only [transportBilinear_apply, map_sum, Finset.sum_neg_distrib] using hh

/-- Actual even coefficient multiplication commutes with Sobolev reflection. -/
theorem coefficient_reflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x) (u : SobolevSpace period q) :
    sobolevReflection period q (coefficientSobolevOperator period K u) =
      coefficientSobolevOperator period K (sobolevReflection period q u) := by
  apply value_injective period
  rw [value_sobolevReflection, coefficientSobolevOperator_value, coefficientSobolevOperator_value,
    value_sobolevReflection, coefficientOperator_reflection period A hA]

/-- Actual odd coefficient multiplication anticommutes with the L² reflection. -/
theorem odd_coefficient_L2_reflection (A : SmoothCoefficient period)
    (hA : ∀ x, A.coefficient (-x) = -A.coefficient x) (f : LiftL2 period) :
    reflection period (A.operator f) = -A.operator (reflection period f) := by
  apply Lp.ext
  filter_upwards [reflection_ae period (A.operator f),
    (measurePreserving_reflection period).quasiMeasurePreserving.ae (A.operator_ae f),
    Lp.coeFn_neg (A.operator (reflection period f)), A.operator_ae (reflection period f),
    reflection_ae period f] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3]
  change A.coefficient (-x) (f (-x)) = -(A.operator (reflection period f) x)
  rw [h4, h5, hA, neg_apply]

/-- Actual odd coefficient multiplication anticommutes with Sobolev reflection. -/
theorem odd_coefficient_reflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = -A.coefficient x) (u : SobolevSpace period q) :
    sobolevReflection period q (coefficientSobolevOperator period K u) =
      -coefficientSobolevOperator period K (sobolevReflection period q u) := by
  apply value_injective period
  change value period (sobolevReflection period q (coefficientSobolevOperator period K u)) =
    -value period (coefficientSobolevOperator period K (sobolevReflection period q u))
  rw [value_sobolevReflection, coefficientSobolevOperator_value, coefficientSobolevOperator_value,
    value_sobolevReflection, odd_coefficient_L2_reflection period A hA]

/-- The concrete coercive pressure acts covariantly at every Sobolev order. -/
theorem pressureSobolev_reflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v,v⟫_ℝ) (u : SobolevSpace period q) :
    sobolevReflection period q (pressureSobolevOperator period K κ m c hc hpos u) =
      pressureSobolevOperator period K κ m c hc hpos (sobolevReflection period q u) := by
  apply value_injective period
  rw [value_sobolevReflection, pressureSobolevOperator_value, pressureSobolevOperator_value,
    value_sobolevReflection, pressure_reflection period A hA]

/-- The actual pressure-corrected forcing commutes with reflection for an even metric. -/
theorem projectedSource_reflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v,v⟫_ℝ) (u : SobolevSpace period q) :
    sobolevReflection period q (projectedSourceOperator period K κ m c hc hpos u) =
      projectedSourceOperator period K κ m c hc hpos (sobolevReflection period q u) := by
  change sobolevReflection period q (u - coefficientSobolevOperator period K
    (pressureSobolevOperator period K κ m c hc hpos u)) =
    sobolevReflection period q u - coefficientSobolevOperator period K
      (pressureSobolevOperator period K κ m c hc hpos (sobolevReflection period q u))
  rw [map_sub, coefficient_reflection period K hA, pressureSobolev_reflection period K hA]

/-- The coordinate product reflects without a derivative sign. -/
theorem coordinateProduct_reflection {q : ℕ} (hq : 6 ≤ q) (i : Fin 3)
    (u v : SobolevSpace period (q+1)) :
    coordinateProduct period hq i (sobolevReflection period (q+1) u) (sobolevReflection period
      (q+1) v) =
      sobolevReflection period q (coordinateProduct period hq i u v) := by
  change productHq period hq (EulerVectorCylinder.coordinate 3 i)
    (EulerVectorCylinder.coordinate_norm_le 3 i)
    (truncateOperator period q (sobolevReflection period (q+1) u))
    (truncateOperator period q (sobolevReflection period (q+1) v)) =
    sobolevReflection period q (productHq period hq (EulerVectorCylinder.coordinate 3 i)
      (EulerVectorCylinder.coordinate_norm_le 3 i) (truncateOperator period q u) (truncateOperator
        period q v))
  exact (congrArg₂ (productHq period hq (EulerVectorCylinder.coordinate 3 i)
    (EulerVectorCylinder.coordinate_norm_le 3 i))
    (truncate_reflection period u) (truncate_reflection period v)).trans
    (product_reflection period hq (EulerVectorCylinder.coordinate 3 i)
      (EulerVectorCylinder.coordinate_norm_le 3 i) (truncateOperator period q u) (truncateOperator
        period q v)).symm

/-- The actual algebraic Euler term reverses reflection because its
coefficient fields, `κ F⁻¹ ∂ᵢF`, are odd. -/
theorem algebraic_reflection {q : ℕ} (hq : 6 ≤ q)
    (A : Fin 3 → SmoothCoefficient period) (K : ∀ i, CoefficientJet period standardDirection q (A
      i))
    (hA : ∀ i x, (A i).coefficient (-x) = -(A i).coefficient x)
    (u v : SobolevSpace period (q+1)) :
    algebraicBilinear period hq (fun i => coefficientSobolevOperator period (K i))
      (sobolevReflection period (q+1) u) (sobolevReflection period (q+1) v) =
      -sobolevReflection period q (algebraicBilinear period hq (fun i => coefficientSobolevOperator
        period (K i)) u v) := by
  have hi (i : Fin 3) : coefficientSobolevOperator period (K i)
      (coordinateProduct period hq i (sobolevReflection period (q+1) u) (sobolevReflection period
        (q+1) v)) =
      -sobolevReflection period q (coefficientSobolevOperator period (K i) (coordinateProduct
        period hq i u v)) := by
    have hp := congrArg (coefficientSobolevOperator period (K i)) (coordinateProduct_reflection
      period hq i u v)
    have hc := congrArg Neg.neg (odd_coefficient_reflection period (K i) (hA i) (coordinateProduct
      period hq i u v))
    simp only [neg_neg] at hc
    exact hp.trans hc.symm
  have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl (fun i _ => hi i)
  simpa only [algebraicBilinear_apply, map_sum, Finset.sum_neg_distrib] using hh

/-- The literal Euler bilinear term reverses pullback reflection. -/
theorem eulerBilinear_reflection {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (A : Fin 3 → SmoothCoefficient period) (K : ∀ i, CoefficientJet period standardDirection q (A
      i))
    (hA : ∀ i x, (A i).coefficient (-x) = -(A i).coefficient x)
    (u v : SobolevSpace period (q+1)) :
    eulerBilinear period hq L hL (fun i => coefficientSobolevOperator period (K i))
      (sobolevReflection period (q+1) u) (sobolevReflection period (q+1) v) =
      -sobolevReflection period q (eulerBilinear period hq L hL (fun i =>
        coefficientSobolevOperator period (K i)) u v) := by
  change transportBilinear period hq L hL _ _ + algebraicBilinear period hq _ _ _ =
    -sobolevReflection period q (transportBilinear period hq L hL u v + algebraicBilinear period hq
      _ u v)
  have hh := congrArg₂ HAdd.hAdd (transport_reflection period hq L hL u v) (algebraic_reflection
    period hq A K hA u v)
  exact hh.trans ((neg_add _ _).symm.trans
    (congrArg Neg.neg (map_add (sobolevReflection period q)
      (transportBilinear period hq L hL u v)
      (algebraicBilinear period hq (fun i => coefficientSobolevOperator period (K i)) u v))).symm)

/-- Signed reflection is an exact symmetry of the actual bilinear Euler term. -/
theorem eulerBilinear_oddReflection {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (A : Fin 3 → SmoothCoefficient period) (K : ∀ i, CoefficientJet period standardDirection q (A
      i))
    (hA : ∀ i x, (A i).coefficient (-x) = -(A i).coefficient x)
    (u v : SobolevSpace period (q+1)) :
    oddReflection period q (eulerBilinear period hq L hL (fun i => coefficientSobolevOperator
      period (K i)) u v) =
      eulerBilinear period hq L hL (fun i => coefficientSobolevOperator period (K i))
        (oddReflection period (q+1) u) (oddReflection period (q+1) v) := by
  simp only [oddReflection_apply, map_neg, neg_apply, neg_neg]
  exact (eulerBilinear_reflection period hq L hL A K hA u v).symm

end EulerSobolevParityOperators
