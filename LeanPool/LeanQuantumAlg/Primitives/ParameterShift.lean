/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Components.Gates
public import LeanPool.LeanQuantumAlg.Core.Measurement
public import LeanPool.LeanQuantumAlg.Util.TrigPolynomial

/-!
# Parameter-shift rule

A *variational* (parameterized) quantum model has a cost `C(θ) = ⟨ψ| U(θ)† O U(θ) |ψ⟩`
that is optimized over the parameters `θ`. When `θ` enters through a single Pauli
rotation gate, `C` is a frequency-1 trigonometric polynomial in `θ`, and its exact
analytic gradient is obtained from two shifted evaluations — the **parameter-shift
rule** `C'(θ) = (C(θ + π/2) − C(θ − π/2)) / 2`.

This module records the parameter-shift rule abstractly (`ParamShiftModel`), and
instantiates it on a concrete single-qubit `R_Y(θ)` ansatz with observable `Z`,
whose cost is `cos θ`.

Sources: Schuld et al. (2019), *Evaluating analytic gradients on quantum hardware*;
Wierichs et al. (2022), *General parameter-shift rules for quantum gradients*;
Farhi, Goldstone, Gutmann (2014), *A Quantum Approximate Optimization Algorithm*.

## Main results

- `LeanPool.LeanQuantumAlg.ParamShiftModel` / `ParamShiftModel.parameter_shift` — the
  parameter-shift rule for any frequency-1 trigonometric cost.
- `LeanPool.LeanQuantumAlg.varCost` — the single-qubit `R_Y(θ)` variational cost.
- `LeanPool.LeanQuantumAlg.varCost_ket0_Z` — the `R_Y` / `Z` / `|0⟩` cost equals `cos θ`.
- `LeanPool.LeanQuantumAlg.varCost_ket0_Z_parameter_shift` — the parameter-shift rule for it.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- A single-parameter variational cost whose dependence on the parameter is a
frequency-1 trigonometric polynomial `a + b cos θ + c sin θ` — the structure that
makes the parameter-shift rule exact. A parameterized-circuit cost built from a
single Pauli rotation gate has this form. -/
structure ParamShiftModel where
  /-- The cost function. -/
  cost : ℝ → ℝ
  /-- Constant Fourier coefficient. -/
  a : ℝ
  /-- Cosine Fourier coefficient. -/
  b : ℝ
  /-- Sine Fourier coefficient. -/
  c : ℝ
  /-- The cost is a frequency-1 trigonometric polynomial. -/
  trig : ∀ θ, cost θ = a + b * Real.cos θ + c * Real.sin θ

/-- **Parameter-shift rule.** The exact derivative of a frequency-1 trigonometric
cost is the symmetric finite difference at shift `π/2`. -/
theorem ParamShiftModel.parameter_shift (M : ParamShiftModel) (θ : ℝ) :
    deriv M.cost θ = (M.cost (θ + Real.pi / 2) - M.cost (θ - Real.pi / 2)) / 2 := by
  have hcost : M.cost = fun t => M.a + M.b * Real.cos t + M.c * Real.sin t :=
    funext M.trig
  rw [hcost]
  exact trig_parameter_shift M.a M.b M.c θ

/-- The single-qubit `R_Y(θ)` variational cost with observable `O` on input `ψ`:
`C(θ) = ⟨ψ| R_Y(θ)† O R_Y(θ) |ψ⟩`. -/
def varCost (ψ : PureState 1) (O : HilbertOperator 1) (θ : ℝ) : ℝ :=
  expVal ((rotY θ).apply ψ) O

/-- `R_Y(θ) |0⟩ = cos(θ/2) |0⟩ + sin(θ/2) |1⟩`. -/
theorem rotY_apply_ket0 (θ : ℝ) :
    ((rotY θ).apply ket0 : StateVector 1)
      = (Real.cos (θ / 2) : ℂ) • ket0 + (Real.sin (θ / 2) : ℂ) • ket1 := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · change (rotY θ).apply ket0 0 = _
    rw [Gate.apply_apply]
    simp [rotY, rotYOp, ket0, ket1, ket_apply, PiLp.smul_apply, PiLp.add_apply]
  · change (rotY θ).apply ket0 1 = _
    rw [Gate.apply_apply]
    simp [rotY, rotYOp, ket0, ket1, ket_apply, PiLp.smul_apply, PiLp.add_apply]

/-- Inner product of two single-qubit states in the computational basis. -/
theorem inner_ket01_combo (a b c d : ℂ) :
    inner ℂ ((a • ket0 + b • ket1 : StateVector 1))
      ((c • ket0 + d • ket1 : StateVector 1))
      = starRingEnd ℂ a * c + starRingEnd ℂ b * d := by
  simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, ket0, ket1,
    PureState.ket, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The `R_Y(θ)` ansatz cost with observable `Z` on `|0⟩` equals `cos θ`. -/
theorem varCost_ket0_Z (θ : ℝ) : varCost ket0 Z θ = Real.cos θ := by
  have hZ : HilbertOperator.applyVec (Z : HilbertOperator 1)
      ((Real.cos (θ / 2) : ℂ) • ket0 + (Real.sin (θ / 2) : ℂ) • ket1)
      = (Real.cos (θ / 2) : ℂ) • ket0 + (-(Real.sin (θ / 2)) : ℂ) • ket1 := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    · change HilbertOperator.applyVec ZOp _ 0 = _
      simp [ZOp, ket0, ket1, PureState.ket, PiLp.smul_apply, PiLp.add_apply,
        smul_eq_mul, HilbertOperator.applyVec]
    · change HilbertOperator.applyVec ZOp _ 1 = _
      simp [ZOp, ket0, ket1, PureState.ket, PiLp.smul_apply, PiLp.add_apply,
        smul_eq_mul, HilbertOperator.applyVec]
  have htrig : Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2)
      = Real.cos θ := by
    have hsc : Real.sin (θ / 2) ^ 2 + Real.cos (θ / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (θ / 2)
    have h2 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
      conv_lhs => rw [show θ = 2 * (θ / 2) from by ring]
      rw [Real.cos_two_mul]
    rw [h2]; nlinarith [hsc]
  rw [varCost, expVal, rotY_apply_ket0, hZ]
  change (inner ℂ
      (((Real.cos (θ / 2) : ℂ) • ket0 + (Real.sin (θ / 2) : ℂ) • ket1)
        : StateVector 1)
      (((Real.cos (θ / 2) : ℂ) • ket0 + (-(Real.sin (θ / 2)) : ℂ) • ket1)
        : StateVector 1)).re = Real.cos θ
  rw [inner_ket01_combo]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_add, Complex.ofReal_re]
  rw [← htrig]; ring

/-- A concrete variational model: the `R_Y` / `Z` / `|0⟩` cost `cos θ`. -/
def rotYZModel : ParamShiftModel where
  cost := varCost ket0 Z
  a := 0
  b := 1
  c := 0
  trig θ := by rw [varCost_ket0_Z]; ring

/-- **Parameter-shift rule for the `R_Y` / `Z` / `|0⟩` ansatz.** -/
theorem varCost_ket0_Z_parameter_shift (θ : ℝ) :
    deriv (varCost ket0 Z) θ
      = (varCost ket0 Z (θ + Real.pi / 2) - varCost ket0 Z (θ - Real.pi / 2)) / 2 :=
  rotYZModel.parameter_shift θ

namespace ParameterShiftRule

/-- Main parameter-shift theorem for a frequency-1 variational cost. -/
theorem main (M : ParamShiftModel) (θ : ℝ) :
    deriv M.cost θ = (M.cost (θ + Real.pi / 2) - M.cost (θ - Real.pi / 2)) / 2 :=
  M.parameter_shift θ

/-- Public supporting theorem: the quantum-free trigonometric identity. -/
theorem main_trig_identity (a b c θ : ℝ) :
    deriv (fun t => a + b * Real.cos t + c * Real.sin t) θ
      = ((a + b * Real.cos (θ + Real.pi / 2) + c * Real.sin (θ + Real.pi / 2))
          - (a + b * Real.cos (θ - Real.pi / 2) + c * Real.sin (θ - Real.pi / 2))) / 2 :=
  trig_parameter_shift a b c θ

/-- Public supporting theorem: the concrete `R_Y` / `Z` / `|0⟩` cost. -/
theorem main_ry_z_example (θ : ℝ) : varCost ket0 Z θ = Real.cos θ :=
  varCost_ket0_Z θ

/-- Public supporting theorem: parameter shift for the concrete `R_Y` / `Z` / `|0⟩` cost. -/
theorem main_ry_z_parameter_shift (θ : ℝ) :
    deriv (varCost ket0 Z) θ
      = (varCost ket0 Z (θ + Real.pi / 2) - varCost ket0 Z (θ - Real.pi / 2)) / 2 :=
  varCost_ket0_Z_parameter_shift θ

end ParameterShiftRule

end

end QuantumAlg
