/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientMap
public import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus

@[expose] public section

/-!
# Quantitative parameter derivatives of time multipliers

The Bochner multiplier is a linear contraction of the uniform coefficient
path. These are bounds on genuine parameter derivatives of that operator,
including the H¹ moving-frame transport used in the variational inverse.
-/

noncomputable section

open scoped ContDiff


namespace EulerTimeLpCoefficientGevrey

open Set ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct EulerTimeLpCoefficientMap
  EulerOperatorGevreyCalculus EulerGevrey

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (T : ℝ) (hT : 0 ≤ T)

local instance coefficientPathGroup : NormedAddCommGroup C(Icc (0 : ℝ) T, E →L[ℝ] F) :=
  inferInstance

local instance coefficientPathSpace : NormedSpace ℝ C(Icc (0 : ℝ) T, E →L[ℝ] F) :=
  inferInstance

local instance timeOperatorGroup : NormedAddCommGroup (TimeLp T E →L[ℝ] TimeLp T F) :=
  inferInstance

local instance timeOperatorSpace : NormedSpace ℝ (TimeLp T E →L[ℝ] TimeLp T F) :=
  inferInstance

/-- The actual coefficient-to-multiplier map is a linear contraction. -/
theorem coefficientMap_norm : ‖coefficientMap (E := E) (F := F) T hT‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  change ‖timeMultiplier T hT A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using timeMultiplier_norm T hT A

/-- A convenient polynomial bound for the genuine terminal primitive. -/
theorem primitive_norm_le_time : ‖primitiveTimeLp (E := E) T hT‖ ≤ T := by
  apply (sq_le_sq₀ (norm_nonneg _) hT).1
  have h := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg (T^2/2))).2
    (primitiveTimeLp_norm_le (E := E) T hT)
  rw [Real.sq_sqrt (by positivity)] at h
  nlinarith [sq_nonneg T]

/-- Actual multiplier derivatives retain the coefficient factorial bounds. -/
theorem timeMultiplier_bound
    (A : P → C(Icc (0 : ℝ) T, E →L[ℝ] F)) (hA : ContDiff ℝ ∞ A)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => timeMultiplier T hT (A y)) x‖ ≤ C * majorant R d n := by
  exact contraction_bound (P := P)
    (E := C(Icc (0 : ℝ) T, E →L[ℝ] F)) (F := TimeLp T E →L[ℝ] TimeLp T F)
    (coefficientMap (E := E) (F := F) T hT) (coefficientMap_norm T hT)
    A hA R C hR hC d hb n x

/-- The genuine H¹ transport costs only the polynomial factor from terminal integration. -/
theorem productDerivative_bound
    (A B : P → C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D) (d : ℕ)
    (ha : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C * majorant R d n)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n B x‖ ≤ D * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => productDerivative T hT (A y) (B y)) x‖ ≤
      (T*D+C) * majorant R d n := by
  have hMB := contDiff_timeMultiplier T hT B hB
  have hright := clm_comp_const_right_bound
    (fun y => timeMultiplier T hT (B y)) (primitiveTimeLp (E := E) T hT)
    hMB R D hR hD d (timeMultiplier_bound T hT B hB R D hR hD d hb)
  have hsum := add_bound
    (fun y => (timeMultiplier T hT (B y)).comp (primitiveTimeLp T hT))
    (fun y => timeMultiplier T hT (A y))
    (hMB.clm_comp contDiff_const) (contDiff_timeMultiplier T hT A hA)
    R (‖primitiveTimeLp (E := E) T hT‖*D) C d hright
    (timeMultiplier_bound T hT A hA R C hR hC d ha) n x
  exact hsum.trans (mul_le_mul_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_right (primitive_norm_le_time (E := E) T hT) hD) (le_refl C))
    (majorant_nonneg R hR d n))

end EulerTimeLpCoefficientGevrey
