/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Kernel.PositiveC0Resolvent

/-!
# Exponential comparison under resolvent generation

A pointwise exponential supersolution estimate for every sufficiently large normalized positive
resolvent passes through the Poisson representation of the Yosida approximants and then through
their strong limit to the generated semigroup.  The represented kernel semigroup inherits the
same comparison for `C₀` observables.

Public declarations:

* `PositiveC0ContractiveResolvent.generatedSemigroup_apply_le_exp_mul`;
* `PositiveC0ContractiveResolvent.integral_kernelSemigroup_le_exp_mul`.

No comparison for indicators of arbitrary measurable sets is asserted.
-/

open Filter Set Topology
open scoped NNReal ZeroAtInfty
open NormedSpace

noncomputable section

namespace MarkovProcess

open _root_.MarkovProcess.Semigroup

namespace PositiveC0ContractiveResolvent

variable {X : Type*} [TopologicalSpace X]

/-- Iterating a positive operator preserves a scalar pointwise supersolution estimate. -/
private theorem pow_apply_le_pow_mul
    (T : C₀(X, ℝ) →L[ℝ] C₀(X, ℝ)) (hT : PositiveC0OperatorMeasure.IsPositive T)
    (v : C₀(X, ℝ)) (a : ℝ) (ha : 0 ≤ a)
    (hTv : ∀ x, T v x ≤ a * v x) :
    ∀ n x, (T ^ n) v x ≤ a ^ n * v x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp only [pow_zero, one_apply_eq_self, one_mul]
      exact le_rfl
  | succ n ih =>
      intro x
      rw [pow_succ', mul_apply_eq_comp]
      calc
        T ((T ^ n) v) x ≤ T (a ^ n • v) x :=
          PositiveC0OperatorMeasure.apply_le_apply_of_isPositive T hT (fun y ↦ by
            simpa only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul] using! ih y) x
        _ = a ^ n * T v x := by rw [map_smul]; rfl
        _ ≤ a ^ n * (a * v x) :=
          mul_le_mul_of_nonneg_left (hTv x) (pow_nonneg ha n)
        _ = a ^ (n + 1) * v x := by rw [pow_succ]; ring

/-- The scalar sum obtained by weighting geometric powers with the Poisson coefficients. -/
private theorem tsum_poissonWeight_mul_pow (c a : ℝ) :
    ∑' n : ℕ, poissonWeight c n * a ^ n = Real.exp (c * (a - 1)) := by
  have hsum : ∑' n : ℕ, (c * a) ^ n / n.factorial = Real.exp (c * a) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
    apply tsum_congr
    intro n
    simp only [div_eq_mul_inv, smul_eq_mul]
    ring
  unfold poissonWeight
  rw [show (fun n : ℕ ↦ Real.exp (-c) * (c ^ n / n.factorial) * a ^ n) =
      fun n ↦ Real.exp (-c) * ((c * a) ^ n / n.factorial) by
    funext n
    rw [mul_pow]
    ring]
  rw [tsum_mul_left, hsum, ← Real.exp_add]
  congr 1
  ring

/-- The scalar exponent in the Yosida comparison converges to its semigroup counterpart. -/
private theorem tendsto_mul_naturalShift_div_sub (b theta : ℝ) :
    Tendsto (fun n : ℕ ↦
      b * (naturalShift n : ℝ) / ((naturalShift n : ℝ) - theta))
      atTop (nhds b) := by
  have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + (1 - theta)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 - theta) tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ ↦ theta / ((n : ℝ) + (1 - theta)))
      atTop (nhds 0) := hden.const_div_atTop theta
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hmain : Tendsto (fun n : ℕ ↦
      b * (1 + theta / ((n : ℝ) + (1 - theta)))) atTop (nhds b) := by
    simpa only [add_zero, mul_one] using (hone.add hsmall).const_mul b
  apply hmain.congr'
  filter_upwards [hden.eventually (eventually_gt_atTop 0)] with n hn
  rw [naturalShift_coe]
  have hden' : 0 < (n : ℝ) + 1 - theta := by
    linarith only [hn]
  field_simp [hden'.ne']
  ring

/-- A Yosida approximant satisfies the exponential comparison furnished by one normalized
resolvent estimate. -/
private theorem yosidaOperator_apply_le_exp_mul
    (R : PositiveC0ContractiveResolvent X) (theta : ℝ) (v : C₀(X, ℝ))
    (mu : PositiveShift) (hmu : theta < (mu : ℝ))
    (hR : ∀ x, (mu : ℝ) * R.toContractiveResolvent.operator mu v x ≤
      (mu : ℝ) / ((mu : ℝ) - theta) * v x)
    (t : NNReal) (x : X) :
    R.toContractiveResolvent.yosidaOperator mu t v x ≤
      Real.exp (theta * (t : ℝ) * (mu : ℝ) / ((mu : ℝ) - theta)) * v x := by
  let Q := R.toContractiveResolvent.scaledOperator mu
  let c : ℝ := (t : ℝ) * (mu : ℝ)
  let a : ℝ := (mu : ℝ) / ((mu : ℝ) - theta)
  have hden : 0 < (mu : ℝ) - theta := sub_pos.mpr hmu
  have ha : 0 ≤ a := div_nonneg mu.property.le hden.le
  have hQpos : PositiveC0OperatorMeasure.IsPositive Q := by
    intro f hf y
    exact mul_nonneg mu.property.le (R.isPositive mu f hf y)
  have hQv : ∀ y, Q v y ≤ a * v y := by
    intro y
    exact hR y
  have hpowers : ∀ n y, (Q ^ n) v y ≤ a ^ n * v y :=
    pow_apply_le_pow_mul Q hQpos v a ha hQv
  have hleftC0 : Summable fun n : ℕ ↦ poissonWeight c n • (Q ^ n) v :=
    summable_poissonWeight_smul_pow_apply Q c v
  have hleft : Summable fun n : ℕ ↦ poissonWeight c n * (Q ^ n) v x := by
    simpa only [Function.comp_apply, smul_apply, smul_eq_mul] using!
      hleftC0.map (c0EvalCLM x) (c0EvalCLM x).continuous
  have hright : Summable fun n : ℕ ↦ poissonWeight c n * (a ^ n * v x) := by
    have hscalar : Summable fun n : ℕ ↦ poissonWeight c n * a ^ n := by
      unfold poissonWeight
      rw [show (fun n : ℕ ↦ Real.exp (-c) * (c ^ n / n.factorial) * a ^ n) =
          fun n ↦ Real.exp (-c) * ((c * a) ^ n / n.factorial) by
        funext n
        rw [mul_pow]
        ring]
      exact (Real.summable_pow_div_factorial (c * a)).mul_left _
    simpa only [mul_assoc] using hscalar.mul_right (v x)
  rw [ContractiveResolvent.yosidaOperator, ContractiveResolvent.yosidaGenerator, smul_smul]
  change exp (c • (Q - ContinuousLinearMap.id ℝ C₀(X, ℝ))) v x ≤ _
  rw [exp_smul_sub_id_apply_eq_tsum]
  change (∑' n : ℕ, poissonWeight c n • (Q ^ n) v) x ≤ _
  rw [show (∑' n : ℕ, poissonWeight c n • (Q ^ n) v) x =
      ∑' n : ℕ, poissonWeight c n * (Q ^ n) v x by
    change c0EvalCLM x (∑' n : ℕ, poissonWeight c n • (Q ^ n) v) = _
    rw [(c0EvalCLM x).map_tsum hleftC0]
    apply tsum_congr
    intro n
    rfl]
  calc
    (∑' n : ℕ, poissonWeight c n * (Q ^ n) v x) ≤
        ∑' n : ℕ, poissonWeight c n * (a ^ n * v x) :=
      hleft.tsum_le_tsum (fun n ↦
        mul_le_mul_of_nonneg_left (hpowers n x) (poissonWeight_nonneg
          (mul_nonneg t.property mu.property.le) n)) hright
    _ = (∑' n : ℕ, poissonWeight c n * a ^ n) * v x := by
      rw [show (fun n : ℕ ↦ poissonWeight c n * (a ^ n * v x)) =
          fun n ↦ (poissonWeight c n * a ^ n) * v x by
        funext n
        ring]
      rw [tsum_mul_right]
    _ = Real.exp (c * (a - 1)) * v x := by rw [tsum_poissonWeight_mul_pow]
    _ = Real.exp (theta * (t : ℝ) * (mu : ℝ) / ((mu : ℝ) - theta)) * v x := by
      congr 2
      dsimp only [c, a]
      field_simp
      ring

/-- **Exponential comparison is stable under resolvent generation.**  A pointwise
supersolution estimate for every normalized resolvent above `theta` passes to the canonical
semigroup generated by the resolvent. -/
theorem generatedSemigroup_apply_le_exp_mul
    (R : PositiveC0ContractiveResolvent X) (theta : ℝ) (v : C₀(X, ℝ))
    (hR : ∀ mu : PositiveShift, theta < (mu : ℝ) → ∀ x,
      (mu : ℝ) * R.toContractiveResolvent.operator mu v x ≤
        (mu : ℝ) / ((mu : ℝ) - theta) * v x)
    (t : NNReal) (x : X) :
    R.toContractiveResolvent.generatedSemigroup t v x ≤
      Real.exp (theta * (t : ℝ)) * v x := by
  have hleft : Tendsto (fun n ↦
      R.toContractiveResolvent.yosidaSemigroup (naturalShift n) t v x)
      atTop (nhds (R.toContractiveResolvent.generatedSemigroup t v x)) := by
    change Tendsto (fun n ↦ c0EvalCLM x
      (R.toContractiveResolvent.yosidaSemigroup (naturalShift n) t v)) _ _
    exact (c0EvalCLM x).continuous.continuousAt.tendsto.comp
      (R.toContractiveResolvent.tendsto_yosidaSemigroup_naturalShift_apply_generatedSemigroup
        t v)
  have hscalar := tendsto_mul_naturalShift_div_sub (theta * (t : ℝ)) theta
  have hright : Tendsto (fun n ↦
      Real.exp (theta * (t : ℝ) * (naturalShift n : ℝ) /
        ((naturalShift n : ℝ) - theta)) * v x)
      atTop (nhds (Real.exp (theta * (t : ℝ)) * v x)) :=
    (Real.continuous_exp.continuousAt.tendsto.comp hscalar).mul_const (v x)
  apply le_of_tendsto_of_tendsto hleft hright
  have hmuTop : Tendsto (fun n : ℕ ↦ (naturalShift n : ℝ)) atTop atTop :=
    tendsto_positiveShift_coe_atTop.comp tendsto_naturalShift_atTop
  filter_upwards [hmuTop.eventually (eventually_gt_atTop theta)] with n hn
  exact yosidaOperator_apply_le_exp_mul R theta v (naturalShift n) hn
    (hR (naturalShift n) hn) t x

section Kernel

variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- The represented kernel semigroup inherits the generated semigroup's exponential comparison
for every `C₀` observable below the supersolution. -/
theorem integral_kernelSemigroup_le_exp_mul
    (R : PositiveC0ContractiveResolvent X) (theta : ℝ) (v : C₀(X, ℝ))
    (hR : ∀ mu : PositiveShift, theta < (mu : ℝ) → ∀ x,
      (mu : ℝ) * R.toContractiveResolvent.operator mu v x ≤
        (mu : ℝ) / ((mu : ℝ) - theta) * v x)
    (f : C₀(X, ℝ)) (hfv : ∀ x, f x ≤ v x) (t : NNReal) (x : X) :
    ∫ y, f y ∂R.kernelSemigroup t x ≤ Real.exp (theta * (t : ℝ)) * v x := by
  rw [R.integral_kernelSemigroup]
  calc
    R.toContractiveResolvent.generatedSemigroup t f x ≤
        R.toContractiveResolvent.generatedSemigroup t v x :=
      PositiveC0OperatorMeasure.apply_le_apply_of_isPositive _
        (R.isPositive_generatedSemigroup t) hfv x
    _ ≤ Real.exp (theta * (t : ℝ)) * v x :=
      R.generatedSemigroup_apply_le_exp_mul theta v hR t x

end Kernel

end PositiveC0ContractiveResolvent

end MarkovProcess
