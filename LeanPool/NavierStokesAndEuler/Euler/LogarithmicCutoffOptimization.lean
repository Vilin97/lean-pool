/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Optimization of the actual heat-scale estimate used in the
whole-space logarithmic gradient bound. -/

noncomputable section

namespace EulerLogarithmicCutoff

open Real

theorem optimize (X c L W H : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < 1 →
      X ≤ c*(L+W*(-log ε)+ε^(1/4 : ℝ)*H)) :
    X ≤ 4*c*(1+L+W*log (exp 1+H)) := by
  let A := exp 1+H
  have hE : 1 < exp (1 : ℝ) := by
    simpa only [exp_zero] using exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hA1 : 1 < A := by dsimp [A]; linarith
  have hA0 : 0 < A := zero_lt_one.trans hA1
  have hl : 0 < log A := log_pos hA1
  let ε := exp (-4*log A)
  have he0 : 0 < ε := exp_pos _
  have he1 : ε < 1 := by
    have hneg : -4*log A < 0 := by linarith
    simpa only [ε,exp_zero] using exp_lt_exp.mpr hneg
  have heLog : -log ε=4*log A := by simp only [ε,log_exp]; ring
  have hePow : ε^(1/4 : ℝ)=A⁻¹ := by
    dsimp [ε]
    rw [rpow_def_of_pos (exp_pos _),log_exp,
      show (-4*log A)*(1/4 : ℝ) = -log A by ring,exp_neg,exp_log hA0]
  have hHA : H ≤ A := le_add_of_nonneg_left (exp_pos 1).le
  have hsmall : A⁻¹*H ≤ 1 := by
    rw [mul_comm,← div_eq_mul_inv]
    exact (div_le_one hA0).mpr hHA
  have h := hbound ε he0 he1
  rw [heLog,hePow] at h
  have hmid : X ≤ c*(L+4*(W*log A)+1) := by
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hc
    nlinarith only [hsmall]
  have hdiff : 0 ≤ c*(3+3*L) := mul_nonneg hc (by linarith)
  change X ≤ 4*c*(1+L+W*log A)
  nlinarith only [hmid,hdiff]

end EulerLogarithmicCutoff
