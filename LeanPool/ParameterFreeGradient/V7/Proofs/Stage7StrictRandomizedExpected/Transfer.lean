/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage7StrictRandomizedExpected.Expected

/-!
The one-dimensional strict-oracle lower bounds transfer to every interior `ℓp` exponent.
-/

@[expose] public section

namespace V7.Stage7StrictRandomizedExpected

/-- Direct derivation from the literal finite-sum definition: on `Fin 1`,
every positive-exponent `ell_p` norm is absolute value. -/
theorem lpNorm_fin_one {p : ℝ} (hp : 0 < p) (x : StrictPoint) :
    lpNorm p x = |x 0| := by
  simp only [lpNorm, O3.lpNorm, O3.lpPower, Fin.sum_univ_one]
  rw [← Real.rpow_mul (abs_nonneg (x 0))]
  rw [mul_one_div_cancel hp.ne', Real.rpow_one]

end V7.Stage7StrictRandomizedExpected

namespace V7

open Stage7StrictRandomizedExpected

theorem oneDimensionalInteriorLpTransfer :
    OneDimensionalInteriorLpTransferStatement := by
  intro p hp
  exact ⟨fun x => lpNorm_fin_one (by linarith) x,
    fun x => lpNorm_fin_one (lt_trans zero_lt_one (O3.one_lt_conjugateExponent hp)) x⟩

end V7
