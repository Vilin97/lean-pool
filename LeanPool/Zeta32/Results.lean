/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Final

/-! Zeta32 — Results. -/

public section

namespace Zeta32Acceptance

public theorem one_zeta_two_zeta_three_linearIndependent :
    LinearIndependent ℚ ![(1 : ℂ), riemannZeta 2, riemannZeta 3] :=
  Zeta32.one_zeta_two_zeta_three_linearIndependent

public theorem one_zeta_two_zeta_three_linearIndependent_series (a b c : ℚ)
    (h : (a : ℝ) + b * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)
      + c * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hli := Zeta32.one_zeta_two_zeta_three_linearIndependent
  rw [Zeta32.LinearIndependence.riemannZeta_two_eq_ofReal_tsum,
    Zeta32.LinearIndependence.riemannZeta_three_eq_ofReal_tsum,
    Fintype.linearIndependent_iff] at hli
  have hg := hli ![a, b, c] (by
    simp only [Fin.sum_univ_three, Rat.smul_def, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_one]
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h)
  exact ⟨by simpa using hg 0, by simpa using hg 1, by simpa using hg 2⟩

end Zeta32Acceptance

end
