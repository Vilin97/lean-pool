/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Real.Basic

/-!
# Parameters for the six-point transfer

The approximate-root ratio and the sibling-density parameter are chosen strictly between the
finite endpoint and the target density.
-/

@[expose] public section

namespace LeanPool.Besicovitch

/-- Between positive parameters `s < β`, choose an approximate-root ratio `q` and a sibling
parameter `γ` with `s < γq`. -/
theorem exists_transfer_parameters {s β : ℝ} (hs : 0 < s) (hsβ : s < β) :
    ∃ q γ : ℝ, 0 < q ∧ q < 1 ∧ s / β < q ∧ 0 < γ ∧ γ < β ∧ s < γ * q := by
  have hβ : 0 < β := hs.trans hsβ
  have hs_div_beta : 0 < s / β := div_pos hs hβ
  have hs_div_beta_lt_one : s / β < 1 := (div_lt_one hβ).2 hsβ
  obtain ⟨q, hsq, hq1⟩ := exists_between hs_div_beta_lt_one
  have hq : 0 < q := hs_div_beta.trans hsq
  have hs_lt_beta_q : s < β * q := by
    simpa [mul_comm] using (div_lt_iff₀ hβ).1 hsq
  have hs_div_q_lt_beta : s / q < β := (div_lt_iff₀ hq).2 <| by
    simpa [mul_comm] using hs_lt_beta_q
  obtain ⟨γ, hsγ, hγβ⟩ := exists_between hs_div_q_lt_beta
  refine ⟨q, γ, hq, hq1, hsq, ?_, hγβ, ?_⟩
  · exact (div_pos hs hq).trans hsγ
  · exact (div_lt_iff₀ hq).1 hsγ

end LeanPool.Besicovitch
