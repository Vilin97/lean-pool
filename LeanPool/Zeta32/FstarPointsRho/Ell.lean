/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.FstarPointsRho.Basic

/-! Uniform bound `ℓ(a) ≤ −159/100` on `[a₋, a₊]`.
`ℓ = 2log(a/2) + (1/3)J₀ + (4/3)J₁ − (1/3)J₅` with `J₀ = −a`, `J₁ = −log(2/(1+U₁)) − (U₁−1)`,
`J₅ = −5log(10/(5+U₅)) − (U₅−5)`, `U_c = √(c²+a²)`. Each term is bounded separately by
monotonicity in `a`
(`U₁ ∈ [2647/1250, 105881/50000]`, `U₅ ∈ [266853/50000, 533707/100000]`), the three logs by
`log_le`/`log_ge'`.
Upper bound obtained: `−1.60135`. Data: `tools/b2_numerics.py`. -/

public section

open Real
namespace Zeta32.Fstar.B2
noncomputable section

theorem log_aPlus_half : log ((186663 / 100000 : ℝ) / 2) ≤ -6901 / 100000 :=
  le_trans (log_le _ 0 (by norm_num) (by norm_num)) (by norm_num [lser])

theorem log_U1_ge : -44393 / 100000 ≤ log ((2 : ℝ) / (1 + 105881 / 50000)) :=
  le_trans (by norm_num [lser]) (log_ge' _ 1 (by norm_num))

theorem log_U5_le : log ((10 : ℝ) / (5 + 266853 / 50000)) ≤ -663 / 20000 :=
  le_trans (log_le _ 0 (by norm_num) (by norm_num)) (by norm_num [lser])

theorem ell_upper {a : ℝ} (h1 : aMinus ≤ a) (h2 : a ≤ aPlus) : ellA a ≤ -159 / 100 := by
  have h1' : (93331 / 50000 : ℝ) ≤ a := by simpa [aMinus] using h1
  have h2' : a ≤ (186663 / 100000 : ℝ) := by simpa [aPlus] using h2
  have ha : 0 < a := by linarith
  have hsq1 : (93331 / 50000 : ℝ) ^ 2 ≤ a ^ 2 := by nlinarith
  have hsq2 : a ^ 2 ≤ (186663 / 100000 : ℝ) ^ 2 := by nlinarith
  have e0 : Jfun a 0 = -a := by
    unfold Jfun; simp [sqrt_sq ha.le]
  have e1 : Jfun a 1 = -log (2 / (1 + √(1 + a ^ 2))) - (√(1 + a ^ 2) - 1) := by
    unfold Jfun; norm_num
  have e5 : Jfun a 5 = -5 * log (10 / (5 + √(25 + a ^ 2))) - (√(25 + a ^ 2) - 5) := by
    unfold Jfun; norm_num
  have hU1u : √(1 + a ^ 2) ≤ 105881 / 50000 := sqrt_le_of_le_sq (by norm_num) (by nlinarith)
  have hU1l : (2647 / 1250 : ℝ) ≤ √(1 + a ^ 2) := le_sqrt_of_sq_le (by norm_num) (by nlinarith)
  have hU5u : √(25 + a ^ 2) ≤ 533707 / 100000 := sqrt_le_of_le_sq (by norm_num) (by nlinarith)
  have hU5l : (266853 / 50000 : ℝ) ≤ √(25 + a ^ 2) := le_sqrt_of_sq_le (by norm_num) (by nlinarith)
  have hl0 : log (a / 2) ≤ log ((186663 / 100000 : ℝ) / 2) := log_le_log (by positivity) (by
    linarith)
  have hl1 : log ((2 : ℝ) / (1 + 105881 / 50000)) ≤ log (2 / (1 + √(1 + a ^ 2))) :=
    log_le_log (by norm_num) (by gcongr)
  have hl5 : log (10 / (5 + √(25 + a ^ 2))) ≤ log ((10 : ℝ) / (5 + 266853 / 50000)) :=
    log_le_log (by positivity) (by gcongr)
  have := log_aPlus_half
  have := log_U1_ge
  have := log_U5_le
  unfold ellA
  rw [e0, e1, e5]
  linarith

end
end Zeta32.Fstar.B2
