/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Certificate

/-!
# The batch 12 to 13

`Sendov.R_le_batch` bounds every `R n α` for `12 ≤ n ≤ 13` by the elementary part and
moment at `n₀ = 12` together with the prefactor at `n₁ = 13`, so one moment and one
certificate serve all 2 degrees.  The certificate has degree 10, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.

The moment numerator `Nmomc` is checked against the packed recurrence
(`Sendov.pev_wsum_eq_of_packed`), and the numerator `Sendov.batchP 12 13 4 Lc Nmomc` of
`1 - bound` is certified positive on `[0, 6]` by its Bernstein coefficients `Bc`
(`Sendov.pev_pos_of_bern`).  Every closed computation is evaluated by the kernel.
-/

public section

namespace Sendov

namespace Batch12To13

/-- The common denominator `L` of the moment weights: `j + 4 ∣ L` for every `j < 2k + 1`. -/
def Lc : ℤ := 27720

/-- The base `β` at which polynomials in `α` are packed: it exceeds twice the absolute value
of every coefficient of `Nmomc` and of the weighted row sum `wsum Lc 0 (qrow …)`. -/
def betac : ℤ := 538941732215041

/-- The base `τ` at which the recurrence rows, evaluated at `betac`, are packed into a single
integer exponentiation: it exceeds twice the absolute value of every row entry. -/
def tauc : ℤ :=
  big [
    435248501929604780211870392204795696401964180489810388769719091757577450834981070202288673,
    180756234778163021074014036716599319294695000296491713270664825204672831809746575409998007,
    6292050050870377734039]

/-- The moment numerator at `n₀ = 12`, `k = 4`. -/
def Nmomc : List ℤ := [
  265646304,
  754389504,
  1044603648,
  1046977536,
  1399732528,
  127959680,
  6424320,
  167936,
  1792]

/-- Bernstein coefficients of `6 ^ 10 * batchP 12 13 4 Lc Nmomc` on `[0, 6]`. -/
def Bc : List ℤ := [
  18738341756209152,
  369304821659271168,
  3125326175066456064,
  14491775837857038336,
  31455696526840295424,
  37998275937620410368,
  48183437605113372672,
  77289206430873305088,
  78482217686052685824,
  36662921411251322880,
  5521524308923392000]

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 12 α = (66 + 5 * α - 2 * α ^ 2) / (22 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 6) : 0 ≤ c 12 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 12) (gg1 12) (gg2 12) 4)) α :=
  pev_wsum_eq_of_packed (gg0 12) (gg1 12) (gg2 12) 4 13 Lc betac tauc Nmomc
    (by decide +kernel) (by decide +kernel)
    (rowZ_bound (gg0 12) (gg1 12) (gg2 12) 4 3 betac tauc (by decide +kernel)
      (by simp) (by simp) (by simp) (by decide +kernel))
    (by decide +kernel)
    (wsum_bound (gg0 12) (gg1 12) (gg2 12) 4 Lc betac (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 12) (gg1 12) (gg2 12) 3 (by simp) (by simp) (by simp) 4))
    (by decide +kernel) α

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 12 α t ^ 4)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 12 * (3 + α)) ^ 4) :=
  integral_moment_packed 12 4 (by norm_num) α hα Lc (by decide +kernel) Nmomc
    (by decide +kernel) (pev_Nmomc α)

/-- The certificate: `batchP 12 13 4 Lc Nmomc` is positive on `[0, 6]`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hU : (1 : ℝ) * α ≤ 6) :
    0 < pev (batchP 12 13 4 Lc Nmomc) α :=
  pev_pos_of_bern _ Bc 6 1 10 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hα (by exact_mod_cast hU)

/-- **The batch `12 ≤ n ≤ 13`.** -/
theorem finite_range {n : ℕ} (h0 : 12 ≤ n) (h1 : n ≤ 13) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h2α : 2 * α ≤ (13 : ℝ) - 1 := by
    exact_mod_cast two_alpha_le_of_le (by omega) h1 hfeas
  refine lt_of_le_of_lt (R_le_batch (n₀ := 12) (n := n) (n₁ := 13) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα (by linarith)) hfeas) ?_
  exact batch_lt_one (by norm_num) (by norm_num) (by norm_num) Lc (by decide +kernel) Nmomc hα
    (integral_lo α hα) (P_pos hα (by linarith))

end Batch12To13

end Sendov
