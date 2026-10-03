/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Certificate

/-!
# The batch 10 to 11

`Sendov.R_le_batch` bounds every `R n α` for `10 ≤ n ≤ 11` by the elementary part and
moment at `n₀ = 10` together with the prefactor at `n₁ = 11`, so one moment and one
certificate serve all 2 degrees.  The certificate has degree 8, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.

The moment numerator `Nmomc` is checked against the packed recurrence
(`Sendov.pev_wsum_eq_of_packed`), and the numerator `Sendov.batchP 10 11 3 Lc Nmomc` of
`1 - bound` is certified positive on `[0, 5]` by its Bernstein coefficients `Bc`
(`Sendov.pev_pos_of_bern`).  Every closed computation is evaluated by the kernel.
-/

public section

namespace Sendov

namespace Batch10To11

/-- The common denominator `L` of the moment weights: `j + 4 ∣ L` for every `j < 2k + 1`. -/
def Lc : ℤ := 2520

/-- The base `β` at which polynomials in `α` are packed: it exceeds twice the absolute value
of every coefficient of `Nmomc` and of the weighted row sum `wsum Lc 0 (qrow …)`. -/
def betac : ℤ := 82590802561

/-- The base `τ` at which the recurrence rows, evaluated at `betac`, are packed into a single
integer exponentiation: it exceeds twice the absolute value of every row entry. -/
def tauc : ℤ :=
  big [
    81496854475499965300896802417388157646295122586173254149900368313668004057389423899346929,
    484002949944962611058313401]

/-- The moment numerator at `n₀ = 10`, `k = 3`. -/
def Nmomc : List ℤ := [
  472392,
  1312200,
  1971216,
  3407184,
  294192,
  12096,
  192]

/-- Bernstein coefficients of `5 ^ 8 * batchP 10 11 3 Lc Nmomc` on `[0, 5]`. -/
def Bc : List ℤ := [
  7546462200000,
  106071372072000,
  590024221488000,
  1022404934016000,
  1176704065080000,
  2736859476600000,
  4242813219072000,
  2642855620608000,
  483084435456000]

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 10 α = (54 + 3 * α - 2 * α ^ 2) / (18 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 5) : 0 ≤ c 10 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 10) (gg1 10) (gg2 10) 3)) α :=
  pev_wsum_eq_of_packed (gg0 10) (gg1 10) (gg2 10) 3 10 Lc betac tauc Nmomc
    (by decide +kernel) (by decide +kernel)
    (rowZ_bound (gg0 10) (gg1 10) (gg2 10) 3 3 betac tauc (by decide +kernel)
      (by simp) (by simp) (by simp) (by decide +kernel))
    (by decide +kernel)
    (wsum_bound (gg0 10) (gg1 10) (gg2 10) 3 Lc betac (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 10) (gg1 10) (gg2 10) 3 (by simp) (by simp) (by simp) 3))
    (by decide +kernel) α

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 10 α t ^ 3)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 10 * (3 + α)) ^ 3) :=
  integral_moment_packed 10 3 (by norm_num) α hα Lc (by decide +kernel) Nmomc
    (by decide +kernel) (pev_Nmomc α)

/-- The certificate: `batchP 10 11 3 Lc Nmomc` is positive on `[0, 5]`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hU : (1 : ℝ) * α ≤ 5) :
    0 < pev (batchP 10 11 3 Lc Nmomc) α :=
  pev_pos_of_bern _ Bc 5 1 8 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hα (by exact_mod_cast hU)

/-- **The batch `10 ≤ n ≤ 11`.** -/
theorem finite_range {n : ℕ} (h0 : 10 ≤ n) (h1 : n ≤ 11) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h2α : 2 * α ≤ (11 : ℝ) - 1 := by
    exact_mod_cast two_alpha_le_of_le (by omega) h1 hfeas
  refine lt_of_le_of_lt (R_le_batch (n₀ := 10) (n := n) (n₁ := 11) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα (by linarith)) hfeas) ?_
  exact batch_lt_one (by norm_num) (by norm_num) (by norm_num) Lc (by decide +kernel) Nmomc hα
    (integral_lo α hα) (P_pos hα (by linarith))

end Batch10To11

end Sendov
