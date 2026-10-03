/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Certificate

/-!
# The batch 16 to 18

`Sendov.R_le_batch` bounds every `R n α` for `16 ≤ n ≤ 18` by the elementary part and
moment at `n₀ = 16` together with the prefactor at `n₁ = 18`, so one moment and one
certificate serve all 3 degrees.  The certificate has degree 14, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.

The moment numerator `Nmomc` is checked against the packed recurrence
(`Sendov.pev_wsum_eq_of_packed`), and the numerator `Sendov.batchP 16 18 6 Lc Nmomc` of
`1 - bound` is certified positive on `[0, 17/2]` by its Bernstein coefficients `Bc`
(`Sendov.pev_pos_of_bern`).  Every closed computation is evaluated by the kernel.
-/

public section

namespace Sendov

namespace Batch16To18

/-- The common denominator `L` of the moment weights: `j + 4 ∣ L` for every `j < 2k + 1`. -/
def Lc : ℤ := 720720

/-- The base `β` at which polynomials in `α` are packed: it exceeds twice the absolute value
of every coefficient of `Nmomc` and of the weighted row sum `wsum Lc 0 (qrow …)`. -/
def betac : ℤ := 9632409706279062743041

/-- The base `τ` at which the recurrence rows, evaluated at `betac`, are packed into a single
integer exponentiation: it exceeds twice the absolute value of every row entry. -/
def tauc : ℤ :=
  big [
    296506721823714704265478805643382244491222183969521021663658026171379394048234274188519553,
    443987808875231567434632560187716182055857676129052451323844518845444325992588835078239595,
    696513917860869931635574183554403391853205017812541311293282390174744915537500427122031507,
    522316333712207898845459456442843781680661940474008113586613026045908148093916427474204047,
    65604308031184443540574573963916799164579355278379645304399696021576697292]

/-- The moment numerator at `n₀ = 16`, `k = 6`. -/
def Nmomc : List ℤ := [
  52612659000000,
  170273696400000,
  255339685800000,
  239918448960000,
  165235950648000,
  99966121176960,
  96500543870016,
  8976458195712,
  533837640960,
  20291420160,
  478172160,
  6377472,
  36864]

/-- Bernstein coefficients of `17 ^ 14 * batchP 16 18 6 Lc Nmomc` on `[0, 17/2]`. -/
def Bc : List ℤ := [
  39156066523015200000000,
  2641641618483619776000000,
  80142049025184478176000000,
  1441455253501674159129600000,
  17017744404780580029384960000,
  136431349549730546005655654400,
  657065025194121333870974023680,
  1682820450813931739016273838080,
  1699536938347827625063230259200,
  118574708059996149423896985600,
  7124570482963915778896148889600,
  34212593538358663648763758510080,
  57300273733894618414333616455680,
  40732039985748952362762240000000,
  9253051318351755817943040000000]

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 16 α = (90 + 9 * α - 2 * α ^ 2) / (30 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 17 / 2) : 0 ≤ c 16 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 16) (gg1 16) (gg2 16) 6)) α :=
  pev_wsum_eq_of_packed (gg0 16) (gg1 16) (gg2 16) 6 19 Lc betac tauc Nmomc
    (by decide +kernel) (by decide +kernel)
    (rowZ_bound (gg0 16) (gg1 16) (gg2 16) 6 3 betac tauc (by decide +kernel)
      (by simp) (by simp) (by simp) (by decide +kernel))
    (by decide +kernel)
    (wsum_bound (gg0 16) (gg1 16) (gg2 16) 6 Lc betac (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 16) (gg1 16) (gg2 16) 3 (by simp) (by simp) (by simp) 6))
    (by decide +kernel) α

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 16 α t ^ 6)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 16 * (3 + α)) ^ 6) :=
  integral_moment_packed 16 6 (by norm_num) α hα Lc (by decide +kernel) Nmomc
    (by decide +kernel) (pev_Nmomc α)

/-- The certificate: `batchP 16 18 6 Lc Nmomc` is positive on `[0, 17/2]`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hU : (2 : ℝ) * α ≤ 17) :
    0 < pev (batchP 16 18 6 Lc Nmomc) α :=
  pev_pos_of_bern _ Bc 17 2 14 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hα (by exact_mod_cast hU)

/-- **The batch `16 ≤ n ≤ 18`.** -/
theorem finite_range {n : ℕ} (h0 : 16 ≤ n) (h1 : n ≤ 18) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h2α : 2 * α ≤ (18 : ℝ) - 1 := by
    exact_mod_cast two_alpha_le_of_le (by omega) h1 hfeas
  refine lt_of_le_of_lt (R_le_batch (n₀ := 16) (n := n) (n₁ := 18) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα (by linarith)) hfeas) ?_
  exact batch_lt_one (by norm_num) (by norm_num) (by norm_num) Lc (by decide +kernel) Nmomc hα
    (integral_lo α hα) (P_pos hα (by linarith))

end Batch16To18

end Sendov
