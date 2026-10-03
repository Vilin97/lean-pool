/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Certificate

/-!
# The batch 14 to 15

`Sendov.R_le_batch` bounds every `R n α` for `14 ≤ n ≤ 15` by the elementary part and
moment at `n₀ = 14` together with the prefactor at `n₁ = 15`, so one moment and one
certificate serve all 2 degrees.  The certificate has degree 12, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.

The moment numerator `Nmomc` is checked against the packed recurrence
(`Sendov.pev_wsum_eq_of_packed`), and the numerator `Sendov.batchP 14 15 5 Lc Nmomc` of
`1 - bound` is certified positive on `[0, 7]` by its Bernstein coefficients `Bc`
(`Sendov.pev_pos_of_bern`).  Every closed computation is evaluated by the kernel.
-/

public section

namespace Sendov

namespace Batch14To15

/-- The common denominator `L` of the moment weights: `j + 4 ∣ L` for every `j < 2k + 1`. -/
def Lc : ℤ := 360360

/-- The base `β` at which polynomials in `α` are packed: it exceeds twice the absolute value
of every coefficient of `Nmomc` and of the weighted row sum `wsum Lc 0 (qrow …)`. -/
def betac : ℤ := 5273811281588129281

/-- The base `τ` at which the recurrence rows, evaluated at `betac`, are packed into a single
integer exponentiation: it exceeds twice the absolute value of every row entry. -/
def tauc : ℤ :=
  big [
    429958677566179709215175220574978194512241977108241372511737172688952893630525928871748289,
    922353242397074581977699087266735169689253384888787652968648421800644465440084079049341105,
    598665938104246888891334041344492138378350247489747112270657502763060533670335383336131627,
    5240604256749137818001775409217258559398270]

/-- The moment numerator at `n₀ = 14`, `k = 5`. -/
def Nmomc : List ℤ := [
  259845693120,
  782498283840,
  1107091851840,
  1019339156160,
  768295987680,
  853275774240,
  79511527040,
  4444832000,
  147210240,
  2670080,
  20480]

/-- Bernstein coefficients of `7 ^ 12 * batchP 14 15 5 Lc Nmomc` on `[0, 7]`. -/
def Bc : List ℤ := [
  61872013896219072000,
  1601111771139196592640,
  18348690049666014205440,
  122077017846530971660800,
  513984158663421307680000,
  1240891390239189007737600,
  1755549123135331098032640,
  1823904907838616177469440,
  2204671461859361932819200,
  2696117661949998062649600,
  2073025154680504440998400,
  781703845979696640000000,
  100534751205977088000000]

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 14 α = (78 + 7 * α - 2 * α ^ 2) / (26 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 7) : 0 ≤ c 14 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 14) (gg1 14) (gg2 14) 5)) α :=
  pev_wsum_eq_of_packed (gg0 14) (gg1 14) (gg2 14) 5 16 Lc betac tauc Nmomc
    (by decide +kernel) (by decide +kernel)
    (rowZ_bound (gg0 14) (gg1 14) (gg2 14) 5 3 betac tauc (by decide +kernel)
      (by simp) (by simp) (by simp) (by decide +kernel))
    (by decide +kernel)
    (wsum_bound (gg0 14) (gg1 14) (gg2 14) 5 Lc betac (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 14) (gg1 14) (gg2 14) 3 (by simp) (by simp) (by simp) 5))
    (by decide +kernel) α

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 14 α t ^ 5)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 14 * (3 + α)) ^ 5) :=
  integral_moment_packed 14 5 (by norm_num) α hα Lc (by decide +kernel) Nmomc
    (by decide +kernel) (pev_Nmomc α)

/-- The certificate: `batchP 14 15 5 Lc Nmomc` is positive on `[0, 7]`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hU : (1 : ℝ) * α ≤ 7) :
    0 < pev (batchP 14 15 5 Lc Nmomc) α :=
  pev_pos_of_bern _ Bc 7 1 12 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hα (by exact_mod_cast hU)

/-- **The batch `14 ≤ n ≤ 15`.** -/
theorem finite_range {n : ℕ} (h0 : 14 ≤ n) (h1 : n ≤ 15) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h2α : 2 * α ≤ (15 : ℝ) - 1 := by
    exact_mod_cast two_alpha_le_of_le (by omega) h1 hfeas
  refine lt_of_le_of_lt (R_le_batch (n₀ := 14) (n := n) (n₁ := 15) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα (by linarith)) hfeas) ?_
  exact batch_lt_one (by norm_num) (by norm_num) (by norm_num) Lc (by decide +kernel) Nmomc hα
    (integral_lo α hα) (P_pos hα (by linarith))

end Batch14To15

end Sendov
