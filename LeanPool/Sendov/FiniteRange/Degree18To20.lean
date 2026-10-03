/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Certificate

/-!
# The batch 18 to 20

`Sendov.R_le_batch` bounds every `R n α` for `18 ≤ n ≤ 20` by the elementary part and
moment at `n₀ = 18` together with the prefactor at `n₁ = 20`, so one moment and one
certificate serve all 3 degrees.  The certificate has degree 16, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.

The moment numerator `Nmomc` is checked against the packed recurrence
(`Sendov.pev_wsum_eq_of_packed`), and the numerator `Sendov.batchP 18 20 7 Lc Nmomc` of
`1 - bound` is certified positive on `[0, 19/2]` by its Bernstein coefficients `Bc`
(`Sendov.pev_pos_of_bern`).  Every closed computation is evaluated by the kernel.
-/

public section

namespace Sendov

namespace Batch18To20

/-- The common denominator `L` of the moment weights: `j + 4 ∣ L` for every `j < 2k + 1`. -/
def Lc : ℤ := 12252240

/-- The base `β` at which polynomials in `α` are packed: it exceeds twice the absolute value
of every coefficient of `Nmomc` and of the weighted row sum `wsum Lc 0 (qrow …)`. -/
def betac : ℤ := 175927662917225332359966721

/-- The base `τ` at which the recurrence rows, evaluated at `betac`, are packed into a single
integer exponentiation: it exceeds twice the absolute value of every row entry. -/
def tauc : ℤ :=
  big [
    843409734000578209410972334682764700002022390759745948434344742136442797552789219566126849,
    44974961647775374731862145935889517758974312266434672837815042172397866699143848730300875,
    437302655829353348979444821042370136731772238800566165427866451094788337835108013894151378,
    24743903798686289485089015224938759859379750541156419506275337584501638157246946150682644,
    398207395719060972709006144830720087322332895913982687118230996245850245160708643412112175,
    274337745620624638936275643757889347744511177653609383831346364707120039183150206364616435,
    358483832023654241638315162089194303184230572320526650607]

/-- The moment numerator at `n₀ = 18`, `k = 7`. -/
def Nmomc : List ℤ := [
  114983435331692928,
  401488164091808640,
  646936588267361280,
  643985937083510784,
  451960609895464320,
  248282531980689024,
  125596226938129920,
  108748744491770880,
  9970165621984512,
  614458050662400,
  25497772633088,
  704123822080,
  12428021760,
  127074304,
  573440]

/-- Bernstein coefficients of `19 ^ 16 * batchP 18 20 7 Lc Nmomc` on `[0, 19/2]`. -/
def Bc : List ℤ := [
  208054831541205956325258240,
  17203895035486325389359037440,
  648259378137605309710414510080,
  14727421937681318437365642670080,
  224807707092248142434225291473920,
  2428302335918630270836617401472000,
  18909033566618236937208885048637440,
  98689416749826346246382499446231040,
  318407071045869598941683739959408640,
  563590537444333145187721274669015040,
  393167385526584554994491269896683520,
  267122351854705486268472576234946560,
  2865369297613449669676832070399098880,
  8869798097737413085373790738984468480,
  11837421152583511697993707192988467200,
  7172429002044214028440320000000000000,
  1449057687130325720448000000000000000]

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 18 α = (102 + 11 * α - 2 * α ^ 2) / (34 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 19 / 2) : 0 ≤ c 18 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 18) (gg1 18) (gg2 18) 7)) α :=
  pev_wsum_eq_of_packed (gg0 18) (gg1 18) (gg2 18) 7 22 Lc betac tauc Nmomc
    (by decide +kernel) (by decide +kernel)
    (rowZ_bound (gg0 18) (gg1 18) (gg2 18) 7 3 betac tauc (by decide +kernel)
      (by simp) (by simp) (by simp) (by decide +kernel))
    (by decide +kernel)
    (wsum_bound (gg0 18) (gg1 18) (gg2 18) 7 Lc betac (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 18) (gg1 18) (gg2 18) 3 (by simp) (by simp) (by simp) 7))
    (by decide +kernel) α

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 18 α t ^ 7)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 18 * (3 + α)) ^ 7) :=
  integral_moment_packed 18 7 (by norm_num) α hα Lc (by decide +kernel) Nmomc
    (by decide +kernel) (pev_Nmomc α)

/-- The certificate: `batchP 18 20 7 Lc Nmomc` is positive on `[0, 19/2]`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hU : (2 : ℝ) * α ≤ 19) :
    0 < pev (batchP 18 20 7 Lc Nmomc) α :=
  pev_pos_of_bern _ Bc 19 2 16 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hα (by exact_mod_cast hU)

/-- **The batch `18 ≤ n ≤ 20`.** -/
theorem finite_range {n : ℕ} (h0 : 18 ≤ n) (h1 : n ≤ 20) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h2α : 2 * α ≤ (20 : ℝ) - 1 := by
    exact_mod_cast two_alpha_le_of_le (by omega) h1 hfeas
  refine lt_of_le_of_lt (R_le_batch (n₀ := 18) (n := n) (n₁ := 20) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα (by linarith)) hfeas) ?_
  exact batch_lt_one (by norm_num) (by norm_num) (by norm_num) Lc (by decide +kernel) Nmomc hα
    (integral_lo α hα) (P_pos hα (by linarith))

end Batch18To20

end Sendov
