/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Certificate

/-!
# The batch 22 to 24

`Sendov.R_le_batch` bounds every `R n α` for `22 ≤ n ≤ 24` by the elementary part and
moment at `n₀ = 22` together with the prefactor at `n₁ = 24`, so one moment and one
certificate serve all 3 degrees.  The certificate has degree 20, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.

The moment numerator `Nmomc` is checked against the packed recurrence
(`Sendov.pev_wsum_eq_of_packed`), and the numerator `Sendov.batchP 22 24 9 Lc Nmomc` of
`1 - bound` is certified positive on `[0, 23/2]` by its Bernstein coefficients `Bc`
(`Sendov.pev_pos_of_bern`).  Every closed computation is evaluated by the kernel.
-/

public section

namespace Sendov

namespace Batch22To24

/-- The common denominator `L` of the moment weights: `j + 4 ∣ L` for every `j < 2k + 1`. -/
def Lc : ℤ := 232792560

/-- The base `β` at which polynomials in `α` are packed: it exceeds twice the absolute value
of every coefficient of `Nmomc` and of the weighted row sum `wsum Lc 0 (qrow …)`. -/
def betac : ℤ := 5774500618193131865874939367342081

/-- The base `τ` at which the recurrence rows, evaluated at `betac`, are packed into a single
integer exponentiation: it exceeds twice the absolute value of every row entry. -/
def tauc : ℤ :=
  big [
    952117888587198162177055098653469266065620379085335980107485574263048810931409342867852289,
    346820352631874830950754461420175060450633533746353185246669199140615772136375726619739932,
    312009671168290779571054910498924756815599827889354729460340914561182011034734511085509420,
    896808211158507170847555638174887653568352512765279104934288526037600114288775668310037707,
    953918608516395993601881499081882159387466173626361142174157279677614740584272959889365094,
    281973726028703612636651711022615997355506630751683900551998989656240038929214649085265235,
    536244361717247282601231552544467258823560691375175811619171316787642443135211274745052812,
    557856484812350076171944041251538965089353404668598911589180101281800066659429973404184827,
    769946235123570814826138813253665092373673643274802319253928901325155969193585802030603998,
    916403957981341978999482593278271409269805645884496135649846419759057009193613300612144616,
    52113403406617399568675768890198434300892440730552860468456457359822812]

/-- The moment numerator at `n₀ = 22`, `k = 9`. -/
def Nmomc : List ℤ := [
  63683904221147656083456,
  258124956324931816114176,
  484131886524725672024064,
  558778379485145387968512,
  446247743318805044026368,
  264110065181693649515520,
  122458189294350124959744,
  47704848438469830322176,
  18201381357540629025792,
  13524983241127074966528,
  1177792095898695426048,
  74548634146090795008,
  3411779294798364672,
  112771637948841984,
  2668046408810496,
  44104655831040,
  484339875840,
  3177971712,
  9437184]

/-- Bernstein coefficients of `23 ^ 20 * batchP 22 24 9 Lc Nmomc` on `[0, 23/2]`. -/
def Bc : List ℤ := [
  512436340556109636690275002662912,
  59959361694969728141148277131460608,
  3252843449711947375136824340636467200,
  108576466656212940030327227402791452672,
  2495350632810396894203913467518923227136,
  41868679629559298116282297797560924160000,
  530557324059939739725975244898725342347264,
  5178073877144904777553076109070235636957184,
  39223577019974028590785928385399991850631168,
  224034035337992794327685117154773147050278912,
  922657178054356216548323419116619544720277504,
  2604799234182272502073311559790132935970193408,
  4652550233867174709975015735175618077379264512,
  4342066551215800661342941056244216739426992128,
  1376833654324503836162135804279901244728803328,
  6049591862595819448351468963684693882875936768,
  29759214414740209787093232841795790507517935616,
  57076833722192473684106328785462591758150926336,
  55046812783674831988293428420585077993314975744,
  25927870732173758776217320138534663258311229440,
  4303071910978821827328069967365848284916613120]

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 22 α = (126 + 15 * α - 2 * α ^ 2) / (42 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 23 / 2) : 0 ≤ c 22 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 22) (gg1 22) (gg2 22) 9)) α :=
  pev_wsum_eq_of_packed (gg0 22) (gg1 22) (gg2 22) 9 28 Lc betac tauc Nmomc
    (by decide +kernel) (by decide +kernel)
    (rowZ_bound (gg0 22) (gg1 22) (gg2 22) 9 3 betac tauc (by decide +kernel)
      (by simp) (by simp) (by simp) (by decide +kernel))
    (by decide +kernel)
    (wsum_bound (gg0 22) (gg1 22) (gg2 22) 9 Lc betac (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 22) (gg1 22) (gg2 22) 3 (by simp) (by simp) (by simp) 9))
    (by decide +kernel) α

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 22 α t ^ 9)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 22 * (3 + α)) ^ 9) :=
  integral_moment_packed 22 9 (by norm_num) α hα Lc (by decide +kernel) Nmomc
    (by decide +kernel) (pev_Nmomc α)

/-- The certificate: `batchP 22 24 9 Lc Nmomc` is positive on `[0, 23/2]`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hU : (2 : ℝ) * α ≤ 23) :
    0 < pev (batchP 22 24 9 Lc Nmomc) α :=
  pev_pos_of_bern _ Bc 23 2 20 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hα (by exact_mod_cast hU)

/-- **The batch `22 ≤ n ≤ 24`.** -/
theorem finite_range {n : ℕ} (h0 : 22 ≤ n) (h1 : n ≤ 24) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h2α : 2 * α ≤ (24 : ℝ) - 1 := by
    exact_mod_cast two_alpha_le_of_le (by omega) h1 hfeas
  refine lt_of_le_of_lt (R_le_batch (n₀ := 22) (n := n) (n₁ := 24) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα (by linarith)) hfeas) ?_
  exact batch_lt_one (by norm_num) (by norm_num) (by norm_num) Lc (by decide +kernel) Nmomc hα
    (integral_lo α hα) (P_pos hα (by linarith))

end Batch22To24

end Sendov
