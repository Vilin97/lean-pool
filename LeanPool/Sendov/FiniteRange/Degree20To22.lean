/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Certificate

/-!
# The batch 20 to 22

`Sendov.R_le_batch` bounds every `R n α` for `20 ≤ n ≤ 22` by the elementary part and
moment at `n₀ = 20` together with the prefactor at `n₁ = 22`, so one moment and one
certificate serve all 3 degrees.  The certificate has degree 18, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.

The moment numerator `Nmomc` is checked against the packed recurrence
(`Sendov.pev_wsum_eq_of_packed`), and the numerator `Sendov.batchP 20 22 8 Lc Nmomc` of
`1 - bound` is certified positive on `[0, 21/2]` by its Bernstein coefficients `Bc`
(`Sendov.pev_pos_of_bern`).  Every closed computation is evaluated by the kernel.
-/

public section

namespace Sendov

namespace Batch20To22

/-- The common denominator `L` of the moment weights: `j + 4 ∣ L` for every `j < 2k + 1`. -/
def Lc : ℤ := 232792560

/-- The base `β` at which polynomials in `α` are packed: it exceeds twice the absolute value
of every coefficient of `Nmomc` and of the weighted row sum `wsum Lc 0 (qrow …)`. -/
def betac : ℤ := 4131209409209679854788987576321

/-- The base `τ` at which the recurrence rows, evaluated at `betac`, are packed into a single
integer exponentiation: it exceeds twice the absolute value of every row entry. -/
def tauc : ℤ :=
  big [
    415554409852677086782888653509986106731604823282151130888540570232939710702306888786166273,
    497970217303849145427269129679404213103006562198768221354213524467878675079767978766859201,
    423376770648009486446989819845183327368715672103880903585609634804230071151638268944708950,
    779542709253460049049834200030423394619361068308927407924992768190982659511467666364074304,
    389560191323401011583801350056642509421229073471652965690556344130689616076286735679016586,
    963919558050105735619336220634358348775620366460327078867856343356142091112197183816351904,
    369910042414392837789684225435587469649384627401365137215111142493529834089724868392831219,
    225592961214127138545037980122454589072908657663380807599570953499350023955756845650273335,
    44775284788996865642893254679922271778917421122771510633920083377417]

/-- The moment numerator at `n₀ = 20`, `k = 8`. -/
def Nmomc : List ℤ := [
  342652681018715139072,
  1290458050152354091008,
  2243577184611827226624,
  2399637756691021787136,
  1783512729454695095808,
  996976999580720707584,
  454864090944105851904,
  197832256724748957696,
  157260237317474747904,
  14092143950522867712,
  885156618381127680,
  38940288112115712,
  1195127971889152,
  25104659120128,
  344544313344,
  2787377152,
  10092544]

/-- Bernstein coefficients of `21 ^ 18 * batchP 20 22 8 Lc Nmomc` on `[0, 21/2]`. -/
def Bc : List ℤ := [
  1361239680374966604932786626560,
  135030682356201219145390618705920,
  6163511451857092722362120967536640,
  171594855639363412752272856968232960,
  3255957310631626716188397927312568320,
  44554558920046459491516231922710036480,
  453290997936448904603716305595259412480,
  3468251516616085189273932034626746204160,
  19073849804031571179903956653702206566400,
  71053461656939345827305421870236392325120,
  166958315995229224738578102322461012295680,
  214510890124420265157640841972968744550400,
  105082497094159080243259851604777919447040,
  187406689986046699469330950767298892267520,
  1236365563384202483001222335243224964136960,
  2904936705979936320722970854093187270574080,
  3244858794905868595707220189117172668170240,
  1717991759104484956215630011198593491271680,
  312909784907273821609979999034117413928960]

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 20 α = (114 + 13 * α - 2 * α ^ 2) / (38 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 21 / 2) : 0 ≤ c 20 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 20) (gg1 20) (gg2 20) 8)) α :=
  pev_wsum_eq_of_packed (gg0 20) (gg1 20) (gg2 20) 8 25 Lc betac tauc Nmomc
    (by decide +kernel) (by decide +kernel)
    (rowZ_bound (gg0 20) (gg1 20) (gg2 20) 8 3 betac tauc (by decide +kernel)
      (by simp) (by simp) (by simp) (by decide +kernel))
    (by decide +kernel)
    (wsum_bound (gg0 20) (gg1 20) (gg2 20) 8 Lc betac (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 20) (gg1 20) (gg2 20) 3 (by simp) (by simp) (by simp) 8))
    (by decide +kernel) α

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 20 α t ^ 8)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 20 * (3 + α)) ^ 8) :=
  integral_moment_packed 20 8 (by norm_num) α hα Lc (by decide +kernel) Nmomc
    (by decide +kernel) (pev_Nmomc α)

/-- The certificate: `batchP 20 22 8 Lc Nmomc` is positive on `[0, 21/2]`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hU : (2 : ℝ) * α ≤ 21) :
    0 < pev (batchP 20 22 8 Lc Nmomc) α :=
  pev_pos_of_bern _ Bc 21 2 18 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hα (by exact_mod_cast hU)

/-- **The batch `20 ≤ n ≤ 22`.** -/
theorem finite_range {n : ℕ} (h0 : 20 ≤ n) (h1 : n ≤ 22) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h2α : 2 * α ≤ (22 : ℝ) - 1 := by
    exact_mod_cast two_alpha_le_of_le (by omega) h1 hfeas
  refine lt_of_le_of_lt (R_le_batch (n₀ := 20) (n := n) (n₁ := 22) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα (by linarith)) hfeas) ?_
  exact batch_lt_one (by norm_num) (by norm_num) (by norm_num) Lc (by decide +kernel) Nmomc hα
    (integral_lo α hα) (P_pos hα (by linarith))

end Batch20To22

end Sendov
