/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Certificate

/-!
# The batch 24 to 26

`Sendov.R_le_batch` bounds every `R n α` for `24 ≤ n ≤ 26` by the elementary part and
moment at `n₀ = 24` together with the prefactor at `n₁ = 26`, so one moment and one
certificate serve all 3 degrees.  The certificate has degree 22, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.

The moment numerator `Nmomc` is checked against the packed recurrence
(`Sendov.pev_wsum_eq_of_packed`), and the numerator `Sendov.batchP 24 26 10 Lc Nmomc` of
`1 - bound` is certified positive on `[0, 25/2]` by its Bernstein coefficients `Bc`
(`Sendov.pev_pos_of_bern`).  Every closed computation is evaluated by the kernel.
-/

public section

namespace Sendov

namespace Batch24To26

/-- The common denominator `L` of the moment weights: `j + 4 ∣ L` for every `j < 2k + 1`. -/
def Lc : ℤ := 5354228880

/-- The base `β` at which polynomials in `α` are packed: it exceeds twice the absolute value
of every coefficient of `Nmomc` and of the weighted row sum `wsum Lc 0 (qrow …)`. -/
def betac : ℤ := 207169535963896720099395591492729077761

/-- The base `τ` at which the recurrence rows, evaluated at `betac`, are packed into a single
integer exponentiation: it exceeds twice the absolute value of every row entry. -/
def tauc : ℤ :=
  big [
    939262352917434034648884345143679115225022717302218543379275426810982214714060272108111873,
    777684405725058238089451929907092518333933640346101136344586892938040988765007336451882866,
    349830619658553076247959754553527964871466306663576806629616777965871520562804437537173211,
    576964681682338544951425176804035838668391516955724735694385595874871472656729746521144495,
    154456776919966756556228106088192297412170853978188023830339107067702315857956086036800427,
    441722254000912895245767176245015981661120146759421315921372443124954613543593343478799715,
    618301030883431417607618760856488445808986867630990003426706499628118824185435630199646483,
    363984727012208457255987446595584067643160838527137552770639009495325056672536563117416826,
    417711376775999926154464728822005557520196678362635217152684345650132590498266302261095946,
    138510475391263611402561988747434102004049942580845088682763442977894869192016597214433416,
    992419947663757588380429163324563529912415106411403011745947325590554409286979300143878596,
    926057162085274681727759515125318949719302456675519000372761221361307915031805467809964014,
    969978190017817116896159063010086182170935195315287986342487638387429295465163650234862127,
    24758917493327576141462812677830183371567017132]

/-- The moment numerator at `n₀ = 24`, `k = 10`. -/
def Nmomc : List ℤ := [
  315542595400376414343137280,
  1372405704784856075197992960,
  2771005826010710543999477760,
  3451094280477455969590272000,
  2974802471342849022363187200,
  1892050373140518166434754560,
  928743180964782053711800320,
  367295306457255483092705280,
  124654360837959477878768640,
  42359986648106960612198400,
  29853908180042393981322240,
  2515924687236660357795840,
  159168052874477224488960,
  7480111606347618385920,
  260880569954468167680,
  6725742542668431360,
  126534063532277760,
  1689884884992000,
  15189584117760,
  82465259520,
  204472320]

/-- Bernstein coefficients of `25 ^ 22 * batchP 24 26 10 Lc Nmomc` on `[0, 25/2]`. -/
def Bc : List ℤ := [
  4817152147030996435465919500800000000,
  655782502148927527231376162841600000000,
  41646935637107143639612532716331520000000,
  1638616681107312362479979453853388800000000,
  44741462734251676492463862114420211200000000,
  899985675687630043165425318396931660800000000,
  13819001147459867042500692227372552563200000000,
  165595496436717694900556392387658508226560000000,
  1569512731670794879387270982335010138860800000000,
  11831206606980075496567044544724954215027200000000,
  69609798863494105611080593669968653748537600000000,
  308998710083958162330649651969719971352268800000000,
  995490437597688874577045498755285990795130880000000,
  2208763366122944304999910681219987206484377600000000,
  3042969129793982887795785080447738671872614400000000,
  1922581657077424314703792308297129180767846400000000,
  212860736682647687566390550208064298508288000000000,
  4531487299041336178923473630855532497766973440000000,
  18017354731018933202691216610356762668050022400000000,
  29396090474017728277872617960000407537818009600000000,
  25009464606326035828239096485484400371695616000000000,
  10623032404934519993915536803114900789185740800000000,
  1620358343675974540316494325684964606628331520000000]

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 24 α = (138 + 17 * α - 2 * α ^ 2) / (46 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 25 / 2) : 0 ≤ c 24 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 24) (gg1 24) (gg2 24) 10)) α :=
  pev_wsum_eq_of_packed (gg0 24) (gg1 24) (gg2 24) 10 31 Lc betac tauc Nmomc
    (by decide +kernel) (by decide +kernel)
    (rowZ_bound (gg0 24) (gg1 24) (gg2 24) 10 3 betac tauc (by decide +kernel)
      (by simp) (by simp) (by simp) (by decide +kernel))
    (by decide +kernel)
    (wsum_bound (gg0 24) (gg1 24) (gg2 24) 10 Lc betac (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
    (wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 24) (gg1 24) (gg2 24) 3 (by simp) (by simp) (by simp) 10))
    (by decide +kernel) α

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 24 α t ^ 10)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 24 * (3 + α)) ^ 10) :=
  integral_moment_packed 24 10 (by norm_num) α hα Lc (by decide +kernel) Nmomc
    (by decide +kernel) (pev_Nmomc α)

/-- The certificate: `batchP 24 26 10 Lc Nmomc` is positive on `[0, 25/2]`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hU : (2 : ℝ) * α ≤ 25) :
    0 < pev (batchP 24 26 10 Lc Nmomc) α :=
  pev_pos_of_bern _ Bc 25 2 22 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hα (by exact_mod_cast hU)

/-- **The batch `24 ≤ n ≤ 26`.** -/
theorem finite_range {n : ℕ} (h0 : 24 ≤ n) (h1 : n ≤ 26) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h2α : 2 * α ≤ (26 : ℝ) - 1 := by
    exact_mod_cast two_alpha_le_of_le (by omega) h1 hfeas
  refine lt_of_le_of_lt (R_le_batch (n₀ := 24) (n := n) (n₁ := 26) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα (by linarith)) hfeas) ?_
  exact batch_lt_one (by norm_num) (by norm_num) (by norm_num) Lc (by decide +kernel) Nmomc hα
    (integral_lo α hα) (P_pos hα (by linarith))

end Batch24To26

end Sendov
