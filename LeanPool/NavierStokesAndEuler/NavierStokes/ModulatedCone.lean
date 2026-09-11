/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.ModulatedHistories
import Mathlib.Analysis.Calculus.Deriv.Prod
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActivationStocks
public import LeanPool.NavierStokesAndEuler.NavierStokes.JetBounds

/-!
# The true cone after radial modulation

The error estimates below concern the genuine derivatives of the realized
profiles. Their constants are obtained from the constructed periodic
primitives on compact sets, independently of the modulation frequency.
-/

section

/-!
# Quantitative stock bounds from actual field and history data

The two stock maps below are the exact integrated lag formulas. Their
Lipschitz constants are derived from smoothness and compactness on sets with
positive angular field and radius. No stock error estimate is assumed.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ModulatedStockBounds

open Set Filter ProfileHistories
open scoped Topology ContDiff

/-- Stock data: an abbreviation for `Fin 12 → ℝ`. -/
abbrev StockData := Fin 12 → ℝ
/-- Stock argument: an abbreviation for `Point × StockData`. -/
abbrev StockArgument := Point × StockData

/-- The field values followed by the actual five histories and their first
parameter derivatives. Pressure includes its prescribed value on the axis. -/
noncomputable def profileData {D : RadialDomain} (P : Profiles D) (p : Point) : StockData :=
  ![P.f p, P.U p, P.M p, parameterPartial P.M p, P.I p, parameterPartial P.I p,
    P.J p, parameterPartial P.J p, P.S p, parameterPartial P.S p,
    P.pressure p, parameterPartial P.pressure p]

/-- Stock map as an element of `ℝ × ℝ`. -/
noncomputable def stockMap (h : ℝ) (q : StockArgument) : ℝ × ℝ :=
  (ActivationStocks.stockOne h q.1.1 q.1.2 (q.2 0) (q.2 2) (q.2 3)
      (q.2 4) (q.2 5) (q.2 6) (q.2 7),
    ActivationStocks.stockTwo h q.1.1 q.1.2 (q.2 0) (q.2 1) (q.2 2) (q.2 3)
      (q.2 8) (q.2 9) (q.2 10) (q.2 11))

theorem profileData_coordinates {D : RadialDomain} (P : Profiles D) (h : ℝ)
    {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0) :
    stockMap h (p, profileData P p) =
      (ActivationStocks.profileStockOne P h p, ActivationStocks.profileStockTwo P h p) := by
  apply Prod.ext
  · exact (ActivationStocks.profileStockOne_eq P h hp hX.ne' hf).symm
  · exact (ActivationStocks.profileStockTwo_eq P h hp hX).symm

theorem profileData_smooth {D : RadialDomain} (P : Profiles D) :
    ContDiffOn ℝ ∞ (profileData P) D.carrier := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact P.f_smooth
  · exact P.U_smooth
  · exact P.M_smooth
  · exact parameterPartial_smooth D P.M_smooth
  · exact P.I_smooth
  · exact parameterPartial_smooth D P.I_smooth
  · exact P.J_smooth
  · exact parameterPartial_smooth D P.J_smooth
  · exact P.S_smooth
  · exact parameterPartial_smooth D P.S_smooth
  · exact P.pressure_smooth
  · exact parameterPartial_smooth D P.pressure_smooth

/-- Stock domain, given by `{q | 0 < q.1.1 ∧ NaturalAxisData.L h q.1.2 ≠ 0 ∧ 0 < q.2 0}`. -/
noncomputable def stockDomain (h : ℝ) : Set StockArgument :=
  {q | 0 < q.1.1 ∧ NaturalAxisData.L h q.1.2 ≠ 0 ∧ 0 < q.2 0}

theorem isOpen_stockDomain (h : ℝ) : IsOpen (stockDomain h) := by
  have hL : Continuous (fun q : StockArgument => NaturalAxisData.L h q.1.2) := by
    unfold NaturalAxisData.L
    fun_prop
  exact (isOpen_lt continuous_const (continuous_fst.comp continuous_fst)).inter
    ((isOpen_ne_fun hL continuous_const).inter
      (isOpen_lt continuous_const ((continuous_apply 0).comp continuous_snd)))

theorem stockMap_smooth (h : ℝ) : ContDiffOn ℝ ∞ (stockMap h) (stockDomain h) := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  have hX : q.1.1 ≠ 0 := hq.1.ne'
  have hf : q.2 0 ≠ 0 := hq.2.2.ne'
  have hs : Real.sqrt (2 * q.1.1) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos (by norm_num) hq.1)).ne'
  have hL : NaturalAxisData.L h q.1.2 ≠ 0 := hq.2.1
  have hxc : ContDiffAt ℝ ∞ (fun q : StockArgument => q.1.1) q := contDiffAt_fst.fst
  have hη : ContDiffAt ℝ ∞ (fun q : StockArgument => q.1.2) q := contDiffAt_fst.snd
  have hz (i : Fin 12) : ContDiffAt ℝ ∞ (fun q : StockArgument => q.2 i) q :=
    ((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffAt
  have hd : ContDiffAt ℝ ∞ (fun q : StockArgument => NaturalAxisData.d q.1.2) q :=
    contDiffAt_const.sub (hη.pow 2)
  have hLc : ContDiffAt ℝ ∞ (fun q : StockArgument => NaturalAxisData.L h q.1.2) q :=
    contDiffAt_const.sub (contDiffAt_const.mul (hη.pow 2))
  have hmass : ContDiffAt ℝ ∞ (fun q : StockArgument =>
      ActivationStocks.massFlux h q.1.1 q.1.2 (q.2 2) (q.2 3)) q :=
    (hxc.sub ((contDiffAt_const.mul hη).mul (hz 2))).sub (hd.mul (hz 3))
  have hrem : ContDiffAt ℝ ∞ (fun q : StockArgument =>
      ActivationStocks.angularRemainder h q.1.2 (q.2 4) (q.2 5) (q.2 6) (q.2 7)) q :=
    (((contDiffAt_const.mul (hz 4)).sub ((contDiffAt_const.mul hη).mul (hz 5))).sub
      (hd.mul (hz 7))).add ((contDiffAt_const.mul hη).mul (hz 6))
  have hA : ContDiffAt ℝ ∞ (fun q : StockArgument =>
      ActivationStocks.stockOne h q.1.1 q.1.2 (q.2 0) (q.2 2) (q.2 3)
        (q.2 4) (q.2 5) (q.2 6) (q.2 7)) q := by
    exact (hmass.neg.add (hrem.div ((contDiffAt_const.mul hxc).mul (hz 0))
      (mul_ne_zero (mul_ne_zero (by norm_num) hX) hf))).div hLc hL
  have hC : ContDiffAt ℝ ∞ (fun q : StockArgument =>
      ActivationStocks.stockTwo h q.1.1 q.1.2 (q.2 0) (q.2 1) (q.2 2) (q.2 3)
        (q.2 8) (q.2 9) (q.2 10) (q.2 11)) q := by
    have hroot : ContDiffAt ℝ ∞ (fun q : StockArgument => Real.sqrt (2 * q.1.1)) q :=
      (contDiffAt_const.mul hxc).sqrt (mul_ne_zero (by norm_num) hX)
    exact ((((hmass.neg.mul (hz 1)).add
      (contDiffAt_const.mul ((hz 2).sub (hη.mul (hz 3))))).add
      ((contDiffAt_const.mul hη).mul (hz 8))).sub (hd.mul (hz 9)) |>.add
      (hxc.mul (((contDiffAt_const.mul hη).mul (hz 10)).sub (hd.mul (hz 11))))).div
      ((hLc.mul hroot).mul (hz 0)) (mul_ne_zero (mul_ne_zero hL hs) hf)
  exact hA.prodMk hC

/-- Data set, given by `Metric.closedBall 0 R ∩ {z | μ ≤ z 0}`. -/
noncomputable def dataSet (μ R : ℝ) : Set StockData :=
  Metric.closedBall 0 R ∩ {z | μ ≤ z 0}

theorem isCompact_dataSet (μ R : ℝ) : IsCompact (dataSet μ R) :=
  (isCompact_closedBall (0 : StockData) R).inter_right
    (isClosed_le continuous_const (continuous_apply 0))

theorem convex_dataSet (μ R : ℝ) : Convex ℝ (dataSet μ R) := by
  have hh : Convex ℝ {z : StockData | μ ≤ z 0} := by
    intro x hx y hy a b ha hb hab
    change μ ≤ a * x 0 + b * y 0
    have hax := mul_le_mul_of_nonneg_left hx ha
    have hby := mul_le_mul_of_nonneg_left hy hb
    calc
      μ = (a + b) * μ := by rw [hab]; ring
      _ = a * μ + b * μ := by ring
      _ ≤ a * x 0 + b * y 0 := add_le_add hax hby
  exact (convex_closedBall (0 : StockData) R).inter hh

/-- Uniform Lipschitz continuity in all field/history data on a compact
positive-radius set. Only the reference coefficients depend on position. -/
theorem stockMap_lipschitz_on_dataSet (h μ R : ℝ) (hμ : 0 < μ)
    {S : Set Point} (hS : IsCompact S) (hX : ∀ p ∈ S, 0 < p.1)
    (hL : ∀ p ∈ S, NaturalAxisData.L h p.2 ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ z ∈ dataSet μ R, ∀ w ∈ dataSet μ R,
      ‖stockMap h (p, w) - stockMap h (p, z)‖ ≤ C * ‖w - z‖ := by
  have hsub : S ×ˢ dataSet μ R ⊆ stockDomain h := by
    intro q hq
    exact ⟨hX q.1 hq.1, hL q.1 hq.1, hμ.trans_le hq.2.2⟩
  have hds : ContDiffOn ℝ ∞ (fderiv ℝ (stockMap h)) (stockDomain h) :=
    (stockMap_smooth h).fderiv_of_isOpen (isOpen_stockDomain h) (by simp)
  have hd := hds.continuousOn
  obtain ⟨C, hC⟩ := (hS.prod (isCompact_dataSet μ R)).exists_bound_of_continuousOn (hd.mono hsub)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p hp z hz w hw
  have hconv : Convex ℝ ({p} ×ˢ dataSet μ R) := (convex_singleton p).prod (convex_dataSet μ R)
  have hderiv : ∀ q ∈ ({p} ×ˢ dataSet μ R),
      HasFDerivWithinAt (stockMap h) (fderiv ℝ (stockMap h) q) ({p} ×ˢ dataSet μ R) q := by
    intro q hq
    have hqp : q.1 = p := hq.1
    have hqS : q ∈ S ×ˢ dataSet μ R := ⟨hqp.symm ▸ hp, hq.2⟩
    exact (((stockMap_smooth h).contDiffAt ((isOpen_stockDomain h).mem_nhds (hsub
        hqS))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hbound : ∀ q ∈ ({p} ×ˢ dataSet μ R), ‖fderiv ℝ (stockMap h) q‖ ≤ max C 0 := by
    intro q hq
    have hqp : q.1 = p := hq.1
    exact (hC q ⟨hqp.symm ▸ hp, hq.2⟩).trans (le_max_left _ _)
  have hm := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound hconv
    (show (p, z) ∈ ({p} ×ˢ dataSet μ R) from ⟨rfl, hz⟩)
    (show (p, w) ∈ ({p} ×ˢ dataSet μ R) from ⟨rfl, hw⟩)
  simpa only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero,
    max_eq_right (norm_nonneg (w - z))] using hm

/-- A small data perturbation automatically retains a positive angular
field, and its exact stock error is bounded linearly by the data error. -/
theorem stockMap_small_perturbation (h μ B : ℝ) (hμ : 0 < μ)
    {S : Set Point} (hS : IsCompact S) (hX : ∀ p ∈ S, 0 < p.1)
    (hL : ∀ p ∈ S, NaturalAxisData.L h p.2 ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ z w : StockData,
      ‖z‖ ≤ B → 2 * μ ≤ z 0 → ‖w - z‖ ≤ min 1 μ →
      μ ≤ w 0 ∧ ‖stockMap h (p, w) - stockMap h (p, z)‖ ≤ C * ‖w - z‖ := by
  obtain ⟨C, hC, hb⟩ := stockMap_lipschitz_on_dataSet h μ (B + 1) hμ hS hX hL
  refine ⟨C, hC, ?_⟩
  intro p hp z w hz hz0 hclose
  have hcomp : |w 0 - z 0| ≤ ‖w - z‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (w - z) (0 : Fin 12)
  have hw0 : μ ≤ w 0 := by
    have := (abs_le.mp (hcomp.trans (hclose.trans (min_le_right _ _)))).1
    linarith
  have hzmem : z ∈ dataSet μ (B + 1) := by
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using
        (hz.trans (by linarith : B ≤ B + 1))
    · change μ ≤ z 0
      linarith
  have hwmem : w ∈ dataSet μ (B + 1) := by
    refine ⟨?_, hw0⟩
    have hw : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (w - z) z
    have hn : ‖w‖ ≤ B + 1 := by linarith [hclose.trans (min_le_left _ _)]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hn
  exact ⟨hw0, hb p hp z hzmem w hwmem⟩

/-- Coordinatewise bounds on genuine field/history data give the required
norm bound; all first history derivatives are actual parameter derivatives. -/
theorem profileData_error_bound {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D')
    (p : Point) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : |P.f p - Q.f p| ≤ ε) (hU : |P.U p - Q.U p| ≤ ε)
    (hH : ∀ r : StressActivation.HistoryRow,
      |StressActivation.profileHistory P r p - StressActivation.profileHistory Q r p| ≤ ε ∧
      |parameterPartial (StressActivation.profileHistory P r) p -
        parameterPartial (StressActivation.profileHistory Q r) p| ≤ ε) :
    ‖profileData P p - profileData Q p‖ ≤ ε := by
  apply (pi_norm_le_iff_of_nonneg hε).mpr
  intro i
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  fin_cases i
  · exact hf
  · exact hU
  · exact (hH .mass).1
  · exact (hH .mass).2
  · exact (hH .angular).1
  · exact (hH .angular).2
  · exact (hH .transport).1
  · exact (hH .transport).2
  · exact (hH .energy).1
  · exact (hH .energy).2
  · exact (hH .pressure).1
  · exact (hH .pressure).2

/-- Uniform quantitative stability of both actual profile stocks, around
a fixed smooth positive nominal profile on a compact set. -/
theorem profile_stocks_lipschitz {D : RadialDomain} (Q : Profiles D) (h : ℝ)
    {S : Set Point} (hS : IsCompact S) (hSD : S ⊆ D.carrier)
    (hX : ∀ p ∈ S, 0 < p.1) (hL : ∀ p ∈ S, NaturalAxisData.L h p.2 ≠ 0)
    (hpos : ∀ p ∈ S, 0 < Q.f p) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ {D' : RadialDomain} (P : Profiles D'),
      ∀ p ∈ S, p ∈ D'.carrier → ‖profileData P p - profileData Q p‖ ≤ δ →
      0 < P.f p ∧
      |ActivationStocks.profileStockOne P h p - ActivationStocks.profileStockOne Q h p| ≤
        C * ‖profileData P p - profileData Q p‖ ∧
      |ActivationStocks.profileStockTwo P h p - ActivationStocks.profileStockTwo Q h p| ≤
        C * ‖profileData P p - profileData Q p‖ := by
  obtain ⟨fmin, hfmin, hmin⟩ := hS.exists_forall_le' (Q.f_smooth.continuousOn.mono hSD) hpos
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn ((profileData_smooth Q).continuousOn.mono hSD)
  have hμ : 0 < fmin / 2 := by positivity
  obtain ⟨C, hC, hbound⟩ := stockMap_small_perturbation h (fmin / 2) B hμ hS hX hL
  refine ⟨min 1 (fmin / 2), C, lt_min zero_lt_one hμ, hC, ?_⟩
  intro D' P p hp hpD hclose
  have hbase : 2 * (fmin / 2) ≤ profileData Q p 0 := by
    change 2 * (fmin / 2) ≤ Q.f p
    linarith [hmin p hp]
  obtain ⟨hnew, hpair⟩ := hbound p hp (profileData Q p) (profileData P p) (hB p hp) hbase hclose
  have hPpos : 0 < P.f p := hμ.trans_le hnew
  rw [profileData_coordinates P h hpD (hX p hp) hPpos.ne',
    profileData_coordinates Q h (hSD hp) (hX p hp) (hpos p hp).ne'] at hpair
  have hcoords :
      |ActivationStocks.profileStockOne P h p - ActivationStocks.profileStockOne Q h p| ≤
        C * ‖profileData P p - profileData Q p‖ ∧
      |ActivationStocks.profileStockTwo P h p - ActivationStocks.profileStockTwo Q h p| ≤
        C * ‖profileData P p - profileData Q p‖ := by
    simpa only [Prod.mk_sub_mk, Prod.norm_def, Real.norm_eq_abs, max_le_iff] using hpair
  exact ⟨hPpos, hcoords⟩

/-- The actual stock difference is bounded linearly by a common bound for
the two field values and the five history values/first parameter derivatives. -/
theorem profile_stocks_from_history_bounds {D : RadialDomain} (Q : Profiles D) (h : ℝ)
    {S : Set Point} (hS : IsCompact S) (hSD : S ⊆ D.carrier)
    (hX : ∀ p ∈ S, 0 < p.1) (hL : ∀ p ∈ S, NaturalAxisData.L h p.2 ≠ 0)
    (hpos : ∀ p ∈ S, 0 < Q.f p) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ {D' : RadialDomain} (P : Profiles D'),
      ∀ p ∈ S, p ∈ D'.carrier → ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ →
      |P.f p - Q.f p| ≤ ε → |P.U p - Q.U p| ≤ ε →
      (∀ r : StressActivation.HistoryRow,
        |StressActivation.profileHistory P r p - StressActivation.profileHistory Q r p| ≤ ε ∧
        |parameterPartial (StressActivation.profileHistory P r) p -
          parameterPartial (StressActivation.profileHistory Q r) p| ≤ ε) →
      0 < P.f p ∧
      |ActivationStocks.profileStockOne P h p - ActivationStocks.profileStockOne Q h p| ≤ C * ε ∧
      |ActivationStocks.profileStockTwo P h p - ActivationStocks.profileStockTwo Q h p| ≤ C * ε :=
          by
  obtain ⟨δ, C, hδ, hC, hb⟩ := profile_stocks_lipschitz Q h hS hSD hX hL hpos
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro D' P p hp hpD ε hε hεδ hf hU hH
  have hd := profileData_error_bound P Q p hε hf hU hH
  obtain ⟨hPpos, hb₁, hb₂⟩ := hb P p hp hpD (hd.trans hεδ)
  exact ⟨hPpos, hb₁.trans (mul_le_mul_of_nonneg_left hd hC),
    hb₂.trans (mul_le_mul_of_nonneg_left hd hC)⟩

/-- A first parameter-jet bound on an actual history difference supplies
exactly the value/derivative estimates used by the stock adapter. -/
theorem profileHistory_first_jet_bound {D D' : RadialDomain}
    (P : Profiles D) (Q : Profiles D') (r : StressActivation.HistoryRow)
    {p : Point} (hp : p ∈ D.carrier) (hp' : p ∈ D'.carrier)
    {J : Set ℝ} {ε : ℝ}
    (hjet : JetBounds.FiniteJetBound 1 (fun η =>
      StressActivation.profileHistory P r (p.1, η) -
        StressActivation.profileHistory Q r (p.1, η)) J ε) (hη : p.2 ∈ J) :
    |StressActivation.profileHistory P r p - StressActivation.profileHistory Q r p| ≤ ε ∧
      |parameterPartial (StressActivation.profileHistory P r) p -
        parameterPartial (StressActivation.profileHistory Q r) p| ≤ ε := by
  have hd := (parameterPartial_hasDerivAt D (StressActivation.profileHistory_smooth P r) hp).fun_sub
    (parameterPartial_hasDerivAt D' (StressActivation.profileHistory_smooth Q r) hp')
  constructor
  · simpa only [Real.norm_eq_abs, Prod.eta] using hjet.norm_le hη
  · simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one,
      hd.deriv, Real.norm_eq_abs] using hjet 1 le_rfl p.2 hη

/-- Actual field and five-row history estimates of order `1/n` imply an
eventual uniform `1/n` estimate for both actual lag stocks. The integer
threshold and the stock constant are conclusions. -/
theorem profile_stocks_rate {D D' : RadialDomain} (Q : Profiles D) (h : ℝ)
    (P : ℝ → Profiles D') {S : Set Point} (hS : IsCompact S)
    (hSD : S ⊆ D.carrier) (hSD' : S ⊆ D'.carrier)
    (hX : ∀ p ∈ S, 0 < p.1) (hL : ∀ p ∈ S, NaturalAxisData.L h p.2 ≠ 0)
    (hpos : ∀ p ∈ S, 0 < Q.f p)
    (n₀ Cdata : ℝ) (hCdata : 0 ≤ Cdata)
    (hdata : ∀ n : ℝ, n₀ ≤ n → 1 ≤ n → ∀ p ∈ S,
      |(P n).f p - Q.f p| ≤ Cdata / n ∧ |(P n).U p - Q.U p| ≤ Cdata / n ∧
      ∀ r : StressActivation.HistoryRow,
        |StressActivation.profileHistory (P n) r p - StressActivation.profileHistory Q r p| ≤ Cdata
            / n ∧
        |parameterPartial (StressActivation.profileHistory (P n) r) p -
          parameterPartial (StressActivation.profileHistory Q r) p| ≤ Cdata / n) :
    ∃ N : ℕ, ∃ C : ℝ, 0 < N ∧ 0 ≤ C ∧ ∀ n : ℝ, (N : ℝ) ≤ n → ∀ p ∈ S,
      0 < (P n).f p ∧
      |ActivationStocks.profileStockOne (P n) h p - ActivationStocks.profileStockOne Q h p| ≤ C / n
          ∧
      |ActivationStocks.profileStockTwo (P n) h p - ActivationStocks.profileStockTwo Q h p| ≤ C / n
          := by
  obtain ⟨δ, C, hδ, hC, hb⟩ := profile_stocks_from_history_bounds Q h hS hSD hX hL hpos
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (max n₀ (Cdata / δ)))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  refine ⟨N, C * Cdata, by exact_mod_cast (lt_trans zero_lt_one hN1), mul_nonneg hC hCdata, ?_⟩
  intro n hn p hp
  have hn1 : 1 ≤ n := hN1.le.trans hn
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  have hn₀ : n₀ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans (hN.le.trans hn)
  have hδn : Cdata / δ ≤ n :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (hN.le.trans hn)
  have hsmall : Cdata / n ≤ δ := by
    apply (div_le_iff₀ hnpos).mpr
    have := (div_le_iff₀ hδ).mp hδn
    linarith
  obtain ⟨hf, hU, hH⟩ := hdata n hn₀ hn1 p hp
  obtain ⟨hPpos, hs₁, hs₂⟩ := hb (P n) p hp (hSD' hp) (Cdata / n)
    (div_nonneg hCdata hnpos.le) hsmall hf hU hH
  exact ⟨hPpos, by simpa only [mul_div_assoc] using hs₁, by simpa only [mul_div_assoc] using hs₂⟩

end NavierStokes.ModulatedStockBounds

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ModulatedCone

open Set
open scoped Topology ContDiff
open ParametricModulation

/-- The actual angular shear of an angular profile `E`. -/
noncomputable def angularShear (E : RadialParameter → ℝ) (p : RadialParameter) : ℝ :=
  1 - 2 * p.1 * deriv (fun X => E (X, p.2)) p.1 / E p

/-- The signed axial shear, in the `C = -b` convention of `TrueConeLoop`. -/
noncomputable def signedAxialShear (E U : RadialParameter → ℝ) (p : RadialParameter) : ℝ :=
  -(2 * p.1 * deriv (fun X => U (X, p.2)) p.1 / E p)

/-- Compactness bounds a continuous periodic family at all real phases. -/
theorem compact_periodic_bound {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (F : X × ℝ → ℝ)
    (hF : ContinuousOn F (K ×ˢ (univ : Set ℝ)))
    (hperiod : ∀ x ∈ K, Function.Periodic (fun θ => F (x, θ)) 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ∀ θ, |F (x, θ)| ≤ M := by
  have hcompact : IsCompact (K ×ˢ Icc (0 : ℝ) 1) := hK.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn
    (hF.mono (fun z hz => ⟨hz.1, mem_univ _⟩))
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro x hx θ
  obtain ⟨φ, hφ, heq⟩ := (hperiod x hx).exists_mem_Ico₀ (by norm_num) θ
  rw [heq]
  exact (hM (x, φ) ⟨hx, hφ.1, hφ.2.le⟩).trans (le_max_left _ _)

/-- The slow radial derivative of a periodic primitive, with the phase held fixed. -/
noncomputable def slowRadial (Q : RadialParameter × ℝ → ℝ)
    (z : RadialParameter × ℝ) : ℝ :=
  RadialModulation.partialX (asRadialPrimitive Q) (z.1.1, z.1.2, z.2)

theorem slowRadial_smooth (Q : RadialParameter × ℝ → ℝ) (hQ : ContDiff ℝ ∞ Q) :
    ContDiff ℝ ∞ (slowRadial Q) := by
  have hd : ContDiff ℝ ∞ (RadialModulation.partialX (asRadialPrimitive Q)) :=
    ((asRadialPrimitive_contDiff Q hQ).fderiv_right (by simp)).clm_apply contDiff_const
  exact hd.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))

theorem slowRadial_eq_deriv (Q : RadialParameter × ℝ → ℝ) (hQ : ContDiff ℝ ∞ Q)
    (X η θ : ℝ) :
    slowRadial Q ((X, η), θ) = deriv (fun x => Q ((x, η), θ)) X := by
  have hg := (hasDerivAt_id X).prodMk
    ((hasDerivAt_const X η).prodMk (hasDerivAt_const X θ))
  exact (((asRadialPrimitive_contDiff Q hQ).differentiable (by simp)
    (X, η, θ)).hasFDerivAt.comp_hasDerivAt X hg).deriv.symm

/-- Differentiation in the slow radius preserves phase periodicity. -/
theorem slowRadial_periodic (Q : RadialParameter × ℝ → ℝ) (hQ : ContDiff ℝ ∞ Q)
    (hperiod : ∀ p, Function.Periodic (fun θ => Q (p, θ)) 1) (p : RadialParameter) :
    Function.Periodic (fun θ => slowRadial Q (p, θ)) 1 := by
  rcases p with ⟨X, η⟩
  intro θ
  change slowRadial Q ((X, η), θ + 1) = slowRadial Q ((X, η), θ)
  rw [slowRadial_eq_deriv Q hQ, slowRadial_eq_deriv Q hQ]
  congr 1
  funext x
  exact hperiod (x, η) θ

variable {a m p₁ p₂ : RadialParameter → ℝ} {K B : Set RadialParameter}

/-- Angular error factor, given by `-2 * z.1.1 * slowRadial r.angularPrimitive z`. -/
noncomputable def angularErrorFactor (r : TrueConeRealization a m p₁ p₂ K B)
    (z : RadialParameter × ℝ) : ℝ :=
  -2 * z.1.1 * slowRadial r.angularPrimitive z

/-- A smooth error factor at inverse frequency zero. -/
noncomputable def axialErrorFactor (r : TrueConeRealization a m p₁ p₂ K B)
    (E : RadialParameter → ℝ) (z : (ℝ × RadialParameter) × ℝ) : ℝ :=
  -r.signedAxialLoop (z.1.2, z.2) * r.angularPrimitive (z.1.2, z.2) *
      StressActivation.meanExp (-z.1.1 * r.angularPrimitive (z.1.2, z.2)) -
    (2 * z.1.2.1 * slowRadial (r.axialPrimitive E) (z.1.2, z.2) / E z.1.2) *
      Real.exp (-z.1.1 * r.angularPrimitive (z.1.2, z.2))

theorem signed_shear_factor (C D A n : ℝ) :
    -((-C + D / n) / Real.exp (A / n)) - C =
      (1 / n) * (-C * A * StressActivation.meanExp (-(1 / n) * A) -
        D * Real.exp (-(1 / n) * A)) := by
  have he : -(A / n) = -(1 / n) * A := by ring
  calc
    _ = C * (Real.exp (-(1 / n) * A) - 1) -
        (1 / n) * D * Real.exp (-(1 / n) * A) := by
      rw [← he, Real.exp_neg]
      ring
    _ = _ := by rw [StressActivation.exp_sub_one]; ring

/-- Exact factorization of both errors in genuine realized shears. -/
theorem realized_shears_factor
    (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (n : ℝ) (hn : n ≠ 0) (p : RadialParameter) (hp : p ∈ K)
    (hX : p.1 ≠ 0) (hE0 : E p ≠ 0)
    (haNom : a p = angularShear E p)
    (hbNom : a p * m p = signedAxialShear E U p) :
    (angularShear (fun q => realizedE r E n q.1 q.2) p -
        r.angularLoop (p, n * Real.log p.1) =
      (1 / n) * angularErrorFactor r (p, n * Real.log p.1)) ∧
    (signedAxialShear (fun q => realizedE r E n q.1 q.2)
        (fun q => realizedU r E U n q.1 q.2) p -
        r.signedAxialLoop (p, n * Real.log p.1) =
      (1 / n) * axialErrorFactor r E ((1 / n, p), n * Real.log p.1)) := by
  have hbNom' : -a p * m p =
      2 * p.1 * deriv (fun x => U (x, p.2)) p.1 / E p := by
    change a p * m p = -(2 * p.1 * deriv (fun x => U (x, p.2)) p.1 / E p) at hbNom
    linarith
  have hexact := realized_shears_exact r E U ha hm hp₂ hE hU n p.1 p.2 hn hX hE0 hp
    haNom hbNom'
  constructor
  · change (1 - 2 * p.1 * deriv (fun x => realizedE r E n x p.2) p.1 /
      realizedE r E n p.1 p.2) - _ = _
    rw [hexact.1]
    unfold angularErrorFactor slowRadial
    ring
  · change -(2 * p.1 * deriv (fun x => realizedU r E U n x p.2) p.1 /
      realizedE r E n p.1 p.2) - _ = _
    rw [hexact.2]
    have hd : 2 * p.1 * RadialModulation.partialX
        (asRadialPrimitive (r.axialPrimitive E)) (p.1, p.2, n * Real.log p.1) /
        (n * E p) =
      (2 * p.1 * slowRadial (r.axialPrimitive E) (p, n * Real.log p.1) / E p) / n := by
      simp only [slowRadial, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hd, signed_shear_factor]
    rfl

/-- The axial error factor is continuous even at inverse frequency zero. -/
theorem axialErrorFactor_continuousOn
    (r : TrueConeRealization a m p₁ p₂ K B) (E : RadialParameter → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (haK : ∀ p ∈ K, 0 < a p)
    (hE0 : ∀ p ∈ K, E p ≠ 0) :
    ContinuousOn (axialErrorFactor r E) ((Icc (0 : ℝ) 1 ×ˢ K) ×ˢ (univ : Set ℝ)) := by
  have hp := r.primitives_smooth E ha hm hp₂ hE
  have hmap : Continuous (fun z : (ℝ × RadialParameter) × ℝ => (z.1.2, z.2)) :=
    (continuous_snd.comp continuous_fst).prodMk continuous_snd
  have hA := hp.1.continuous.comp hmap
  have hAX := (slowRadial_smooth _ hp.2).continuous.comp hmap
  have hC : ContinuousOn (fun z : (ℝ × RadialParameter) × ℝ =>
      r.signedAxialLoop (z.1.2, z.2)) ((Icc (0 : ℝ) 1 ×ˢ K) ×ˢ (univ : Set ℝ)) :=
    ((r.loop_smooth ha hm hp₂).2.continuousOn).comp
    hmap.continuousOn (fun z hz => ⟨haK z.1.2 hz.1.2, mem_univ _⟩)
  have hEp : Continuous (fun z : (ℝ × RadialParameter) × ℝ => E z.1.2) :=
    hE.continuous.comp (continuous_snd.comp continuous_fst)
  have ht : Continuous (fun z : (ℝ × RadialParameter) × ℝ =>
      -z.1.1 * r.angularPrimitive (z.1.2, z.2)) :=
    (continuous_fst.comp continuous_fst).neg.mul hA
  exact ((hC.neg.mul hA.continuousOn).mul
    (StressActivation.meanExp_smooth.continuous.comp ht).continuousOn).sub
      (((continuousOn_const.mul (continuous_fst.comp
        (continuous_snd.comp continuous_fst)).continuousOn).mul hAX.continuousOn).div
        hEp.continuousOn (fun z hz => hE0 z.1.2 hz.1.2) |>.mul
          (Real.continuous_exp.comp ht).continuousOn)

/-- Both actual shears differ from their prescribed loop values by `C/n`.
No derivative estimate for the modulated profiles is assumed. -/
theorem realized_shears_uniform_bound
    (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (hK : IsCompact K)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (haK : ∀ p ∈ K, 0 < a p) (hX : ∀ p ∈ K, p.1 ≠ 0)
    (hE0 : ∀ p ∈ K, E p ≠ 0)
    (haNom : ∀ p ∈ K, a p = angularShear E p)
    (hbNom : ∀ p ∈ K, a p * m p = signedAxialShear E U p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℝ, 1 ≤ n → ∀ p ∈ K,
      |angularShear (fun q => realizedE r E n q.1 q.2) p -
        r.angularLoop (p, n * Real.log p.1)| ≤ C / n ∧
      |signedAxialShear (fun q => realizedE r E n q.1 q.2)
        (fun q => realizedU r E U n q.1 q.2) p -
        r.signedAxialLoop (p, n * Real.log p.1)| ≤ C / n := by
  have hp := r.primitives_smooth E ha hm hp₂ hE
  have hperA := fun p => (r.primitives_periodic E ha hm hp₂ p).1
  have hperB := fun p => (r.primitives_periodic E ha hm hp₂ p).2
  have hperAX := slowRadial_periodic _ hp.1 hperA
  have hperBX := slowRadial_periodic _ hp.2 hperB
  have hca : Continuous (angularErrorFactor r) :=
    (continuous_const.mul (continuous_fst.comp continuous_fst)).mul
      (slowRadial_smooth _ hp.1).continuous
  obtain ⟨CA, hCA, hba⟩ := compact_periodic_bound hK (angularErrorFactor r)
    hca.continuousOn (by intro p _ θ; simp only [angularErrorFactor, hperAX p θ])
  obtain ⟨CC, hCC, hbc⟩ := compact_periodic_bound (isCompact_Icc.prod hK)
    (axialErrorFactor r E) (axialErrorFactor_continuousOn r E ha hm hp₂ hE haK hE0)
    (by
      intro z hz θ
      simp only [axialErrorFactor, (r.loop_periods_means z.2 (haK z.2 hz.2)).2.1 θ,
        hperA z.2 θ, hperBX z.2 θ])
  refine ⟨max CA CC, hCA.trans (le_max_left _ _), ?_⟩
  intro n hn p hpK
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hninv : 1 / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg zero_le_one hnpos.le, (div_le_one hnpos).mpr hn⟩
  have he := realized_shears_factor r E U ha hm hp₂ hE hU n hnpos.ne' p hpK
    (hX p hpK) (hE0 p hpK) (haNom p hpK) (hbNom p hpK)
  rw [he.1, he.2, abs_mul, abs_mul, abs_of_nonneg hninv.1]
  constructor
  · calc
      _ ≤ (1 / n) * CA := mul_le_mul_of_nonneg_left (hba p hpK _) hninv.1
      _ ≤ (1 / n) * max CA CC := mul_le_mul_of_nonneg_left (le_max_left _ _) hninv.1
      _ = _ := by ring
  · calc
      _ ≤ (1 / n) * CC := mul_le_mul_of_nonneg_left (hbc (1 / n, p) ⟨hninv, hpK⟩ _) hninv.1
      _ ≤ (1 / n) * max CA CC := mul_le_mul_of_nonneg_left (le_max_right _ _) hninv.1
      _ = _ := by ring

/-- The two stocks and two signed shears before conversion to `(P,J,v)`. -/
abbrev StockShearDatum := (ℝ × ℝ) × (ℝ × ℝ)

/-- Cone coordinates, given by `(z.1.1 + z.1.2 * (z.2.2 / z.2.1), z.1.2 - z.1.1 * (z.2.2 /
z.2.1), z.2.1 * (1 + (z.2.2 / z.2.1) ^ 2))`. -/
noncomputable def coneCoordinates (z : StockShearDatum) : UniformCone.ConeDatum :=
  (z.1.1 + z.1.2 * (z.2.2 / z.2.1),
    z.1.2 - z.1.1 * (z.2.2 / z.2.1),
    z.2.1 * (1 + (z.2.2 / z.2.1) ^ 2))

/-- Stock shear cone, given by `{z | TrueConeLoop.InTrueCone z.1.1 z.1.2 z.2.1 z.2.2}`. -/
noncomputable def stockShearCone : Set StockShearDatum :=
  {z | TrueConeLoop.InTrueCone z.1.1 z.1.2 z.2.1 z.2.2}

theorem coneCoordinates_continuousAt {z : StockShearDatum} (hz : z.2.1 ≠ 0) :
    ContinuousAt coneCoordinates z := by
  have ht : ContinuousAt (fun w : StockShearDatum => w.2.2 / w.2.1) z :=
    continuousAt_snd.snd.div continuousAt_snd.fst hz
  exact (continuousAt_fst.fst.add (continuousAt_fst.snd.mul ht)).prodMk
    ((continuousAt_fst.snd.sub (continuousAt_fst.fst.mul ht)).prodMk
      (continuousAt_snd.fst.mul (continuousAt_const.add (ht.pow 2))))

/-- Openness is inherited from the already verified exact root cone. -/
theorem isOpen_stockShearCone : IsOpen stockShearCone := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hpos : {w : StockShearDatum | 0 < w.2.1} ∈ 𝓝 z :=
    (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds hz.1
  have hc : {w : StockShearDatum | coneCoordinates w ∈ UniformCone.trueCone} ∈ 𝓝 z :=
    (coneCoordinates_continuousAt (ne_of_gt hz.1))
      (UniformCone.isOpen_trueCone.mem_nhds hz.2)
  exact Filter.inter_mem hpos hc

/-- A compact periodic loop has a single tolerance in the original four
coordinates, including stock errors and both shear errors. -/
theorem compact_periodic_stockShear_stable {X : Type*} [TopologicalSpace X]
    (p₁ p₂ : X → ℝ) (A C : X × ℝ → ℝ) {K : Set X} (hK : IsCompact K)
    (hp₁ : ContinuousOn p₁ K) (hp₂ : ContinuousOn p₂ K)
    (hA : ContinuousOn A (K ×ˢ (univ : Set ℝ)))
    (hC : ContinuousOn C (K ×ˢ (univ : Set ℝ)))
    (hAp : ∀ x ∈ K, Function.Periodic (fun θ => A (x, θ)) 1)
    (hCp : ∀ x ∈ K, Function.Periodic (fun θ => C (x, θ)) 1)
    (hcone : ∀ x ∈ K, ∀ θ, TrueConeLoop.InTrueCone (p₁ x) (p₂ x) (A (x, θ)) (C (x, θ))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ θ q₁ q₂ A' C' : ℝ,
      |q₁ - p₁ x| ≤ ρ → |q₂ - p₂ x| ≤ ρ →
      |A' - A (x, θ)| ≤ ρ → |C' - C (x, θ)| ≤ ρ →
      TrueConeLoop.InTrueCone q₁ q₂ A' C' := by
  let F : X × ℝ → StockShearDatum := fun z => ((p₁ z.1, p₂ z.1), (A z, C z))
  have hF : ContinuousOn F (K ×ˢ Icc (0 : ℝ) 1) :=
    ((hp₁.comp continuousOn_fst (fun _ hz => hz.1)).prodMk
      (hp₂.comp continuousOn_fst (fun _ hz => hz.1))).prodMk
        ((hA.mono (fun _ hz => ⟨hz.1, mem_univ _⟩)).prodMk
          (hC.mono (fun _ hz => ⟨hz.1, mem_univ _⟩)))
  have hcompact := (hK.prod isCompact_Icc).image_of_continuousOn hF
  have hsub : F '' (K ×ˢ Icc (0 : ℝ) 1) ⊆ stockShearCone := by
    rintro z ⟨w, hw, rfl⟩
    exact hcone w.1 hw.1 w.2
  obtain ⟨ρ, hρ, hthick⟩ := hcompact.exists_cthickening_subset_open isOpen_stockShearCone hsub
  refine ⟨ρ, hρ, ?_⟩
  intro x hx θ q₁ q₂ A' C' hq₁ hq₂ hA' hC'
  have hpair : Function.Periodic (fun φ => (A (x, φ), C (x, φ))) 1 := by
    intro φ
    exact Prod.ext (hAp x hx φ) (hCp x hx φ)
  obtain ⟨φ, hφ, heq⟩ := hpair.exists_mem_Ico₀ (by norm_num) θ
  have hAE : A (x, θ) = A (x, φ) := congrArg Prod.fst heq
  have hCE : C (x, θ) = C (x, φ) := congrArg Prod.snd heq
  have hmem : F (x, φ) ∈ F '' (K ×ˢ Icc (0 : ℝ) 1) :=
    mem_image_of_mem F ⟨hx, hφ.1, hφ.2.le⟩
  have hdist : dist ((q₁, q₂), (A', C')) (F (x, φ)) ≤ ρ := by
    simpa only [F, Prod.dist_eq, Real.dist_eq, ← hAE, ← hCE] using
      max_le (max_le hq₁ hq₂) (max_le hA' hC')
  exact hthick (Metric.mem_cthickening_of_dist_le ((q₁, q₂), (A', C'))
    (F (x, φ)) ρ (F '' (K ×ˢ Icc (0 : ℝ) 1)) hmem hdist)

/-- The tolerance is available for the actual loop selected from nominal
relaxed-cone data, without a true-cone assumption on those nominal shears. -/
theorem realized_loop_stable
    (r : TrueConeRealization a m p₁ p₂ K B) (hK : IsCompact K)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (haK : ∀ p ∈ K, 0 < a p)
    (hrelaxed : ∀ p ∈ K, TrueConeLoop.nominalSpeed (a p) (m p) <
      ConeAlgebra.coneBound (p₁ p + p₂ p * m p) (p₂ p - p₁ p * m p)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p ∈ K, ∀ θ q₁ q₂ A' C' : ℝ,
      |q₁ - p₁ p| ≤ ρ → |q₂ - p₂ p| ≤ ρ →
      |A' - r.angularLoop (p, θ)| ≤ ρ →
      |C' - r.signedAxialLoop (p, θ)| ≤ ρ →
      TrueConeLoop.InTrueCone q₁ q₂ A' C' := by
  have hs := r.loop_smooth ha hm hp₂
  exact compact_periodic_stockShear_stable p₁ p₂ r.angularLoop r.signedAxialLoop hK
    hp₁.continuous.continuousOn hp₂.continuous.continuousOn
    (hs.1.continuousOn.mono (fun z hz => ⟨haK z.1 hz.1, hz.2⟩))
    (hs.2.continuousOn.mono (fun z hz => ⟨haK z.1 hz.1, hz.2⟩))
    (fun p hp => (r.loop_periods_means p (haK p hp)).1)
    (fun p hp => (r.loop_periods_means p (haK p hp)).2.1)
    (r.loop_trueCone hrelaxed)

/-- One finite integer controls every later frequency. -/
theorem exists_integer_frequency (C ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ (n : ℝ) ∧ C / (n : ℝ) ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (C / ε))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNC : C < (N : ℝ) * ε := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hN)
  refine ⟨N, by exact_mod_cast (lt_trans zero_lt_one hN1), ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := hN1.le.trans hNn
  refine ⟨hn1, (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hn1)).mpr ?_⟩
  nlinarith

/-- Interface for combining the derived shear bound with derived stock
estimates. The actual history construction supplies `hstock` below. -/
theorem realized_trueCone_of_stock_bound
    (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (hK : IsCompact K)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (haK : ∀ p ∈ K, 0 < a p) (hX : ∀ p ∈ K, p.1 ≠ 0)
    (hE0 : ∀ p ∈ K, E p ≠ 0)
    (haNom : ∀ p ∈ K, a p = angularShear E p)
    (hbNom : ∀ p ∈ K, a p * m p = signedAxialShear E U p)
    (hrelaxed : ∀ p ∈ K, TrueConeLoop.nominalSpeed (a p) (m p) <
      ConeAlgebra.coneBound (p₁ p + p₂ p * m p) (p₂ p - p₁ p * m p))
    (q₁ q₂ : ℝ → RadialParameter → ℝ) (Cstock : ℝ)
    (hstock : ∀ n : ℝ, 1 ≤ n → ∀ p ∈ K,
      |q₁ n p - p₁ p| ≤ Cstock / n ∧ |q₂ n p - p₂ p| ≤ Cstock / n) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ p ∈ K,
      TrueConeLoop.InTrueCone (q₁ n p) (q₂ n p)
        (angularShear (fun q => realizedE r E n q.1 q.2) p)
        (signedAxialShear (fun q => realizedE r E n q.1 q.2)
          (fun q => realizedU r E U n q.1 q.2) p) := by
  obtain ⟨Cshear, _, hshear⟩ := realized_shears_uniform_bound r E U hK
    ha hm hp₂ hE hU haK hX hE0 haNom hbNom
  obtain ⟨ρ, hρ, hstable⟩ := realized_loop_stable r hK ha hm hp₁ hp₂ haK hrelaxed
  obtain ⟨N, hN, hlarge⟩ := exists_integer_frequency (max Cstock Cshear) ρ hρ
  refine ⟨N, hN, ?_⟩
  intro n hn p hp
  obtain ⟨hn1, hsmall⟩ := hlarge n hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hs := hstock n hn1 p hp
  have hv := hshear n hn1 p hp
  have hCs : Cstock / n ≤ ρ :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hn0).trans hsmall
  have hCv : Cshear / n ≤ ρ :=
    (div_le_div_of_nonneg_right (le_max_right _ _) hn0).trans hsmall
  exact hstable p hp (n * Real.log p.1) _ _ _ _
    (hs.1.trans hCs) (hs.2.trans hCs) (hv.1.trans hCv) (hv.2.trans hCv)

/-- Quotient perturbations controlled by a common positive denominator. -/
theorem quotient_perturbation_bound {μ M ε x y e f : ℝ}
    (hμ : 0 < μ) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (he : μ ≤ e) (hf : μ ≤ f) (hx : |x| ≤ M)
    (hxy : |y - x| ≤ ε) (hef : |f - e| ≤ ε) :
    |y / f - x / e| ≤ (1 / μ + M / (μ * μ)) * ε := by
  have he0 : 0 < e := hμ.trans_le he
  have hf0 : 0 < f := hμ.trans_le hf
  have hid : y / f - x / e = (y - x) / f + x * (e - f) / (f * e) := by
    field_simp; ring
  have hef' : |e - f| ≤ ε := by rwa [abs_sub_comm]
  have hden : μ * μ ≤ f * e := mul_le_mul hf he hμ.le hf0.le
  calc
    _ ≤ |(y - x) / f| + |x * (e - f) / (f * e)| := by rw [hid]; exact abs_add_le _ _
    _ = |y - x| / f + |x| * |e - f| / (f * e) := by
      simp only [abs_div, abs_mul, abs_of_pos he0, abs_of_pos hf0]
    _ ≤ ε / μ + (M * ε) / (μ * μ) := by
      exact add_le_add (div_le_div₀ hε hxy hμ hf)
        (div_le_div₀ (mul_nonneg hM hε) (mul_le_mul hx hef' (abs_nonneg _) hM)
          (mul_pos hμ hμ) hden)
    _ = _ := by ring

/-- A small edit in field value and first radial derivatives produces a
small edit in both genuine shear quotients. -/
theorem shear_perturbation_bound {μ R M ε X E₀ E₁ EX₀ EX₁ UX₀ UX₁ : ℝ}
    (hμ : 0 < μ) (hR : 0 ≤ R) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hE₀ : μ ≤ E₀) (hE₁ : μ ≤ E₁) (hX : |X| ≤ R)
    (hEX : |EX₀| ≤ M) (hUX : |UX₀| ≤ M)
    (hEedit : |E₁ - E₀| ≤ ε) (hEXedit : |EX₁ - EX₀| ≤ ε)
    (hUXedit : |UX₁ - UX₀| ≤ ε) :
    |(1 - 2 * X * EX₁ / E₁) - (1 - 2 * X * EX₀ / E₀)| ≤
      (2 * R * (1 / μ + M / (μ * μ))) * ε ∧
    |-(2 * X * UX₁ / E₁) - -(2 * X * UX₀ / E₀)| ≤
      (2 * R * (1 / μ + M / (μ * μ))) * ε := by
  have hcommon : 0 ≤ (1 / μ + M / (μ * μ)) * ε := by positivity
  have hquotA := quotient_perturbation_bound hμ hM hε hE₀ hE₁ hEX hEXedit hEedit
  have hquotC := quotient_perturbation_bound hμ hM hε hE₀ hE₁ hUX hUXedit hEedit
  have hrad : |-(2 * X)| ≤ 2 * R := by
    simpa only [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 2)
  constructor
  · have hid : (1 - 2 * X * EX₁ / E₁) - (1 - 2 * X * EX₀ / E₀) =
        -(2 * X) * (EX₁ / E₁ - EX₀ / E₀) := by ring
    rw [hid, abs_mul]
    calc
      _ ≤ (2 * R) * ((1 / μ + M / (μ * μ)) * ε) :=
        mul_le_mul hrad hquotA (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · have hid : -(2 * X * UX₁ / E₁) - -(2 * X * UX₀ / E₀) =
        -(2 * X) * (UX₁ / E₁ - UX₀ / E₀) := by ring
    rw [hid, abs_mul]
    calc
      _ ≤ (2 * R) * ((1 / μ + M / (μ * μ)) * ε) :=
        mul_le_mul hrad hquotC (abs_nonneg _) (by positivity)
      _ = _ := by ring

/-- Equality on an open collar includes equality of the actual shears. -/
theorem shears_eq_on_open {E U F V : RadialParameter → ℝ} {O : Set RadialParameter}
    (hO : IsOpen O) (hE : EqOn E F O) (hU : EqOn U V O)
    {p : RadialParameter} (hp : p ∈ O) :
    angularShear E p = angularShear F p ∧
      signedAxialShear E U p = signedAxialShear F V p := by
  have hnear : ∀ᶠ X in 𝓝 p.1, (X, p.2) ∈ O :=
    (continuousAt_id.prodMk continuousAt_const) (hO.mem_nhds hp)
  have hED : deriv (fun X => E (X, p.2)) p.1 = deriv (fun X => F (X, p.2)) p.1 :=
    Filter.EventuallyEq.deriv_eq (hnear.mono (fun X hX => hE hX))
  have hUD : deriv (fun X => U (X, p.2)) p.1 = deriv (fun X => V (X, p.2)) p.1 :=
    Filter.EventuallyEq.deriv_eq (hnear.mono (fun X hX => hU hX))
  simp only [angularShear, signedAxialShear, hED, hUD, hE hp, and_self]

/-- The genuine derivative with the parameter held fixed. -/
noncomputable def radialDerivative (E : RadialParameter → ℝ) (p : RadialParameter) : ℝ :=
  deriv (fun X => E (X, p.2)) p.1

theorem radialDerivative_smooth (E : RadialParameter → ℝ) (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (radialDerivative E) := by
  have heq : radialDerivative E = fun p => fderiv ℝ E p (1, 0) := by
    funext p
    exact ((hE.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv
  rw [heq]
  exact (hE.fderiv_right (by simp)).clm_apply contDiff_const

/-- Compact smooth positive nominal fields have a uniform `C¹`-to-shear
estimate. The positive denominator after the edit is a conclusion. -/
theorem compact_shear_perturbation
    (E U : RadialParameter → ℝ) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    {S : Set RadialParameter} (hS : IsCompact S) (hpos : ∀ p ∈ S, 0 < E p) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ (F V : RadialParameter → ℝ) (ε : ℝ),
      0 ≤ ε → ε ≤ δ →
      (∀ p ∈ S, |F p - E p| ≤ ε ∧
        |radialDerivative F p - radialDerivative E p| ≤ ε ∧
        |radialDerivative V p - radialDerivative U p| ≤ ε) →
      ∀ p ∈ S, δ ≤ F p ∧
        |angularShear F p - angularShear E p| ≤ C * ε ∧
        |signedAxialShear F V p - signedAxialShear E U p| ≤ C * ε := by
  obtain ⟨e, he, hmin⟩ := UniformCone.positive_uniform_margin hS hE.continuous.continuousOn hpos
  obtain ⟨R₀, hR₀⟩ := hS.exists_bound_of_continuousOn
    (continuous_fst.continuousOn : ContinuousOn (fun p : RadialParameter => p.1) S)
  obtain ⟨ME, hME⟩ := hS.exists_bound_of_continuousOn
    (radialDerivative_smooth E hE).continuous.continuousOn
  obtain ⟨MU, hMU⟩ := hS.exists_bound_of_continuousOn
    (radialDerivative_smooth U hU).continuous.continuousOn
  let R := max R₀ 0
  let M := max (max ME MU) 0
  let δ := e / 2
  let C := 2 * R * (1 / δ + M / (δ * δ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hR : 0 ≤ R := le_max_right _ _
  have hM : 0 ≤ M := le_max_right _ _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro F V ε hε hεδ hdata p hp
  obtain ⟨hedit, hEedit, hUedit⟩ := hdata p hp
  have hnom : δ ≤ E p := by have := hmin p hp; dsimp [δ]; linarith
  have hnew : δ ≤ F p := by
    have := hmin p hp
    have := (abs_le.mp hedit).1
    dsimp [δ] at *
    linarith
  have hrad : |p.1| ≤ R := (hR₀ p hp).trans (le_max_left _ _)
  have hEd : |radialDerivative E p| ≤ M :=
    (hME p hp).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hUd : |radialDerivative U p| ≤ M :=
    (hMU p hp).trans ((le_max_right _ _).trans (le_max_left _ _))
  exact ⟨hnew, shear_perturbation_bound hδ hR hM hε hnom hnew hrad hEd hUd
    hedit hEedit hUedit⟩

/-- The primitive construction preserves a single open collar for the
values and the genuine radial shears, at every frequency. -/
theorem realized_profiles_boundary_shears
    (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hBK : B ⊆ K) :
    ∃ O : Set RadialParameter, IsOpen O ∧ B ⊆ O ∧ ∀ n : ℝ, ∀ p ∈ O,
      realizedE r E n p.1 p.2 = E p ∧ realizedU r E U n p.1 p.2 = U p ∧
      angularShear (fun q => realizedE r E n q.1 q.2) p = angularShear E p ∧
      signedAxialShear (fun q => realizedE r E n q.1 q.2)
        (fun q => realizedU r E U n q.1 q.2) p = signedAxialShear E U p := by
  obtain ⟨O, hO, hBO, heq⟩ := realized_profiles_boundary_match r E U ha hm hBK
  refine ⟨O, hO, hBO, ?_⟩
  intro n p hp
  exact ⟨(heq n p.1 p.2 hp).1, (heq n p.1 p.2 hp).2,
    shears_eq_on_open hO (fun q hq => (heq n q.1 q.2 hq).1)
      (fun q hq => (heq n q.1 q.2 hq).2) hp⟩

/-- Local agreement along the radial variable suffices for exact shear agreement. -/
theorem shears_eq_of_radial_eventuallyEq
    {E U F V : RadialParameter → ℝ} {p : RadialParameter}
    (hE : (fun X => E (X, p.2)) =ᶠ[𝓝 p.1] (fun X => F (X, p.2)))
    (hU : (fun X => U (X, p.2)) =ᶠ[𝓝 p.1] (fun X => V (X, p.2))) :
    angularShear E p = angularShear F p ∧
      signedAxialShear E U p = signedAxialShear F V p := by
  have hval : E p = F p := hE.eq_of_nhds
  simp only [angularShear, signedAxialShear, hE.deriv_eq, hU.deriv_eq, hval, and_self]

/-- The same four-coordinate tolerance applies to an ordinary compact
nominal true-cone patch (the constant periodic-loop case). -/
theorem nominal_stockShear_stable
    (a m p₁ p₂ : RadialParameter → ℝ) {S : Set RadialParameter} (hS : IsCompact S)
    (ha : ContinuousOn a S) (hm : ContinuousOn m S)
    (hp₁ : ContinuousOn p₁ S) (hp₂ : ContinuousOn p₂ S)
    (hcone : ∀ p ∈ S, TrueConeLoop.InTrueCone (p₁ p) (p₂ p) (a p) (a p * m p)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p ∈ S, ∀ q₁ q₂ A' C' : ℝ,
      |q₁ - p₁ p| ≤ ρ → |q₂ - p₂ p| ≤ ρ → |A' - a p| ≤ ρ → |C' - a p * m p| ≤ ρ →
      TrueConeLoop.InTrueCone q₁ q₂ A' C' := by
  have ha' : ContinuousOn (fun z : RadialParameter × ℝ => a z.1) (S ×ˢ (univ : Set ℝ)) :=
    ha.comp continuousOn_fst (fun _ hz => hz.1)
  have hm' : ContinuousOn (fun z : RadialParameter × ℝ => m z.1) (S ×ˢ (univ : Set ℝ)) :=
    hm.comp continuousOn_fst (fun _ hz => hz.1)
  obtain ⟨ρ, hρ, hstable⟩ := compact_periodic_stockShear_stable p₁ p₂
    (fun z => a z.1) (fun z => a z.1 * m z.1) hS hp₁ hp₂ ha' (ha'.mul hm')
      (by intro p _ θ; rfl) (by intro p _ θ; rfl) (fun p hp _ => hcone p hp)
  exact ⟨ρ, hρ, fun p hp q₁ q₂ A' C' => hstable p hp 0 q₁ q₂ A' C'⟩

/-- Composition interface for the actual following repair. The modulation
region uses its derived shear estimate, while a nominal true-cone patch uses
the derived `C¹` perturbation estimate. Later the actual history and moment
construction supplies the stock/edit bounds and the local equality premise. -/
theorem repaired_trueCone_of_bounds
    (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (hK : IsCompact K)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (haK : ∀ p ∈ K, 0 < a p) (hX : ∀ p ∈ K, p.1 ≠ 0)
    (hE0 : ∀ p ∈ K, E p ≠ 0)
    (haNom : ∀ p ∈ K, a p = angularShear E p)
    (hbNom : ∀ p ∈ K, a p * m p = signedAxialShear E U p)
    (hrelaxed : ∀ p ∈ K, TrueConeLoop.nominalSpeed (a p) (m p) <
      ConeAlgebra.coneBound (p₁ p + p₂ p * m p) (p₂ p - p₁ p * m p))
    (S : Set RadialParameter) (hS : IsCompact S) (hSpos : ∀ p ∈ S, 0 < E p)
    (haS : ∀ p ∈ S, a p = angularShear E p)
    (hbS : ∀ p ∈ S, a p * m p = signedAxialShear E U p)
    (hScone : ∀ p ∈ S, TrueConeLoop.InTrueCone (p₁ p) (p₂ p) (a p) (a p * m p))
    (F V q₁ q₂ : ℕ → RadialParameter → ℝ) (n₀ : ℕ) (Cstock Cedit : ℝ) (hCedit : 0 ≤ Cedit)
    (hstock : ∀ n : ℕ, n₀ ≤ n → 1 ≤ (n : ℝ) → ∀ p ∈ K ∪ S,
      |q₁ n p - p₁ p| ≤ Cstock / n ∧ |q₂ n p - p₂ p| ≤ Cstock / n)
    (hedit : ∀ n : ℕ, n₀ ≤ n → 1 ≤ (n : ℝ) → ∀ p ∈ S,
      |F n p - E p| ≤ Cedit / n ∧
      |radialDerivative (F n) p - radialDerivative E p| ≤ Cedit / n ∧
      |radialDerivative (V n) p - radialDerivative U p| ≤ Cedit / n)
    (hlocal : ∀ n : ℕ, n₀ ≤ n → ∀ p ∈ K,
      ((fun X => F n (X, p.2)) =ᶠ[𝓝 p.1] (fun X => realizedE r E n X p.2)) ∧
      ((fun X => V n (X, p.2)) =ᶠ[𝓝 p.1] (fun X => realizedU r E U n X p.2))) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ p ∈ K ∪ S,
      TrueConeLoop.InTrueCone (q₁ n p) (q₂ n p)
        (angularShear (F n) p) (signedAxialShear (F n) (V n) p) := by
  obtain ⟨Cshear, _, hshear⟩ := realized_shears_uniform_bound r E U hK
    ha hm hp₂ hE hU haK hX hE0 haNom hbNom
  obtain ⟨ρK, hρK, hstableK⟩ := realized_loop_stable r hK ha hm hp₁ hp₂ haK hrelaxed
  obtain ⟨ρS, hρS, hstableS⟩ := nominal_stockShear_stable a m p₁ p₂ hS
    ha.continuous.continuousOn hm.continuous.continuousOn
    hp₁.continuous.continuousOn hp₂.continuous.continuousOn hScone
  obtain ⟨δ, D, hδ, _, hC1⟩ := compact_shear_perturbation E U hE hU hS hSpos
  let C := max Cstock (max Cshear (D * Cedit))
  obtain ⟨Ncone, hNcone, hlarge⟩ := exists_integer_frequency C (min ρK ρS) (lt_min hρK hρS)
  obtain ⟨Nedit, _, hlargeEdit⟩ := exists_integer_frequency Cedit δ hδ
  refine ⟨max n₀ (max Ncone Nedit), hNcone.trans_le
    ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro n hn p hp
  have hn₀ : n₀ ≤ n := (le_max_left _ _).trans hn
  have hncone : Ncone ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnedit : Nedit ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  obtain ⟨hn1, hsmall⟩ := hlarge n hncone
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hbound : ∀ c : ℝ, c ≤ C → c / (n : ℝ) ≤ min ρK ρS := by
    intro c hc
    exact (div_le_div_of_nonneg_right hc hnpos.le).trans hsmall
  obtain ⟨hq₁, hq₂⟩ := hstock n hn₀ hn1 p hp
  have hstockSmall : Cstock / (n : ℝ) ≤ min ρK ρS := hbound Cstock (le_max_left _ _)
  rcases hp with hpK | hpS
  · have heq := shears_eq_of_radial_eventuallyEq (p := p) (E := F n) (U := V n)
      (F := fun q => realizedE r E n q.1 q.2) (V := fun q => realizedU r E U n q.1 q.2)
      (hlocal n hn₀ p hpK).1 (hlocal n hn₀ p hpK).2
    obtain ⟨hA, hC⟩ := hshear n hn1 p hpK
    have hs : Cshear / (n : ℝ) ≤ ρK :=
      (hbound Cshear ((le_max_left _ _).trans (le_max_right _ _))).trans (min_le_left _ _)
    rw [heq.1, heq.2]
    exact hstableK p hpK (n * Real.log p.1) _ _ _ _
      ((hq₁.trans hstockSmall).trans (min_le_left _ _))
      ((hq₂.trans hstockSmall).trans (min_le_left _ _)) (hA.trans hs) (hC.trans hs)
  · have hC1p := hC1 (F n) (V n) (Cedit / n) (div_nonneg hCedit hnpos.le)
      (hlargeEdit n hnedit).2 (hedit n hn₀ hn1) p hpS
    have hs : D * (Cedit / (n : ℝ)) ≤ ρS := by
      rw [← mul_div_assoc]
      exact (hbound (D * Cedit) ((le_max_right _ _).trans (le_max_right _ _))).trans
        (min_le_right _ _)
    apply hstableS p hpS _ _ _ _
      ((hq₁.trans hstockSmall).trans (min_le_right _ _))
      ((hq₂.trans hstockSmall).trans (min_le_right _ _))
    · rw [haS p hpS]
      exact hC1p.2.1.trans hs
    · rw [hbS p hpS]
      exact hC1p.2.2.trans hs

namespace Localized

open ProfileHistories StressActivation

/-- History index as an element of `HistoryRow → Fin 5 | .mass => 0 | .angular => 1 | .transport
=> 2 | .energy => 3 | .pressure => 4`. -/
noncomputable def historyIndex : HistoryRow → Fin 5
  | .mass => 0
  | .angular => 1
  | .transport => 2
  | .energy => 3
  | .pressure => 4

theorem profileHistory_eq_row {D : RadialDomain} (P : Profiles D)
    (row : HistoryRow) (p : Point) :
    profileHistory P row p = ModulatedHistories.profileRows P p (historyIndex row) := by
  cases row <;> rfl

/-- Localization preserves the uniform field-value estimate, including at
all points outside the modulation window. -/
theorem fields_uniform_bound (W : ModulatedHistories.Window)
    (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (J : Set ℝ) (hJ : IsCompact J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℝ, 1 ≤ n → ∀ X : ℝ, ∀ η ∈ J,
      |ModulatedHistories.localizedF W r f n (X, η) - f (X, η)| ≤ C / n ∧
      |ModulatedHistories.localizedU W r E U n (X, η) - U (X, η)| ≤ C / n := by
  obtain ⟨Cf, _, hCf, _, hbf⟩ := realized_profiles_uniform_eta_jets r f U ha hm hp₂ hf hU
    (Icc W.left W.right) J isCompact_Icc hJ 0
  obtain ⟨_, Cu, _, hCu, hbu⟩ := realized_profiles_uniform_eta_jets r E U ha hm hp₂ hE hU
    (Icc W.left W.right) J isCompact_Icc hJ 0
  refine ⟨max Cf Cu, hCf.trans (le_max_left _ _), ?_⟩
  intro n hn X η hη
  have hn0 : 0 ≤ n := le_trans zero_le_one hn
  by_cases hX : X ∈ Ioc W.left W.right
  · have hX' : X ∈ Icc W.left W.right := ⟨hX.1.le, hX.2⟩
    have hf' := (hbf n hn X hX' η hη).1
    have hu' := (hbu n hn X hX' η hη).2
    simp only [iteratedDeriv_zero] at hf' hu'
    simpa only [ModulatedHistories.localizedF, ModulatedHistories.localizedU,
      ModulatedHistories.splice, ite_eq_left hX, ModulatedHistories.rawF, ModulatedHistories.rawU]
          using
      And.intro (hf'.trans (div_le_div_of_nonneg_right (le_max_left _ _) hn0))
        (hu'.trans (div_le_div_of_nonneg_right (le_max_right _ _) hn0))
  · simp only [ModulatedHistories.localizedF, ModulatedHistories.localizedU,
      ModulatedHistories.splice, ite_eq_right hX, sub_self, abs_zero, and_self]
    exact div_nonneg (hCf.trans (le_max_left _ _)) hn0

/-- Each actual localized profile history has the constructed integral
difference; the pressure constant is retained exactly. -/
theorem profileHistory_difference {D D' : RadialDomain}
    (W : ModulatedHistories.Window) (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (n : ℝ) (P : Profiles D) (Q : Profiles D')
    (hPf : P.f = ModulatedHistories.localizedF W r f n)
    (hPU : P.U = ModulatedHistories.localizedU W r E U n)
    (hQf : Q.f = f) (hQU : Q.U = U) (hP0 : P.pressure0 = Q.pressure0)
    (row : HistoryRow) (p : Point) (hX : 0 ≤ p.1) :
    profileHistory P row p - profileHistory Q row p =
      ModulatedHistories.historyDifference W r f E U n p.1 p.2 (historyIndex row) := by
  rw [profileHistory_eq_row, profileHistory_eq_row]
  change (ModulatedHistories.profileRows P p - ModulatedHistories.profileRows Q p) (historyIndex
      row) = _
  rw [ModulatedHistories.profileRows_sub P Q hP0, hPf, hPU, hQf, hQU,
    ModulatedHistories.axisHistory_localized_sub W r f E U ha hm hp₂ hf hE hU n p.1 p.2 hX]

/-- Actual localized history values and their first parameter derivatives
have one frequency-independent `C/n` bound. -/
theorem profileHistory_uniform_bound {D D' : RadialDomain}
    (W : ModulatedHistories.Window) (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (P : ℝ → Profiles D) (Q : Profiles D')
    (hPf : ∀ n, (P n).f = ModulatedHistories.localizedF W r f n)
    (hPU : ∀ n, (P n).U = ModulatedHistories.localizedU W r E U n)
    (hQf : Q.f = f) (hQU : Q.U = U) (hP0 : ∀ n, (P n).pressure0 = Q.pressure0)
    (J : Set ℝ) (hJ : IsCompact J) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℝ, 1 ≤ n → ∀ p : Point, 0 ≤ p.1 → p.2 ∈ J →
      p ∈ D.carrier → p ∈ D'.carrier → ∀ row : HistoryRow,
      |profileHistory (P n) row p - profileHistory Q row p| ≤ C / n ∧
      |parameterPartial (profileHistory (P n) row) p - parameterPartial (profileHistory Q row) p| ≤
          C / n := by
  obtain ⟨C, hC, hb⟩ := ModulatedHistories.historyDifference_scalar_jets
    W r f E U ha hm hp₂ hf hE hU J hJ 1
  refine ⟨C, hC, ?_⟩
  intro n hn p hX hη hp hp' row
  have heq (η : ℝ) := profileHistory_difference W r f E U ha hm hp₂ hf hE hU n (P n) Q
    (hPf n) (hPU n) hQf hQU (hP0 n) row (p.1, η) hX
  have heqfun : (fun η => profileHistory (P n) row (p.1, η) - profileHistory Q row (p.1, η)) =
      (fun η => ModulatedHistories.historyDifference W r f E U n p.1 η (historyIndex row)) :=
    funext heq
  have hd := ((parameterPartial_hasDerivAt D (profileHistory_smooth (P n) row) hp).fun_sub
    (parameterPartial_hasDerivAt D' (profileHistory_smooth Q row) hp')).deriv
  rw [heqfun] at hd
  constructor
  · rw [heq p.2]
    simpa only [iteratedDeriv_zero] using hb n hn p.1 p.2 hη 0 (by omega) (historyIndex row)
  · simpa only [iteratedDeriv_one, hd] using hb n hn p.1 p.2 hη 1 le_rfl (historyIndex row)

/-- The actual stocks of the localized modulation have a uniform `C/n`
bound, derived from its actual axis-integrated histories. -/
theorem profile_stocks_rate {D D' : RadialDomain}
    (W : ModulatedHistories.Window) (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (P : ℝ → Profiles D) (Q : Profiles D')
    (hPf : ∀ n, (P n).f = ModulatedHistories.localizedF W r f n)
    (hPU : ∀ n, (P n).U = ModulatedHistories.localizedU W r E U n)
    (hQf : Q.f = f) (hQU : Q.U = U) (hP0 : ∀ n, (P n).pressure0 = Q.pressure0)
    (J : Set ℝ) (hJ : IsCompact J) (T : Set Point) (hT : IsCompact T)
    (hTJ : ∀ p ∈ T, p.2 ∈ J) (hTD : T ⊆ D.carrier) (hTD' : T ⊆ D'.carrier)
    (h : ℝ) (hX : ∀ p ∈ T, 0 < p.1) (hL : ∀ p ∈ T, NaturalAxisData.L h p.2 ≠ 0)
    (hpos : ∀ p ∈ T, 0 < Q.f p) :
    ∃ N : ℕ, ∃ C : ℝ, 0 < N ∧ 0 ≤ C ∧ ∀ n : ℝ, (N : ℝ) ≤ n → ∀ p ∈ T,
      0 < (P n).f p ∧
      |ActivationStocks.profileStockOne (P n) h p - ActivationStocks.profileStockOne Q h p| ≤ C / n
          ∧
      |ActivationStocks.profileStockTwo (P n) h p - ActivationStocks.profileStockTwo Q h p| ≤ C / n
          := by
  obtain ⟨Cf, hCf, hfb⟩ := fields_uniform_bound W r f E U ha hm hp₂ hf hE hU J hJ
  obtain ⟨CH, hCH, hHb⟩ := profileHistory_uniform_bound W r f E U ha hm hp₂ hf hE hU P Q
    hPf hPU hQf hQU hP0 J hJ
  apply ModulatedStockBounds.profile_stocks_rate Q h P hT hTD' hTD hX hL hpos 1 (max Cf CH)
    (hCf.trans (le_max_left _ _))
  intro n _ hn p hp
  have hn0 : 0 ≤ n := le_trans zero_le_one hn
  have hfbound : Cf / n ≤ max Cf CH / n := div_le_div_of_nonneg_right (le_max_left _ _) hn0
  have hHbound : CH / n ≤ max Cf CH / n := div_le_div_of_nonneg_right (le_max_right _ _) hn0
  obtain ⟨hfv, hUv⟩ := hfb n hn p.1 p.2 (hTJ p hp)
  refine ⟨?_, ?_, ?_⟩
  · rw [hPf n, hQf]
    exact hfv.trans hfbound
  · rw [hPU n, hQU]
    exact hUv.trans hfbound
  · intro row
    have hb := hHb n hn p (hX p hp).le (hTJ p hp) (hTD hp) (hTD' hp) row
    exact ⟨hb.1.trans hHbound, hb.2.trans hHbound⟩

theorem splice_eventuallyEq (W : ModulatedHistories.Window) (base actual : Field)
    {p : Point} (hp : p.1 ∈ Icc W.left W.right)
    (hleft : p.1 = W.left → actual =ᶠ[𝓝 p] base)
    (hright : p.1 = W.right → actual =ᶠ[𝓝 p] base) :
    ModulatedHistories.splice W base actual =ᶠ[𝓝 p] actual := by
  by_cases hl : p.1 = W.left
  · filter_upwards [hleft hl] with q hq
    exact (ModulatedHistories.splice_eq_of_eq W hq).trans hq.symm
  by_cases hr : p.1 = W.right
  · filter_upwards [hright hr] with q hq
    exact (ModulatedHistories.splice_eq_of_eq W hq).trans hq.symm
  have hint : p.1 ∈ Ioo W.left W.right :=
    ⟨lt_of_le_of_ne hp.1 (Ne.symm hl), lt_of_le_of_ne hp.2 hr⟩
  filter_upwards [(isOpen_Ioo.preimage continuous_fst).mem_nhds hint] with q hq
  exact ite_eq_left ⟨hq.1, hq.2.le⟩

/-- The endpoint collars make the localized functions locally equal to
the raw modulated functions even at both endpoints of the closed window. -/
theorem raw_agreement (W : ModulatedHistories.Window)
    (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hBK : B ⊆ K)
    (J : Set ℝ) (hends : ∀ η ∈ J, (W.left, η) ∈ B ∧ (W.right, η) ∈ B)
    (n : ℝ) {p : Point} (hp : p.1 ∈ Icc W.left W.right) (hη : p.2 ∈ J) :
    (ModulatedHistories.localizedF W r f n =ᶠ[𝓝 p] ModulatedHistories.rawF r f n) ∧
      (ModulatedHistories.localizedU W r E U n =ᶠ[𝓝 p] ModulatedHistories.rawU r E U n) := by
  obtain ⟨V, hV, hBV, hz⟩ := r.boundary_vanishing E ha hm hBK
  have hraw : ∀ q ∈ V, ModulatedHistories.rawF r f n q = f q ∧
      ModulatedHistories.rawU r E U n q = U q := by
    intro q hq
    have hzero := hz q hq (n * Real.log q.1)
    simp only [ModulatedHistories.rawF, ModulatedHistories.rawU, realizedE, realizedU,
      RadialModulation.modulatedE, RadialModulation.modulatedU, RadialModulation.phasePoint,
      asRadialPrimitive, Prod.eta, hzero.1, hzero.2, zero_div, Real.exp_zero,
      mul_one, add_zero, and_self]
  have hnear : p.1 = W.left ∨ p.1 = W.right →
      (ModulatedHistories.rawF r f n =ᶠ[𝓝 p] f) ∧
      (ModulatedHistories.rawU r E U n =ᶠ[𝓝 p] U) := by
    intro hend
    have hpB : p ∈ B := by
      rcases hend with hl | hr
      · simpa only [← hl, Prod.eta] using (hends p.2 hη).1
      · simpa only [← hr, Prod.eta] using (hends p.2 hη).2
    have hb : ∀ᶠ q in 𝓝 p, ModulatedHistories.rawF r f n q = f q ∧
        ModulatedHistories.rawU r E U n q = U q := by
      filter_upwards [hV.mem_nhds (hBV hpB)] with q hq
      exact hraw q hq
    exact ⟨hb.mono (fun _ h => h.1), hb.mono (fun _ h => h.2)⟩
  exact ⟨splice_eventuallyEq W f (ModulatedHistories.rawF r f n) hp
      (fun hl => (hnear (Or.inl hl)).1) (fun hr => (hnear (Or.inr hr)).1),
    splice_eventuallyEq W U (ModulatedHistories.rawU r E U n) hp
      (fun hl => (hnear (Or.inl hl)).2) (fun hr => (hnear (Or.inr hr)).2)⟩

/-- The actual localized physical fields agree locally with the raw
realized fields, including at the boundary collars. -/
theorem physical_profile_germs {D : RadialDomain} (W : ModulatedHistories.Window)
    (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hBK : B ⊆ K)
    (J : Set ℝ) (hends : ∀ η ∈ J, (W.left, η) ∈ B ∧ (W.right, η) ∈ B)
    (n : ℝ) (P : Profiles D)
    (hPf : P.f = ModulatedHistories.localizedF W r f n)
    (hPU : P.U = ModulatedHistories.localizedU W r E U n)
    {p : Point} (hp : p.1 ∈ Icc W.left W.right) (hη : p.2 ∈ J)
    (hphys : E =ᶠ[𝓝 p] fun q => Real.sqrt (2 * q.1) * f q) :
    (P.E =ᶠ[𝓝 p] fun q => realizedE r E n q.1 q.2) ∧
      (P.U =ᶠ[𝓝 p] fun q => realizedU r E U n q.1 q.2) := by
  have hraw := raw_agreement W r f E U ha hm hBK J hends n hp hη
  have hEj : P.E =ᶠ[𝓝 p] fun q => realizedE r E n q.1 q.2 := by
    filter_upwards [hraw.1, hphys] with q hq hEq
    change Real.sqrt (2 * q.1) * P.f q = _
    rw [hPf, hq]
    exact ModulatedHistories.rawF_physical r f E n q.1 q.2 hEq
  have hUj : P.U =ᶠ[𝓝 p] fun q => realizedU r E U n q.1 q.2 := by
    rw [hPU]
    exact hraw.2
  exact ⟨hEj, hUj⟩

/-- Both shears of the actual localized physical profiles equal the
already estimated realized shears, including at the boundary collars. -/
theorem physical_shears_match {D : RadialDomain} (W : ModulatedHistories.Window)
    (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hBK : B ⊆ K)
    (J : Set ℝ) (hends : ∀ η ∈ J, (W.left, η) ∈ B ∧ (W.right, η) ∈ B)
    (n : ℝ) (P : Profiles D)
    (hPf : P.f = ModulatedHistories.localizedF W r f n)
    (hPU : P.U = ModulatedHistories.localizedU W r E U n)
    {p : Point} (hp : p.1 ∈ Icc W.left W.right) (hη : p.2 ∈ J)
    (hphys : E =ᶠ[𝓝 p] fun q => Real.sqrt (2 * q.1) * f q) :
    angularShear P.E p = angularShear (fun q => realizedE r E n q.1 q.2) p ∧
      signedAxialShear P.E P.U p = signedAxialShear (fun q => realizedE r E n q.1 q.2)
        (fun q => realizedU r E U n q.1 q.2) p := by
  obtain ⟨hEj, hUj⟩ := physical_profile_germs W r f E U ha hm hBK J hends n P hPf hPU hp hη hphys
  have hrad : Filter.Tendsto (fun X : ℝ => (X, p.2)) (𝓝 p.1) (𝓝 p) :=
    continuousAt_id.prodMk continuousAt_const
  exact shears_eq_of_radial_eventuallyEq (p := p) (E := P.E) (U := P.U)
    (F := fun q => realizedE r E n q.1 q.2) (V := fun q => realizedU r E U n q.1 q.2)
    (hEj.comp_tendsto hrad) (hUj.comp_tendsto hrad)

/-- A finite integer frequency puts the actual localized profiles, with
their actual axis-integrated stresses, in the true cone throughout the
closed modulation window. All error bounds are derived in this theorem. -/
theorem profiles_trueCone {D D' : RadialDomain}
    (W : ModulatedHistories.Window) (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (hK : IsCompact K) (hKW : ∀ p ∈ K, p.1 ∈ Icc W.left W.right)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (haK : ∀ p ∈ K, 0 < a p)
    (haNom : ∀ p ∈ K, a p = angularShear E p)
    (hbNom : ∀ p ∈ K, a p * m p = signedAxialShear E U p)
    (hrelaxed : ∀ p ∈ K, TrueConeLoop.nominalSpeed (a p) (m p) <
      ConeAlgebra.coneBound (p₁ p + p₂ p * m p) (p₂ p - p₁ p * m p))
    (P : ℝ → Profiles D) (Q : Profiles D')
    (hPf : ∀ n, (P n).f = ModulatedHistories.localizedF W r f n)
    (hPU : ∀ n, (P n).U = ModulatedHistories.localizedU W r E U n)
    (hQf : Q.f = f) (hQU : Q.U = U) (hP0 : ∀ n, (P n).pressure0 = Q.pressure0)
    (J : Set ℝ) (hJ : IsCompact J) (hKJ : ∀ p ∈ K, p.2 ∈ J)
    (hKD : K ⊆ D.carrier) (hKD' : K ⊆ D'.carrier)
    (h : ℝ) (hL : ∀ p ∈ K, NaturalAxisData.L h p.2 ≠ 0)
    (hpos : ∀ p ∈ K, 0 < Q.f p)
    (hstock₁ : ∀ p ∈ K, p₁ p = ActivationStocks.profileStockOne Q h p)
    (hstock₂ : ∀ p ∈ K, p₂ p = ActivationStocks.profileStockTwo Q h p)
    (hBK : B ⊆ K) (hends : ∀ η ∈ J, (W.left, η) ∈ B ∧ (W.right, η) ∈ B)
    (hphys : ∀ p ∈ K, E =ᶠ[𝓝 p] fun q => Real.sqrt (2 * q.1) * f q) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ p ∈ K,
      0 < (P n).f p ∧
      TrueConeLoop.InTrueCone (ActivationStocks.profileStockOne (P n) h p)
        (ActivationStocks.profileStockTwo (P n) h p)
        (angularShear (P n).E p) (signedAxialShear (P n).E (P n).U p) := by
  have hX : ∀ p ∈ K, 0 < p.1 := fun p hp => W.left_pos.trans_le (hKW p hp).1
  have hE0 : ∀ p ∈ K, E p ≠ 0 := by
    intro p hp
    rw [(hphys p hp).eq_of_nhds]
    have hfpos : 0 < f p := by rw [← hQf]; exact hpos p hp
    exact (mul_pos (Real.sqrt_pos.mpr (mul_pos (by norm_num) (hX p hp))) hfpos).ne'
  obtain ⟨Ns, Cs, _, _, hsb⟩ := profile_stocks_rate W r f E U ha hm hp₂ hf hE hU P Q
    hPf hPU hQf hQU hP0 J hJ K hK hKJ hKD hKD' h hX hL hpos
  obtain ⟨Cv, _, hvb⟩ := realized_shears_uniform_bound r E U hK ha hm hp₂ hE hU haK
    (fun p hp => (hX p hp).ne') hE0 haNom hbNom
  obtain ⟨ρ, hρ, hstable⟩ := realized_loop_stable r hK ha hm hp₁ hp₂ haK hrelaxed
  obtain ⟨Nc, hNc, hlarge⟩ := exists_integer_frequency (max Cs Cv) ρ hρ
  refine ⟨max Ns Nc, hNc.trans_le (le_max_right _ _), ?_⟩
  intro n hn p hp
  have hns : Ns ≤ n := (le_max_left _ _).trans hn
  have hnc : Nc ≤ n := (le_max_right _ _).trans hn
  obtain ⟨hn1, hsmall⟩ := hlarge n hnc
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hs := hsb n (by exact_mod_cast hns) p hp
  have hv := hvb n hn1 p hp
  have hCs : Cs / (n : ℝ) ≤ ρ :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hn0).trans hsmall
  have hCv : Cv / (n : ℝ) ≤ ρ :=
    (div_le_div_of_nonneg_right (le_max_right _ _) hn0).trans hsmall
  have heq := physical_shears_match W r f E U ha hm hBK J hends n (P n)
    (hPf n) (hPU n) (hKW p hp) (hKJ p hp) (hphys p hp)
  refine ⟨hs.1, ?_⟩
  rw [heq.1, heq.2]
  apply hstable p hp (n * Real.log p.1) _ _ _ _
  · rw [hstock₁ p hp]
    exact hs.2.1.trans hCs
  · rw [hstock₂ p hp]
    exact hs.2.2.trans hCs
  · exact hv.1.trans hCv
  · exact hv.2.trans hCv

theorem after_window_agreement (W : ModulatedHistories.Window)
    (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (hBK : B ⊆ K) (J : Set ℝ)
    (hends : ∀ η ∈ J, (W.left, η) ∈ B ∧ (W.right, η) ∈ B)
    (n : ℝ) {p : Point} (hp : W.right ≤ p.1) (hη : p.2 ∈ J) :
    (ModulatedHistories.localizedF W r f n =ᶠ[𝓝 p] f) ∧
      (ModulatedHistories.localizedU W r E U n =ᶠ[𝓝 p] U) := by
  by_cases hstrict : W.right < p.1
  · have hn : {q : Point | W.right < q.1} ∈ 𝓝 p :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hstrict
    constructor
    · filter_upwards [hn] with q hq
      exact ModulatedHistories.splice_eq_after W f _ hq
    · filter_upwards [hn] with q hq
      exact ModulatedHistories.splice_eq_after W U _ hq
  · have heq : p.1 = W.right := (le_of_not_gt hstrict).antisymm hp
    have hpB : p ∈ B := by simpa only [← heq, Prod.eta] using (hends p.2 hη).2
    obtain ⟨Ω, V, _, _, hV, hBV, _, hmatch⟩ :=
      ModulatedHistories.exists_smooth_localization W r f E U ha hm hp₂ hf hE hU J hBK hends
    constructor
    · filter_upwards [hV.mem_nhds (hBV hpB)] with q hq
      exact (hmatch n q hq).1
    · filter_upwards [hV.mem_nhds (hBV hpB)] with q hq
      exact (hmatch n q hq).2

theorem physical_after_window_agreement {D : RadialDomain} (W : ModulatedHistories.Window)
    (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (hBK : B ⊆ K) (J : Set ℝ)
    (hends : ∀ η ∈ J, (W.left, η) ∈ B ∧ (W.right, η) ∈ B)
    (n : ℝ) (P : Profiles D)
    (hPf : P.f = ModulatedHistories.localizedF W r f n)
    (hPU : P.U = ModulatedHistories.localizedU W r E U n)
    {p : Point} (hp : W.right ≤ p.1) (hη : p.2 ∈ J)
    (hphys : E =ᶠ[𝓝 p] fun q => Real.sqrt (2 * q.1) * f q) :
    (P.E =ᶠ[𝓝 p] E) ∧ (P.U =ᶠ[𝓝 p] U) := by
  have hbase := after_window_agreement W r f E U ha hm hp₂ hf hE hU hBK J hends n hp hη
  constructor
  · filter_upwards [hbase.1, hphys] with q hq hEq
    change Real.sqrt (2 * q.1) * P.f q = E q
    rw [hPf, hq, hEq]
  · simpa only [hPU] using hbase.2

/-- The localized `Profiles` family used by the cone theorems is actually
constructed from the modulation and one common axis-pressure function. -/
theorem exists_profile_family (W : ModulatedHistories.Window)
    (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field) (P0 : ℝ → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (hP0 : ContDiff ℝ ∞ P0) (J : Set ℝ) (hBK : B ⊆ K)
    (hends : ∀ η ∈ J, (W.left, η) ∈ B ∧ (W.right, η) ∈ B) :
    ∃ (Ω : Set ℝ) (hΩ : IsOpen Ω), J ⊆ Ω ∧
      ∃ P : ℝ → Profiles (ModulatedHistories.stripDomain Ω hΩ),
        (∀ n, (P n).f = ModulatedHistories.localizedF W r f n ∧
          (P n).U = ModulatedHistories.localizedU W r E U n ∧ (P n).pressure0 = P0) ∧
        ∃ V : Set Point, IsOpen V ∧ B ⊆ V ∧
          ∀ n : ℝ, ∀ p ∈ V, (P n).f p = f p ∧ (P n).U p = U p := by
  obtain ⟨Ω, V, hΩ, hJΩ, hV, hBV, hsmooth, hmatch⟩ :=
    ModulatedHistories.exists_smooth_localization W r f E U ha hm hp₂ hf hE hU J hBK hends
  let P : ℝ → Profiles (ModulatedHistories.stripDomain Ω hΩ) := fun n =>
    ModulatedHistories.profiles Ω hΩ (ModulatedHistories.localizedF W r f n)
      (ModulatedHistories.localizedU W r E U n) P0 (hsmooth n).1 (hsmooth n).2 hP0.contDiffOn
  exact ⟨Ω, hΩ, hJΩ, P, (fun _ => ⟨rfl, rfl, rfl⟩), V, hV, hBV, hmatch⟩

end Localized

namespace Repaired

open ProfileHistories StressActivation

/-- The actual physical correction, retaining the existing axis pressure. -/
noncomputable def profileRepair {D : RadialDomain} (P : Profiles D)
    (patch : FiveProfileMoments.Patch) (A : ℝ → ℝ) (c : ℝ → ModulatedHistories.Coeff)
    (hA : ContDiff ℝ ∞ A) (hc : ContDiff ℝ ∞ c) : Profiles D where
  f := ModulatedHistories.applyRepairF patch A c P.f
  U := ModulatedHistories.applyRepairU patch A c P.U
  f_smooth := P.f_smooth.add (ModulatedHistories.editF_contDiff patch A c hA hc).contDiffOn
  U_smooth := P.U_smooth.add (ModulatedHistories.editU_contDiff patch A c hA hc).contDiffOn
  pressure0 := P.pressure0
  pressure0_smooth := P.pressure0_smooth

theorem profileRepair_radial_germs {D : RadialDomain} (P : Profiles D)
    (patch : FiveProfileMoments.Patch) (A : ℝ → ℝ) (c : ℝ → ModulatedHistories.Coeff)
    (hA : ContDiff ℝ ∞ A) (hc : ContDiff ℝ ∞ c) {p : Point}
    (hp : p.1 ∉ Ioo patch.left patch.right) :
    ((fun X => (profileRepair P patch A c hA hc).E (X, p.2)) =ᶠ[𝓝 p.1] fun X => P.E (X, p.2)) ∧
      ((fun X => (profileRepair P patch A c hA hc).U (X, p.2)) =ᶠ[𝓝 p.1] fun X => P.U (X, p.2)) :=
          by
  have hg := ModulatedHistories.repair_preserves_radial_germ patch A c P.f P.U p.1 p.2 hp
  constructor
  · filter_upwards [hg.1] with X hX
    change Real.sqrt (2 * X) * ModulatedHistories.applyRepairF patch A c P.f (X, p.2) = _
    rw [hX]
    rfl
  · exact hg.2

/-- Rows eta, given by `![parameterPartial P.M p, parameterPartial P.I p, parameterPartial P.J
p, parameterPartial P.S p, parameterPartial P.pressure p]`. -/
noncomputable def rowsEta {D : RadialDomain} (P : Profiles D) (p : Point) : Fin 5 → ℝ :=
  ![parameterPartial P.M p, parameterPartial P.I p, parameterPartial P.J p,
    parameterPartial P.S p, parameterPartial P.pressure p]

theorem rows_hasDerivAt {D : RadialDomain} (P : Profiles D) {p : Point} (hp : p ∈ D.carrier) :
    HasDerivAt (fun η => ModulatedHistories.profileRows P (p.1, η)) (rowsEta P p) p.2 := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact parameterPartial_hasDerivAt D P.M_smooth hp
  · exact parameterPartial_hasDerivAt D P.I_smooth hp
  · exact parameterPartial_hasDerivAt D P.J_smooth hp
  · exact parameterPartial_hasDerivAt D P.S_smooth hp
  · exact parameterPartial_hasDerivAt D P.pressure_smooth hp

theorem profileHistory_eta_eq_row {D : RadialDomain} (P : Profiles D)
    (row : HistoryRow) (p : Point) :
    parameterPartial (profileHistory P row) p = rowsEta P p (Localized.historyIndex row) := by
  cases row <;> rfl

/-- Vector bounds for the five actual history jets imply each actual
history/parameter-derivative bound needed by the stock estimate. -/
theorem rows_first_jet_bound {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D')
    {p : Point} (hp : p ∈ D.carrier) (hp' : p ∈ D'.carrier) {J : Set ℝ} {ε : ℝ}
    (hjet : JetBounds.FiniteJetBound 1 (fun η =>
      ModulatedHistories.profileRows P (p.1, η) - ModulatedHistories.profileRows Q (p.1, η)) J ε)
    (hη : p.2 ∈ J) (row : HistoryRow) :
    |profileHistory P row p - profileHistory Q row p| ≤ ε ∧
      |parameterPartial (profileHistory P row) p - parameterPartial (profileHistory Q row) p| ≤ ε
          := by
  have hv : ‖ModulatedHistories.profileRows P p - ModulatedHistories.profileRows Q p‖ ≤ ε :=
    hjet.norm_le hη
  have hd : ‖rowsEta P p - rowsEta Q p‖ ≤ ε := by
    have hderiv := ((rows_hasDerivAt P hp).fun_sub (rows_hasDerivAt Q hp')).deriv
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one, hderiv] using
      hjet 1 le_rfl p.2 hη
  constructor
  · rw [Localized.profileHistory_eq_row, Localized.profileHistory_eq_row]
    exact (show |ModulatedHistories.profileRows P p (Localized.historyIndex row) -
      ModulatedHistories.profileRows Q p (Localized.historyIndex row)| ≤
        ‖ModulatedHistories.profileRows P p - ModulatedHistories.profileRows Q p‖ from
      by simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        norm_le_pi_norm (ModulatedHistories.profileRows P p - ModulatedHistories.profileRows Q p)
          (Localized.historyIndex row)).trans hv
  · rw [profileHistory_eta_eq_row, profileHistory_eta_eq_row]
    exact (show |rowsEta P p (Localized.historyIndex row) - rowsEta Q p (Localized.historyIndex
        row)| ≤
        ‖rowsEta P p - rowsEta Q p‖ from by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        norm_le_pi_norm (rowsEta P p - rowsEta Q p) (Localized.historyIndex row)).trans hd

/-- The actual correction leaves the physical fields and both radial
shears unchanged outside the open repair patch. -/
theorem shears_unchanged_outside {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D')
    (patch : FiveProfileMoments.Patch) (A : ℝ → ℝ) (c : ℝ → ModulatedHistories.Coeff)
    (hf : P.f = ModulatedHistories.applyRepairF patch A c Q.f)
    (hU : P.U = ModulatedHistories.applyRepairU patch A c Q.U)
    {p : Point} (hp : p.1 ∉ Ioo patch.left patch.right) :
    P.E p = Q.E p ∧ P.U p = Q.U p ∧
      angularShear P.E p = angularShear Q.E p ∧
      signedAxialShear P.E P.U p = signedAxialShear Q.E Q.U p := by
  have hg := ModulatedHistories.repair_preserves_radial_germ patch A c Q.f Q.U p.1 p.2 hp
  have hEg : (fun X => P.E (X, p.2)) =ᶠ[𝓝 p.1] (fun X => Q.E (X, p.2)) := by
    filter_upwards [hg.1] with X hX
    change Real.sqrt (2 * X) * P.f (X, p.2) = Real.sqrt (2 * X) * Q.f (X, p.2)
    rw [hf, hX]
  have hUg : (fun X => P.U (X, p.2)) =ᶠ[𝓝 p.1] (fun X => Q.U (X, p.2)) := by
    simpa only [hU] using hg.2
  exact ⟨hEg.eq_of_nhds, hUg.eq_of_nhds,
    shears_eq_of_radial_eventuallyEq (p := p) (E := P.E) (U := P.U) (F := Q.E) (V := Q.U) hEg hUg⟩

theorem radialDerivative_add (F G : Field) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (p : Point) : radialDerivative (fun q => F q + G q) p = radialDerivative F p + radialDerivative
        G p := by
  exact deriv_fun_add
    ((hF.differentiable (by
        simp) p).comp p.1 (differentiableAt_id.prodMk (differentiableAt_const p.2)))
    ((hG.differentiable (by
        simp) p).comp p.1 (differentiableAt_id.prodMk (differentiableAt_const p.2)))

/-- On a patch where the base profile is nominal, the actual physical
repair has exactly its prescribed additive value and derivative errors. -/
theorem field_difference_identities {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D')
    (patch : FiveProfileMoments.Patch) (A : ℝ → ℝ) (c : ℝ → ModulatedHistories.Coeff)
    (hA : ContDiff ℝ ∞ A) (hc : ContDiff ℝ ∞ c)
    (hf : P.f = ModulatedHistories.applyRepairF patch A c Q.f)
    (hU : P.U = ModulatedHistories.applyRepairU patch A c Q.U)
    (E U : Field) (hE : ContDiff ℝ ∞ E) (hUs : ContDiff ℝ ∞ U)
    {p : Point} (hp : 0 < p.1) (hbaseE : Q.E =ᶠ[𝓝 p] E) (hbaseU : Q.U =ᶠ[𝓝 p] U) :
    P.E p - E p = ModulatedHistories.editE patch A c p ∧
      radialDerivative P.E p - radialDerivative E p = radialDerivative (ModulatedHistories.editE
          patch A c) p ∧
      radialDerivative P.U p - radialDerivative U p = radialDerivative (ModulatedHistories.editU
          patch A c) p := by
  have hEg : P.E =ᶠ[𝓝 p] (fun q => E q + ModulatedHistories.editE patch A c q) := by
    have hn : {q : Point | 0 < q.1} ∈ 𝓝 p :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hp
    filter_upwards [hbaseE, hn] with q hq hX
    have hs : Real.sqrt (2 * q.1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    calc
      P.E q = Q.E q + ModulatedHistories.editE patch A c q := by
        dsimp only [Profiles.E]
        rw [hf]
        dsimp only [ModulatedHistories.applyRepairF, ModulatedHistories.editF]
        field_simp
      _ = _ := by rw [hq]
  have hUg : P.U =ᶠ[𝓝 p] (fun q => U q + ModulatedHistories.editU patch A c q) := by
    filter_upwards [hbaseU] with q hq
    rw [hU, ModulatedHistories.applyRepairU, hq]
  have hrad : Filter.Tendsto (fun X : ℝ => (X, p.2)) (𝓝 p.1) (𝓝 p) :=
    continuousAt_id.prodMk continuousAt_const
  have hEd := (hEg.comp_tendsto hrad).deriv_eq
  have hUd := (hUg.comp_tendsto hrad).deriv_eq
  change radialDerivative P.E p = radialDerivative (fun q => E q + ModulatedHistories.editE patch A
      c q) p at hEd
  change radialDerivative P.U p = radialDerivative (fun q => U q + ModulatedHistories.editU patch A
      c q) p at hUd
  rw [radialDerivative_add E _ hE (ModulatedHistories.editE_contDiff patch A c hA hc) p] at hEd
  rw [radialDerivative_add U _ hUs (ModulatedHistories.editU_contDiff patch A c hA hc) p] at hUd
  exact ⟨by linarith [hEg.eq_of_nhds], by linarith, by linarith⟩

/-- The actual moment edit supplies a uniform first-radial-derivative
bound from its coefficient jet bound. No shear estimate is a premise. -/
theorem field_C1_bound (patch : FiveProfileMoments.Patch) (J : Set ℝ) (hJ : IsCompact J)
    (A : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ → ModulatedHistories.Coeff, ContDiff ℝ ∞ c →
      ∀ ε : ℝ, 0 ≤ ε → JetBounds.FiniteJetBound 1 c J ε →
      ∀ {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D'),
      P.f = ModulatedHistories.applyRepairF patch A c Q.f →
      P.U = ModulatedHistories.applyRepairU patch A c Q.U →
      ∀ E U : Field, ContDiff ℝ ∞ E → ContDiff ℝ ∞ U → ∀ p : Point,
      0 < p.1 → p.2 ∈ J → Q.E =ᶠ[𝓝 p] E → Q.U =ᶠ[𝓝 p] U →
      |P.E p - E p| ≤ C * ε ∧
        |radialDerivative P.E p - radialDerivative E p| ≤ C * ε ∧
        |radialDerivative P.U p - radialDerivative U p| ≤ C * ε := by
  obtain ⟨C, hC, hb⟩ := ModulatedHistories.physical_mixed_edits_bound patch J hJ A hA 1
  refine ⟨C, hC, ?_⟩
  intro c hc ε hε hjet D D' P Q hf hU E U hE hUs p hp hη hbaseE hbaseU
  have hi := field_difference_identities P Q patch A c hA hc hf hU E U hE hUs hp hbaseE hbaseU
  rw [hi.1, hi.2.1, hi.2.2]
  have hv := (hb c hc ε hε hjet p.2 hη 0 (by omega) 0 (by omega) p.1).2
  have hd := hb c hc ε hε hjet p.2 hη 1 le_rfl 0 (by omega) p.1
  simpa only [norm_iteratedFDeriv_zero, iteratedDeriv_zero, iteratedDeriv_one,
    Real.norm_eq_abs, radialDerivative] using And.intro hv (And.intro hd.2 hd.1)

/-- A later repair preserves the already realized shears on the entire
closed modulation window, including both endpoint collars. -/
theorem window_shears_match {D D' : RadialDomain} (W : ModulatedHistories.Window)
    (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hBK : B ⊆ K)
    (J : Set ℝ) (hends : ∀ η ∈ J, (W.left, η) ∈ B ∧ (W.right, η) ∈ B)
    (n : ℝ) (Q : Profiles D) (P : Profiles D')
    (hQf : Q.f = ModulatedHistories.localizedF W r f n)
    (hQU : Q.U = ModulatedHistories.localizedU W r E U n)
    (patch : FiveProfileMoments.Patch) (A : ℝ → ℝ) (c : ℝ → ModulatedHistories.Coeff)
    (hgap : W.right < patch.left)
    (hPf : P.f = ModulatedHistories.applyRepairF patch A c Q.f)
    (hPU : P.U = ModulatedHistories.applyRepairU patch A c Q.U)
    {p : Point} (hp : p.1 ∈ Icc W.left W.right) (hη : p.2 ∈ J)
    (hphys : E =ᶠ[𝓝 p] fun q => Real.sqrt (2 * q.1) * f q) :
    angularShear P.E p = angularShear (fun q => realizedE r E n q.1 q.2) p ∧
      signedAxialShear P.E P.U p = signedAxialShear (fun q => realizedE r E n q.1 q.2)
        (fun q => realizedU r E U n q.1 q.2) p := by
  have hout : p.1 ∉ Ioo patch.left patch.right := by
    intro hx
    linarith [hp.2, hx.1]
  have hr := shears_unchanged_outside P Q patch A c hPf hPU hout
  have hm := Localized.physical_shears_match W r f E U ha hm hBK J hends n Q hQf hQU hp hη hphys
  exact ⟨hr.2.2.1.trans hm.1, hr.2.2.2.trans hm.2⟩

/-- The actual repaired profile data satisfy a uniform estimate before,
inside, and after the repair. The two contributions are the modulation
error and the coefficient size of this same physical repair. -/
theorem profile_data_bound (W : ModulatedHistories.Window)
    (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (patch : FiveProfileMoments.Patch) (hgap : W.right < patch.left)
    (A : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (J : Set ℝ) (hJ : IsCompact J) :
    ∃ δ C₁ C₂ : ℝ, 0 < δ ∧ 0 < C₁ ∧ 0 < C₂ ∧ ∀ n : ℝ, 1 ≤ n →
      ∀ c : ℝ → ModulatedHistories.Coeff, ContDiff ℝ ∞ c →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ → JetBounds.FiniteJetBound 1 c J ε →
      ∀ {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D'),
      P.f = ModulatedHistories.applyRepairF patch A c (ModulatedHistories.localizedF W r f n) →
      P.U = ModulatedHistories.applyRepairU patch A c (ModulatedHistories.localizedU W r E U n) →
      Q.f = f → Q.U = U → P.pressure0 = Q.pressure0 →
      ∀ p : Point, 0 ≤ p.1 → p.2 ∈ J → p ∈ D.carrier → p ∈ D'.carrier →
      ‖ModulatedStockBounds.profileData P p - ModulatedStockBounds.profileData Q p‖ ≤ C₁ / n + C₂ *
          ε := by
  obtain ⟨δ, CH₁, CH₂, hδ, hCH₁, hCH₂, hhistory⟩ := ModulatedHistories.repaired_axisHistory_jets
    W r f E U ha hm hp₂ hf hE hU patch hgap A hA J hJ 1
  obtain ⟨Cf, hCf, hfield⟩ := Localized.fields_uniform_bound W r f E U ha hm hp₂ hf hE hU J hJ
  obtain ⟨Ce, hCe, hedit⟩ := ModulatedHistories.normalized_edits_eta_bound patch J hJ A hA 1
  refine ⟨δ, max Cf CH₁, max Ce CH₂, hδ, hCH₁.trans_le (le_max_right _ _),
    hCe.trans_le (le_max_left _ _), ?_⟩
  intro n hn c hc ε hε hεδ hjet D D' P Q hPf hPU hQf hQU hP0 p hX hη hp hp'
  have hn0 : 0 ≤ n := le_trans zero_le_one hn
  have hF := hfield n hn p.1 p.2 hη
  have hEbound := hedit c hc ε hε hjet p.2 hη 0 (by omega) p.1
  simp only [iteratedDeriv_zero] at hEbound
  have hfb : Cf / n + Ce * ε ≤ max Cf CH₁ / n + max Ce CH₂ * ε :=
    add_le_add (div_le_div_of_nonneg_right (le_max_left _ _) hn0)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hε)
  have hhb : CH₁ / n + CH₂ * ε ≤ max Cf CH₁ / n + max Ce CH₂ * ε :=
    add_le_add (div_le_div_of_nonneg_right (le_max_right _ _) hn0)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hε)
  have hrows : JetBounds.FiniteJetBound 1 (fun η =>
      ModulatedHistories.profileRows P (p.1, η) - ModulatedHistories.profileRows Q (p.1, η)) J
      (CH₁ / n + CH₂ * ε) := by
    have heq : (fun η => ModulatedHistories.profileRows P (p.1, η) -
        ModulatedHistories.profileRows Q (p.1, η)) = (fun η =>
        ModulatedHistories.axisHistory
          (ModulatedHistories.applyRepairF patch A c (ModulatedHistories.localizedF W r f n))
          (ModulatedHistories.applyRepairU patch A c (ModulatedHistories.localizedU W r E U n))
              (p.1, η) -
        ModulatedHistories.axisHistory f U (p.1, η)) := by
      funext η
      rw [ModulatedHistories.profileRows_sub P Q hP0, hPf, hPU, hQf, hQU]
    rw [heq]
    exact hhistory n hn c hc ε hε hεδ hjet p.1 hX
  apply ModulatedStockBounds.profileData_error_bound P Q p (by positivity)
  · rw [hPf, hQf]
    change |ModulatedHistories.localizedF W r f n p + ModulatedHistories.editF patch A c p - f p| ≤
        _
    calc
      _ = |(ModulatedHistories.localizedF W r f n p - f p) + ModulatedHistories.editF patch A c p|
          := by
          congr 1; ring
      _ ≤ |ModulatedHistories.localizedF W r f n p - f p| + |ModulatedHistories.editF patch A c p|
          := abs_add_le _ _
      _ ≤ Cf / n + Ce * ε := add_le_add hF.1 hEbound.1
      _ ≤ _ := hfb
  · rw [hPU, hQU]
    change |ModulatedHistories.localizedU W r E U n p + ModulatedHistories.editU patch A c p - U p|
        ≤ _
    calc
      _ = |(ModulatedHistories.localizedU W r E U n p - U p) + ModulatedHistories.editU patch A c
          p| := by
          congr 1; ring
      _ ≤ |ModulatedHistories.localizedU W r E U n p - U p| + |ModulatedHistories.editU patch A c
          p| := abs_add_le _ _
      _ ≤ Cf / n + Ce * ε := add_le_add hF.2 hEbound.2
      _ ≤ _ := hfb
  · intro row
    have hb := rows_first_jet_bound P Q hp hp' hrows hη row
    exact ⟨hb.1.trans hhb, hb.2.trans hhb⟩

/-- Uniform stock estimates for a family of actual repaired profiles,
using only the proved coefficient size of the moment solver. -/
theorem profile_stocks_rate {D D' : RadialDomain}
    (W : ModulatedHistories.Window) (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (patch : FiveProfileMoments.Patch) (hgap : W.right < patch.left)
    (A : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (J : Set ℝ) (hJ : IsCompact J)
    (c : ℝ → ℝ → ModulatedHistories.Coeff) (hc : ∀ n, ContDiff ℝ ∞ (c n))
    (n₀ Cc : ℝ) (hCc : 0 ≤ Cc)
    (hcoeff : ∀ n : ℝ, n₀ ≤ n → 1 ≤ n → JetBounds.FiniteJetBound 1 (c n) J (Cc / n))
    (P : ℝ → Profiles D) (Q : Profiles D')
    (hPf : ∀ n, (P n).f = ModulatedHistories.applyRepairF patch A (c n)
        (ModulatedHistories.localizedF W r f n))
    (hPU : ∀ n, (P n).U = ModulatedHistories.applyRepairU patch A (c n)
        (ModulatedHistories.localizedU W r E U n))
    (hQf : Q.f = f) (hQU : Q.U = U) (hP0 : ∀ n, (P n).pressure0 = Q.pressure0)
    (T : Set Point) (hT : IsCompact T) (hTJ : ∀ p ∈ T, p.2 ∈ J)
    (hTD : T ⊆ D.carrier) (hTD' : T ⊆ D'.carrier)
    (h : ℝ) (hX : ∀ p ∈ T, 0 < p.1) (hL : ∀ p ∈ T, NaturalAxisData.L h p.2 ≠ 0)
    (hpos : ∀ p ∈ T, 0 < Q.f p) :
    ∃ N : ℕ, ∃ C : ℝ, 0 < N ∧ 0 ≤ C ∧ ∀ n : ℝ, (N : ℝ) ≤ n → ∀ p ∈ T,
      0 < (P n).f p ∧
      |ActivationStocks.profileStockOne (P n) h p - ActivationStocks.profileStockOne Q h p| ≤ C / n
          ∧
      |ActivationStocks.profileStockTwo (P n) h p - ActivationStocks.profileStockTwo Q h p| ≤ C / n
          := by
  obtain ⟨δr, C₁, C₂, hδr, hC₁, hC₂, hdata⟩ := profile_data_bound
    W r f E U ha hm hp₂ hf hE hU patch hgap A hA J hJ
  obtain ⟨δs, Cs, hδs, hCs, hstock⟩ := ModulatedStockBounds.profile_stocks_lipschitz
    Q h hT hTD' hX hL hpos
  let Ddata := C₁ + C₂ * Cc
  have hDdata : 0 ≤ Ddata := by dsimp [Ddata]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (max n₀ (max (Cc / δr) (Ddata / δs))))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  refine ⟨N, Cs * Ddata, by exact_mod_cast (lt_trans zero_lt_one hN1), mul_nonneg hCs hDdata, ?_⟩
  intro n hn p hp
  have hn1 : 1 ≤ n := hN1.le.trans hn
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  have hnr : n₀ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans (hN.le.trans hn)
  have hsmallr : Cc / n ≤ δr := by
    apply (div_le_iff₀ hnpos).mpr
    have hb : Cc / δr ≤ n :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans (hN.le.trans hn)
    have := (div_le_iff₀ hδr).mp hb
    linarith
  have hsmalls : Ddata / n ≤ δs := by
    apply (div_le_iff₀ hnpos).mpr
    have hb : Ddata / δs ≤ n :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans (hN.le.trans
          hn)
    have := (div_le_iff₀ hδs).mp hb
    linarith
  have hdatap := hdata n hn1 (c n) (hc n) (Cc / n) (div_nonneg hCc hnpos.le) hsmallr
    (hcoeff n hnr hn1) (P n) Q (hPf n) (hPU n) hQf hQU (hP0 n) p (hX p hp).le
    (hTJ p hp) (hTD hp) (hTD' hp)
  have hd : ‖ModulatedStockBounds.profileData (P n) p - ModulatedStockBounds.profileData Q p‖ ≤
      Ddata / n := by
    convert! hdatap using 1
    dsimp [Ddata]
    ring
  obtain ⟨hPpos, hs₁, hs₂⟩ := hstock (P n) p hp (hTD hp) (hd.trans hsmalls)
  refine ⟨hPpos, ?_, ?_⟩
  · exact (hs₁.trans (mul_le_mul_of_nonneg_left hd hCs)).trans_eq (by ring)
  · exact (hs₂.trans (mul_le_mul_of_nonneg_left hd hCs)).trans_eq (by ring)

/-- Both portions of the actual repaired construction lie in the true
cone for one finite frequency threshold. The coefficient input is the
quantitative output of the actual moment solver. -/
theorem profiles_trueCone {D D' : RadialDomain}
    (W : ModulatedHistories.Window) (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (hK : IsCompact K) (hKW : ∀ p ∈ K, p.1 ∈ Icc W.left W.right)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (haK : ∀ p ∈ K, 0 < a p)
    (S : Set Point) (hS : IsCompact S) (hSW : ∀ p ∈ S, W.right ≤ p.1)
    (haNom : ∀ p ∈ K ∪ S, a p = angularShear E p)
    (hbNom : ∀ p ∈ K ∪ S, a p * m p = signedAxialShear E U p)
    (hrelaxed : ∀ p ∈ K, TrueConeLoop.nominalSpeed (a p) (m p) <
      ConeAlgebra.coneBound (p₁ p + p₂ p * m p) (p₂ p - p₁ p * m p))
    (hScone : ∀ p ∈ S, TrueConeLoop.InTrueCone (p₁ p) (p₂ p) (a p) (a p * m p))
    (P : ℝ → Profiles D) (Q : Profiles D')
    (hPf : ∀ n, (P n).f = ModulatedHistories.localizedF W r f n)
    (hPU : ∀ n, (P n).U = ModulatedHistories.localizedU W r E U n)
    (hQf : Q.f = f) (hQU : Q.U = U) (hP0 : ∀ n, (P n).pressure0 = Q.pressure0)
    (J : Set ℝ) (hJ : IsCompact J) (hTJ : ∀ p ∈ K ∪ S, p.2 ∈ J)
    (hTD : K ∪ S ⊆ D.carrier) (hTD' : K ∪ S ⊆ D'.carrier)
    (h : ℝ) (hL : ∀ p ∈ K ∪ S, NaturalAxisData.L h p.2 ≠ 0)
    (hpos : ∀ p ∈ K ∪ S, 0 < Q.f p)
    (hstock₁ : ∀ p ∈ K ∪ S, p₁ p = ActivationStocks.profileStockOne Q h p)
    (hstock₂ : ∀ p ∈ K ∪ S, p₂ p = ActivationStocks.profileStockTwo Q h p)
    (hBK : B ⊆ K) (hends : ∀ η ∈ J, (W.left, η) ∈ B ∧ (W.right, η) ∈ B)
    (hphys : ∀ p ∈ K ∪ S, E =ᶠ[𝓝 p] fun q => Real.sqrt (2 * q.1) * f q)
    (patch : FiveProfileMoments.Patch) (hgap : W.right < patch.left)
    (A : ℝ → ℝ) (hA : ContDiff ℝ ∞ A)
    (c : ℝ → ℝ → ModulatedHistories.Coeff) (hc : ∀ n, ContDiff ℝ ∞ (c n))
    (n₀ Cc : ℝ) (hCc : 0 ≤ Cc)
    (hcoeff : ∀ n : ℝ, n₀ ≤ n → 1 ≤ n → JetBounds.FiniteJetBound 1 (c n) J (Cc / n)) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ p ∈ K ∪ S,
      let R := profileRepair (P n) patch A (c n) hA (hc n)
      0 < R.f p ∧ TrueConeLoop.InTrueCone (ActivationStocks.profileStockOne R h p)
        (ActivationStocks.profileStockTwo R h p) (angularShear R.E p) (signedAxialShear R.E R.U p)
            := by
  let R : ℝ → Profiles D := fun n => profileRepair (P n) patch A (c n) hA (hc n)
  have hX : ∀ p ∈ K ∪ S, 0 < p.1 := by
    intro p hp
    rcases hp with hp | hp
    · exact W.left_pos.trans_le (hKW p hp).1
    · exact (W.left_pos.trans W.ordered).trans_le (hSW p hp)
  have hEp : ∀ p ∈ K ∪ S, 0 < E p := by
    intro p hp
    rw [(hphys p hp).eq_of_nhds]
    have hfp : 0 < f p := by rw [← hQf]; exact hpos p hp
    exact mul_pos (Real.sqrt_pos.mpr (by have := hX p hp; positivity)) hfp
  have hRf (n : ℝ) : (R n).f = ModulatedHistories.applyRepairF patch A (c n)
      (ModulatedHistories.localizedF W r f n) := by rw [← hPf n]; rfl
  have hRU (n : ℝ) : (R n).U = ModulatedHistories.applyRepairU patch A (c n)
      (ModulatedHistories.localizedU W r E U n) := by rw [← hPU n]; rfl
  obtain ⟨Ns, Cs, _, _, hsb⟩ := profile_stocks_rate W r f E U ha hm hp₂ hf hE hU patch hgap A hA
    J hJ c hc n₀ Cc hCc hcoeff R Q hRf hRU hQf hQU hP0 (K ∪ S) (hK.union hS) hTJ
    hTD hTD' h hX hL hpos
  obtain ⟨Ce, hCe, heb⟩ := field_C1_bound patch J hJ A hA
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt n₀
  let M := max Ns N₀
  have hstock : ∀ n : ℕ, M ≤ n → 1 ≤ (n : ℝ) → ∀ p ∈ K ∪ S,
      |ActivationStocks.profileStockOne (R n) h p - p₁ p| ≤ Cs / n ∧
      |ActivationStocks.profileStockTwo (R n) h p - p₂ p| ≤ Cs / n := by
    intro n hn _ p hp
    have hns : (Ns : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_left _ _) hn)
    have hs := (hsb n hns p hp).2
    simpa only [hstock₁ p hp, hstock₂ p hp] using hs
  have hnb : ∀ n : ℕ, M ≤ n → n₀ ≤ (n : ℝ) := by
    intro n hn
    exact hN₀.le.trans (by exact_mod_cast (le_trans (le_max_right _ _) hn))
  have hedit : ∀ n : ℕ, M ≤ n → 1 ≤ (n : ℝ) → ∀ p ∈ S,
      |(R n).E p - E p| ≤ (Ce * Cc) / n ∧
      |radialDerivative (R n).E p - radialDerivative E p| ≤ (Ce * Cc) / n ∧
      |radialDerivative (R n).U p - radialDerivative U p| ≤ (Ce * Cc) / n := by
    intro n hn hn1 p hp
    have hb := Localized.physical_after_window_agreement W r f E U ha hm hp₂ hf hE hU hBK J hends
      n (P n) (hPf n) (hPU n) (hSW p hp) (hTJ p (Or.inr hp)) (hphys p (Or.inr hp))
    have he := heb (c n) (hc n) (Cc / n) (div_nonneg hCc (by positivity))
      (hcoeff n (hnb n hn) hn1) (R n) (P n) rfl rfl E U hE hU p (hX p (Or.inr hp))
      (hTJ p (Or.inr hp)) hb.1 hb.2
    simpa only [mul_div_assoc] using he
  have hlocal : ∀ n : ℕ, M ≤ n → ∀ p ∈ K,
      ((fun X => (R n).E (X, p.2)) =ᶠ[𝓝 p.1] fun X => realizedE r E n X p.2) ∧
      ((fun X => (R n).U (X, p.2)) =ᶠ[𝓝 p.1] fun X => realizedU r E U n X p.2) := by
    intro n _ p hp
    have hout : p.1 ∉ Ioo patch.left patch.right := by intro hx; linarith [(hKW p hp).2, hx.1]
    have hg := profileRepair_radial_germs (P n) patch A (c n) hA (hc n) hout
    have hb := Localized.physical_profile_germs W r f E U ha hm hBK J hends n (P n) (hPf n) (hPU n)
      (hKW p hp) (hTJ p (Or.inl hp)) (hphys p (Or.inl hp))
    have hrad : Filter.Tendsto (fun X : ℝ => (X, p.2)) (𝓝 p.1) (𝓝 p) :=
      continuousAt_id.prodMk continuousAt_const
    exact ⟨hg.1.trans (hb.1.comp_tendsto hrad), hg.2.trans (hb.2.comp_tendsto hrad)⟩
  obtain ⟨Nc, hNc, hcone⟩ := repaired_trueCone_of_bounds r E U hK ha hm hp₁ hp₂ hE hU haK
    (fun p hp => (hX p (Or.inl hp)).ne') (fun p hp => (hEp p (Or.inl hp)).ne')
    (fun p hp => haNom p (Or.inl hp)) (fun p hp => hbNom p (Or.inl hp)) hrelaxed S hS
    (fun p hp => hEp p (Or.inr hp)) (fun p hp => haNom p (Or.inr hp))
    (fun p hp => hbNom p (Or.inr hp)) hScone
    (fun n => (R n).E) (fun n => (R n).U)
    (fun n => ActivationStocks.profileStockOne (R n) h)
    (fun n => ActivationStocks.profileStockTwo (R n) h) M Cs (Ce * Cc) (mul_nonneg hCe.le hCc)
    hstock hedit hlocal
  refine ⟨max Nc Ns, hNc.trans_le (le_max_left _ _), ?_⟩
  intro n hn p hp
  have hns : (Ns : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right _ _) hn)
  exact ⟨(hsb n hns p hp).1, hcone n ((le_max_left _ _).trans hn) p hp⟩

/-- The actual nonlinear five-row solve and the actual modulation allow
one finite integer frequency with the true cone throughout the loop and
following nominal patch. All five histories are restored exactly after
the repair, and every radial germ outside its support is unchanged. -/
theorem exists_with_moment_repair {D D' : RadialDomain}
    (W : ModulatedHistories.Window) (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (hK : IsCompact K) (hKW : ∀ p ∈ K, p.1 ∈ Icc W.left W.right)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (haK : ∀ p ∈ K, 0 < a p)
    (S : Set Point) (hS : IsCompact S) (hSW : ∀ p ∈ S, W.right ≤ p.1)
    (haNom : ∀ p ∈ K ∪ S, a p = angularShear E p)
    (hbNom : ∀ p ∈ K ∪ S, a p * m p = signedAxialShear E U p)
    (hrelaxed : ∀ p ∈ K, TrueConeLoop.nominalSpeed (a p) (m p) <
      ConeAlgebra.coneBound (p₁ p + p₂ p * m p) (p₂ p - p₁ p * m p))
    (hScone : ∀ p ∈ S, TrueConeLoop.InTrueCone (p₁ p) (p₂ p) (a p) (a p * m p))
    (P : ℝ → Profiles D) (Q : Profiles D')
    (hPf : ∀ n, (P n).f = ModulatedHistories.localizedF W r f n)
    (hPU : ∀ n, (P n).U = ModulatedHistories.localizedU W r E U n)
    (hQf : Q.f = f) (hQU : Q.U = U) (hP0 : ∀ n, (P n).pressure0 = Q.pressure0)
    (J : Set ℝ) (hJ : IsCompact J) (hTJ : ∀ p ∈ K ∪ S, p.2 ∈ J)
    (hTD : K ∪ S ⊆ D.carrier) (hTD' : K ∪ S ⊆ D'.carrier)
    (h : ℝ) (hL : ∀ p ∈ K ∪ S, NaturalAxisData.L h p.2 ≠ 0)
    (hpos : ∀ p ∈ K ∪ S, 0 < Q.f p)
    (hstock₁ : ∀ p ∈ K ∪ S, p₁ p = ActivationStocks.profileStockOne Q h p)
    (hstock₂ : ∀ p ∈ K ∪ S, p₂ p = ActivationStocks.profileStockTwo Q h p)
    (hBK : B ⊆ K) (hends : ∀ η ∈ J, (W.left, η) ∈ B ∧ (W.right, η) ∈ B)
    (hphys : ∀ p ∈ K ∪ S, E =ᶠ[𝓝 p] fun q => Real.sqrt (2 * q.1) * f q)
    (patch : FiveProfileMoments.Patch) (hgap : W.right < patch.left)
    (A G : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G) (hApos : ∀ η, 0 < A η)
    (hwindow : Icc W.left W.right ×ˢ J ⊆ K)
    (hfollowing : Icc W.right patch.right ×ˢ J ⊆ S)
    (b : ℝ) (hb : FiveProfileMoments.GoodExponent b)
    (hpatchU : ∀ η ∈ J, ∀ X ∈ Ioo patch.left patch.right, U (X, η) = G η)
    (hpatchE : ∀ η ∈ J, ∀ X ∈ Ioo patch.left patch.right,
      Real.sqrt (2 * X) * f (X, η) = A η * X ^ b) :
    ∃ (N : ℕ) (c : ℝ → ModulatedHistories.Coeff) (hc : ContDiff ℝ ∞ c), 0 < N ∧
      let R := profileRepair (P N) patch A c hA hc
      (∀ p ∈ Icc W.left patch.right ×ˢ J, 0 < R.f p ∧ TrueConeLoop.InTrueCone
          (ActivationStocks.profileStockOne R h p)
        (ActivationStocks.profileStockTwo R h p) (angularShear R.E p) (signedAxialShear R.E R.U p))
            ∧
      (∀ η ∈ J, ∀ X : ℝ, patch.right ≤ X →
        ModulatedHistories.profileRows R (X, η) = ModulatedHistories.profileRows Q (X, η)) ∧
      (∀ p : Point, p.1 ∉ Ioo patch.left patch.right →
        R.E p = (P N).E p ∧ R.U p = (P N).U p ∧
        angularShear R.E p = angularShear (P N).E p ∧
        signedAxialShear R.E R.U p = signedAxialShear (P N).E (P N).U p) := by
  classical
  obtain ⟨N₀, Cc, hN₀, hCc, hbranch⟩ := ModulatedHistories.actual_repair_family
    W r f E U ha hm hp₂ hf hE hU patch b hb J hJ A G hA hG hApos 1
  choose c₀ V hc₀ hV hJV hsolve hjet using hbranch
  let c : ℝ → ℝ → ModulatedHistories.Coeff := fun n =>
    if hn : N₀ ≤ n then c₀ n hn else fun _ => 0
  have hc (n : ℝ) : ContDiff ℝ ∞ (c n) := by
    dsimp only [c]
    split_ifs with hn
    · exact hc₀ n hn
    · exact contDiff_const
  have hcoeff : ∀ n : ℝ, N₀ ≤ n → 1 ≤ n → JetBounds.FiniteJetBound 1 (c n) J (Cc / n) := by
    intro n hn _
    simpa only [c, dite_eq_left hn] using hjet n hn
  obtain ⟨Nc, hNc, hcone⟩ := profiles_trueCone W r f E U hK hKW ha hm hp₁ hp₂ hf hE hU haK
    S hS hSW haNom hbNom hrelaxed hScone P Q hPf hPU hQf hQU hP0 J hJ hTJ hTD hTD'
    h hL hpos hstock₁ hstock₂ hBK hends hphys patch hgap A hA c hc N₀ Cc hCc.le hcoeff
  obtain ⟨Nr, hNr⟩ := exists_nat_gt N₀
  let N : ℕ := max Nc Nr
  have hcn : Nc ≤ N := le_max_left _ _
  have hrn : N₀ ≤ (N : ℝ) := hNr.le.trans (by exact_mod_cast (le_max_right Nc Nr))
  refine ⟨N, c N, hc N, hNc.trans_le hcn, ?_, ?_, ?_⟩
  · intro p hp
    have hpt : p ∈ K ∪ S := by
      by_cases hr : p.1 ≤ W.right
      · exact Or.inl (hwindow ⟨⟨hp.1.1, hr⟩, hp.2⟩)
      · exact Or.inr (hfollowing ⟨⟨(lt_of_not_ge hr).le, hp.1.2⟩, hp.2⟩)
    exact hcone N hcn p hpt
  · intro η hη X hX
    have hmom : FiveProfileMoments.physicalMoments patch b (A η) (G η) (c N η) =
        ModulatedHistories.repairDebt W r f E U N η := by
      simpa only [c, dite_eq_left hrn] using (hsolve N hrn η (hJV N hrn hη)).1
    have hs := ModulatedHistories.actual_histories_restored W r f E U ha hm hp₂ hf hE hU
      patch hgap b A G (c N) N η X hX (hApos η).ne' (hpatchU η hη) (hpatchE η hη) hmom
    apply sub_eq_zero.mp
    rw [ModulatedHistories.profileRows_sub (profileRepair (P N) patch A (c N) hA (hc N)) Q (hP0 N)]
    change ModulatedHistories.axisHistory
      (ModulatedHistories.applyRepairF patch A (c N) (P N).f)
      (ModulatedHistories.applyRepairU patch A (c N) (P N).U) (X, η) -
      ModulatedHistories.axisHistory Q.f Q.U (X, η) = 0
    rw [hPf N, hPU N, hQf, hQU, hs, sub_self]
  · intro p hp
    exact shears_unchanged_outside _ (P N) patch A (c N) rfl rfl hp

end Repaired

end NavierStokes.ModulatedCone
