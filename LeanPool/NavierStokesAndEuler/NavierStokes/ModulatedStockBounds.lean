/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActivationStocks
public import LeanPool.NavierStokesAndEuler.NavierStokes.JetBounds

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
    nlinarith
  obtain ⟨hf, hU, hH⟩ := hdata n hn₀ hn1 p hp
  obtain ⟨hPpos, hs₁, hs₂⟩ := hb (P n) p hp (hSD' hp) (Cdata / n)
    (div_nonneg hCdata hnpos.le) hsmall hf hU hH
  exact ⟨hPpos, by simpa only [mul_div_assoc] using hs₁, by simpa only [mul_div_assoc] using hs₂⟩

end NavierStokes.ModulatedStockBounds
