/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.AbelWeak.PlanarLogBranch
import LeanPool.JacobianDiffgeo.PlanarStokes.AnnulusResidue
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# abel-theorem: the planar log piece and its residue identity (design §4.1 step 5, planar core)

Unit: abel-theorem. Namespace `RS.Abel`. Pure `ℂ → ℂ`, no manifold imports.

`LogPieceData` packages one planar weak-solution piece exactly as `AbelWeak/SingleChart.lean`
builds it: inside `ball c ρ` the rational function `(z - β)/(z - α)` (simple zero at `β`, simple
pole at `α`), interpolated to `1` across the bump annulus `ρ < rIn ≤ ‖z - c‖ ≤ rOut` through
`exp (χ · L)` with `L` the exterior log branch (`exists_exteriorLogBranch`). Exports:

* `g` — the piece itself, with the `SingleChart`-style facts (`g_eqOn_inner`, `g_one`,
  `g_contDiffAt`, `g_ne_zero`) plus the punctured-limit factorizations `tendsto_zero_factor` /
  `tendsto_pole_factor` (feeding the order bookkeeping of `UpgradeDischarge.lean`);
* `dlog` — the `(0,1)` logarithmic-derivative coefficient `h = dbar(χL)`, globally smooth,
  compactly supported in the closed bump annulus, with `dbarg = h · g` off `{α, β}`
  (`wirtingerDbar_g`);
* **`integral_dlog_mul`** — Forster's Lemma 20.3/20.5 in planar form: for any holomorphic
  primitive pair `Gp' = w` on a ball containing the piece,
  `∫ h·w dA = π (Gp β - Gp α)` — the annulus-Stokes atom
  (`circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar`) reduces the area
  integral to `-∮ L·w` over the inner circle, integration by parts along the circle
  (`circleIntegral.integral_eq_zero_of_hasDerivWithinAt`) trades `L·w` for the two-pole kernel
  `((z-β)⁻¹ - (z-α)⁻¹)·Gp`, and the Cauchy integral formula
  (`DiffContOnCl.circleIntegral_sub_inv_smul`) evaluates it.
-/

open scoped ContDiff
open Complex Metric Set MeasureTheory Filter Topology

noncomputable section

namespace RS.Abel

/-- One planar log piece: zero at `β`, pole at `α`, both inside `ball c ρ`, with a fixed
exterior log branch `L` and bump `χ`. -/
structure LogPieceData where
  /-- The chart-ball center. -/
  c : ℂ
  /-- The inner radius enclosing the two divisor points. -/
  ρ : ℝ
  hρ : 0 < ρ
  /-- The pole. -/
  α : ℂ
  /-- The zero. -/
  β : ℂ
  hne : α ≠ β
  hα : α - c ∈ ball (0 : ℂ) ρ
  hβ : β - c ∈ ball (0 : ℂ) ρ
  /-- The interpolation bump (recentred at `0`). -/
  χ : ContDiffBump (0 : ℂ)
  hρχ : ρ < χ.rIn
  /-- The exterior log branch of `(z - (β - c))/(z - (α - c))` on `{ρ < ‖z‖}`. -/
  L : ℂ → ℂ
  hL : ∀ z : ℂ, ρ < ‖z‖ → HasDerivAt L (1 / (z - (β - c)) - 1 / (z - (α - c))) z
  hLexp : ∀ z : ℂ, ρ < ‖z‖ → Complex.exp (L z) = (z - (β - c)) / (z - (α - c))

namespace LogPieceData

variable (P : LogPieceData)

theorem hρOut : P.ρ < P.χ.rOut := P.hρχ.trans P.χ.rIn_lt_rOut

/-- The piece. -/
def g : ℂ → ℂ := fun z =>
  if ‖z - P.c‖ ≤ P.ρ then (z - P.β) / (z - P.α)
  else Complex.exp ((P.χ (z - P.c) : ℝ) * P.L (z - P.c))

/-- The recentred branch composite and its derivative. -/
theorem hasDerivAt_L_sub {z : ℂ} (hz : P.ρ < ‖z - P.c‖) :
    HasDerivAt (fun w => P.L (w - P.c)) (1 / (z - P.β) - 1 / (z - P.α)) z := by
  have h1 := (P.hL (z - P.c) hz).comp z ((hasDerivAt_id z).sub_const P.c)
  have h2 : (1 / (z - P.c - (P.β - P.c)) - 1 / (z - P.c - (P.α - P.c))) * 1
      = 1 / (z - P.β) - 1 / (z - P.α) := by
    rw [mul_one, sub_sub_sub_cancel_right, sub_sub_sub_cancel_right]
  rwa [h2] at h1

theorem exp_L_sub {z : ℂ} (hz : P.ρ < ‖z - P.c‖) :
    Complex.exp (P.L (z - P.c)) = (z - P.β) / (z - P.α) := by
  have := P.hLexp (z - P.c) hz
  rw [this, sub_sub_sub_cancel_right, sub_sub_sub_cancel_right]

/-- Consistency on the transition annulus. -/
theorem g_consistent {z : ℂ} (hz1 : P.ρ < ‖z - P.c‖) (hz2 : ‖z - P.c‖ ≤ P.χ.rIn) :
    P.g z = (z - P.β) / (z - P.α) := by
  have hχ1 : P.χ (z - P.c) = 1 := P.χ.one_of_mem_closedBall (by
    simpa [Metric.mem_closedBall] using hz2)
  rw [g, ite_eq_right (not_le.mpr hz1), hχ1]
  rw [show ((1 : ℝ) : ℂ) * P.L (z - P.c) = P.L (z - P.c) by push_cast; ring]
  exact P.exp_L_sub hz1

/-- The piece is `1` far from the center. -/
theorem g_one {z : ℂ} (hz : P.χ.rOut ≤ ‖z - P.c‖) : P.g z = 1 := by
  have hzρ : P.ρ < ‖z - P.c‖ := lt_of_lt_of_le P.hρOut hz
  have hχ0 : P.χ (z - P.c) = 0 := P.χ.zero_of_le_dist (by rw [dist_zero_right]; exact hz)
  rw [g, ite_eq_right (not_le.mpr hzρ), hχ0]
  simp

/-- The piece is the rational function on the whole inner ball. -/
theorem g_eqOn_inner : Set.EqOn P.g (fun z => (z - P.β) / (z - P.α)) (ball P.c P.χ.rIn) := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  by_cases h : ‖z - P.c‖ ≤ P.ρ
  · rw [g, ite_eq_left h]
  · exact P.g_consistent (not_le.mp h) hz.le

/-- The piece agrees with `exp (χ L)` on the exterior region. -/
theorem g_exp {z : ℂ} (hz : P.ρ < ‖z - P.c‖) :
    P.g z = Complex.exp ((P.χ (z - P.c) : ℝ) * P.L (z - P.c)) := by
  rw [g, ite_eq_right (not_le.mpr hz)]

theorem isOpen_exterior : IsOpen {w : ℂ | P.ρ < ‖w - P.c‖} :=
  isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))

theorem mem_exterior {z : ℂ} (hz : P.ρ < ‖z - P.c‖) :
    z ∈ {w : ℂ | P.ρ < ‖w - P.c‖} := hz

theorem notMem_exterior {z : ℂ} (hz : ¬ P.ρ < ‖z - P.c‖) :
    z ∉ {w : ℂ | P.ρ < ‖w - P.c‖} := hz

/-- The bump-log product is real-smooth on the exterior region. -/
theorem contDiffAt_chiL {z : ℂ} (hz : P.ρ < ‖z - P.c‖) :
    ContDiffAt ℝ ∞ (fun w => ((P.χ (w - P.c) : ℝ) : ℂ) * P.L (w - P.c)) z := by
  have hL_diffOn : DifferentiableOn ℂ P.L {w : ℂ | P.ρ < ‖w‖} :=
    fun w hw => (P.hL w hw).differentiableAt.differentiableWithinAt
  have hL_contDiffAt : ContDiffAt ℝ ∞ (fun w : ℂ => P.L (w - P.c)) z := by
    have hLan : AnalyticOnNhd ℂ P.L {w : ℂ | P.ρ < ‖w‖} := hL_diffOn.analyticOnNhd
      (isOpen_lt continuous_const continuous_norm)
    have h1 : ContDiffAt ℂ ∞ P.L (z - P.c) := (hLan (z - P.c) hz).contDiffAt
    exact (h1.restrict_scalars ℝ).comp z (contDiffAt_id.sub contDiffAt_const)
  have hχ_contDiffAt : ContDiffAt ℝ ∞ (fun w : ℂ => ((P.χ (w - P.c) : ℝ) : ℂ)) z := by
    have hsub : ContDiffAt ℝ ∞ (fun w : ℂ => w - P.c) z := contDiffAt_id.sub contDiffAt_const
    have hcomp : ContDiffAt ℝ ∞ ((⇑P.χ) ∘ (fun w : ℂ => w - P.c)) z :=
      P.χ.contDiffAt.comp z hsub
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hcomp
  exact hχ_contDiffAt.mul hL_contDiffAt

/-- Real-smoothness of the piece off the pole. -/
theorem g_contDiffAt {z : ℂ} (hz : z ≠ P.α) : ContDiffAt ℝ ∞ P.g z := by
  by_cases hcase : ‖z - P.c‖ < P.χ.rIn
  · have hzmem : z ∈ ball P.c P.χ.rIn := by rw [Metric.mem_ball, dist_eq_norm]; exact hcase
    have heq : P.g =ᶠ[nhds z] (fun w => (w - P.β) / (w - P.α)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzmem] with w hw using P.g_eqOn_inner hw
    have hdiff : ContDiffAt ℝ ∞ (fun w : ℂ => (w - P.β) / (w - P.α)) z := by
      have h1 : ContDiffAt ℂ ∞ (fun w : ℂ => (w - P.β) / (w - P.α)) z :=
        (contDiffAt_id.sub contDiffAt_const).div (contDiffAt_id.sub contDiffAt_const)
          (sub_ne_zero.mpr hz)
      exact h1.restrict_scalars ℝ
    exact hdiff.congr_of_eventuallyEq heq
  · rw [not_lt] at hcase
    have hzρ : P.ρ < ‖z - P.c‖ := lt_of_lt_of_le P.hρχ hcase
    have heq : P.g =ᶠ[nhds z]
        (fun w => Complex.exp ((P.χ (w - P.c) : ℝ) * P.L (w - P.c))) := by
      filter_upwards [P.isOpen_exterior.mem_nhds (P.mem_exterior hzρ)] with w hw
      exact P.g_exp hw
    have hexp : ContDiffAt ℝ ∞
        (fun w : ℂ => Complex.exp (((P.χ (w - P.c) : ℝ) : ℂ) * P.L (w - P.c))) z :=
      (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp z (P.contDiffAt_chiL hzρ)
    exact hexp.congr_of_eventuallyEq heq

/-- Non-vanishing off the divisor. -/
theorem g_ne_zero {z : ℂ} (hzα : z ≠ P.α) (hzβ : z ≠ P.β) : P.g z ≠ 0 := by
  by_cases hcase : ‖z - P.c‖ ≤ P.ρ
  · rw [g, ite_eq_left hcase]
    exact div_ne_zero (sub_ne_zero.mpr hzβ) (sub_ne_zero.mpr hzα)
  · rw [g, ite_eq_right hcase]
    exact Complex.exp_ne_zero _

theorem g_zero_at_zero : P.g P.β = 0 := by
  have hβmem : ‖P.β - P.c‖ < P.ρ := by
    have := P.hβ
    rwa [mem_ball, dist_zero_right] at this
  rw [g, ite_eq_left hβmem.le, sub_self, zero_div]

/-! ## The `(0,1)` logarithmic-derivative coefficient -/

/-- The `dbar log g` coefficient: `dbar(χ L)` on the exterior region, `0` inside. -/
def dlog : ℂ → ℂ :=
  {w : ℂ | P.ρ < ‖w - P.c‖}.indicator
    (RS.wirtingerDbar (fun w => ((P.χ (w - P.c) : ℝ) : ℂ) * P.L (w - P.c)))

/-- The coefficient vanishes on the inner ball (where `χ ≡ 1` and `L` is holomorphic). -/
theorem dlog_eq_zero_inner {z : ℂ} (hz : ‖z - P.c‖ < P.χ.rIn) : P.dlog z = 0 := by
  by_cases hzρ : P.ρ < ‖z - P.c‖
  · rw [dlog, Set.indicator_of_mem (P.mem_exterior hzρ)]
    -- near `z`, `χ ≡ 1` so `χL = L`, which is holomorphic
    have hev : (fun w => ((P.χ (w - P.c) : ℝ) : ℂ) * P.L (w - P.c)) =ᶠ[nhds z]
        (fun w => P.L (w - P.c)) := by
      have hnear : ∀ᶠ w in nhds z, ‖w - P.c‖ < P.χ.rIn := by
        have hcont : Continuous (fun w : ℂ => ‖w - P.c‖) :=
          continuous_norm.comp (continuous_id.sub continuous_const)
        exact (hcont.tendsto z).eventually (eventually_lt_nhds hz)
      filter_upwards [hnear] with w hw
      rw [P.χ.one_of_mem_closedBall (by simpa [Metric.mem_closedBall] using hw.le)]
      push_cast
      ring
    rw [RS.wirtingerDbar_congr_nhds _ _ z hev]
    exact RS.wirtingerDbar_eq_zero_of_differentiableAt _ _
      ((P.hasDerivAt_L_sub hzρ).differentiableAt)
  · rw [dlog, Set.indicator_of_notMem (P.notMem_exterior hzρ)]

/-- The coefficient vanishes outside the closed bump ball. -/
theorem dlog_eq_zero_outer {z : ℂ} (hz : P.χ.rOut < ‖z - P.c‖) : P.dlog z = 0 := by
  have hzρ : P.ρ < ‖z - P.c‖ := P.hρOut.trans hz
  rw [dlog, Set.indicator_of_mem (P.mem_exterior hzρ)]
  have hev : (fun w => ((P.χ (w - P.c) : ℝ) : ℂ) * P.L (w - P.c)) =ᶠ[nhds z]
      (fun _ => (0 : ℂ)) := by
    have hcont : Continuous (fun w : ℂ => ‖w - P.c‖) :=
      continuous_norm.comp (continuous_id.sub continuous_const)
    have hnear : ∀ᶠ w in nhds z, P.χ.rOut < ‖w - P.c‖ :=
      (hcont.tendsto z).eventually (eventually_gt_nhds hz)
    filter_upwards [hnear] with w hw
    rw [P.χ.zero_of_le_dist (by rw [dist_zero_right]; exact hw.le)]
    push_cast
    ring
  rw [RS.wirtingerDbar_congr_nhds _ _ z hev]
  exact RS.wirtingerDbar_const z 0

/-- The support of the coefficient sits in the closed bump annulus. -/
theorem support_dlog_subset :
    Function.support P.dlog ⊆ closedBall P.c P.χ.rOut \ ball P.c P.χ.rIn := by
  intro z hz
  rw [Function.mem_support] at hz
  constructor
  · rw [Metric.mem_closedBall, dist_eq_norm]
    by_contra hout
    exact hz (P.dlog_eq_zero_outer (not_le.mp hout))
  · rw [Metric.mem_ball, dist_eq_norm]
    intro hin
    exact hz (P.dlog_eq_zero_inner hin)

/-- Global smoothness of the coefficient. -/
theorem contDiff_dlog : ContDiff ℝ ∞ P.dlog := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hcase : ‖z - P.c‖ < P.χ.rIn
  · -- vanishes on the open inner ball
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    have hcont : Continuous (fun w : ℂ => ‖w - P.c‖) :=
      continuous_norm.comp (continuous_id.sub continuous_const)
    have hnear : ∀ᶠ w in nhds z, ‖w - P.c‖ < P.χ.rIn :=
      (hcont.tendsto z).eventually (eventually_lt_nhds hcase)
    filter_upwards [hnear] with w hw
    exact P.dlog_eq_zero_inner hw
  · -- smooth on the exterior region
    have hzρ : P.ρ < ‖z - P.c‖ := lt_of_lt_of_le P.hρχ (not_lt.mp hcase)
    have hev : P.dlog =ᶠ[nhds z]
        (RS.wirtingerDbar (fun w => ((P.χ (w - P.c) : ℝ) : ℂ) * P.L (w - P.c))) := by
      filter_upwards [P.isOpen_exterior.mem_nhds (P.mem_exterior hzρ)] with w hw
      rw [dlog, Set.indicator_of_mem (s := {w : ℂ | P.ρ < ‖w - P.c‖}) hw]
    have hsm : ContDiffOn ℝ ∞
        (RS.wirtingerDbar (fun w => ((P.χ (w - P.c) : ℝ) : ℂ) * P.L (w - P.c)))
        {w : ℂ | P.ρ < ‖w - P.c‖} :=
      RS.contDiffOn_wirtingerDbar _ P.isOpen_exterior
        (fun w hw => (P.contDiffAt_chiL hw).contDiffWithinAt)
    exact ((hsm.contDiffAt (P.isOpen_exterior.mem_nhds hzρ))).congr_of_eventuallyEq hev

/-! ## The exponential chain rule and the logarithmic-derivative identity -/

/-- `dbar(exp v) = exp v · dbarv` for real-differentiable `v`. -/
theorem wirtingerDbar_cexp (v : ℂ → ℂ) (z : ℂ) (hv : DifferentiableAt ℝ v z) :
    RS.wirtingerDbar (fun w => Complex.exp (v w)) z
      = Complex.exp (v z) * RS.wirtingerDbar v z := by
  have hchain : HasFDerivAt (fun w => Complex.exp (v w))
      (Complex.exp (v z) • fderiv ℝ v z) z :=
    (Complex.hasDerivAt_exp (v z)).comp_hasFDerivAt z hv.hasFDerivAt
  rw [RS.wirtingerDbar, RS.wirtingerDbar, hchain.fderiv]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- **The logarithmic-derivative identity**: `dbarg = dlog · g` off the divisor. -/
theorem wirtingerDbar_g {z : ℂ} (hzα : z ≠ P.α) (_hzβ : z ≠ P.β) :
    RS.wirtingerDbar P.g z = P.dlog z * P.g z := by
  by_cases hcase : ‖z - P.c‖ < P.χ.rIn
  · -- the rational region: both sides vanish
    have hzmem : z ∈ ball P.c P.χ.rIn := by rw [Metric.mem_ball, dist_eq_norm]; exact hcase
    have heq : P.g =ᶠ[nhds z] (fun w => (w - P.β) / (w - P.α)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzmem] with w hw using P.g_eqOn_inner hw
    rw [RS.wirtingerDbar_congr_nhds _ _ z heq, P.dlog_eq_zero_inner hcase, zero_mul]
    exact RS.wirtingerDbar_eq_zero_of_differentiableAt _ _
      (((differentiableAt_id.sub (differentiableAt_const _)).div
        (differentiableAt_id.sub (differentiableAt_const _))
        (sub_ne_zero.mpr hzα)))
  · -- the exponential region
    have hzρ : P.ρ < ‖z - P.c‖ := lt_of_lt_of_le P.hρχ (not_lt.mp hcase)
    have heq : P.g =ᶠ[nhds z]
        (fun w => Complex.exp (((P.χ (w - P.c) : ℝ) : ℂ) * P.L (w - P.c))) := by
      filter_upwards [P.isOpen_exterior.mem_nhds (P.mem_exterior hzρ)] with w hw
      rw [P.g_exp hw]
    have hv : DifferentiableAt ℝ (fun w => ((P.χ (w - P.c) : ℝ) : ℂ) * P.L (w - P.c)) z :=
      (P.contDiffAt_chiL hzρ).differentiableAt (by norm_num)
    rw [RS.wirtingerDbar_congr_nhds _ _ z heq, wirtingerDbar_cexp _ z hv, dlog,
      Set.indicator_of_mem (P.mem_exterior hzρ), P.g_exp hzρ]
    ring

/-! ## Punctured-limit factorizations (order bookkeeping inputs) -/

/-- At the zero `β`: `g(z)/(z - β) → (β - α)⁻¹ ≠ 0`. -/
theorem tendsto_zero_factor :
    Tendsto (fun z => P.g z * (z - P.β)⁻¹) (nhdsWithin P.β {P.β}ᶜ)
      (nhds ((P.β - P.α)⁻¹)) := by
  have hβmem : P.β ∈ ball P.c P.χ.rIn := by
    have := P.hβ
    rw [mem_ball, dist_zero_right] at this
    rw [Metric.mem_ball, dist_eq_norm]
    exact this.trans P.hρχ
  have hev : (fun z => P.g z * (z - P.β)⁻¹) =ᶠ[nhdsWithin P.β {P.β}ᶜ]
      (fun z => (z - P.α)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hβmem)] with z hz1 hz2
    rw [P.g_eqOn_inner hz2]
    have hzβ : z - P.β ≠ 0 := sub_ne_zero.mpr (by simpa using hz1)
    field_simp
  refine Tendsto.congr' hev.symm ?_
  have hcont : ContinuousAt (fun z : ℂ => (z - P.α)⁻¹) P.β := by
    have hne : P.β - P.α ≠ 0 := sub_ne_zero.mpr (Ne.symm P.hne)
    exact ((continuous_id.sub continuous_const).continuousAt).inv₀ hne
  exact hcont.continuousWithinAt.tendsto

/-- At the pole `α`: `g(z)·(z - α) → α - β ≠ 0`. -/
theorem tendsto_pole_factor :
    Tendsto (fun z => P.g z * (z - P.α)) (nhdsWithin P.α {P.α}ᶜ)
      (nhds (P.α - P.β)) := by
  have hαmem : P.α ∈ ball P.c P.χ.rIn := by
    have := P.hα
    rw [mem_ball, dist_zero_right] at this
    rw [Metric.mem_ball, dist_eq_norm]
    exact this.trans P.hρχ
  have hev : (fun z => P.g z * (z - P.α)) =ᶠ[nhdsWithin P.α {P.α}ᶜ]
      (fun z => z - P.β) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hαmem)] with z hz1 hz2
    rw [P.g_eqOn_inner hz2]
    have hzα : z - P.α ≠ 0 := sub_ne_zero.mpr (by simpa using hz1)
    field_simp
  refine Tendsto.congr' hev.symm ?_
  have hcont : ContinuousAt (fun z : ℂ => z - P.β) P.α :=
    (continuous_id.sub continuous_const).continuousAt
  have hval : P.α - P.β ≠ 0 := sub_ne_zero.mpr P.hne
  simpa using hcont.continuousWithinAt.tendsto

/-! ## The residue identity (Forster 20.3/20.5, planar) -/

/-- The two-pole Cauchy atom on the middle circle: the difference of simple poles at `β` and `α`,
integrated against a holomorphic `Gp`, is `2πi (Gp β - Gp α)`. Split out of `integral_dlog_mul`
to keep that proof under the 200-line size we hold ourselves to. -/
private theorem circleIntegral_two_pole {r : ℝ} (hr : P.χ.rOut < r) {Gp : ℂ → ℂ}
    (hGpdiff : DifferentiableOn ℂ Gp (ball P.c r)) {ρ' : ℝ} (hρ'pos : 0 < ρ')
    (hρ'1 : P.ρ < ρ') (hρ'2 : ρ' < P.χ.rIn) :
    (∮ z in C(P.c, ρ'), (1 / (z - P.β) - 1 / (z - P.α)) * Gp z)
      = 2 * (Real.pi : ℂ) * Complex.I * (Gp P.β - Gp P.α) := by
  have hGpcl : DiffContOnCl ℂ Gp (ball P.c ρ') := by
    refine DiffContOnCl.mk (hGpdiff.mono ?_) ((hGpdiff.continuousOn).mono ?_)
    · exact ball_subset_ball (le_of_lt ((hρ'2.trans P.χ.rIn_lt_rOut).trans hr))
    · rw [closure_ball P.c hρ'pos.ne']
      intro z hz
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      exact hz.trans_lt ((hρ'2.trans P.χ.rIn_lt_rOut).trans hr)
  have hβball : P.β ∈ ball P.c ρ' := by
    have := P.hβ
    rw [mem_ball, dist_zero_right] at this
    rw [Metric.mem_ball, dist_eq_norm]
    exact this.trans hρ'1
  have hαball : P.α ∈ ball P.c ρ' := by
    have := P.hα
    rw [mem_ball, dist_zero_right] at this
    rw [Metric.mem_ball, dist_eq_norm]
    exact this.trans hρ'1
  have hβint := hGpcl.circleIntegral_sub_inv_smul hβball
  have hαint := hGpcl.circleIntegral_sub_inv_smul hαball
  -- `ContinuousOn.smul` concludes about `f • g` (pointwise), so the two factors are named
  -- first and combined with `exact`, rather than `refine`d against the lambda form.
  have hGpsph : ContinuousOn Gp (sphere P.c ρ') :=
    (hGpdiff.continuousOn).mono (fun z hz => by
      rw [mem_sphere] at hz
      rw [Metric.mem_ball, hz]
      exact (hρ'2.trans P.χ.rIn_lt_rOut).trans hr)
  have hint1 : CircleIntegrable (fun z => (z - P.β)⁻¹ • Gp z) P.c ρ' := by
    refine ContinuousOn.circleIntegrable hρ'pos.le ?_
    have hinv : ContinuousOn (fun z : ℂ => (z - P.β)⁻¹) (sphere P.c ρ') := by
      refine ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn) ?_
      intro z hz
      rw [mem_sphere, dist_eq_norm] at hz
      refine sub_ne_zero.mpr (fun heq => ?_)
      have hmem := P.hβ
      rw [mem_ball, dist_zero_right] at hmem
      rw [← heq, hz] at hmem
      exact absurd hmem (not_lt.mpr hρ'1.le)
    exact hinv.smul hGpsph
  have hint2 : CircleIntegrable (fun z => (z - P.α)⁻¹ • Gp z) P.c ρ' := by
    refine ContinuousOn.circleIntegrable hρ'pos.le ?_
    have hinv : ContinuousOn (fun z : ℂ => (z - P.α)⁻¹) (sphere P.c ρ') := by
      refine ContinuousOn.inv₀ ((continuous_id.sub continuous_const).continuousOn) ?_
      intro z hz
      rw [mem_sphere, dist_eq_norm] at hz
      refine sub_ne_zero.mpr (fun heq => ?_)
      have hmem := P.hα
      rw [mem_ball, dist_zero_right] at hmem
      rw [← heq, hz] at hmem
      exact absurd hmem (not_lt.mpr hρ'1.le)
    exact hinv.smul hGpsph
  have hcongr : (∮ z in C(P.c, ρ'), (1 / (z - P.β) - 1 / (z - P.α)) * Gp z)
      = (∮ z in C(P.c, ρ'), ((z - P.β)⁻¹ • Gp z - (z - P.α)⁻¹ • Gp z)) := by
    refine circleIntegral.integral_congr hρ'pos.le (fun z _ => ?_)
    simp only [smul_eq_mul, one_div]
    ring
  rw [hcongr, circleIntegral.integral_sub hint1 hint2, hβint, hαint]
  simp only [smul_eq_mul]
  ring

/-- **The residue identity**: for a holomorphic primitive `Gp` of `w` on a ball containing the
whole piece, `∫ dlog · w dA = π (Gp β - Gp α)`. -/
theorem integral_dlog_mul {r : ℝ} (hr : P.χ.rOut < r) {w Gp : ℂ → ℂ}
    (hprim : ∀ z ∈ ball P.c r, HasDerivAt Gp (w z) z) :
    ∫ z : ℂ, P.dlog z * w z = (Real.pi : ℂ) * (Gp P.β - Gp P.α) := by
  -- the middle radius
  set ρ' : ℝ := (P.ρ + P.χ.rIn) / 2 with hρ'_def
  have hρ'1 : P.ρ < ρ' := by rw [hρ'_def]; linarith [P.hρχ]
  have hρ'2 : ρ' < P.χ.rIn := by rw [hρ'_def]; linarith [P.hρχ]
  have hρ'pos : 0 < ρ' := P.hρ.trans hρ'1
  have hρ'out : ρ' ≤ P.χ.rOut := (hρ'2.trans P.χ.rIn_lt_rOut).le
  -- `w` is holomorphic on the ball
  have hGpdiff : DifferentiableOn ℂ Gp (ball P.c r) :=
    fun z hz => (hprim z hz).differentiableAt.differentiableWithinAt
  have hGpan : AnalyticOnNhd ℂ Gp (ball P.c r) := hGpdiff.analyticOnNhd isOpen_ball
  have hw_eq : ∀ z ∈ ball P.c r, deriv Gp z = w z := fun z hz => (hprim z hz).deriv
  have hwan : ∀ z ∈ ball P.c r, AnalyticAt ℂ w z := by
    intro z hz
    exact ((hGpan z hz).deriv).congr (by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      exact hw_eq y hy)
  have hwdiff : ∀ z ∈ ball P.c r, DifferentiableAt ℂ w z := fun z hz =>
    (hwan z hz).differentiableAt
  -- the annulus integrand
  set u : ℂ → ℂ := fun z => ((P.χ (z - P.c) : ℝ) : ℂ) * P.L (z - P.c) * w z with hu_def
  have hmem_ext : ∀ z ∈ closedBall P.c P.χ.rOut \ ball P.c ρ', P.ρ < ‖z - P.c‖ := by
    intro z hz
    have := hz.2
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at this
    exact hρ'1.trans_le this
  have hmem_ball : ∀ z ∈ closedBall P.c P.χ.rOut, z ∈ ball P.c r := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    exact hz.trans_lt hr
  have hu_cd : ContDiffOn ℝ 1 u (closedBall P.c P.χ.rOut \ ball P.c ρ') := by
    intro z hz
    have h1 : ContDiffAt ℝ 1 u z := by
      have hχL : ContDiffAt ℝ 1 (fun w' => ((P.χ (w' - P.c) : ℝ) : ℂ) * P.L (w' - P.c)) z :=
        (P.contDiffAt_chiL (hmem_ext z hz)).of_le (by norm_num)
      have hw1 : ContDiffAt ℝ 1 w z :=
        (hwan z (hmem_ball z hz.1)).contDiffAt.restrict_scalars ℝ
      exact hχL.mul hw1
    exact h1.contDiffWithinAt
  -- the annulus Stokes atom
  have hatom := RS.circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar
    (u := u) (c := P.c) hρ'pos hρ'out hu_cd
  -- outer circle: `u ≡ 0`
  have houter : (∮ z in C(P.c, P.χ.rOut), u z) = 0 := by
    have hEq : Set.EqOn u 0 (sphere P.c P.χ.rOut) := by
      intro z hz
      rw [mem_sphere, dist_eq_norm] at hz
      have hχ0 : P.χ (z - P.c) = 0 :=
        P.χ.zero_of_le_dist (by rw [dist_zero_right, hz])
      simp only [hu_def, hχ0, Pi.zero_apply, Complex.ofReal_zero, zero_mul]
    rw [circleIntegral.integral_congr (le_of_lt (hρ'pos.trans_le hρ'out)) hEq]
    simp [circleIntegral]
  -- inner circle: `u = L·w`
  have hinner : (∮ z in C(P.c, ρ'), u z) = ∮ z in C(P.c, ρ'), P.L (z - P.c) * w z := by
    refine circleIntegral.integral_congr hρ'pos.le (fun z hz => ?_)
    rw [mem_sphere, dist_eq_norm] at hz
    have hχ1 : P.χ (z - P.c) = 1 :=
      P.χ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_zero_right, hz]; exact hρ'2.le)
    simp only [hu_def, hχ1, Complex.ofReal_one, one_mul]
  -- the area integral is `∫ dlog · w`
  have harea : ∫ z in closedBall P.c P.χ.rOut \ ball P.c ρ', RS.wirtingerDbar u z
      = ∫ z : ℂ, P.dlog z * w z := by
    have hmeas : MeasurableSet (closedBall P.c P.χ.rOut \ ball P.c ρ') :=
      (isClosed_closedBall).measurableSet.diff isOpen_ball.measurableSet
    have hEqOn : ∀ z ∈ closedBall P.c P.χ.rOut \ ball P.c ρ',
        RS.wirtingerDbar u z = P.dlog z * w z := by
      intro z hz
      have hzρ := hmem_ext z hz
      have hχLd : DifferentiableAt ℝ (fun w' => ((P.χ (w' - P.c) : ℝ) : ℂ) * P.L (w' - P.c)) z :=
        (P.contDiffAt_chiL hzρ).differentiableAt (by norm_num)
      have hwd : DifferentiableAt ℂ w z := hwdiff z (hmem_ball z hz.1)
      rw [hu_def]
      have := RS.wirtingerDbar_mul_of_differentiableAt (z := z)
        (g := fun w' => ((P.χ (w' - P.c) : ℝ) : ℂ) * P.L (w' - P.c)) (f := w) hχLd hwd
      rw [this, dlog, Set.indicator_of_mem (P.mem_exterior hzρ)]
    rw [MeasureTheory.setIntegral_congr_fun hmeas hEqOn]
    -- extend to the whole plane: the integrand vanishes off the region
    have hzero : ∀ z, z ∉ closedBall P.c P.χ.rOut \ ball P.c ρ' → P.dlog z * w z = 0 := by
      intro z hz
      rw [Set.mem_sdiff, not_and_or] at hz
      rcases hz with hz1 | hz2
      · rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hz1
        rw [P.dlog_eq_zero_outer hz1, zero_mul]
      · rw [not_not] at hz2
        rw [Metric.mem_ball, dist_eq_norm] at hz2
        rw [P.dlog_eq_zero_inner (hz2.trans hρ'2), zero_mul]
    have hind : (fun z => P.dlog z * w z)
        = (closedBall P.c P.χ.rOut \ ball P.c ρ').indicator (fun z => P.dlog z * w z) := by
      funext z
      by_cases hz : z ∈ closedBall P.c P.χ.rOut \ ball P.c ρ'
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hzero z hz]
    conv_rhs => rw [hind]
    rw [MeasureTheory.integral_indicator hmeas]
  -- the circle integration by parts
  have hparts : (∮ z in C(P.c, ρ'), P.L (z - P.c) * w z)
      = -(∮ z in C(P.c, ρ'), (1 / (z - P.β) - 1 / (z - P.α)) * Gp z) := by
    have hsphere_ball : (sphere P.c ρ' : Set ℂ) ⊆ ball P.c r := by
      intro z hz
      rw [mem_sphere] at hz
      rw [Metric.mem_ball, hz]
      exact (hρ'2.trans P.χ.rIn_lt_rOut).trans hr
    have hsphere_ext : ∀ z ∈ (sphere P.c ρ' : Set ℂ), P.ρ < ‖z - P.c‖ := by
      intro z hz
      rw [mem_sphere, dist_eq_norm] at hz
      rw [hz]
      exact hρ'1
    have hderivΦ : ∀ z ∈ (sphere P.c ρ' : Set ℂ),
        HasDerivWithinAt (fun y => P.L (y - P.c) * Gp y)
          ((1 / (z - P.β) - 1 / (z - P.α)) * Gp z + P.L (z - P.c) * w z)
          (sphere P.c ρ') z := by
      intro z hz
      exact (((P.hasDerivAt_L_sub (hsphere_ext z hz)).mul
        (hprim z (hsphere_ball hz)))).hasDerivWithinAt
    have hzero := circleIntegral.integral_eq_zero_of_hasDerivWithinAt hρ'pos.le hderivΦ
    -- split the vanishing integral
    have hint1 : CircleIntegrable (fun z => (1 / (z - P.β) - 1 / (z - P.α)) * Gp z) P.c ρ' := by
      refine ContinuousOn.circleIntegrable hρ'pos.le ?_
      refine ContinuousOn.mul ?_ ((hGpdiff.continuousOn).mono hsphere_ball)
      refine ContinuousOn.sub ?_ ?_ <;>
      · refine ContinuousOn.div continuousOn_const
          ((continuous_id.sub continuous_const).continuousOn) ?_
        intro z hz
        rw [mem_sphere, dist_eq_norm] at hz
        refine sub_ne_zero.mpr (fun heq => ?_)
        first
        | (have hmem := P.hβ
           rw [mem_ball, dist_zero_right] at hmem
           rw [← heq] at hmem
           rw [hz] at hmem
           exact absurd hmem (not_lt.mpr hρ'1.le))
        | (have hmem := P.hα
           rw [mem_ball, dist_zero_right] at hmem
           rw [← heq] at hmem
           rw [hz] at hmem
           exact absurd hmem (not_lt.mpr hρ'1.le))
    have hint2 : CircleIntegrable (fun z => P.L (z - P.c) * w z) P.c ρ' := by
      refine ContinuousOn.circleIntegrable hρ'pos.le ?_
      refine ContinuousOn.mul ?_ ?_
      · intro z hz
        exact ((P.hasDerivAt_L_sub (hsphere_ext z hz)).differentiableAt.restrictScalars
          ℝ).continuousAt.continuousWithinAt
      · intro z hz
        exact (hwdiff z (hsphere_ball hz)).continuousAt.continuousWithinAt
    have hsplit := circleIntegral.integral_add hint1 hint2
    linear_combination hzero - hsplit
  -- the Cauchy formula evaluation
  have hcauchy := circleIntegral_two_pole P hr hGpdiff hρ'pos hρ'1 hρ'2
  -- assemble
  rw [houter, hinner, hparts, hcauchy, harea] at hatom
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  apply mul_left_cancel₀ hI
  linear_combination -hatom

end LogPieceData

end RS.Abel

end
