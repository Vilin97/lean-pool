/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalResidualJetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialization

@[expose] public section

/-!
# Actual polar graph coverage of the nominal active annulus

The geometric hypotheses are the nominal closed active annulus and the strict
dyadic choice q ≤ Q n < 2 * q. Chart coverage is a conclusion. The native
open domain allows every positive radius and retains the actual slow region;
the smaller weighted strip is reached through its closure at radial endpoints.
-/

noncomputable section

namespace NavierStokes.ActualPolarCoverage

open Set Function Filter ProblemStatement CorrectionInitialization
open PhysicalWaveSum PhysicalGraphBounds PhysicalMeanJetBounds
open scoped Topology

abbrev Point := PhysicalMeanJetBounds.Point
abbrev Cylinder := PhysicalResidualJetBounds.Cylinder

noncomputable def active : Set SpaceTime :=
  {w | (SlowBorelBase.cartesianChart ActualPrimary.h w).2.1 ∈
    Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
      (NominalConeAssembly.activeRight ActualPrimary.nominal)}

noncomputable def inner : ℝ :=
  PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4

noncomputable def outer : ℝ :=
  2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal

noncomputable def nativeDomain : Set Cylinder :=
  HarmonicResidual.liftDomain
    (ActualInitialization.geometry.domain ∩ {x : Point | 0 < x.1})

theorem inner_pos : 0 < inner :=
  div_pos (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal) (by norm_num)

theorem outer_pos : 0 < outer :=
  mul_pos (by norm_num) (PrimaryTargetBounds.rightRadius_pos ActualPrimary.nominal)

theorem inner_lt_outer : inner < outer := by
  have ha := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  have hab := PrimaryTargetBounds.radii_ordered ActualPrimary.nominal
  change PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4 <
    2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal
  linarith

theorem nativeDomain_open : IsOpen nativeDomain :=
  HarmonicResidual.liftDomain_open
    (ActualInitialization.geometry.domain_open.inter
      (isOpen_lt continuous_const continuous_fst))

theorem nativeDomain_radius_pos {x : Cylinder} (hx : x ∈ nativeDomain) :
    0 < x.1.1 := hx.1.2

theorem nativeDomain_radius_ne {x : Cylinder} (hx : x ∈ nativeDomain) :
    x.1.1 ≠ 0 := (nativeDomain_radius_pos hx).ne'

/-! ## Scale identities independent of the particular actual profile -/

theorem graph_radius_nonneg (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    0 ≤ (graph h n d w).1 := by
  rw [graph_radius]
  exact PolarCharts.radius_nonneg _

theorem graph_radius_sq (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    (graph h n d w).1 ^ 2 =
      (w.2 0 ^ 2 + w.2 1 ^ 2) / ChartScales.Q n := by
  rw [graph_radius, PolarCharts.radius_sq]
  have hs : (ChartScales.Q n ^ (-(1 / 2 : ℝ))) ^ 2 =
      (ChartScales.Q n)⁻¹ := by
    rw [← Real.rpow_mul_natCast (ChartScales.Q_pos n).le]
    norm_num [Real.rpow_neg_one]
  change (ChartScales.Q n ^ (-(1 / 2 : ℝ)) * w.2 0) ^ 2 +
    (ChartScales.Q n ^ (-(1 / 2 : ℝ)) * w.2 1) ^ 2 = _
  calc
    _ = (ChartScales.Q n ^ (-(1 / 2 : ℝ))) ^ 2 *
        (w.2 0 ^ 2 + w.2 1 ^ 2) := by ring
    _ = _ := by rw [hs]; ring

theorem graph_profileRadius_sq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal) :
    ((graph h n d w).1 /
      VariableGaugeMean.qLength (2 * h) (graph h n d w).2.1) ^ 2 / 2 =
        (SlowBorelBase.cartesianChart h w).2.1 := by
  have hq := physicalQ_pos hh hh1 hw
  have hQ := ChartScales.Q_pos n
  have hqc : 0 < SimilarityCoordinates.coordinateQ (2 * h) (graph h n d w).2.1 := by
    rw [graph_q_eq hh hh1 n d hw]
    exact div_pos hq hQ
  change ((graph h n d w).1 /
    Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) (graph h n d w).2.1)) ^ 2 / 2 = _
  rw [div_pow, Real.sq_sqrt hqc.le, graph_radius_sq, graph_q_eq hh hh1 n d hw]
  change ((w.2 0 ^ 2 + w.2 1 ^ 2) / ChartScales.Q n /
    (physicalQ h w / ChartScales.Q n)) / 2 =
      ((w.2 0 ^ 2 + w.2 1 ^ 2) / 2) / physicalQ h w
  rw [div_div_div_cancel_right₀ hQ.ne']
  ring

theorem graph_profileRadius_mem {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) (n d : ℕ) {w : SpaceTime}
    (hw : w ∈ preterminal)
    (hactive : (SlowBorelBase.cartesianChart F.data.h w).2.1 ∈
      Icc (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)) :
    (graph F.data.h n d w).1 /
      VariableGaugeMean.qLength (2 * F.data.h) (graph F.data.h n d w).2.1 ∈
        Icc (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W) := by
  have hsq := graph_profileRadius_sq F.data.h_pos F.data.h_lt_half n d hw
  have hr := div_nonneg (graph_radius_nonneg F.data.h n d w)
    (graph_length_pos F.data.h_pos F.data.h_lt_half n d hw).le
  have ha := PrimaryTargetBounds.leftRadius_pos W
  have hb := PrimaryTargetBounds.rightRadius_pos W
  have hasq : PrimaryTargetBounds.leftRadius W ^ 2 =
      2 * NominalConeAssembly.activeLeft W :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos W).le)
  have hbsq : PrimaryTargetBounds.rightRadius W ^ 2 =
      2 * NominalConeAssembly.activeRight W :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos W).le)
  constructor
  · apply (sq_le_sq₀ ha.le hr).mp
    nlinarith [hactive.1]
  · apply (sq_le_sq₀ hr hb.le).mp
    nlinarith [hactive.2]

/-! ## Closure of a moving strip, including both radial endpoints -/

theorem mem_closure_strip (G : SignedMeanGain.Geometry) {x : Point}
    (hx : x ∈ G.domain)
    (hr : (LocalSignedRequest.profileMap G.coord x).1 ∈ Icc G.patch.a G.patch.b) :
    x ∈ closure G.strip.domain := by
  let ell := Real.sqrt (MeanRankUpdate.chartQ G.coord x)
  have hell : 0 < ell := Real.sqrt_pos.mpr (G.region.chartQ_pos hx)
  let f : ℝ → Point := fun r => (r * ell, x.2)
  have hf : Continuous f := (continuous_id.mul continuous_const).prodMk continuous_const
  have hmaps : MapsTo f (Ioo G.patch.a G.patch.b) G.strip.domain := by
    intro r hr
    apply (LocalSignedRequest.movingStrip_domain G.region G.patch.a G.patch.b
      G.leftWeight G.rightWeight G.patch.a_pos G.left_pos G.right_pos G.epsilon G.slow
      G.epsilon_pos G.epsilon_le_one G.slow_ge_one (f r)).mpr
    refine ⟨hx, ?_⟩
    change r * ell / ell ∈ Ioo G.patch.a G.patch.b
    simpa only [mul_div_cancel_right₀ _ hell.ne'] using hr
  have hrcl : x.1 / ell ∈ closure (Ioo G.patch.a G.patch.b) := by
    rw [closure_Ioo G.patch.a_lt_b.ne]
    exact hr
  have hfcl := hf.continuousAt.continuousWithinAt.mem_closure hrcl hmaps
  have hfx : f (x.1 / ell) = x := by
    dsimp only [f]
    rw [div_mul_cancel₀ _ hell.ne']
  rwa [hfx] at hfcl

theorem mem_closure_liftStrip (G : SignedMeanGain.Geometry) {x : Point}
    (hx : x ∈ G.domain)
    (hr : (LocalSignedRequest.profileMap G.coord x).1 ∈ Icc G.patch.a G.patch.b)
    (theta : ℝ) :
    (x, theta) ∈ closure (HarmonicResidual.liftDomain G.strip.domain) := by
  have hc := mem_closure_strip G hx hr
  have hf : Continuous (fun y : Point => (y, theta)) :=
    continuous_id.prodMk continuous_const
  exact hf.continuousAt.continuousWithinAt.mem_closure hc
    (fun y hy => ⟨hy, Set.mem_univ theta⟩)

/-! ## The actual selected band belongs to the native slow window -/

theorem graph_slow_mem_standard {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hqQ : physicalQ h w ≤ ChartScales.Q n)
    (hQq : ChartScales.Q n < 2 * physicalQ h w) :
    (graph h n d w).2.1 ∈ (ActualSignedGeometry.standardSlowRegion hh hh1).carrier := by
  change 0 < (graph h n d w).2.1.1 ∧
    SimilarityCoordinates.coordinateQ (2 * h) (graph h n d w).2.1 ∈ Ioo (1 / 2 : ℝ) 2
  refine ⟨graph_time_pos h n d hw, ?_⟩
  rw [graph_q_eq hh hh1 n d hw]
  have hQ := ChartScales.Q_pos n
  constructor
  · apply (lt_div_iff₀ hQ).mpr
    linarith
  · apply (div_lt_iff₀ hQ).mpr
    linarith

theorem selected_mean_domain (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hqQ : physicalQ ActualPrimary.h w ≤ ChartScales.Q n)
    (hQq : ChartScales.Q n < 2 * physicalQ ActualPrimary.h w) :
    graph ActualPrimary.h n d w ∈ ActualInitialization.geometry.domain :=
  graph_slow_mem_standard ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n d hw hqQ hQq

theorem selected_mean_radius_pos (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hactive : w ∈ active) : 0 < (graph ActualPrimary.h n d w).1 := by
  have hr := graph_profileRadius_mem ActualPrimary.nominal n d hw hactive
  have hell := graph_length_pos ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n d hw
  exact (mul_pos (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal) hell).trans_le
    ((le_div_iff₀ hell).mp hr.1)

theorem selected_annulus (n : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hactive : w ∈ active)
    (hqQ : physicalQ ActualPrimary.h w ≤ ChartScales.Q n)
    (hQq : ChartScales.Q n < 2 * physicalQ ActualPrimary.h w) :
    scaledRadial n w ∈ annulus inner outer := by
  have hq := physicalQ_pos ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half hw
  have hlo : physicalQ ActualPrimary.h w / 2 ≤ ChartScales.Q n := by linarith
  have hell := graph_length_pos ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n 0 hw
  have hlen := graph_length_bounds ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half n 0 hw hlo hQq.le
  have hr := graph_profileRadius_mem ActualPrimary.nominal n 0 hw hactive
  have hloR := (le_div_iff₀ hell).mp hr.1
  have hhiR := (div_le_iff₀ hell).mp hr.2
  have ha := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  have hb := PrimaryTargetBounds.rightRadius_pos ActualPrimary.nominal
  have hRlo : PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 2 ≤
      (graph ActualPrimary.h n 0 w).1 := by nlinarith [hlen.1]
  have hRhi : (graph ActualPrimary.h n 0 w).1 ≤
      2 * PrimaryTargetBounds.rightRadius ActualPrimary.nominal := by nlinarith [hlen.2]
  rw [graph_radius] at hRlo hRhi
  refine ⟨?_, ?_⟩
  · simpa only [outer, Metric.mem_closedBall, dist_zero_right] using
      (PolarCharts.norm_le_radius (scaledRadial n w)).trans hRhi
  · change PrimaryTargetBounds.leftRadius ActualPrimary.nominal / 4 ≤ ‖scaledRadial n w‖
    linarith only [hRlo, PolarCharts.radius_le_two_norm (scaledRadial n w)]

theorem selected_chart_exists (n : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hactive : w ∈ active)
    (hqQ : physicalQ ActualPrimary.h w ≤ ChartScales.Q n)
    (hQq : ChartScales.Q n < 2 * physicalQ ActualPrimary.h w) :
    ∃ j : PolarCharts.Index, scaledRadial n w ∈ PolarCharts.chartDomain inner j := by
  obtain ⟨j, hj⟩ := PolarCharts.annulus_covered inner_pos
    (selected_annulus n hw hactive hqQ hQq)
  exact ⟨j, PolarCharts.sector_subset_chartDomain inner_pos j hj⟩

theorem selected_polar_nativeDomain (j : PolarCharts.Index) (n d : ℕ)
    {w : SpaceTime} (hw : w ∈ preterminal) (hactive : w ∈ active)
    (hqQ : physicalQ ActualPrimary.h w ≤ ChartScales.Q n)
    (hQq : ChartScales.Q n < 2 * physicalQ ActualPrimary.h w)
    (hj : scaledRadial n w ∈ PolarCharts.chartDomain inner j) :
    PhysicalResidualJetBounds.polarGraph inner ActualPrimary.h j n d w ∈ nativeDomain := by
  rw [PhysicalResidualJetBounds.polarGraph_eq_meanGraph inner_pos ActualPrimary.h j n d hj]
  exact ⟨⟨selected_mean_domain n d hw hqQ hQq, selected_mean_radius_pos n d hw hactive⟩,
    Set.mem_univ _⟩

theorem selected_polar_closure (j : PolarCharts.Index) (n d : ℕ)
    {w : SpaceTime} (hw : w ∈ preterminal) (hactive : w ∈ active)
    (hqQ : physicalQ ActualPrimary.h w ≤ ChartScales.Q n)
    (hQq : ChartScales.Q n < 2 * physicalQ ActualPrimary.h w)
    (hj : scaledRadial n w ∈ PolarCharts.chartDomain inner j) :
    PhysicalResidualJetBounds.polarGraph inner ActualPrimary.h j n d w ∈
      closure (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain) := by
  rw [PhysicalResidualJetBounds.polarGraph_eq_meanGraph inner_pos ActualPrimary.h j n d hj]
  apply mem_closure_liftStrip ActualInitialization.geometry
    (selected_mean_domain n d hw hqQ hQq)
  change (graph ActualPrimary.h n d w).1 /
    VariableGaugeMean.qLength (2 * ActualPrimary.h) (graph ActualPrimary.h n d w).2.1 ∈
      Icc (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
        (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
  exact graph_profileRadius_mem ActualPrimary.nominal n d hw hactive

/-! ## Selection above an arbitrary certified floor -/

theorem exists_selected_band (N : ℕ) {w : SpaceTime}
    (hw : w ∈ preterminal) (hactive : w ∈ active)
    (hsmall : physicalQ ActualPrimary.h w ≤ ChartScales.Q N) :
    ∃ n : ℕ, N ≤ n ∧ physicalQ ActualPrimary.h w ≤ ChartScales.Q n ∧
      ChartScales.Q n < 2 * physicalQ ActualPrimary.h w ∧
      scaledRadial n w ∈ annulus inner outer ∧
      ∀ (j : PolarCharts.Index) (d : ℕ),
        scaledRadial n w ∈ PolarCharts.chartDomain inner j →
          PhysicalResidualJetBounds.polarGraph inner ActualPrimary.h j n d w ∈ nativeDomain ∧
          PhysicalResidualJetBounds.polarGraph inner ActualPrimary.h j n d w ∈
            closure (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain) := by
  obtain ⟨n, hn, hqQ, hQq⟩ := exists_comparable_band N
    (physicalQ_pos ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half hw)
    hsmall
  refine ⟨n, hn, hqQ, hQq, selected_annulus n hw hactive hqQ hQq, ?_⟩
  intro j d hj
  exact ⟨selected_polar_nativeDomain j n d hw hactive hqQ hQq hj,
    selected_polar_closure j n d hw hactive hqQ hQq hj⟩

theorem exists_selected_band_of_qbig (firstBand : ℕ) {qbig : ℝ} {w : SpaceTime}
    (hw : w ∈ preterminal) (hactive : w ∈ active)
    (hsmall : physicalQ ActualPrimary.h w ≤ qbig)
    (hfloor : qbig ≤ ChartScales.Q firstBand) :
    ∃ n : ℕ, firstBand ≤ n ∧ physicalQ ActualPrimary.h w ≤ ChartScales.Q n ∧
      ChartScales.Q n < 2 * physicalQ ActualPrimary.h w ∧
      scaledRadial n w ∈ annulus inner outer ∧
      ∀ (j : PolarCharts.Index) (d : ℕ),
        scaledRadial n w ∈ PolarCharts.chartDomain inner j →
          PhysicalResidualJetBounds.polarGraph inner ActualPrimary.h j n d w ∈ nativeDomain ∧
          PhysicalResidualJetBounds.polarGraph inner ActualPrimary.h j n d w ∈
            closure (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain) :=
  exists_selected_band firstBand hw hactive (hsmall.trans hfloor)

end NavierStokes.ActualPolarCoverage
