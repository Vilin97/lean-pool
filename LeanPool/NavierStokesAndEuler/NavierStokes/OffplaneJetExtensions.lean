/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.GenericEndpointExtension
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedDiagonalExtensions
public import LeanPool.NavierStokesAndEuler.NavierStokes.CutStageEstimates
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhysicalStageBounds

@[expose] public section

/-!
# Off-plane endpoint extensions from actual raw jets

A compact spacetime localization converts bounds on every actual derivative
in a past half-ball into a genuine smooth extension.  The physical scale is
then localized away from zero, so raw power-logarithmic jet bounds supply
the required estimates without a recursive continuation assumption.
-/

noncomputable section

namespace NavierStokes.OffplaneJetExtensions

open Set Function Filter Metric ProblemStatement
open scoped Topology ContDiff BigOperators

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

noncomputable def pastBall (x : Space) (r : ℝ) : Set SpaceTime :=
  Metric.ball (1, x) r ∩ SpacetimeEndpoint.openPast 1

theorem pastBall_open (x : Space) (r : ℝ) : IsOpen (pastBall x r) :=
  isOpen_ball.inter (SpacetimeEndpoint.openPast_isOpen 1)

noncomputable def localBump (x : Space) {r : ℝ} (hr : 0 < r) : ContDiffBump ((1 : ℝ), x) where
  rIn := r / 4
  rOut := r / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem localBump_support (x : Space) {r : ℝ} (hr : 0 < r) :
    tsupport (localBump x hr) ⊆ Metric.ball ((1 : ℝ), x) r := by
  rw [(localBump x hr).tsupport_eq]
  exact Metric.closedBall_subset_ball (by change r / 2 < r; linarith)

theorem localBump_jet_bounded (x : Space) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SpaceTime, ‖iteratedFDeriv ℝ m (localBump x hr) w‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((localBump x hr).hasCompactSupport.iteratedFDeriv (𝕜 := ℝ)
    m).exists_bound_of_continuous
    ((localBump x hr).contDiff.continuous_iteratedFDeriv (nat_le_infty m))
  exact ⟨max C 0, le_max_right _ _, fun w => (hC w).trans (le_max_left _ _)⟩

section LocalExtension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def localized (f : SpaceTime → V) (x : Space) {r : ℝ} (hr : 0 < r)
    (w : SpaceTime) : V := localBump x hr w • f w

theorem localized_zero_germ (f : SpaceTime → V) (x : Space) {r : ℝ} (hr : 0 < r)
    {w : SpaceTime} (hw : w ∉ tsupport (localBump x hr)) :
    localized f x hr =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hw] with z hz
  simp only [localized, hz, Pi.zero_apply, zero_smul]

theorem localized_smooth {f : SpaceTime → V} {x : Space} {r : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (pastBall x r)) :
    ContDiffOn ℝ ∞ (localized f x hr) GenericEndpointExtension.openStrip := by
  intro w hw
  by_cases hs : w ∈ tsupport (localBump x hr)
  · have hlocal : w ∈ pastBall x r :=
      ⟨localBump_support x hr hs, hw.1.2, mem_univ _⟩
    exact (((localBump x hr).contDiff.contDiffAt).smul
      (hf.contDiffAt ((pastBall_open x r).mem_nhds hlocal))).contDiffWithinAt
  · exact ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : SpaceTime => (0 : V))
    w).congr_of_eventuallyEq
      (localized_zero_germ f x hr hs)).contDiffWithinAt

theorem localized_jets_bounded {f : SpaceTime → V} {x : Space} {r : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (pastBall x r))
    (hb : ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ pastBall x r, ‖iteratedFDeriv ℝ m f w‖ ≤ C) :
    ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ GenericEndpointExtension.openStrip,
      ‖iteratedFDeriv ℝ m (localized f x hr) w‖ ≤ C := by
  choose A hA using hb
  choose C hC hCb using localBump_jet_bounded x hr
  intro m
  let K : ℝ := ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * C i * max (A (m - i)) 0
  have hK : 0 ≤ K := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (le_max_right _ _)
  refine ⟨K, fun w hw => ?_⟩
  by_cases hs : w ∈ tsupport (localBump x hr)
  · have hlocal : w ∈ pastBall x r :=
      ⟨localBump_support x hr hs, hw.1.2, mem_univ _⟩
    have hprod := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ)
      (localBump x hr).contDiff.contDiffOn hf (pastBall_open x r).uniqueDiffOn
      hlocal (nat_le_infty m)
    simp only [iteratedFDerivWithin_of_isOpen _ (pastBall_open x r) hlocal] at hprod
    apply hprod.trans
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hCb i w) (Nat.cast_nonneg _))
      ((hA (m - i) w hlocal).trans (le_max_left _ _))
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC i))
  · have hz : iteratedFDeriv ℝ m (localized f x hr) w = 0 := by
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
        (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (localized_zero_germ f x hr hs)
          m).self_of_nhds
    rw [hz, norm_zero]
    exact hK

variable [CompleteSpace V]

/-- A local bound for every actual joint derivative supplies an actual
smooth extension. Endpoint derivative limits are constructed by the
generic extension theorem; they are not additional inputs. -/
theorem extension_of_local_jets {f : SpaceTime → V} {x : Space} {r : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (pastBall x r))
    (hb : ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ pastBall x r, ‖iteratedFDeriv ℝ m f w‖ ≤ C) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  let g := localized f x hr
  have hg : ContDiffOn ℝ ∞ g GenericEndpointExtension.openStrip := localized_smooth hr hf
  have hgb : ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ GenericEndpointExtension.openStrip,
      ‖iteratedFDeriv ℝ m g w‖ ≤ C := localized_jets_bounded hr hf hb
  refine ⟨{
    value := GenericEndpointExtension.extension g hg hgb
    domain := Metric.ball ((1 : ℝ), x) (r / 4) ∩ {w : SpaceTime | -1 < w.1}
    isOpen := isOpen_ball.inter (isOpen_lt continuous_const continuous_fst)
    mem := ⟨Metric.mem_ball_self (by positivity), by norm_num⟩
    smooth := (GenericEndpointExtension.extension_contDiff hg hgb).contDiffOn
    agrees := ?_ }⟩
  intro w hw
  have hstrip : w ∈ GenericEndpointExtension.openStrip :=
    ⟨⟨hw.1.2, hw.2.1⟩, mem_univ _⟩
  rw [GenericEndpointExtension.extension_eq hg hgb hstrip]
  have hc : localBump x hr w = 1 :=
    (localBump x hr).one_of_mem_closedBall (Metric.mem_closedBall.mpr hw.1.1.le)
  simp only [g, localized, hc, one_smul]

end LocalExtension

section PhysicalScale

/-- One neighborhood controls the physical scale for all derivative
orders. Only the actual past coordinate is used in the conclusion. -/
theorem exists_scale_neighborhood {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : Space} (hx : x 2 ≠ 0)
    (hq : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    ∃ r : ℝ, 0 < r ∧ ∀ w ∈ pastBall x r,
      w ∈ CutStageEstimates.physicalSublevel h qbig ∧
      EndpointCoordinates.endpointRoot (2 * h) (x 2) / 2 < PhysicalWaveSum.physicalQ h w ∧
      |w.1| ≤ 1 := by
  have hp := EndpointCoordinates.endpointRoot_pos (2 * h) hx
  have hlim := MixedDiagonalExtensions.physicalQ_tendsto_endpoint hh hh1 hx
  have he : ∀ᶠ w in 𝓝[SpacetimeEndpoint.openPast 1] (1, x),
      PhysicalWaveSum.physicalQ h w ∈
        Ioo (EndpointCoordinates.endpointRoot (2 * h) (x 2) / 2) qbig :=
    hlim.eventually (isOpen_Ioo.mem_nhds ⟨by linarith, hq⟩)
  obtain ⟨U, hU, hxU, hsub⟩ := mem_nhdsWithin.mp he
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  refine ⟨min r 1, lt_min hr zero_lt_one, ?_⟩
  intro w hw
  have hwU : w ∈ U := hball (ball_subset_ball (min_le_left _ _) hw.1)
  have hscale := hsub ⟨hwU, hw.2⟩
  have hfst : dist w.1 (1 : ℝ) ≤ dist w ((1 : ℝ), x) := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hdist : dist w.1 (1 : ℝ) < 1 :=
    hfst.trans_lt (hw.1.trans_le (min_le_right _ _))
  have htime : 0 < w.1 := by
    rw [Real.dist_eq] at hdist
    have hs := (abs_lt.mp hdist).1
    linarith
  exact ⟨⟨hw.2.1, hscale.2⟩, hscale.1,
    by rw [abs_of_pos htime]; exact hw.2.1.le⟩

/-- Arbitrary real powers and logarithmic losses are uniformly bounded
when the scale lies in a fixed compact subinterval of `(0,∞)`. -/
theorem powerLog_bounded {a : ℝ} (ha : 0 < a) (C p e : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q ∈ Icc a 1,
      C * (1 + |Real.log q|) ^ p * q ^ e ≤ K := by
  have hne : ∀ q ∈ Icc a (1 : ℝ), q ≠ 0 := fun q hq => (ha.trans_le hq.1).ne'
  have hl : ContinuousOn (fun q : ℝ => 1 + |Real.log q|) (Icc a 1) :=
    continuousOn_const.add ((continuousOn_id.log hne).abs)
  have hlne : ∀ q ∈ Icc a (1 : ℝ), (1 + |Real.log q|) ≠ 0 := by
    intro q _
    positivity
  have hc : ContinuousOn (fun q : ℝ => C * (1 + |Real.log q|) ^ p * q ^ e) (Icc a 1) :=
    (continuousOn_const.mul (hl.rpow_const (fun q hq => Or.inl (hlne q hq)))).mul
      (continuousOn_id.rpow_const (fun q hq => Or.inl (hne q hq)))
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max K 0, le_max_right _ _, fun q hq => ?_⟩
  have hk : |C * (1 + |Real.log q|) ^ p * q ^ e| ≤ K := by
    simpa only [Real.norm_eq_abs] using hK q hq
  exact (le_abs_self _).trans (hk.trans (le_max_left _ _))

end PhysicalScale

section PhysicalExtensions

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- A single-field endpoint theorem, including the bounded finite pieces
at stage zero. It assumes only their actual interior jet estimates. -/
theorem extension_of_powerLog_jets {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : qbig ≤ 1) {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ m : ℕ, ∃ C p e : ℝ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      |w.1| ≤ 1 → PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤
        C * (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ p *
          PhysicalWaveSum.physicalQ h w ^ e)
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  obtain ⟨r, hr, hscale⟩ := exists_scale_neighborhood hh hh1 hx hqx
  apply extension_of_local_jets hr (hf.mono (fun w hw => (hscale w hw).1))
  intro m
  obtain ⟨C, p, e, hm⟩ := hb m
  obtain ⟨K, _, hK⟩ := powerLog_bounded (half_pos (EndpointCoordinates.endpointRoot_pos (2 * h)
    hx)) C p e
  refine ⟨K, fun w hw => ?_⟩
  have hs := hscale w hw
  have hq1 : PhysicalWaveSum.physicalQ h w ≤ 1 := hs.1.2.le.trans hqbig
  exact (hm w hs.1 hs.2.2 hq1).trans (hK _ ⟨hs.2.1.le, hq1⟩)

theorem extension_of_power_jets {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : qbig ≤ 1) {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ m : ℕ, ∃ C e : ℝ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ e)
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  apply extension_of_powerLog_jets hh hh1 hqbig hf _ hx hqx
  intro m
  obtain ⟨C, e, hm⟩ := hb m
  refine ⟨C, 0, e, fun w hw _ hq1 => ?_⟩
  simpa only [Real.rpow_zero, mul_one] using hm w hw hq1

/-- Positive raw stages extend directly from `RawStageBounds`. The stage
index hypothesis is retained exactly: no stage-zero estimate is inferred. -/
theorem rawStage_extension {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : qbig ≤ 1) {F : ℕ → SpaceTime → V} {g L : ℕ → ℝ} {C p : ℕ → ℕ → ℝ}
    (hb : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) F g L C p
      (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig))
    {j : ℕ} (hj : 1 ≤ j)
    (hf : ContDiffOn ℝ ∞ (F j) (CutStageEstimates.physicalSublevel h qbig))
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension (F j) x) := by
  apply extension_of_powerLog_jets hh hh1 hqbig hf _ hx hqx
  intro m
  exact ⟨C j m, p j m, g j - L m, fun w hw _ hq1 => hb j hj m w ⟨hw.1, hw⟩ hq1⟩

theorem rawStages_extensions {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : qbig ≤ 1) {F : ℕ → SpaceTime → V} {g L : ℕ → ℝ} {C p : ℕ → ℕ → ℝ}
    (hb : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) F g L C p
      (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig))
    (hf : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (F j) (CutStageEstimates.physicalSublevel h qbig))
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    ∀ j, 1 ≤ j → Nonempty (JointResidualLimits.OneSidedExtension (F j) x) :=
  fun j hj => rawStage_extension hh hh1 hqbig hb hj (hf j hj) hx hqx

end PhysicalExtensions

section Assembly

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Combine, for example, the existing base-gauge extension with the
separately derived extension of the finite initial correction. -/
noncomputable def addExtension {f g : SpaceTime → V} {x : Space}
    (ef : JointResidualLimits.OneSidedExtension f x)
    (eg : JointResidualLimits.OneSidedExtension g x) :
    JointResidualLimits.OneSidedExtension (fun w => f w + g w) x where
  value w := ef.value w + eg.value w
  domain := ef.domain ∩ eg.domain
  isOpen := ef.isOpen.inter eg.isOpen
  mem := ⟨ef.mem, eg.mem⟩
  smooth := (ef.smooth.mono inter_subset_left).add (eg.smooth.mono inter_subset_right)
  agrees := fun w hw => by
    change ef.value w + eg.value w = f w + g w
    rw [ef.agrees ⟨hw.1.1, hw.2⟩, eg.agrees ⟨hw.1.2, hw.2⟩]

theorem extension_add {f g : SpaceTime → V} {x : Space}
    (hf : Nonempty (JointResidualLimits.OneSidedExtension f x))
    (hg : Nonempty (JointResidualLimits.OneSidedExtension g x)) :
    Nonempty (JointResidualLimits.OneSidedExtension (fun w => f w + g w) x) :=
  hf.elim fun ef => hg.elim fun eg => ⟨addExtension ef eg⟩

/-- The constructed stage need only agree with the bounded model on its
actual validity region. The positive scale margin supplies the required
past neighborhood automatically. -/
theorem extension_of_eqOn_sublevel {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f g : SpaceTime → V} (he : EqOn f g (CutStageEstimates.physicalSublevel h qbig))
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig)
    (eg : Nonempty (JointResidualLimits.OneSidedExtension g x)) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  obtain ⟨eg⟩ := eg
  apply MixedDiagonalExtensions.extension_of_eventuallyEq _ eg
  filter_upwards [self_mem_nhdsWithin,
    (MixedDiagonalExtensions.physicalQ_tendsto_endpoint hh hh1 hx).eventually (gt_mem_nhds hqx)]
      with w hw hq
  exact he ⟨hw.1, hq⟩

end Assembly

section FiniteInitialPieces

open ActualPhysicalStageBounds

theorem mean_field_extension {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : qbig ≤ 1)
    (hq : qbig ≤ ChartScales.Q M.firstBand) {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension M.family.field x) := by
  apply extension_of_power_jets hh hh1 hqbig (M.field_smooth hh hh1 hq) _ hx hqx
  intro m
  obtain ⟨C, _, hb⟩ := M.field_bound hh hh1 hq m
  exact ⟨C, h * M.alpha - PhysicalMeanJetBounds.loss degree m, hb⟩

theorem mean_angular_extension {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : qbig ≤ 1)
    (hq : qbig ≤ ChartScales.Q M.firstBand) {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension M.family.angularField x) := by
  apply extension_of_power_jets hh hh1 hqbig (M.angular_smooth hh hh1 hq) _ hx hqx
  intro m
  obtain ⟨C, _, hb⟩ := M.angular_bound hh hh1 hq m
  exact ⟨C, h * M.alpha - PhysicalMeanJetBounds.loss degree m, hb⟩

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}

/-- The finite initialized potential correction has its own derived
estimate. This theorem does not apply the positive-stage bound to index zero. -/
theorem initialIncrement_extension {h qbig : ℝ}
    (W : PhysicalStageBounds.WaveData h D I K (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : qbig ≤ 1)
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand)
    {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension (initialIncrement W MT MR) x) := by
  apply extension_of_power_jets hh hh1 hqbig (initialIncrement_smooth W MT MR hh hh1 hqT hqR) _ hx
    hqx
  intro m
  obtain ⟨C, _, hb⟩ := initialIncrement_bound W MT MR hh hh1 hqT hqR m
  exact ⟨C, -InitializedPhysicalBackground.seedPotentialLoss h W.alpha W.shift (min MT.alpha
    MR.alpha) m, hb⟩

theorem initialPressureIncrement_extension {h qbig : ℝ}
    (W : PhysicalStageBounds.WaveData h D I K Unit)
    (M : MeanInput h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : qbig ≤ 1)
    (hq : qbig ≤ ChartScales.Q M.firstBand) {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension (initialPressureIncrement W M) x) := by
  apply extension_of_power_jets hh hh1 hqbig (initialPressureIncrement_smooth W M hh hh1 hq) _ hx
    hqx
  intro m
  obtain ⟨C, _, hb⟩ := initialPressureIncrement_bound W M hh hh1 hq m
  exact ⟨C, -initialPressureLoss h W.alpha W.shift M.alpha m, hb⟩

end FiniteInitialPieces

end NavierStokes.OffplaneJetExtensions
