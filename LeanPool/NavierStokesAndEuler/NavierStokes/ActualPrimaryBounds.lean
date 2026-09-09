/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionInitialization
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalizedWaveBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformBlockBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhaseDefect

@[expose] public section

/-!
# Uniform estimates for the chosen primary waves

All fields below use `ActualPrimary.choice`.
The estimates retain the moving edge weight and the actual pulse envelope.
Constants precede the orientation, spatial label, band, and lattice copy.
-/

noncomputable section

namespace NavierStokes.ActualPrimaryBounds

open Set Function Filter WeightedClasses PhaseJetBounds PrimaryCopyBounds
open CorrectionInitialization
open scoped ContDiff Topology BigOperators


abbrev Native := ActualSignedGeometry.Native
abbrev Point := LocalSignedRequest.Point

noncomputable def region : LocalSignedRequest.SlowRegion (2 * ActualPrimary.h) :=
  ActualSignedGeometry.standardSlowRegion ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half

noncomputable def strip : StripData Point := BaseContextAssembly.nativeStrip ActualPrimary.nominal
  region

noncomputable def nativeStrip : StripData Native := ActualSignedGeometry.viewStrip
  ActualPrimary.nominal region id

abbrev SignedLabel (B N0 : ℕ) := Fin 2 × ActualPrimary.Label B N0

section NativeBounds

variable (B N0 : ℕ)

/-- The outer slot localization is differentiated before periodization. -/
theorem outer_velocity_jets (j : Fin 2) :
    NativeJets (NativeBandExtension.radialDomain ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared)
      (NativeBandExtension.velocityWeight ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos j)
      (fun L => ActualPrimary.outerRawVelocity j L) := by
  have hb := NativeBandExtension.bandVelocity_radial_jets ActualPrimary.certificate
    ActualPrimary.modulation (ActualPrimary.choice B N0).prepared
    ActualPrimary.slots.radius_pos ActualPrimary.radialVector ActualPrimary.temporalVector
      (ActualPrimary.closedMargins B N0) j
    (((ActualPrimary.preOuterVelocity_jets B N0 j).polynomial_smul
      (NativeBandExtension.outerCutoff_native_polynomial ActualPrimary.certificate
        ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos)).congr
      (fun L x _ => (NativeBandExtension.bandVelocity_eq_outer ActualPrimary.certificate
        ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos
          ActualPrimary.radialVector ActualPrimary.temporalVector j L x).symm))
  exact hb.congr (fun L x _ => congrFun (ActualPrimary.bandVelocity_eq j L) x)

theorem outer_pressure_jets (j : Fin 2) :
    NativeJets (NativeBandExtension.radialDomain ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared)
      (NativeBandExtension.pressureWeight ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos j)
      (fun L => ActualPrimary.outerRawPressure j L) := by
  have hb := NativeBandExtension.bandPressure_radial_jets ActualPrimary.certificate
    ActualPrimary.modulation (ActualPrimary.choice B N0).prepared
    ActualPrimary.slots.radius_pos ActualPrimary.radialVector ActualPrimary.temporalVector
      (ActualPrimary.closedMargins B N0) j
    (((ActualPrimary.preOuterPressure_jets B N0 j).polynomial_smul
      (NativeBandExtension.outerCutoff_native_polynomial ActualPrimary.certificate
        ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos)).congr
      (fun L x _ => (NativeBandExtension.bandPressure_eq_outer ActualPrimary.certificate
        ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos
          ActualPrimary.radialVector ActualPrimary.temporalVector j L x).symm))
  exact hb.congr (fun L x _ => congrFun (ActualPrimary.bandPressure_eq j L) x)

/-- The annular attachment is equal to the native field on the entire
open radial domain, including flat dyadic and transverse boundaries. -/
theorem attached_velocity_jets (j : Fin 2) :
    NativeJets (NativeBandExtension.radialDomain ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared)
      (NativeBandExtension.velocityWeight ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos j)
      (fun L => ActualPrimary.attachedRawVelocity j L) := by
  apply (outer_velocity_jets B N0 j).congr
  intro L x hx
  exact (WaveEdgeExtension.nativeExtension_inside ActualPrimary.nominal
    (ActualPrimary.outerRawVelocity j L) hx.2).symm

theorem attached_pressure_jets (j : Fin 2) :
    NativeJets (NativeBandExtension.radialDomain ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared)
      (NativeBandExtension.pressureWeight ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos j)
      (fun L => ActualPrimary.attachedRawPressure j L) := by
  apply (outer_pressure_jets B N0 j).congr
  intro L x hx
  exact (WaveEdgeExtension.nativeExtension_inside ActualPrimary.nominal
    (ActualPrimary.outerRawPressure j L) hx.2).symm

/-- Both signs share the same finite-jet constants. -/
theorem attached_velocity_signed_jets :
    NativeJets (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared))
      (fun l => NativeBandExtension.velocityWeight ActualPrimary.certificate
        ActualPrimary.modulation (ActualPrimary.choice B N0).prepared
        ActualPrimary.slots.radius_pos l.1 l.2)
      (fun l => ActualPrimary.attachedRawVelocity l.1 l.2) :=
  NativeJets.both_signs (attached_velocity_jets B N0)

theorem attached_pressure_signed_jets :
    NativeJets (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared))
      (fun l => NativeBandExtension.pressureWeight ActualPrimary.certificate
        ActualPrimary.modulation (ActualPrimary.choice B N0).prepared
        ActualPrimary.slots.radius_pos l.1 l.2)
      (fun l => ActualPrimary.attachedRawPressure l.1 l.2) :=
  NativeJets.both_signs (attached_pressure_jets B N0)

end NativeBounds

section CopyGeometry

variable {B N0 : ℕ}

noncomputable def spatialLabel (l : SignedLabel B N0) : SlotColoring.Label :=
  PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label ActualPrimary.nominal l.2) l.1

theorem label_large (l : SignedLabel B N0) : 4 ≤ (spatialLabel l).1 :=
  ((ActualPrimary.choice B N0).prepared.large _ l.2.property).four_le

noncomputable def near (l : SignedLabel B N0) (n : ℕ) : Prop :=
  1 ≤ n ∧ BaseChartJets.cellBand l.2 ∈ CommonWindow.levels n

theorem near_distance {l : SignedLabel B N0} {n : ℕ} (hn : near l n) :
    n ≤ (spatialLabel l).1 + 4 ∧ (spatialLabel l).1 ≤ n + 4 :=
  CommonWindow.distance hn.2

theorem geometry_eq (l : SignedLabel B N0) (n : ℕ) :
    ActualPrimary.chartGeometry n l.1 l.2 =
      ActualSignedGeometry.slotGeometry ActualPrimary.slots ActualPrimary.vectors_det (spatialLabel
        l)
        (ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2) - CommonWindow.index
          ActualPrimary.h n) := by
  rfl

theorem clock_eq (l : SignedLabel B N0) :
    ActualPrimary.clockWindow l.2 = ActualSignedGeometry.clockWindow ActualPrimary.slots
      (BaseChartJets.cellBand l.2) := rfl

noncomputable def copyPoint (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency) : Native →
  Native :=
  ActualSignedGeometry.copyPoint ActualPrimary.slots ActualPrimary.vectors_det (spatialLabel l)
    n (CommonWindow.index ActualPrimary.h n) k

noncomputable def copyLinear (l : SignedLabel B N0) (n : ℕ) : Native →L[ℝ] Native :=
  ActualSignedGeometry.copyLinear ActualPrimary.slots ActualPrimary.vectors_det (spatialLabel l)
    n (CommonWindow.index ActualPrimary.h n)

theorem copyPoint_affine (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency) (x : Native) :
    copyPoint l n k x = copyLinear l n x + copyPoint l n k 0 :=
  ActualSignedGeometry.copyPoint_affine _ _ _ _ _ _ _

theorem copyPoint_smooth (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency) :
    ContDiff ℝ ∞ (copyPoint l n k) := by
  have he : copyPoint l n k = fun x => copyLinear l n x + copyPoint l n k 0 :=
    funext (copyPoint_affine l n k)
  rw [he]
  exact (copyLinear l n).contDiff.add contDiff_const

noncomputable def copyCost : ℝ :=
  ActualSignedGeometry.slowChangeCost ActualPrimary.h +
    25 * CommonCoverClass.bandArgumentCost
      (TorusAverages.slotChart ActualPrimary.radialVector ActualPrimary.temporalVector
        ActualPrimary.vectors_det)
      (CommonWindow.gap ActualPrimary.h + SlotColoring.nativeGap ActualPrimary.h)

theorem copyCost_one : 1 ≤ copyCost := by
  have ha := ActualSignedGeometry.slowChangeCost_one ActualPrimary.h
  have hb := CommonCoverClass.bandArgumentCost_one_le
    (TorusAverages.slotChart ActualPrimary.radialVector ActualPrimary.temporalVector
      ActualPrimary.vectors_det)
    (CommonWindow.gap ActualPrimary.h + SlotColoring.nativeGap ActualPrimary.h)
  unfold copyCost
  linarith

theorem copyLinear_bound {l : SignedLabel B N0} {n : ℕ} (hn : near l n) :
    ‖copyLinear l n‖ ≤ copyCost * nativeStrip.slow n :=
  ActualSignedGeometry.norm_copyLinear_le ActualPrimary.slots ActualPrimary.vectors_det
    ActualPrimary.outgoing.data.h_pos.le
    (CommonWindow.indexBounds ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    hn.1 (label_large l) (near_distance hn).1 (near_distance hn).2

noncomputable def copyCells (l : SignedLabel B N0) :
    PeriodizedWaveBounds.Cells Native TorusInverse.Frequency :=
  PeriodizedWaveBounds.nativeCells (fun n => ActualPrimary.chartGeometry n l.1 l.2)
    (fun _ => (ActualPrimary.clockWindow l.2).core)
    (fun _ => (ActualPrimary.clockWindow l.2).core_compact)
    (fun n => by
      rw [geometry_eq, clock_eq]
      exact (ActualSignedGeometry.clockWindow_injective ActualPrimary.slots
        ActualPrimary.vectors_det
        ActualPrimary.outgoing.data.h_pos.le (label_large l) _).mono
          (Set.image_mono (ActualSignedGeometry.clockWindow ActualPrimary.slots
            _).core_subset_outer))

noncomputable def pulseEnvelope (l : SignedLabel B N0) : ℝ → ℝ :=
  PrimaryPulseBounds.referenceP ((ActualPrimary.phases B N0 l.1).lam l.2)
    ((ActualPrimary.phases B N0 l.1).u l.2) ((ActualPrimary.phases B N0 l.1).L l.2)

noncomputable def envelope (l : SignedLabel B N0) (n : ℕ) (x : Native) : ℝ :=
  WaveEnvelopeTransport.copyEnvelope (ActualPrimary.chartGeometry n l.1 l.2)
    ActualPrimary.slots.radius
    ((ActualPrimary.phases B N0 l.1).L l.2) (pulseEnvelope l) x.2

theorem envelope_nonneg (l : SignedLabel B N0) (n : ℕ) (x : Native) : 0 ≤ envelope l n x :=
  WaveEnvelopeTransport.copyEnvelope_nonneg _ _ _
    (fun t => (PrimaryPulseBounds.referenceP_pos _ _ _ t).le) _

theorem envelope_copy (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency)
    {x : Native} (hx : x ∈ (copyCells l).carrier n k) :
    envelope l n x = pulseEnvelope l (copyPoint l n k x).2.2 := by
  have hs : WaveEnvelopeTransport.Separated (ActualPrimary.chartGeometry n l.1 l.2)
      ActualPrimary.slots.radius ((ActualPrimary.phases B N0 l.1).L l.2) := by
    rw [ActualPrimary.length_sign l.1 l.2, geometry_eq]
    exact ActualSignedGeometry.slotGeometry_separated ActualPrimary.slots ActualPrimary.vectors_det
      ActualPrimary.outgoing.data.h_pos.le (label_large l) _
  have hc : (ActualPrimary.chartGeometry n l.1 l.2).coordinates k x.2 ∈
      WaveEnvelopeTransport.rectangle ActualPrimary.slots.radius ((ActualPrimary.phases B N0 l.1).L
        l.2) := by
    rw [ActualPrimary.length_sign l.1 l.2]
    exact hx
  have he := WaveEnvelopeTransport.copyEnvelope_eq_copy hs (pulseEnvelope l) hc
  simp only [envelope, copyPoint, ActualSignedGeometry.copyPoint] at he ⊢
  exact he

end CopyGeometry

section NativeCopyEstimates

variable {B N0 : ℕ}

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

theorem copyPoint_radial (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency)
    {x : Native} (hx : x ∈ nativeStrip.domain) :
    copyPoint l n k x ∈ NativeBandExtension.radialInterior ActualPrimary.nominal := by
  have hm := (ActualSignedGeometry.viewStrip_mem ActualPrimary.nominal region id x).mp hx
  have ht := BaseContextAssembly.nativeStrip_time ActualPrimary.nominal region hm
  have hr := BaseContextAssembly.nativeStrip_radius ActualPrimary.nominal region hm
  refine ⟨ActualSignedGeometry.slowChange_time (ChartScales.Q_pos _) (ChartScales.Q_pos _) ht, ?_⟩
  change PrimaryTargetBounds.profileRadius ActualPrimary.h
    (ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2)) x.1) ∈
        Ioo (PrimaryTargetBounds.leftRadius ActualPrimary.nominal) (PrimaryTargetBounds.rightRadius
          ActualPrimary.nominal)
  rw [ActualSignedGeometry.profileRadius_slowChange (ChartScales.Q_pos _) (ChartScales.Q_pos _) ht
    hr]
  exact ((BaseContextAssembly.nativeStrip_mem ActualPrimary.nominal region _).mp hm).2

theorem copyPoint_weight (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency)
    {x : Native} (hx : x ∈ nativeStrip.domain) :
    PrimaryTargetBounds.movingWeight ActualPrimary.nominal (copyPoint l n k x).1 = nativeStrip.zeta
      x := by
  have hm := (ActualSignedGeometry.viewStrip_mem ActualPrimary.nominal region id x).mp hx
  have ht := BaseContextAssembly.nativeStrip_time ActualPrimary.nominal region hm
  have hr := BaseContextAssembly.nativeStrip_radius ActualPrimary.nominal region hm
  change PrimaryTargetBounds.movingWeight ActualPrimary.nominal
    (ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand l.2)) x.1) = _
  rw [ActualSignedGeometry.movingWeight_slowChange ActualPrimary.nominal
    (ChartScales.Q_pos _) (ChartScales.Q_pos _) ht hr]
  exact (ActualSignedGeometry.viewStrip_zeta ActualPrimary.nominal region id x).symm

theorem copyPoint_growth {l : SignedLabel B N0} {n : ℕ} (hn : near l n)
    (k : TorusInverse.Frequency) {x : Native} (hx : x ∈ nativeStrip.domain) :
    (NativeBandExtension.radialDomain ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared).growth l.2 (copyPoint l n k x) ≤
        25 * nativeStrip.growth n x := by
  have hm := (ActualSignedGeometry.viewStrip_mem ActualPrimary.nominal region id x).mp hx
  have ht := BaseContextAssembly.nativeStrip_time ActualPrimary.nominal region hm
  have hr := BaseContextAssembly.nativeStrip_radius ActualPrimary.nominal region hm
  have hρ : WaveEdgeExtension.nativeRadius ActualPrimary.h (copyPoint l n k x) =
      PrimaryTargetBounds.profileRadius ActualPrimary.h x.1 :=
    ActualSignedGeometry.profileRadius_slowChange (ChartScales.Q_pos _) (ChartScales.Q_pos _) ht hr
  rw [NativeBandExtension.radialDomain_growth]
  have hg : WaveEdgeExtension.edgeGrowth (WaveEdgeExtension.nativeRadius ActualPrimary.h)
      (PrimaryTargetBounds.leftRadius ActualPrimary.nominal) (PrimaryTargetBounds.rightRadius
        ActualPrimary.nominal)
      (copyPoint l n k x) = max 1 (nativeStrip.delta x)⁻¹ := by
    unfold WaveEdgeExtension.edgeGrowth WaveEdgeExtension.logCoordinate
    rw [hρ]
    exact congrArg (fun d : ℝ => max 1 d⁻¹)
      (ActualSignedGeometry.viewStrip_delta ActualPrimary.nominal region id x).symm
  rw [hg]
  have hS := PhysicalGraphBounds.S_ge_one hn.1
  have hs : BaseContextAssembly.slowScale (BaseChartJets.cellBand l.2) ≤
      25 * BaseContextAssembly.slowScale n := by
    unfold BaseContextAssembly.slowScale
    rw [max_eq_right hS]
    exact max_le (by linarith) (ActualSignedGeometry.S_window_le hn.1 (near_distance hn).2)
  exact (mul_le_mul_of_nonneg_right hs (zero_le_one.trans (le_max_left 1 _))).trans_eq (by
    change (25 * BaseContextAssembly.slowScale n) * max 1 (nativeStrip.delta x)⁻¹ =
      25 * (BaseContextAssembly.slowScale n * max 1 (nativeStrip.delta x)⁻¹)
    ring)

theorem epsilon_power_window {n m : ℕ} (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) (α : ℝ) :
    ChartScales.epsilon ActualPrimary.h m ^ α ≤
      ActualSignedGeometry.powerBound (-(ActualPrimary.h * α)) *
        ChartScales.epsilon ActualPrimary.h n ^ α := by
  have he : ChartScales.epsilon ActualPrimary.h m ^ α /
      ChartScales.epsilon ActualPrimary.h n ^ α =
      PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) (-(ActualPrimary.h *
        α)) := by
    rw [ChartScales.epsilon, ChartScales.epsilon,
      ← Real.rpow_mul (ChartScales.Q_pos m).le, ← Real.rpow_mul (ChartScales.Q_pos n).le]
    simpa only [neg_neg] using (PhysicalParticularWave.ratioPower_neg_div
      (ChartScales.Q_pos n) (ChartScales.Q_pos m) (-(ActualPrimary.h * α)))
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (ChartScales.epsilon_pos _ _) α)).mp
  rw [he]
  exact ActualSignedGeometry.dyadic_ratioPower_le hnm hmn _

noncomputable def nativeWeight (α : ℝ) (l : SignedLabel B N0) (x : Native) : ℝ :=
  ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2) ^ α *
    Real.sqrt (PrimaryTargetBounds.movingWeight ActualPrimary.nominal x.1) * pulseEnvelope l x.2.2

noncomputable def coefficientScale (a : ℝ) (l : SignedLabel B N0) (n : ℕ) : ℝ :=
  PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2)) a

theorem coefficientScale_pos (a : ℝ) (l : SignedLabel B N0) (n : ℕ) :
    0 < coefficientScale a l n := PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos _)
      (ChartScales.Q_pos _) _

noncomputable def copied {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : SignedLabel B N0 → Native → E) (l : SignedLabel B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : Native) : E := by
  classical
  exact if near l n then coefficientScale a l n • f l (copyPoint l n k x) else 0

/-- Active-window comparisons are required only where the copy is
present. No comparison is imposed between remote band/label pairs. -/
theorem copied_uniformLocalJets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a α : ℝ} {f : SignedLabel B N0 → Native → E}
    (hf : NativeJets (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared)) (nativeWeight α) f) :
    PeriodizedWaveBounds.UniformLocalJets nativeStrip
      (fun l n x => Real.sqrt (nativeStrip.zeta x) * envelope l n x) α
      (fun l => (copyCells l).carrier) (copied a f) := by
  let V := signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
    ActualPrimary.modulation (ActualPrimary.choice B N0).prepared)
  have hs (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency) (x : Native)
      (hx : x ∈ nativeStrip.domain) : ContDiffAt ℝ ∞ (fun y => f l (copyPoint l n k y)) x :=
    ((hf.smooth l).contDiffAt ((V.isOpen l).mem_nhds (copyPoint_radial l n k hx))).comp x
      (copyPoint_smooth l n k).contDiffAt
  refine ⟨?_, ?_⟩
  · intro l n k x hx hk
    by_cases hn : near l n
    · rw [show copied a f l n k = fun y => coefficientScale a l n • f l (copyPoint l n k y) from
        funext (fun y => ite_eq_left hn)]
      exact (hs l n k x hx).const_smul (coefficientScale a l n)
    · rw [show copied a f l n k = fun _ => 0 from funext (fun _ => ite_eq_right hn)]
      exact contDiffAt_const
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bound m
    let A := ActualSignedGeometry.powerBound a * ActualSignedGeometry.powerBound (-(ActualPrimary.h
      * α))
    have hcost := copyCost_one
    have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le
      (ActualSignedGeometry.powerBound_one _) (ActualSignedGeometry.powerBound_one _)
    refine ⟨C * 25 ^ p * copyCost ^ m * A, by positivity, p + m, ?_⟩
    intro l n k x hx hk j hj
    by_cases hn : near l n
    · have ht := copyPoint_radial l n k hx
      have hG := nativeStrip.one_le_growth n x
      have hW : 0 ≤ Real.sqrt (nativeStrip.zeta x) * envelope l n x :=
        mul_nonneg (Real.sqrt_nonneg _) (envelope_nonneg l n x)
      have hcost := copyCost_one
      have hS := nativeStrip.one_le_slow n
      have hB : 1 ≤ copyCost * nativeStrip.slow n := one_le_mul_of_one_le_of_one_le hcost hS
      have hlin : ‖copyLinear l n‖ ^ j ≤ copyCost ^ m * nativeStrip.growth n x ^ m := by
        calc
          _ ≤ (copyCost * nativeStrip.slow n) ^ m :=
            (pow_le_pow_left₀ (norm_nonneg _) (copyLinear_bound hn) j).trans (pow_le_pow_right₀ hB
              hj)
          _ ≤ (copyCost * nativeStrip.growth n x) ^ m := by
            gcongr
            exact nativeStrip.slow_le_growth n x
          _ = _ := mul_pow _ _ _
      have hu : ‖iteratedFDeriv ℝ j (fun y => f l (copyPoint l n k y)) x‖ ≤
          ‖iteratedFDeriv ℝ j (f l) (copyPoint l n k x)‖ * ‖copyLinear l n‖ ^ j := by
        simpa only [← copyPoint_affine] using
          norm_jet_comp_affine (V.isOpen l) (hf.smooth l) (copyLinear l n) (copyPoint l n k 0)
            (by simp only [← copyPoint_affine]; exact ht) j
      have hscale : coefficientScale a l n * ChartScales.epsilon ActualPrimary.h
        (BaseChartJets.cellBand l.2) ^ α ≤
          A * nativeStrip.epsilon n ^ α := by
        calc
          _ ≤ ActualSignedGeometry.powerBound a *
              (ActualSignedGeometry.powerBound (-(ActualPrimary.h * α)) *
                ChartScales.epsilon ActualPrimary.h n ^ α) :=
            mul_le_mul (ActualSignedGeometry.dyadic_ratioPower_le (near_distance hn).1
              (near_distance hn).2 a)
              (epsilon_power_window (near_distance hn).1 (near_distance hn).2 α)
              (Real.rpow_pos_of_pos (ChartScales.epsilon_pos _ _) _).le
              (zero_le_one.trans (ActualSignedGeometry.powerBound_one _))
          _ = _ := by
            change ActualSignedGeometry.powerBound a *
              (ActualSignedGeometry.powerBound (-(ActualPrimary.h * α)) * ChartScales.epsilon
                ActualPrimary.h n ^ α) =
                A * ChartScales.epsilon ActualPrimary.h n ^ α
            dsimp [A]
            ring
      rw [show copied a f l n k = fun y => coefficientScale a l n • f l (copyPoint l n k y) from
        funext (fun y => ite_eq_left hn)]
      rw [iteratedFDeriv_const_smul_apply' ((hs l n k x hx).of_le (nat_le_infty j)),
        norm_smul (coefficientScale a l n) (iteratedFDeriv ℝ j (fun y => f l (copyPoint l n k y))
          x),
        Real.norm_of_nonneg (coefficientScale_pos a l n).le]
      have hnative : nativeWeight α l (copyPoint l n k x) =
          ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2) ^ α *
            (Real.sqrt (nativeStrip.zeta x) * envelope l n x) := by
        rw [nativeWeight, copyPoint_weight l n k hx, envelope_copy l n k hk]
        ring
      calc
        _ ≤ coefficientScale a l n *
            ((C * (25 * nativeStrip.growth n x) ^ p * nativeWeight α l (copyPoint l n k x)) *
              (copyCost ^ m * nativeStrip.growth n x ^ m)) := by
          apply mul_le_mul_of_nonneg_left _ (coefficientScale_pos a l n).le
          apply hu.trans
          have hfb := (hb l _ ht j hj).trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
              (zero_le_one.trans (V.one_le_growth l ht)) (copyPoint_growth hn k hx) p)
              (zero_le_one.trans hC)) (hf.nonneg l _ ht))
          exact mul_le_mul hfb hlin (pow_nonneg (norm_nonneg _) _)
            ((norm_nonneg _).trans hfb)
        _ = (C * 25 ^ p * copyCost ^ m) * nativeStrip.growth n x ^ (p + m) *
            (coefficientScale a l n * ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand
              l.2) ^ α) *
            (Real.sqrt (nativeStrip.zeta x) * envelope l n x) := by
          rw [hnative, mul_pow, pow_add]
          ring
        _ ≤ (C * 25 ^ p * copyCost ^ m) * nativeStrip.growth n x ^ (p + m) *
            (A * nativeStrip.epsilon n ^ α) *
            (Real.sqrt (nativeStrip.zeta x) * envelope l n x) := by gcongr
        _ = majorant nativeStrip (fun n x => Real.sqrt (nativeStrip.zeta x) * envelope l n x) α
            (C * 25 ^ p * copyCost ^ m * A) (p + m) n x := by unfold majorant; ring
    · rw [show copied a f l n k = fun _ => 0 from funext (fun _ => ite_eq_right hn),
      iteratedFDeriv_fun_zero]
      have hc : 0 ≤ C * 25 ^ p * copyCost ^ m * A := by positivity
      simpa only [Pi.zero_apply, norm_zero] using majorant_nonneg nativeStrip
        (fun n x => Real.sqrt (nativeStrip.zeta x) * envelope l n x) α hc
        (p + m) n x (mul_nonneg (Real.sqrt_nonneg _) (envelope_nonneg l n x))

end NativeCopyEstimates

section ActualCopySums

variable {B N0 : ℕ}

theorem velocityWeight_eq (l : SignedLabel B N0) (x : Native) :
    NativeBandExtension.velocityWeight ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos l.1 l.2 x = nativeWeight
        (1 / 2) l x := by
  change Real.sqrt (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2)) *
    Real.sqrt (PrimaryTargetBounds.movingWeight ActualPrimary.nominal x.1) *
      PrimaryPulseBounds.referenceP ((ActualPrimary.phases B N0 l.1).lam l.2)
        ((ActualPrimary.phases B N0 l.1).u l.2) ((ActualPrimary.phases B N0 l.1).L l.2)
        (((ActualPrimary.phases B N0 l.1).L l.2) * (x.2.2 / ((ActualPrimary.phases B N0 0).L l.2)))
          = _
  rw [ActualPrimary.length_sign l.1 l.2,
    mul_div_cancel₀ _ ((ActualPrimary.phases B N0 0).L_pos l.2).ne']
  simp only [nativeWeight, pulseEnvelope, ← Real.sqrt_eq_rpow, ActualPrimary.length_sign l.1 l.2]

theorem pressureWeight_eq (l : SignedLabel B N0) (x : Native) :
    NativeBandExtension.pressureWeight ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos l.1 l.2 x = nativeWeight
        1 l x := by
  change ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2) *
    Real.sqrt (PrimaryTargetBounds.movingWeight ActualPrimary.nominal x.1) *
      PrimaryPulseBounds.referenceP ((ActualPrimary.phases B N0 l.1).lam l.2)
        ((ActualPrimary.phases B N0 l.1).u l.2) ((ActualPrimary.phases B N0 l.1).L l.2)
        (((ActualPrimary.phases B N0 l.1).L l.2) * (x.2.2 / ((ActualPrimary.phases B N0 0).L l.2)))
          = _
  rw [ActualPrimary.length_sign l.1 l.2,
    mul_div_cancel₀ _ ((ActualPrimary.phases B N0 0).L_pos l.2).ne']
  simp only [nativeWeight, pulseEnvelope, Real.rpow_one, ActualPrimary.length_sign l.1 l.2]

theorem complex_velocity_native_jets :
    NativeJets (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared)) (nativeWeight (1 / 2))
      (fun l x => CurlClassBounds.complexify (ActualPrimary.attachedRawVelocity l.1 l.2 x)) := by
  have hw : (fun l : SignedLabel B N0 => NativeBandExtension.velocityWeight
    ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos
        l.1 l.2) =
      nativeWeight (1 / 2) := funext (fun l => funext (velocityWeight_eq l))
  have hh := (attached_velocity_signed_jets B N0).map CurlClassBounds.complexify
  rw [hw] at hh
  exact hh

theorem pressure_native_jets :
    NativeJets (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared)) (nativeWeight 1)
      (fun l => ActualPrimary.attachedRawPressure l.1 l.2) := by
  have hw : (fun l : SignedLabel B N0 => NativeBandExtension.pressureWeight
    ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos
        l.1 l.2) =
      nativeWeight 1 := funext (fun l => funext (pressureWeight_eq l))
  rw [← hw]
  exact attached_pressure_signed_jets B N0

noncomputable def periodized {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : SignedLabel B N0 → Native → E) (l : SignedLabel B N0) (n : ℕ) : Native → E :=
  PeriodizedWaveBounds.copySum (copied a f l n)

theorem periodized_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a α : ℝ} {f : SignedLabel B N0 → Native → E}
    (hf : NativeJets (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared)) (nativeWeight α) f)
    (hs : ∀ l x, f l x ≠ 0 → x.2 ∈ (ActualPrimary.clockWindow l.2).core) :
    LabelSumBounds.UniformWaveClass nativeStrip envelope α (periodized a f) := by
  apply PeriodizedWaveBounds.copySum_uniformClass copyCells
    (fun l n x _ => mul_nonneg (Real.sqrt_nonneg _) (envelope_nonneg l n x))
  · intro l n k x hx
    by_cases hn : near l n
    · have hfn : f l (copyPoint l n k x) ≠ 0 := by
        intro hz
        exact hx (by simp only [copied, ite_eq_left hn, hz, smul_zero])
      have hk := hs l (copyPoint l n k x) hfn
      simp only [copyPoint, ActualSignedGeometry.copyPoint] at hk ⊢
      exact hk
    · exact (hx (by simp only [copied, ite_eq_right hn])).elim
  · exact copied_uniformLocalJets hf

theorem periodized_velocity_uniform :
    LabelSumBounds.UniformWaveClass nativeStrip envelope (1 / 2)
      (periodized (CoordinateAlgebra.A ActualPrimary.h)
        (fun l : SignedLabel B N0 => fun x => CurlClassBounds.complexify
          (ActualPrimary.attachedRawVelocity l.1 l.2 x))) := by
  apply periodized_uniform complex_velocity_native_jets
  intro l x hx
  apply ActualPrimary.attachedRawVelocity_core l.1 l.2 x
  intro hz
  exact hx (by rw [hz, map_zero])

theorem periodized_pressure_uniform :
    LabelSumBounds.UniformWaveClass nativeStrip envelope 1
      (periodized (2 * CoordinateAlgebra.A ActualPrimary.h)
        (fun l : SignedLabel B N0 => ActualPrimary.attachedRawPressure l.1 l.2)) :=
  periodized_uniform pressure_native_jets (fun l x => ActualPrimary.attachedRawPressure_core l.1
    l.2 x)

end ActualCopySums

section InactiveBands

variable {B N0 : ℕ}

/-- A nonzero closed native dyadic band meets only the actual finite
two-level window. The stronger four-level estimates therefore apply. -/
theorem near_of_closed_band (l : SignedLabel B N0) (n : ℕ) {p : PhaseCalculus.Slow}
    (hp : p ∈ BaseContextAssembly.slowCarrier ActualPrimary.nominal region)
    (hq : SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) p) ∈ Icc (1 / 2 : ℝ) 2) : near l n := by
  have hm := (BaseContextAssembly.nativeStrip_mem ActualPrimary.nominal region _).mp hp
  have ht : 0 < p.2.2 := hm.1.1
  have hq0 : SimilarityHomogeneity.chartQ ActualPrimary.h p ∈ Ioo (1 / 2 : ℝ) 2 := hm.1.2
  let q := ChartScales.Q n * SimilarityHomogeneity.chartQ ActualPrimary.h p
  have hqpos : 0 < q := mul_pos (ChartScales.Q_pos _) (by linarith [hq0.1])
  have he : SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) p) = q / ChartScales.Q (BaseChartJets.cellBand
          l.2) := by
    rw [ActualSignedGeometry.slowChange_eq_transition (ChartScales.Q_pos _) (ChartScales.Q_pos _),
      SimilarityHomogeneity.chartQ_transition ActualPrimary.outgoing.data.h_pos
        ActualPrimary.outgoing.data.h_lt_half (ChartScales.Q_pos _) (ChartScales.Q_pos _) ht]
    dsimp [q]
    ring
  rw [he] at hq
  have hn := PhysicalWaveSum.logCoordinate_in_band hqpos
    (show ChartScales.Q n / 2 ≤ q by dsimp [q]; nlinarith [ChartScales.Q_pos n, hq0.1])
    (show q ≤ 2 * ChartScales.Q n by dsimp [q]; nlinarith [ChartScales.Q_pos n, hq0.2])
  have hL := PhysicalWaveSum.logCoordinate_in_band hqpos
    (show ChartScales.Q (BaseChartJets.cellBand l.2) / 2 ≤ q by
      have hh := (le_div_iff₀ (ChartScales.Q_pos _)).mp hq.1
      linarith)
    ((div_le_iff₀ (ChartScales.Q_pos _)).mp hq.2)
  have hnm : n ≤ BaseChartJets.cellBand l.2 + 2 := by
    have hh : (n : ℝ) ≤ (BaseChartJets.cellBand l.2 : ℝ) + 2 := by linarith [hn.1, hL.2]
    exact_mod_cast hh
  have hmn : BaseChartJets.cellBand l.2 ≤ n + 2 := by
    have hh : (BaseChartJets.cellBand l.2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [hL.1, hn.2]
    exact_mod_cast hh
  have hm4 : 4 ≤ BaseChartJets.cellBand l.2 := label_large l
  refine ⟨by omega, Finset.mem_insert_of_mem ?_⟩
  exact Finset.mem_Icc.mpr ⟨max_le (by omega) (by omega), hmn⟩

theorem attached_zero_inactive (l : SignedLabel B N0) (n : ℕ) {p : PhaseCalculus.Slow}
    (hp : p ∈ BaseContextAssembly.slowCarrier ActualPrimary.nominal region)
    (hn : ¬near l n) (Y : TorusInverse.Plane) :
    ActualPrimary.attachedRawVelocity l.1 l.2
      (ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) p, Y) = 0 ∧
    ActualPrimary.attachedRawPressure l.1 l.2
      (ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) p, Y) = 0 := by
  let y : Native := (ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
    (ChartScales.Q (BaseChartJets.cellBand l.2)) p, Y)
  have ht : 0 < y.1.2.2 := ActualSignedGeometry.slowChange_time (ChartScales.Q_pos _)
    (ChartScales.Q_pos _) (BaseContextAssembly.nativeStrip_time ActualPrimary.nominal region hp)
  have hq : NativeBandExtension.nativeQ ActualPrimary.h y ∉ Icc (1 / 2 : ℝ) 2 :=
    fun hq => hn (near_of_closed_band l n hp hq)
  have hz := NativeBandExtension.band_pair_zero_germ_factor ActualPrimary.certificate
    ActualPrimary.modulation
    (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos ActualPrimary.radialVector
    ActualPrimary.temporalVector l.1 l.2
    (NativeBandExtension.factor_zero_germ_band ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared l.2 ht hq)
  have hv : ActualPrimary.outerRawVelocity l.1 l.2 y = 0 := by
    have hv := hz.1.eq_of_nhds
    simpa only [ActualPrimary.bandVelocity_eq] using hv
  have hp' : ActualPrimary.outerRawPressure l.1 l.2 y = 0 := by
    have hp' := hz.2.eq_of_nhds
    simpa only [ActualPrimary.bandPressure_eq] using hp'
  constructor
  · change ActualPrimary.attachedRawVelocity l.1 l.2 y = 0
    simp only [ActualPrimary.attachedRawVelocity, WaveEdgeExtension.nativeExtension,
      WaveEdgeExtension.extension, hv, ite_self]
  · change ActualPrimary.attachedRawPressure l.1 l.2 y = 0
    simp only [ActualPrimary.attachedRawPressure, WaveEdgeExtension.nativeExtension,
      WaveEdgeExtension.extension, hp', ite_self]

end InactiveBands

section LiteralCoefficients

variable {B N0 : ℕ}

theorem coefficientScale_eq (a : ℝ) (l : SignedLabel B N0) (n : ℕ) :
    coefficientScale a l n = ChartScales.Q n ^ a *
      ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-a) := by
  rw [coefficientScale, PhysicalParticularWave.ratioPower, Real.rpow_neg (ChartScales.Q_pos _).le]
  rfl

theorem periodized_velocity_eq (l : SignedLabel B N0) (n : ℕ) {x : Native}
    (hx : x ∈ nativeStrip.domain) (θ : ℝ) :
    periodized (CoordinateAlgebra.A ActualPrimary.h)
      (fun l : SignedLabel B N0 => fun y => CurlClassBounds.complexify
        (ActualPrimary.attachedRawVelocity l.1 l.2 y)) l n x =
      (ActualPrimary.chartCoefficients l.1 l.2).amplitude n (ActualSignedGeometry.meanEquiv x, θ)
        := by
  classical
  by_cases hn : near l n
  · rw [ActualPrimary.chartCoefficients_amplitude_copies l.1 l.2 n (CommonWindow.index_le hn.2)]
    simp only [periodized, PeriodizedWaveBounds.copySum, copied, ite_eq_left hn,
      ActualSignedGeometry.meanEquiv.symm_apply_apply, ← tsum_const_smul'']
    rw [coefficientScale_eq]
    rfl
  · have hm := (ActualSignedGeometry.viewStrip_mem ActualPrimary.nominal region id x).mp hx
    have hz (k : TorusInverse.Frequency) : ActualPrimary.attachedRawVelocity l.1 l.2
        (ActualPrimary.nativeSlow l.2 (ActualPrimary.toAbsolute n (ActualSignedGeometry.meanEquiv
          x)),
          (ActualPrimary.geometry l.1 l.2).coordinates k
            (ActualPrimary.toAbsolute n (ActualSignedGeometry.meanEquiv x)).2) = 0 := by
      rw [ActualPrimary.nativeSlow_toAbsolute_eq_slowChange]
      exact (attached_zero_inactive l n hm hn _).1
    simp only [periodized, PeriodizedWaveBounds.copySum, copied, ite_eq_right hn, tsum_zero]
    simp only [ActualPrimary.chartCoefficients, ActualPrimary.absoluteAmplitude,
      ActualPrimary.uncutAmplitude,
      hz, map_zero, tsum_zero, smul_zero]

theorem periodized_pressure_eq (l : SignedLabel B N0) (n : ℕ) {x : Native}
    (hx : x ∈ nativeStrip.domain) (θ : ℝ) :
    periodized (2 * CoordinateAlgebra.A ActualPrimary.h)
      (fun l : SignedLabel B N0 => ActualPrimary.attachedRawPressure l.1 l.2) l n x =
      (ActualPrimary.chartCoefficients l.1 l.2).pressure n (ActualSignedGeometry.meanEquiv x, θ) :=
        by
  classical
  by_cases hn : near l n
  · rw [ActualPrimary.chartCoefficients_pressure_copies l.1 l.2 n (CommonWindow.index_le hn.2)]
    simp only [periodized, PeriodizedWaveBounds.copySum, copied, ite_eq_left hn,
      ActualSignedGeometry.meanEquiv.symm_apply_apply, ← tsum_const_smul'']
    rw [coefficientScale_eq]
    rfl
  · have hm := (ActualSignedGeometry.viewStrip_mem ActualPrimary.nominal region id x).mp hx
    have hz (k : TorusInverse.Frequency) : ActualPrimary.attachedRawPressure l.1 l.2
        (ActualPrimary.nativeSlow l.2 (ActualPrimary.toAbsolute n (ActualSignedGeometry.meanEquiv
          x)),
          (ActualPrimary.geometry l.1 l.2).coordinates k
            (ActualPrimary.toAbsolute n (ActualSignedGeometry.meanEquiv x)).2) = 0 := by
      rw [ActualPrimary.nativeSlow_toAbsolute_eq_slowChange]
      exact (attached_zero_inactive l n hm hn _).2
    simp only [periodized, PeriodizedWaveBounds.copySum, copied, ite_eq_right hn, tsum_zero]
    simp only [ActualPrimary.chartCoefficients, ActualPrimary.absolutePressure,
      ActualPrimary.uncutPressure,
      hz, tsum_zero, smul_zero]

theorem uniform_lift {D E ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : StripData D}
    {w : ι → ℕ → D → ℝ} {α : ℝ} {f : ι → ℕ → D → E}
    (hf : LabelSumBounds.UniformClass s w α f) :
    LabelSumBounds.UniformClass (HarmonicWaveInteraction.productStrip s)
      (fun l n x => w l n x.1) α (fun l n x => f l n x.1) := by
  refine ⟨fun l n x hx => hf.weight_nonneg l n x.1 hx,
    fun l n => (hf.each l |> HarmonicWaveInteraction.class_lift).smooth n, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, fun l n x hx j hj => ?_⟩
  have hd := HarmonicWaveInteraction.norm_jet_comp_linear s.isOpen_domain (hf.smooth l n)
    HarmonicWaveInteraction.projection hx j
  exact (hd.trans (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) HarmonicWaveInteraction.projection_norm))).trans (hb l n x.1 hx j
      hj)

noncomputable def fullEnvelope (l : SignedLabel B N0) (n : ℕ) (x : ActualPrimary.FullPoint) : ℝ :=
  envelope l n (ActualSignedGeometry.meanEquiv.symm x.1)

theorem chart_amplitude_uniform :
    LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip strip) fullEnvelope (1 /
      2)
      (fun l : SignedLabel B N0 => (ActualPrimary.chartCoefficients l.1 l.2).amplitude) := by
  have hh := UniformBlockBounds.uniform_reindex ActualSignedGeometry.meanEquiv.symm
    (periodized_velocity_uniform (B := B) (N0 := N0))
  change LabelSumBounds.UniformWaveClass strip
    (fun l n x => envelope l n (ActualSignedGeometry.meanEquiv.symm x)) (1 / 2)
    (fun l n x => periodized (CoordinateAlgebra.A ActualPrimary.h)
      (fun l : SignedLabel B N0 => fun y => CurlClassBounds.complexify
        (ActualPrimary.attachedRawVelocity l.1 l.2 y))
      l n (ActualSignedGeometry.meanEquiv.symm x)) at hh
  apply (uniform_lift hh).congr
  intro l n x hx
  simpa only [ActualSignedGeometry.meanEquiv.apply_symm_apply] using
    periodized_velocity_eq l n (x := ActualSignedGeometry.meanEquiv.symm x.1) hx x.2

theorem chart_pressure_uniform :
    LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip strip) fullEnvelope 1
      (fun l : SignedLabel B N0 => (ActualPrimary.chartCoefficients l.1 l.2).pressure) := by
  have hh := UniformBlockBounds.uniform_reindex ActualSignedGeometry.meanEquiv.symm
    (periodized_pressure_uniform (B := B) (N0 := N0))
  change LabelSumBounds.UniformWaveClass strip
    (fun l n x => envelope l n (ActualSignedGeometry.meanEquiv.symm x)) 1
    (fun l n x => periodized (2 * CoordinateAlgebra.A ActualPrimary.h)
      (fun l : SignedLabel B N0 => ActualPrimary.attachedRawPressure l.1 l.2)
      l n (ActualSignedGeometry.meanEquiv.symm x)) at hh
  apply (uniform_lift hh).congr
  intro l n x hx
  simpa only [ActualSignedGeometry.meanEquiv.apply_symm_apply] using
    periodized_pressure_eq l n (x := ActualSignedGeometry.meanEquiv.symm x.1) hx x.2

end LiteralCoefficients

section GaussianCutoff

variable {B N0 : ℕ}

noncomputable def timeProjection (L : ActualPrimary.Label B N0) : Native →L[ℝ] ℝ :=
  (((ActualPrimary.phases B N0 0).L L)⁻¹) •
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ PhaseCalculus.Slow
      TorusInverse.Plane))

theorem timeProjection_norm (L : ActualPrimary.Label B N0) :
    ‖timeProjection L‖ ≤ (ActualPrimary.choice B N0).prepared.M := by
  have hL := (ActualPrimary.phases B N0 0).L_pos L
  have hr := ActualPrimary.slots.radius_pos
  have hn : 4 ≤ BaseChartJets.cellBand L := ((ActualPrimary.choice B N0).prepared.large _
    L.property).four_le
  have hlen := (ChartScales.slotLength_bounds ActualPrimary.slots.radius ActualPrimary.h
    ActualPrimary.slots.radius_pos.le ActualPrimary.outgoing.data.h_pos.le hn).1
  have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ BaseChartJets.cellBand L by omega)
  have hlow : 2 * ActualPrimary.slots.radius ≤ (ActualPrimary.phases B N0 0).L L := by
    exact (le_mul_of_one_le_right (by positivity) hS).trans hlen
  have hi : ((ActualPrimary.phases B N0 0).L L)⁻¹ ≤ (ActualPrimary.choice B N0).prepared.M := by
    simpa only [one_div] using ((one_div_le_one_div_of_le (by positivity) hlow).trans
      (ActualPrimary.choice B N0).prepared.length_bound)
  apply le_trans _ hi
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_pos.mpr hL).le
  intro x
  change ‖((ActualPrimary.phases B N0 0).L L)⁻¹ * x.2.2‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg (inv_pos.mpr hL).le]
  exact mul_le_mul_of_nonneg_left ((norm_snd_le x.2).trans (norm_snd_le x)) (inv_pos.mpr hL).le

/-- The fixed compact Gaussian profile has uniform jets after the actual
slot rescaling, on the full radial domain. -/
theorem gaussian_polynomial :
    PolynomialJets (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared)).toDomain
      (fun l : SignedLabel B N0 => ActualPrimary.gaussian l.2) := by
  have hh := gaussianCutoff_affine_jets
    (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared)).toDomain
    (fun l : SignedLabel B N0 => timeProjection l.2) (fun _ => 0)
    (ActualPrimary.choice B N0).prepared.one_le_M 0
    (fun l => by simpa only [pow_zero, mul_one] using timeProjection_norm l.2)
  simp only [timeProjection,
    _root_.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
    smul_eq_mul, add_zero, mul_comm] at hh ⊢
  exact hh

noncomputable def cutNativeVelocity (l : SignedLabel B N0) (x : Native) :
  HarmonicCalculus.ComplexVector :=
  ActualPrimary.gaussian l.2 x • CurlClassBounds.complexify (ActualPrimary.attachedRawVelocity l.1
    l.2 x)

noncomputable def cutNativePressure (l : SignedLabel B N0) (x : Native) : ℂ :=
  ActualPrimary.gaussian l.2 x • ActualPrimary.attachedRawPressure l.1 l.2 x

theorem cut_native_velocity_jets :
    NativeJets (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared)) (nativeWeight (1 / 2))
      (cutNativeVelocity (B := B) (N0 := N0)) :=
  complex_velocity_native_jets.polynomial_smul gaussian_polynomial

theorem cut_native_pressure_jets :
    NativeJets (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared)) (nativeWeight 1)
      (cutNativePressure (B := B) (N0 := N0)) :=
  pressure_native_jets.polynomial_smul gaussian_polynomial

theorem periodized_cut_velocity_uniform :
    LabelSumBounds.UniformWaveClass nativeStrip envelope (1 / 2)
      (periodized (CoordinateAlgebra.A ActualPrimary.h) (cutNativeVelocity (B := B) (N0 := N0))) :=
        by
  apply periodized_uniform cut_native_velocity_jets
  intro l x hx
  apply ActualPrimary.attachedRawVelocity_core l.1 l.2 x
  intro hz
  exact hx (by simp only [cutNativeVelocity, hz, map_zero, smul_zero])

theorem periodized_cut_pressure_uniform :
    LabelSumBounds.UniformWaveClass nativeStrip envelope 1
      (periodized (2 * CoordinateAlgebra.A ActualPrimary.h) (cutNativePressure (B := B) (N0 :=
        N0))) := by
  apply periodized_uniform cut_native_pressure_jets
  intro l x hx
  apply ActualPrimary.attachedRawPressure_core l.1 l.2 x
  intro hz
  exact hx (by simp only [cutNativePressure, hz, smul_zero])

theorem gaussian_on_copy (l : SignedLabel B N0) (n : ℕ) (hn : near l n)
    (k : TorusInverse.Frequency) (x : Native) (θ : ℝ)
    (hc : (copyPoint l n k x).2 ∈ (ActualPrimary.clockWindow l.2).core) :
    ActualPrimary.chartCutoff l.1 l.2 n (ActualSignedGeometry.meanEquiv x, θ) =
      ActualPrimary.gaussian l.2 (copyPoint l n k x) := by
  have he := ActualPrimary.chart_nativePoint l.1 l.2 n (CommonWindow.index_le hn.2) k
    (ActualSignedGeometry.meanEquiv x)
  simp only [ActualSignedGeometry.meanEquiv.symm_apply_apply] at he
  change _ = copyPoint l n k x at he
  have hs : (ActualPrimary.geometry l.1 l.2).coordinates k
      (ActualPrimary.toAbsolute n (ActualSignedGeometry.meanEquiv x)).2 ∈
        (ActualPrimary.clockWindow l.2).core := by
    rw [← he] at hc
    exact hc
  have hg := ActualPrimary.periodicGaussian_eq_on_core l.1 l.2
    (ActualPrimary.nativeSlow l.2 (ActualPrimary.toAbsolute n (ActualSignedGeometry.meanEquiv x)))
    (ActualPrimary.toAbsolute n (ActualSignedGeometry.meanEquiv x)).2 k hs
  rw [he] at hg
  exact hg

theorem periodized_cut_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : SignedLabel B N0 → Native → E)
    (hs : ∀ l x, f l x ≠ 0 → x.2 ∈ (ActualPrimary.clockWindow l.2).core)
    (l : SignedLabel B N0) (n : ℕ) (x : Native) (θ : ℝ) :
    periodized a (fun l y => ActualPrimary.gaussian l.2 y • f l y) l n x =
      ActualPrimary.chartCutoff l.1 l.2 n (ActualSignedGeometry.meanEquiv x, θ) • periodized a f l
        n x := by
  classical
  by_cases hn : near l n
  · simp only [periodized, PeriodizedWaveBounds.copySum, copied, ite_eq_left hn]
    rw [← tsum_const_smul'']
    apply tsum_congr
    intro k
    by_cases hz : f l (copyPoint l n k x) = 0
    · simp only [hz, smul_zero]
    · rw [gaussian_on_copy l n hn k x θ (hs l _ hz)]
      exact smul_comm _ _ _
  · simp only [periodized, PeriodizedWaveBounds.copySum, copied, ite_eq_right hn, tsum_zero,
    smul_zero]

theorem chart_cut_amplitude_uniform :
    LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip strip) fullEnvelope (1 /
      2)
      (fun l : SignedLabel B N0 =>
        ((ActualPrimary.chartCoefficients l.1 l.2).withCutoff (ActualPrimary.chartCutoff l.1
          l.2)).amplitude) := by
  have hh := UniformBlockBounds.uniform_reindex ActualSignedGeometry.meanEquiv.symm
    (periodized_cut_velocity_uniform (B := B) (N0 := N0))
  change LabelSumBounds.UniformWaveClass strip
    (fun l n x => envelope l n (ActualSignedGeometry.meanEquiv.symm x)) (1 / 2)
    (fun l n x => periodized (CoordinateAlgebra.A ActualPrimary.h) cutNativeVelocity
      l n (ActualSignedGeometry.meanEquiv.symm x)) at hh
  apply (uniform_lift hh).congr
  intro l n x hx
  have hs (l : SignedLabel B N0) (y : Native)
      (hy : CurlClassBounds.complexify (ActualPrimary.attachedRawVelocity l.1 l.2 y) ≠ 0) :
      y.2 ∈ (ActualPrimary.clockWindow l.2).core := by
    apply ActualPrimary.attachedRawVelocity_core l.1 l.2 y
    intro hz
    exact hy (by rw [hz, map_zero])
  have he := periodized_cut_eq (CoordinateAlgebra.A ActualPrimary.h)
    (fun l : SignedLabel B N0 => fun y => CurlClassBounds.complexify
      (ActualPrimary.attachedRawVelocity l.1 l.2 y))
    hs l n (ActualSignedGeometry.meanEquiv.symm x.1) x.2
  rw [periodized_velocity_eq l n hx x.2] at he
  simp only [ActualSignedGeometry.meanEquiv.apply_symm_apply,
    LinearWaveBounds.WaveCoefficients.withCutoff] at he ⊢
  exact he

theorem chart_cut_pressure_uniform :
    LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip strip) fullEnvelope 1
      (fun l : SignedLabel B N0 =>
        ((ActualPrimary.chartCoefficients l.1 l.2).withCutoff (ActualPrimary.chartCutoff l.1
          l.2)).pressure) := by
  have hh := UniformBlockBounds.uniform_reindex ActualSignedGeometry.meanEquiv.symm
    (periodized_cut_pressure_uniform (B := B) (N0 := N0))
  change LabelSumBounds.UniformWaveClass strip
    (fun l n x => envelope l n (ActualSignedGeometry.meanEquiv.symm x)) 1
    (fun l n x => periodized (2 * CoordinateAlgebra.A ActualPrimary.h) cutNativePressure
      l n (ActualSignedGeometry.meanEquiv.symm x)) at hh
  apply (uniform_lift hh).congr
  intro l n x hx
  have he := periodized_cut_eq (2 * CoordinateAlgebra.A ActualPrimary.h)
    (fun l : SignedLabel B N0 => ActualPrimary.attachedRawPressure l.1 l.2)
    (fun l y => ActualPrimary.attachedRawPressure_core l.1 l.2 y)
    l n (ActualSignedGeometry.meanEquiv.symm x.1) x.2
  rw [periodized_pressure_eq l n hx x.2] at he
  simp only [ActualSignedGeometry.meanEquiv.apply_symm_apply,
    LinearWaveBounds.WaveCoefficients.withCutoff] at he ⊢
  exact he

end GaussianCutoff

section EnvelopeRange

variable {B N0 : ℕ}

theorem envelope_le_one (l : SignedLabel B N0) (n : ℕ) (x : Native) : envelope l n x ≤ 1 := by
  classical
  by_cases hc : ∃ k, x ∈ (copyCells l).carrier n k
  · obtain ⟨k, hk⟩ := hc
    rw [envelope_copy l n k hk]
    apply PrimaryPulseBounds.referenceP_le_one
      ((ActualPrimary.phases B N0 l.1).lam_pos l.2)
      ((ActualPrimary.phases B N0 l.1).u_pos l.2)
      ((ActualPrimary.phases B N0 l.1).L_pos l.2)
    have ht : (copyPoint l n k x).2.2 ∈ Icc 0 ((ActualPrimary.phases B N0 0).L l.2) := by
      have hh : (copyPoint l n k x).2 ∈ (ActualPrimary.clockWindow l.2).core := by
        simp only [copyPoint, ActualSignedGeometry.copyPoint] at hk ⊢
        exact hk
      exact hh.2
    simpa only [ActualPrimary.length_sign l.1 l.2] using ht
  · have hz : ∀ k : TorusInverse.Frequency,
        (ActualPrimary.chartGeometry n l.1 l.2).coordinates k x.2 ∉
          WaveEnvelopeTransport.rectangle ActualPrimary.slots.radius ((ActualPrimary.phases B N0
            l.1).L l.2) := by
      intro k hk
      apply hc
      refine ⟨k, ?_⟩
      simp only [ActualPrimary.length_sign l.1 l.2] at hk
      exact hk
    simp only [envelope, WaveEnvelopeTransport.copyEnvelope, ite_eq_right (hz _), tsum_zero,
      zero_le_one]

theorem fullEnvelope_nonneg (l : SignedLabel B N0) (n : ℕ) (x : ActualPrimary.FullPoint) :
    0 ≤ fullEnvelope l n x := envelope_nonneg l n _

theorem fullEnvelope_le_one (l : SignedLabel B N0) (n : ℕ) (x : ActualPrimary.FullPoint) :
    fullEnvelope l n x ≤ 1 := envelope_le_one l n _

noncomputable def meanEnvelope (l : SignedLabel B N0) (n : ℕ) (x : Point) : ℝ :=
  fullEnvelope l n (x, 0)

noncomputable def angularFrequency (l : SignedLabel B N0) (_n : ℕ) : ℤ :=
  PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
    (ActualPrimary.choice B N0).prepared l.1 l.2

noncomputable def phase (l : SignedLabel B N0) (n : ℕ) (x : Point) : ℝ :=
  (ActualPrimary.chartCoefficients l.1 l.2).phase n (x, 0)

theorem tangent_block_uniform :
    (∀ i m, LabelSumBounds.UniformWaveClass strip meanEnvelope (1 / 2)
      (fun l : SignedLabel B N0 => fun n x =>
        ((ActualPrimary.piece region l.1 l.2).tangentBlock (phase l) (angularFrequency l)).velocity
          n i m x)) ∧
    (∀ m, LabelSumBounds.UniformWaveClass strip meanEnvelope 1
      (fun l : SignedLabel B N0 => fun n x =>
        ((ActualPrimary.piece region l.1 l.2).tangentBlock (phase l) (angularFrequency l)).pressure
          n m x)) :=
  UniformBlockBounds.blockOfCoefficients_product_uniform
    (fun l : SignedLabel B N0 => (ActualPrimary.chartCoefficients l.1 l.2).withCutoff
      (ActualPrimary.chartCutoff l.1 l.2)) angularFrequency
    chart_cut_amplitude_uniform chart_cut_pressure_uniform

end EnvelopeRange

section LocalControl

variable {B N0 : ℕ}

abbrev CopyIndex (B N0 : ℕ) := SignedLabel B N0 × TorusInverse.Frequency

noncomputable def fullCopy (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency)
    (x : ActualPrimary.FullPoint) : Native := copyPoint l n k (ActualSignedGeometry.meanEquiv.symm
      x.1)

noncomputable def controlCell (n : ℕ) (i : CopyIndex B N0) : Set ActualPrimary.FullPoint :=
  {x | near i.1 n ∧
    (fullCopy i.1 n i.2 x).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
        N0).prepared.N).carrier i.1.2 ∧
    (fullCopy i.1 n i.2 x).2 ∈ (ActualPrimary.clockWindow i.1.2).core ∧
    SimilarityHomogeneity.chartQ ActualPrimary.h (fullCopy i.1 n i.2 x).1 ∈ Icc (1 / 2 : ℝ) 2}

noncomputable def fullStrip : StripData ActualPrimary.FullPoint :=
  HarmonicWaveInteraction.productStrip strip

noncomputable def nativeOfFull : ActualPrimary.FullPoint →L[ℝ] Native :=
  ActualSignedGeometry.meanEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ Point ℝ)

theorem nativeOfFull_norm : ‖nativeOfFull‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖ActualSignedGeometry.meanEquiv.symm x.1‖ ≤ 1 * ‖x‖
  rw [ActualSignedGeometry.meanEquiv.symm.norm_map, one_mul]
  exact norm_fst_le x

noncomputable def slotOfNative : Native →L[ℝ] (PhaseCalculus.Slow × ℝ) :=
  (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow TorusInverse.Plane).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ PhaseCalculus.Slow
      TorusInverse.Plane))

theorem slotOfNative_norm : ‖slotOfNative‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change max ‖x.1‖ ‖x.2.2‖ ≤ 1 * ‖x‖
  rw [one_mul]
  exact max_le (norm_fst_le x) ((norm_snd_le x.2).trans (norm_snd_le x))

noncomputable def slotLinear (l : SignedLabel B N0) (n : ℕ) :
    ActualPrimary.FullPoint →L[ℝ] (PhaseCalculus.Slow × ℝ) :=
  slotOfNative.comp ((copyLinear l n).comp nativeOfFull)

theorem slotLinear_bound {l : SignedLabel B N0} {n : ℕ} (hn : near l n) :
    ‖slotLinear l n‖ ≤ copyCost * fullStrip.slow n := by
  calc
    _ ≤ ‖slotOfNative‖ * (‖copyLinear l n‖ * ‖nativeOfFull‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖copyLinear l n‖ * 1) := by gcongr <;> first | exact slotOfNative_norm | exact
      nativeOfFull_norm
    _ ≤ _ := by simp only [one_mul, mul_one]; exact copyLinear_bound hn

theorem slotCopy_affine (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency) (x :
  ActualPrimary.FullPoint) :
    ((fullCopy l n k x).1, (fullCopy l n k x).2.2) =
      slotLinear l n x + slotOfNative (copyPoint l n k 0) := by
  change slotOfNative (copyPoint l n k (nativeOfFull x)) = _
  rw [copyPoint_affine, map_add]
  rfl

theorem control_maps {i : CopyIndex B N0} {n : ℕ} {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ controlCell n i) :
    ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2) ∈
      (ActualPhaseDefect.reducedJetDomain ActualPhaseDefect.paddedRegion).carrier i.1 := by
  have hr := copyPoint_radial i.1 n i.2 (x := ActualSignedGeometry.meanEquiv.symm x.1) hx
  apply ActualPhaseDefect.native_reduced_domain_mem ActualPhaseDefect.paddedRegion i.1.1 i.1.2
    hc.2.1
    (ActualPhaseDefect.padded_slow_mem hr.1 hc.2.2.2 hr.2)
  simp only [ActualPrimary.length_sign i.1.1 i.1.2]
  exact hc.2.2.1.2

/-- Actual affine pullback of polynomial native jets, with constants
uniform over the active label, chart, and lattice copy. -/
theorem polynomial_on_control {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : SignedLabel B N0 → PhaseCalculus.Slow × ℝ → E}
    (hf : PolynomialJets (ActualPhaseDefect.reducedJetDomain ActualPhaseDefect.paddedRegion) f) :
    LocalizedWaveBounds.LocalUnweighted fullStrip controlCell 0
      (fun n i x => f i.1 ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2)) := by
  let D := ActualPhaseDefect.reducedJetDomain (B := B) (N0 := N0) ActualPhaseDefect.paddedRegion
  refine ⟨fun _ _ _ _ => zero_le_one, ?_, ?_⟩
  · intro n i x hx hc
    have hm := control_maps hx hc
    rw [slotCopy_affine] at hm
    have hh := ((hf.smooth i.1).contDiffAt ((D.isOpen i.1).mem_nhds hm)).comp x
      (((slotLinear i.1 n).contDiff.add
        (contDiff_const (c := slotOfNative (copyPoint i.1 n i.2 0)))).contDiffAt)
    simpa only [← slotCopy_affine, Function.comp_def] using hh
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bound m
    have hcost := copyCost_one
    refine ⟨C * 25 ^ p * copyCost ^ m, by positivity, p + m, ?_⟩
    intro n i x hx hc j hj
    have hG := fullStrip.one_le_growth n x
    have hS := fullStrip.one_le_slow n
    have hm := control_maps hx hc
    have hscale : D.scale i.1 ≤ 25 * fullStrip.growth n x := by
      exact (ActualSignedGeometry.S_window_le hc.1.1 (near_distance hc.1).2).trans
        (mul_le_mul_of_nonneg_left
          ((le_max_right 1 (ChartScales.S n)).trans (fullStrip.slow_le_growth n x)) (by norm_num))
    have hlin : ‖slotLinear i.1 n‖ ^ j ≤ copyCost ^ m * fullStrip.growth n x ^ m := by
      calc
        _ ≤ (copyCost * fullStrip.slow n) ^ m :=
          (pow_le_pow_left₀ (norm_nonneg _) (slotLinear_bound hc.1) j).trans
            (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hcost hS) hj)
        _ ≤ (copyCost * fullStrip.growth n x) ^ m := by gcongr; exact fullStrip.slow_le_growth n x
        _ = _ := mul_pow _ _ _
    have hu := norm_jet_comp_affine (D.isOpen i.1) (hf.smooth i.1)
      (slotLinear i.1 n) (slotOfNative (copyPoint i.1 n i.2 0))
      (by simpa only [← slotCopy_affine] using hm) j
    simp only [← slotCopy_affine] at hu
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (f i.1) ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2)‖ *
          ‖slotLinear i.1 n‖ ^ j := hu
      _ ≤ (C * (25 * fullStrip.growth n x) ^ p) * (copyCost ^ m * fullStrip.growth n x ^ m) := by
        have hfb := (hb i.1 j hj _ hm).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans (D.one_le_scale i.1)) hscale p) (zero_le_one.trans
            hC))
        exact mul_le_mul hfb hlin (pow_nonneg (norm_nonneg _) _) ((norm_nonneg _).trans hfb)
      _ = majorant fullStrip (fun _ _ => 1) 0 (C * 25 ^ p * copyCost ^ m) (p + m) n x := by
        rw [majorant, mul_pow, pow_add, Real.rpow_zero]
        ring

noncomputable def jointPhase : PhaseFamily (SignedLabel B N0) where
  epsilon l := (ActualPrimary.phases B N0 l.1).phase.epsilon l.2
  p l := (ActualPrimary.phases B N0 l.1).phase.p l.2
  pz l := (ActualPrimary.phases B N0 l.1).phase.pz l.2
  x0 l := (ActualPrimary.phases B N0 l.1).phase.x0 l.2
  theta l := (ActualPrimary.phases B N0 l.1).phase.theta l.2
  F l := (ActualPrimary.phases B N0 l.1).phase.F l.2
  G l := (ActualPrimary.phases B N0 l.1).phase.G l.2

theorem native_normal_polynomial :
    PolynomialJets (ActualPhaseDefect.reducedJetDomain ActualPhaseDefect.paddedRegion)
      (jointPhase (B := B) (N0 := N0)).normal := by
  let D := ActualPhaseDefect.reducedSlowDomain (B := B) (N0 := N0) ActualPhaseDefect.paddedRegion
  let M := (ActualPrimary.phases B N0 0).M + (ActualPrimary.phases B N0 1).M
  let r := min (ActualPrimary.phases B N0 0).r (ActualPrimary.phases B N0 1).r
  have hM0 := (ActualPrimary.phases B N0 0).one_le_M
  have hM1 := (ActualPrimary.phases B N0 1).one_le_M
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hMj (j : Fin 2) : (ActualPrimary.phases B N0 j).M ≤ M := by
    fin_cases j <;> dsimp [M] <;> linarith
  have hr : 0 < r := lt_min (ActualPrimary.phases B N0 0).r_pos (ActualPrimary.phases B N0 1).r_pos
  have hrj (j : Fin 2) : r ≤ (ActualPrimary.phases B N0 j).r := by
    fin_cases j
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hF : PolynomialJets D (jointPhase (B := B) (N0 := N0)).F :=
    PrimaryGeometryAssembly.polynomial_restrict_reindex (ActualPrimary.phases B N0 0).baseF Prod.snd
      (fun _ => rfl) (fun _ _ hx => hx.1)
  have hG : PolynomialJets D (jointPhase (B := B) (N0 := N0)).G :=
    PrimaryGeometryAssembly.polynomial_restrict_reindex (ActualPrimary.phases B N0 0).baseG Prod.snd
      (fun _ => rfl) (fun _ _ hx => hx.1)
  have hh := (jointPhase (B := B) (N0 := N0)).polynomial_jets D
    (fun l => (ActualPrimary.phases B N0 l.1).V l.2)
    (fun l => (ActualPrimary.phases B N0 l.1).openV l.2) hF hG hr hM
    (fun l => by
      have h := (ActualPrimary.phases B N0 l.1).constants l.2
      exact ⟨h.1.trans (hMj _), h.2.1.trans (hMj _), h.2.2.1.trans (hMj _), h.2.2.2.trans (hMj _)⟩)
    (fun l => (ActualPrimary.phases B N0 l.1).epsilon_ne l.2)
    (fun l p hp => by
      have h := (ActualPrimary.phases B N0 l.1).radius l.2 p hp.1
      exact ⟨(hrj _).trans h.1, h.2.trans (hMj _)⟩)
    (fun l t ht => ((ActualPrimary.phases B N0 l.1).slot l.2 t ht).trans
      (mul_le_mul_of_nonneg_right (hMj _) (zero_le_one.trans (D.one_le_scale l))))
  exact hh.1

end LocalControl

section ActualNormal

variable {B N0 : ℕ}

theorem context_normal_swap
    (c : CorrectionState.Context Point) (s : StripData Point)
    (a : LinearWaveBounds.WaveCoefficients ActualPrimary.FullPoint)
    (n : ℕ) (G : PhysicalResidualBridge.ScaledGraph)
    (hG : PhysicalResidualTZ.MatchesAtTZ c.operators G n)
    (hepsilon : s.epsilon n = c.operators.epsilon n)
    (hradius : a.radius n = fun x => x.1.1)
    (Φ : PhysicalResidualBridge.Cylinder → ℝ)
    (hphase : a.phase n = fun y => Φ (PhysicalResidualTZ.swapCylinder y))
    (x : ActualPrimary.FullPoint) :
    a.normal (HarmonicWaveInteraction.productStrip s) (PrimaryResidualClass.directions c) n x =
      HarmonicCalculus.phaseNormal PhysicalResidualBridge.ScaledGraph.radius G.radial
        PhysicalResidualBridge.ScaledGraph.angular G.axial Φ (PhysicalResidualTZ.swapCylinder x) :=
          by
  have hr : PhysicalResidualTZ.swapCylinder ((PrimaryResidualClass.directions c).radialField n x) =
      G.radial (PhysicalResidualTZ.swapCylinder x) := by
    simp [PrimaryResidualClass.directions, LinearWaveBounds.GraphDirections.radialField,
      PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply,
      hG.eR, hG.vR, hG.frequency, hG.profile, PhysicalResidualBridge.ScaledGraph.radial, smul_smul]
  have hz : PhysicalResidualTZ.swapCylinder ((PrimaryResidualClass.directions c).axialField
      (HarmonicWaveInteraction.productStrip s) n x) = G.axial (PhysicalResidualTZ.swapCylinder x)
        := by
    simp [PrimaryResidualClass.directions, LinearWaveBounds.GraphDirections.axialField,
      PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply,
      hG.eZ, hepsilon, hG.epsilon, PhysicalResidualBridge.ScaledGraph.axial,
      HarmonicWaveInteraction.productStrip, HarmonicWaveInteraction.pullbackStrip]
  have ha : PhysicalResidualTZ.swapCylinder (PrimaryResidualClass.directions c).angular =
      PhysicalResidualBridge.ScaledGraph.angular (PhysicalResidualTZ.swapCylinder x) := rfl
  have hd (z : ActualPrimary.FullPoint) :
      fderiv ℝ (fun y => Φ (PhysicalResidualTZ.swapCylinder y)) x z =
        fderiv ℝ Φ (PhysicalResidualTZ.swapCylinder x) (PhysicalResidualTZ.swapCylinder z) :=
    PhysicalResidualTZ.fderiv_reindex PhysicalResidualTZ.swapCylinder.toContinuousLinearEquiv Φ x z
  unfold LinearWaveBounds.WaveCoefficients.normal HarmonicCalculus.phaseNormal
    HarmonicCalculus.along
  rw [hphase]
  simp only [hd, hr, hz, ha, hradius]
  rfl

noncomputable def normalScale (l : SignedLabel B N0) (n : ℕ) : ℝ :=
  PhysicalParticularWave.normalWeight (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand l.2))
    (ChartScales.carrier ActualPrimary.h n) (ChartScales.carrier ActualPrimary.h
      (BaseChartJets.cellBand l.2))

noncomputable def chartNormal (l : SignedLabel B N0) (n : ℕ) : ActualPrimary.FullPoint →
  ProblemStatement.Space :=
  (ActualPrimary.chartCoefficients l.1 l.2).normal fullStrip
    (PrimaryResidualClass.directions (ActualPrimary.commonContext B)) n

theorem fullCopy_slot (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency)
    (x : ActualPrimary.FullPoint) :
    (fullCopy l n k x).2 =
      (ActualSignedGeometry.slotGeometry ActualPrimary.slots ActualPrimary.vectors_det
        (spatialLabel l)
        (ChartScales.nativeIndex ActualPrimary.h (spatialLabel l).1 - CommonWindow.index
          ActualPrimary.h n)).coordinates
          k (ActualSignedGeometry.meanEquiv.symm x.1).2 := rfl

theorem chart_normal_germ {i : CopyIndex B N0} {n : ℕ} {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ controlCell n i) :
    chartNormal i.1 n =ᶠ[𝓝 x] fun y => normalScale i.1 n •
      (jointPhase (B := B) (N0 := N0)).normal i.1
        ((fullCopy i.1 n i.2 y).1, (fullCopy i.1 n i.2 y).2.2) := by
  let P := ActualPrimary.phases B N0 i.1.1
  let l := spatialLabel i.1
  let gap := ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand i.1.2) -
    CommonWindow.index ActualPrimary.h n
  have hp : ActualSignedGeometry.slowChange ActualPrimary.h (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand i.1.2))
      ((PhysicalResidualTZ.swapCylinder x).1.1, (PhysicalResidualTZ.swapCylinder x).1.2.1) ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
        N0).prepared.N).carrier i.1.2 := hc.2.1
  have hcore : (ActualSignedGeometry.slotGeometry ActualPrimary.slots
    ActualSignedGeometry.vectors_det l 0).coordinates i.2
      (CommonCoverSolve.coverPower gap (PhysicalResidualTZ.swapCylinder x).1.2.2) ∈
      (ActualSignedGeometry.clockWindow ActualPrimary.slots l.1).core := by
    erw [ActualSignedGeometry.slot_coordinates_from_zero]
    have hl : l.1 = BaseChartJets.cellBand i.1.2 := rfl
    have hg : gap = ChartScales.nativeIndex ActualPrimary.h (spatialLabel i.1).1 -
      CommonWindow.index ActualPrimary.h n := rfl
    have hY : (PhysicalResidualTZ.swapCylinder x).1.2.2 = (ActualSignedGeometry.meanEquiv.symm
      x.1).2 := rfl
    rw [hg, hY, ← fullCopy_slot]
    rw [hl, ← clock_eq i.1]
    exact hc.2.2.1
  have hxR : 0 < x.1.1 := BaseContextAssembly.nativeStrip_radius ActualPrimary.nominal region hx
  have hphys := ActualSignedGeometry.phase_normal_view_germ ActualPrimary.slots
    ActualPrimary.outgoing.data.h_pos.le (label_large i.1) (CommonWindow.index ActualPrimary.h n)
      gap
    (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand i.1.2))
    (ChartScales.carrier ActualPrimary.h n) (ChartScales.carrier ActualPrimary.h
      (BaseChartJets.cellBand i.1.2))
    (P.phase.p i.1.2) (P.phase.pz i.1.2) (P.phase.x0 i.1.2) (P.phase.F i.1.2) (P.phase.G i.1.2)
    ((PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
      N0).prepared.N).isOpen i.1.2)
    (P.baseF.smooth i.1.2) (P.baseG.smooth i.1.2) i.2 (P.phase.theta i.1.2)
    (x := PhysicalResidualTZ.swapCylinder x)
    hxR hp hcore
  have hfull := hphys.comp_tendsto PhysicalResidualTZ.swapCylinder.continuous.continuousAt
  filter_upwards [hfull] with y hy
  rw [chartNormal, fullStrip, context_normal_swap (ActualPrimary.commonContext B) strip
    (ActualPrimary.chartCoefficients i.1.1 i.1.2) n
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) ActualPrimary.h (CommonWindow.index
      ActualPrimary.h n))
    (CommonBaseContext.context_matches_physical ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B _ n)
    rfl rfl
    (ActualSignedGeometry.preparedViewPhase ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.slots
      (ActualPrimary.choice B N0).prepared i.1.1 i.1.2 n (CommonWindow.index ActualPrimary.h n))
    (funext (ActualPrimary.chartCoefficients_phase_view i.1.1 i.1.2 n (CommonWindow.index_le
      hc.1.2)))]
  apply hy.trans
  change normalScale i.1 n • _ = normalScale i.1 n • _
  apply congrArg (fun z => normalScale i.1 n • z)
  change PhaseCalculus.phaseNormal _ _ _ _ _ _ _ = PhaseCalculus.phaseNormal _ _ _ _ _ _ _
  erw [ActualSignedGeometry.slot_coordinates_from_zero]
  rfl

noncomputable def normalLower : ℝ :=
  (1 / 2 : ℝ) * (1 / ActualSignedGeometry.powerBound (ActualPrimary.h / 2 + 1 / 2))

noncomputable def normalUpper : ℝ :=
  2 * ActualSignedGeometry.powerBound (ActualPrimary.h / 2 + 1 / 2)

theorem normalLower_pos : 0 < normalLower := by
  have h := ActualSignedGeometry.powerBound_one (ActualPrimary.h / 2 + 1 / 2)
  unfold normalLower
  positivity

theorem normalUpper_pos : 0 < normalUpper := by
  have h := ActualSignedGeometry.powerBound_one (ActualPrimary.h / 2 + 1 / 2)
  unfold normalUpper
  positivity

theorem normalScale_bounds {l : SignedLabel B N0} {n : ℕ} (hn : near l n) :
    normalLower ≤ normalScale l n ∧ normalScale l n ≤ normalUpper := by
  let hnear : ∀ (_ : Unit) (_ : ℕ), n ≤ BaseChartJets.cellBand l.2 + 4 ∧
      BaseChartJets.cellBand l.2 ≤ n + 4 := fun _ _ => near_distance hn
  have hs := (ActualSignedGeometry.normalScale (fun _ => n)
    (fun (_ : Unit) _ => BaseChartJets.cellBand l.2) hnear
      ActualPrimary.outgoing.data.h_pos.le).bounds () 0
  rw [ActualSignedGeometry.normalScale_value] at hs
  exact hs

/-- A bound on an index-dependent constant is already a local all-jet
bound, with the constant chosen before the index. -/
theorem local_constant {s : StripData ActualPrimary.FullPoint}
    {I : Type*} {K : ℕ → I → Set ActualPrimary.FullPoint} {r : ℕ → I → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hr : ∀ n i x, x ∈ s.domain → x ∈ K n i → |r n i| ≤ C) :
    LocalizedWaveBounds.LocalUnweighted s K 0 (fun n i _ => r n i) := by
  refine ⟨fun _ _ _ _ => zero_le_one, fun _ _ _ _ _ => contDiffAt_const,
    fun m => ⟨C, hC, 0, ?_⟩⟩
  intro n i x hx hi j _
  cases j with
  | zero =>
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, majorant,
      Real.rpow_zero, pow_zero, mul_one] using hr n i x hx hi
  | succ j => simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, majorant,
      Real.rpow_zero, pow_zero, mul_one] using hC

theorem normalScale_local : LocalizedWaveBounds.LocalUnweighted fullStrip (controlCell (B := B) (N0
  := N0)) 0
    (fun n i (_ : ActualPrimary.FullPoint) => normalScale i.1 n) := by
  apply local_constant normalUpper_pos.le
  intro n i x _ hx
  have h := normalScale_bounds hx.1
  rw [abs_of_pos (normalLower_pos.trans_le h.1)]
  exact h.2

theorem chart_normal_local : LocalizedWaveBounds.LocalUnweighted fullStrip (controlCell (B := B)
  (N0 := N0)) 0
    (fun n i => chartNormal i.1 n) := by
  have hn := LocalizedWaveBounds.unweighted_smul (normalScale_local (B := B) (N0 := N0))
    (polynomial_on_control native_normal_polynomial)
  have hn' : LocalizedWaveBounds.LocalUnweighted fullStrip controlCell 0
      (fun n i x => normalScale i.1 n • (jointPhase (B := B) (N0 := N0)).normal i.1
        ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2)) := by
    simpa only [zero_add] using hn
  exact hn'.congr_germ (fun _ _ _ hx hc => (chart_normal_germ hx hc).symm)

noncomputable def normalFloor (B N0 : ℕ) : ℝ :=
  normalLower * min (ActualPrimary.phases B N0 0).b (ActualPrimary.phases B N0 1).b

noncomputable def normalCeiling (B N0 : ℕ) : ℝ :=
  normalUpper * max ((ActualPrimary.phases B N0 0).M ^ 2 + 3 * (ActualPrimary.phases B N0 0).M)
    ((ActualPrimary.phases B N0 1).M ^ 2 + 3 * (ActualPrimary.phases B N0 1).M)

theorem normalFloor_pos (B N0 : ℕ) : 0 < normalFloor B N0 :=
  mul_pos normalLower_pos (lt_min (ActualPrimary.phases B N0 0).b_pos (ActualPrimary.phases B N0
    1).b_pos)

theorem chart_normal_range {i : CopyIndex B N0} {n : ℕ} {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ controlCell n i) :
    normalFloor B N0 ≤ ‖chartNormal i.1 n x‖ ∧
      ‖chartNormal i.1 n x‖ ≤ normalCeiling B N0 := by
  let P := ActualPrimary.phases B N0 i.1.1
  have ht : (fullCopy i.1 n i.2 x).2.2 ∈ P.V i.1.2 :=
    P.interval i.1.2 (by erw [ActualPrimary.length_sign i.1.1 i.1.2]; exact hc.2.2.1.2)
  have hdom : ((fullCopy i.1 n i.2 x).1, (fullCopy i.1 n i.2 x).2.2) ∈
      ((PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
        N0).prepared.N).slot P.V P.openV).carrier i.1.2 :=
    ⟨hc.2.1, ht⟩
  have hlow := P.normal_range.1 i.1.2 _ hdom
  have hupp := P.normal_range.2 i.1.2 _ hdom
  have hscale := normalScale_bounds hc.1
  rw [(chart_normal_germ hx hc).eq_of_nhds, norm_smul, Real.norm_eq_abs,
    abs_of_pos (normalLower_pos.trans_le hscale.1)]
  have hj : i.1.1 = 0 ∨ i.1.1 = 1 := by omega
  have hb : min (ActualPrimary.phases B N0 0).b (ActualPrimary.phases B N0 1).b ≤ P.b := by
    rcases hj with h | h <;> simp only [P, h]
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hM : P.M ^ 2 + 3 * P.M ≤
      max ((ActualPrimary.phases B N0 0).M ^ 2 + 3 * (ActualPrimary.phases B N0 0).M)
        ((ActualPrimary.phases B N0 1).M ^ 2 + 3 * (ActualPrimary.phases B N0 1).M) := by
    rcases hj with h | h <;> simp only [P, h]
    · exact le_max_left _ _
    · exact le_max_right _ _
  exact ⟨mul_le_mul hscale.1 (hb.trans hlow)
      (le_min (ActualPrimary.phases B N0 0).b_pos.le (ActualPrimary.phases B N0 1).b_pos.le)
      (normalLower_pos.trans_le hscale.1).le,
    mul_le_mul hscale.2 (hupp.trans hM) (norm_nonneg _) normalUpper_pos.le⟩

theorem chart_defect_local : LocalizedWaveBounds.LocalUnweighted fullStrip (controlCell (B := B)
  (N0 := N0)) 1
    (fun n i => ActualPhaseDefect.defect i.1.1 i.1.2 n) := by
  have hweight : LocalizedWaveBounds.LocalUnweighted fullStrip (controlCell (B := B) (N0 := N0)) 0
      (fun n i (_ : ActualPrimary.FullPoint) => ActualPhaseDefect.materialWeight i.1.2 n) := by
    apply local_constant (show 0 ≤ ActualPhaseDefect.materialWeightBound by
      have h0 := ActualSignedGeometry.powerBound_one (ActualPrimary.h / 2 + 1 / 2)
      have h1 := ActualSignedGeometry.powerBound_one (CoordinateAlgebra.A ActualPrimary.h -
        ActualPrimary.h)
      unfold ActualPhaseDefect.materialWeightBound
      positivity)
    intro n i x _ hc
    obtain ⟨hp, hu⟩ := ActualPhaseDefect.active_materialWeight_bound i.1.2 n hc.1.2
    simpa only [abs_of_pos hp] using hu
  have hr := polynomial_on_control (ActualPhaseDefect.native_reduced_polynomial
    (B := B) (N0 := N0) ActualPhaseDefect.paddedRegion)
  have hm := (LocalizedWaveBounds.unweighted_mul hweight hr).band_smul
    (LinearWaveBounds.band_epsilon fullStrip)
  have hm' : LocalizedWaveBounds.LocalUnweighted fullStrip (controlCell (B := B) (N0 := N0)) 1
      (fun n i x => ChartScales.epsilon ActualPrimary.h n * ActualPhaseDefect.materialWeight i.1.2
        n *
        ActualPhaseDefect.reducedExpression i.1.1 i.1.2 n i.2 x) := by
    simp only [zero_add, smul_eq_mul, mul_assoc, ActualPhaseDefect.reducedExpression_eq_native] at
      hm ⊢
    exact hm
  apply hm'.congr_germ
  intro n i x hx hc
  apply Filter.EventuallyEq.symm
  apply ActualPhaseDefect.active_copy_defect_germ i.1.1 i.1.2 n hc.1.2 i.2 hx hc.2.1
  rw [← clock_eq i.1]
  exact hc.2.2.1

end ActualNormal

section ActualLocalInputs

variable {B N0 : ℕ}

noncomputable def cutCoefficients (l : SignedLabel B N0) :
    LinearWaveBounds.WaveCoefficients ActualPrimary.FullPoint :=
  (ActualPrimary.chartCoefficients l.1 l.2).withCutoff (ActualPrimary.chartCutoff l.1 l.2)

noncomputable def actualFamily : LocalizedWaveBounds.WaveFamily ActualPrimary.FullPoint (CopyIndex
  B N0) :=
  LocalizedWaveBounds.WaveFamily.ofCoefficients (fun i => cutCoefficients i.1)

noncomputable def directions (B : ℕ) := PrimaryResidualClass.directions
  (ActualPrimary.commonContext B)

theorem actualFamily_normal_eq :
    (actualFamily (B := B) (N0 := N0)).normal fullStrip (directions B) =
      fun n i => chartNormal i.1 n := by
  funext n i x
  simp only [LocalizedWaveBounds.WaveFamily.normal, LocalizedWaveBounds.WaveFamily.coefficients,
    actualFamily, LocalizedWaveBounds.WaveFamily.ofCoefficients, cutCoefficients,
    LinearWaveBounds.WaveCoefficients.withCutoff, LinearWaveBounds.WaveCoefficients.normal,
    chartNormal, directions]

theorem actualFamily_defect_eq :
    (actualFamily (B := B) (N0 := N0)).defect fullStrip (directions B) =
      fun n i => ActualPhaseDefect.defect i.1.1 i.1.2 n := by
  funext n i x
  simp only [LocalizedWaveBounds.WaveFamily.defect, LocalizedWaveBounds.WaveFamily.coefficients,
    actualFamily, LocalizedWaveBounds.WaveFamily.ofCoefficients, cutCoefficients,
    LinearWaveBounds.WaveCoefficients.withCutoff, LinearWaveBounds.WaveCoefficients.defect,
    ActualPhaseDefect.defect, directions, fullStrip, strip, region, ActualPrimary.standardRegion]

theorem actualFamily_normal_range {i : CopyIndex B N0} {n : ℕ} {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∈ controlCell n i) :
    normalFloor B N0 ≤ ‖(actualFamily (B := B) (N0 := N0)).normal fullStrip (directions B) n i x‖ ∧
      ‖(actualFamily (B := B) (N0 := N0)).normal fullStrip (directions B) n i x‖ ≤ normalCeiling B
        N0 := by
  rw [actualFamily_normal_eq]
  exact chart_normal_range hx hc

theorem actualFamily_good_eq :
    (actualFamily (B := B) (N0 := N0)).retainedGood fullStrip (directions B) =
      fun n i => (ActualPrimary.piece region i.1.1 i.1.2).linearGood n := by
  funext n i x
  simp only [LocalizedWaveBounds.WaveFamily.retainedGood,
    LocalizedWaveBounds.WaveFamily.principalVelocity, LocalizedWaveBounds.WaveFamily.remainder,
    LocalizedWaveBounds.WaveFamily.addAmplitude, LocalizedWaveBounds.WaveFamily.curlCorrection,
    LocalizedWaveBounds.WaveFamily.coefficients, actualFamily,
    LocalizedWaveBounds.WaveFamily.ofCoefficients, cutCoefficients,
    PrimaryPiece.linearGood, ActualPrimary.piece, LinearWaveBounds.WaveCoefficients.constructedGood,
    LinearWaveBounds.WaveCoefficients.goodCoefficient,
      LinearWaveBounds.WaveCoefficients.principalVelocity,
    LinearWaveBounds.WaveCoefficients.remainder, LinearWaveBounds.WaveCoefficients.addAmplitude,
    LinearWaveBounds.WaveCoefficients.withCutoff, directions, fullStrip, strip]

theorem local_of_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : SignedLabel B N0 → ℕ → ActualPrimary.FullPoint → ℝ} {α : ℝ}
    {f : SignedLabel B N0 → ℕ → ActualPrimary.FullPoint → E}
    (hf : LabelSumBounds.UniformClass fullStrip w α f) :
    LocalizedWaveBounds.LocalClass fullStrip controlCell (fun n i => w i.1 n) α
      (fun n i => f i.1 n) := by
  refine ⟨fun n i x hx => hf.weight_nonneg i.1 n x hx,
    fun n i x hx _ => (hf.smooth i.1 n).contDiffAt (fullStrip.isOpen_domain.mem_nhds hx), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun n i x hx _ j hj => hb i.1 n x hx j hj⟩

theorem carrier_band : BandBound fullStrip (-(1 / 2 : ℝ))
    (fun n => (ChartScales.carrier ActualPrimary.h n : ℝ)) := by
  refine ⟨2, by norm_num, 0, fun n => ?_⟩
  have he := fullStrip.epsilon_pos n
  have hk : 0 < (ChartScales.carrier ActualPrimary.h n : ℝ) :=
    Scaling.carrier_frequency_pos he
  have hs := Real.sqrt_pos.mpr he
  have hu := (Scaling.carrier_frequency_sqrt_bounds he).2
  have hs1 := Real.sqrt_le_one.mpr (fullStrip.epsilon_le_one n)
  have hle : (ChartScales.carrier ActualPrimary.h n : ℝ) ≤ 2 / Real.sqrt (fullStrip.epsilon n) := by
    apply (le_div_iff₀ hs).mpr
    exact hu.trans (by linarith)
  rw [Real.sqrt_eq_rpow] at hle
  simpa only [Real.norm_eq_abs, abs_of_pos hk, pow_zero, mul_one,
    Real.rpow_neg he.le, div_eq_mul_inv] using hle

theorem inverse_carrier_band : BandBound fullStrip (1 / 2 : ℝ)
    (fun n => 1 / (ChartScales.carrier ActualPrimary.h n : ℝ)) := by
  have hb := CurlClassBounds.harmonic_inverse_bandBound fullStrip (fun _ => 1) (fun _ => by
    norm_num)
  simp only [Int.cast_one, mul_one] at hb
  exact hb

theorem inverse_carrier_local : LocalizedWaveBounds.LocalUnweighted fullStrip
    (controlCell (B := B) (N0 := N0)) (1 / 2 : ℝ)
    (fun n _ (_ : ActualPrimary.FullPoint) => 1 / (ChartScales.carrier ActualPrimary.h n : ℝ)) :=
  LocalizedWaveBounds.LocalClass.band_const inverse_carrier_band

theorem radius_unweighted : UnweightedClass fullStrip 0
    (fun _ (x : ActualPrimary.FullPoint) => x.1.1) := by
  have hr : UnweightedClass strip 0 (fun _ (x : Point) => x.1) := by
    apply BaseContextAssembly.radial_unweighted
      (a := BaseContextAssembly.geometryRadius ActualPrimary.nominal region)
      (b := Real.sqrt region.qhi * PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
      (g := id) _ contDiff_id
    intro x hx
    exact BaseContextAssembly.movingStrip_radial_bounds ActualPrimary.outgoing.data.h_pos.le region
      _ _ _ _ (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
      (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)) zero_lt_one hx
  exact HarmonicWaveInteraction.class_lift hr

theorem slow_auxiliary (B : ℕ) :
    BaseContextAssembly.slowCoordinates (directions B).auxiliary.1 = 0 := rfl

theorem slow_field_auxiliary (B : ℕ) (f : PhaseCalculus.Slow → ℝ) (x : ActualPrimary.FullPoint) :
    fderiv ℝ (fun y : ActualPrimary.FullPoint => f (BaseContextAssembly.slowCoordinates y.1)) x
      (directions B).auxiliary = 0 := by
  apply CopyAngularInvariance.Invariant.directional_zero
  intro y t
  change f (BaseContextAssembly.slowCoordinates (y.1 + t • (directions B).auxiliary.1)) = _
  rw [map_add, map_smul, slow_auxiliary, smul_zero, add_zero]

theorem actual_local_inputs :
    LocalizedWaveBounds.InputBounds fullStrip (controlCell (B := B) (N0 := N0))
      (fun n i => fullEnvelope i.1 n) (1 / 2 : ℝ) ChartScales.kappa (directions B) actualFamily :=
        by
  have ho := CommonBaseContext.context_operator_bounds ActualPrimary.certificate
    ActualPrimary.modulation
    ActualPrimary.upper B region (CommonWindow.index_le_native ActualPrimary.h)
  refine {
    loss_nonneg := by norm_num [ChartScales.kappa]
    radial_profile := LocalizedWaveBounds.LocalClass.of_global (HarmonicWaveInteraction.class_lift
      ho.radialProfile)
    radial_scale := ho.radialFrequency
    fast_scale := ho.fastCoefficient
    frequency_scale := LocalizedWaveBounds.LocalClass.band_const carrier_band
    radius := LocalizedWaveBounds.LocalClass.of_global radius_unweighted
    inverse_radius := LocalizedWaveBounds.LocalClass.of_global (HarmonicWaveInteraction.class_lift
      ho.invRadius)
    radial_base := LocalizedWaveBounds.LocalClass.of_global (HarmonicWaveInteraction.class_lift
      (BaseContextAssembly.radialBase_unweighted ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B region))
    frequency_base := LocalizedWaveBounds.LocalClass.of_global (HarmonicWaveInteraction.class_lift
      (BaseContextAssembly.frequencyBase_unweighted ActualPrimary.certificate
        ActualPrimary.modulation ActualPrimary.upper B region))
    axial_base := LocalizedWaveBounds.LocalClass.of_global (HarmonicWaveInteraction.class_lift
      (BaseContextAssembly.axialBase_unweighted ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B region))
    radial_base_aux := ?_
    frequency_base_aux := ?_
    axial_base_aux := ?_
    normal := by rw [actualFamily_normal_eq]; exact chart_normal_local
    defect := by rw [actualFamily_defect_eq]; exact chart_defect_local
    amplitude := fun j => local_of_uniform (chart_cut_amplitude_uniform.map
      (ContinuousLinearMap.proj j))
    pressure := ?_ }
  · intro n i x _ _
    exact Filter.Eventually.of_forall (slow_field_auxiliary B
      (BaseContextAssembly.radialSlow ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B n))
  · intro n i x _ _
    exact Filter.Eventually.of_forall (slow_field_auxiliary B
      (BaseContextAssembly.frequencySlow ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B n))
  · intro n i x _ _
    exact Filter.Eventually.of_forall (slow_field_auxiliary B
      (BaseContextAssembly.axialSlow ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B n))
  · have hp := local_of_uniform (chart_cut_pressure_uniform (B := B) (N0 := N0))
    simp only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
    exact hp

theorem actual_local_curl : LocalizedWaveBounds.LocalWave fullStrip
    (controlCell (B := B) (N0 := N0)) (fun n i => fullEnvelope i.1 n) (1 - ChartScales.kappa)
    (fun n i => (cutCoefficients i.1).curlCorrection fullStrip (directions B) n) := by
  convert! actual_local_inputs.curlCorrection_class (normalFloor_pos B N0)
    (fun _ _ _ hx hc => (actualFamily_normal_range hx hc).1)
    (fun _ _ _ hx hc => (actualFamily_normal_range hx hc).2)
    inverse_carrier_local using 1
  norm_num

theorem actual_local_good : LocalizedWaveBounds.LocalWave fullStrip
    (controlCell (B := B) (N0 := N0)) (fun n i => fullEnvelope i.1 n) (1 - 3 * ChartScales.kappa)
    (actualFamily.retainedGood fullStrip (directions B)) := by
  convert! actual_local_inputs.retainedGood_class (show ChartScales.kappa ≤ 1 / 2 by norm_num
    [ChartScales.kappa])
    (normalFloor_pos B N0) (fun _ _ _ hx hc => (actualFamily_normal_range hx hc).1)
    (fun _ _ _ hx hc => (actualFamily_normal_range hx hc).2) inverse_carrier_local using 1
  norm_num

end ActualLocalInputs

section ActualSupportCover

variable {B N0 : ℕ}

theorem cut_amplitude_eq (l : SignedLabel B N0) (n : ℕ) {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) :
    (cutCoefficients l).amplitude n x =
      periodized (CoordinateAlgebra.A ActualPrimary.h) cutNativeVelocity l n (nativeOfFull x) := by
  have hs (l : SignedLabel B N0) (y : Native)
      (hy : CurlClassBounds.complexify (ActualPrimary.attachedRawVelocity l.1 l.2 y) ≠ 0) :
      y.2 ∈ (ActualPrimary.clockWindow l.2).core := by
    apply ActualPrimary.attachedRawVelocity_core l.1 l.2 y
    intro hz
    exact hy (by rw [hz, map_zero])
  have he := periodized_cut_eq (CoordinateAlgebra.A ActualPrimary.h)
    (fun l : SignedLabel B N0 => fun y => CurlClassBounds.complexify
      (ActualPrimary.attachedRawVelocity l.1 l.2 y))
    hs l n (ActualSignedGeometry.meanEquiv.symm x.1) x.2
  rw [periodized_velocity_eq l n hx x.2] at he
  simp only [ActualSignedGeometry.meanEquiv.apply_symm_apply,
    cutCoefficients, LinearWaveBounds.WaveCoefficients.withCutoff] at he ⊢
  exact he.symm

theorem cut_pressure_eq (l : SignedLabel B N0) (n : ℕ) {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) :
    (cutCoefficients l).pressure n x =
      periodized (2 * CoordinateAlgebra.A ActualPrimary.h) cutNativePressure l n (nativeOfFull x)
        := by
  have he := periodized_cut_eq (2 * CoordinateAlgebra.A ActualPrimary.h)
    (fun l : SignedLabel B N0 => ActualPrimary.attachedRawPressure l.1 l.2)
    (fun l y => ActualPrimary.attachedRawPressure_core l.1 l.2 y)
    l n (ActualSignedGeometry.meanEquiv.symm x.1) x.2
  rw [periodized_pressure_eq l n hx x.2] at he
  simp only [ActualSignedGeometry.meanEquiv.apply_symm_apply,
    cutCoefficients, LinearWaveBounds.WaveCoefficients.withCutoff] at he ⊢
  exact he.symm

theorem cut_amplitude_germ (l : SignedLabel B N0) (n : ℕ) {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) :
    (cutCoefficients l).amplitude n =ᶠ[𝓝 x]
      fun y => periodized (CoordinateAlgebra.A ActualPrimary.h) cutNativeVelocity l n (nativeOfFull
        y) := by
  filter_upwards [fullStrip.isOpen_domain.mem_nhds hx] with y hy
  exact cut_amplitude_eq l n hy

theorem cut_pressure_germ (l : SignedLabel B N0) (n : ℕ) {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) :
    (cutCoefficients l).pressure n =ᶠ[𝓝 x]
      fun y => periodized (2 * CoordinateAlgebra.A ActualPrimary.h) cutNativePressure l n
        (nativeOfFull y) := by
  filter_upwards [fullStrip.isOpen_domain.mem_nhds hx] with y hy
  exact cut_pressure_eq l n hy

theorem copied_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : SignedLabel B N0 → Native → E)
    (hs : ∀ l x, f l x ≠ 0 → x.2 ∈ (ActualPrimary.clockWindow l.2).core)
    (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency) :
    support (copied a f l n k) ⊆ (copyCells l).carrier n k := by
  intro x hx
  classical
  by_cases hn : near l n
  · have hfn : f l (copyPoint l n k x) ≠ 0 := by
      intro hz
      exact hx (by simp only [copied, ite_eq_left hn, hz, smul_zero])
    have hk := hs l (copyPoint l n k x) hfn
    simp only [copyPoint, ActualSignedGeometry.copyPoint] at hk ⊢
    exact hk
  · exact (hx (by simp only [copied, ite_eq_right hn])).elim

theorem cut_native_velocity_support (l : SignedLabel B N0) (x : Native)
    (hx : cutNativeVelocity l x ≠ 0) : x.2 ∈ (ActualPrimary.clockWindow l.2).core := by
  apply ActualPrimary.attachedRawVelocity_core l.1 l.2 x
  intro hz
  exact hx (by simp only [cutNativeVelocity, hz, map_zero, smul_zero])

theorem cut_native_pressure_support (l : SignedLabel B N0) (x : Native)
    (hx : cutNativePressure l x ≠ 0) : x.2 ∈ (ActualPrimary.clockWindow l.2).core := by
  apply ActualPrimary.attachedRawPressure_core l.1 l.2 x
  intro hz
  exact hx (by simp only [cutNativePressure, hz, smul_zero])

theorem cut_native_zero_germs (l : SignedLabel B N0) {x : Native}
    (hT : 0 < x.1.2.2)
    (hout : x.1 ∉ (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
      N0).prepared.N).carrier l.2 ∨
      SimilarityHomogeneity.chartQ ActualPrimary.h x.1 ∉ Icc (1 / 2 : ℝ) 2) :
    (cutNativeVelocity l =ᶠ[𝓝 x] fun _ => 0) ∧ (cutNativePressure l =ᶠ[𝓝 x] fun _ => 0) := by
  have hz : (ActualPrimary.outerRawVelocity l.1 l.2 =ᶠ[𝓝 x] fun _ => 0) ∧
      (ActualPrimary.outerRawPressure l.1 l.2 =ᶠ[𝓝 x] fun _ => 0) := by
    have hh : (NativeBandExtension.bandVelocity ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos
          ActualPrimary.radialVector ActualPrimary.temporalVector l.1 l.2 =ᶠ[𝓝 x] fun _ => 0) ∧
      (NativeBandExtension.bandPressure ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos
          ActualPrimary.radialVector ActualPrimary.temporalVector l.1 l.2 =ᶠ[𝓝 x] fun _ => 0) := by
      rcases hout with hp | hq
      · exact NativeBandExtension.band_pair_zero_germ_cell ActualPrimary.certificate
        ActualPrimary.modulation
          (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos
            ActualPrimary.radialVector ActualPrimary.temporalVector l.1 l.2 hT hp
      · exact NativeBandExtension.band_pair_zero_germ_factor ActualPrimary.certificate
        ActualPrimary.modulation
          (ActualPrimary.choice B N0).prepared ActualPrimary.slots.radius_pos
            ActualPrimary.radialVector ActualPrimary.temporalVector l.1 l.2
          (NativeBandExtension.factor_zero_germ_band ActualPrimary.certificate
            ActualPrimary.modulation
            (ActualPrimary.choice B N0).prepared l.2 hT hq)
    simpa only [ActualPrimary.bandVelocity_eq, ActualPrimary.bandPressure_eq] using hh
  constructor
  · filter_upwards [hz.1] with y hy
    simp only [cutNativeVelocity, ActualPrimary.attachedRawVelocity,
      WaveEdgeExtension.nativeExtension, WaveEdgeExtension.extension, hy, ite_self, map_zero,
        smul_zero]
  · filter_upwards [hz.2] with y hy
    simp only [cutNativePressure, ActualPrimary.attachedRawPressure,
      WaveEdgeExtension.nativeExtension, WaveEdgeExtension.extension, hy, ite_self, smul_zero]

/-- Every point has either an actual controlled native copy, or a
neighborhood on which both literal input coefficients vanish. -/
theorem actual_input_cover (l : SignedLabel B N0) (n : ℕ) {x : ActualPrimary.FullPoint}
    (hx : x ∈ fullStrip.domain) :
    (∃ k, x ∈ controlCell n (l, k)) ∨
      ((cutCoefficients l).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
      ((cutCoefficients l).pressure n =ᶠ[𝓝 x] fun _ => 0) := by
  classical
  have ha := cut_amplitude_germ l n hx
  have hp := cut_pressure_germ l n hx
  have hsA := copied_support (CoordinateAlgebra.A ActualPrimary.h) cutNativeVelocity
    cut_native_velocity_support l n
  have hsP := copied_support (2 * CoordinateAlgebra.A ActualPrimary.h) cutNativePressure
    cut_native_pressure_support l n
  by_cases hn : near l n
  · by_cases he : ∃ k, nativeOfFull x ∈ (copyCells l).carrier n k
    · obtain ⟨k, hk⟩ := he
      have hcore : (fullCopy l n k x).2 ∈ (ActualPrimary.clockWindow l.2).core := by
        simp only [fullCopy, copyPoint, ActualSignedGeometry.copyPoint] at hk ⊢
        exact hk
      by_cases hc : (fullCopy l n k x).1 ∈
          (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B
            N0).prepared.N).carrier l.2 ∧
        SimilarityHomogeneity.chartQ ActualPrimary.h (fullCopy l n k x).1 ∈ Icc (1 / 2 : ℝ) 2
      · exact Or.inl ⟨k, hn, hc.1, hcore, hc.2⟩
      · right
        have hz := cut_native_zero_germs l (x := fullCopy l n k x)
          (copyPoint_radial l n k (x := nativeOfFull x) hx).1 (not_and_or.mp hc)
        have ht : Tendsto (fullCopy l n k) (𝓝 x) (𝓝 (fullCopy l n k x)) :=
          ((copyPoint_smooth l n k).continuous.comp nativeOfFull.continuous).continuousAt
        have hAz := hz.1.comp_tendsto ht
        have hPz := hz.2.comp_tendsto ht
        have hAg := (PeriodizedWaveBounds.copySum_germ (copyCells l) n
          (copied (CoordinateAlgebra.A ActualPrimary.h) cutNativeVelocity l n) hsA hk).comp_tendsto
            nativeOfFull.continuous.continuousAt
        have hPg := (PeriodizedWaveBounds.copySum_germ (copyCells l) n
          (copied (2 * CoordinateAlgebra.A ActualPrimary.h) cutNativePressure l n) hsP
            hk).comp_tendsto
            nativeOfFull.continuous.continuousAt
        constructor
        · filter_upwards [ha, hAg, hAz] with y hay hgy hzy
          change cutNativeVelocity l (fullCopy l n k y) = 0 at hzy
          simp only [Function.comp_apply] at hgy
          rw [hay]
          change PeriodizedWaveBounds.copySum _ (nativeOfFull y) = _
          rw [hgy]
          simp only [copied, ite_eq_left hn]
          change coefficientScale (CoordinateAlgebra.A ActualPrimary.h) l n •
            cutNativeVelocity l (fullCopy l n k y) = 0
          rw [hzy, smul_zero]
        · filter_upwards [hp, hPg, hPz] with y hpy hgy hzy
          change cutNativePressure l (fullCopy l n k y) = 0 at hzy
          simp only [Function.comp_apply] at hgy
          rw [hpy]
          change PeriodizedWaveBounds.copySum _ (nativeOfFull y) = _
          rw [hgy]
          simp only [copied, ite_eq_left hn]
          change coefficientScale (2 * CoordinateAlgebra.A ActualPrimary.h) l n •
            cutNativePressure l (fullCopy l n k y) = 0
          rw [hzy, smul_zero]
    · right
      have hAg := (PeriodizedWaveBounds.copySum_zero_germ (copyCells l) n
        (copied (CoordinateAlgebra.A ActualPrimary.h) cutNativeVelocity l n) hsA
        (not_exists.mp he)).comp_tendsto nativeOfFull.continuous.continuousAt
      have hPg := (PeriodizedWaveBounds.copySum_zero_germ (copyCells l) n
        (copied (2 * CoordinateAlgebra.A ActualPrimary.h) cutNativePressure l n) hsP
        (not_exists.mp he)).comp_tendsto nativeOfFull.continuous.continuousAt
      exact ⟨ha.trans hAg, hp.trans hPg⟩
  · right
    constructor
    · filter_upwards [ha] with y hy
      simpa only [periodized, PeriodizedWaveBounds.copySum, copied, ite_eq_right hn, tsum_zero]
        using hy
    · filter_upwards [hp] with y hy
      simpa only [periodized, PeriodizedWaveBounds.copySum, copied, ite_eq_right hn, tsum_zero]
        using hy

end ActualSupportCover

section UniformActualOutputs

variable {B N0 : ℕ}

theorem chart_curl_uniform : LabelSumBounds.UniformWaveClass fullStrip
    (fullEnvelope (B := B) (N0 := N0)) (1 - ChartScales.kappa)
    (fun l => (cutCoefficients l).curlCorrection fullStrip (directions B)) := by
  have hj : PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun l n x => Real.sqrt (fullStrip.zeta x) * fullEnvelope l n x)
      (1 - ChartScales.kappa) (fun (l : SignedLabel B N0) n k => controlCell n (l, k))
      (fun l n _k => (cutCoefficients l).curlCorrection fullStrip (directions B) n) :=
    actual_local_curl.to_uniformLocalJets
  apply PeriodizedWaveBounds.uniformClass_of_local_germs
    (fun l n x _ => mul_nonneg (Real.sqrt_nonneg _) (fullEnvelope_nonneg l n x)) hj
  intro l n x hx
  rcases actual_input_cover l n hx with ⟨k, hk⟩ | ⟨ha, hp⟩
  · exact Or.inl ⟨k, hk, Filter.EventuallyEq.rfl⟩
  · exact Or.inr ((actualFamily (B := B) (N0 := N0)).outputs_zero_germs fullStrip (directions B)
      (i := (l, 0)) ha hp).1

theorem chart_exact_amplitude_uniform : LabelSumBounds.UniformWaveClass fullStrip
    (fullEnvelope (B := B) (N0 := N0)) (1 / 2)
    (fun l => (ActualPrimary.piece region l.1 l.2).exactCoefficients.amplitude) := by
  have hc := (chart_curl_uniform (B := B) (N0 := N0)).mono_exponent
    (show (1 / 2 : ℝ) ≤ 1 - ChartScales.kappa by norm_num [ChartScales.kappa])
  exact chart_cut_amplitude_uniform.add hc

theorem chart_difference_uniform : LabelSumBounds.UniformWaveClass fullStrip
    (fullEnvelope (B := B) (N0 := N0)) (1 - ChartScales.kappa)
    (fun l n x => (ActualPrimary.piece region l.1 l.2).exactCoefficients.amplitude n x -
      (cutCoefficients l).amplitude n x) := by
  apply chart_curl_uniform.congr
  intro l n x _
  simp only [PrimaryPiece.exactCoefficients, ActualPrimary.piece,
    LinearWaveBounds.WaveCoefficients.corrected, LinearWaveBounds.WaveCoefficients.addAmplitude,
    cutCoefficients, add_sub_cancel_left]
  rfl

theorem chart_exact_pressure_uniform : LabelSumBounds.UniformWaveClass fullStrip
    (fullEnvelope (B := B) (N0 := N0)) 1
    (fun l => (ActualPrimary.piece region l.1 l.2).exactCoefficients.pressure) :=
  chart_cut_pressure_uniform

theorem chart_good_uniform : LabelSumBounds.UniformWaveClass fullStrip
    (fullEnvelope (B := B) (N0 := N0)) (1 - 3 * ChartScales.kappa)
    (fun l => (ActualPrimary.piece region l.1 l.2).linearGood) := by
  have hg := actual_local_good (B := B) (N0 := N0)
  rw [actualFamily_good_eq] at hg
  have hj : PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun l n x => Real.sqrt (fullStrip.zeta x) * fullEnvelope l n x)
      (1 - 3 * ChartScales.kappa) (fun (l : SignedLabel B N0) n k => controlCell n (l, k))
      (fun l n _k => (ActualPrimary.piece region l.1 l.2).linearGood n) :=
    hg.to_uniformLocalJets
  apply PeriodizedWaveBounds.uniformClass_of_local_germs
    (fun l n x _ => mul_nonneg (Real.sqrt_nonneg _) (fullEnvelope_nonneg l n x)) hj
  intro l n x hx
  rcases actual_input_cover l n hx with ⟨k, hk⟩ | ⟨ha, hp⟩
  · exact Or.inl ⟨k, hk, Filter.EventuallyEq.rfl⟩
  · have hz := ((actualFamily (B := B) (N0 := N0)).outputs_zero_germs fullStrip (directions B)
      (i := (l, 0)) ha hp).2.2
    rw [actualFamily_good_eq] at hz
    exact Or.inr hz

theorem exact_block_uniform :
    (∀ i m, LabelSumBounds.UniformWaveClass strip (meanEnvelope (B := B) (N0 := N0)) (1 / 2)
      (fun l n x => ((ActualPrimary.piece region l.1 l.2).harmonicBlock (phase l) (angularFrequency
        l)).velocity n i m x)) ∧
    (∀ m, LabelSumBounds.UniformWaveClass strip (meanEnvelope (B := B) (N0 := N0)) 1
      (fun l n x => ((ActualPrimary.piece region l.1 l.2).harmonicBlock (phase l) (angularFrequency
        l)).pressure n m x)) :=
  UniformBlockBounds.blockOfCoefficients_product_uniform
    (fun l : SignedLabel B N0 => (ActualPrimary.piece region l.1 l.2).exactCoefficients)
    angularFrequency chart_exact_amplitude_uniform chart_exact_pressure_uniform

theorem difference_block_uniform :
    ∀ i m, LabelSumBounds.UniformWaveClass strip (meanEnvelope (B := B) (N0 := N0))
      (1 - ChartScales.kappa)
      (fun l n x => ((ActualPrimary.piece region l.1 l.2).differenceBlock (phase l)
        (angularFrequency l)).velocity n i m x) := by
  have hp : LabelSumBounds.UniformWaveClass fullStrip (fullEnvelope (B := B) (N0 := N0))
      (1 - ChartScales.kappa) (fun _ _ _ => (0 : ℂ)) :=
    LabelSumBounds.UniformClass.zero (fun l n x _ =>
      mul_nonneg (Real.sqrt_nonneg _) (fullEnvelope_nonneg l n x))
  exact (UniformBlockBounds.blockOfCoefficients_product_uniform
    (s := strip) (P := meanEnvelope (B := B) (N0 := N0))
    (α := 1 - ChartScales.kappa) (γ := 1 - ChartScales.kappa)
    (fun l : SignedLabel B N0 => (ActualPrimary.piece region l.1 l.2).differenceCoefficients)
    angularFrequency chart_difference_uniform hp).1

end UniformActualOutputs

end NavierStokes.ActualPrimaryBounds
