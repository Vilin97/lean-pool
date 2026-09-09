/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentWaveSupport
public import LeanPool.NavierStokesAndEuler.NavierStokes.LabelSumBounds

@[expose] public section

/-!
# Physical jet bounds for the actual current particular label sum

The closed label windows bound the number of contributing spatial labels.
The two column choices are retained by the signed-label map and are already
included in the 2250-color palette.  The finite harmonic sum remains explicit.
-/

noncomputable section

namespace NavierStokes.CurrentParticularLabelBounds

open Set Function Filter ProblemStatement
open CorrectionState CorrectionStep CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators


abbrev Label (B N0 : ℕ) := ActualCurrentParticularPhysical.Label B N0

variable {B N0 : ℕ}

noncomputable def signedLabel (l : Label B N0) : SlotColoring.Label :=
  ActualPrimaryCovariance.signedLabelOf (l.2, l.1)

theorem signedLabel_injective : Injective (signedLabel (B := B) (N0 := N0)) := by
  intro l k he
  have hk := ActualPrimaryCovariance.signedLabelOf_injective he
  exact Prod.ext (congrArg Prod.snd hk) (congrArg Prod.fst hk)

theorem signedLabel_level (l : Label B N0) : 1 ≤ (signedLabel l).1 :=
  l.2.val.property.1

noncomputable def windowPosition (w : SpaceTime) : SlotColoring.Position :=
  ![AnnularEndpoint.radius w, w.2 2, 1 - w.1]

noncomputable def window (w : SpaceTime) : LabelSumBounds.WindowPoint :=
  (SquaredPartition.logCoordinate (PhysicalWaveSum.physicalQ h w), windowPosition w)

theorem windowPosition_continuous : Continuous windowPosition := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact AnnularEndpoint.radius_continuous
  · exact (EuclideanSpace.proj 2).continuous.comp continuous_snd
  · exact continuous_const.sub continuous_fst

theorem window_continuousAt {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal) :
    ContinuousAt window w := by
  have hq := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half ht
  have hc := (PhysicalWaveSum.physicalQ_smoothAt outgoing.data.h_pos
    outgoing.data.h_lt_half ht).continuousAt
  exact (((Real.continuousAt_log hq.ne').comp hc).neg.div_const _).prodMk
    windowPosition_continuous.continuousAt

noncomputable def chartPoint (n : ℕ) (w : SpaceTime) : LocalSignedRequest.Point :=
  ActualCarrierTransport.associatedPoint
    (ActualCurrentParticularPhysical.nativePoint n w).1.1
    (ActualCurrentParticularPhysical.nativePoint n w).2

theorem chartPoint_time_pos (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) : 0 < (chartPoint n w).2.1.1 :=
  (ActualCurrentWaveSupport.nativePoint_parameterDomain n hw).1

theorem chartPoint_scale (n : ℕ) {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal) :
    physicalScale n (chartPoint n w) = PhysicalWaveSum.physicalQ h w := by
  change ChartScales.Q n * SimilarityCoordinates.coordinateQ (2 * h)
    (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 = _
  rw [ActualCurrentWaveSupport.nativePoint_coordinateQ n ht]
  field_simp [(ChartScales.Q_pos n).ne']

theorem chartPoint_position (n : ℕ) (w : SpaceTime) :
    physicalPosition n (chartPoint n w) = windowPosition w := by
  have hs := ActualCurrentWaveSupport.nativePoint_slow n w
  have hr := ActualCurrentWaveSupport.nativePoint_radius n w
  have hQ := (ChartScales.Q_pos n).ne'
  have hp (a : ℝ) : ChartScales.Q n ^ a * ChartScales.Q n ^ (-a) = 1 := by
    rw [← Real.rpow_add (ChartScales.Q_pos n)]
    simp
  funext i
  fin_cases i
  · change Real.sqrt (ChartScales.Q n) *
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.1 = AnnularEndpoint.radius w
    rw [hr, Real.sqrt_eq_rpow, ← mul_assoc, hp, one_mul]
  · change ChartScales.Q n ^ CoordinateAlgebra.D h *
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.2.2 = w.2 2
    rw [hs, ← mul_assoc, hp, one_mul]
  · change ChartScales.Q n *
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.2.1 = 1 - w.1
    rw [hs, mul_div_cancel₀ _ hQ]

/-- The genuine one-mesh native support is contained in the two-mesh
physical box. The column sign does not change the physical box. -/
theorem nativeMask_physicalBox (L : CorrectionInitialization.ActualPrimary.Label B N0)
    (j : Fin 2) {p : PhaseCalculus.Slow}
    (hp : p ∈ tsupport (PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand L)
      (PrimaryGeometryAssembly.label nominal L).2)) :
    position L p ∈ SlotColoring.physicalBox (CoordinateAlgebra.D h) (signedLabel (j, L)) := by
  have hb := PrimaryRepresentatives.nativeMask_tsupport_subset L.val.property.1
    (PrimaryGeometryAssembly.label nominal L).2 hp
  intro i
  have hscale : 0 < ChartScales.Q (BaseChartJets.cellBand L) ^
      SlotColoring.axisExponent (CoordinateAlgebra.D h) i :=
    Real.rpow_pos_of_pos (ChartScales.Q_pos _) _
  have hspacing := SquaredPartition.nativeSpacing_pos L.val.property.1
  have he : position L p i =
      ChartScales.Q (BaseChartJets.cellBand L) ^ SlotColoring.axisExponent (CoordinateAlgebra.D h)
        i *
        PrimaryRepresentatives.position p i := by
    fin_cases i <;> simp [position, PrimaryRepresentatives.position,
      SlotColoring.axisExponent, Real.sqrt_eq_rpow]
  change |position L p i - SlotColoring.width (CoordinateAlgebra.D h) i
      (BaseChartJets.cellBand L) * (((PrimaryGeometryAssembly.label nominal L).2 i : ℤ) : ℝ)| ≤
    2 * SlotColoring.width (CoordinateAlgebra.D h) i (BaseChartJets.cellBand L)
  rw [he]
  simp only [PrimaryRepresentatives.width_eq_scaled_spacing]
  rw [show ChartScales.Q (BaseChartJets.cellBand L) ^ SlotColoring.axisExponent
    (CoordinateAlgebra.D h) i *
      PrimaryRepresentatives.position p i -
      (ChartScales.Q (BaseChartJets.cellBand L) ^ SlotColoring.axisExponent (CoordinateAlgebra.D h)
        i *
        SquaredPartition.nativeSpacing (BaseChartJets.cellBand L)) *
          (((PrimaryGeometryAssembly.label nominal L).2 i : ℤ) : ℝ) =
      ChartScales.Q (BaseChartJets.cellBand L) ^ SlotColoring.axisExponent (CoordinateAlgebra.D h)
        i *
        (PrimaryRepresentatives.position p i - SquaredPartition.nativeSpacing
          (BaseChartJets.cellBand L) *
          (((PrimaryGeometryAssembly.label nominal L).2 i : ℤ) : ℝ)) by ring]
  rw [abs_mul, abs_of_pos hscale]
  have hi := mul_le_mul_of_nonneg_left (hb i) hscale.le
  rw [one_mul] at hi
  refine hi.trans ?_
  have hn := mul_nonneg hscale.le hspacing.le
  have he := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) hn
  simp only [one_mul] at he
  exact he

/-- Full refined support, including the native dyadic factor and the slow
mask, puts a physical point in its actual signed label's closed window. -/
theorem refinedCarrier_window (l : Label B N0) (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n)
    (hs : chartPoint n w ∈ ActualCoreSupport.refinedCarrier (l.2, l.1) n) :
    window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) := by
  have hT := chartPoint_time_pos n hw
  obtain ⟨hb, _, hq⟩ := (ActualCoreSupport.mem_refinedCarrier_iff (l.2, l.1) n hT).mp hs
  obtain ⟨k, hk⟩ := hb
  have hslow : ActualPrimaryCovariance.nativePoint n (chartPoint n w) l.2 ∈
      tsupport (PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand l.2)
        (PrimaryGeometryAssembly.label nominal l.2).2) := hk.1
  have hbox := nativeMask_physicalBox l.2 l.1 hslow
  rw [ActualPrimaryCovariance.nativePoint_position, chartPoint_position] at hbox
  have he := ActualPrimaryCovariance.nativePoint_scale n hT l.2
  change ChartScales.Q (BaseChartJets.cellBand l.2) *
    ActualCoreSupport.nativeQ (l.2, l.1) n (chartPoint n w) =
      physicalScale n (chartPoint n w) at he
  rw [chartPoint_scale n hw.1] at he
  have hleft : ChartScales.Q (BaseChartJets.cellBand l.2) / 2 ≤ PhysicalWaveSum.physicalQ h w := by
    have hb := mul_le_mul_of_nonneg_left hq.1 (ChartScales.Q_pos (BaseChartJets.cellBand l.2)).le
    nlinarith
  have hright : PhysicalWaveSum.physicalQ h w ≤ 2 * ChartScales.Q (BaseChartJets.cellBand l.2) := by
    have hb := mul_le_mul_of_nonneg_left hq.2 (ChartScales.Q_pos (BaseChartJets.cellBand l.2)).le
    nlinarith
  have hlog := PhysicalWaveSum.logCoordinate_in_band
    (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1) hleft hright
  refine ⟨?_, hbox⟩
  change SquaredPartition.logCoordinate (PhysicalWaveSum.physicalQ h w) ∈
    Icc ((BaseChartJets.cellBand l.2 : ℝ) - 2) ((BaseChartJets.cellBand l.2 : ℝ) + 2)
  constructor <;> linarith [hlog.1, hlog.2]

theorem current_modes_window
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CycleState (Label B N0)) (l : Label B N0)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (j : ℤ) (n : ℕ) {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n) :
    (ActualCurrentParticularPhysical.localPotentialMode x l j n w ≠ 0 →
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l)) ∧
    (ActualCurrentParticularPhysical.localPressureMode x l j n w ≠ 0 →
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l)) := by
  have hm := ActualCurrentWaveSupport.current_modes_support hN x l hs j n hw
  exact ⟨fun hv => refinedCarrier_window l n hw (hm.1 hv),
    fun hv => refinedCarrier_window l n hw (hm.2 hv)⟩

/-! ## Finite harmonic sums with uniform spatial multiplicity -/

section Summation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The spatial factor is 2250, independently of the number of labels.
Different harmonics may retain different constants. All jet hypotheses
are pointwise at `w`; the open band is used only for support and germs. -/
theorem finite_modes_jet_bound (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n)
    (F : Finset (Label B N0)) (J : Finset ℤ) (f : Label B N0 → ℤ → SpaceTime → E)
    (m : ℕ)
    (hf : ∀ l ∈ F, ∀ j ∈ J, ContDiffAt ℝ m (f l j) w)
    (hs : ∀ l ∈ F, ∀ j ∈ J, ∀ y ∈ ValidDyadicBandCover.band h n, f l j y ≠ 0 →
      window y ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l))
    (C : ℤ → ℝ) (hC : ∀ j ∈ J, 0 ≤ C j)
    (hb : ∀ l ∈ F, ∀ j ∈ J,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (f l j) w‖ ≤ C j) :
    ‖iteratedFDeriv ℝ m (fun y => ∑ l ∈ F, ∑ j ∈ J, f l j y) w‖ ≤
      2250 * ∑ j ∈ J, C j := by
  classical
  have hj (j : ℤ) (hj : j ∈ J) :
      ‖iteratedFDeriv ℝ m (fun y => ∑ l ∈ F, f l j y) w‖ ≤ 2250 * C j :=
    LabelSumBounds.finite_sum_jet_bound
      (ValidDyadicBandCover.band_open outgoing.data.h_pos outgoing.data.h_lt_half n) hw
      F signedLabel signedLabel_injective.injOn (fun l _ => signedLabel_level l)
      (CoordinateAlgebra.D h) window (window_continuousAt hw.1) (fun l => f l j) m
      (fun l hl => hf l hl j hj) (fun l hl => hs l hl j hj) (hC j hj)
      (fun l hl => hb l hl j hj)
  have hsm (j : ℤ) (hj : j ∈ J) : ContDiffAt ℝ m (fun y => ∑ l ∈ F, f l j y) w :=
    ContDiffAt.sum (fun l hl => hf l hl j hj)
  have he : (fun y => ∑ l ∈ F, ∑ j ∈ J, f l j y) =
      (fun y => ∑ j ∈ J, ∑ l ∈ F, f l j y) := by
    funext y
    exact Finset.sum_comm
  rw [he, PhysicalWaveSum.iteratedFDeriv_finset_sum_at J hsm]
  calc
    _ ≤ ∑ j ∈ J, ‖iteratedFDeriv ℝ m (fun y => ∑ l ∈ F, f l j y) w‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, 2250 * C j := Finset.sum_le_sum hj
    _ = 2250 * ∑ j ∈ J, C j := by rw [Finset.mul_sum]

end Summation

theorem modes_card (N : ℕ) : (ParticularWaveAssembly.modes N).card = 2 * N := by
  classical
  unfold ParticularWaveAssembly.modes
  rw [Finset.card_erase_of_mem (by simp), Int.card_Icc]
  omega

section ActualSums

variable (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CycleState (Label B N0))
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (n m : ℕ) {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n)

include hN hs hw

theorem localPotential_jet_bound (C : ℤ → ℝ)
    (hC : ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, 0 ≤ C j)
    (hf : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      ContDiffAt ℝ m (ActualCurrentParticularPhysical.localPotentialMode x l j n) w)
    (hb : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode x l j n) w‖ ≤ C j) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotential x n) w‖ ≤
      2250 * ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, C j :=
  finite_modes_jet_bound n hw (x.coefficients.labels n)
    (ParticularWaveAssembly.modes x.coefficients.residualBand)
    (fun l j => ActualCurrentParticularPhysical.localPotentialMode x l j n) m hf
    (fun l _ j _ _y hy => (current_modes_window hN x l (hs l) j n hy).1) C hC hb

theorem localPressure_jet_bound (C : ℤ → ℝ)
    (hC : ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, 0 ≤ C j)
    (hf : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      ContDiffAt ℝ m (ActualCurrentParticularPhysical.localPressureMode x l j n) w)
    (hb : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode x l j n) w‖ ≤ C j) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressure x n) w‖ ≤
      2250 * ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, C j :=
  finite_modes_jet_bound n hw (x.coefficients.labels n)
    (ParticularWaveAssembly.modes x.coefficients.residualBand)
    (fun l j => ActualCurrentParticularPhysical.localPressureMode x l j n) m hf
    (fun l _ j _ _y hy => (current_modes_window hN x l (hs l) j n hy).2) C hC hb

theorem localPotential_jet_bound_uniform {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      ContDiffAt ℝ m (ActualCurrentParticularPhysical.localPotentialMode x l j n) w)
    (hb : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode x l j n) w‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotential x n) w‖ ≤
      2250 * (2 * x.coefficients.residualBand : ℕ) * C := by
  have hh := localPotential_jet_bound hN x hs n m hw (fun _ => C) (fun _ _ => hC) hf hb
  simpa only [Finset.sum_const, nsmul_eq_mul, modes_card, mul_assoc] using hh

theorem localPressure_jet_bound_uniform {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      ContDiffAt ℝ m (ActualCurrentParticularPhysical.localPressureMode x l j n) w)
    (hb : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode x l j n) w‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressure x n) w‖ ≤
      2250 * (2 * x.coefficients.residualBand : ℕ) * C := by
  have hh := localPressure_jet_bound hN x hs n m hw (fun _ => C) (fun _ _ => hC) hf hb
  simpa only [Finset.sum_const, nsmul_eq_mul, modes_card, mul_assoc] using hh

end ActualSums

/-! ## The incoming actual invariant supplies all mode regularity -/

section Invariant

variable {σ : ℝ} {x : CycleState (ActualInitialization.Index B N0)}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)

include H hN

/-- Per-mode physical smoothness on the whole open valid band, including
the axis. The invariant supplies source regularity and the actual raw
boundary values; at the axis the retained support gives a zero germ. -/
theorem current_modes_contDiffAt (l : Label B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ)
    {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n) :
    ContDiffAt ℝ ∞ (ActualCurrentParticularPhysical.localPotentialMode
      (ActualCycleParameters.particularState x) l j n) w ∧
    ContDiffAt ℝ ∞ (ActualCurrentParticularPhysical.localPressureMode
      (ActualCycleParameters.particularState x) l j n) w := by
  by_cases ha : PhysicalGraphBounds.radialProjection w = 0
  · have hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
        (ActualCoreSupport.refinedCarrier (l.2, l.1))
        ((ActualCycleParameters.particularState x).coefficients.blocks l)
        ((ActualCycleParameters.particularState x).coefficients.gaussian l)
        ((ActualCycleParameters.particularState x).coefficients.aliasCoefficients l) :=
      H.inputSupport (l.2, l.1)
    have hh := ActualCurrentWaveSupport.current_mode_annulus hN
      (ActualCycleParameters.particularState x) l hs j 0
    exact ⟨contDiffAt_const.congr_of_eventuallyEq
      (hh.1.axis_zero_germ outgoing.data.h_pos outgoing.data.h_lt_half
        (PrimaryTargetBounds.leftRadius_pos nominal) (Nat.zero_le n) hw ha),
      contDiffAt_const.congr_of_eventuallyEq
      (hh.2.axis_zero_germ outgoing.data.h_pos outgoing.data.h_lt_half
        (PrimaryTargetBounds.leftRadius_pos nominal) (Nat.zero_le n) hw ha)⟩
  · have hpos : 0 < ‖PhysicalGraphBounds.radialProjection w‖ := norm_pos_iff.mpr ha
    have hc := ActualCurrentParticularPhysical.chosenChart_valid ha
    have hm : ActualCurrentParticularPhysical.nativePoint n w ∈
        ActualCurrentParticularPhysical.nativeDomain :=
      ⟨ActualCurrentWaveSupport.nativePoint_parameterDomain n hw, mem_univ _⟩
    exact ActualCurrentParticularPhysical.localModes_contDiffAt_of_invariant H hN
      (l.2, l.1) j hj n hpos
      (PhysicalWaveSum.chooseChart ‖PhysicalGraphBounds.radialProjection w‖
        (PhysicalGraphBounds.radialProjection w)) hc hm

theorem current_modes_contDiffOn (l : Label B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    ContDiffOn ℝ ∞ (ActualCurrentParticularPhysical.localPotentialMode
      (ActualCycleParameters.particularState x) l j n) (ValidDyadicBandCover.band h n) ∧
    ContDiffOn ℝ ∞ (ActualCurrentParticularPhysical.localPressureMode
      (ActualCycleParameters.particularState x) l j n) (ValidDyadicBandCover.band h n) := by
  constructor
  · intro w hw
    exact (current_modes_contDiffAt H hN l j hj n hw).1.contDiffWithinAt
  · intro w hw
    exact (current_modes_contDiffAt H hN l j hj n hw).2.contDiffWithinAt

omit H hN in
private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

theorem localPotential_jet_bound_of_invariant (n m : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) (C : ℤ → ℝ)
    (hC : ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, 0 ≤ C j)
    (hb : ∀ l ∈ (ActualCycleParameters.particularState x).coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤ C j) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotential
      (ActualCycleParameters.particularState x) n) w‖ ≤
      2250 * ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, C j :=
  localPotential_jet_bound hN (ActualCycleParameters.particularState x)
    (fun l => H.inputSupport (l.2, l.1)) n m hw C hC
    (fun l _ j hj => (current_modes_contDiffAt H hN l j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 n hw).1.of_le (nat_le_infty m)) hb

theorem localPressure_jet_bound_of_invariant (n m : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) (C : ℤ → ℝ)
    (hC : ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, 0 ≤ C j)
    (hb : ∀ l ∈ (ActualCycleParameters.particularState x).coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤ C j) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressure
      (ActualCycleParameters.particularState x) n) w‖ ≤
      2250 * ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, C j :=
  localPressure_jet_bound hN (ActualCycleParameters.particularState x)
    (fun l => H.inputSupport (l.2, l.1)) n m hw C hC
    (fun l _ j hj => (current_modes_contDiffAt H hN l j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 n hw).2.of_le (nat_le_infty m)) hb

theorem localPotential_jet_bound_uniform_of_invariant (n m : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ l ∈ (ActualCycleParameters.particularState x).coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotential
      (ActualCycleParameters.particularState x) n) w‖ ≤
      2250 * (2 * x.coefficients.residualBand : ℕ) * C := by
  have hh := localPotential_jet_bound_of_invariant H hN n m hw (fun _ => C) (fun _ _ => hC) hb
  simpa only [Finset.sum_const, nsmul_eq_mul, modes_card, mul_assoc] using hh

theorem localPressure_jet_bound_uniform_of_invariant (n m : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ l ∈ (ActualCycleParameters.particularState x).coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressure
      (ActualCycleParameters.particularState x) n) w‖ ≤
      2250 * (2 * x.coefficients.residualBand : ℕ) * C := by
  have hh := localPressure_jet_bound_of_invariant H hN n m hw (fun _ => C) (fun _ _ => hC) hb
  simpa only [Finset.sum_const, nsmul_eq_mul, modes_card, mul_assoc] using hh

end Invariant

end NavierStokes.CurrentParticularLabelBounds
