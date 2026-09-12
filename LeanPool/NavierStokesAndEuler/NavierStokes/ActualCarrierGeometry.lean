/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialExcluded

/-!
# Geometry of the actual broad primary carrier

The Gaussian source carrier keeps the native slow mask and source rectangle,
but does not keep a separate dyadic mask.  A single geometric threshold,
chosen before the actual primary family, controls this larger carrier.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualCarrierGeometry

open Set Function Filter
open CorrectionInitialization ActualPrimary
open scoped Topology

/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point
/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow

/-- This threshold depends only on the fixed nominal profile and its actual
positive reference cells.  In particular, it is independent of the Borel
order, the chosen primary label, and the correction stage. -/
noncomputable def geometricThreshold : ℕ :=
  (PositiveRepresentatives.exists_positive_reference_charts
    outgoing.data.h_pos outgoing.data.h_lt_half
    (NominalConeAssembly.activeLeft_pos nominal)
    (PrimaryGeometryAssembly.active_order (W := nominal)).le).choose

/-- The final construction can enlarge its requested starting band once,
before selecting `ActualPrimary.choice`. -/
noncomputable def startingThreshold (requested : ℕ) : ℕ := max requested geometricThreshold

theorem requested_le_startingThreshold (requested : ℕ) : requested ≤ startingThreshold requested :=
  le_max_left _ _

theorem geometricThreshold_le_startingThreshold (requested : ℕ) :
    geometricThreshold ≤ startingThreshold requested := le_max_right _ _

theorem startingThreshold_le_prepared (B requested : ℕ) :
    startingThreshold requested ≤ (choice B (startingThreshold requested)).prepared.N :=
  ActualPrimary.threshold B (startingThreshold requested)

section Cells

variable {B N0 : ℕ}

theorem threshold_le_band (hN : geometricThreshold ≤ N0) (L : Label B N0) :
    geometricThreshold ≤ BaseChartJets.cellBand L :=
  hN.trans ((ActualPrimary.threshold B N0).trans L.property)

/-- The original positive-cell theorem applies to the same selected label;
no new representative or prepared family is chosen. -/
theorem cell_geometry (hN : geometricThreshold ≤ N0) (L : Label B N0)
    {p : Slow}
    (hp : p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L) :
    0 < p.1 ∧ Real.sqrt (NominalConeAssembly.activeLeft nominal) / 2 ≤ p.1 ∧
      ‖p‖ ≤ PositiveRepresentatives.cellBound (NominalConeAssembly.activeRight nominal) ∧
      0 < p.2.2 ∧ SimilarityHomogeneity.chartQ h p ∈ Ioo (1 / 4 : ℝ) 4 ∧
      SimilarityHomogeneity.chartX h p ∈
        Ioo (NominalConeAssembly.activeLeft nominal / 2)
          (2 * NominalConeAssembly.activeRight nominal) := by
  have ht := (PositiveRepresentatives.exists_positive_reference_charts
    outgoing.data.h_pos outgoing.data.h_lt_half
    (NominalConeAssembly.activeLeft_pos nominal)
    (PrimaryGeometryAssembly.active_order (W := nominal)).le).choose_spec
  exact (ht L.val (threshold_le_band hN L)).2.2.2.2 p
    (PrimaryGeometryAssembly.carrier_in_baseDomain nominal L hp)

theorem sourceCell_subset_clock (L : Label B N0) :
    ActualGaussianCoverage.sourceCell slots.radius
        (ChartScales.slotLength slots.radius h (BaseChartJets.cellBand L)) 1 ⊆
      (clockWindow L).core := by
  intro z hz
  have ht := ActualGaussianCoverage.sourceCell_time
    ((phases B N0 0).L_pos L) (by norm_num : (0 : ℝ) < 1) hz
  change z.1 ∈ Icc (-slots.radius) slots.radius ∧
    z.2 ∈ Icc 0 ((phases B N0 0).L L)
  exact ⟨hz.1, ht.1.le, by simpa only [div_one] using ht.2.le⟩

theorem labelCarrier_slow_core (l : ActualPrimaryBounds.SignedLabel B N0) (n : ℕ)
    {x : Point} (hx : x ∈ ActualInitialExcluded.labelCarrier l n) :
    ActualPrimaryCovariance.nativePoint n x l.2 ∈
      ActualGaussianCoverage.actualSlowCore certificate modulation (choice B N0).prepared l.2 := by
  obtain ⟨k, hk⟩ := hx
  exact hk.1

theorem labelCarrier_in_cell (l : ActualPrimaryBounds.SignedLabel B N0) (n : ℕ)
    {x : Point} (hT : 0 < x.2.1.1) (hx : x ∈ ActualInitialExcluded.labelCarrier l n) :
    ActualPrimaryCovariance.nativePoint n x l.2 ∈
      (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier l.2 :=
  ActualGaussianCoverage.actualSlowCore_inside certificate modulation (choice B N0).prepared l.2
    (labelCarrier_slow_core l n hx) (ActualPrimaryCovariance.nativePoint_time n hT l.2)

theorem labelCarrier_q (hN : geometricThreshold ≤ N0)
    (l : ActualPrimaryBounds.SignedLabel B N0) (n : ℕ)
    {x : Point} (hT : 0 < x.2.1.1) (hx : x ∈ ActualInitialExcluded.labelCarrier l n) :
    SimilarityHomogeneity.chartQ h (ActualPrimaryCovariance.nativePoint n x l.2) ∈
      Ioo (1 / 4 : ℝ) 4 :=
  (cell_geometry hN l.2 (labelCarrier_in_cell l n hT hx)).2.2.2.2.1

end Cells

section BandComparison

theorem logCoordinate_in_broad_band {q : ℝ} (hq : 0 < q) {n : ℕ}
    (hlo : ChartScales.Q n / 4 < q) (hhi : q < 4 * ChartScales.Q n) :
    SquaredPartition.logCoordinate q ∈ Ioo ((n : ℝ) - 2) ((n : ℝ) + 2) := by
  have hQ := ChartScales.Q_pos n
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogQ : Real.log (ChartScales.Q n) = -(n : ℝ) * Real.log 2 := by
    rw [← SquaredPartition.integerQ_nat, SquaredPartition.log_integerQ]
    simp only [Int.cast_natCast]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl := Real.log_lt_log (div_pos hQ (by norm_num : (0 : ℝ) < 4)) hlo
  have hu := Real.log_lt_log hq hhi
  rw [Real.log_div hQ.ne' (by norm_num : (4 : ℝ) ≠ 0), hlogQ, hlog4] at hl
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hQ.ne', hlogQ, hlog4] at hu
  change (n : ℝ) - 2 < -Real.log q / Real.log 2 ∧
    -Real.log q / Real.log 2 < (n : ℝ) + 2
  constructor
  · apply (lt_div_iff₀ h2).mpr
    nlinarith
  · apply (div_lt_iff₀ h2).mpr
    nlinarith

variable {B N0 : ℕ}

theorem labelCarrier_log_band (hN : geometricThreshold ≤ N0)
    (l : ActualPrimaryBounds.SignedLabel B N0) (n : ℕ) {x : Point}
    (hT : 0 < x.2.1.1) (hx : x ∈ ActualInitialExcluded.labelCarrier l n) :
    SquaredPartition.logCoordinate (physicalScale n x) ∈
      Ioo ((BaseChartJets.cellBand l.2 : ℝ) - 2)
        ((BaseChartJets.cellBand l.2 : ℝ) + 2) := by
  have hq := labelCarrier_q hN l n hT hx
  have he := ActualPrimaryCovariance.nativePoint_scale n hT l.2
  change ChartScales.Q (BaseChartJets.cellBand l.2) *
    SimilarityHomogeneity.chartQ h (ActualPrimaryCovariance.nativePoint n x l.2) =
      physicalScale n x at he
  have hlo : ChartScales.Q (BaseChartJets.cellBand l.2) / 4 < physicalScale n x := by
    rw [← he]
    nlinarith [ChartScales.Q_pos (BaseChartJets.cellBand l.2), hq.1]
  have hhi : physicalScale n x < 4 * ChartScales.Q (BaseChartJets.cellBand l.2) := by
    rw [← he]
    nlinarith [ChartScales.Q_pos (BaseChartJets.cellBand l.2), hq.2]
  exact logCoordinate_in_broad_band
    ((div_pos (ChartScales.Q_pos _) (by norm_num : (0 : ℝ) < 4)).trans hlo) hlo hhi

theorem strip_log_band (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) :
    SquaredPartition.logCoordinate (physicalScale n x) ∈ Icc ((n : ℝ) - 1) ((n : ℝ) + 1) := by
  have hq := ((BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mp hx).1.2
  change SimilarityCoordinates.coordinateQ (2 * h) x.2.1 ∈ Ioo (1 / 2 : ℝ) 2 at hq
  apply PhysicalWaveSum.logCoordinate_in_band
  · change 0 < ChartScales.Q n * _
    exact mul_pos (ChartScales.Q_pos n) (lt_trans (by norm_num) hq.1)
  · change ChartScales.Q n / 2 ≤ ChartScales.Q n * _
    nlinarith [ChartScales.Q_pos n, hq.1]
  · change ChartScales.Q n * _ ≤ 2 * ChartScales.Q n
    nlinarith [ChartScales.Q_pos n, hq.2]

/-- The strict broad-cell range saves one integer level: the true band
distance is at most two, despite the absence of the dyadic mask. -/
theorem labelCarrier_band_distance (hN : geometricThreshold ≤ N0)
    (l : ActualPrimaryBounds.SignedLabel B N0) (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
    (hc : x ∈ ActualInitialExcluded.labelCarrier l n) :
    n ≤ BaseChartJets.cellBand l.2 + 2 ∧ BaseChartJets.cellBand l.2 ≤ n + 2 := by
  have ht := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  have hn := strip_log_band n hx
  have hm := labelCarrier_log_band hN l n ht hc
  have hnm : n < BaseChartJets.cellBand l.2 + 3 := by
    have he : (n : ℝ) < (BaseChartJets.cellBand l.2 : ℝ) + 3 := by linarith [hn.1, hm.2]
    exact_mod_cast he
  have hmn : BaseChartJets.cellBand l.2 < n + 3 := by
    have he : (BaseChartJets.cellBand l.2 : ℝ) < (n : ℝ) + 3 := by linarith [hm.1, hn.2]
    exact_mod_cast he
  omega

theorem labelCarrier_near (hN : geometricThreshold ≤ N0)
    (l : ActualPrimaryBounds.SignedLabel B N0) (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
    (hc : x ∈ ActualInitialExcluded.labelCarrier l n) : ActualPrimaryBounds.near l n := by
  obtain ⟨hnm, hmn⟩ := labelCarrier_band_distance hN l n hx hc
  have hm4 : 4 ≤ BaseChartJets.cellBand l.2 := ActualPrimaryBounds.label_large l
  refine ⟨by omega, ?_⟩
  unfold CommonWindow.levels
  refine Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ?_)
  exact ⟨max_le (by omega) (by omega), hmn⟩

theorem labelCarrier_phaseCell (hN : geometricThreshold ≤ N0)
    (l : ActualPrimaryBounds.SignedLabel B N0) (n : ℕ) {x : FullPoint}
    (hx : x ∈ ActualPrimaryBounds.fullStrip.domain)
    (hc : x.1 ∈ ActualInitialExcluded.labelCarrier l n) :
    ∃ k : TorusInverse.Frequency,
      ActualPrimaryBounds.near l n ∧
      (ActualPrimaryBounds.fullCopy l n k x).1 ∈
        (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier l.2 ∧
      (ActualPrimaryBounds.fullCopy l n k x).2 ∈ (clockWindow l.2).core := by
  change x.1 ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain at hx
  have hn := labelCarrier_near hN l n hx hc
  obtain ⟨k, hk⟩ := hc
  have he := chart_nativePoint l.1 l.2 n (CommonWindow.index_le hn.2) k x.1
  change (_, _) = ActualPrimaryBounds.fullCopy l n k x at he
  refine ⟨k, hn, ?_, ?_⟩
  · rw [← he]
    exact ActualGaussianCoverage.actualSlowCore_inside certificate modulation (choice B
        N0).prepared l.2
      hk.1 (ActualPrimaryCovariance.nativePoint_time n
        (BaseContextAssembly.nativeStrip_time nominal standardRegion hx) l.2)
  · rw [← he]
    exact sourceCell_subset_clock l.2 hk.2

end BandComparison

section Windows

variable {B N0 : ℕ}

theorem position_component (L : Label B N0) (p : Slow) (j : Fin 3) :
    position L p j =
      ChartScales.Q (BaseChartJets.cellBand L) ^ SlotColoring.axisExponent (CoordinateAlgebra.D h)
          j *
        PrimaryRepresentatives.position p j := by
  fin_cases j <;>
    simp [position, PrimaryRepresentatives.position, SlotColoring.axisExponent, Real.sqrt_eq_rpow]

theorem width_eq (D : ℝ) (j : Fin 3) (n : ℕ) :
    SlotColoring.width D j n =
      ChartScales.Q n ^ SlotColoring.axisExponent D j * SquaredPartition.nativeSpacing n := by
  unfold SlotColoring.width
  rw [SlotColoring.spacing_eq_scaled_mesh]
  simp only [ChartScales.Q, SquaredPartition.nativeSpacing, ChartScales.S, one_div]

theorem nativeSlowCore_physicalBox (l : ActualPrimaryBounds.SignedLabel B N0)
    {p : Slow}
    (hp : p ∈ ActualGaussianCoverage.actualSlowCore certificate modulation
      (choice B N0).prepared l.2) :
    position l.2 p ∈ SlotColoring.physicalBox (CoordinateAlgebra.D h)
      (ActualPrimaryCovariance.signedLabelOf (l.2, l.1)) := by
  have hb := PrimaryRepresentatives.nativeMask_tsupport_subset l.2.val.property.1
    (PrimaryGeometryAssembly.label nominal l.2).2 hp
  intro j
  have ha : 0 < ChartScales.Q (BaseChartJets.cellBand l.2) ^
      SlotColoring.axisExponent (CoordinateAlgebra.D h) j :=
    Real.rpow_pos_of_pos (ChartScales.Q_pos _) _
  have hw := SlotColoring.width_pos (CoordinateAlgebra.D h) j l.2.val.property.1
  change 0 < SlotColoring.width (CoordinateAlgebra.D h) j (BaseChartJets.cellBand l.2) at hw
  change |position l.2 p j - SlotColoring.width (CoordinateAlgebra.D h) j
      (BaseChartJets.cellBand l.2) * ((PrimaryGeometryAssembly.label nominal l.2).2 j : ℝ)| ≤
    2 * SlotColoring.width (CoordinateAlgebra.D h) j (BaseChartJets.cellBand l.2)
  calc
    _ = (ChartScales.Q (BaseChartJets.cellBand l.2) ^
        SlotColoring.axisExponent (CoordinateAlgebra.D h) j) *
        |PrimaryRepresentatives.position p j - SquaredPartition.nativeSpacing
            (BaseChartJets.cellBand l.2) *
          ((PrimaryGeometryAssembly.label nominal l.2).2 j : ℝ)| := by
      rw [position_component, width_eq, mul_assoc, ← mul_sub, abs_mul, abs_of_pos ha]
    _ ≤ (ChartScales.Q (BaseChartJets.cellBand l.2) ^
        SlotColoring.axisExponent (CoordinateAlgebra.D h) j) *
        SquaredPartition.nativeSpacing (BaseChartJets.cellBand l.2) :=
      mul_le_mul_of_nonneg_left (by have hh := hb j; simp only [one_mul] at hh; exact hh) ha.le
    _ = SlotColoring.width (CoordinateAlgebra.D h) j (BaseChartJets.cellBand l.2) :=
      (width_eq _ _ _).symm
    _ ≤ _ := by linarith

/-- The broad source carrier fits the existing closed two-level,
two-mesh window.  Its missing dyadic factor is not restored or assumed. -/
theorem labelCarrier_window (hN : geometricThreshold ≤ N0)
    (l : ActualPrimaryBounds.SignedLabel B N0) (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
    (hc : x ∈ ActualInitialExcluded.labelCarrier l n) :
    ActualPrimaryCovariance.physicalWindow n x ∈
      LabelSumBounds.closedWindow (CoordinateAlgebra.D h)
        (ActualPrimaryCovariance.signedLabelOf (l.2, l.1)) := by
  have hb := labelCarrier_log_band hN l n
    (BaseContextAssembly.nativeStrip_time nominal standardRegion hx) hc
  refine ⟨⟨hb.1.le, hb.2.le⟩, ?_⟩
  change physicalPosition n x ∈ _
  rw [← ActualPrimaryCovariance.nativePoint_position n x l.2]
  exact nativeSlowCore_physicalBox l (labelCarrier_slow_core l n hc)

theorem signedLabel_injective : Function.Injective
    (fun l : ActualPrimaryBounds.SignedLabel B N0 =>
      ActualPrimaryCovariance.signedLabelOf (l.2, l.1)) := by
  intro l m he
  have he' := ActualPrimaryCovariance.signedLabelOf_injective he
  exact Prod.ext (congrArg Prod.snd he') (congrArg Prod.fst he')

theorem labelCarrier_window_card (hN : geometricThreshold ≤ N0)
    (n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
    (s : Finset (ActualPrimaryBounds.SignedLabel B N0))
    (hs : ∀ l ∈ s, x ∈ ActualInitialExcluded.labelCarrier l n) : s.card ≤ 2250 := by
  apply LabelSumBounds.window_card_le s
    (fun l => ActualPrimaryCovariance.signedLabelOf (l.2, l.1)) signedLabel_injective.injOn
  · intro l hl
    exact ⟨l.2.val.property.1, labelCarrier_window hN l n hx (hs l hl)⟩

end Windows

section Separation

theorem geometry_liftedSupport (g : CommonCoverSolve.Geometry)
    {C S : Set TorusInverse.Plane}
    (hCS : (fun z => g.center + g.basis z) '' C ⊆ S)
    (k : TorusInverse.Frequency) {Y : TorusInverse.Plane}
    (hY : g.coordinates k Y ∈ C) : Y ∈ SlotGeometry.liftedSupport g.gap S := by
  refine ⟨g.center + g.basis (g.coordinates k Y), hCS ⟨_, hY, rfl⟩, ?_⟩
  have he : CommonCoverSolve.coverPower g.gap Y =
      TorusAverages.latticePoint k + (g.center + g.basis (g.coordinates k Y)) := by
    simp only [CommonCoverSolve.Geometry.coordinates, ContinuousLinearEquiv.apply_symm_apply]
    abel
  rw [← CommonCoverSolve.coverPower_apply, he]
  exact SlotGeometry.torusEq_symm (PartitionedCovariance.torusEq_lattice_add k _)

variable {B N0 : ℕ}

theorem clock_core_in_slot (l : ActualPrimaryBounds.SignedLabel B N0) :
    (fun z => (geometry l.1 l.2).center + (geometry l.1 l.2).basis z) ''
        (clockWindow l.2).core ⊆
      PartitionedCovariance.slotSet h slots.radius radialVector temporalVector
        (ActualPrimaryCovariance.signedLabelOf (l.2, l.1)) := by
  apply Set.Subset.trans (Set.image_mono (clockWindow l.2).core_subset_outer)
  exact ActualSignedGeometry.clock_outer_in_slot slots vectors_det outgoing.data.h_pos.le
    (ActualPrimaryBounds.label_large l) (ChartScales.nativeIndex h (BaseChartJets.cellBand l.2))

/-- The source rectangle lies in the actual selected absolute slot.  This
part is purely geometric and needs neither the threshold nor strip membership. -/
theorem labelCarrier_liftedSupport (l : ActualPrimaryBounds.SignedLabel B N0)
    (n : ℕ) {x : Point} (hx : x ∈ ActualInitialExcluded.labelCarrier l n) :
    ActualPrimaryCovariance.absoluteAuxiliary n x ∈
      SlotGeometry.liftedSupport
        (SlotColoring.nativeIndex h (ActualPrimaryCovariance.signedLabelOf (l.2, l.1)).1)
        (PartitionedCovariance.slotSet h slots.radius radialVector temporalVector
          (ActualPrimaryCovariance.signedLabelOf (l.2, l.1))) := by
  obtain ⟨k, hk⟩ := hx
  exact geometry_liftedSupport (geometry l.1 l.2) (clock_core_in_slot l) k
    (sourceCell_subset_clock l.2 hk.2)

/-- Distinct broad carriers are disjoint on the actual strip.  Separation
comes from the original rational slot system and the proved window bound. -/
theorem labelCarrier_disjoint (hN : geometricThreshold ≤ N0)
    (n : ℕ) {l m : ActualPrimaryBounds.SignedLabel B N0} (hne : l ≠ m) :
    Disjoint
      ((BaseContextAssembly.nativeStrip nominal standardRegion).domain ∩
          ActualInitialExcluded.labelCarrier l n)
      ((BaseContextAssembly.nativeStrip nominal standardRegion).domain ∩
          ActualInitialExcluded.labelCarrier m n) := by
  apply Set.disjoint_left.mpr
  intro x hl hm
  have hadj := LabelSumBounds.closedWindow_adjacency l.2.val.property.1 m.2.val.property.1
    (fun he => hne (signedLabel_injective he))
    (labelCarrier_window hN l n hl.1 hl.2) (labelCarrier_window hN m n hm.1 hm.2)
  exact Set.disjoint_left.mp (slots.disjoint _ _ hadj)
    (labelCarrier_liftedSupport l n hl.2) (labelCarrier_liftedSupport m n hm.2)

end Separation

end NavierStokes.ActualCarrierGeometry
