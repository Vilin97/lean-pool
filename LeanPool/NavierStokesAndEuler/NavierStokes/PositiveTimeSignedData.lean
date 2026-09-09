/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveTimeCopyFamily
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedExterior
import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveTimeSignedLocalization

/-!
# Signed physical data from positive native time

The native signed sources are used only at positive native time.  Their
totalized formula need not vanish in the past of that domain.  This module
uses an explicit zero extension of the physical copy amplitudes outside
positive native time, while retaining the original masks, sources, and
carrier profiles on their genuine domains.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PositiveTimeSignedData

open Set Function Filter ProblemStatement HarmonicCalculus WeightedClasses
open ActualSignedPhysicalData
open scoped Topology ContDiff BigOperators

attribute [local instance] Classical.propDecidable


/-- The original mask and target localize the native source only where
native time is positive.  The time hypothesis is explicit in both fields. -/
structure PrimitiveLocalization {h : ℝ}
    {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (f : SignedFamily U)
    (a b : ℝ) (s : StripData Native) : Prop where
  normalized : ∀ (L : NativeLabel f.active) (y : Native), y ∈ nativePast → 0 ≤ y.1 →
    (f.primary L).mask L.val.1 (nativeCylinder y) ≠ 0 →
    (f.primary L).target L.val.1 (nativeCylinder y) ≠ 0 →
    1 / 2 ≤ SimilarityCoordinates.coordinateQ (2 * h) y.2.1 ∧
      SimilarityCoordinates.coordinateQ (2 * h) y.2.1 ≤ 2 ∧
      a ≤ y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ∧
      y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ≤ b
  domain : ∀ (L : NativeLabel f.active) (y : Native), y ∈ nativePast → 0 ≤ y.1 →
    (f.primary L).mask L.val.1 (nativeCylinder y) ≠ 0 →
    (f.primary L).target L.val.1 (nativeCylinder y) ≠ 0 → y ∈ s.domain
  mask_pullback : ∀ (L : NativeLabel f.active) (w : SpaceTime),
    w ∈ PhysicalWaveSum.preterminal →
    (f.primary L).mask L.val.1
        (cylinderZero (PhysicalGraphBounds.physicalLift h L.val.1 w)) =
      PhysicalWaveSum.physicalMask (CoordinateAlgebra.D h) L.val
        (PhysicalWaveSum.physicalParams h w)

section Localization

variable {h a b : ℝ} {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
  {f : SignedFamily U} {s : StripData Native}
  (hloc : PrimitiveLocalization (h := h) f a b s)

include hloc

/-- Positive-time primitive localization supplies the actual Cartesian
annulus and slow-coordinate bound. -/
theorem primitive_annulus (hh0 : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hb : 0 < b) (L : NativeLabel f.active) (x : LiftPoint)
    (hx : 0 < x.1.1)
    (hm : (f.primary L).mask L.val.1 (cylinderZero x) ≠ 0)
    (hT : (f.primary L).target L.val.1 (cylinderZero x) ≠ 0) :
    PhysicalGraphBounds.liftXY x ∈ PhysicalGraphBounds.annulus (a / 4) (2 * b) ∧
      ‖PhysicalGraphBounds.liftZT x‖ ≤ 2 := by
  let y := PhysicalClassBounds.cylindricalMap x
  have hy := hloc.normalized L y hx (Real.sqrt_nonneg _) hm hT
  have hq : 0 < SimilarityCoordinates.coordinateQ (2 * h) y.2.1 := by linarith [hy.1]
  have hs := Real.sqrt_pos.mpr hq
  have hslow := normalized_slow_norm hh0 hh1 hx hy.1 hy.2.1
  have hlo : 1 / 2 ≤ Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) :=
    (Real.le_sqrt (by norm_num) hq.le).mpr (by nlinarith [hy.1])
  have hhi : Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ≤ 2 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by linarith [hy.2.1])
  have hradlo := (le_div_iff₀ hs).mp hy.2.2.1
  have hradhi := (div_le_iff₀ hs).mp hy.2.2.2
  have hR : y.1 = PolarCharts.radius (PhysicalGraphBounds.liftXY x) := rfl
  rw [hR] at hradlo hradhi
  have hnorm : ‖PhysicalGraphBounds.liftXY x‖ ≤ 2 * b := by
    exact (PolarCharts.norm_le_radius _).trans (hradhi.trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hhi hb.le))
  have hnormlo : a / 4 ≤ ‖PhysicalGraphBounds.liftXY x‖ := by
    have hradius := PolarCharts.radius_le_two_norm (PhysicalGraphBounds.liftXY x)
    have hmul := mul_le_mul_of_nonneg_left hlo ha.le
    linarith
  constructor
  · exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm, hnormlo⟩
  · change max ‖x.1.2.2.2‖ ‖x.1.1‖ ≤ 2
    change max ‖x.1.1‖ ‖x.1.2.2.2‖ ≤ 2 at hslow
    simpa only [max_comm] using hslow

theorem primitive_domain (L : NativeLabel f.active) (x : LiftPoint)
    (hx : 0 < x.1.1)
    (hm : (f.primary L).mask L.val.1 (cylinderZero x) ≠ 0)
    (hT : (f.primary L).target L.val.1 (cylinderZero x) ≠ 0) :
    PhysicalClassBounds.cylindricalMap x ∈ s.domain :=
  hloc.domain L _ hx (Real.sqrt_nonneg _) hm hT

end Localization

section Copies

variable {D h : ℝ}
  (sys : PartitionedCovariance.SlotSystem D h
    ActualSignedGeometry.radialVector ActualSignedGeometry.temporalVector)
  (hh : 0 ≤ h) {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (f : SignedFamily U)

/-- Only the positive-time representative changes; the native potential
source and every carrier are the original ones. -/
noncomputable def potentialCopies (i : Fin 3) : PhysicalCopyBounds.CopyFamily 1 Frequency :=
  PositiveTimeCopyFamily.gate (ActualSignedPhysicalData.potentialFamily sys hh f i)

/-- Pressure copies, given by `PositiveTimeCopyFamily.gate
(ActualSignedPhysicalData.pressureFamily sys hh f)`. -/
noncomputable def pressureCopies : PhysicalCopyBounds.CopyFamily 1 Frequency :=
  PositiveTimeCopyFamily.gate (ActualSignedPhysicalData.pressureFamily sys hh f)

/-- Potential cells, given by `PositiveTimeCopyFamily.gateCells (localizedPotentialCells sys hh
f i)`. -/
noncomputable def potentialCells (i : Fin 3) :
    PhysicalCopyBounds.SupportCells (potentialCopies sys hh f i) :=
  PositiveTimeCopyFamily.gateCells (localizedPotentialCells sys hh f i)

/-- Pressure cells, given by `PositiveTimeCopyFamily.gateCells (localizedPressureCells sys hh
f)`. -/
noncomputable def pressureCells :
    PhysicalCopyBounds.SupportCells (pressureCopies sys hh f) :=
  PositiveTimeCopyFamily.gateCells (localizedPressureCells sys hh f)

variable {a b : ℝ} {s : StripData Native}
  (hloc : PrimitiveLocalization (h := h) f a b s)
  (G : ReferenceGeometry sys f) (hh0 : 0 < h) (hh1 : h < 1 / 2)
  (ha : 0 < a) (hb : 0 < b)

include hloc G hh0 hh1 ha hb

/-- The globally quantified support record is valid for the explicit
positive-time amplitude representative. -/
theorem potential_support (i : Fin 3) :
    LocalPhysicalCopyBounds.SupportData (potentialCopies sys hh f i)
      (a / 4) (2 * b) h sys.radius 2 0 where
  gap_le _ := le_rfl
  gap_native _ := Nat.zero_le _
  angular_integer k L := by
    by_cases hL : L ∈ f.active
    · refine ⟨(G.angular ⟨L.val, L.property, hL⟩).mode, ?_⟩
      simpa only [potentialCopies, PositiveTimeCopyFamily.gate,
        ActualSignedPhysicalData.potentialFamily, extendedCarrier, dite_eq_left hL] using
        angular_integer sys f G ⟨L.val, L.property, hL⟩ k
    · exact ⟨0, by simp [potentialCopies, PositiveTimeCopyFamily.gate,
        ActualSignedPhysicalData.potentialFamily, extendedCarrier, hL,
        ActualSignedPhysicalData.carrier]⟩
  geometry_support k I w hw := by
    obtain ⟨hpast, hraw⟩ := (PositiveTimeCopyFamily.gate_amplitude_ne_zero_iff
      (ActualSignedPhysicalData.potentialFamily sys hh f i) k I _).mp hw
    change 0 < (PhysicalWaveSum.commonLift h I.1.val.1 0 w).1.1 at hpast
    change (ActualSignedPhysicalData.potentialFamily sys hh f i).amplitude k I
      (PhysicalWaveSum.commonLift h I.1.val.1 0 w) ≠ 0 at hraw
    rw [commonLift_zero] at hpast hraw
    obtain ⟨hL, _, hm, ht⟩ := potential_amplitude_inputs sys hh f i k I _ hraw
    have hn := primitive_annulus hloc hh0 hh1 ha hb
      ⟨I.1.val, I.1.property, hL⟩ _ hpast hm ht
    refine ⟨?_, hn.2, ?_⟩
    · simpa only [PhysicalGraphBounds.liftXY_physicalLift] using hn.1
    · have hc := potential_amplitude_mem sys hh f i k I _ hraw
      have hwid := width_on_core sys I.1.val 0 k
        (PhysicalGraphBounds.physicalLift h I.1.val.1 w).2 hc
      change |PhysicalGraphBounds.etaCoordinate
        (PhysicalGraphBounds.nativeGraph h I.1.val.1 w -
          (extendedCarrier (h := h) f I.1 k).center)| ≤ sys.radius
      rw [extendedCarrier_center]
      exact hwid
  mask_support k I w hw hne := by
    have hraw := ((PositiveTimeCopyFamily.gate_amplitude_ne_zero_iff
      (ActualSignedPhysicalData.potentialFamily sys hh f i) k I _).mp hne).2
    change (ActualSignedPhysicalData.potentialFamily sys hh f i).amplitude k I
      (PhysicalWaveSum.commonLift h I.1.val.1 0 w) ≠ 0 at hraw
    rw [commonLift_zero] at hraw
    obtain ⟨hL, _, hm, _⟩ := potential_amplitude_inputs sys hh f i k I _ hraw
    rw [← hloc.mask_pullback ⟨I.1.val, I.1.property, hL⟩ w hw]
    exact hm

theorem pressure_support :
    LocalPhysicalCopyBounds.SupportData (pressureCopies sys hh f)
      (a / 4) (2 * b) h sys.radius 2 0 where
  gap_le _ := le_rfl
  gap_native _ := Nat.zero_le _
  angular_integer k L := by
    by_cases hL : L ∈ f.active
    · refine ⟨(G.angular ⟨L.val, L.property, hL⟩).mode, ?_⟩
      simpa only [pressureCopies, PositiveTimeCopyFamily.gate,
        ActualSignedPhysicalData.pressureFamily, extendedCarrier, dite_eq_left hL] using
        angular_integer sys f G ⟨L.val, L.property, hL⟩ k
    · exact ⟨0, by simp [pressureCopies, PositiveTimeCopyFamily.gate,
        ActualSignedPhysicalData.pressureFamily, extendedCarrier, hL,
        ActualSignedPhysicalData.carrier]⟩
  geometry_support k I w hw := by
    obtain ⟨hpast, hraw⟩ := (PositiveTimeCopyFamily.gate_amplitude_ne_zero_iff
      (ActualSignedPhysicalData.pressureFamily sys hh f) k I _).mp hw
    change 0 < (PhysicalWaveSum.commonLift h I.1.val.1 0 w).1.1 at hpast
    change (ActualSignedPhysicalData.pressureFamily sys hh f).amplitude k I
      (PhysicalWaveSum.commonLift h I.1.val.1 0 w) ≠ 0 at hraw
    rw [commonLift_zero] at hpast hraw
    obtain ⟨hL, _, hm, ht⟩ := pressure_amplitude_inputs sys hh f k I _ hraw
    have hn := primitive_annulus hloc hh0 hh1 ha hb
      ⟨I.1.val, I.1.property, hL⟩ _ hpast hm ht
    refine ⟨?_, hn.2, ?_⟩
    · simpa only [PhysicalGraphBounds.liftXY_physicalLift] using hn.1
    · have hc := pressure_amplitude_mem sys hh f k I _ hraw
      have hwid := width_on_core sys I.1.val 0 k
        (PhysicalGraphBounds.physicalLift h I.1.val.1 w).2 hc
      change |PhysicalGraphBounds.etaCoordinate
        (PhysicalGraphBounds.nativeGraph h I.1.val.1 w -
          (extendedCarrier (h := h) f I.1 k).center)| ≤ sys.radius
      rw [extendedCarrier_center]
      exact hwid
  mask_support k I w hw hne := by
    have hraw := ((PositiveTimeCopyFamily.gate_amplitude_ne_zero_iff
      (ActualSignedPhysicalData.pressureFamily sys hh f) k I _).mp hne).2
    change (ActualSignedPhysicalData.pressureFamily sys hh f).amplitude k I
      (PhysicalWaveSum.commonLift h I.1.val.1 0 w) ≠ 0 at hraw
    rw [commonLift_zero] at hraw
    obtain ⟨hL, _, hm, _⟩ := pressure_amplitude_inputs sys hh f k I _ hraw
    rw [← hloc.mask_pullback ⟨I.1.val, I.1.property, hL⟩ w hw]
    exact hm

omit hloc G hh0 hh1 hb in
/-- Potential carrier, constructed using `PositiveTimeCopyFamily.gateCarrier`. -/
noncomputable def potentialCarrier (hp : NativeProfiles (h := h) f) (i : Fin 3) :
    PhysicalCopyBounds.CarrierBounds (potentialCopies sys hh f i)
      (potentialCells sys hh f i) (a / 4) (2 * b) h sys.radius :=
  PositiveTimeCopyFamily.gateCarrier (localizedPotentialCells sys hh f i)
    (ActualSignedPhysicalData.potentialCarrier sys hh f ha hp i)

omit hloc G hh0 hh1 hb in
/-- Pressure carrier, given by `PositiveTimeCopyFamily.gateCarrier (localizedPressureCells sys
hh f) (ActualSignedPhysicalData.pressureCarrier sys hh f ha hp)`. -/
noncomputable def pressureCarrier (hp : NativeProfiles (h := h) f) :
    PhysicalCopyBounds.CarrierBounds (pressureCopies sys hh f)
      (pressureCells sys hh f) (a / 4) (2 * b) h sys.radius :=
  PositiveTimeCopyFamily.gateCarrier (localizedPressureCells sys hh f)
    (ActualSignedPhysicalData.pressureCarrier sys hh f ha hp)

omit hloc G hh0 hh1 hb in
theorem potential_amplitude_smooth (hn : NativeRegular sys hh f)
    (i : Fin 3) (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1) :
    ContDiffOn ℝ ∞ ((potentialCopies sys hh f i).amplitude k I) (liftedNativePast a b) := by
  apply (ActualSignedPhysicalData.potential_amplitude_smooth sys hh f ha hn i k I).congr
  intro x hx
  exact PositiveTimeCopyFamily.gate_amplitude_eq _ _ _ hx.2

omit hloc G hh0 hh1 hb in
theorem pressure_amplitude_smooth (hn : NativeRegular sys hh f)
    (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1) :
    ContDiffOn ℝ ∞ ((pressureCopies sys hh f).amplitude k I) (liftedNativePast a b) := by
  apply (ActualSignedPhysicalData.pressure_amplitude_smooth sys hh f ha hn k I).congr
  intro x hx
  exact PositiveTimeCopyFamily.gate_amplitude_eq _ _ _ hx.2

theorem potentialSmooth (hp : NativeProfiles (h := h) f) (hn : NativeRegular sys hh f)
    (i : Fin 3) :
    LocalPhysicalCopyBounds.SmoothData (potentialCopies sys hh f i) (a / 4) h sys.radius := by
  let hr := potential_support sys hh f hloc G hh0 hh1 ha hb i
  constructor
  · intro k I w hw ht
    exact LocalPhysicalCopyBounds.SmoothNear.of_open (liftedNativePast_open a b)
      (potential_amplitude_smooth sys hh f ha hn i k I)
      (commonLift_mem_liftedNativePast ha _ hw (hr.tsupport_geometry I k ht).1)
  · intro k I w hw ht j hj
    have hc := (potentialCells sys hh f i).term_tsupport_mem
      (div_pos ha (by norm_num)) I k (hr.tsupport_geometry I k ht).1 ht
    have hl := term_tsupport_labelRegion hr hh0 hh1 I k hw ht
    have hp' := hp.covers I.1 w hw hl
      (by simpa only [potentialCopies, PositiveTimeCopyFamily.gate,
        ActualSignedPhysicalData.potentialFamily, commonLift_zero] using hc.2)
    change LocalPhysicalCopyBounds.SmoothNear (extendedCarrier (h := h) f I.1 k).F
        (LocalPhysicalCopyBounds.slotSlow ((extendedCarrier (h := h) f I.1 k).withChart j) _ _ _ _
            _) ∧
      LocalPhysicalCopyBounds.SmoothNear (extendedCarrier (h := h) f I.1 k).G
        (LocalPhysicalCopyBounds.slotSlow ((extendedCarrier (h := h) f I.1 k).withChart j) _ _ _ _
            _)
    rw [slotSlow_eq_nativeSlow (div_pos ha (by norm_num)) _ _ _ _ _ _ hj]
    exact ⟨LocalPhysicalCopyBounds.SmoothNear.of_open (hp.region_open I.1)
      (hp.jets.smooth (k, I.1)).fst hp',
      LocalPhysicalCopyBounds.SmoothNear.of_open (hp.region_open I.1)
      (hp.jets.smooth (k, I.1)).snd hp'⟩

theorem pressureSmooth (hp : NativeProfiles (h := h) f) (hn : NativeRegular sys hh f) :
    LocalPhysicalCopyBounds.SmoothData (pressureCopies sys hh f) (a / 4) h sys.radius := by
  let hr := pressure_support sys hh f hloc G hh0 hh1 ha hb
  constructor
  · intro k I w hw ht
    exact LocalPhysicalCopyBounds.SmoothNear.of_open (liftedNativePast_open a b)
      (pressure_amplitude_smooth sys hh f ha hn k I)
      (commonLift_mem_liftedNativePast ha _ hw (hr.tsupport_geometry I k ht).1)
  · intro k I w hw ht j hj
    have hc := (pressureCells sys hh f).term_tsupport_mem
      (div_pos ha (by norm_num)) I k (hr.tsupport_geometry I k ht).1 ht
    have hl := term_tsupport_labelRegion hr hh0 hh1 I k hw ht
    have hp' := hp.covers I.1 w hw hl
      (by simpa only [pressureCopies, PositiveTimeCopyFamily.gate,
        ActualSignedPhysicalData.pressureFamily, commonLift_zero] using hc.2)
    change LocalPhysicalCopyBounds.SmoothNear (extendedCarrier (h := h) f I.1 k).F
        (LocalPhysicalCopyBounds.slotSlow ((extendedCarrier (h := h) f I.1 k).withChart j) _ _ _ _
            _) ∧
      LocalPhysicalCopyBounds.SmoothNear (extendedCarrier (h := h) f I.1 k).G
        (LocalPhysicalCopyBounds.slotSlow ((extendedCarrier (h := h) f I.1 k).withChart j) _ _ _ _
            _)
    rw [slotSlow_eq_nativeSlow (div_pos ha (by norm_num)) _ _ _ _ _ _ hj]
    exact ⟨LocalPhysicalCopyBounds.SmoothNear.of_open (hp.region_open I.1)
      (hp.jets.smooth (k, I.1)).fst hp',
      LocalPhysicalCopyBounds.SmoothNear.of_open (hp.region_open I.1)
      (hp.jets.smooth (k, I.1)).snd hp'⟩

end Copies

/-! ## Source charts confined to positive time -/

/-- The chart equality is asserted only on its actual open domain.  The
source remains the original source, including its unchanged totalization. -/
noncomputable def identitySourceChart {N : ℕ} {K I : Type}
    (f : PhysicalCopyBounds.CopyFamily N K) (cells : PhysicalCopyBounds.SupportCells f)
    {a b h r Z σ : ℝ} {gap : ℕ} (ha : 0 < a)
    (hs : LocalPhysicalCopyBounds.SupportData (PositiveTimeCopyFamily.gate f)
      a b h r Z gap)
    (s : StripData LiftPoint) (source : I → ℕ → LiftPoint → ℂ)
    (idx : K → PhysicalWaveSum.WaveIndex N → I)
    (he : ∀ k J x, f.amplitude k J x =
      ChartScales.Q J.1.val.1 ^ σ • source (idx k J) J.1.val.1 x)
    (hd : ∀ k J x, x ∈ PositiveTimeCopyFamily.liftPast →
      f.amplitude k J x ≠ 0 → x ∈ s.domain) :
    LocalPhysicalCopyBounds.CommonChart (PositiveTimeCopyFamily.gate f)
      (PositiveTimeCopyFamily.gateCells cells) a b h r σ source where
  sourceIndex := idx
  map _ _ := id
  domain _ _ := s.domain ∩ PositiveTimeCopyFamily.liftPast
  open_domain _ _ := s.isOpen_domain.inter PositiveTimeCopyFamily.liftPast_open
  smooth _ _ := contDiffOn_id
  positive_jets m := by
    refine ⟨1, le_rfl, 0, ?_⟩
    intro k J x hx j hj hjm
    simp only [pow_zero, mul_one]
    exact (PhysicalGraphBounds.norm_positive_jet_linear_le
      (ContinuousLinearMap.id ℝ LiftPoint) x hj).trans (by simp)
  amplitude_eq k J x hx :=
    (PositiveTimeCopyFamily.gate_amplitude_eq f k J hx.2).trans (he k J x)
  contains k J z _ _ _ _ hz := by
    have hrad := (hs.tsupport_geometry J k hz).1
    have hm := (PhysicalWaveSum.commonLift_smoothAt h J.1.val.1 (f.gap J.1)
      (PhysicalGraphBounds.scaledRadial_ne_zero
        (PhysicalGraphBounds.annulus_axisFree ha hrad))).continuousAt
    apply hm.continuousWithinAt.mem_closure hz
    intro y hy
    have hraw := (PositiveTimeCopyFamily.gate_amplitude_ne_zero_iff f k J _).mp
      (PhysicalWaveSum.globalWave_ne_zero_amp hy)
    exact ⟨hd k J _ hraw.1 hraw.2, hraw.1⟩

section WaveData

variable {D h : ℝ}
  (sys : PartitionedCovariance.SlotSystem D h
    ActualSignedGeometry.radialVector ActualSignedGeometry.temporalVector)
  (hh : 0 ≤ h) {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (f : SignedFamily U)
  {a b : ℝ} {s : StripData Native}
  (hloc : PrimitiveLocalization (h := h) f a b s)
  (G : ReferenceGeometry sys f) (hh0 : 0 < h) (hh1 : h < 1 / 2)
  (ha : 0 < a) (hb : 0 < b)

include hloc hh0 hh1 ha hb

theorem potential_source_domain (i : Fin 3) (k : Frequency)
    (I : PhysicalWaveSum.WaveIndex 1) (x : LiftPoint)
    (hx : x ∈ PositiveTimeCopyFamily.liftPast)
    (hne : (ActualSignedPhysicalData.potentialFamily sys hh f i).amplitude k I x ≠ 0) :
    x ∈ (CartesianCopySource.pullStrip s (a / 4) (2 * b)
      (div_pos ha (by norm_num))).domain := by
  obtain ⟨hL, _, hm, ht⟩ := potential_amplitude_inputs sys hh f i k I x hne
  have hg := primitive_annulus hloc hh0 hh1 ha hb
    ⟨I.1.val, I.1.property, hL⟩ x hx hm ht
  refine ⟨?_, primitive_domain hloc ⟨I.1.val, I.1.property, hL⟩ x hx hm ht⟩
  have hu : ‖PhysicalGraphBounds.liftXY x‖ ≤ 2 * b := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hg.1.1
  have hl : a / 4 ≤ ‖PhysicalGraphBounds.liftXY x‖ := hg.1.2
  exact ⟨by change a / 4 / 2 < _; linarith, by change _ < 2 * b + 1; linarith⟩

theorem pressure_source_domain (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1)
    (x : LiftPoint) (hx : x ∈ PositiveTimeCopyFamily.liftPast)
    (hne : (ActualSignedPhysicalData.pressureFamily sys hh f).amplitude k I x ≠ 0) :
    x ∈ (CartesianCopySource.pullStrip s (a / 4) (2 * b)
      (div_pos ha (by norm_num))).domain := by
  obtain ⟨hL, _, hm, ht⟩ := pressure_amplitude_inputs sys hh f k I x hne
  have hg := primitive_annulus hloc hh0 hh1 ha hb
    ⟨I.1.val, I.1.property, hL⟩ x hx hm ht
  refine ⟨?_, primitive_domain hloc ⟨I.1.val, I.1.property, hL⟩ x hx hm ht⟩
  have hu : ‖PhysicalGraphBounds.liftXY x‖ ≤ 2 * b := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hg.1.1
  have hl : a / 4 ≤ ‖PhysicalGraphBounds.liftXY x‖ := hg.1.2
  exact ⟨by change a / 4 / 2 < _; linarith, by change _ < 2 * b + 1; linarith⟩

variable (hp : NativeProfiles (h := h) f) (hn : NativeRegular sys hh f)
  {P : ℝ} (hP : 1 ≤ P)
  (hf : ∀ L : NativeLabel f.active,
    |((f.primary L).pulse (f.column L)).phase.p L.val.1| ≤ P ∧
    |((f.primary L).pulse (f.column L)).phase.pz L.val.1| ≤ P ∧
    |((f.primary L).pulse (f.column L)).phase.x0 L.val.1| ≤ P)
  {α : ℝ} {w : SourceIndex → ℕ → Native → ℝ}

/-- A physical potential datum using the original source bounds and the
proved positive-time support.  No off-past localization is required. -/
noncomputable def potentialWaveData
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds s h α w
      (nativePotentialSource sys hh f)) :
    PhysicalStageBounds.WaveData h LiftPoint (Fin 3 × SourceIndex) Frequency (Fin 3) where
  lowerRadius := a / 4
  upperRadius := 2 * b
  nativeWidth := sys.radius
  slowBound := 2
  frequencyBound := P
  alpha := α
  shift := -h
  harmonics := 1
  gapBound := 0
  lower_pos := div_pos ha (by norm_num)
  width_nonneg := sys.radius_pos.le
  slow_nonneg := by norm_num
  frequency_one_le := hP
  strip := CartesianCopySource.pullStrip s (a / 4) (2 * b) (div_pos ha (by norm_num))
  weight I n x := w I.2 n (PhysicalClassBounds.cylindricalMap x)
  source I n x := CartesianCopySource.rotatedSource (nativePotentialSource sys hh f) I.2 n x I.1
  source_bounds := componentSourceBounds (CartesianCopySource.sourceBounds_rotated
    (b := 2 * b) (div_pos ha (by norm_num)) hs)
  copies := potentialCopies sys hh f
  cells := potentialCells sys hh f
  chart i := identitySourceChart _ _ (div_pos ha (by norm_num))
    (potential_support sys hh f hloc G hh0 hh1 ha hb i) _ _ (fun k I => (i, I, k))
    (potential_amplitude_eq_source sys hh f i)
    (potential_source_domain sys hh f hloc hh0 hh1 ha hb i)
  chart_maps _ _ _ := fun _ hx => hx.1
  carrier := potentialCarrier sys hh f ha hp
  support := potential_support sys hh f hloc G hh0 hh1 ha hb
  smooth := potentialSmooth sys hh f hloc G hh0 hh1 ha hb hp hn
  frequencies _ := carrier_frequencies f hP hf

/-- Pressure wave data, bundling `lowerRadius`, `upperRadius`, `nativeWidth`, `slowBound` and
the required compatibility proofs. -/
noncomputable def pressureWaveData
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds s h α w
      (nativePressureSource sys hh f)) :
    PhysicalStageBounds.WaveData h LiftPoint SourceIndex Frequency Unit where
  lowerRadius := a / 4
  upperRadius := 2 * b
  nativeWidth := sys.radius
  slowBound := 2
  frequencyBound := P
  alpha := α
  shift := -(2 * CoordinateAlgebra.A h)
  harmonics := 1
  gapBound := 0
  lower_pos := div_pos ha (by norm_num)
  width_nonneg := sys.radius_pos.le
  slow_nonneg := by norm_num
  frequency_one_le := hP
  strip := CartesianCopySource.pullStrip s (a / 4) (2 * b) (div_pos ha (by norm_num))
  weight I n x := w I n (PhysicalClassBounds.cylindricalMap x)
  source I n x := nativePressureSource sys hh f I n (PhysicalClassBounds.cylindricalMap x)
  source_bounds := CartesianCopySource.sourceBounds_pullback
    (b := 2 * b) (div_pos ha (by norm_num)) hs
  copies _ := pressureCopies sys hh f
  cells _ := pressureCells sys hh f
  chart _ := identitySourceChart _ _ (div_pos ha (by norm_num))
    (pressure_support sys hh f hloc G hh0 hh1 ha hb) _ _ (fun k I => (I, k))
    (pressure_amplitude_eq_source sys hh f)
    (pressure_source_domain sys hh f hloc hh0 hh1 ha hb)
  chart_maps _ _ _ := fun _ hx => hx.1
  carrier _ := pressureCarrier sys hh f ha hp
  support _ := pressure_support sys hh f hloc G hh0 hh1 ha hb
  smooth _ := pressureSmooth sys hh f hloc G hh0 hh1 ha hb hp hn
  frequencies _ := carrier_frequencies f hP hf

variable
  (hpotential : LocalPhysicalCopyBounds.LocalSourceBounds s h α w
    (nativePotentialSource sys hh f))
  (hpressure : LocalPhysicalCopyBounds.LocalSourceBounds s h α w
    (nativePressureSource sys hh f))

/-- Every preterminal potential germ is the germ of the original physical
copy sum, including all spatial and time derivatives. -/
theorem potentialWaveData_vector_germ {x : SpaceTime}
    (hx : x ∈ PhysicalWaveSum.preterminal) :
    (potentialWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpotential).vector
      =ᶠ[𝓝 x] PhysicalCopyBounds.vectorSum
        (ActualSignedPhysicalData.potentialFamily sys hh f) (a / 4) h sys.radius :=
  PositiveTimeCopyFamily.vectorSum_germ
    (ActualSignedPhysicalData.potentialFamily sys hh f) (a / 4) h sys.radius hx

theorem pressureWaveData_pressure_germ {x : SpaceTime}
    (hx : x ∈ PhysicalWaveSum.preterminal) :
    (pressureWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpressure).pressure
      =ᶠ[𝓝 x] fun y =>
        ((ActualSignedPhysicalData.pressureFamily sys hh f).sum (a / 4) h sys.radius y).re := by
  filter_upwards [PositiveTimeCopyFamily.sum_germ
    (ActualSignedPhysicalData.pressureFamily sys hh f) (a / 4) h sys.radius hx] with y hy
  exact congrArg Complex.re hy

include G hp hn hP hf hpotential in
/-- The physical estimate applies to the original preterminal potential,
not just to its chosen positive-time representative. -/
theorem potential_physical_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h x ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (PhysicalCopyBounds.vectorSum (ActualSignedPhysicalData.potentialFamily sys hh f)
          (a / 4) h sys.radius) x‖ ≤
        C * PhysicalWaveSum.physicalQ h x ^
          (h * α - PhysicalClassBounds.physicalLoss h (-h) m) := by
  obtain ⟨C, hC, hbound⟩ :=
    (potentialWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpotential).vector_bound
      hh0 hh1 m
  refine ⟨C, hC, fun x hx hq => ?_⟩
  rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
    (potentialWaveData_vector_germ sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpotential hx) m]
  exact hbound x hx hq

include G hp hn hP hf hpressure in
theorem pressure_physical_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h x ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (fun y => ((ActualSignedPhysicalData.pressureFamily sys hh f).sum
          (a / 4) h sys.radius y).re) x‖ ≤
        C * PhysicalWaveSum.physicalQ h x ^
          (h * α - PhysicalClassBounds.physicalLoss h (-(2 * CoordinateAlgebra.A h)) m) := by
  obtain ⟨C, hC, hbound⟩ :=
    (pressureWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpressure).pressure_bound
      hh0 hh1 m
  refine ⟨C, hC, fun x hx hq => ?_⟩
  rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
    (pressureWaveData_pressure_germ sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpressure hx) m]
  exact hbound x hx hq

end WaveData

/-! ## The actual dependent signed family -/

section Actual

open CorrectionInitialization

variable {B N0 : ℕ}
  (s : ∀ l : ActualSignedPhysicalBinding.Label B N0,
    (ActualSignedPhysicalBinding.nativeViews l).StateData)

/-- Every actual singleton supplies the positive-time primitive data.
Neither its current request nor any output support property is assumed. -/
theorem singletonLocalization
    (L : NativeLabel (ActualSignedExterior.family s).active) :
    PrimitiveLocalization (h := ActualPrimary.h)
      ((ActualSignedExterior.family s).singleton L)
      (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
      (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
      ActualPrimaryBounds.strip where
  normalized K y hy _ hm ht := by
    have hK := (ActualSignedExterior.family s).singleton_label_val L K
    change (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).mask
      K.val.1 (nativeCylinder y) ≠ 0 at hm
    change (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).target
      K.val.1 (nativeCylinder y) ≠ 0 at ht
    rw [hK, ← ActualSignedExterior.actualLabel_reference L] at hm ht
    exact PositiveTimeSignedLocalization.normalized_bounds
      (ActualSignedExterior.actualLabel L) y hy hm ht
  domain K y hy _ hm ht := by
    have hK := (ActualSignedExterior.family s).singleton_label_val L K
    change (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).mask
      K.val.1 (nativeCylinder y) ≠ 0 at hm
    change (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).target
      K.val.1 (nativeCylinder y) ≠ 0 at ht
    rw [hK, ← ActualSignedExterior.actualLabel_reference L] at hm ht
    exact PositiveTimeSignedLocalization.native_mem_strip
      (ActualSignedExterior.actualLabel L) y hy hm ht
  mask_pullback K x hx := by
    have hK := (ActualSignedExterior.family s).singleton_label_val L K
    change (ActualSignedPhysicalBinding.primary (ActualSignedExterior.actualLabel L)).mask
      K.val.1 (cylinderZero (PhysicalGraphBounds.physicalLift ActualPrimary.h K.val.1 x)) = _
    rw [hK]
    have he := PositiveTimeSignedLocalization.mask_pullback
      (ActualSignedExterior.actualLabel L) x hx
    rw [ActualSignedExterior.actualLabel_reference L] at he
    have hl : ActualSignedPhysicalBinding.spatialLabel (ActualSignedExterior.actualLabel L) = L.val
        :=
      congrArg Subtype.val (ActualSignedExterior.bandLabel_actualLabel L)
    simpa only [hl] using he

end Actual

end NavierStokes.PositiveTimeSignedData
