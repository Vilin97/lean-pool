/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualMeanPhysicalData
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalStageSupport
import LeanPool.NavierStokesAndEuler.NavierStokes.LocalMeanPhysicalBounds

/-!
# Angular stage data for the actual physical means

The scalar is the same physical mean evaluated on the positive radial
half-plane.  Radial symmetry of the actual auxiliary graph proves its
Cartesian angular representation.  Native annulus support gives a positive
inner radius and the common shrinking outer support.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualMeanStageData

open Set Function Filter ProblemStatement
open scoped Topology ContDiff


/-- The fixed positive radial half-plane, without changing any graph data. -/
noncomputable def radialSection (p : DirectAngularDiagonal.CylPoint) : SpaceTime :=
  (p.1, AxisymmetricResidual.pack p.2.1 0 p.2.2)

theorem radialSection_smooth : ContDiff ℝ ∞ radialSection := by
  unfold radialSection AxisymmetricResidual.pack
  exact contDiff_fst.prodMk (((contDiff_snd.fst.smul_const (coordinateVector 0)).add
    ((contDiff_const (c := (0 : ℝ))).smul_const (coordinateVector 1))).add
      (contDiff_snd.snd.smul_const (coordinateVector 2)))

theorem radialSection_slow (p : DirectAngularDiagonal.CylPoint) :
    DirectAngularDiagonal.slowPoint (radialSection p) = DirectAngularDiagonal.slowOfCyl p := by
  simp [radialSection, DirectAngularDiagonal.slowPoint, DirectAngularDiagonal.slowOfCyl]

theorem radialSection_radius {p : DirectAngularDiagonal.CylPoint} (hp : 0 ≤ p.2.1) :
    DirectAngularDiagonal.radius (radialSection p) = p.2.1 := by
  simp [radialSection, DirectAngularDiagonal.radius, PolarCharts.radius, Real.sqrt_sq hp]

/-- The auxiliary graph, as well as the slow and radial coordinates, is
unchanged when a Cartesian point is moved to its positive radial half-plane. -/
theorem physicalPoint_radialSection (h : ℝ) (w : SpaceTime) :
    PhysicalMeanJetBounds.physicalPoint h (radialSection (DirectAngularDiagonal.cylPoint w)) =
        PhysicalMeanJetBounds.physicalPoint h w := by
  have hs : (DirectAngularDiagonal.radius w) ^ 2 = (w.2 0) ^ 2 + (w.2 1) ^ 2 := by
    exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  simp only [PhysicalMeanJetBounds.physicalPoint, radialSection, DirectAngularDiagonal.cylPoint,
    PhysicalGraphBounds.radialProjection_apply, AxisymmetricResidual.pack_zero,
    AxisymmetricResidual.pack_one, AxisymmetricResidual.pack_two]
  simp [PhysicalClassBounds.cartesianRadius, PhysicalGraphBounds.radialProfile,
    PhysicalGraphBounds.radiusPower, hs]

section Generic

variable {h degree : ℝ} {N Δ : ℕ} {U : Set PhysicalGraphBounds.Plane}

/-- Coefficient, given by `D.field ∘ radialSection`. -/
noncomputable def coefficient (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ U ℝ) :
    DirectAngularDiagonal.Coefficient :=
  D.field ∘ radialSection

theorem coefficient_cylPoint (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ U ℝ) (w :
    SpaceTime) :
    coefficient D (DirectAngularDiagonal.cylPoint w) = D.field w := by
  change D.physical (PhysicalMeanJetBounds.physicalPoint h (radialSection
      (DirectAngularDiagonal.cylPoint w))) =
    D.physical (PhysicalMeanJetBounds.physicalPoint h w)
  rw [physicalPoint_radialSection]

/-- This is a global identity, including the totalized angular frame at the axis. -/
theorem coefficient_angularField (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ U ℝ) :
    DirectAngularDiagonal.angularField (coefficient D) = D.angularField := by
  funext w
  rw [DirectAngularDiagonal.angularField, coefficient_cylPoint]
  change _ = D.field w • PhysicalMeanJetBounds.angularVector (PhysicalGraphBounds.radialProjection
      w)
  simp only [PhysicalMeanJetBounds.angularVector, PhysicalGraphBounds.radialProjection_apply,
    DirectAngularDiagonal.radius, PolarCharts.radius, PhysicalClassBounds.cartesianRadius,
    smul_add, smul_smul]
  congr 1 <;> congr 1 <;> ring

/-- A conservative inner radius common to every native band and stage. -/
noncomputable def innerRadius (h a : ℝ) (s : DirectAngularDiagonal.Slow) : ℝ :=
  (a / 4) * Real.sqrt (LocalAngularDiagonal.slowQ h s)

theorem innerRadius_continuous {a qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContinuousOn (innerRadius h a) (LocalAngularDiagonal.localSlowDomain h qbig) := by
  intro s hs
  exact (continuousAt_const.mul
    (LocalAngularDiagonal.slowQ_smoothAt hh hh1 hs.1).continuousAt.sqrt).continuousWithinAt

theorem innerRadius_pos {a qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a)
    {s : DirectAngularDiagonal.Slow} (hs : s ∈ LocalAngularDiagonal.localSlowDomain h qbig) :
    0 < innerRadius h a s := by
  apply mul_pos (div_pos ha (by norm_num)) (Real.sqrt_pos.mpr ?_)
  exact (SimilarityCoordinates.coordinateQ_spec (a := 2 * h) (p := (1 - s.1, s.2))
    (by linarith) (by linarith) (sub_pos.mpr hs.1)).1

theorem physical_radius_scale (n : ℕ) (w : SpaceTime) :
    DirectAngularDiagonal.radius w = Real.sqrt (ChartScales.Q n) *
      PolarCharts.radius (PhysicalGraphBounds.scaledRadial n w) := by
  unfold DirectAngularDiagonal.radius
  rw [← PhysicalGraphBounds.unscale_radial n w,
    PolarCharts.radius_smul (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _),
    ← Real.sqrt_eq_rpow]

/-- An actual nonzero physical coefficient must lie outside the positive
inner radius.  The proof selects a valid comparable band and uses its native support. -/
theorem innerRadius_le_of_ne (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hs : PhysicalMeanJetBounds.NativeSupport h a b N U D.native)
    {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hq : PhysicalWaveSum.physicalQ h w ≤ ChartScales.Q N) (hne : D.field w ≠ 0) :
    innerRadius h a (DirectAngularDiagonal.slowPoint w) ≤ DirectAngularDiagonal.radius w := by
  have hqpos := PhysicalWaveSum.physicalQ_pos hh hh1 ht
  obtain ⟨n, hn, hqn, hnq⟩ := PhysicalMeanJetBounds.exists_comparable_band N hqpos hq
  have hu := hcover (PhysicalStageSupport.comparable_graph_mem hh hh1 n (D.gap n) ht hqn hnq)
  have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hn ht hu
    (by linarith : PhysicalWaveSum.physicalQ h w / 2 ≤ ChartScales.Q n) hnq.le
    (subset_tsupport _ hne)
  have hr : a / 4 ≤ PolarCharts.radius (PhysicalGraphBounds.scaledRadial n w) := by
    exact hann.2.trans (PolarCharts.norm_le_radius _)
  calc
    innerRadius h a (DirectAngularDiagonal.slowPoint w) = (a / 4) * Real.sqrt
        (PhysicalWaveSum.physicalQ h w) := rfl
    _ ≤ (a / 4) * Real.sqrt (ChartScales.Q n) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqn) (by positivity)
    _ = Real.sqrt (ChartScales.Q n) * (a / 4) := mul_comm _ _
    _ ≤ Real.sqrt (ChartScales.Q n) * PolarCharts.radius (PhysicalGraphBounds.scaledRadial n w) :=
      mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg _)
    _ = DirectAngularDiagonal.radius w := (physical_radius_scale n w).symm

theorem coefficient_smooth (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : PhysicalMeanJetBounds.NativeSupport h a b N U D.native)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    ContDiffOn ℝ ∞ (coefficient D) (DirectAngularDiagonal.positiveDomain
        (LocalAngularDiagonal.localSlowDomain h qbig)) := by
  apply (LocalMeanPhysicalBounds.field_sublevel_smooth D hh hh1 ha hab hU hcover hsm hs hq).comp
    radialSection_smooth.contDiffOn
  intro p hp
  change (radialSection p).1 < 1 ∧
    LocalAngularDiagonal.slowQ h (DirectAngularDiagonal.slowPoint (radialSection p)) < qbig
  rw [radialSection_slow]
  exact hp.1

theorem coefficient_vanishes (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hs : PhysicalMeanJetBounds.NativeSupport h a b N U D.native)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    (p : DirectAngularDiagonal.CylPoint) (hp : DirectAngularDiagonal.slowOfCyl p ∈
        LocalAngularDiagonal.localSlowDomain h qbig)
    (hr : 0 ≤ p.2.1) (hinner : p.2.1 < innerRadius h a (DirectAngularDiagonal.slowOfCyl p)) :
    coefficient D p = 0 := by
  by_contra hne
  have ht : radialSection p ∈ PhysicalWaveSum.preterminal := hp.1
  have hq' : PhysicalWaveSum.physicalQ h (radialSection p) ≤ ChartScales.Q N := by
    change LocalAngularDiagonal.slowQ h (DirectAngularDiagonal.slowPoint (radialSection p)) ≤ _
    rw [radialSection_slow]
    exact hp.2.le.trans hq
  have hb := innerRadius_le_of_ne D hh hh1 ha hab hU hcover hs ht hq' hne
  rw [radialSection_slow, radialSection_radius hr] at hb
  exact (not_lt_of_ge hb) hinner

/-- Coherent angular data, bundling `scalar`, `smooth`, `inner`, `inner_continuous` and the
required compatibility proofs. -/
noncomputable def coherentAngularData (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : PhysicalMeanJetBounds.NativeSupport h a b N U D.native)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h qbig) where
  scalar := coefficient D
  smooth := coefficient_smooth D hh hh1 ha hab hU hcover hsm hs hq
  inner := innerRadius h a
  inner_continuous := innerRadius_continuous hh hh1
  inner_pos _ hp := innerRadius_pos hh hh1 ha hp
  vanishes := coefficient_vanishes D hh hh1 ha hab hU hcover hs hq

theorem coherentAngularData_field (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : PhysicalMeanJetBounds.NativeSupport h a b N U D.native)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    DirectAngularDiagonal.angularField (coherentAngularData D hh hh1 ha hab hU hcover hsm hs qbig
        hq).scalar = D.angularField :=
  coefficient_angularField D

end Generic

/-! ## The fixed actual atlas and native moving support -/

open CorrectionInitialization.ActualPrimary ActualMeanPhysicalData
open CorrectionStep CorrectionState

section Actual

variable {degree : ℝ} {N Δ : ℕ}

theorem nativeSupport_of_moving
    (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native) :
    PhysicalMeanJetBounds.NativeSupport h ActualInitialization.geometry.patch.a
      ActualInitialization.geometry.patch.b N standardRegion.carrier D.native :=
  fun n _ z hz hne => Hm.supported n z hz hne

/-- Actual angular data, constructed using `coherentAngularData`. -/
noncomputable def actualAngularData
    (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h qbig) :=
  coherentAngularData D outgoing.data.h_pos outgoing.data.h_lt_half
    ActualInitialization.geometry.patch.a_pos ActualInitialization.geometry.patch.a_lt_b
    standardRegion.isOpen (fun _ hx => hx) (fun n _ => Hm.smooth n)
    (nativeSupport_of_moving D Hm) qbig hq

@[simp] theorem actualAngularData_field
    (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    DirectAngularDiagonal.angularField (actualAngularData D Hm qbig hq).scalar = D.angularField :=
  coefficient_angularField D

@[simp] theorem actualAngularData_inner
    (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    (actualAngularData D Hm qbig hq).inner = innerRadius h ActualInitialization.geometry.patch.a :=
        rfl

/-- Actual angular support, given by `MixedAxisPreservation.AngularSupport.ofAngularData
(actualAngularData D Hm qbig hq) (fun _ hw => hw)`. -/
noncomputable def actualAngularSupport
    (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    MixedAxisPreservation.AngularSupport (MixedAxisPreservation.localDomain h qbig) :=
  MixedAxisPreservation.AngularSupport.ofAngularData (actualAngularData D Hm qbig hq) (fun _ hw =>
      hw)

@[simp] theorem actualAngularSupport_field
    (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    (actualAngularSupport D Hm qbig hq).field = D.angularField :=
  coefficient_angularField D

theorem actualAngularData_shrinkingSupport
    (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant qbig
      (DirectAngularDiagonal.angularField (actualAngularData D Hm qbig hq).scalar) := by
  rw [actualAngularData_field]
  exact (PhysicalStageSupport.actual_coherent_support D (nativeSupport_of_moving D Hm) hq).2

theorem actualAngularSupport_shrinkingSupport
    (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant qbig
      (actualAngularSupport D Hm qbig hq).field :=
  actualAngularData_shrinkingSupport D Hm qbig hq

theorem actualAngular_zero_germ
    (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N)
    {w : SpaceTime} (hw : w ∈ MixedAxisPreservation.localDomain h qbig)
    (hr : DirectAngularDiagonal.radius w <
      innerRadius h ActualInitialization.geometry.patch.a (DirectAngularDiagonal.slowPoint w)) :
    D.angularField =ᶠ[𝓝 w] fun _ => 0 := by
  have he := (actualAngularData D Hm qbig hq).field_zero_germ
    (LocalAngularDiagonal.localSlowDomain_open outgoing.data.h_pos outgoing.data.h_lt_half qbig) hw
        hr
  rwa [actualAngularData_field] at he

theorem actualAngular_axis_zero_germ
    (D : PhysicalMeanJetBounds.CoherentFamily h degree N Δ standardRegion.carrier ℝ)
    (Hm : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
      commonGauge.radial.outer D.native)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N)
    {w : SpaceTime} (hw : w ∈ MixedAxisPreservation.localDomain h qbig)
    (hr : DirectAngularDiagonal.radius w = 0) :
    D.angularField =ᶠ[𝓝 w] fun _ => 0 := by
  apply actualAngular_zero_germ D Hm qbig hq hw
  rw [hr]
  exact innerRadius_pos outgoing.data.h_pos outgoing.data.h_lt_half
    ActualInitialization.geometry.patch.a_pos hw

end Actual

/-! ## Initialized direct angular mean and actual temporal/rank streams -/

/-- Initial angular data, given by `actualAngularData (initialAngularFamily B N0 N)
(initial_mean_moving B N0).angular qbig hq`. -/
noncomputable def initialAngularData (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularData (initialAngularFamily B N0 N) (initial_mean_moving B N0).angular qbig hq

/-- Initial temporal data, given by `actualAngularData (initialTemporalFamily B N0 N)
(initialTemporal_moving B N0) qbig hq`. -/
noncomputable def initialTemporalData (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularData (initialTemporalFamily B N0 N) (initialTemporal_moving B N0) qbig hq

/-- Initial rank data, given by `actualAngularData (initialRankFamily B N0 N)
(initialRank_moving B N0) qbig hq`. -/
noncomputable def initialRankData (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularData (initialRankFamily B N0 N) (initialRank_moving B N0) qbig hq

/-- Initial stream data, given by `actualAngularData (initialStreamFamily B N0 N)
(initialStream_moving B N0) qbig hq`. -/
noncomputable def initialStreamData (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularData (initialStreamFamily B N0 N) (initialStream_moving B N0) qbig hq

@[simp] theorem initialAngularData_field (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    DirectAngularDiagonal.angularField (initialAngularData B N0 N qbig hq).scalar =
      (initialAngularFamily B N0 N).angularField := coefficient_angularField (initialAngularFamily
          B N0 N)

@[simp] theorem initialTemporalData_field (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    DirectAngularDiagonal.angularField (initialTemporalData B N0 N qbig hq).scalar =
      (initialTemporalFamily B N0 N).angularField := coefficient_angularField
          (initialTemporalFamily B N0 N)

@[simp] theorem initialRankData_field (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    DirectAngularDiagonal.angularField (initialRankData B N0 N qbig hq).scalar =
      (initialRankFamily B N0 N).angularField := coefficient_angularField (initialRankFamily B N0 N)

@[simp] theorem initialStreamData_field (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    DirectAngularDiagonal.angularField (initialStreamData B N0 N qbig hq).scalar =
      (initialStreamFamily B N0 N).angularField := coefficient_angularField (initialStreamFamily B
          N0 N)

/-- Initial angular support, given by `actualAngularSupport (initialAngularFamily B N0 N)
(initial_mean_moving B N0).angular qbig hq`. -/
noncomputable def initialAngularSupport (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularSupport (initialAngularFamily B N0 N) (initial_mean_moving B N0).angular qbig hq

/-- Initial temporal support, given by `actualAngularSupport (initialTemporalFamily B N0 N)
(initialTemporal_moving B N0) qbig hq`. -/
noncomputable def initialTemporalSupport (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularSupport (initialTemporalFamily B N0 N) (initialTemporal_moving B N0) qbig hq

/-- Initial rank support, given by `actualAngularSupport (initialRankFamily B N0 N)
(initialRank_moving B N0) qbig hq`. -/
noncomputable def initialRankSupport (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularSupport (initialRankFamily B N0 N) (initialRank_moving B N0) qbig hq

/-- Initial stream support, given by `actualAngularSupport (initialStreamFamily B N0 N)
(initialStream_moving B N0) qbig hq`. -/
noncomputable def initialStreamSupport (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularSupport (initialStreamFamily B N0 N) (initialStream_moving B N0) qbig hq

@[simp] theorem initialAngularSupport_field (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    (initialAngularSupport B N0 N qbig hq).field = (initialAngularFamily B N0 N).angularField :=
  coefficient_angularField (initialAngularFamily B N0 N)

@[simp] theorem initialTemporalSupport_field (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    (initialTemporalSupport B N0 N qbig hq).field = (initialTemporalFamily B N0 N).angularField :=
  coefficient_angularField (initialTemporalFamily B N0 N)

@[simp] theorem initialRankSupport_field (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    (initialRankSupport B N0 N qbig hq).field = (initialRankFamily B N0 N).angularField :=
  coefficient_angularField (initialRankFamily B N0 N)

@[simp] theorem initialStreamSupport_field (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    (initialStreamSupport B N0 N qbig hq).field = (initialStreamFamily B N0 N).angularField :=
  coefficient_angularField (initialStreamFamily B N0 N)

theorem initial_shrinkingSupport (B N0 N : ℕ) (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant qbig
        (initialAngularSupport B N0 N qbig hq).field ∧
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
          qbig
        (initialTemporalSupport B N0 N qbig hq).field ∧
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
          qbig
        (initialRankSupport B N0 N qbig hq).field ∧
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
          qbig
        (initialStreamSupport B N0 N qbig hq).field :=
  ⟨actualAngularSupport_shrinkingSupport (initialAngularFamily B N0 N) (initial_mean_moving B
      N0).angular qbig hq,
    actualAngularSupport_shrinkingSupport (initialTemporalFamily B N0 N) (initialTemporal_moving B
        N0) qbig hq,
    actualAngularSupport_shrinkingSupport (initialRankFamily B N0 N) (initialRank_moving B N0) qbig
        hq,
    actualAngularSupport_shrinkingSupport (initialStreamFamily B N0 N) (initialStream_moving B N0)
        qbig hq⟩

/-! ## The literal iterated mean stages -/

section Cycles

variable {B N0 N : ℕ} {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}

/-- Cycle angular data, given by `actualAngularData ((initialCycleData H).angularIncrementFamily
k) ((initialCycleData H).angularIncrement_moving k) qbig hq`. -/
noncomputable def cycleAngularData (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularData ((initialCycleData H).angularIncrementFamily k)
    ((initialCycleData H).angularIncrement_moving k) qbig hq

/-- Cycle temporal data, given by `actualAngularData ((initialCycleData H).temporalFamily k)
((initialCycleData H).temporal_moving k) qbig hq`. -/
noncomputable def cycleTemporalData (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularData ((initialCycleData H).temporalFamily k)
    ((initialCycleData H).temporal_moving k) qbig hq

/-- Cycle rank data, given by `actualAngularData ((initialCycleData H).rankFamily k)
((initialCycleData H).rank_moving k) qbig hq`. -/
noncomputable def cycleRankData (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularData ((initialCycleData H).rankFamily k)
    ((initialCycleData H).rank_moving k) qbig hq

/-- Cycle stream data, given by `actualAngularData ((initialCycleData H).streamFamily k)
((initialCycleData H).stream_moving k) qbig hq`. -/
noncomputable def cycleStreamData (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularData ((initialCycleData H).streamFamily k)
    ((initialCycleData H).stream_moving k) qbig hq

@[simp] theorem cycleAngularData_field (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    DirectAngularDiagonal.angularField (cycleAngularData H k qbig hq).scalar =
      ((initialCycleData H).angularIncrementFamily k).angularField :=
  coefficient_angularField ((initialCycleData H).angularIncrementFamily k)

@[simp] theorem cycleTemporalData_field (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    DirectAngularDiagonal.angularField (cycleTemporalData H k qbig hq).scalar =
      ((initialCycleData H).temporalFamily k).angularField :=
  coefficient_angularField ((initialCycleData H).temporalFamily k)

@[simp] theorem cycleRankData_field (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    DirectAngularDiagonal.angularField (cycleRankData H k qbig hq).scalar =
      ((initialCycleData H).rankFamily k).angularField :=
  coefficient_angularField ((initialCycleData H).rankFamily k)

@[simp] theorem cycleStreamData_field (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    DirectAngularDiagonal.angularField (cycleStreamData H k qbig hq).scalar =
      ((initialCycleData H).streamFamily k).angularField :=
  coefficient_angularField ((initialCycleData H).streamFamily k)

/-- Cycle angular support, given by `actualAngularSupport ((initialCycleData
H).angularIncrementFamily k) ((initialCycleData H).angularIncrement_moving k) qbig hq`. -/
noncomputable def cycleAngularSupport (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularSupport ((initialCycleData H).angularIncrementFamily k)
    ((initialCycleData H).angularIncrement_moving k) qbig hq

/-- Cycle temporal support, given by `actualAngularSupport ((initialCycleData H).temporalFamily
k) ((initialCycleData H).temporal_moving k) qbig hq`. -/
noncomputable def cycleTemporalSupport (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularSupport ((initialCycleData H).temporalFamily k)
    ((initialCycleData H).temporal_moving k) qbig hq

/-- Cycle rank support, given by `actualAngularSupport ((initialCycleData H).rankFamily k)
((initialCycleData H).rank_moving k) qbig hq`. -/
noncomputable def cycleRankSupport (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularSupport ((initialCycleData H).rankFamily k)
    ((initialCycleData H).rank_moving k) qbig hq

/-- Cycle stream support, given by `actualAngularSupport ((initialCycleData H).streamFamily k)
((initialCycleData H).stream_moving k) qbig hq`. -/
noncomputable def cycleStreamSupport (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :=
  actualAngularSupport ((initialCycleData H).streamFamily k)
    ((initialCycleData H).stream_moving k) qbig hq

@[simp] theorem cycleAngularSupport_field (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    (cycleAngularSupport H k qbig hq).field =
      ((initialCycleData H).angularIncrementFamily k).angularField :=
  coefficient_angularField ((initialCycleData H).angularIncrementFamily k)

@[simp] theorem cycleTemporalSupport_field (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    (cycleTemporalSupport H k qbig hq).field =
      ((initialCycleData H).temporalFamily k).angularField :=
  coefficient_angularField ((initialCycleData H).temporalFamily k)

@[simp] theorem cycleRankSupport_field (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    (cycleRankSupport H k qbig hq).field =
      ((initialCycleData H).rankFamily k).angularField :=
  coefficient_angularField ((initialCycleData H).rankFamily k)

@[simp] theorem cycleStreamSupport_field (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    (cycleStreamSupport H k qbig hq).field =
      ((initialCycleData H).streamFamily k).angularField :=
  coefficient_angularField ((initialCycleData H).streamFamily k)

theorem cycle_shrinkingSupport (H : InitialCycleInput B N0 N p) (k : ℕ)
    (qbig : ℝ) (hq : qbig ≤ ChartScales.Q N) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant qbig
        (cycleAngularSupport H k qbig hq).field ∧
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
          qbig
        (cycleTemporalSupport H k qbig hq).field ∧
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
          qbig
        (cycleRankSupport H k qbig hq).field ∧
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
          qbig
        (cycleStreamSupport H k qbig hq).field :=
  ⟨actualAngularSupport_shrinkingSupport ((initialCycleData H).angularIncrementFamily k)
      ((initialCycleData H).angularIncrement_moving k) qbig hq,
    actualAngularSupport_shrinkingSupport ((initialCycleData H).temporalFamily k)
      ((initialCycleData H).temporal_moving k) qbig hq,
    actualAngularSupport_shrinkingSupport ((initialCycleData H).rankFamily k)
      ((initialCycleData H).rank_moving k) qbig hq,
    actualAngularSupport_shrinkingSupport ((initialCycleData H).streamFamily k)
      ((initialCycleData H).stream_moving k) qbig hq⟩

end Cycles

end NavierStokes.ActualMeanStageData
