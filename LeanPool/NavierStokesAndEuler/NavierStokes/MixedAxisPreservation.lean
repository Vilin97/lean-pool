/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalPhysicalCopyBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.DirectAngularDiagonal
import LeanPool.NavierStokesAndEuler.NavierStokes.AxisPreservation
import LeanPool.NavierStokesAndEuler.NavierStokes.NaturalCore

/-!
# Axis preservation for the mixed physical diagonal

The wave terms below are the actual sums of full, copy-dependent carriers.
Only native support geometry and support cells are used.  Mean stream
potentials and direct angular velocities remain separate inputs and sums.

The support hypotheses may hold on a proper open physical subdomain, such
as `t < 1` and `physicalQ h < qbig`.  No global smoothness of an uncut stage,
common annular radius for all stages, or blow-up of the resulting diagonal
is postulated.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.MixedAxisPreservation

open Set Function Filter ProblemStatement
open scoped Topology ContDiff BigOperators

universe u

/-! ## Actual copy sums vanish near the axis -/

theorem copy_sum_zero_germ {H : ℕ} {K : Type*}
    {f : PhysicalCopyBounds.CopyFamily H K} {a b h r0 Z : ℝ} {gap : ℕ}
    (hf : LocalPhysicalCopyBounds.SupportData f a b h r0 Z gap)
    (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1 / 2) {w : SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (haxis : PhysicalGraphBounds.radialProjection w = 0) :
    f.sum a h r0 =ᶠ[𝓝 w] fun _ => 0 := by
  classical
  obtain ⟨s, _, hsum⟩ := hf.sum_locally_finite hh hh1 hw
  have hz (I : PhysicalWaveSum.WaveIndex H) :
      f.periodized a h r0 I =ᶠ[𝓝 w] fun _ => 0 := by
    apply hf.periodized_zero_off_annulus I
    intro hm
    apply PhysicalGraphBounds.annulus_axisFree ha hm
    simp only [PhysicalGraphBounds.scaledRadial, _root_.smul_apply,
      haxis, smul_zero]
  have hfinite : ∀ᶠ y in 𝓝 w, ∀ I ∈ s, f.periodized a h r0 I y = 0 :=
    (eventually_all_finset s).2 (fun I _ => hz I)
  filter_upwards [hsum, hfinite] with y hy hzero
  rw [hy]
  exact Finset.sum_eq_zero hzero

theorem copy_vector_zero_germ {H : ℕ} {K : Type*}
    {f : Fin 3 → PhysicalCopyBounds.CopyFamily H K} {a b h r0 Z : ℝ} {gap : ℕ}
    (hf : ∀ i, LocalPhysicalCopyBounds.SupportData (f i) a b h r0 Z gap)
    (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1 / 2) {w : SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (haxis : PhysicalGraphBounds.radialProjection w = 0) :
    PhysicalCopyBounds.vectorSum f a h r0 =ᶠ[𝓝 w] fun _ => 0 := by
  have hz : ∀ᶠ y in 𝓝 w, ∀ i : Fin 3, (f i).sum a h r0 y = 0 :=
    (Filter.eventually_all).2 (fun i => copy_sum_zero_germ (hf i) ha hh hh1 hw haxis)
  filter_upwards [hz] with y hy
  simp only [PhysicalCopyBounds.vectorSum, hy, map_zero, Finset.sum_const_zero]

/-- Primitive data for one actual vector-valued copy sum.  Support cells
retain the genuine locally finite meaning of the copy periodization. -/
structure CopyPotential (h : ℝ) where
  /-- Copy of `CopyPotential`, of type `Type u`. -/
  Copy : Type u
  /-- Harmonics of `CopyPotential`, of type `ℕ`. -/
  harmonics : ℕ
  /-- Family of `CopyPotential`, of type `Fin 3 → PhysicalCopyBounds.CopyFamily harmonics Copy`. -/
  family : Fin 3 → PhysicalCopyBounds.CopyFamily harmonics Copy
  /-- Inner of `CopyPotential`, of type `ℝ`. -/
  inner : ℝ
  /-- Outer of `CopyPotential`, of type `ℝ`. -/
  outer : ℝ
  /-- Width of `CopyPotential`, of type `ℝ`. -/
  width : ℝ
  /-- Axial radius of `CopyPotential`, of type `ℝ`. -/
  axialRadius : ℝ
  /-- Gap of `CopyPotential`, of type `ℕ`. -/
  gap : ℕ
  inner_pos : 0 < inner
  support : ∀ i, LocalPhysicalCopyBounds.SupportData (family i)
    inner outer h width axialRadius gap
  /-- Cells of `CopyPotential`, of type `∀ i, PhysicalCopyBounds.SupportCells (family i)`. -/
  cells : ∀ i, PhysicalCopyBounds.SupportCells (family i)

/-- Field, given by `PhysicalCopyBounds.vectorSum p.family p.inner h p.width`. -/
noncomputable def CopyPotential.field {h : ℝ} (p : CopyPotential.{u} h) : VelocityField :=
  PhysicalCopyBounds.vectorSum p.family p.inner h p.width

theorem CopyPotential.zero_germ {h : ℝ} (p : CopyPotential.{u} h)
    (hh : 0 < h) (hh1 : h < 1 / 2) {w : SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (haxis : PhysicalGraphBounds.radialProjection w = 0) :
    p.field =ᶠ[𝓝 w] fun _ => 0 :=
  copy_vector_zero_germ p.support p.inner_pos hh hh1 hw haxis

/-! ## Local primitive support of the mean terms -/

/-- Support of a literal angular scalar on the actual physical domain.
Smoothness is deliberately absent: the domain can be the raw stage's
small-`q` domain, and axis preservation uses only these support facts. -/
structure AngularSupport (Ω : Set SpaceTime) where
  /-- Scalar of `AngularSupport`, of type `DirectAngularDiagonal.Coefficient`. -/
  scalar : DirectAngularDiagonal.Coefficient
  /-- Inner of `AngularSupport`, of type `DirectAngularDiagonal.Slow → ℝ`. -/
  inner : DirectAngularDiagonal.Slow → ℝ
  inner_continuous : ContinuousOn (fun w => inner (DirectAngularDiagonal.slowPoint w)) Ω
  inner_pos : ∀ w ∈ Ω, 0 < inner (DirectAngularDiagonal.slowPoint w)
  vanishes : ∀ w ∈ Ω, DirectAngularDiagonal.radius w < inner (DirectAngularDiagonal.slowPoint w) →
    scalar (DirectAngularDiagonal.cylPoint w) = 0

/-- Field, given by `DirectAngularDiagonal.angularField D.scalar`. -/
noncomputable def AngularSupport.field {Ω : Set SpaceTime} (D : AngularSupport Ω) : VelocityField :=
  DirectAngularDiagonal.angularField D.scalar

/-- Zero, bundling `scalar`, `inner`, `inner_continuous`, `inner_pos` and the required
compatibility proofs. -/
noncomputable def AngularSupport.zero (Ω : Set SpaceTime) : AngularSupport Ω where
  scalar := 0
  inner := fun _ => 1
  inner_continuous := continuousOn_const
  inner_pos _ _ := zero_lt_one
  vanishes _ _ _ := rfl

/-- Finite direct angular pieces can be combined without taking a radial
or axial primitive.  The inner support radius is their positive minimum. -/
noncomputable def AngularSupport.add {Ω : Set SpaceTime}
    (D E : AngularSupport Ω) : AngularSupport Ω where
  scalar := D.scalar + E.scalar
  inner := fun s => min (D.inner s) (E.inner s)
  inner_continuous := continuous_min.comp_continuousOn
    (D.inner_continuous.prodMk E.inner_continuous)
  inner_pos w hw := lt_min (D.inner_pos w hw) (E.inner_pos w hw)
  vanishes w hw hr := by
    change D.scalar _ + E.scalar _ = 0
    rw [D.vanishes w hw (hr.trans_le (min_le_left _ _)),
      E.vanishes w hw (hr.trans_le (min_le_right _ _)), add_zero]

theorem AngularSupport.field_add {Ω : Set SpaceTime} (D E : AngularSupport Ω) :
    (D.add E).field = fun w => D.field w + E.field w := by
  funext w
  simp only [AngularSupport.field, AngularSupport.add, DirectAngularDiagonal.angularField,
    Pi.add_apply, mul_add, add_smul]
  abel

/-- Existing mean-field `AngularData` restricts to the required physical
domain.  Its actual scalar, normalization, and graph are unchanged. -/
noncomputable def AngularSupport.ofAngularData {U : Set DirectAngularDiagonal.Slow}
    (D : DirectAngularDiagonal.AngularData U) {Ω : Set SpaceTime}
    (hΩ : Ω ⊆ DirectAngularDiagonal.physicalDomain U) : AngularSupport Ω where
  scalar := D.scalar
  inner := D.inner
  inner_continuous := D.inner_continuous.comp
    DirectAngularDiagonal.slowPoint_smooth.continuous.continuousOn hΩ
  inner_pos _ hw := D.inner_pos _ (hΩ hw)
  vanishes w hw hr := D.vanishes _ (hΩ hw) (DirectAngularDiagonal.radius_nonneg w) hr

theorem AngularSupport.zero_germ {Ω : Set SpaceTime} (D : AngularSupport Ω)
    (hΩ : IsOpen Ω) {w : SpaceTime} (hw : w ∈ Ω)
    (haxis : DirectAngularDiagonal.radius w = 0) :
    D.field =ᶠ[𝓝 w] fun _ => 0 := by
  have hi := D.inner_continuous.continuousAt (hΩ.mem_nhds hw)
  have hlt : DirectAngularDiagonal.radius w < D.inner (DirectAngularDiagonal.slowPoint w) :=
    haxis ▸ D.inner_pos w hw
  filter_upwards [hΩ.mem_nhds hw,
    (DirectAngularDiagonal.radius_continuous.continuousAt.sub hi).eventually
      (gt_mem_nhds (sub_neg.mpr hlt))] with y hy hsmall
  have hz := D.vanishes y hy (sub_neg.mp hsmall)
  simp only [AngularSupport.field, DirectAngularDiagonal.angularField, hz,
    mul_zero, zero_smul, add_zero]

theorem radius_zero_of_axis {w : SpaceTime}
    (haxis : PhysicalGraphBounds.radialProjection w = 0) :
    DirectAngularDiagonal.radius w = 0 := by
  simp [DirectAngularDiagonal.radius, haxis, PolarCharts.radius]

/-- One potential increment: finitely many actual copy-vector sums and
finitely many literal azimuthal mean stream potentials.  Direct angular
velocities are not included in this potential. -/
structure PotentialStage (h : ℝ) (Ω : Set SpaceTime) where
  /-- Wave count of `PotentialStage`, of type `ℕ`. -/
  waveCount : ℕ
  /-- Waves of `PotentialStage`, of type `Fin waveCount → CopyPotential.{u} h`. -/
  waves : Fin waveCount → CopyPotential.{u} h
  /-- Stream count of `PotentialStage`, of type `ℕ`. -/
  streamCount : ℕ
  /-- Streams of `PotentialStage`, of type `Fin streamCount → AngularSupport Ω`. -/
  streams : Fin streamCount → AngularSupport Ω

/-- Field, defined pointwise by `(∑ i : Fin p.waveCount, (p.waves i).field w) + ∑ i : Fin
p.streamCount, (p.streams i).field w`. -/
noncomputable def PotentialStage.field {h : ℝ} {Ω : Set SpaceTime}
    (p : PotentialStage.{u} h Ω) : VelocityField :=
  fun w => (∑ i : Fin p.waveCount, (p.waves i).field w) +
    ∑ i : Fin p.streamCount, (p.streams i).field w

theorem PotentialStage.zero_germ {h : ℝ} {Ω : Set SpaceTime}
    (p : PotentialStage.{u} h Ω) (hh : 0 < h) (hh1 : h < 1 / 2)
    (hΩ : IsOpen Ω) {w : SpaceTime} (hw : w ∈ Ω)
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (haxis : PhysicalGraphBounds.radialProjection w = 0) :
    p.field =ᶠ[𝓝 w] fun _ => 0 := by
  have hcopy : ∀ᶠ y in 𝓝 w, ∀ i : Fin p.waveCount, (p.waves i).field y = 0 :=
    (Filter.eventually_all).2 (fun i => (p.waves i).zero_germ hh hh1 ht haxis)
  have hstream : ∀ᶠ y in 𝓝 w, ∀ i : Fin p.streamCount, (p.streams i).field y = 0 :=
    (Filter.eventually_all).2 (fun i => (p.streams i).zero_germ hΩ hw (radius_zero_of_axis haxis))
  filter_upwards [hcopy, hstream] with y hy hs
  simp only [PotentialStage.field, hy, hs, Finset.sum_const_zero, add_zero]

/-- The zeroth potential is the anchored base; all positive stages are the
constructed copy/mean increments. -/
noncomputable def potentialSeries {h : ℝ} {Ω : Set SpaceTime} (base : VelocityField)
    (p : ℕ → PotentialStage.{u} h Ω) : ℕ → VelocityField
  | 0 => base
  | j + 1 => (p j).field

theorem potentialSeries_zero_germ {h : ℝ} {Ω : Set SpaceTime} (base : VelocityField)
    (p : ℕ → PotentialStage.{u} h Ω) (hh : 0 < h) (hh1 : h < 1 / 2)
    (hΩ : IsOpen Ω) {w : SpaceTime} (hw : w ∈ Ω)
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (haxis : PhysicalGraphBounds.radialProjection w = 0) :
    ∀ j, j ≠ 0 → potentialSeries base p j =ᶠ[𝓝 w] fun _ => 0 := by
  intro j hj
  cases j with
  | zero => exact (hj rfl).elim
  | succ j => exact (p j).zero_germ hh hh1 hΩ hw ht haxis

/-! ## The actual two diagonal sums -/

/-- Potential diagonal, given by `SolenoidalDiagonal.potentialSum scales
(PhysicalWaveSum.physicalQ h) (potentialSeries base p)`. -/
noncomputable def potentialDiagonal {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (p : ℕ → PotentialStage.{u} h Ω) (scales : ℕ → ℝ) : VelocityField :=
  SolenoidalDiagonal.potentialSum scales (PhysicalWaveSum.physicalQ h) (potentialSeries base p)

/-- Direct diagonal, given by `DirectAngularDiagonal.angularSum scales
(PhysicalWaveSum.physicalQ h) (fun j => (D j).scalar)`. -/
noncomputable def directDiagonal (h : ℝ) {Ω : Set SpaceTime}
    (D : ℕ → AngularSupport Ω) (scales : ℕ → ℝ) : VelocityField :=
  DirectAngularDiagonal.angularSum scales (PhysicalWaveSum.physicalQ h) (fun j => (D j).scalar)

/-- Mixed diagonal, given by `DirectAngularDiagonal.mixedVelocity scales
(PhysicalWaveSum.physicalQ h) (potentialSeries base p) (fun j => (D j).scalar)`. -/
noncomputable def mixedDiagonal {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (p : ℕ → PotentialStage.{u} h Ω)
    (D : ℕ → AngularSupport Ω) (scales : ℕ → ℝ) : VelocityField :=
  DirectAngularDiagonal.mixedVelocity scales (PhysicalWaveSum.physicalQ h)
    (potentialSeries base p) (fun j => (D j).scalar)

theorem mixedDiagonal_eq {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (p : ℕ → PotentialStage.{u} h Ω)
    (D : ℕ → AngularSupport Ω) (scales : ℕ → ℝ) :
    mixedDiagonal base p D scales = fun w =>
      SpatialCurl.spatialCurl (potentialDiagonal base p scales) w + directDiagonal h D scales w :=
          rfl

theorem directDiagonal_zero_germ {h : ℝ} {Ω : Set SpaceTime}
    (D : ℕ → AngularSupport Ω) (hh : 0 < h) (hh1 : h < 1 / 2)
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop)
    (hΩ : IsOpen Ω) {w : SpaceTime} (hw : w ∈ Ω)
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (haxis : PhysicalGraphBounds.radialProjection w = 0) :
    directDiagonal h D scales =ᶠ[𝓝 w] fun _ => 0 :=
  DirectAngularDiagonal.potentialSum_zero_germ hs
    (PhysicalWaveSum.physicalQ_smoothAt hh hh1 ht).continuousAt
    (PhysicalWaveSum.physicalQ_pos hh hh1 ht) (fun j => (D j).field)
    (fun j => (D j).zero_germ hΩ hw (radius_zero_of_axis haxis))

theorem potentialDiagonal_eq_cutBase_germ {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (p : ℕ → PotentialStage.{u} h Ω)
    (hh : 0 < h) (hh1 : h < 1 / 2) {scales : ℕ → ℝ}
    (hs : Tendsto scales atTop atTop) (hΩ : IsOpen Ω) {w : SpaceTime}
    (hw : w ∈ Ω) (ht : w ∈ PhysicalWaveSum.preterminal)
    (haxis : PhysicalGraphBounds.radialProjection w = 0) :
    potentialDiagonal base p scales =ᶠ[𝓝 w]
      fun y => SmoothCutoffs.scaledCutoff (scales 0) (PhysicalWaveSum.physicalQ h y) • base y :=
  AxisPreservation.potentialSum_eq_first_near hs
    (PhysicalWaveSum.physicalQ_smoothAt hh hh1 ht).continuousAt
    (PhysicalWaveSum.physicalQ_pos hh hh1 ht)
    (potentialSeries_zero_germ base p hh hh1 hΩ hw ht haxis)

/-- Every preterminal axis germ in the support domain is the curl of the
cut base, even before its zeroth cutoff has reached the plateau. -/
theorem mixedDiagonal_eq_cutBase_germ {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (p : ℕ → PotentialStage.{u} h Ω)
    (D : ℕ → AngularSupport Ω) (hh : 0 < h) (hh1 : h < 1 / 2)
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop)
    (hΩ : IsOpen Ω) {w : SpaceTime} (hw : w ∈ Ω)
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (haxis : PhysicalGraphBounds.radialProjection w = 0) :
    mixedDiagonal base p D scales =ᶠ[𝓝 w] SpatialCurl.spatialCurl
      (fun y => SmoothCutoffs.scaledCutoff (scales 0) (PhysicalWaveSum.physicalQ h y) • base y) :=
          by
  have hp := SolenoidalDiagonal.spatialCurl_eventuallyEq
    (potentialDiagonal_eq_cutBase_germ base p hh hh1 hs hΩ hw ht haxis)
  have hd := directDiagonal_zero_germ D hh hh1 hs hΩ hw ht haxis
  filter_upwards [hp, hd] with y hy hdy
  change SpatialCurl.spatialCurl (potentialDiagonal base p scales) y + directDiagonal h D scales y
      = _
  rw [hdy, add_zero, hy]

/-- On the zeroth cutoff plateau all potential and direct corrections
preserve the base curl on a neighborhood, not just at a point. -/
theorem mixedDiagonal_eq_base_germ {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (p : ℕ → PotentialStage.{u} h Ω)
    (D : ℕ → AngularSupport Ω) (hh : 0 < h) (hh1 : h < 1 / 2)
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop)
    (hΩ : IsOpen Ω) {w : SpaceTime} (hw : w ∈ Ω)
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (haxis : PhysicalGraphBounds.radialProjection w = 0)
    (hsmall : |scales 0 * PhysicalWaveSum.physicalQ h w| < 1 / 2) :
    mixedDiagonal base p D scales =ᶠ[𝓝 w] SpatialCurl.spatialCurl base := by
  have hc := (SmoothCutoffs.scaledCutoff_eventually_one hsmall).comp_tendsto
    (PhysicalWaveSum.physicalQ_smoothAt hh hh1 ht).continuousAt
  have hbase : (fun y => SmoothCutoffs.scaledCutoff (scales 0) (PhysicalWaveSum.physicalQ h y) •
      base y)
      =ᶠ[𝓝 w] base := by
    filter_upwards [hc] with y hy
    change SmoothCutoffs.scaledCutoff (scales 0) (PhysicalWaveSum.physicalQ h y) = 1 at hy
    rw [hy, one_smul]
  exact (mixedDiagonal_eq_cutBase_germ base p D hh hh1 hs hΩ hw ht haxis).trans
    (SolenoidalDiagonal.spatialCurl_eventuallyEq hbase)

theorem mixedDiagonal_axis_jets {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (p : ℕ → PotentialStage.{u} h Ω)
    (D : ℕ → AngularSupport Ω) (hh : 0 < h) (hh1 : h < 1 / 2)
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop)
    (hΩ : IsOpen Ω) {w : SpaceTime} (hw : w ∈ Ω)
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (haxis : PhysicalGraphBounds.radialProjection w = 0)
    (hsmall : |scales 0 * PhysicalWaveSum.physicalQ h w| < 1 / 2) (k : ℕ) :
    iteratedFDeriv ℝ k (mixedDiagonal base p D scales) w =
      iteratedFDeriv ℝ k (SpatialCurl.spatialCurl base) w :=
  (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (mixedDiagonal_eq_base_germ base p D hh hh1 hs hΩ hw ht haxis hsmall) k).self_of_nhds

theorem radialProjection_origin (t : ℝ) :
    PhysicalGraphBounds.radialProjection (t, (0 : Space)) = 0 := by
  simp only [PhysicalGraphBounds.radialProjection_apply]
  rfl

/-- Only eventual support near the terminal origin is needed; the raw
increments can have a smaller domain than the whole preterminal region. -/
theorem origin_eventually_base_germ {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (p : ℕ → PotentialStage.{u} h Ω)
    (D : ℕ → AngularSupport Ω) (hh : 0 < h) (hh1 : h < 1 / 2)
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) (hΩ : IsOpen Ω)
    (hΩaxis : ∀ᶠ t : ℝ in 𝓝[<] 1, (t, (0 : Space)) ∈ Ω) :
    ∀ᶠ t : ℝ in 𝓝[<] 1,
      mixedDiagonal base p D scales =ᶠ[𝓝 (t, (0 : Space))] SpatialCurl.spatialCurl base := by
  have hl := ((tendsto_const_nhds.mul (AxisPreservation.physicalQ_origin_tendsto hh hh1)).abs :
    Tendsto (fun t : ℝ => |scales 0 * PhysicalWaveSum.physicalQ h (t, 0)|)
      (𝓝[<] 1) (𝓝 |scales 0 * 0|))
  simp only [mul_zero, abs_zero] at hl
  have hsmall := hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [hΩaxis, hsmall, self_mem_nhdsWithin (a := (1 : ℝ)) (s := Iio 1)] with t ht hst ht1
  exact mixedDiagonal_eq_base_germ base p D hh hh1 hs hΩ ht ht1 (radialProjection_origin t) hst

theorem origin_eventually_eq_base {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (p : ℕ → PotentialStage.{u} h Ω)
    (D : ℕ → AngularSupport Ω) (hh : 0 < h) (hh1 : h < 1 / 2)
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) (hΩ : IsOpen Ω)
    (hΩaxis : ∀ᶠ t : ℝ in 𝓝[<] 1, (t, (0 : Space)) ∈ Ω) :
    (fun t : ℝ => mixedDiagonal base p D scales (t, 0)) =ᶠ[𝓝[<] 1]
      (fun t => SpatialCurl.spatialCurl base (t, 0)) :=
  (origin_eventually_base_germ base p D hh hh1 hs hΩ hΩaxis).mono fun _ ht => ht.self_of_nhds

theorem origin_blowup {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (p : ℕ → PotentialStage.{u} h Ω)
    (D : ℕ → AngularSupport Ω) (hh : 0 < h) (hh1 : h < 1 / 2)
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) (hΩ : IsOpen Ω)
    (hΩaxis : ∀ᶠ t : ℝ in 𝓝[<] 1, (t, (0 : Space)) ∈ Ω)
    (hbase : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl base (t, 0)‖) (𝓝[<] 1) atTop) :
    Tendsto (fun t : ℝ => ‖mixedDiagonal base p D scales (t, 0)‖) (𝓝[<] 1) atTop := by
  apply hbase.congr'
  exact (origin_eventually_eq_base base p D hh hh1 hs hΩ hΩaxis).symm.mono
    (fun _ ht => congrArg norm ht)

/-! ## Finite initialization stays in stage zero -/

/-- Initialized base, defined pointwise by `base w + initial.field w`. -/
noncomputable def initializedBase {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (initial : PotentialStage.{u} h Ω) : VelocityField :=
  fun w => base w + initial.field w

/-- This is the manuscript's stage numbering: the finite initialization
and base share cutoff zero; each subsequent stage has its own cutoff. -/
noncomputable def initializedSeries {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (initial : PotentialStage.{u} h Ω)
    (p : ℕ → PotentialStage.{u} h Ω) : ℕ → VelocityField :=
  potentialSeries (initializedBase base initial) p

/-- Initialized diagonal, given by `mixedDiagonal (initializedBase base initial) p D scales`. -/
noncomputable def initializedDiagonal {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (initial : PotentialStage.{u} h Ω)
    (p : ℕ → PotentialStage.{u} h Ω) (D : ℕ → AngularSupport Ω)
    (scales : ℕ → ℝ) : VelocityField :=
  mixedDiagonal (initializedBase base initial) p D scales

theorem initializedSeries_zero {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (initial : PotentialStage.{u} h Ω)
    (p : ℕ → PotentialStage.{u} h Ω) (w : SpaceTime) :
    initializedSeries base initial p 0 w = base w + initial.field w := rfl

theorem initializedSeries_succ {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (initial : PotentialStage.{u} h Ω)
    (p : ℕ → PotentialStage.{u} h Ω) (j : ℕ) :
    initializedSeries base initial p (j + 1) = (p j).field := rfl

theorem initializedDiagonal_eq {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (initial : PotentialStage.{u} h Ω)
    (p : ℕ → PotentialStage.{u} h Ω) (D : ℕ → AngularSupport Ω) (scales : ℕ → ℝ) :
    initializedDiagonal base initial p D scales =
      DirectAngularDiagonal.mixedVelocity scales (PhysicalWaveSum.physicalQ h)
        (initializedSeries base initial p) (fun j => (D j).scalar) := rfl

theorem initializedBase_germ {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (initial : PotentialStage.{u} h Ω)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hΩ : IsOpen Ω) {w : SpaceTime}
    (hw : w ∈ Ω) (ht : w ∈ PhysicalWaveSum.preterminal)
    (haxis : PhysicalGraphBounds.radialProjection w = 0) :
    initializedBase base initial =ᶠ[𝓝 w] base := by
  filter_upwards [initial.zero_germ hh hh1 hΩ hw ht haxis] with y hy
  simp only [initializedBase, hy, add_zero]

theorem initialized_eq_base_germ {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (initial : PotentialStage.{u} h Ω)
    (p : ℕ → PotentialStage.{u} h Ω) (D : ℕ → AngularSupport Ω)
    (hh : 0 < h) (hh1 : h < 1 / 2) {scales : ℕ → ℝ}
    (hs : Tendsto scales atTop atTop) (hΩ : IsOpen Ω) {w : SpaceTime}
    (hw : w ∈ Ω) (ht : w ∈ PhysicalWaveSum.preterminal)
    (haxis : PhysicalGraphBounds.radialProjection w = 0)
    (hsmall : |scales 0 * PhysicalWaveSum.physicalQ h w| < 1 / 2) :
    initializedDiagonal base initial p D scales =ᶠ[𝓝 w] SpatialCurl.spatialCurl base :=
  (mixedDiagonal_eq_base_germ (initializedBase base initial) p D hh hh1 hs hΩ hw ht haxis
      hsmall).trans
    (SolenoidalDiagonal.spatialCurl_eventuallyEq (initializedBase_germ base initial hh hh1 hΩ hw ht
        haxis))

theorem initialized_axis_jets {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (initial : PotentialStage.{u} h Ω)
    (p : ℕ → PotentialStage.{u} h Ω) (D : ℕ → AngularSupport Ω)
    (hh : 0 < h) (hh1 : h < 1 / 2) {scales : ℕ → ℝ}
    (hs : Tendsto scales atTop atTop) (hΩ : IsOpen Ω) {w : SpaceTime}
    (hw : w ∈ Ω) (ht : w ∈ PhysicalWaveSum.preterminal)
    (haxis : PhysicalGraphBounds.radialProjection w = 0)
    (hsmall : |scales 0 * PhysicalWaveSum.physicalQ h w| < 1 / 2) (k : ℕ) :
    iteratedFDeriv ℝ k (initializedDiagonal base initial p D scales) w =
      iteratedFDeriv ℝ k (SpatialCurl.spatialCurl base) w :=
  (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (initialized_eq_base_germ base initial p D hh hh1 hs hΩ hw ht haxis hsmall) k).self_of_nhds

theorem initialized_origin_eventually {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (initial : PotentialStage.{u} h Ω)
    (p : ℕ → PotentialStage.{u} h Ω) (D : ℕ → AngularSupport Ω)
    (hh : 0 < h) (hh1 : h < 1 / 2) {scales : ℕ → ℝ}
    (hs : Tendsto scales atTop atTop) (hΩ : IsOpen Ω)
    (hΩaxis : ∀ᶠ t : ℝ in 𝓝[<] 1, (t, (0 : Space)) ∈ Ω) :
    ∀ᶠ t : ℝ in 𝓝[<] 1,
      initializedDiagonal base initial p D scales =ᶠ[𝓝 (t, (0 : Space))] SpatialCurl.spatialCurl
          base := by
  filter_upwards [origin_eventually_base_germ (initializedBase base initial) p D hh hh1 hs hΩ
      hΩaxis,
    hΩaxis, self_mem_nhdsWithin (a := (1 : ℝ)) (s := Iio 1)] with t he ht ht1
  exact he.trans (SolenoidalDiagonal.spatialCurl_eventuallyEq
    (initializedBase_germ base initial hh hh1 hΩ ht ht1 (radialProjection_origin t)))

theorem initialized_origin_blowup {h : ℝ} {Ω : Set SpaceTime}
    (base : VelocityField) (initial : PotentialStage.{u} h Ω)
    (p : ℕ → PotentialStage.{u} h Ω) (D : ℕ → AngularSupport Ω)
    (hh : 0 < h) (hh1 : h < 1 / 2) {scales : ℕ → ℝ}
    (hs : Tendsto scales atTop atTop) (hΩ : IsOpen Ω)
    (hΩaxis : ∀ᶠ t : ℝ in 𝓝[<] 1, (t, (0 : Space)) ∈ Ω)
    (hbase : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl base (t, 0)‖) (𝓝[<] 1) atTop) :
    Tendsto (fun t : ℝ => ‖initializedDiagonal base initial p D scales (t, 0)‖) (𝓝[<] 1) atTop := by
  apply hbase.congr'
  exact (initialized_origin_eventually base initial p D hh hh1 hs hΩ hΩaxis).mono
    (fun _ ht => congrArg norm ht.self_of_nhds.symm)

/-! ## The actual small-similarity-parameter domain -/

/-- Local domain, given by `{w | w.1 < 1 ∧ PhysicalWaveSum.physicalQ h w < qbig}`. -/
noncomputable def localDomain (h qbig : ℝ) : Set SpaceTime :=
  {w | w.1 < 1 ∧ PhysicalWaveSum.physicalQ h w < qbig}

theorem localDomain_open {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (qbig : ℝ) :
    IsOpen (localDomain h qbig) := by
  apply isOpen_iff_mem_nhds.mpr
  intro w hw
  exact Filter.inter_mem (PhysicalWaveSum.preterminal_open.mem_nhds hw.1)
    ((PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw.1).continuousAt (gt_mem_nhds hw.2))

theorem origin_eventually_localDomain {h qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig) :
    ∀ᶠ t : ℝ in 𝓝[<] 1, (t, (0 : Space)) ∈ localDomain h qbig := by
  filter_upwards [self_mem_nhdsWithin (a := (1 : ℝ)) (s := Iio 1),
    (AxisPreservation.physicalQ_origin_tendsto hh hh1).eventually (gt_mem_nhds hqbig)] with t ht hq
  exact ⟨ht, hq⟩

/-! ## Compatibility with the global axis-preservation endpoint -/

/-- When support is known on the full preterminal region, the existing
`AxisPreservation.origin_blowup` theorem applies to the actual copy series.
The local-domain theorem above does not require this stronger hypothesis. -/
theorem origin_blowup_global {h : ℝ}
    (base : VelocityField) (p : ℕ → PotentialStage.{u} h PhysicalWaveSum.preterminal)
    (D : ℕ → AngularSupport PhysicalWaveSum.preterminal)
    (hh : 0 < h) (hh1 : h < 1 / 2) {scales : ℕ → ℝ}
    (hs : Tendsto scales atTop atTop)
    (hbase : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl base (t, 0)‖) (𝓝[<] 1) atTop) :
    Tendsto (fun t : ℝ => ‖mixedDiagonal base p D scales (t, 0)‖) (𝓝[<] 1) atTop := by
  have hz : ∀ t < 1, ∀ j : ℕ, j ≠ 0 → potentialSeries base p j =ᶠ[𝓝 (t, 0)] fun _ => 0 :=
    fun t ht => potentialSeries_zero_germ base p hh hh1 PhysicalWaveSum.preterminal_open ht ht
      (radialProjection_origin t)
  have hb := AxisPreservation.origin_blowup hs
    (fun _ ht => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 ht).continuousAt)
    (fun _ ht => PhysicalWaveSum.physicalQ_pos hh hh1 ht) hz
    (AxisPreservation.physicalQ_origin_tendsto hh hh1) hbase
  apply hb.congr'
  exact Filter.Eventually.of_forall fun t => congrArg norm
    (DirectAngularDiagonal.mixedVelocity_axis scales (PhysicalWaveSum.physicalQ h)
      (potentialSeries base p) (fun j => (D j).scalar) t 0 rfl rfl).symm

/-! ## The anchored base supplies the actual blow-up -/

section FinalBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

theorem anchored_base_axis_tendsto (upper : ℝ) (B : ℕ) :
    Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl (TailGaugePotential.finalPotential H v upper B)
      (t, 0)‖) (𝓝[<] 1) atTop := by
  apply (FinalSlowBase.axis_tendsto H v upper B).congr'
  filter_upwards [self_mem_nhdsWithin (a := (1 : ℝ)) (s := Iio 1)] with t ht
  rw [TailGaugePotential.finalPotential_sameCurl H v upper B (w := (t, 0)) ht]

theorem final_origin_eventually (upper : ℝ) (B : ℕ) {Ω : Set SpaceTime}
    (p : ℕ → PotentialStage.{u} F.data.h Ω) (D : ℕ → AngularSupport Ω)
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) (hΩ : IsOpen Ω)
    (hΩaxis : ∀ᶠ t : ℝ in 𝓝[<] 1, (t, (0 : Space)) ∈ Ω) :
    (fun t : ℝ => mixedDiagonal (TailGaugePotential.finalPotential H v upper B) p D scales (t, 0))
      =ᶠ[𝓝[<] 1] (fun t =>
        ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) • coordinateVector 2) := by
  filter_upwards [origin_eventually_eq_base (TailGaugePotential.finalPotential H v upper B) p D
    F.data.h_pos F.data.h_lt_half hs hΩ hΩaxis,
    self_mem_nhdsWithin (a := (1 : ℝ)) (s := Iio 1)] with t he ht
  rw [he, TailGaugePotential.finalPotential_sameCurl H v upper B (w := (t, 0)) ht,
    FinalSlowBase.origin H v upper B ht]

theorem final_origin_blowup (upper : ℝ) (B : ℕ) {Ω : Set SpaceTime}
    (p : ℕ → PotentialStage.{u} F.data.h Ω) (D : ℕ → AngularSupport Ω)
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) (hΩ : IsOpen Ω)
    (hΩaxis : ∀ᶠ t : ℝ in 𝓝[<] 1, (t, (0 : Space)) ∈ Ω) :
    Tendsto (fun t : ℝ =>
      ‖mixedDiagonal (TailGaugePotential.finalPotential H v upper B) p D scales (t, 0)‖)
      (𝓝[<] 1) atTop :=
  origin_blowup _ p D F.data.h_pos F.data.h_lt_half hs hΩ hΩaxis
    (anchored_base_axis_tendsto H v upper B)

theorem final_speedUnbounded (upper : ℝ) (B : ℕ) {Ω : Set SpaceTime}
    (p : ℕ → PotentialStage.{u} F.data.h Ω) (D : ℕ → AngularSupport Ω)
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) (hΩ : IsOpen Ω)
    (hΩaxis : ∀ᶠ t : ℝ in 𝓝[<] 1, (t, (0 : Space)) ∈ Ω) :
    SpeedUnboundedAtOne (mixedDiagonal (TailGaugePotential.finalPotential H v upper B) p D scales)
        :=
  NaturalCore.speedUnbounded_of_axis_tendsto (final_origin_blowup H v upper B p D hs hΩ hΩaxis)

/-- Raw stage support is needed only where `q < qbig`.  The concrete base,
the actual cutoff scale, and the literal mixed sums are kept throughout. -/
theorem local_final_origin_blowup (upper : ℝ) (B : ℕ) {qbig : ℝ} (hqbig : 0 < qbig)
    (p : ℕ → PotentialStage.{u} F.data.h (localDomain F.data.h qbig))
    (D : ℕ → AngularSupport (localDomain F.data.h qbig))
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) :
    Tendsto (fun t : ℝ =>
      ‖mixedDiagonal (TailGaugePotential.finalPotential H v upper B) p D scales (t, 0)‖)
      (𝓝[<] 1) atTop :=
  final_origin_blowup H v upper B p D hs (localDomain_open F.data.h_pos F.data.h_lt_half qbig)
    (origin_eventually_localDomain F.data.h_pos F.data.h_lt_half hqbig)

theorem local_final_speedUnbounded (upper : ℝ) (B : ℕ) {qbig : ℝ} (hqbig : 0 < qbig)
    (p : ℕ → PotentialStage.{u} F.data.h (localDomain F.data.h qbig))
    (D : ℕ → AngularSupport (localDomain F.data.h qbig))
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) :
    SpeedUnboundedAtOne (mixedDiagonal (TailGaugePotential.finalPotential H v upper B) p D scales)
        :=
  NaturalCore.speedUnbounded_of_axis_tendsto (local_final_origin_blowup H v upper B hqbig p D hs)

theorem local_initialized_final_origin_blowup (upper : ℝ) (B : ℕ)
    {qbig : ℝ} (hqbig : 0 < qbig)
    (initial : PotentialStage.{u} F.data.h (localDomain F.data.h qbig))
    (p : ℕ → PotentialStage.{u} F.data.h (localDomain F.data.h qbig))
    (D : ℕ → AngularSupport (localDomain F.data.h qbig))
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) :
    Tendsto (fun t : ℝ =>
      ‖initializedDiagonal (TailGaugePotential.finalPotential H v upper B) initial p D scales (t,
          0)‖)
      (𝓝[<] 1) atTop :=
  initialized_origin_blowup _ initial p D F.data.h_pos F.data.h_lt_half hs
    (localDomain_open F.data.h_pos F.data.h_lt_half qbig)
    (origin_eventually_localDomain F.data.h_pos F.data.h_lt_half hqbig)
    (anchored_base_axis_tendsto H v upper B)

theorem local_initialized_final_speedUnbounded (upper : ℝ) (B : ℕ)
    {qbig : ℝ} (hqbig : 0 < qbig)
    (initial : PotentialStage.{u} F.data.h (localDomain F.data.h qbig))
    (p : ℕ → PotentialStage.{u} F.data.h (localDomain F.data.h qbig))
    (D : ℕ → AngularSupport (localDomain F.data.h qbig))
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) :
    SpeedUnboundedAtOne
      (initializedDiagonal (TailGaugePotential.finalPotential H v upper B) initial p D scales) :=
  NaturalCore.speedUnbounded_of_axis_tendsto
    (local_initialized_final_origin_blowup H v upper B hqbig initial p D hs)

end FinalBase

/-- The exponent belongs to the already selected, constructed profile. -/
noncomputable def constructedExponent : ℝ := FinalSlowBase.actualProfile.outgoing.data.h

theorem constructed_origin_blowup (upper : ℝ) (B : ℕ) {qbig : ℝ} (hqbig : 0 < qbig)
    (p : ℕ → PotentialStage.{u} constructedExponent (localDomain constructedExponent qbig))
    (D : ℕ → AngularSupport (localDomain constructedExponent qbig))
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) :
    Tendsto (fun t : ℝ =>
      ‖mixedDiagonal (TailGaugePotential.constructedPotential upper B) p D scales (t, 0)‖)
      (𝓝[<] 1) atTop :=
  local_final_origin_blowup FinalSlowBase.actualProfile.certificate
    FinalSlowBase.actualProfile.modulation upper B hqbig p D hs

theorem constructed_speedUnbounded (upper : ℝ) (B : ℕ) {qbig : ℝ} (hqbig : 0 < qbig)
    (p : ℕ → PotentialStage.{u} constructedExponent (localDomain constructedExponent qbig))
    (D : ℕ → AngularSupport (localDomain constructedExponent qbig))
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) :
    SpeedUnboundedAtOne (mixedDiagonal (TailGaugePotential.constructedPotential upper B) p D
        scales) :=
  NaturalCore.speedUnbounded_of_axis_tendsto (constructed_origin_blowup upper B hqbig p D hs)

theorem initialized_constructed_origin_blowup (upper : ℝ) (B : ℕ) {qbig : ℝ} (hqbig : 0 < qbig)
    (initial : PotentialStage.{u} constructedExponent (localDomain constructedExponent qbig))
    (p : ℕ → PotentialStage.{u} constructedExponent (localDomain constructedExponent qbig))
    (D : ℕ → AngularSupport (localDomain constructedExponent qbig))
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) :
    Tendsto (fun t : ℝ =>
      ‖initializedDiagonal (TailGaugePotential.constructedPotential upper B) initial p D scales (t,
          0)‖)
      (𝓝[<] 1) atTop :=
  local_initialized_final_origin_blowup FinalSlowBase.actualProfile.certificate
    FinalSlowBase.actualProfile.modulation upper B hqbig initial p D hs

theorem initialized_constructed_speedUnbounded (upper : ℝ) (B : ℕ) {qbig : ℝ} (hqbig : 0 < qbig)
    (initial : PotentialStage.{u} constructedExponent (localDomain constructedExponent qbig))
    (p : ℕ → PotentialStage.{u} constructedExponent (localDomain constructedExponent qbig))
    (D : ℕ → AngularSupport (localDomain constructedExponent qbig))
    {scales : ℕ → ℝ} (hs : Tendsto scales atTop atTop) :
    SpeedUnboundedAtOne
      (initializedDiagonal (TailGaugePotential.constructedPotential upper B) initial p D scales) :=
  NaturalCore.speedUnbounded_of_axis_tendsto
    (initialized_constructed_origin_blowup upper B hqbig initial p D hs)

end NavierStokes.MixedAxisPreservation
