/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPeriodizedSignedRealization
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalStageBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedAxisPreservation
public import LeanPool.NavierStokesAndEuler.NavierStokes.CartesianCopySource

@[expose] public section

/-!
# Physical data of the actual native signed copies

The primitive signed quotient is unchanged.  Its compact auxiliary cutoff
is repartitioned exactly, and the physical carrier uses the midpoint of
each actual lattice-translated slot.
-/

noncomputable section

namespace NavierStokes.ActualSignedPhysicalData

open Set Function Filter ProblemStatement HarmonicCalculus LinearWaveBounds WeightedClasses
open scoped Topology ContDiff BigOperators InnerProductSpace

attribute [local instance] Classical.propDecidable

abbrev Plane := TorusInverse.Plane
abbrev Frequency := TorusInverse.Frequency
abbrev Cylinder := PhysicalResidualBridge.Cylinder
abbrev LiftPoint := PhysicalGraphBounds.LiftPoint
abbrev Mat2 := SmoothCovariance.Mat2
abbrev Vec2 := SmoothCovariance.Vec2

section Repartition

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
  (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2)
  (mask factor cutoff : ℕ → D → ℝ) (unit Ndot : ℕ → D → Space)
  (A : ℕ → D → Space →L[ℝ] Space) (j : Fin 2)

theorem repartition_amplitude (n : ℕ) (x : D) :
    ((SignedWaveUpdate.coefficients a s d H T R (fun n x => mask n x * factor n x)
      unit Ndot A j).withCutoff cutoff).amplitude n x =
    ((SignedWaveUpdate.coefficients a s d H T R mask unit Ndot A j).withCutoff
      (fun n x => cutoff n x * factor n x)).amplitude n x := by
  simp only [WaveCoefficients.withCutoff,
    ActualPeriodizedSignedRealization.coefficients_amplitude_at,
    ActualPeriodizedSignedRealization.signedScalar_mul_mask, mul_smul]

theorem repartition_pressure (n : ℕ) (x : D) :
    ((SignedWaveUpdate.coefficients a s d H T R (fun n x => mask n x * factor n x)
      unit Ndot A j).withCutoff cutoff).pressure n x =
    ((SignedWaveUpdate.coefficients a s d H T R mask unit Ndot A j).withCutoff
      (fun n x => cutoff n x * factor n x)).pressure n x := by
  simp only [WaveCoefficients.withCutoff,
    ActualPeriodizedSignedRealization.coefficients_pressure_at,
    ActualPeriodizedSignedRealization.signedScalar_mul_mask,
    Complex.real_smul, Complex.ofReal_mul]
  ring

/-- Moving a scalar cutoff from the raw signed mask to the final cutoff
preserves both coefficients, before any differentiation. -/
theorem coefficients_repartition :
    (SignedWaveUpdate.coefficients a s d H T R (fun n x => mask n x * factor n x)
      unit Ndot A j).withCutoff cutoff =
    (SignedWaveUpdate.coefficients a s d H T R mask unit Ndot A j).withCutoff
      (fun n x => cutoff n x * factor n x) := by
  let u := (SignedWaveUpdate.coefficients a s d H T R (fun n x => mask n x * factor n x)
    unit Ndot A j).withCutoff cutoff
  let v := (SignedWaveUpdate.coefficients a s d H T R mask unit Ndot A j).withCutoff
    (fun n x => cutoff n x * factor n x)
  have ha : u.amplitude = v.amplitude := funext fun n => funext fun x =>
    repartition_amplitude a s d H T R mask factor cutoff unit Ndot A j n x
  have hp : u.pressure = v.pressure := funext fun n => funext fun x =>
    repartition_pressure a s d H T R mask factor cutoff unit Ndot A j n x
  calc
    u = {a with amplitude := u.amplitude, pressure := u.pressure} := rfl
    _ = {a with amplitude := v.amplitude, pressure := v.pressure} := by rw [ha, hp]
    _ = v := rfl

/-- The outer bump is one on the Gaussian support, so it can be removed
from the raw mask without changing the actual once-cutoff signed wave. -/
theorem coefficients_outer (clock : ℕ → D → ℝ) :
    (SignedWaveUpdate.coefficients a s d H T R
      (fun n x => mask n x * PrimaryCopyBounds.outerCutoff (clock n x))
      unit Ndot A j).withCutoff (fun n x => GaussianTailFlat.profile (clock n x)) =
    (SignedWaveUpdate.coefficients a s d H T R mask unit Ndot A j).withCutoff
      (fun n x => GaussianTailFlat.profile (clock n x)) := by
  rw [coefficients_repartition]
  have he : (fun n x => GaussianTailFlat.profile (clock n x) * PrimaryCopyBounds.outerCutoff (clock
    n x)) =
      (fun n x => GaussianTailFlat.profile (clock n x)) :=
    funext fun n => funext fun x => PrimaryCopyBounds.profile_mul_outerCutoff (clock n x)
  rw [he]

theorem corrected_outer (clock : ℕ → D → ℝ) :
    (SignedWaveUpdate.coefficients a s d H T R
      (fun n x => mask n x * PrimaryCopyBounds.outerCutoff (clock n x))
      unit Ndot A j).corrected s d (fun n x => GaussianTailFlat.profile (clock n x)) =
    (SignedWaveUpdate.coefficients a s d H T R mask unit Ndot A j).corrected s d
      (fun n x => GaussianTailFlat.profile (clock n x)) := by
  simp only [WaveCoefficients.corrected, coefficients_outer]

end Repartition

section Copies

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {K : Type}

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Equality of every actual localized copy is enough for equality of the
whole common coefficients.  Summability is not assumed here. -/
theorem common_eq_of_localized (f g : PeriodizedWaveBounds.CopyData D K)
    (hb : f.background = g.background) (he : ∀ k, f.localized k = g.localized k) :
    f.common = g.common := by
  have ha : f.common.amplitude = g.common.amplitude := by
    funext n x
    change (∑' k, (f.localized k).amplitude n x) = ∑' k, (g.localized k).amplitude n x
    exact tsum_congr fun k => congrArg (fun a : WaveCoefficients D => a.amplitude n x) (he k)
  have hp : f.common.pressure = g.common.pressure := by
    funext n x
    change (∑' k, (f.localized k).pressure n x) = ∑' k, (g.localized k).pressure n x
    exact tsum_congr fun k => congrArg (fun a : WaveCoefficients D => a.pressure n x) (he k)
  calc
    f.common = {f.background with amplitude := f.common.amplitude, pressure := f.common.pressure}
      := rfl
    _ = {g.background with amplitude := g.common.amplitude, pressure := g.common.pressure} := by rw
      [hb, ha, hp]
    _ = g.common := rfl

theorem commonCorrected_eq_of_localized (f g : PeriodizedWaveBounds.CopyData D K)
    (hb : f.background = g.background) (he : ∀ k, f.localized k = g.localized k)
    (s : StripData D) (d : GraphDirections D) :
    f.commonCorrected s d = g.commonCorrected s d := by
  unfold PeriodizedWaveBounds.CopyData.commonCorrected
  rw [common_eq_of_localized f g hb he]

end Copies

section Geometry

variable {D h : ℝ}
  (sys : PartitionedCovariance.SlotSystem D h ActualSignedGeometry.radialVector
    ActualSignedGeometry.temporalVector)

noncomputable def geometry (label : SlotColoring.Label) (gap : ℕ) : CommonCoverSolve.Geometry :=
  ActualSignedGeometry.slotGeometry sys ActualSignedGeometry.vectors_det label gap

/-- The carrier center is the midpoint of the physical slot, including
this copy's own lattice translation. -/
noncomputable def center (label : SlotColoring.Label) (k : Frequency) : Plane :=
  PartitionedCovariance.slotCenter h label + TorusAverages.latticePoint k

theorem center_eq_anchor (label : SlotColoring.Label) (gap : ℕ) (k : Frequency) :
    center (h := h) label k = PhysicalCopyBounds.nativeCenter (geometry sys label gap) k +
      sys.radius • ActualSignedGeometry.temporalVector := by
  change _ = (PartitionedCovariance.slotCenter h label - sys.radius •
    ActualSignedGeometry.temporalVector +
    TorusAverages.latticePoint k) + sys.radius • ActualSignedGeometry.temporalVector
  unfold center
  abel

theorem eta_basis (label : SlotColoring.Label) (gap : ℕ) (z : Plane) :
    PhysicalGraphBounds.etaCoordinate ((geometry sys label gap).basis z) =
      ChartScales.timeCoefficient h label.1 * z.2 := by
  rw [geometry, ActualSignedGeometry.slotGeometry_basis, map_add, map_smul, map_smul]
  change z.1 * PhysicalGraphBounds.etaCoordinate PhysicalGraphBounds.radialDirection +
    (ChartScales.timeCoefficient h label.1 * z.2) *
      PhysicalGraphBounds.etaCoordinate PhysicalGraphBounds.timeDirection = _
  rw [PhysicalGraphBounds.etaCoordinate_radial, PhysicalGraphBounds.etaCoordinate_time]
  ring

theorem eta_offset (label : SlotColoring.Label) (gap : ℕ) (k : Frequency) (Y : Plane) :
    PhysicalGraphBounds.etaCoordinate (CommonCoverSolve.coverPower gap Y - center (h := h) label k)
      =
      ChartScales.timeCoefficient h label.1 * ((geometry sys label gap).coordinates k Y).2 -
        sys.radius := by
  rw [center_eq_anchor sys label gap k, ← sub_sub, map_sub, map_smul]
  have he := PhysicalCopyBounds.native_offset (geometry sys label gap) k Y
  change CommonCoverSolve.coverPower gap Y - _ = _ at he
  rw [he, eta_basis]
  change _ - sys.radius * PhysicalGraphBounds.etaCoordinate PhysicalGraphBounds.timeDirection = _
  rw [PhysicalGraphBounds.etaCoordinate_time, mul_one]

/-- The physical `+ radius` convention recovers the native clock exactly;
using the lower endpoint as carrier center would count this shift twice. -/
theorem clock_eq_native (label : SlotColoring.Label) (gap : ℕ) (k : Frequency) (Y : Plane) :
    (PhysicalGraphBounds.etaCoordinate (CommonCoverSolve.coverPower gap Y - center (h := h) label
      k) + sys.radius) /
      ChartScales.timeCoefficient h label.1 = ((geometry sys label gap).coordinates k Y).2 := by
  rw [eta_offset]
  field_simp [(ChartScales.timeCoefficient_pos h label.1).ne'] ; ring

theorem width_on_core (label : SlotColoring.Label) (gap : ℕ) (k : Frequency) (Y : Plane)
    (hy : (geometry sys label gap).coordinates k Y ∈ (ActualSignedGeometry.clockWindow sys
      label.1).core) :
    |PhysicalGraphBounds.etaCoordinate (CommonCoverSolve.coverPower gap Y - center (h := h) label
      k)| ≤ sys.radius := by
  rw [eta_offset]
  have hci := ChartScales.timeCoefficient_pos h label.1
  have hv : 0 ≤ ((geometry sys label gap).coordinates k Y).2 ∧
      ((geometry sys label gap).coordinates k Y).2 ≤ ChartScales.slotLength sys.radius h label.1 :=
        hy.2
  have hb := mul_le_mul_of_nonneg_left hv.2 hci.le
  have he : ChartScales.timeCoefficient h label.1 * ChartScales.slotLength sys.radius h label.1 =
      2 * sys.radius := by
    unfold ChartScales.slotLength
    field_simp
  exact abs_le.mpr ⟨by nlinarith [mul_nonneg hci.le hv.1], by nlinarith⟩

noncomputable def nativeMask (label : SlotColoring.Label) (z : Plane) : ℝ :=
  PartitionedCovariance.cutoff sys.radius z.1 *
    PrimaryCopyBounds.outerCutoff (z.2 / ChartScales.slotLength sys.radius h label.1)

theorem nativeMask_smooth (label : SlotColoring.Label) : ContDiff ℝ ∞ (nativeMask sys label) :=
  ((SquaredPartition.gridMask_smooth sys.radius 0).comp contDiff_fst).mul
    (PrimaryCopyBounds.outerCutoff_smooth.comp (contDiff_snd.div_const _))

theorem nativeMask_support (label : SlotColoring.Label) :
    support (nativeMask sys label) ⊆ (ActualSignedGeometry.clockWindow sys label.1).core := by
  intro z hz
  have hn := mul_ne_zero_iff.mp hz
  have hu : z.1 ∈ Ioo (-sys.radius) sys.radius := by
    rw [← PartitionedCovariance.cutoff_support sys.radius_pos]
    exact hn.1
  have hv := PrimaryCopyBounds.outerCutoff_support
    (subset_tsupport PrimaryCopyBounds.outerCutoff hn.2)
  have hL : 0 < ChartScales.slotLength sys.radius h label.1 :=
    div_pos (mul_pos (by norm_num) sys.radius_pos) (ChartScales.timeCoefficient_pos _ _)
  have hv0 : 0 ≤ z.2 := by
    have he := (le_div_iff₀ hL).mp (show 0 ≤ z.2 / _ by linarith [hv.1])
    simpa only [zero_mul] using he
  have hv1 : z.2 ≤ ChartScales.slotLength sys.radius h label.1 :=
    (div_le_one hL).mp (by linarith [hv.2])
  exact ⟨⟨hu.1.le, hu.2.le⟩, hv0, hv1⟩

/-- The concrete compact native layout used to periodize the same signed
reference.  Its geometry is the existing selected slot geometry. -/
noncomputable def layout (hh : 0 ≤ h) (label : SlotColoring.Label) (hl : 4 ≤ label.1)
    (gap : ℕ) : ActualPeriodizedSignedRealization.Layout where
  geometry _ := geometry sys label gap
  window _ := ActualSignedGeometry.clockWindow sys label.1
  length _ := ChartScales.slotLength sys.radius h label.1
  length_pos _ := div_pos (mul_pos (by norm_num) sys.radius_pos) (ChartScales.timeCoefficient_pos _
    _)
  cutoff _ := nativeMask sys label
  cutoff_smooth _ := nativeMask_smooth sys label
  cutoff_support _ := nativeMask_support sys label
  injective _ := ActualSignedGeometry.clockWindow_injective sys ActualSignedGeometry.vectors_det hh
    hl gap

/-- The actual native carrier, retaining the individual lattice midpoint. -/
noncomputable def carrier (label : SlotColoring.Label) (k : Frequency)
    (p pz x0 : ℝ) (F G : PhysicalGraphBounds.Slow → ℝ) : PhysicalWaveSum.CarrierData where
  chart := 0
  center := center (h := h) label k
  angular := p
  axial := pz
  radial := x0
  F := F
  G := G

/-- Polar coordinates are used only as a chart for the actual Cartesian
lift; the free torus coordinate remains unchanged. -/
noncomputable def cylinderAt (a : ℝ) (chart : PolarCharts.Index) (x : LiftPoint) : Cylinder :=
  (((PolarCharts.chart a chart (PhysicalGraphBounds.liftXY x)).1,
    (PhysicalGraphBounds.liftZT x, x.2)),
      (PolarCharts.chart a chart (PhysicalGraphBounds.liftXY x)).2)

theorem slotMap_eq_native (label : SlotColoring.Label) (gap : ℕ) (k : Frequency)
    (a : ℝ) (chart : PolarCharts.Index) (x : LiftPoint) :
    PhysicalGraphBounds.slotMap (PolarCharts.chart a chart)
      (ChartScales.timeCoefficient h label.1) (center (h := h) label k) sys.radius
      (PhysicalWaveSum.upLift gap x) =
        ActualSignedGeometry.slotCoordinates (geometry sys label gap) k (cylinderAt a chart x) := by
  rw [PhysicalGraphBounds.slotMap_formula]
  change (((PolarCharts.chart a chart (PhysicalGraphBounds.liftXY x)).1, PhysicalGraphBounds.liftZT
    x),
    ((PolarCharts.chart a chart (PhysicalGraphBounds.liftXY x)).2,
      (PhysicalGraphBounds.etaCoordinate (CommonCoverSolve.coverPower gap x.2 - center label k) +
        sys.radius) /
        ChartScales.timeCoefficient h label.1)) = _
  rw [clock_eq_native]
  rfl

theorem carrier_phase_eq_native (label : SlotColoring.Label) (gap : ℕ) (k : Frequency)
    (p pz x0 : ℝ) (F G : PhysicalGraphBounds.Slow → ℝ)
    (a : ℝ) (chart : PolarCharts.Index) (x : LiftPoint) :
    ((carrier (h := h) label k p pz x0 F G).withChart chart).phase a h label.1 sys.radius
        (PhysicalWaveSum.upLift gap x) =
      PhaseCalculus.phase (ChartScales.epsilon h label.1) p pz x0 F G
        (ActualSignedGeometry.slotCoordinates (geometry sys label gap) k (cylinderAt a chart x)) :=
          by
  change PhaseCalculus.phase (ChartScales.epsilon h label.1) p pz x0 F G
    (PhysicalGraphBounds.slotMap (PolarCharts.chart a chart)
      (ChartScales.timeCoefficient h label.1) (center label k) sys.radius
        (PhysicalWaveSum.upLift gap x)) = _
  rw [slotMap_eq_native]

end Geometry

section ActualCopies

variable {D h : ℝ}
  (sys : PartitionedCovariance.SlotSystem D h ActualSignedGeometry.radialVector
    ActualSignedGeometry.temporalVector)
  (hh : 0 ≤ h) (label : SlotColoring.Label) (hl : 4 ≤ label.1) (gap : ℕ)
  {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (B : PhysicalSignedWave.PrimaryData U)
  {reference : ℕ} (V : B.Views reference)

noncomputable def dynamicCoefficients (request : ℕ → Cylinder → Vec2) (j : Fin 2) (k : Frequency) :
    WaveCoefficients Cylinder :=
  ActualPeriodizedSignedRealization.coefficientsWith B (layout sys hh label hl gap) V request j
    (ActualPeriodizedSignedRealization.sharedMask B V)
    (ActualPeriodizedSignedRealization.nativeUnit B (layout sys hh label hl gap) V j k)

/-- The raw mask carries only the slow cutoff.  The transverse mask and
Gaussian together form the final compact native cutoff. -/
noncomputable def dynamicCopyData (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    PeriodizedWaveBounds.CopyData Cylinder Frequency where
  background := (ActualPeriodizedSignedRealization.periodizedPrimary B (layout sys hh label hl
    gap)).viewBase
    V.background V.frequency (fun n => V.map n) reference
  amplitude n k := (dynamicCoefficients sys hh label hl gap B V request j k).amplitude n
  pressure n k := (dynamicCoefficients sys hh label hl gap B V request j k).pressure n
  cutoff n k x := PartitionedCovariance.cutoff sys.radius
    ((geometry sys label gap).coordinates k (V.map n x).1.2.2).1 *
      (layout sys hh label hl gap).nativeGaussian reference k (V.map n x).1.2.2
  source := fun _ _ => 0

theorem dynamic_localized_eq (request : ℕ → Cylinder → Vec2) (j : Fin 2) (k : Frequency) :
    (dynamicCopyData sys hh label hl gap B V request j).localized k =
      (ActualPeriodizedSignedRealization.copyData B (layout sys hh label hl gap) V request
        j).localized k := by
  have hm : ActualPeriodizedSignedRealization.copyMask B (layout sys hh label hl gap) V k =
      fun n x => ActualPeriodizedSignedRealization.sharedMask B V n x *
        nativeMask sys label ((geometry sys label gap).coordinates k (V.map n x).1.2.2) := rfl
  change ((dynamicCoefficients sys hh label hl gap B V request j k).withCutoff _) =
    ((ActualPeriodizedSignedRealization.nativeCoefficients B (layout sys hh label hl gap) V request
      j k).withCutoff _)
  unfold dynamicCoefficients ActualPeriodizedSignedRealization.nativeCoefficients
  rw [hm]
  unfold ActualPeriodizedSignedRealization.coefficientsWith
  rw [coefficients_repartition]
  congr 1
  funext n x
  change PartitionedCovariance.cutoff sys.radius
      ((geometry sys label gap).coordinates k (V.map n x).1.2.2).1 *
    GaussianTailFlat.profile (((geometry sys label gap).coordinates k (V.map n x).1.2.2).2 /
      ChartScales.slotLength sys.radius h label.1) =
    GaussianTailFlat.profile (((geometry sys label gap).coordinates k (V.map n x).1.2.2).2 /
      ChartScales.slotLength sys.radius h label.1) *
      (PartitionedCovariance.cutoff sys.radius
        ((geometry sys label gap).coordinates k (V.map n x).1.2.2).1 *
        PrimaryCopyBounds.outerCutoff (((geometry sys label gap).coordinates k (V.map n x).1.2.2).2
          /
          ChartScales.slotLength sys.radius h label.1))
  rw [mul_left_comm, PrimaryCopyBounds.profile_mul_outerCutoff]

theorem dynamic_common_eq (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    (dynamicCopyData sys hh label hl gap B V request j).common =
      (ActualPeriodizedSignedRealization.copyData B (layout sys hh label hl gap) V request
        j).common :=
  common_eq_of_localized _ _ rfl (dynamic_localized_eq sys hh label hl gap B V request j)

theorem dynamic_commonCorrected_eq (request : ℕ → Cylinder → Vec2) (j : Fin 2) :
    (dynamicCopyData sys hh label hl gap B V request j).commonCorrected V.strip V.directions =
      (ActualPeriodizedSignedRealization.views B (layout sys hh label hl gap) V).exactCoefficients
        request j := by
  rw [commonCorrected_eq_of_localized
    (dynamicCopyData sys hh label hl gap B V request j)
    (ActualPeriodizedSignedRealization.copyData B (layout sys hh label hl gap) V request j) rfl
    (dynamic_localized_eq sys hh label hl gap B V request j),
    ActualPeriodizedSignedRealization.commonCorrected_eq]

end ActualCopies

/-! ## Literal physical copies of the same signed reference data -/

/-- An actual active label, retaining the native slot label and its band
bound without selecting data for omitted labels. -/
structure NativeLabel (active : Set PhysicalWaveSum.BandLabel) where
  val : SlotColoring.Label
  property : 4 ≤ val.1
  mem : (⟨val, property⟩ : PhysicalWaveSum.BandLabel) ∈ active

instance {active : Set PhysicalWaveSum.BandLabel} :
    CoeOut (NativeLabel active) PhysicalWaveSum.BandLabel := ⟨fun L => ⟨L.val, L.property⟩⟩

/-- The same primary/view/state triple is stored only for actual active
labels. Omitted physical labels will be exactly zero. -/
structure SignedFamily (U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow) where
  active : Set PhysicalWaveSum.BandLabel
  primary : NativeLabel active → PhysicalSignedWave.PrimaryData U
  view : (L : NativeLabel active) → (primary L).Views L.val.1
  state : (L : NativeLabel active) → (view L).StateData
  column : NativeLabel active → Fin 2

noncomputable def positiveIndex (L : PhysicalWaveSum.BandLabel) : PhysicalWaveSum.WaveIndex 1 :=
  (L, ⟨1, by decide⟩)

noncomputable def cylinderZero (x : LiftPoint) : Cylinder :=
  ((PolarCharts.radius (PhysicalGraphBounds.liftXY x), (PhysicalGraphBounds.liftZT x, x.2)), 0)

/-- Rotation into Cartesian components using the actual Cartesian
coordinates.  No choice of angular branch appears in the amplitude. -/
noncomputable def rotateCoefficient (Y : Plane) (v : ComplexVector) : ComplexVector :=
  ![(Y.1 / PolarCharts.radius Y : ℝ) • v 0 - (Y.2 / PolarCharts.radius Y : ℝ) • v 1,
    (Y.2 / PolarCharts.radius Y : ℝ) • v 0 + (Y.1 / PolarCharts.radius Y : ℝ) • v 1,
    v 2]

theorem rotateCoefficient_zero (Y : Plane) : rotateCoefficient Y 0 = 0 := by
  ext i
  fin_cases i <;> simp [rotateCoefficient]


noncomputable def rotationMap (Y : Plane) : ComplexVector →L[ℝ] ComplexVector :=
  ContinuousLinearMap.pi ![
    (Y.1 / PolarCharts.radius Y) • ContinuousLinearMap.proj 0 -
      (Y.2 / PolarCharts.radius Y) • ContinuousLinearMap.proj 1,
    (Y.2 / PolarCharts.radius Y) • ContinuousLinearMap.proj 0 +
      (Y.1 / PolarCharts.radius Y) • ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 2]

theorem rotationMap_apply (Y : Plane) (v : ComplexVector) : rotationMap Y v = rotateCoefficient Y v
  := by
  ext i
  fin_cases i <;> simp [rotationMap, rotateCoefficient]

theorem rotateCoefficient_real_smul (Y : Plane) (c : ℝ) (v : ComplexVector) :
    rotateCoefficient Y (c • v) = c • rotateCoefficient Y v := by
  simpa only [rotationMap_apply] using (rotationMap Y).map_smul c v

theorem rotateCoefficient_complex_smul (Y : Plane) (c : ℂ) (v : ComplexVector) :
    rotateCoefficient Y (c • v) = c • rotateCoefficient Y v := by
  ext i
  fin_cases i <;> simp [rotateCoefficient, Complex.real_smul, Pi.smul_apply, smul_eq_mul] <;> ring

theorem rotateCoefficient_vectorMode (Y : Plane) (K : ℝ) (Phi : Cylinder → ℝ)
    (v : Cylinder → ComplexVector) (x : Cylinder) (i : Fin 3) :
    rotateCoefficient Y (HarmonicCalculus.vectorMode K Phi v x) i =
      rotateCoefficient Y (v x) i * HarmonicCalculus.carrier K Phi x := by
  fin_cases i <;> simp [rotateCoefficient, HarmonicCalculus.vectorMode, HarmonicCalculus.mode,
    Complex.real_smul] <;> ring

theorem chart_radius {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) {Y : Plane}
    (hY : Y ∈ PolarCharts.chartDomain a j) :
    (PolarCharts.chart a j Y).1 = PolarCharts.radius Y := by
  rw [PolarCharts.chart_eq_localChart ha j hY, PolarCharts.localChart_apply]

theorem chart_radius_pos {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) {Y : Plane}
    (hY : Y ∈ PolarCharts.chartDomain a j) : 0 < PolarCharts.radius Y := by
  have hp : 0 < (PolarCharts.rotate j Y).1 := lt_trans (by positivity : (0 : ℝ) < a / 4) hY
  simpa only [PolarCharts.radius_rotate] using PolarCharts.radius_pos_of_fst_pos hp

theorem rotateCoefficient_chart_re {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) {Y : Plane}
    (hY : Y ∈ PolarCharts.chartDomain a j) (v : ComplexVector) (i : Fin 3) :
    (rotateCoefficient Y v i).re =
      CylindricalResidual.frame (PolarCharts.chart a j Y).2 (PhysicalCurlCovariance.realVector v) i
        := by
  have hc := congrArg Prod.fst (PolarCharts.polar_chart ha j hY)
  have hs := congrArg Prod.snd (PolarCharts.polar_chart ha j hY)
  simp only [PolarCharts.polar, chart_radius ha j hY] at hc hs
  have hr := (chart_radius_pos ha j hY).ne'
  have hcos : Y.1 / PolarCharts.radius Y = Real.cos (PolarCharts.chart a j Y).2 := by
    rw [← hc]
    field_simp
  have hsin : Y.2 / PolarCharts.radius Y = Real.sin (PolarCharts.chart a j Y).2 := by
    rw [← hs]
    field_simp
  fin_cases i <;> simp [rotateCoefficient, hcos, hsin, CylindricalResidual.frame_apply,
    PhysicalCurlCovariance.realVector, AxisymmetricResidual.pack, coordinateVector,
    -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem cylinderAt_fst {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) {x : LiftPoint}
    (hx : PhysicalGraphBounds.liftXY x ∈ PolarCharts.chartDomain a j) :
    (cylinderAt a j x).1 = (cylinderZero x).1 := by
  simp only [cylinderAt, cylinderZero, chart_radius ha j hx]


theorem radiusPower_eq_radius (d : ℝ) (Y : Plane) :
    PhysicalGraphBounds.radiusPower d Y = PolarCharts.radius Y ^ d := by
  unfold PhysicalGraphBounds.radiusPower PolarCharts.radius
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ Y.1 ^ 2 + Y.2 ^ 2)]
  congr 1
  ring

theorem scaledRadial_forward (n : ℕ) (z : SpaceTime) :
    PhysicalGraphBounds.scaledRadial n (z.1, CylindricalResidual.chart z.2) =
      PolarCharts.polar (ChartScales.Q n ^ (-(1 / 2 : ℝ)) * z.2 0, z.2 1) := by
  ext <;> simp [PhysicalGraphBounds.scaledRadial, PhysicalGraphBounds.radialProjection_apply,
    CylindricalResidual.chart, PolarCharts.polar, AxisymmetricResidual.pack, coordinateVector] <;>
      ring

/-- The exact physical Cartesian lift and the common cylindrical graph
have identical coordinates; in particular no fast variable is discarded. -/
theorem cylinderAt_physical_forward (h : ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) (z : SpaceTime) (hr : 0 < z.2 0)
    (hangle : z.2 1 - PolarCharts.offset j ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hchart : PhysicalGraphBounds.scaledRadial n (z.1, CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain a j) :
    cylinderAt a j (PhysicalGraphBounds.physicalLift h n (z.1, CylindricalResidual.chart z.2)) =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (ChartScales.nativeIndex h n)).map z
        := by
  have hQ := ChartScales.Q_pos n
  have hR : 0 < ChartScales.Q n ^ (-(1 / 2 : ℝ)) * z.2 0 :=
    mul_pos (Real.rpow_pos_of_pos hQ _) hr
  have hp : PolarCharts.chart a j
      (PhysicalGraphBounds.scaledRadial n (z.1, CylindricalResidual.chart z.2)) =
      (ChartScales.Q n ^ (-(1 / 2 : ℝ)) * z.2 0, z.2 1) := by
    rw [scaledRadial_forward] at hchart ⊢
    exact PolarCharts.chart_polar ha j hR hangle hchart
  have hax : ChartScales.Q n ^ (-(1 / 2 : ℝ)) * ChartScales.Q n ^ h =
      ChartScales.Q n ^ (-CoordinateAlgebra.D h) := by
    rw [← Real.rpow_add hQ]
    congr 1
    unfold CoordinateAlgebra.D
    ring
  have ht : ChartScales.Q n ^ (-CoordinateAlgebra.A h) *
      ChartScales.Q n ^ (-(1 / 2 : ℝ)) * ChartScales.Q n ^ h = ChartScales.Q n ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hQ, ← Real.rpow_add hQ]
    congr 1
    unfold CoordinateAlgebra.A
    ring
  have hf : ChartScales.Q n ^ (-CoordinateAlgebra.A h) *
      ChartScales.Q n ^ (-(1 / 2 : ℝ)) *
        (ChartScales.Tg ^ ChartScales.nativeIndex h n * ChartScales.Q n ^ (1 + h)) =
        ChartScales.Tg ^ ChartScales.nativeIndex h n := by
    calc
      _ = ChartScales.Tg ^ ChartScales.nativeIndex h n *
        (ChartScales.Q n ^ (-CoordinateAlgebra.A h) * ChartScales.Q n ^ (-(1 / 2 : ℝ)) *
          ChartScales.Q n ^ (1 + h)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hQ, ← Real.rpow_add hQ,
          show -CoordinateAlgebra.A h + -(1 / 2 : ℝ) + (1 + h) = 0 by unfold CoordinateAlgebra.A;
            ring,
          Real.rpow_zero, mul_one]
  have hn := PhysicalGraphBounds.nativeGraph_normalized h n (z.1, CylindricalResidual.chart z.2)
  rw [PhysicalGraphBounds.radialProfile, radiusPower_eq_radius, scaledRadial_forward,
    PolarCharts.radius_polar, abs_of_pos hR] at hn
  have hc : cylinderAt a j (PhysicalGraphBounds.physicalLift h n (z.1, CylindricalResidual.chart
    z.2)) =
      ((ChartScales.Q n ^ (-(1 / 2 : ℝ)) * z.2 0,
        ((ChartScales.Q n ^ (-CoordinateAlgebra.D h) * z.2 2,
          ChartScales.Q n ^ (-1 : ℝ) * (1 - z.1)),
          PhysicalGraphBounds.nativeGraph h n (z.1, CylindricalResidual.chart z.2))), z.2 1) := by
    unfold cylinderAt
    rw [PhysicalGraphBounds.liftXY_physicalLift, hp]
    ext <;> simp [PhysicalGraphBounds.liftZT, PhysicalGraphBounds.physicalLift,
      PhysicalGraphBounds.physicalChart, PhysicalGraphBounds.chartLinear_apply,
      CylindricalResidual.chart, AxisymmetricResidual.pack, coordinateVector]
    ring
  rw [hc, hn]
  simp only [PhysicalResidualBridge.ScaledGraph.map, PhysicalResidualBridge.commonGraph,
    hax, ht, hf, ChartScales.radialCoefficient, smul_smul]

section PhysicalFamilies

variable {D h : ℝ}
  (sys : PartitionedCovariance.SlotSystem D h ActualSignedGeometry.radialVector
    ActualSignedGeometry.temporalVector)
  (hh : 0 ≤ h) {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (f : SignedFamily U)

noncomputable def waveMask (label : SlotColoring.Label) (z : Plane) : ℝ :=
  PartitionedCovariance.cutoff sys.radius z.1 *
    GaussianTailFlat.profile (z.2 / ChartScales.slotLength sys.radius h label.1)

theorem waveMask_eq_compact (label : SlotColoring.Label) (z : Plane) :
    waveMask sys label z = nativeMask sys label z *
      GaussianTailFlat.profile (z.2 / ChartScales.slotLength sys.radius h label.1) := by
  unfold waveMask nativeMask
  calc
    _ = PartitionedCovariance.cutoff sys.radius z.1 *
        (GaussianTailFlat.profile (z.2 / ChartScales.slotLength sys.radius h label.1) *
          PrimaryCopyBounds.outerCutoff (z.2 / ChartScales.slotLength sys.radius h label.1)) := by
      rw [PrimaryCopyBounds.profile_mul_outerCutoff]
    _ = _ := by ring

theorem waveMask_support (label : SlotColoring.Label) :
    support (waveMask sys label) ⊆ (ActualSignedGeometry.clockWindow sys label.1).core := by
  intro z hz
  apply nativeMask_support sys label
  intro hn
  exact hz (by rw [waveMask_eq_compact, hn, zero_mul])

noncomputable def selectedCarrier (L : NativeLabel f.active) (k : Frequency) :
    PhysicalWaveSum.CarrierData :=
  carrier (h := h) L.val k
    (((f.primary L).pulse (f.column L)).phase.p L.val.1)
    (((f.primary L).pulse (f.column L)).phase.pz L.val.1)
    (((f.primary L).pulse (f.column L)).phase.x0 L.val.1)
    (((f.primary L).pulse (f.column L)).phase.F L.val.1)
    (((f.primary L).pulse (f.column L)).phase.G L.val.1)

noncomputable def extendedCarrier (L : PhysicalWaveSum.BandLabel) (k : Frequency) :
    PhysicalWaveSum.CarrierData :=
  if hL : L ∈ f.active then
    selectedCarrier (h := h) f ⟨L.val, L.property, hL⟩ k
  else carrier (h := h) L.val k 0 0 0 (fun _ => 0) (fun _ => 0)

theorem extendedCarrier_active (L : NativeLabel f.active) (k : Frequency) :
    extendedCarrier (h := h) f L k = selectedCarrier (h := h) f L k := by
  simp only [extendedCarrier, dite_eq_left L.mem]

theorem extendedCarrier_center (L : PhysicalWaveSum.BandLabel) (k : Frequency) :
    (extendedCarrier (h := h) f L k).center = center (h := h) L.val k := by
  unfold extendedCarrier
  split_ifs <;> rfl

noncomputable def rawSignedAmplitude (L : NativeLabel f.active) (k : Frequency) (x : Cylinder) :
    ComplexVector :=
  ActualPeriodizedSignedRealization.referenceScalar (f.primary L) (f.state L).referenceRequest
    (f.column L) L.val.1 x • CurlClassBounds.complexify
      (ActualPeriodizedSignedRealization.referenceNativeUnit (f.primary L)
        (layout sys hh L.val L.property 0) (f.column L) L.val.1 k x)

noncomputable def rawPotential (L : NativeLabel f.active) (k : Frequency) (x : Cylinder) :
    ComplexVector :=
  CurlClassBounds.inverseCarrier ((f.primary L).base.frequency L.val.1) •
    CurlClassBounds.normalCoefficient
      ((f.primary L).base.normal (f.primary L).strip (f.primary L).directions L.val.1 x)
      (rawSignedAmplitude sys hh f L k x)

noncomputable def rawPressure (L : NativeLabel f.active) (k : Frequency) (x : Cylinder) : ℂ :=
  ActualPeriodizedSignedRealization.referenceScalar (f.primary L) (f.state L).referenceRequest
    (f.column L) L.val.1 x •
      ActualPeriodizedSignedRealization.homogeneousPressure ((f.primary L).base.frequency L.val.1)
        ((f.primary L).base.normal (f.primary L).strip (f.primary L).directions L.val.1 x)
        ((f.primary L).normalMotion L.val.1 x) ((f.primary L).action L.val.1 x)
        (ActualPeriodizedSignedRealization.referenceNativeUnit (f.primary L)
          (layout sys hh L.val L.property 0) (f.column L) L.val.1 k x)

/-- One positive harmonic suffices because the physical field takes the
real part.  Its native copies retain their individual centers and phases. -/
noncomputable def potentialFamily (i : Fin 3) : PhysicalCopyBounds.CopyFamily 1 Frequency where
  gap _ := 0
  carrier k L := extendedCarrier (h := h) f L k
  amplitude k I x := if hL : I.1 ∈ f.active then
    if I.2.val = 1 then
    ((ChartScales.Q I.1.val.1 ^ (-h) : ℝ) : ℂ) *
      (waveMask sys I.1.val ((geometry sys I.1.val 0).coordinates k x.2) : ℂ) *
      rotateCoefficient (PhysicalGraphBounds.liftXY x)
        (rawPotential sys hh f ⟨I.1.val, I.1.property, hL⟩ k (cylinderZero x)) i
    else 0
  else 0

noncomputable def pressureFamily : PhysicalCopyBounds.CopyFamily 1 Frequency where
  gap _ := 0
  carrier k L := extendedCarrier (h := h) f L k
  amplitude k I x := if hL : I.1 ∈ f.active then
    if I.2.val = 1 then
    ((ChartScales.Q I.1.val.1 ^ (-(2 * CoordinateAlgebra.A h)) : ℝ) : ℂ) *
      (waveMask sys I.1.val ((geometry sys I.1.val 0).coordinates k x.2) : ℂ) *
      rawPressure sys hh f ⟨I.1.val, I.1.property, hL⟩ k (cylinderZero x)
    else 0
  else 0

theorem potential_term_active (L : NativeLabel f.active) (k : Frequency) (i : Fin 3)
    (a : ℝ) (w : SpaceTime) :
    (potentialFamily sys hh f i).term a h sys.radius (positiveIndex L) k w =
      PhysicalWaveSum.globalWave a h L.val.1 0 sys.radius (selectedCarrier (h := h) f L k)
        ((potentialFamily sys hh f i).amplitude k (positiveIndex L)) 1 w := by
  change PhysicalWaveSum.globalWave _ _ _ _ _ (extendedCarrier (h := h) f L k) _ _ _ = _
  rw [extendedCarrier_active]
  rfl

theorem pressure_term_active (L : NativeLabel f.active) (k : Frequency)
    (a : ℝ) (w : SpaceTime) :
    (pressureFamily sys hh f).term a h sys.radius (positiveIndex L) k w =
      PhysicalWaveSum.globalWave a h L.val.1 0 sys.radius (selectedCarrier (h := h) f L k)
        ((pressureFamily sys hh f).amplitude k (positiveIndex L)) 1 w := by
  change PhysicalWaveSum.globalWave _ _ _ _ _ (extendedCarrier (h := h) f L k) _ _ _ = _
  rw [extendedCarrier_active]
  rfl

theorem potential_amplitude_mem (i : Fin 3) (k : Frequency)
    (I : PhysicalWaveSum.WaveIndex 1) (x : LiftPoint)
    (hx : (potentialFamily sys hh f i).amplitude k I x ≠ 0) :
    (geometry sys I.1.val 0).coordinates k x.2 ∈ (ActualSignedGeometry.clockWindow sys
      I.1.val.1).core := by
  by_cases hL : I.1 ∈ f.active
  · apply waveMask_support sys I.1.val
    intro hz
    apply hx
    simp only [potentialFamily, dite_eq_left hL, hz, Complex.ofReal_zero, mul_zero, zero_mul,
      ite_self]
  · exact False.elim (hx (by simp [potentialFamily, hL]))

theorem pressure_amplitude_mem (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1) (x : LiftPoint)
    (hx : (pressureFamily sys hh f).amplitude k I x ≠ 0) :
    (geometry sys I.1.val 0).coordinates k x.2 ∈ (ActualSignedGeometry.clockWindow sys
      I.1.val.1).core := by
  by_cases hL : I.1 ∈ f.active
  · apply waveMask_support sys I.1.val
    intro hz
    apply hx
    simp only [pressureFamily, dite_eq_left hL, hz, Complex.ofReal_zero, mul_zero, zero_mul,
      ite_self]
  · exact False.elim (hx (by simp [pressureFamily, hL]))

noncomputable def potentialCells (i : Fin 3) : PhysicalCopyBounds.SupportCells (potentialFamily sys
  hh f i) :=
  PhysicalCopyBounds.nativeSupportCells
    (fun L => geometry sys L.val 0) (fun L => (ActualSignedGeometry.clockWindow sys L.val.1).core)
    (fun L => (ActualSignedGeometry.clockWindow sys L.val.1).core_compact)
    (fun L => (ActualSignedGeometry.clockWindow_injective sys ActualSignedGeometry.vectors_det hh
      L.property 0).mono
      (Set.image_mono (ActualSignedGeometry.clockWindow sys L.val.1).core_subset_outer))
    (potential_amplitude_mem sys hh f i)

noncomputable def pressureCells : PhysicalCopyBounds.SupportCells (pressureFamily sys hh f) :=
  PhysicalCopyBounds.nativeSupportCells
    (fun L => geometry sys L.val 0) (fun L => (ActualSignedGeometry.clockWindow sys L.val.1).core)
    (fun L => (ActualSignedGeometry.clockWindow sys L.val.1).core_compact)
    (fun L => (ActualSignedGeometry.clockWindow_injective sys ActualSignedGeometry.vectors_det hh
      L.property 0).mono
      (Set.image_mono (ActualSignedGeometry.clockWindow sys L.val.1).core_subset_outer))
    (pressure_amplitude_mem sys hh f)


/-- Finite native support justifies applying any linear potential operation
before or after the copy sum. -/
theorem waveMask_summable_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : PhysicalWaveSum.BandLabel) (Y : Plane) (v : Frequency → E) :
    Summable (fun k => waveMask sys L.val ((geometry sys L.val 0).coordinates k Y) • v k) := by
  obtain ⟨J, hJ⟩ := (geometry sys L.val 0).finite_copy_cutoffs
    (HasCompactSupport.of_support_subset_isCompact
      (ActualSignedGeometry.clockWindow sys L.val.1).core_compact (nativeMask_support sys L.val))
        ‖Y‖
  apply summable_of_ne_finset_zero (s := J)
  intro k hk
  have hz : nativeMask sys L.val ((geometry sys L.val 0).coordinates k Y) = 0 := hJ Y le_rfl k hk
  rw [waveMask_eq_compact, hz, zero_mul, zero_smul]

theorem signed_raw_eq_sum (L : NativeLabel f.active) (x : Cylinder) :
    (ActualPeriodizedSignedRealization.periodizedPrimary (f.primary L)
      (layout sys hh L.val L.property 0)).raw (f.state L).referenceRequest (f.column L) L.val.1 x =
      ∑' k, waveMask sys L.val ((geometry sys L.val 0).coordinates k x.1.2.2) •
        rawSignedAmplitude sys hh f L k x := by
  rw [ActualPeriodizedSignedRealization.reference_raw_eq_sum]
  apply tsum_congr
  intro k
  rw [waveMask_eq_compact, mul_smul]
  rfl

noncomputable def potentialMap (K : ℝ) (N : Space) : ComplexVector →L[ℝ] ComplexVector :=
  CurlClassBounds.inverseCarrier K •
    ((‖N‖ ^ 2)⁻¹ • CurlClassBounds.complexCrossLinear (CurlClassBounds.complexify N))

theorem potentialMap_apply (K : ℝ) (N : Space) (v : ComplexVector) :
    potentialMap K N v = CurlClassBounds.inverseCarrier K • CurlClassBounds.normalCoefficient N v
      := rfl

theorem signed_potential_eq_sum (L : NativeLabel f.active) (x : Cylinder) :
    CurlClassBounds.inverseCarrier ((f.primary L).base.frequency L.val.1) •
      CurlClassBounds.normalCoefficient
        ((f.primary L).base.normal (f.primary L).strip (f.primary L).directions L.val.1 x)
        ((ActualPeriodizedSignedRealization.periodizedPrimary (f.primary L)
          (layout sys hh L.val L.property 0)).raw (f.state L).referenceRequest (f.column L) L.val.1
            x) =
      ∑' k, waveMask sys L.val ((geometry sys L.val 0).coordinates k x.1.2.2) •
        rawPotential sys hh f L k x := by
  change potentialMap _ _ _ = _
  rw [signed_raw_eq_sum]
  rw [ContinuousLinearMap.map_tsum _ (waveMask_summable_smul sys L x.1.2.2 _)]
  apply tsum_congr
  intro k
  rw [map_smul]
  rfl

theorem signed_pressure_eq_sum (L : NativeLabel f.active) (x : Cylinder) :
    (ActualPeriodizedSignedRealization.periodizedPrimary (f.primary L)
      (layout sys hh L.val L.property 0)).rawPressure (f.state L).referenceRequest (f.column L)
        L.val.1 x =
      ∑' k, waveMask sys L.val ((geometry sys L.val 0).coordinates k x.1.2.2) •
        rawPressure sys hh f L k x := by
  let l := layout sys hh L.val L.property 0
  let B := f.primary L
  let v := (ActualPeriodizedSignedRealization.periodizedPrimary B l).fundamental (f.column L)
    L.val.1 x
  have hs : SignedWaveUpdate.signedScalar (ActualPeriodizedSignedRealization.periodizedPrimary B
    l).strip
      (ActualPeriodizedSignedRealization.periodizedPrimary B l).matrix
      (ActualPeriodizedSignedRealization.periodizedPrimary B l).target (f.state L).referenceRequest
      (ActualPeriodizedSignedRealization.periodizedPrimary B l).mask (f.column L) L.val.1 x =
      l.mask L.val.1 x.1.2.2 * ActualPeriodizedSignedRealization.referenceScalar B
        (f.state L).referenceRequest (f.column L) L.val.1 x :=
    ActualPeriodizedSignedRealization.signedScalar_mul_mask _ _ _ _ _ _ _ _ _
  change l.gaussian L.val.1 x.1.2.2 •
    ((ActualPeriodizedSignedRealization.periodizedPrimary B l).coefficients
      (f.state L).referenceRequest (f.column L)).pressure L.val.1 x = _
  rw [PhysicalSignedWave.PrimaryData.coefficients,
    ActualPeriodizedSignedRealization.coefficients_pressure_at, hs, mul_smul]
  rw [← l.gaussian_mask_sum]
  apply tsum_congr
  intro k
  by_cases hk : l.nativeMask L.val.1 k x.1.2.2 = 0
  · have hk' : nativeMask sys L.val ((geometry sys L.val 0).coordinates k x.1.2.2) = 0 := hk
    simp only [hk, zero_smul, smul_zero, waveMask_eq_compact, hk', zero_mul]
  · rw [ActualPeriodizedSignedRealization.referenceUnit_eq_native B l _ _ _ _ hk]
    rw [waveMask_eq_compact, mul_smul, smul_comm]
    rfl


/-- Primitive reference identities.  The selected phase is the actual
periodic clock phase; all geometric and angular statements concern the
uncorrected inputs, never the output potential or velocity. -/
structure ReferenceGeometry where
  frequency : ∀ L, (f.primary L).base.frequency L.val.1 = (ChartScales.carrier h L.val.1 : ℝ)
  phase : ∀ L, (f.primary L).base.phase L.val.1 =
    ActualSignedGeometry.periodicPhase sys L.val 0 (ChartScales.epsilon h L.val.1)
      (((f.primary L).pulse (f.column L)).phase.p L.val.1)
      (((f.primary L).pulse (f.column L)).phase.pz L.val.1)
      (((f.primary L).pulse (f.column L)).phase.x0 L.val.1)
      (((f.primary L).pulse (f.column L)).phase.F L.val.1)
      (((f.primary L).pulse (f.column L)).phase.G L.val.1)
  angular : ∀ L, (f.primary L).Angular (f.state L).referenceRequest L.val.1
  chart : ∀ L, PhysicalSignedWave.ChartGeometry (f.primary L).base (f.primary L).strip
    (f.primary L).directions L.val.1 h (ChartScales.Q L.val.1) (ChartScales.nativeIndex h L.val.1)
  exponent : ∀ L, (f.view L).exponent = h
  scale : ∀ L, (f.view L).referenceScale = ChartScales.Q L.val.1
  cover : ∀ L, (f.view L).referenceCover = ChartScales.nativeIndex h L.val.1

variable (G : ReferenceGeometry sys f)

include G hh

theorem rawSignedAmplitude_invariant (L : NativeLabel f.active) (k : Frequency) :
    CopyAngularInvariance.Invariant ((0, 1) : Cylinder) (rawSignedAmplitude sys hh f L k) := by
  intro x t
  have hm : (f.primary L).matrix L.val.1 (x + t • (0, 1)) = (f.primary L).matrix L.val.1 x := by
    simp only [PhysicalSignedWave.PrimaryData.matrix, SignedWaveUpdate.phaseMatrix,
      PrimaryPulseBounds.chartCovariance, (G.angular L).coordinate x t]
  simp only [rawSignedAmplitude, ActualPeriodizedSignedRealization.referenceScalar,
    SignedWaveUpdate.signedScalar, hm, (G.angular L).target x t, (G.angular L).request x t,
    (G.angular L).mask x t, ActualPeriodizedSignedRealization.referenceNativeUnit,
    (G.angular L).coordinate x t, Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]

theorem rawPotential_invariant (L : NativeLabel f.active) (k : Frequency) :
    CopyAngularInvariance.Invariant ((0, 1) : Cylinder) (rawPotential sys hh f L k) := by
  intro x t
  simp only [rawPotential, (rawSignedAmplitude_invariant sys hh f G L k) x t,
    (G.chart L).normal_invariant (G.angular L).phase x t]

theorem rawPressure_invariant (L : NativeLabel f.active) (k : Frequency) :
    CopyAngularInvariance.Invariant ((0, 1) : Cylinder) (rawPressure sys hh f L k) := by
  intro x t
  have hm : (f.primary L).matrix L.val.1 (x + t • (0, 1)) = (f.primary L).matrix L.val.1 x := by
    simp only [PhysicalSignedWave.PrimaryData.matrix, SignedWaveUpdate.phaseMatrix,
      PrimaryPulseBounds.chartCovariance, (G.angular L).coordinate x t]
  simp only [rawPressure, ActualPeriodizedSignedRealization.referenceScalar,
    SignedWaveUpdate.signedScalar, hm, (G.angular L).target x t, (G.angular L).request x t,
    (G.angular L).mask x t, ActualPeriodizedSignedRealization.referenceNativeUnit,
    (G.angular L).coordinate x t, Prod.fst_add, Prod.smul_fst, smul_zero, add_zero,
    (G.chart L).normal_invariant (G.angular L).phase x t,
    (G.angular L).normalMotion x t, (G.angular L).action x t]

omit sys hh f G in
theorem invariant_angle_zero {E : Type} (F : Cylinder → E)
    (hF : CopyAngularInvariance.Invariant ((0, 1) : Cylinder) F) (x : Cylinder) :
    F x = F (x.1, 0) := by
  have he : (x.1, (0 : ℝ)) + x.2 • ((0, 1) : Cylinder) = x := by
    ext <;> simp
  simpa only [he] using hF (x.1, 0) x.2

theorem phase_eq_native (L : NativeLabel f.active) (k : Frequency)
    (a : ℝ) (chart : PolarCharts.Index) (x : LiftPoint)
    (hx : (geometry sys L.val 0).coordinates k x.2 ∈ (ActualSignedGeometry.clockWindow sys
      L.val.1).core) :
    (f.primary L).base.phase L.val.1 (cylinderAt a chart x) =
      ((selectedCarrier (h := h) f L k).withChart chart).phase a h L.val.1 sys.radius x := by
  rw [G.phase L]
  have he := (ActualSignedGeometry.periodicPhase_germ sys hh L.property 0
    (ChartScales.epsilon h L.val.1)
    (((f.primary L).pulse (f.column L)).phase.p L.val.1)
    (((f.primary L).pulse (f.column L)).phase.pz L.val.1)
    (((f.primary L).pulse (f.column L)).phase.x0 L.val.1)
    (((f.primary L).pulse (f.column L)).phase.F L.val.1)
    (((f.primary L).pulse (f.column L)).phase.G L.val.1) k (x := cylinderAt a chart x)
      hx).eq_of_nhds
  exact he.trans (carrier_phase_eq_native sys L.val 0 k
    (((f.primary L).pulse (f.column L)).phase.p L.val.1)
    (((f.primary L).pulse (f.column L)).phase.pz L.val.1)
    (((f.primary L).pulse (f.column L)).phase.x0 L.val.1)
    (((f.primary L).pulse (f.column L)).phase.F L.val.1)
    (((f.primary L).pulse (f.column L)).phase.G L.val.1) a chart x).symm


omit sys hh f G in
theorem commonLift_zero (h : ℝ) (n : ℕ) (w : SpaceTime) :
    PhysicalWaveSum.commonLift h n 0 w = PhysicalGraphBounds.physicalLift h n w := by
  simp [PhysicalWaveSum.commonLift, CommonCoverSolve.coverPower]

theorem rawPotential_cylinderAt (L : NativeLabel f.active) (k : Frequency)
    {a : ℝ} (ha : 0 < a) (chart : PolarCharts.Index) {x : LiftPoint}
    (hx : PhysicalGraphBounds.liftXY x ∈ PolarCharts.chartDomain a chart) :
    rawPotential sys hh f L k (cylinderAt a chart x) = rawPotential sys hh f L k (cylinderZero x)
      := by
  rw [invariant_angle_zero _ (rawPotential_invariant sys hh f G L k), cylinderAt_fst ha chart hx]
  rfl

theorem rawPressure_cylinderAt (L : NativeLabel f.active) (k : Frequency)
    {a : ℝ} (ha : 0 < a) (chart : PolarCharts.Index) {x : LiftPoint}
    (hx : PhysicalGraphBounds.liftXY x ∈ PolarCharts.chartDomain a chart) :
    rawPressure sys hh f L k (cylinderAt a chart x) = rawPressure sys hh f L k (cylinderZero x) :=
      by
  rw [invariant_angle_zero _ (rawPressure_invariant sys hh f G L k), cylinderAt_fst ha chart hx]
  rfl

/-- The local oscillatory pressure is the native pressure with its actual
copy phase.  Equality with the common periodic phase is used only where
this copy's cutoff is nonzero. -/
theorem pressure_commonWave (L : NativeLabel f.active) (k : Frequency)
    {a : ℝ} (ha : 0 < a) (chart : PolarCharts.Index) (w : SpaceTime)
    (hchart : PhysicalGraphBounds.scaledRadial L.val.1 w ∈ PolarCharts.chartDomain a chart) :
    PhysicalWaveSum.commonWave a h L.val.1 0 sys.radius
      ((selectedCarrier (h := h) f L k).withChart chart)
      ((pressureFamily sys hh f).amplitude k (positiveIndex L)) 1 w =
      (ChartScales.Q L.val.1 ^ (-(2 * CoordinateAlgebra.A h)) : ℝ) •
        (waveMask sys L.val ((geometry sys L.val 0).coordinates k
          (PhysicalGraphBounds.physicalLift h L.val.1 w).2) •
          rawPressure sys hh f L k (cylinderAt a chart (PhysicalGraphBounds.physicalLift h L.val.1
            w))) *
        HarmonicCalculus.carrier ((f.primary L).base.frequency L.val.1)
          ((f.primary L).base.phase L.val.1)
          (cylinderAt a chart (PhysicalGraphBounds.physicalLift h L.val.1 w)) := by
  have hc : PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h L.val.1 w) ∈
      PolarCharts.chartDomain a chart := by
    simpa only [PhysicalGraphBounds.liftXY_physicalLift] using hchart
  simp only [PhysicalWaveSum.commonWave, commonLift_zero, pressureFamily, positiveIndex,
    dite_eq_left L.mem, Int.cast_one, mul_one, ite_true]
  rw [← rawPressure_cylinderAt sys hh f G L k ha chart hc]
  by_cases hz : waveMask sys L.val ((geometry sys L.val 0).coordinates k
      (PhysicalGraphBounds.physicalLift h L.val.1 w).2) = 0
  · simp [hz]
  · rw [← phase_eq_native sys hh f G L k a chart _ (waveMask_support sys L.val hz), G.frequency L]
    simp only [PhysicalGraphBounds.character, HarmonicCalculus.carrier,
      HarmonicCalculus.phaseFactor, PhysicalGraphBounds.phaseFactor, Complex.real_smul]
    congr 1
    ring

/-- The complete copy sum is exactly the same reference pressure mode. -/
theorem pressure_periodized (L : NativeLabel f.active) {a b : ℝ} (ha : 0 < a)
    (w : SpaceTime) (hw : PhysicalGraphBounds.scaledRadial L.val.1 w ∈ PhysicalGraphBounds.annulus
      a b) :
    (pressureFamily sys hh f).periodized a h sys.radius (positiveIndex L) w =
      (ChartScales.Q L.val.1 ^ (-(2 * CoordinateAlgebra.A h)) : ℝ) •
        HarmonicCalculus.mode ((f.primary L).base.frequency L.val.1)
          ((f.primary L).base.phase L.val.1)
          ((ActualPeriodizedSignedRealization.periodizedPrimary (f.primary L)
            (layout sys hh L.val L.property 0)).rawPressure (f.state L).referenceRequest (f.column
              L) L.val.1)
          (cylinderAt a (PhysicalWaveSum.chooseChart a (PhysicalGraphBounds.scaledRadial L.val.1 w))
            (PhysicalGraphBounds.physicalLift h L.val.1 w)) := by
  have hc := PhysicalWaveSum.chooseChart_valid ha hw
  unfold PhysicalCopyBounds.CopyFamily.periodized
  simp_rw [pressure_term_active]
  change (∑' k, PhysicalWaveSum.commonWave a h L.val.1 0 sys.radius
    ((selectedCarrier (h := h) f L k).withChart
      (PhysicalWaveSum.chooseChart a (PhysicalGraphBounds.scaledRadial L.val.1 w)))
    ((pressureFamily sys hh f).amplitude k (positiveIndex L)) 1 w) = _
  simp_rw [pressure_commonWave sys hh f G L _ ha _ w hc]
  rw [tsum_mul_right, tsum_const_smul'']
  rw [HarmonicCalculus.mode, signed_pressure_eq_sum sys hh f L]
  exact smul_mul_assoc _ _ _


theorem potential_commonWave (L : NativeLabel f.active) (k : Frequency) (i : Fin 3)
    {a : ℝ} (ha : 0 < a) (chart : PolarCharts.Index) (w : SpaceTime)
    (hchart : PhysicalGraphBounds.scaledRadial L.val.1 w ∈ PolarCharts.chartDomain a chart) :
    PhysicalWaveSum.commonWave a h L.val.1 0 sys.radius
      ((selectedCarrier (h := h) f L k).withChart chart)
      ((potentialFamily sys hh f i).amplitude k (positiveIndex L)) 1 w =
      (ChartScales.Q L.val.1 ^ (-h) : ℝ) •
        (waveMask sys L.val ((geometry sys L.val 0).coordinates k
          (PhysicalGraphBounds.physicalLift h L.val.1 w).2) •
          rotateCoefficient (PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h L.val.1
            w))
            (rawPotential sys hh f L k (cylinderAt a chart (PhysicalGraphBounds.physicalLift h
              L.val.1 w))) i) *
        HarmonicCalculus.carrier ((f.primary L).base.frequency L.val.1)
          ((f.primary L).base.phase L.val.1)
          (cylinderAt a chart (PhysicalGraphBounds.physicalLift h L.val.1 w)) := by
  have hc : PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h L.val.1 w) ∈
      PolarCharts.chartDomain a chart := by
    simpa only [PhysicalGraphBounds.liftXY_physicalLift] using hchart
  simp only [PhysicalWaveSum.commonWave, commonLift_zero, potentialFamily, positiveIndex,
    dite_eq_left L.mem, Int.cast_one, mul_one, ite_true]
  rw [← rawPotential_cylinderAt sys hh f G L k ha chart hc]
  by_cases hz : waveMask sys L.val ((geometry sys L.val 0).coordinates k
      (PhysicalGraphBounds.physicalLift h L.val.1 w).2) = 0
  · simp [hz]
  · rw [← phase_eq_native sys hh f G L k a chart _ (waveMask_support sys L.val hz), G.frequency L]
    simp only [PhysicalGraphBounds.character, HarmonicCalculus.carrier,
      HarmonicCalculus.phaseFactor, PhysicalGraphBounds.phaseFactor, Complex.real_smul]
    congr 1
    ring

omit G in
noncomputable def referencePotentialCoefficient (L : NativeLabel f.active) (x : Cylinder) :
  ComplexVector :=
  CurlClassBounds.inverseCarrier ((f.primary L).base.frequency L.val.1) •
    CurlClassBounds.normalCoefficient
      ((f.primary L).base.normal (f.primary L).strip (f.primary L).directions L.val.1 x)
      ((ActualPeriodizedSignedRealization.periodizedPrimary (f.primary L)
        (layout sys hh L.val L.property 0)).raw (f.state L).referenceRequest (f.column L) L.val.1 x)

omit G in
theorem rotatedPotential_sum (L : NativeLabel f.active) (x : Cylinder) (Y : Plane) (i : Fin 3) :
    (∑' k, waveMask sys L.val ((geometry sys L.val 0).coordinates k x.1.2.2) •
      rotateCoefficient Y (rawPotential sys hh f L k x) i) =
        rotateCoefficient Y (referencePotentialCoefficient sys hh f L x) i := by
  let A : ComplexVector →L[ℝ] ℂ := (ContinuousLinearMap.proj i).comp (rotationMap Y)
  have he := A.map_tsum (waveMask_summable_smul sys L x.1.2.2 (fun k => rawPotential sys hh f L k
    x))
  simp only [map_smul, A, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    rotationMap_apply] at he
  rw [← signed_potential_eq_sum sys hh f L x] at he
  exact he.symm

/-- The complete vector-potential copy sum retains the same reference
coefficient.  The rotation acts on the actual sum, not a surrogate field. -/
theorem potential_periodized (L : NativeLabel f.active) (i : Fin 3)
    {a b : ℝ} (ha : 0 < a) (w : SpaceTime)
    (hw : PhysicalGraphBounds.scaledRadial L.val.1 w ∈ PhysicalGraphBounds.annulus a b) :
    (potentialFamily sys hh f i).periodized a h sys.radius (positiveIndex L) w =
      (ChartScales.Q L.val.1 ^ (-h) : ℝ) •
        (rotateCoefficient (PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h L.val.1
          w))
          (referencePotentialCoefficient sys hh f L
            (cylinderAt a (PhysicalWaveSum.chooseChart a (PhysicalGraphBounds.scaledRadial L.val.1
              w))
              (PhysicalGraphBounds.physicalLift h L.val.1 w))) i *
        HarmonicCalculus.carrier ((f.primary L).base.frequency L.val.1)
          ((f.primary L).base.phase L.val.1)
          (cylinderAt a (PhysicalWaveSum.chooseChart a (PhysicalGraphBounds.scaledRadial L.val.1 w))
            (PhysicalGraphBounds.physicalLift h L.val.1 w))) := by
  have hc := PhysicalWaveSum.chooseChart_valid ha hw
  unfold PhysicalCopyBounds.CopyFamily.periodized
  simp_rw [potential_term_active]
  change (∑' k, PhysicalWaveSum.commonWave a h L.val.1 0 sys.radius
    ((selectedCarrier (h := h) f L k).withChart
      (PhysicalWaveSum.chooseChart a (PhysicalGraphBounds.scaledRadial L.val.1 w)))
    ((potentialFamily sys hh f i).amplitude k (positiveIndex L)) 1 w) = _
  simp_rw [potential_commonWave sys hh f G L _ i ha _ w hc]
  rw [tsum_mul_right, tsum_const_smul'']
  rw [← rotatedPotential_sum sys hh f L
    (cylinderAt a (PhysicalWaveSum.chooseChart a (PhysicalGraphBounds.scaledRadial L.val.1 w))
      (PhysicalGraphBounds.physicalLift h L.val.1 w))
    (PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h L.val.1 w)) i]
  exact smul_mul_assoc _ _ _


omit hh in
theorem angular_integer (L : NativeLabel f.active) (k : Frequency) :
    (ChartScales.carrier h L.val.1 : ℝ) * (selectedCarrier (h := h) f L k).angular =
      ((G.angular L).mode : ℝ) := by
  have he := (G.angular L).phase (0 : Cylinder) 1
  rw [G.phase L] at he
  simp only [ActualSignedGeometry.periodicPhase, PhaseCalculus.phase, Prod.fst_zero, Prod.snd_zero,
    one_smul, zero_add, mul_zero,
    mul_one, add_zero] at he
  have hp : ((f.primary L).pulse (f.column L)).phase.p L.val.1 =
      (G.angular L).mode / (f.primary L).base.frequency L.val.1 := by linarith
  change (ChartScales.carrier h L.val.1 : ℝ) *
    ((f.primary L).pulse (f.column L)).phase.p L.val.1 = _
  rw [hp, G.frequency L]
  field_simp [PartitionedCovariance.actual_carrier_ne_zero h L.val.1]


theorem pressure_periodized_of_chart (L : NativeLabel f.active) {a b : ℝ} (ha : 0 < a)
    (w : SpaceTime) (hw : PhysicalGraphBounds.scaledRadial L.val.1 w ∈ PhysicalGraphBounds.annulus
      a b)
    (j : PolarCharts.Index) (hj : PhysicalGraphBounds.scaledRadial L.val.1 w ∈
      PolarCharts.chartDomain a j) :
    (pressureFamily sys hh f).periodized a h sys.radius (positiveIndex L) w =
      (ChartScales.Q L.val.1 ^ (-(2 * CoordinateAlgebra.A h)) : ℝ) •
        HarmonicCalculus.mode ((f.primary L).base.frequency L.val.1)
          ((f.primary L).base.phase L.val.1)
          ((ActualPeriodizedSignedRealization.periodizedPrimary (f.primary L)
            (layout sys hh L.val L.property 0)).rawPressure (f.state L).referenceRequest (f.column
              L) L.val.1)
          (cylinderAt a j (PhysicalGraphBounds.physicalLift h L.val.1 w)) := by
  have hc := PhysicalWaveSum.chooseChart_valid ha hw
  unfold PhysicalCopyBounds.CopyFamily.periodized
  simp_rw [pressure_term_active]
  change (∑' k, PhysicalWaveSum.commonWave a h L.val.1 0 sys.radius
    ((selectedCarrier (h := h) f L k).withChart
      (PhysicalWaveSum.chooseChart a (PhysicalGraphBounds.scaledRadial L.val.1 w)))
    ((pressureFamily sys hh f).amplitude k (positiveIndex L)) 1 w) = _
  have he (k : Frequency) := PhysicalWaveSum.commonWave_charts_agree ha h L.val.1 0 sys.radius
    (selectedCarrier (h := h) f L k) ((pressureFamily sys hh f).amplitude k (positiveIndex L)) 1 w
    (G.angular L).mode (angular_integer sys f G L k) _ j hc hj
  simp_rw [he, pressure_commonWave sys hh f G L _ ha j w hj]
  rw [tsum_mul_right, tsum_const_smul'', HarmonicCalculus.mode, signed_pressure_eq_sum sys hh f L]
  exact smul_mul_assoc _ _ _

theorem potential_periodized_of_chart (L : NativeLabel f.active) (i : Fin 3)
    {a b : ℝ} (ha : 0 < a) (w : SpaceTime)
    (hw : PhysicalGraphBounds.scaledRadial L.val.1 w ∈ PhysicalGraphBounds.annulus a b)
    (j : PolarCharts.Index) (hj : PhysicalGraphBounds.scaledRadial L.val.1 w ∈
      PolarCharts.chartDomain a j) :
    (potentialFamily sys hh f i).periodized a h sys.radius (positiveIndex L) w =
      (ChartScales.Q L.val.1 ^ (-h) : ℝ) •
        (rotateCoefficient (PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h L.val.1
          w))
          (referencePotentialCoefficient sys hh f L
            (cylinderAt a j (PhysicalGraphBounds.physicalLift h L.val.1 w))) i *
        HarmonicCalculus.carrier ((f.primary L).base.frequency L.val.1)
          ((f.primary L).base.phase L.val.1)
          (cylinderAt a j (PhysicalGraphBounds.physicalLift h L.val.1 w))) := by
  have hc := PhysicalWaveSum.chooseChart_valid ha hw
  unfold PhysicalCopyBounds.CopyFamily.periodized
  simp_rw [potential_term_active]
  change (∑' k, PhysicalWaveSum.commonWave a h L.val.1 0 sys.radius
    ((selectedCarrier (h := h) f L k).withChart
      (PhysicalWaveSum.chooseChart a (PhysicalGraphBounds.scaledRadial L.val.1 w)))
    ((potentialFamily sys hh f i).amplitude k (positiveIndex L)) 1 w) = _
  have he (k : Frequency) := PhysicalWaveSum.commonWave_charts_agree ha h L.val.1 0 sys.radius
    (selectedCarrier (h := h) f L k) ((potentialFamily sys hh f i).amplitude k (positiveIndex L)) 1
      w
    (G.angular L).mode (angular_integer sys f G L k) _ j hc hj
  simp_rw [he, potential_commonWave sys hh f G L _ i ha j w hj]
  rw [tsum_mul_right, tsum_const_smul'']
  rw [← rotatedPotential_sum sys hh f L (cylinderAt a j (PhysicalGraphBounds.physicalLift h L.val.1
    w))
    (PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h L.val.1 w)) i]
  exact smul_mul_assoc _ _ _

/-- Equality with the original Cartesian signed pressure, not merely a
newly defined coefficient sum. -/
theorem pressure_periodized_physical (L : NativeLabel f.active) {a b delta : ℝ}
    (ha : 0 < a) (hdelta : 0 < delta) (j : PolarCharts.Index) (z : SpaceTime)
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical delta j)
    (hw : PhysicalGraphBounds.scaledRadial L.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PhysicalGraphBounds.annulus a b)
    (hj : PhysicalGraphBounds.scaledRadial L.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain a j) :
    ((pressureFamily sys hh f).periodized a h sys.radius (positiveIndex L)
      (z.1, CylindricalResidual.chart z.2)).re =
      ActualPeriodizedSignedRealization.physicalPressure (f.primary L)
        (layout sys hh L.val L.property 0) (f.view L) (f.state L) (f.column L) delta
        (z.1, CylindricalResidual.chart z.2) := by
  rw [pressure_periodized_of_chart sys hh f G L ha _ hw j hj,
    cylinderAt_physical_forward h L.val.1 ha j z hz.1 hz.2.1 hj]
  have hK : (f.primary L).base.frequency L.val.1 ≠ 0 := by
    rw [G.frequency L]
    exact PartitionedCovariance.actual_carrier_ne_zero _ _
  have hG : PhysicalSignedWave.ChartGeometry
      (ActualPeriodizedSignedRealization.periodizedPrimary (f.primary L) (layout sys hh L.val
        L.property 0)).base
      (ActualPeriodizedSignedRealization.periodizedPrimary (f.primary L) (layout sys hh L.val
        L.property 0)).strip
      (ActualPeriodizedSignedRealization.periodizedPrimary (f.primary L) (layout sys hh L.val
        L.property 0)).directions
      L.val.1 (f.view L).exponent (f.view L).referenceScale (f.view L).referenceCover := by
    simp only [G.exponent L, G.scale L, G.cover L]
    exact G.chart L
  have he := (ActualPeriodizedSignedRealization.views (f.primary L)
    (layout sys hh L.val L.property 0) (f.view L)).physicalPressure_forward
      (ActualPeriodizedSignedRealization.periodizedAngular (f.primary L)
        (layout sys hh L.val L.property 0) (G.angular L)) hK hG (f.column L) hdelta j hz
  change _ = (ActualPeriodizedSignedRealization.views (f.primary L)
    (layout sys hh L.val L.property 0) (f.view L)).physicalPressure
      (f.state L).referenceRequest (f.column L) delta (z.1, CylindricalResidual.chart z.2)
  rw [he]
  simp only [PhysicalSignedWave.PrimaryData.Views.complexPhysicalPressure,
    PhysicalSignedWave.PrimaryData.Views.physicalPressureCoefficient,
    ActualPeriodizedSignedRealization.views, G.exponent L, G.scale L, G.cover L,
    HarmonicCalculus.mode, smul_mul_assoc]
  rfl


/-- The original physical potential is the pulled-back native coefficient
mode, with the potential scale derived by the actual curl construction. -/
theorem referencePotential_eq_mode (L : NativeLabel f.active)
    (hPhi : ContDiffOn ℝ ∞ ((f.primary L).base.phase L.val.1) (f.primary L).strip.domain)
    (z : SpaceTime) (hr : 0 < z.2 0)
    (hz : (PhysicalResidualBridge.commonGraph (ChartScales.Q L.val.1) h
      (ChartScales.nativeIndex h L.val.1)).map z ∈ (f.primary L).strip.domain) :
    (ActualPeriodizedSignedRealization.views (f.primary L) (layout sys hh L.val L.property 0)
      (f.view L)).referencePotential (f.state L).referenceRequest (f.column L) z =
      (ChartScales.Q L.val.1 ^ (-h) : ℝ) • HarmonicCalculus.vectorMode
        ((f.primary L).base.frequency L.val.1) ((f.primary L).base.phase L.val.1)
        (referencePotentialCoefficient sys hh f L)
        ((PhysicalResidualBridge.commonGraph (ChartScales.Q L.val.1) h
          (ChartScales.nativeIndex h L.val.1)).map z) := by
  let V := ActualPeriodizedSignedRealization.views (f.primary L)
    (layout sys hh L.val L.property 0) (f.view L)
  have hK : (f.primary L).base.frequency L.val.1 ≠ 0 := by
    rw [G.frequency L]
    exact PartitionedCovariance.actual_carrier_ne_zero _ _
  have hx : z ∈ (PhysicalResidualBridge.commonGraph (f.view L).referenceScale
      (f.view L).exponent (f.view L).referenceCover).source (f.primary L).strip.domain := by
    simp only [G.scale L, G.exponent L, G.cover L]
    exact And.intro hr hz
  have he := PhysicalCurlCovariance.referencePotential_eq_on (f.view L).referenceScale_pos
    (f.view L).exponent (f.view L).referenceCover (f.primary L).strip.isOpen_domain
    hK hK hPhi
    ((ActualPeriodizedSignedRealization.periodizedPrimary (f.primary L)
      (layout sys hh L.val L.property 0)).raw (f.state L).referenceRequest (f.column L) L.val.1)
    V.physicalPhase (V.physicalRaw (f.state L).referenceRequest (f.column L))
    (fun _ _ => rfl) (fun _ _ => rfl) hx
  simp only [G.scale L, G.exponent L, G.cover L] at he
  change V.referencePotential (f.state L).referenceRequest (f.column L) z = _ at he
  simp only [CurlClassBounds.vectorPotential, CurlClassBounds.coefficient,
    ← (G.chart L).normal] at he ⊢
  exact he

/-- Equality with the same signed Cartesian potential. Every native copy,
cutoff and the potential's actual derivative normalization is retained. -/
theorem potential_periodized_physical (L : NativeLabel f.active) (i : Fin 3)
    (hPhi : ContDiffOn ℝ ∞ ((f.primary L).base.phase L.val.1) (f.primary L).strip.domain)
    {a b delta : ℝ} (ha : 0 < a) (hdelta : 0 < delta) (j : PolarCharts.Index) (z : SpaceTime)
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical delta j)
    (hsource : (PhysicalResidualBridge.commonGraph (ChartScales.Q L.val.1) h
      (ChartScales.nativeIndex h L.val.1)).map z ∈ (f.primary L).strip.domain)
    (hw : PhysicalGraphBounds.scaledRadial L.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PhysicalGraphBounds.annulus a b)
    (hj : PhysicalGraphBounds.scaledRadial L.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain a j) :
    ((potentialFamily sys hh f i).periodized a h sys.radius (positiveIndex L)
      (z.1, CylindricalResidual.chart z.2)).re =
      ActualPeriodizedSignedRealization.physicalPotential (f.primary L)
        (layout sys hh L.val L.property 0) (f.view L) (f.state L) (f.column L) delta
        (z.1, CylindricalResidual.chart z.2) i := by
  let V := ActualPeriodizedSignedRealization.views (f.primary L)
    (layout sys hh L.val L.property 0) (f.view L)
  have hK : (f.primary L).base.frequency L.val.1 ≠ 0 := by
    rw [G.frequency L]
    exact PartitionedCovariance.actual_carrier_ne_zero _ _
  have hmap := cylinderAt_physical_forward h L.val.1 ha j z hz.1 hz.2.1 hj
  have hc : PhysicalGraphBounds.liftXY
      (PhysicalGraphBounds.physicalLift h L.val.1 (z.1, CylindricalResidual.chart z.2)) ∈
      PolarCharts.chartDomain a j := by simpa only [PhysicalGraphBounds.liftXY_physicalLift] using
        hj
  have hangle : (PolarCharts.chart a j (PhysicalGraphBounds.liftXY
      (PhysicalGraphBounds.physicalLift h L.val.1 (z.1, CylindricalResidual.chart z.2)))).2 = z.2 1
        :=
    congrArg Prod.snd hmap
  rw [potential_periodized_of_chart sys hh f G L i ha _ hw j hj,
    ← rotateCoefficient_vectorMode]
  have he := rotateCoefficient_chart_re ha j hc
    ((ChartScales.Q L.val.1 ^ (-h) : ℝ) • HarmonicCalculus.vectorMode
      ((f.primary L).base.frequency L.val.1) ((f.primary L).base.phase L.val.1)
      (referencePotentialCoefficient sys hh f L)
      (cylinderAt a j (PhysicalGraphBounds.physicalLift h L.val.1 (z.1, CylindricalResidual.chart
        z.2)))) i
  rw [rotateCoefficient_real_smul, Pi.smul_apply] at he
  rw [he, hangle, hmap, ← referencePotential_eq_mode sys hh f G L hPhi z hz.1 hsource]
  have hf := (PhysicalCurlCovariance.globalCartesianPotential_forward_germ hdelta j
    (V.referencePotential (f.state L).referenceRequest (f.column L))
    (V.referencePotential_periodic (ActualPeriodizedSignedRealization.periodizedAngular
      (f.primary L) (layout sys hh L.val L.property 0) (G.angular L)) hK (f.column L))
        hz).eq_of_nhds
  exact (congrArg (fun v : Space => v i) hf).symm

end PhysicalFamilies


/-! ## Explicit native sources and their physical class adapter -/

abbrev Native := CartesianCopySource.Native
abbrev SourceIndex := PhysicalWaveSum.WaveIndex 1 × Frequency

noncomputable def nativeCylinder (y : Native) : Cylinder :=
  ((y.1, ((y.2.1.2, y.2.1.1), y.2.2)), 0)

theorem nativeCylinder_map (x : LiftPoint) :
    nativeCylinder (PhysicalClassBounds.cylindricalMap x) = cylinderZero x := rfl

theorem cartesian_rotation (Y : Plane) (v : ComplexVector) :
    CartesianCopySource.rotationMap Y v = rotateCoefficient Y v := by
  rw [CartesianCopySource.rotationMap_apply]
  rfl

section NativeSources

variable {D h : ℝ}
  (sys : PartitionedCovariance.SlotSystem D h ActualSignedGeometry.radialVector
    ActualSignedGeometry.temporalVector)
  (hh : 0 ≤ h) {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (f : SignedFamily U)

noncomputable def nativePotentialSource (I : SourceIndex) (n : ℕ) (y : Native) : ComplexVector :=
  if hL : I.1.1 ∈ f.active then
    if I.1.2.val = 1 ∧ n = I.1.1.val.1 then
      waveMask sys I.1.1.val ((geometry sys I.1.1.val 0).coordinates I.2 y.2.2) •
        rawPotential sys hh f ⟨I.1.1.val, I.1.1.property, hL⟩ I.2 (nativeCylinder y)
    else 0
  else 0

noncomputable def nativePressureSource (I : SourceIndex) (n : ℕ) (y : Native) : ℂ :=
  if hL : I.1.1 ∈ f.active then
    if I.1.2.val = 1 ∧ n = I.1.1.val.1 then
      waveMask sys I.1.1.val ((geometry sys I.1.1.val 0).coordinates I.2 y.2.2) •
        rawPressure sys hh f ⟨I.1.1.val, I.1.1.property, hL⟩ I.2 (nativeCylinder y)
    else 0
  else 0

theorem potential_amplitude_eq_source (i : Fin 3) (k : Frequency)
    (I : PhysicalWaveSum.WaveIndex 1) (x : LiftPoint) :
    (potentialFamily sys hh f i).amplitude k I x =
      (ChartScales.Q I.1.val.1 ^ (-h) : ℝ) •
        CartesianCopySource.rotatedSource (nativePotentialSource sys hh f) (I, k) I.1.val.1 x i :=
          by
  unfold CartesianCopySource.rotatedSource
  rw [cartesian_rotation]
  by_cases hL : I.1 ∈ f.active
  · by_cases hI : I.2.val = 1
    · simp only [potentialFamily, nativePotentialSource, dite_eq_left hL, hI, and_self,
        ite_true, nativeCylinder_map, rotateCoefficient_real_smul, Pi.smul_apply]
      simp only [Complex.real_smul, mul_assoc]
      rfl
    · simp [potentialFamily, nativePotentialSource, hL, hI, rotateCoefficient_zero]
  · simp [potentialFamily, nativePotentialSource, hL, rotateCoefficient_zero]

theorem pressure_amplitude_eq_source (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1) (x :
  LiftPoint) :
    (pressureFamily sys hh f).amplitude k I x =
      (ChartScales.Q I.1.val.1 ^ (-(2 * CoordinateAlgebra.A h)) : ℝ) •
        nativePressureSource sys hh f (I, k) I.1.val.1 (PhysicalClassBounds.cylindricalMap x) := by
  by_cases hL : I.1 ∈ f.active
  · by_cases hI : I.2.val = 1
    · simp only [pressureFamily, nativePressureSource, dite_eq_left hL, hI, and_self,
        ite_true, nativeCylinder_map]
      simp only [Complex.real_smul, mul_assoc]
      rfl
    · simp [pressureFamily, nativePressureSource, hL, hI]
  · simp [pressureFamily, nativePressureSource, hL]

omit sys hh f in
theorem increment_zero_target (H : Mat2) (R : Vec2) (j : Fin 2) :
    SignedCovariance.increment H 0 R j = 0 := by
  fin_cases j <;> simp [SignedCovariance.increment, SmoothCovariance.amplitudes,
    SmoothCovariance.weights,
    SmoothCovariance.cramerNumerator]

theorem rawPotential_zero (L : NativeLabel f.active) (k : Frequency) (x : Cylinder)
    (hx : (f.primary L).mask L.val.1 x = 0 ∨ (f.primary L).target L.val.1 x = 0) :
    rawPotential sys hh f L k x = 0 := by
  have hr : ActualPeriodizedSignedRealization.referenceScalar (f.primary L)
      (f.state L).referenceRequest (f.column L) L.val.1 x = 0 := by
    rcases hx with hm | ht
    · simp [ActualPeriodizedSignedRealization.referenceScalar, SignedWaveUpdate.signedScalar, hm]
    · simp [ActualPeriodizedSignedRealization.referenceScalar, SignedWaveUpdate.signedScalar, ht,
        increment_zero_target]
  simp [rawPotential, rawSignedAmplitude, hr, CurlClassBounds.normalCoefficient,
    CurlClassBounds.normalCross]

theorem rawPressure_zero (L : NativeLabel f.active) (k : Frequency) (x : Cylinder)
    (hx : (f.primary L).mask L.val.1 x = 0 ∨ (f.primary L).target L.val.1 x = 0) :
    rawPressure sys hh f L k x = 0 := by
  have hr : ActualPeriodizedSignedRealization.referenceScalar (f.primary L)
      (f.state L).referenceRequest (f.column L) L.val.1 x = 0 := by
    rcases hx with hm | ht
    · simp [ActualPeriodizedSignedRealization.referenceScalar, SignedWaveUpdate.signedScalar, hm]
    · simp [ActualPeriodizedSignedRealization.referenceScalar, SignedWaveUpdate.signedScalar, ht,
        increment_zero_target]
  simp only [rawPressure, hr, zero_smul]

theorem potential_amplitude_inputs (i : Fin 3) (k : Frequency)
    (I : PhysicalWaveSum.WaveIndex 1) (x : LiftPoint)
    (hx : (potentialFamily sys hh f i).amplitude k I x ≠ 0) :
    ∃ hL : I.1 ∈ f.active, I.2.val = 1 ∧
      (f.primary ⟨I.1.val, I.1.property, hL⟩).mask I.1.val.1 (cylinderZero x) ≠ 0 ∧
      (f.primary ⟨I.1.val, I.1.property, hL⟩).target I.1.val.1 (cylinderZero x) ≠ 0 := by
  by_cases hL : I.1 ∈ f.active
  · by_cases hI : I.2.val = 1
    · refine ⟨hL, hI, ?_, ?_⟩
      · intro hm
        have hr := rawPotential_zero sys hh f ⟨I.1.val, I.1.property, hL⟩ k (cylinderZero x)
          (Or.inl hm)
        exact hx (by simp [potentialFamily, hL, hI, hr, rotateCoefficient_zero])
      · intro ht
        have hr := rawPotential_zero sys hh f ⟨I.1.val, I.1.property, hL⟩ k (cylinderZero x)
          (Or.inr ht)
        exact hx (by simp [potentialFamily, hL, hI, hr, rotateCoefficient_zero])
    · exact False.elim (hx (by simp [potentialFamily, hL, hI]))
  · exact False.elim (hx (by simp [potentialFamily, hL]))

theorem pressure_amplitude_inputs (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1) (x : LiftPoint)
    (hx : (pressureFamily sys hh f).amplitude k I x ≠ 0) :
    ∃ hL : I.1 ∈ f.active, I.2.val = 1 ∧
      (f.primary ⟨I.1.val, I.1.property, hL⟩).mask I.1.val.1 (cylinderZero x) ≠ 0 ∧
      (f.primary ⟨I.1.val, I.1.property, hL⟩).target I.1.val.1 (cylinderZero x) ≠ 0 := by
  by_cases hL : I.1 ∈ f.active
  · by_cases hI : I.2.val = 1
    · refine ⟨hL, hI, ?_, ?_⟩
      · intro hm
        have hr := rawPressure_zero sys hh f ⟨I.1.val, I.1.property, hL⟩ k (cylinderZero x) (Or.inl
          hm)
        exact hx (by simp [pressureFamily, hL, hI, hr])
      · intro ht
        have hr := rawPressure_zero sys hh f ⟨I.1.val, I.1.property, hL⟩ k (cylinderZero x) (Or.inr
          ht)
        exact hx (by simp [pressureFamily, hL, hI, hr])
    · exact False.elim (hx (by simp [pressureFamily, hL, hI]))
  · exact False.elim (hx (by simp [pressureFamily, hL]))


/-- Localization facts about the original shared mask and target.  The
native domain condition is on every slow/fast fiber. No support statement
about a corrected velocity, potential, pressure, or copy sum is assumed. -/
structure PrimitiveLocalization (a b : ℝ) (s : StripData Native) : Prop where
  normalized : ∀ (L : NativeLabel f.active) (y : Native), 0 ≤ y.1 →
    (f.primary L).mask L.val.1 (nativeCylinder y) ≠ 0 →
    (f.primary L).target L.val.1 (nativeCylinder y) ≠ 0 →
    0 < y.2.1.1 ∧
      1 / 2 ≤ SimilarityCoordinates.coordinateQ (2 * h) y.2.1 ∧
      SimilarityCoordinates.coordinateQ (2 * h) y.2.1 ≤ 2 ∧
      a ≤ y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ∧
      y.1 / Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ≤ b
  domain : ∀ (L : NativeLabel f.active) (y : Native), 0 ≤ y.1 →
    (f.primary L).mask L.val.1 (nativeCylinder y) ≠ 0 →
    (f.primary L).target L.val.1 (nativeCylinder y) ≠ 0 → y ∈ s.domain
  mask_pullback : ∀ (L : NativeLabel f.active) (w : SpaceTime), w ∈ PhysicalWaveSum.preterminal →
    (f.primary L).mask L.val.1 (cylinderZero (PhysicalGraphBounds.physicalLift h L.val.1 w)) =
      PhysicalWaveSum.physicalMask (CoordinateAlgebra.D h) L.val (PhysicalWaveSum.physicalParams h
        w)

omit sys hh f in
theorem normalized_slow_norm {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) {p : Plane}
    (ht : 0 < p.1) (hlo : 1 / 2 ≤ SimilarityCoordinates.coordinateQ (2 * h) p)
    (hhi : SimilarityCoordinates.coordinateQ (2 * h) p ≤ 2) : ‖p‖ ≤ 2 := by
  have he := SimilarityCoordinates.coordinateQ_spec (by linarith : 0 < 2 * h)
    (by linarith : 2 * h < 1) ht
  have hq : 0 < SimilarityCoordinates.coordinateQ (2 * h) p := he.1
  dsimp only [SimilarityCoordinates.forwardScalar] at he
  have hp : 1 / 2 ≤ SimilarityCoordinates.coordinateQ (2 * h) p ^ (2 * h) := by
    by_cases h1 : SimilarityCoordinates.coordinateQ (2 * h) p ≤ 1
    · calc
        1 / 2 ≤ SimilarityCoordinates.coordinateQ (2 * h) p := hlo
        _ = SimilarityCoordinates.coordinateQ (2 * h) p ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hq h1 (by linarith)
    · exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans
        (Real.one_le_rpow (le_of_not_ge h1) (by positivity))
  have hprod : 0 ≤ p.2 ^ 2 * SimilarityCoordinates.coordinateQ (2 * h) p ^ (2 * h) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hq.le _)
  have hT : |p.1| ≤ 2 := by rw [abs_of_pos ht]; linarith [he.2]
  have hZ : |p.2| ≤ 2 := by
    have hs : p.2 ^ 2 ≤ 4 := by nlinarith [he.2, sq_nonneg p.2]
    nlinarith [sq_abs p.2, abs_nonneg p.2]
  simpa only [Prod.norm_def, Real.norm_eq_abs] using max_le hT hZ

variable {a b : ℝ} {s : StripData Native}
  (hloc : PrimitiveLocalization (h := h) f a b s)

include hloc

theorem primitive_annulus (hh0 : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hb : 0 < b)
    (L : NativeLabel f.active) (x : LiftPoint)
    (hm : (f.primary L).mask L.val.1 (cylinderZero x) ≠ 0)
    (hT : (f.primary L).target L.val.1 (cylinderZero x) ≠ 0) :
    PhysicalGraphBounds.liftXY x ∈ PhysicalGraphBounds.annulus (a / 4) (2 * b) ∧
      ‖PhysicalGraphBounds.liftZT x‖ ≤ 2 := by
  let y := PhysicalClassBounds.cylindricalMap x
  have hy := hloc.normalized L y (Real.sqrt_nonneg _) hm hT
  have hq : 0 < SimilarityCoordinates.coordinateQ (2 * h) y.2.1 := by linarith [hy.2.1]
  have hs := Real.sqrt_pos.mpr hq
  have hslow := normalized_slow_norm hh0 hh1 hy.1 hy.2.1 hy.2.2.1
  have hlo : 1 / 2 ≤ Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) :=
    (Real.le_sqrt (by norm_num) hq.le).mpr (by nlinarith [hy.2.1])
  have hhi : Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) y.2.1) ≤ 2 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by linarith [hy.2.2.1])
  have hradlo := (le_div_iff₀ hs).mp hy.2.2.2.1
  have hradhi := (div_le_iff₀ hs).mp hy.2.2.2.2
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
    (hm : (f.primary L).mask L.val.1 (cylinderZero x) ≠ 0)
    (hT : (f.primary L).target L.val.1 (cylinderZero x) ≠ 0) :
    PhysicalClassBounds.cylindricalMap x ∈ s.domain :=
  hloc.domain L _ (Real.sqrt_nonneg _) hm hT


theorem potential_support (G : ReferenceGeometry sys f) (hh0 : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hb : 0 < b) (i : Fin 3) :
    LocalPhysicalCopyBounds.SupportData (potentialFamily sys hh f i) (a / 4) (2 * b) h sys.radius 2
      0 where
  gap_le _ := le_rfl
  gap_native _ := Nat.zero_le _
  angular_integer k L := by
    by_cases hL : L ∈ f.active
    · refine ⟨(G.angular ⟨L.val, L.property, hL⟩).mode, ?_⟩
      simpa only [potentialFamily, extendedCarrier, dite_eq_left hL] using
        angular_integer sys f G ⟨L.val, L.property, hL⟩ k
    · exact ⟨0, by simp [potentialFamily, extendedCarrier, hL, carrier]⟩
  geometry_support k I w hw := by
    change (potentialFamily sys hh f i).amplitude k I (PhysicalWaveSum.commonLift h I.1.val.1 0 w)
      ≠ 0 at hw
    rw [commonLift_zero] at hw
    obtain ⟨hL, _, hm, hT⟩ := potential_amplitude_inputs sys hh f i k I _ hw
    have hn := primitive_annulus (f := f) hloc hh0 hh1 ha hb ⟨I.1.val, I.1.property, hL⟩ _ hm hT
    refine ⟨?_, hn.2, ?_⟩
    · simpa only [PhysicalGraphBounds.liftXY_physicalLift] using hn.1
    · have hs := potential_amplitude_mem sys hh f i k I _ hw
      have hwidth := width_on_core sys I.1.val 0 k (PhysicalGraphBounds.physicalLift h I.1.val.1
        w).2 hs
      change |PhysicalGraphBounds.etaCoordinate
        (PhysicalGraphBounds.nativeGraph h I.1.val.1 w - (extendedCarrier (h := h) f I.1
          k).center)| ≤ sys.radius
      rw [extendedCarrier_center]
      exact hwidth
  mask_support k I w hw hne := by
    change (potentialFamily sys hh f i).amplitude k I (PhysicalWaveSum.commonLift h I.1.val.1 0 w)
      ≠ 0 at hne
    rw [commonLift_zero] at hne
    obtain ⟨hL, _, hm, _⟩ := potential_amplitude_inputs sys hh f i k I _ hne
    rw [← hloc.mask_pullback ⟨I.1.val, I.1.property, hL⟩ w hw]
    exact hm

theorem pressure_support (G : ReferenceGeometry sys f) (hh0 : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hb : 0 < b) :
    LocalPhysicalCopyBounds.SupportData (pressureFamily sys hh f) (a / 4) (2 * b) h sys.radius 2 0
      where
  gap_le _ := le_rfl
  gap_native _ := Nat.zero_le _
  angular_integer k L := by
    by_cases hL : L ∈ f.active
    · refine ⟨(G.angular ⟨L.val, L.property, hL⟩).mode, ?_⟩
      simpa only [pressureFamily, extendedCarrier, dite_eq_left hL] using
        angular_integer sys f G ⟨L.val, L.property, hL⟩ k
    · exact ⟨0, by simp [pressureFamily, extendedCarrier, hL, carrier]⟩
  geometry_support k I w hw := by
    change (pressureFamily sys hh f).amplitude k I (PhysicalWaveSum.commonLift h I.1.val.1 0 w) ≠ 0
      at hw
    rw [commonLift_zero] at hw
    obtain ⟨hL, _, hm, hT⟩ := pressure_amplitude_inputs sys hh f k I _ hw
    have hn := primitive_annulus (f := f) hloc hh0 hh1 ha hb ⟨I.1.val, I.1.property, hL⟩ _ hm hT
    refine ⟨?_, hn.2, ?_⟩
    · simpa only [PhysicalGraphBounds.liftXY_physicalLift] using hn.1
    · have hs := pressure_amplitude_mem sys hh f k I _ hw
      have hwidth := width_on_core sys I.1.val 0 k (PhysicalGraphBounds.physicalLift h I.1.val.1
        w).2 hs
      change |PhysicalGraphBounds.etaCoordinate
        (PhysicalGraphBounds.nativeGraph h I.1.val.1 w - (extendedCarrier (h := h) f I.1
          k).center)| ≤ sys.radius
      rw [extendedCarrier_center]
      exact hwidth
  mask_support k I w hw hne := by
    change (pressureFamily sys hh f).amplitude k I (PhysicalWaveSum.commonLift h I.1.val.1 0 w) ≠ 0
      at hne
    rw [commonLift_zero] at hne
    obtain ⟨hL, _, hm, _⟩ := pressure_amplitude_inputs sys hh f k I _ hne
    rw [← hloc.mask_pullback ⟨I.1.val, I.1.property, hL⟩ w hw]
    exact hm

/-- The actual vector-potential sum is an axis-preserving copy potential,
with the same fixed outer radius used by the physical stage estimates. -/
noncomputable def copyPotential (G : ReferenceGeometry sys f) (hh0 : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hb : 0 < b) : MixedAxisPreservation.CopyPotential h where
  Copy := Frequency
  harmonics := 1
  family := potentialFamily sys hh f
  inner := a / 4
  outer := 2 * b
  width := sys.radius
  axialRadius := 2
  gap := 0
  inner_pos := div_pos ha (by norm_num)
  support := potential_support sys hh f hloc G hh0 hh1 ha hb
  cells := potentialCells sys hh f

theorem copyPotential_field (G : ReferenceGeometry sys f) (hh0 : 0 < h) (hh1 : h < 1 / 2)
    (ha : 0 < a) (hb : 0 < b) :
    (copyPotential sys hh f hloc G hh0 hh1 ha hb).field =
      PhysicalCopyBounds.vectorSum (potentialFamily sys hh f) (a / 4) h sys.radius := rfl

end NativeSources



/-! ## A fixed native region for the selected carrier profiles -/

noncomputable def carrierRegion (h a b : ℝ) : Set PhysicalGraphBounds.Slow :=
  {p | p.1 ∈ Ioo (a / 8) (4 * b + 1) ∧
    (p.2.2, p.2.1) ∈ PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 4) 4}

theorem carrierRegion_open {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (a b : ℝ) :
    IsOpen (carrierRegion h a b) :=
  (isOpen_Ioo.preimage continuous_fst).inter
    ((PhysicalMeanDomain.normalizedSlowDomain_open (by linarith : 0 < 2 * h)
      (by linarith : 2 * h < 1) (1 / 4) 4).preimage
      (continuous_snd.snd.prodMk continuous_snd.fst))

/-- Carrier profile arguments lie in a fixed open native region. The
native phase center affects the clock, but not this slow argument. -/
theorem carrierRegion_contains {h a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a)
    (c : PhysicalWaveSum.CarrierData) (r0 : ℝ) (L : PhysicalWaveSum.BandLabel)
    (w : SpaceTime) (hw : w ∈ PhysicalWaveSum.preterminal)
    (hregion : PhysicalWaveSum.physicalParams h w ∈
      PhysicalWaveSum.labelRegion (CoordinateAlgebra.D h) L.val)
    (hann : PhysicalGraphBounds.scaledRadial L.val.1 w ∈ PhysicalGraphBounds.annulus (a / 4) (2 *
      b))
    (j : PolarCharts.Index)
    (hj : PhysicalGraphBounds.scaledRadial L.val.1 w ∈ PolarCharts.chartDomain (a / 4) j) :
    LocalPhysicalCopyBounds.slotSlow (c.withChart j) (a / 4) h L.val.1 r0 w ∈ carrierRegion h a b
      := by
  have ha4 : 0 < a / 4 := by positivity
  have hrel := PhysicalWaveSum.labelRegion_active_relation hregion
  have hs := PhysicalMeanJetBounds.graph_slow_normalized hh hh1 L.val.1 0 hw hrel.1 hrel.2
  have hn : ‖PhysicalGraphBounds.scaledRadial L.val.1 w‖ ≤ 2 * b := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hann.1
  have hl : a / 4 ≤ ‖PhysicalGraphBounds.scaledRadial L.val.1 w‖ := hann.2
  have hrlo := PolarCharts.norm_le_radius (PhysicalGraphBounds.scaledRadial L.val.1 w)
  have hrhi := PolarCharts.radius_le_two_norm (PhysicalGraphBounds.scaledRadial L.val.1 w)
  change ((PhysicalGraphBounds.slotMap (PolarCharts.chart (a / 4) j)
    (ChartScales.timeCoefficient h L.val.1) c.center r0
      (PhysicalGraphBounds.physicalLift h L.val.1 w)).1).1 ∈ Ioo (a / 8) (4 * b + 1) ∧ _
  rw [PhysicalGraphBounds.slotMap_formula, PhysicalGraphBounds.liftXY_physicalLift,
    chart_radius ha4 j hj]
  constructor
  · exact ⟨by linarith, by linarith⟩
  · simpa only [LocalPhysicalCopyBounds.slotSlow, PhysicalGraphBounds.slotMap_formula,
      PhysicalMeanJetBounds.graph, Function.comp_apply, commonLift_zero,
      PhysicalClassBounds.cylindricalMap, PhysicalClassBounds.slowFast_apply] using hs

/-- Support of one full native carrier implies closed label membership,
including the edge of the actual zero-extended coefficient. -/
theorem term_tsupport_labelRegion {H : ℕ} {K : Type*}
    {f : PhysicalCopyBounds.CopyFamily H K} {a b h r0 Z : ℝ} {gap : ℕ}
    (hr : LocalPhysicalCopyBounds.SupportData f a b h r0 Z gap)
    (hh : 0 < h) (hh1 : h < 1 / 2) (I : PhysicalWaveSum.WaveIndex H) (k : K)
    {w : SpaceTime} (hw : w ∈ PhysicalWaveSum.preterminal)
    (ht : w ∈ tsupport (f.term a h r0 I k)) :
    PhysicalWaveSum.physicalParams h w ∈ PhysicalWaveSum.labelRegion (CoordinateAlgebra.D h)
      I.1.val := by
  apply PhysicalWaveSum.closed_property_on_tsupport PhysicalWaveSum.preterminal_open hw
    (PhysicalWaveSum.physicalParams_continuousAt hh hh1 hw)
    (PhysicalWaveSum.labelRegion_closed _ _) ?_ ht
  intro y hy hny
  exact PhysicalWaveSum.physicalMask_support_subset _ _
    (hr.mask_support k I y hy (PhysicalWaveSum.globalWave_ne_zero_amp hny))


noncomputable def nativeSlow (y : Native) : PhysicalGraphBounds.Slow := (y.1, (y.2.1.2, y.2.1.1))

theorem slotSlow_eq_nativeSlow {a : ℝ} (ha : 0 < a) (c : PhysicalWaveSum.CarrierData)
    (h : ℝ) (n : ℕ) (r0 : ℝ) (j : PolarCharts.Index) (w : SpaceTime)
    (hj : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    LocalPhysicalCopyBounds.slotSlow (c.withChart j) a h n r0 w =
      nativeSlow (PhysicalMeanJetBounds.graph h n 0 w) := by
  have hxy : PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h n w) ∈
      PolarCharts.chartDomain a j := by simpa only [PhysicalGraphBounds.liftXY_physicalLift] using
        hj
  unfold LocalPhysicalCopyBounds.slotSlow
  rw [PhysicalGraphBounds.slotMap_formula]
  rw [PhysicalMeanJetBounds.graph, Function.comp_apply, commonLift_zero]
  change ((PolarCharts.chart a j (PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h n
    w))).1,
    PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w)) = _
  rw [chart_radius ha j hxy]
  rfl

noncomputable def nativePast : Set Native := {y | 0 < y.2.1.1}

theorem nativePast_open : IsOpen nativePast := isOpen_lt continuous_const continuous_snd.fst.fst

/-- Intersecting native cells with one closed slow support retains their
actual local finiteness and their disjointness. -/
noncomputable def restrictCells {E K : Type*} [TopologicalSpace E]
    (c : PeriodizedWaveBounds.Cells E K) (s : Set E) (hs : IsClosed s) :
    PeriodizedWaveBounds.Cells E K where
  carrier n k := c.carrier n k ∩ s
  closed n k := (c.closed n k).inter hs
  locallyFinite n := (c.locallyFinite n).subset (fun _ => inter_subset_left)
  unique n i j x hi hj := c.unique n i j x hi.1 hj.1

noncomputable def primitiveCore {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (f : SignedFamily U) (L : PhysicalWaveSum.BandLabel) : Set LiftPoint :=
  {x | ∃ hL : L ∈ f.active,
    (f.primary ⟨L.val, L.property, hL⟩).mask L.val.1 (cylinderZero x) ≠ 0 ∧
    (f.primary ⟨L.val, L.property, hL⟩).target L.val.1 (cylinderZero x) ≠ 0}

section NativeBounds

variable {D h : ℝ}
  (sys : PartitionedCovariance.SlotSystem D h ActualSignedGeometry.radialVector
    ActualSignedGeometry.temporalVector)
  (hh : 0 ≤ h) {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (f : SignedFamily U)

/-- The native cell is narrowed only by the support of the original mask
and target. This avoids asking for phase estimates outside their Prepared
region and does not change any coefficient. -/
noncomputable def localizedPotentialCells (i : Fin 3) :
    PhysicalCopyBounds.SupportCells (potentialFamily sys hh f i) where
  cells L := restrictCells ((potentialCells sys hh f i).cells L)
    (closure (primitiveCore f L)) isClosed_closure
  support I k x hx := by
    obtain ⟨hL, _, hm, ht⟩ := potential_amplitude_inputs sys hh f i k I x hx
    exact ⟨(potentialCells sys hh f i).support I k hx,
      subset_closure ⟨hL, hm, ht⟩⟩

noncomputable def localizedPressureCells :
    PhysicalCopyBounds.SupportCells (pressureFamily sys hh f) where
  cells L := restrictCells ((pressureCells sys hh f).cells L)
    (closure (primitiveCore f L)) isClosed_closure
  support I k x hx := by
    obtain ⟨hL, _, hm, ht⟩ := pressure_amplitude_inputs sys hh f k I x hx
    exact ⟨(pressureCells sys hh f).support I k hx,
      subset_closure ⟨hL, hm, ht⟩⟩

/-- The same selected profile functions on their genuine Prepared native
regions. Only the slow coordinate cover and native polynomial jets are
stored; no physical bound or carrier representation is an input. -/
structure NativeProfiles where
  region : PhysicalWaveSum.BandLabel → Set PhysicalGraphBounds.Slow
  region_open : ∀ L, IsOpen (region L)
  jets : PhaseJetBounds.PolynomialJets
    (PhysicalCopyBounds.copyBandDomain (fun (_ : Frequency) L => region L) (fun _ L => region_open
      L))
    (fun I p => ((extendedCarrier (h := h) f I.2 I.1).F p, (extendedCarrier (h := h) f I.2 I.1).G
      p))
  covers : ∀ L w, w ∈ PhysicalWaveSum.preterminal →
    PhysicalWaveSum.physicalParams h w ∈ PhysicalWaveSum.labelRegion (CoordinateAlgebra.D h) L.val →
    PhysicalGraphBounds.physicalLift h L.val.1 w ∈ closure (primitiveCore f L) →
    nativeSlow (PhysicalMeanJetBounds.graph h L.val.1 0 w) ∈ region L

/-- Qualitative regularity of the literal native cut sources. The moving
edge construction supplies these statements before any physical pullback. -/
structure NativeRegular : Prop where
  potential : ∀ I n, ContDiffOn ℝ ∞ (nativePotentialSource sys hh f I n) nativePast
  pressure : ∀ I n, ContDiffOn ℝ ∞ (nativePressureSource sys hh f I n) nativePast

variable {a b : ℝ} (ha : 0 < a) (hp : NativeProfiles (h := h) f)

noncomputable def potentialCarrier (i : Fin 3) :
    PhysicalCopyBounds.CarrierBounds (potentialFamily sys hh f i) (localizedPotentialCells sys hh f
      i)
      (a / 4) (2 * b) h sys.radius where
  region _ L := hp.region L
  open_region _ L := hp.region_open L
  jets := hp.jets
  contains _ I w hw hr _ hc j hj := by
    change LocalPhysicalCopyBounds.slotSlow ((extendedCarrier (h := h) f I.1 _).withChart j)
      (a / 4) h I.1.val.1 sys.radius w ∈ hp.region I.1
    rw [slotSlow_eq_nativeSlow (div_pos ha (by norm_num)) _ _ _ _ _ _ hj]
    apply hp.covers I.1 w hw hr
    simpa only [potentialFamily, commonLift_zero] using hc.2

noncomputable def pressureCarrier :
    PhysicalCopyBounds.CarrierBounds (pressureFamily sys hh f) (localizedPressureCells sys hh f)
      (a / 4) (2 * b) h sys.radius where
  region _ L := hp.region L
  open_region _ L := hp.region_open L
  jets := hp.jets
  contains _ I w hw hr _ hc j hj := by
    change LocalPhysicalCopyBounds.slotSlow ((extendedCarrier (h := h) f I.1 _).withChart j)
      (a / 4) h I.1.val.1 sys.radius w ∈ hp.region I.1
    rw [slotSlow_eq_nativeSlow (div_pos ha (by norm_num)) _ _ _ _ _ _ hj]
    apply hp.covers I.1 w hw hr
    simpa only [pressureFamily, commonLift_zero] using hc.2

noncomputable def liftedNativePast (a b : ℝ) : Set LiftPoint :=
  PhysicalClassBounds.cylindricalDomain (a / 4) (2 * b) ∩
    PhysicalClassBounds.cylindricalMap ⁻¹' nativePast

theorem liftedNativePast_open (a b : ℝ) : IsOpen (liftedNativePast a b) :=
  (PhysicalClassBounds.cylindricalDomain_open _ _).inter
    (nativePast_open.preimage CartesianCopySource.cylindricalMap_continuous)

variable (hn : NativeRegular sys hh f)

include hn ha

theorem potential_amplitude_smooth (i : Fin 3) (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1) :
    ContDiffOn ℝ ∞ ((potentialFamily sys hh f i).amplitude k I) (liftedNativePast a b) := by
  have hm : ContDiffOn ℝ ∞ PhysicalClassBounds.cylindricalMap (liftedNativePast a b) :=
    (PhysicalClassBounds.cylindricalMap_smooth (div_pos ha (by norm_num))).mono inter_subset_left
  have hsrc := (hn.potential (I, k) I.1.val.1).comp hm (fun _ hx => hx.2)
  have hrot : ContDiffOn ℝ ∞ (fun x : LiftPoint => CartesianCopySource.rotationMap
    (PhysicalGraphBounds.liftXY x))
      (liftedNativePast a b) :=
    CartesianCopySource.rotationMap_smooth.comp PhysicalGraphBounds.liftXY.contDiff.contDiffOn
      (fun _ hx => PhysicalClassBounds.cylindricalDomain_axisFree (div_pos ha (by norm_num)) hx.1)
  have hv := (ContinuousLinearMap.proj i : ComplexVector →L[ℝ] ℂ).contDiff.comp_contDiffOn
    (hrot.clm_apply hsrc)
  apply (hv.const_smul (ChartScales.Q I.1.val.1 ^ (-h))).congr
  intro x _
  exact potential_amplitude_eq_source sys hh f i k I x

theorem pressure_amplitude_smooth (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1) :
    ContDiffOn ℝ ∞ ((pressureFamily sys hh f).amplitude k I) (liftedNativePast a b) := by
  have hm : ContDiffOn ℝ ∞ PhysicalClassBounds.cylindricalMap (liftedNativePast a b) :=
    (PhysicalClassBounds.cylindricalMap_smooth (div_pos ha (by norm_num))).mono inter_subset_left
  have hsrc := (hn.pressure (I, k) I.1.val.1).comp hm (fun _ hx => hx.2)
  apply (hsrc.const_smul (ChartScales.Q I.1.val.1 ^ (-(2 * CoordinateAlgebra.A h)))).congr
  intro x _
  exact pressure_amplitude_eq_source sys hh f k I x

omit sys hh f hp hn in
theorem commonLift_mem_liftedNativePast (n : ℕ) {w : SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hann : PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus (a / 4) (2 * b)) :
    PhysicalWaveSum.commonLift h n 0 w ∈ liftedNativePast a b := by
  constructor
  · change a / 4 / 2 < ‖PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n 0 w)‖ ∧
      ‖PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n 0 w)‖ < 2 * b + 1
    rw [commonLift_zero, PhysicalGraphBounds.liftXY_physicalLift]
    have hb' : ‖PhysicalGraphBounds.scaledRadial n w‖ ≤ 2 * b := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hann.1
    have ha' : a / 4 ≤ ‖PhysicalGraphBounds.scaledRadial n w‖ := hann.2
    exact ⟨by linarith, by linarith⟩
  · exact PhysicalMeanJetBounds.graph_time_pos h n 0 hw

variable {s : StripData Native} (hloc : PrimitiveLocalization (h := h) f a b s)
  (G : ReferenceGeometry sys f) (hh0 : 0 < h) (hh1 : h < 1 / 2) (hb : 0 < b)

include hp hloc G hh0 hh1 hb

theorem potentialSmooth (i : Fin 3) :
    LocalPhysicalCopyBounds.SmoothData (potentialFamily sys hh f i) (a / 4) h sys.radius := by
  let hr := potential_support sys hh f hloc G hh0 hh1 ha hb i
  constructor
  · intro k I w hw ht
    exact LocalPhysicalCopyBounds.SmoothNear.of_open (liftedNativePast_open a b)
      (potential_amplitude_smooth sys hh f ha hn i k I)
      (commonLift_mem_liftedNativePast ha _ hw (hr.tsupport_geometry I k ht).1)
  · intro k I w hw ht j hj
    have hc := (localizedPotentialCells sys hh f i).term_tsupport_mem
      (div_pos ha (by norm_num)) I k (hr.tsupport_geometry I k ht).1 ht
    have hl := term_tsupport_labelRegion hr hh0 hh1 I k hw ht
    have hp' := hp.covers I.1 w hw hl
      (by simpa only [potentialFamily, commonLift_zero] using hc.2)
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

theorem pressureSmooth :
    LocalPhysicalCopyBounds.SmoothData (pressureFamily sys hh f) (a / 4) h sys.radius := by
  let hr := pressure_support sys hh f hloc G hh0 hh1 ha hb
  constructor
  · intro k I w hw ht
    exact LocalPhysicalCopyBounds.SmoothNear.of_open (liftedNativePast_open a b)
      (pressure_amplitude_smooth sys hh f ha hn k I)
      (commonLift_mem_liftedNativePast ha _ hw (hr.tsupport_geometry I k ht).1)
  · intro k I w hw ht j hj
    have hc := (localizedPressureCells sys hh f).term_tsupport_mem
      (div_pos ha (by norm_num)) I k (hr.tsupport_geometry I k ht).1 ht
    have hl := term_tsupport_labelRegion hr hh0 hh1 I k hw ht
    have hp' := hp.covers I.1 w hw hl
      (by simpa only [pressureFamily, commonLift_zero] using hc.2)
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

end NativeBounds

/-! ## From native source estimates to actual physical wave data -/

/-- Taking all three components preserves one constant before the component,
label, copy, and band indices. -/
theorem componentSourceBounds {ι X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {s : StripData X} {w : ι → ℕ → X → ℝ} {h α : ℝ}
    {f : ι → ℕ → X → ComplexVector}
    (hf : LocalPhysicalCopyBounds.LocalSourceBounds s h α w f) :
    LocalPhysicalCopyBounds.LocalSourceBounds s h α (fun q : Fin 3 × ι => w q.2)
      (fun q n x => f q.2 n x q.1) := by
  refine ⟨⟨fun q => hf.uniform.weight_nonneg q.2,
    fun q n => (ContinuousLinearMap.proj q.1 : ComplexVector →L[ℝ] ℂ).contDiff.comp_contDiffOn
      (hf.uniform.smooth q.2 n), ?_⟩,
    hf.flat_geometry, ?_, hf.epsilon_eq, hf.slow_le⟩
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.uniform.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro q n x hx j hj
    have hc := ((hf.uniform.smooth q.2 n).contDiffAt (s.isOpen_domain.mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
    have hproj : ‖(ContinuousLinearMap.proj q.1 : ComplexVector →L[ℝ] ℂ)‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      simp only [one_mul]
      exact norm_le_pi_norm v q.1
    exact (PhysicalWaveSum.norm_jet_linear_comp_at hc (ContinuousLinearMap.proj q.1)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hproj).trans (hb q.2 n x hx j hj))
  · obtain ⟨c, hc, hb⟩ := hf.weight_le
    exact ⟨c, hc, fun q => hb q.2⟩

/-- An identity source chart, with its closure property derived from the
actual amplitude support. No physical derivative bound is an input. -/
noncomputable def identitySourceChart {N : ℕ} {K I : Type}
    (f : PhysicalCopyBounds.CopyFamily N K) (cells : PhysicalCopyBounds.SupportCells f)
    {a b h r Z σ : ℝ} {gap : ℕ} (ha : 0 < a)
    (hs : LocalPhysicalCopyBounds.SupportData f a b h r Z gap)
    (s : StripData LiftPoint) (source : I → ℕ → LiftPoint → ℂ)
    (idx : K → PhysicalWaveSum.WaveIndex N → I)
    (he : ∀ k J x, f.amplitude k J x =
      ChartScales.Q J.1.val.1 ^ σ • source (idx k J) J.1.val.1 x)
    (hd : ∀ k J x, f.amplitude k J x ≠ 0 → x ∈ s.domain) :
    LocalPhysicalCopyBounds.CommonChart f cells a b h r σ source where
  sourceIndex := idx
  map _ _ := id
  domain _ _ := s.domain
  open_domain _ _ := s.isOpen_domain
  smooth _ _ := contDiffOn_id
  positive_jets m := by
    refine ⟨1, le_rfl, 0, ?_⟩
    intro k J x hx j hj hjm
    simp only [pow_zero, mul_one]
    exact (PhysicalGraphBounds.norm_positive_jet_linear_le
        (ContinuousLinearMap.id ℝ LiftPoint) x hj).trans (by simp)
  amplitude_eq k J x _ := he k J x
  contains k J z _ _ _ _ hz := by
    have hrad := (hs.tsupport_geometry J k hz).1
    have hm := (PhysicalWaveSum.commonLift_smoothAt h J.1.val.1 (f.gap J.1)
      (PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha
        hrad))).continuousAt
    exact hm.continuousWithinAt.mem_closure hz
      (fun y hy => hd k J _ (PhysicalWaveSum.globalWave_ne_zero_amp hy))

section WaveData

variable {D h : ℝ}
  (sys : PartitionedCovariance.SlotSystem D h ActualSignedGeometry.radialVector
    ActualSignedGeometry.temporalVector)
  (hh : 0 ≤ h) {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (f : SignedFamily U)
  {a b : ℝ} {s : StripData Native} (hloc : PrimitiveLocalization (h := h) f a b s)
  (G : ReferenceGeometry sys f) (hh0 : 0 < h) (hh1 : h < 1 / 2)
  (ha : 0 < a) (hb : 0 < b)

include hloc hh0 hh1 ha hb

theorem potential_source_domain (i : Fin 3) (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1)
    (x : LiftPoint) (hx : (potentialFamily sys hh f i).amplitude k I x ≠ 0) :
    x ∈ (CartesianCopySource.pullStrip s (a / 4) (2 * b) (div_pos ha (by norm_num))).domain := by
  obtain ⟨hL, _, hm, ht⟩ := potential_amplitude_inputs sys hh f i k I x hx
  have hg := primitive_annulus (f := f) hloc hh0 hh1 ha hb ⟨I.1.val, I.1.property, hL⟩ x hm ht
  refine ⟨?_, primitive_domain (f := f) hloc ⟨I.1.val, I.1.property, hL⟩ x hm ht⟩
  have hu : ‖PhysicalGraphBounds.liftXY x‖ ≤ 2 * b := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hg.1.1
  have hl : a / 4 ≤ ‖PhysicalGraphBounds.liftXY x‖ := hg.1.2
  exact ⟨by change a / 4 / 2 < _; linarith, by change _ < 2 * b + 1; linarith⟩

theorem pressure_source_domain (k : Frequency) (I : PhysicalWaveSum.WaveIndex 1)
    (x : LiftPoint) (hx : (pressureFamily sys hh f).amplitude k I x ≠ 0) :
    x ∈ (CartesianCopySource.pullStrip s (a / 4) (2 * b) (div_pos ha (by norm_num))).domain := by
  obtain ⟨hL, _, hm, ht⟩ := pressure_amplitude_inputs sys hh f k I x hx
  have hg := primitive_annulus (f := f) hloc hh0 hh1 ha hb ⟨I.1.val, I.1.property, hL⟩ x hm ht
  refine ⟨?_, primitive_domain (f := f) hloc ⟨I.1.val, I.1.property, hL⟩ x hm ht⟩
  have hu : ‖PhysicalGraphBounds.liftXY x‖ ≤ 2 * b := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hg.1.1
  have hl : a / 4 ≤ ‖PhysicalGraphBounds.liftXY x‖ := hg.1.2
  exact ⟨by change a / 4 / 2 < _; linarith, by change _ < 2 * b + 1; linarith⟩

omit sys hh hloc G hh0 hh1 ha hb in
theorem carrier_frequencies {P : ℝ} (hP : 1 ≤ P)
    (hf : ∀ L : NativeLabel f.active,
      |((f.primary L).pulse (f.column L)).phase.p L.val.1| ≤ P ∧
      |((f.primary L).pulse (f.column L)).phase.pz L.val.1| ≤ P ∧
      |((f.primary L).pulse (f.column L)).phase.x0 L.val.1| ≤ P)
    (k : Frequency) (L : PhysicalWaveSum.BandLabel) :
    |(extendedCarrier (h := h) f L k).angular| ≤ P ∧
    |(extendedCarrier (h := h) f L k).axial| ≤ P ∧
    |(extendedCarrier (h := h) f L k).radial| ≤ P := by
  by_cases hL : L ∈ f.active
  · simpa only [extendedCarrier, dite_eq_left hL, selectedCarrier, carrier] using
      hf ⟨L.val, L.property, hL⟩
  · simp only [extendedCarrier, dite_eq_right hL, carrier, abs_zero]
    exact ⟨le_trans zero_le_one hP, le_trans zero_le_one hP, le_trans zero_le_one hP⟩

variable (hp : NativeProfiles (h := h) f) (hn : NativeRegular sys hh f)
  {P : ℝ} (hP : 1 ≤ P)
  (hf : ∀ L : NativeLabel f.active,
      |((f.primary L).pulse (f.column L)).phase.p L.val.1| ≤ P ∧
      |((f.primary L).pulse (f.column L)).phase.pz L.val.1| ≤ P ∧
      |((f.primary L).pulse (f.column L)).phase.x0 L.val.1| ≤ P)
  {α : ℝ} {w : SourceIndex → ℕ → Native → ℝ}

/-- The physical potential estimate is constructed from the literal cut
native potential, Cartesian rotation, and the actual copy geometry. -/
noncomputable def potentialWaveData
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds s h α w (nativePotentialSource sys hh f)) :
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
  copies := potentialFamily sys hh f
  cells := localizedPotentialCells sys hh f
  chart i := identitySourceChart _ _ (div_pos ha (by norm_num))
    (potential_support sys hh f hloc G hh0 hh1 ha hb i) _ _ (fun k I => (i, I, k))
    (potential_amplitude_eq_source sys hh f i)
    (potential_source_domain sys hh f hloc hh0 hh1 ha hb i)
  chart_maps _ _ _ := fun _ hx => hx
  carrier := potentialCarrier sys hh f ha hp
  support := potential_support sys hh f hloc G hh0 hh1 ha hb
  smooth := potentialSmooth sys hh f ha hp hn hloc G hh0 hh1 hb
  frequencies _ := carrier_frequencies f hP hf

/-- Pressure retains its own physical factor, exactly once. -/
noncomputable def pressureWaveData
    (hs : LocalPhysicalCopyBounds.LocalSourceBounds s h α w (nativePressureSource sys hh f)) :
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
  source_bounds := CartesianCopySource.sourceBounds_pullback (b := 2 * b)
    (div_pos ha (by norm_num)) hs
  copies _ := pressureFamily sys hh f
  cells _ := localizedPressureCells sys hh f
  chart _ := identitySourceChart _ _ (div_pos ha (by norm_num))
    (pressure_support sys hh f hloc G hh0 hh1 ha hb) _ _ (fun k I => (I, k))
    (pressure_amplitude_eq_source sys hh f)
    (pressure_source_domain sys hh f hloc hh0 hh1 ha hb)
  chart_maps _ _ _ := fun _ hx => hx
  carrier _ := pressureCarrier sys hh f ha hp
  support _ := pressure_support sys hh f hloc G hh0 hh1 ha hb
  smooth _ := pressureSmooth sys hh f ha hp hn hloc G hh0 hh1 hb
  frequencies _ := carrier_frequencies f hP hf

variable
  (hpotential : LocalPhysicalCopyBounds.LocalSourceBounds s h α w (nativePotentialSource sys hh f))
  (hpressure : LocalPhysicalCopyBounds.LocalSourceBounds s h α w (nativePressureSource sys hh f))

theorem potentialWaveData_vector :
    (potentialWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpotential).vector =
      PhysicalCopyBounds.vectorSum (potentialFamily sys hh f) (a / 4) h sys.radius := rfl

theorem pressureWaveData_pressure :
    (pressureWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpressure).pressure =
      fun x => ((pressureFamily sys hh f).sum (a / 4) h sys.radius x).re := rfl

theorem potentialWaveData_copyPotential :
    (potentialWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpotential).vector =
      (copyPotential sys hh f hloc G hh0 hh1 ha hb).field := rfl

theorem potentialWaveData_outer :
    (potentialWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpotential).upperRadius =
      2 * b := rfl

theorem pressureWaveData_outer :
    (pressureWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpressure).upperRadius =
      2 * b := rfl

/- Every fixed physical jet is controlled by the supplied native exponent,
with the physical potential scaling retained exactly. -/
include G hp hn hP hf hpotential in
theorem potential_physical_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h x ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (PhysicalCopyBounds.vectorSum (potentialFamily sys hh f) (a / 4) h sys.radius) x‖ ≤
        C * PhysicalWaveSum.physicalQ h x ^
          (h * α - PhysicalClassBounds.physicalLoss h (-h) m) :=
  (potentialWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpotential).vector_bound hh0 hh1 m

include G hp hn hP hf hpressure in
theorem pressure_physical_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h x ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (fun y => ((pressureFamily sys hh f).sum (a / 4) h sys.radius y).re) x‖ ≤
        C * PhysicalWaveSum.physicalQ h x ^
          (h * α - PhysicalClassBounds.physicalLoss h (-(2 * CoordinateAlgebra.A h)) m) :=
  (pressureWaveData sys hh f hloc G hh0 hh1 ha hb hp hn hP hf hpressure).pressure_bound hh0 hh1 m

end WaveData

/-! ## Cartesian germs of the original reference fields -/

theorem polarCoordinates_backward {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    {x : SpaceTime} (hx : PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a j) :
    ((PhysicalCurlCovariance.polarCoordinates a j x).1,
      CylindricalResidual.chart (PhysicalCurlCovariance.polarCoordinates a j x).2) = x := by
  have hp := PolarCharts.polar_chart ha j hx
  refine Prod.ext rfl ?_
  ext i
  fin_cases i
  · simpa [PhysicalCurlCovariance.polarCoordinates, PhysicalCurlCovariance.polarInput,
      CylindricalResidual.chart, AxisymmetricResidual.pack, coordinateVector,
      PiLp.single_apply, PolarCharts.polar, PhysicalGraphBounds.radialProjection_apply]
      using congrArg Prod.fst hp
  · simpa [PhysicalCurlCovariance.polarCoordinates, PhysicalCurlCovariance.polarInput,
      CylindricalResidual.chart, AxisymmetricResidual.pack, coordinateVector,
      PiLp.single_apply, PolarCharts.polar, PhysicalGraphBounds.radialProjection_apply]
      using congrArg Prod.snd hp
  · simp [PhysicalCurlCovariance.polarCoordinates, CylindricalResidual.chart]

theorem polarCoordinates_valid {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    {x : SpaceTime} (hx : PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain a j) :
    PhysicalCurlCovariance.polarCoordinates a j x ∈ PhysicalCurlCovariance.validCylindrical a j :=
      by
  have hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection x) := by
    rw [← PolarCharts.radius_rotate j]
    apply PolarCharts.radius_pos_of_fst_pos
    have hx' : a / 4 < (PolarCharts.rotate j (PhysicalGraphBounds.radialProjection x)).1 := hx
    linarith
  change 0 < (PhysicalCurlCovariance.polarCoordinates a j x).2 0 ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rwa [PhysicalCurlCovariance.polarCoordinates_radius ha j hx]
  · simp only [PhysicalCurlCovariance.polarCoordinates, AxisymmetricResidual.pack_one,
      PhysicalCurlCovariance.polarInput, PolarCharts.chart_eq_localChart ha j hx,
      PolarCharts.localChart_apply, add_sub_cancel_right]
    exact ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  · simpa only [PhysicalCurlCovariance.polarCoordinates, AxisymmetricResidual.pack_zero,
      AxisymmetricResidual.pack_one, PhysicalCurlCovariance.polarInput, Prod.eta,
      PolarCharts.polar_chart ha j hx] using hx

section ReferenceGerms

variable {D h : ℝ}
  (sys : PartitionedCovariance.SlotSystem D h ActualSignedGeometry.radialVector
    ActualSignedGeometry.temporalVector)
  (hh : 0 ≤ h) {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow} (f : SignedFamily U)

noncomputable def labelPotential (L : NativeLabel f.active) (a : ℝ) : VelocityField :=
  fun x => PhysicalCurlCovariance.realVector (fun i =>
    (potentialFamily sys hh f i).periodized a h sys.radius (positiveIndex L) x)

noncomputable def labelPressure (L : NativeLabel f.active) (a : ℝ) : PressureField :=
  fun x => ((pressureFamily sys hh f).periodized a h sys.radius (positiveIndex L) x).re

/-- Only coordinate domains and the original native phase domain occur in
this set. Its definition contains no output-field equality. -/
noncomputable def referencePatch (L : NativeLabel f.active) (a b delta : ℝ)
    (j : PolarCharts.Index) : Set SpaceTime :=
  {x | PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain delta j ∧
    PhysicalGraphBounds.scaledRadial L.val.1 x ∈ PhysicalGraphBounds.annulus a b ∧
    PhysicalGraphBounds.scaledRadial L.val.1 x ∈ PolarCharts.chartDomain a j ∧
    (PhysicalResidualBridge.commonGraph (ChartScales.Q L.val.1) h
      (ChartScales.nativeIndex h L.val.1)).map (PhysicalCurlCovariance.polarCoordinates delta j x) ∈
        (f.primary L).strip.domain}

variable (G : ReferenceGeometry sys f) (L : NativeLabel f.active)
  (hPhi : ContDiffOn ℝ ∞ ((f.primary L).base.phase L.val.1) (f.primary L).strip.domain)
  {a b delta : ℝ} (ha : 0 < a) (hd : 0 < delta) (j : PolarCharts.Index)

include G ha hd

include hPhi in
theorem labelPotential_eq_reference {x : SpaceTime}
    (hx : x ∈ referencePatch (h := h) f L a b delta j) :
    labelPotential sys hh f L a x =
      ActualPeriodizedSignedRealization.physicalPotential (f.primary L)
        (layout sys hh L.val L.property 0) (f.view L) (f.state L) (f.column L) delta x := by
  let z := PhysicalCurlCovariance.polarCoordinates delta j x
  have hz : z ∈ PhysicalCurlCovariance.validCylindrical delta j := polarCoordinates_valid hd j hx.1
  have he : (z.1, CylindricalResidual.chart z.2) = x := polarCoordinates_backward hd j hx.1
  ext i
  simp only [labelPotential, PhysicalCurlCovariance.realVector_apply]
  have hb' : PhysicalGraphBounds.scaledRadial L.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PhysicalGraphBounds.annulus a b := by simpa only [he] using hx.2.1
  have hj' : PhysicalGraphBounds.scaledRadial L.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain a j := by simpa only [he] using hx.2.2.1
  have H := potential_periodized_physical sys hh f G L i hPhi ha hd j z hz hx.2.2.2 hb' hj'
  simp only [he] at H
  exact H

theorem labelPressure_eq_reference {x : SpaceTime}
    (hx : x ∈ referencePatch (h := h) f L a b delta j) :
    labelPressure sys hh f L a x =
      ActualPeriodizedSignedRealization.physicalPressure (f.primary L)
        (layout sys hh L.val L.property 0) (f.view L) (f.state L) (f.column L) delta x := by
  let z := PhysicalCurlCovariance.polarCoordinates delta j x
  have hz : z ∈ PhysicalCurlCovariance.validCylindrical delta j := polarCoordinates_valid hd j hx.1
  have he : (z.1, CylindricalResidual.chart z.2) = x := polarCoordinates_backward hd j hx.1
  have hb' : PhysicalGraphBounds.scaledRadial L.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PhysicalGraphBounds.annulus a b := by simpa only [he] using hx.2.1
  have hj' : PhysicalGraphBounds.scaledRadial L.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain a j := by simpa only [he] using hx.2.2.1
  have H := pressure_periodized_physical sys hh f G L ha hd j z hz hb' hj'
  simp only [he] at H
  exact H

include hPhi in
theorem labelPotential_germ {x : SpaceTime}
    (hx : x ∈ interior (referencePatch (h := h) f L a b delta j)) :
    labelPotential sys hh f L a =ᶠ[𝓝 x]
      ActualPeriodizedSignedRealization.physicalPotential (f.primary L)
        (layout sys hh L.val L.property 0) (f.view L) (f.state L) (f.column L) delta :=
  eventually_of_mem (isOpen_interior.mem_nhds hx) (fun _ hy =>
    labelPotential_eq_reference sys hh f G L hPhi ha hd j (interior_subset hy))

theorem labelPressure_germ {x : SpaceTime}
    (hx : x ∈ interior (referencePatch (h := h) f L a b delta j)) :
    labelPressure sys hh f L a =ᶠ[𝓝 x]
      ActualPeriodizedSignedRealization.physicalPressure (f.primary L)
        (layout sys hh L.val L.property 0) (f.view L) (f.state L) (f.column L) delta :=
  eventually_of_mem (isOpen_interior.mem_nhds hx) (fun _ hy =>
    labelPressure_eq_reference sys hh f G L ha hd j (interior_subset hy))

include hPhi in
theorem labelVelocity_eq_reference {x : SpaceTime}
    (hx : x ∈ interior (referencePatch (h := h) f L a b delta j)) :
    SpatialCurl.spatialCurl (labelPotential sys hh f L a) x =
      ActualPeriodizedSignedRealization.physicalVelocity (f.primary L)
        (layout sys hh L.val L.property 0) (f.view L) (f.state L) (f.column L) delta x :=
  PhysicalCurlCovariance.spatialCurl_congr (labelPotential_germ sys hh f G L hPhi ha hd j hx)

include hPhi in
theorem labelPotential_jets_eq_reference {x : SpaceTime}
    (hx : x ∈ interior (referencePatch (h := h) f L a b delta j)) (m : ℕ) :
    iteratedFDeriv ℝ m (labelPotential sys hh f L a) x =
      iteratedFDeriv ℝ m (ActualPeriodizedSignedRealization.physicalPotential (f.primary L)
        (layout sys hh L.val L.property 0) (f.view L) (f.state L) (f.column L) delta) x :=
  PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
    (labelPotential_germ sys hh f G L hPhi ha hd j hx) m

end ReferenceGerms

end NavierStokes.ActualSignedPhysicalData
