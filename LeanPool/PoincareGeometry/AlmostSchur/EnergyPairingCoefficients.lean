/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.GradientL2
public import LeanPool.PoincareGeometry.RellichKondrachov.Geometry.Manifold.Sobolev.Localization

/-! # Continuous coefficients for intrinsic energy reconstruction

Only C¹ regularity of the scalar function is used: its gradient is a continuous
bundle section. No derivative of that gradient is taken.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set MeasureTheory
open scoped Manifold ContDiff Topology
open RellichKondrachov.Geometry.Manifold.Sobolev FiniteChartData

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local instance : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- Coordinate components of a continuous tangent section are continuous on
the chart target; C¹ regularity of the section is unnecessary. -/
theorem continuousOn_coordinateVectorField (c : M) (X : Π x, TangentSpace I x)
    (hX : Continuous (fun x => (⟨x, X x⟩ : TotalSpace E (TangentSpace I)))) :
    ContinuousOn (coordinateVectorField (I := I) c X) (extChartAt I c).target := by
  let e := trivializationAt E (TangentSpace I) c
  have hsec := hX.comp_continuousOn (continuousOn_extChartAt_symm (I := I) c)
  have ht := e.continuousOn.comp hsec (fun z hz => e.mem_source.mpr (by
    change (extChartAt I c).symm z ∈ (chartAt H c).source
    simpa only [extChartAt_source] using (extChartAt I c).map_target hz))
  apply ht.snd.congr
  intro z hz
  exact (e.continuousLinearMapAt_apply_of_mem (R := ℝ) (by
    change (extChartAt I c).symm z ∈ (chartAt H c).source
    simpa only [extChartAt_source] using (extChartAt I c).map_target hz) _)

/-- A C¹ scalar function has continuous coordinate gradient components. -/
theorem continuousOn_coordinateVectorField_gradient (c : M) {g : M → ℝ}
    (hg : CMDiff 1 g) :
    ContinuousOn (coordinateVectorField (I := I) c (gradient (I := I) g))
      (extChartAt I c).target :=
  continuousOn_coordinateVectorField c _ (contMDiff_gradient (I := I) 0 hg).continuous

variable [T2Space M] [CompactSpace M]

/-- The cutoff and true coordinate density, multiplied by one coordinate
component of the intrinsic gradient. The cutoff already vanishes off-chart. -/
def energyPairingCoeff (d : FiniteChartData (H := H) (M := M) I)
    (i : d.ι) (g : M → ℝ) (v : E) (z : E) : ℝ :=
  localize (d := d) (fun _ => (1 : ℝ)) i z *
    matrixDensity (coordinateMetric (I := I) (stdOrthonormalBasis ℝ E).toBasis (d.center i) z) *
    inner ℝ v (coordinateVectorField (I := I) (d.center i) (gradient (I := I) g) z)

/-- The coefficient is supported in the fixed compact coordinate cutoff support. -/
theorem tsupport_energyPairingCoeff_subset (d : FiniteChartData (H := H) (M := M) I)
    (i : d.ι) (g : M → ℝ) (v : E) :
    tsupport (energyPairingCoeff d i g v) ⊆ rhoSupportImage (d := d) i := by
  exact tsupport_mul_subset_left.trans
    (tsupport_mul_subset_left.trans
      (tsupport_localize_subset_rhoSupportImage (d := d) (fun _ => (1 : ℝ)) i))

theorem hasCompactSupport_energyPairingCoeff (d : FiniteChartData (H := H) (M := M) I)
    (i : d.ι) (g : M → ℝ) (v : E) : HasCompactSupport (energyPairingCoeff d i g v) :=
  (isCompact_rhoSupportImage (d := d) i).of_isClosed_subset isClosed_closure
    (tsupport_energyPairingCoeff_subset d i g v)

/-- Zero extension is continuous because the cutoff support lies inside the
chart target. The gradient itself is only required to be continuous. -/
theorem continuous_energyPairingCoeff (d : FiniteChartData (H := H) (M := M) I)
    (i : d.ι) {g : M → ℝ} (hg : CMDiff 1 g) (v : E) :
    Continuous (energyPairingCoeff d i g v) := by
  apply ContinuousOn.continuous_of_tsupport_subset _ (isOpen_extChartAt_target (d.center i))
    ((tsupport_energyPairingCoeff_subset d i g v).trans (rhoSupportImage_subset_target (d := d) i))
  exact (((localize_mem_C1c (d := d) contMDiff_const i).1.continuous.continuousOn).mul
    (continuousOn_coordinateDensity (stdOrthonormalBasis ℝ E).toBasis (d.center i))).mul
      (continuousOn_const.inner (continuousOn_coordinateVectorField_gradient (d.center i) hg))

variable [MeasurableSpace E] [BorelSpace E]

/-- Each reconstruction coefficient is a genuine Euclidean L² function. -/
theorem memLp_energyPairingCoeff (d : FiniteChartData (H := H) (M := M) I)
    (i : d.ι) {g : M → ℝ} (hg : CMDiff 1 g) (v : E) :
    MemLp (energyPairingCoeff d i g v) 2 volume :=
  (continuous_energyPairingCoeff d i hg v).memLp_of_hasCompactSupport
    (hasCompactSupport_energyPairingCoeff d i g v)

end AlmostSchur
