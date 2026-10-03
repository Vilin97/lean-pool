/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ProductWeakSlices
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.UnitCube
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.TimeCube

/-!
# Euclidean representatives of the synchronized gradient limit

The product gradient determines a spatial torus `L²` section for almost every time. Pulling its
coordinate representatives back to the Euclidean cover gives periodic gradients with the cellwise
    `L²` bounds.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open Homogenization
open scoped Topology RealInnerProductSpace

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance gradientRepresentativeMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance gradientRepresentativeMeasureIsAddHaar : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance gradientRepresentativeProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

theorem ProductGradientRepresentative.realFourierModeAmbient_contDiff_withTop (N : ℕ)
    (j : Fin (RealFourierDimension N)) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (realFourierModeAmbient N
      ((realFourierIndexEquivFin N).symm j)) := by
  exact (realFourierModeAmbient_contDiff N
    ((realFourierIndexEquivFin N).symm j)).of_le le_top

theorem ProductGradientRepresentative.measurable_toUnitTorus_frozen :
    Measurable (AVenhance.Infra.Torus.toUnitTorus 2) := by
  apply measurable_pi_iff.2
  intro i
  exact (AddCircle.measurable_mk' (a := 1)).comp (measurable_pi_apply i)

/-- Pass from physical time-space to time times the torus, preserving time. -/
def physicalTimeTorusMap : ℝ × Vec 2 → ℝ × Torus := fun p =>
  (p.1, AVenhance.Infra.Torus.toUnitTorus 2 p.2)

/-- The Euclidean-to-torus map preserves measure on the spatial cell. -/
theorem measurePreserving_toUnitTorus_unitCube :
    MeasurePreserving (AVenhance.Infra.Torus.toUnitTorus 2)
      (volume.restrict AVenhance.unitCube) (volume : Measure Torus) := by
  let cell : Set (Vec 2) := AVenhance.Infra.Torus.unitCell 2
  let cellSubtype := {x : Vec 2 // x ∈ cell}
  let cellMeasure : Measure cellSubtype :=
    volume.comap (Subtype.val : cellSubtype → Vec 2)
  let equiv := UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ))
  have hcellMeas : MeasurableSet cell := AVenhance.Infra.Torus.measurableSet_unitCell 2
  have hmeasureCell : MeasurePreserving (Subtype.val : cellSubtype → Vec 2)
      cellMeasure ((volume : Measure (Vec 2)).restrict cell) := by
    change MeasurePreserving Subtype.val
      ((volume : Measure (Vec 2)).comap (Subtype.val : cellSubtype → Vec 2))
      ((volume : Measure (Vec 2)).restrict cell)
    exact ⟨measurable_subtype_coe, map_comap_subtype_coe hcellMeas volume⟩
  have hmeasureTorus : MeasurePreserving equiv (volume : Measure Torus) cellMeasure := by
    change MeasurePreserving equiv (volume : Measure Torus)
      ((volume : Measure (Vec 2)).comap (Subtype.val : cellSubtype → Vec 2))
    simpa [equiv, cell, AVenhance.Infra.Torus.unitCell,
      AVenhance.Infra.Torus.unitCellAt] using
      UnitAddTorus.measurePreserving_equivPiIoc (a := fun _ : Fin 2 => (0 : ℝ))
  have hequiv (x : cellSubtype) : equiv.symm x =
      AVenhance.Infra.Torus.toUnitTorus 2 x.1 := by
    apply equiv.injective
    apply Subtype.ext
    funext i
    rfl
  have hmapCell : Measure.map (AVenhance.Infra.Torus.toUnitTorus 2)
      ((volume : Measure (Vec 2)).restrict cell) = (volume : Measure Torus) := by
    rw [← hmeasureCell.map_eq, Measure.map_map
      ProductGradientRepresentative.measurable_toUnitTorus_frozen measurable_subtype_coe]
    have hfun : (AVenhance.Infra.Torus.toUnitTorus 2) ∘
        (Subtype.val : cellSubtype → Vec 2) = equiv.symm := by
      funext x
      exact (hequiv x).symm
    rw [hfun]
    exact hmeasureTorus.symm.map_eq
  have hcellCube : (volume : Measure (Vec 2)).restrict cell =
      (volume : Measure (Vec 2)).restrict AVenhance.unitCube := by
    exact le_antisymm
      (Measure.restrict_mono_ae AVenhance.Infra.Torus.unitCell_ae_eq_unitCube.le)
      (Measure.restrict_mono_ae AVenhance.Infra.Torus.unitCell_ae_eq_unitCube.ge)
  refine ⟨ProductGradientRepresentative.measurable_toUnitTorus_frozen, ?_⟩
  rw [← hcellCube, hmapCell]

/-- Pulling back a product-torus `L²` class to the spacetime cell preserves its
coordinatewise `L²` bounds. -/
theorem measurePreserving_physicalTimeTorusMap :
    MeasurePreserving physicalTimeTorusMap
      (volume.restrict AVenhance.timeCube)
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
  have htime : MeasurePreserving (id : ℝ → ℝ)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) GalerkinTimeMeasure := by
    refine ⟨measurable_id, ?_⟩
    change Measure.map id (volume.restrict (Set.Ioo (0 : ℝ) 1)) =
      volume.restrict (Set.Ioc (0 : ℝ) 1)
    rw [Measure.map_id]
    exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc
  have hproduct := htime.prod measurePreserving_toUnitTorus_unitCube
  have hsource : volume.restrict AVenhance.timeCube =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube) := by
    rw [AVenhance.timeCube, Measure.prod_restrict,
      ← Measure.volume_eq_prod ℝ (Vec 2)]
  refine ⟨by
      exact measurable_fst.prodMk
        (ProductGradientRepresentative.measurable_toUnitTorus_frozen.comp measurable_snd), ?_⟩
  rw [hsource]
  exact hproduct.map_eq

/-- The selected product-gradient representative, pulled back periodically to Euclidean space. -/
def synchronizedGradientRepresentative (G : GradientProductTimeL2) :
    ℝ → Vec 2 → Vec 2 := fun t x =>
      G (t, AVenhance.Infra.Torus.toUnitTorus 2 x)

/-- The selected Euclidean gradient representative is periodic at every time. -/
theorem synchronizedGradientRepresentative_periodic (G : GradientProductTimeL2) (t : ℝ) :
    AVenhance.IsZ2Periodic (synchronizedGradientRepresentative G t) := by
  have hperiodic : AVenhance.Infra.Torus.IsZdPeriodic
      (AVenhance.Infra.Torus.fromUnitTorus (fun y : Torus => G (t, y))) :=
    AVenhance.Infra.Torus.isZdPeriodic_fromUnitTorus _
  intro k x
  have h := (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen _).1 hperiodic k x
  ext i
  change (G (t, AVenhance.Infra.Torus.toUnitTorus 2
      (x + AVenhance.latticeShift k))).ofLp i =
    (G (t, AVenhance.Infra.Torus.toUnitTorus 2 x)).ofLp i
  exact congrArg (fun v : SpatialVector => v.ofLp i) h

/-- A coordinate of the selected gradient representative is square-integrable on the open unit
    cell whenever the product section is an `L²` slice. -/
theorem synchronizedGradientRepresentative_coordinate_memL2On
    (G : GradientProductTimeL2) (t : ℝ)
    (hsection : MemLp (fun y : Torus => G (t, y)) 2 (volume : Measure Torus))
    (i : Fin 2) :
    MemL2On AVenhance.unitCube
      (fun x => synchronizedGradientRepresentative G t x i) := by
  let coordinate : SpatialVector →L[ℝ] ℝ :=
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i
  exact (coordinate.comp_memLp' hsection).comp_measurePreserving
    measurePreserving_toUnitTorus_unitCube

/-- For almost every time, the synchronized Euclidean gradient has the coordinatewise
`L²` bound on the cell. -/
theorem synchronizedGradientRepresentative_gradMemL2On_ae
    (G : GradientProductTimeL2) :
    ∀ᵐ t ∂GalerkinTimeMeasure,
      GradMemL2On AVenhance.unitCube (synchronizedGradientRepresentative G t) := by
  have hsection := gradientProductTimeL2_memLp_sections G
  filter_upwards [hsection] with t ht
  intro i
  exact synchronizedGradientRepresentative_coordinate_memL2On G t ht i

/-- Every coordinate of the Euclidean representative belongs to the exact space-time
`L²` carrier. -/
theorem synchronizedGradientRepresentative_memLp_timeCube
    (G : GradientProductTimeL2) (i : Fin 2) :
    MemLp (fun p : ℝ × Vec 2 => synchronizedGradientRepresentative G p.1 p.2 i)
      2 (volume.restrict AVenhance.timeCube) := by
  let coordinate : SpatialVector →L[ℝ] ℝ :=
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i
  have hcoord : MemLp (fun p : ℝ × Torus => coordinate (G p)) 2
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) :=
    coordinate.comp_memLp' (Lp.memLp G)
  have hphysical := hcoord.comp_measurePreserving measurePreserving_physicalTimeTorusMap
  have heq : ((fun q : ℝ × Torus => coordinate (G q)) ∘ physicalTimeTorusMap) =
      fun p : ℝ × Vec 2 => synchronizedGradientRepresentative G p.1 p.2 i := by
    funext p
    simp [synchronizedGradientRepresentative, physicalTimeTorusMap, coordinate,
      PiLp.proj_apply]
  rw [← heq]
  exact hphysical

/-- The synchronized weak spatial derivative identities hold on one common full-measure set for
every real Fourier mode and both coordinates. This is the countable Fourier criterion needed for
the later periodic `H¹` closure argument. -/
theorem FrozenDriftProblem.synchronized_limit_realFourier_derivative_ae
    (P : FrozenDriftProblem) (σ : ℕ → ℕ)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2)
    (Uprod : ScalarProductTimeL2) (Gprod : GradientProductTimeL2)
    (hPathWeak : ∀ t v, Tendsto
      (fun n => inner ℝ (P.scalarPath (σ n) t) v) atTop
      (𝓝 (inner ℝ (u t) v)))
    (hUweak : ∀ v, Tendsto
      (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Uprod v)))
    (hGweak : ∀ v, Tendsto
      (fun n => inner ℝ (P.gradientProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Gprod v)))
    (hUcont : ∀ v, Continuous (fun t => inner ℝ (u t) v))
    (hUbound : ∀ t, ‖u t‖ ≤ P.scalarBound) :
    ∀ᵐ t ∂GalerkinTimeMeasure, ∀ i : Fin 2,
      ∀ N : ℕ, ∀ j : Fin (RealFourierDimension N),
        (∫ x : Torus, inner ℝ (Gprod (t, x))
          (scalarToSpatialGradientL2 i
            (smoothPeriodicTestL2
              (ProductGradientRepresentative.realFourierModeAmbient_contDiff_withTop N j)
              (realFourierModeAmbient_periodic N
                ((realFourierIndexEquivFin N).symm j))) x) ∂volume) =
          -inner ℝ (u (clampTimeToUnit t))
            (smoothPeriodicTestL2
              (productWeakGradient_coord_contDiff
                (ProductGradientRepresentative.realFourierModeAmbient_contDiff_withTop N j) i)
              (productWeakGradient_coord_periodic
                (ProductGradientRepresentative.realFourierModeAmbient_contDiff_withTop N j)
          (realFourierModeAmbient_periodic N
            ((realFourierIndexEquivFin N).symm j)) i)) := by
  let ι := Σ N : ℕ, Fin (RealFourierDimension N)
  let ψ : ι → Vec 2 → ℝ := fun a =>
    realFourierModeAmbient a.1 ((realFourierIndexEquivFin a.1).symm a.2)
  have hψ : ∀ a, ContDiff ℝ (↑(⊤ : ℕ∞)) (ψ a) := by
    intro a
    change ContDiff ℝ (↑(⊤ : ℕ∞))
      (realFourierModeAmbient a.1 ((realFourierIndexEquivFin a.1).symm a.2))
    exact ProductGradientRepresentative.realFourierModeAmbient_contDiff_withTop a.1 a.2
  have hperiodic : ∀ a, AVenhance.IsZ2Periodic (ψ a) := by
    intro a
    exact realFourierModeAmbient_periodic a.1
      ((realFourierIndexEquivFin a.1).symm a.2)
  have hcommon (i : Fin 2) : ∀ᵐ t ∂GalerkinTimeMeasure, ∀ a : ι,
      (∫ x : Torus, inner ℝ (Gprod (t, x))
        (scalarToSpatialGradientL2 i
          (smoothPeriodicTestL2 (hψ a) (hperiodic a)) x) ∂volume) =
        -inner ℝ (u (clampTimeToUnit t))
          (smoothPeriodicTestL2
            (productWeakGradient_coord_contDiff (hψ a) i)
            (productWeakGradient_coord_periodic (hψ a) (hperiodic a) i)) :=
    P.synchronized_limit_spatial_derivative_ae_countable σ u Uprod Gprod
      hPathWeak hUweak hGweak hUcont hUbound i ψ hψ hperiodic
  have hcombined : ∀ᵐ t ∂GalerkinTimeMeasure, ∀ i : Fin 2, ∀ a : ι,
      (∫ x : Torus, inner ℝ (Gprod (t, x))
        (scalarToSpatialGradientL2 i
          (smoothPeriodicTestL2 (hψ a) (hperiodic a)) x) ∂volume) =
        -inner ℝ (u (clampTimeToUnit t))
          (smoothPeriodicTestL2
            (productWeakGradient_coord_contDiff (hψ a) i)
            (productWeakGradient_coord_periodic (hψ a) (hperiodic a) i)) := by
    rw [ae_all_iff]
    intro i
    exact hcommon i
  simpa [ψ, ι, Sigma.forall] using hcombined

end AVenhance.Infra.Parabolic.FourierGalerkin

end
