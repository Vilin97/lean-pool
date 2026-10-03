/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.GradientSpace
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.UnitCube
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Transfer of initial data to the unit torus

The datum is only assumed square-integrable on the open unit cube and need not be
periodic. This module transports that representative to the quotient torus through its canonical
`Ioc` representative, using the fact that the open and half-open cells agree almost everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance frozenInitialMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance frozenInitialMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance frozenInitialProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- A `L²` datum on the open unit square induces an `L²` datum on the quotient torus. -/
theorem frozenInitialData_memLp_torus {θ₀ : Vec 2 → ℝ}
    (hθ₀ : MemL2On AVenhance.unitCube θ₀) :
    MemLp (AVenhance.Infra.Torus.periodicToTorus θ₀) 2 (volume : Measure Torus) := by
  let cell : Set (Vec 2) := AVenhance.Infra.Torus.unitCell 2
  have hcellMeas : MeasurableSet cell := by
    exact AVenhance.Infra.Torus.measurableSet_unitCell 2
  have hcellLe : (volume : Measure (Vec 2)).restrict cell ≤
      (volume : Measure (Vec 2)).restrict AVenhance.unitCube := by
    exact Measure.restrict_mono_ae
      AVenhance.Infra.Torus.unitCell_ae_eq_unitCube.le
  have hθcell : MemLp θ₀ 2 ((volume : Measure (Vec 2)).restrict cell) :=
    hθ₀.mono_measure hcellLe
  let cellSubtype := {x : Vec 2 // x ∈ cell}
  let cellMeasure : Measure cellSubtype :=
    volume.comap (Subtype.val : cellSubtype → Vec 2)
  have hmeasureCell : MeasurePreserving (fun x : cellSubtype => (x : Vec 2))
      cellMeasure ((volume : Measure (Vec 2)).restrict cell) := by
    change MeasurePreserving Subtype.val
      ((volume : Measure (Vec 2)).comap (Subtype.val : cellSubtype → Vec 2))
      ((volume : Measure (Vec 2)).restrict cell)
    exact ⟨measurable_subtype_coe, map_comap_subtype_coe hcellMeas volume⟩
  have hθsubtype : MemLp (fun x : cellSubtype => θ₀ x.1) 2 cellMeasure := by
    simpa [cellMeasure, Function.comp_def] using hθcell.comp_measurePreserving hmeasureCell
  let equiv := UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ))
  have hmeasureTorus : MeasurePreserving equiv (volume : Measure Torus) cellMeasure := by
    change MeasurePreserving equiv (volume : Measure Torus)
      ((volume : Measure (Vec 2)).comap (Subtype.val : cellSubtype → Vec 2))
    simpa [equiv, cell, AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt] using
      UnitAddTorus.measurePreserving_equivPiIoc (a := fun _ : Fin 2 => (0 : ℝ))
  have hcomp := hθsubtype.comp_measurePreserving hmeasureTorus
  have hfun : (fun x : Torus => θ₀ (equiv x).1) =
      AVenhance.Infra.Torus.periodicToTorus θ₀ := by
    funext x
    rfl
  exact hfun ▸ hcomp

end AVenhance.Infra.Parabolic.FourierGalerkin

end
