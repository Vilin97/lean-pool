/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Frequency
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Modes
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Projection
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# The spatial `L²` gradient space for real Fourier cutoffs

This module places the explicitly differentiated real modes in the vector-valued torus `L²`
space and packages their finite synthesis as a continuous linear map. The Euclidean norm on the
two gradient coordinates is the `PiLp 2` norm, matching the gradient energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance gradientSpaceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance gradientSpaceMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance gradientSpaceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Euclidean two-vectors with their usual squared-sum norm. -/
abbrev SpatialVector := PiLp 2 (fun _ : Fin 2 => ℝ)

/-- The Hilbert space of square-integrable spatial vector fields on the unit torus. -/
abbrev SpatialGradientL2 := Lp SpatialVector 2 (volume : Measure Torus)

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def GradientSpace.closedCell : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem GradientSpace.isCompact_closedCell : IsCompact GradientSpace.closedCell := by
  simpa [GradientSpace.closedCell] using (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem GradientSpace.unitTorusRepresentative_mem_closedCell (x : Torus) :
    AVenhance.Infra.Torus.unitTorusRepresentative 2 x ∈ GradientSpace.closedCell := by
  simp only [GradientSpace.closedCell, Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  have hi : AVenhance.Infra.Torus.unitTorusRepresentative 2 x i ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa [AVenhance.Infra.Torus.unitTorusRepresentative] using
      (AddCircle.equivIoc (1 : ℝ) 0 (x i)).2
  exact ⟨le_of_lt hi.1, hi.2⟩

/-- Every real Fourier gradient mode is an element of vector-valued spatial `L²`. -/
theorem realFourierModeGradFin_memLp (N : ℕ) (i : Fin (RealFourierDimension N)) :
    MemLp (fun x : Torus =>
      (WithLp.toLp 2 (realFourierModeGradFin N i x) : SpatialVector))
      2 (volume : Measure Torus) := by
  let f : Vec 2 → SpatialVector := fun x =>
    WithLp.toLp 2
      (realFourierModeAmbientGrad N ((realFourierIndexEquivFin N).symm i) x)
  have hf : Continuous f := by
    exact PiLp.continuous_toLp 2 _ |>.comp (realFourierModeAmbientGrad_continuous N
      ((realFourierIndexEquivFin N).symm i))
  have hmeas : Measurable (fun x : Torus => f
      (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)) :=
    hf.measurable.comp (AVenhance.Infra.Torus.measurable_unitTorusRepresentative 2)
  have himage : Bornology.IsBounded (f '' GradientSpace.closedCell) :=
    (GradientSpace.isCompact_closedCell.image hf).isBounded
  obtain ⟨C, hCpos, hC⟩ := himage.subset_ball_lt 0 0
  apply MemLp.of_bound hmeas.aestronglyMeasurable C
  filter_upwards with x
  have hx : f (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) ∈ f '' GradientSpace.closedCell :=
    ⟨AVenhance.Infra.Torus.unitTorusRepresentative 2 x,
      GradientSpace.unitTorusRepresentative_mem_closedCell x, rfl⟩
  have hball := hC hx
  have hnorm : ‖f (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)‖ < C := by
    simpa [Metric.mem_ball, dist_eq_norm] using hball
  have hrepr : f (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) =
      WithLp.toLp 2 (realFourierModeGradFin N i x) := by
    simp [f, realFourierModeGradFin_eq_periodicToTorus,
      AVenhance.Infra.Torus.periodicToTorus]
  rw [hrepr]
  exact hnorm.le

/-- A real Fourier gradient mode, represented as an `L²` equivalence class. -/
noncomputable def realFourierModeGradL2 (N : ℕ)
    (i : Fin (RealFourierDimension N)) : SpatialGradientL2 :=
  (realFourierModeGradFin_memLp N i).toLp
    (fun x : Torus => WithLp.toLp 2 (realFourierModeGradFin N i x))

/-- Finite synthesis of the vector-valued gradient modes. -/
noncomputable def realFourierGradientMap (N : ℕ) :
    Coefficients (RealFourierDimension N) →L[ℝ] SpatialGradientL2 :=
  ∑ i : Fin (RealFourierDimension N),
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (RealFourierDimension N) => ℝ) i).smulRight
      (realFourierModeGradL2 N i)

@[simp]
theorem realFourierGradientMap_apply (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    realFourierGradientMap N c =
      ∑ i : Fin (RealFourierDimension N), (c i) • realFourierModeGradL2 N i := by
  simp [realFourierGradientMap, PiLp.proj_apply]

end AVenhance.Infra.Parabolic.FourierGalerkin

end
