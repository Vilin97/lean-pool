/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.CoordinatePolynomialMeasure
public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.FiniteProductCoordinateNormalForm
public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.ProjectiveFamily
public import Mathlib.MeasureTheory.Integral.CompactlySupported


/-!
# Compact-test transport for finite-set kernels

This file identifies the increasing-coordinate representation of a finite set with its ordinary
function space by a homeomorphism. It transports compactly supported tests across that
homeomorphism and rewrites their finite-set-kernel integrals as finite-time-kernel integrals.

Strong measurability of a compactly supported test follows from the shared uniform coordinate-
polynomial approximations. This avoids adding an `OpensMeasurableSpace` assumption on the finite
product. These declarations are finite-dimensional infrastructure; no statement about path space
is proved here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup

/-- The increasing-coordinate representation of paths on a finite time set, as a homeomorphism. -/
noncomputable def orderedPathToFiniteSetHomeomorph
    {alpha : Type*} [TopologicalSpace alpha] (I : Finset NNReal) :
    (Fin I.card → alpha) ≃ₜ (I → alpha) :=
  Homeomorph.piCongrLeft (Y := fun _ : I ↦ alpha) (I.orderIsoOfFin rfl).toEquiv

/-- The ordered-coordinate homeomorphism has underlying function `orderedPathToFiniteSet`. -/
@[simp]
theorem orderedPathToFiniteSetHomeomorph_apply
    {alpha : Type*} [TopologicalSpace alpha] (I : Finset NNReal)
    (path : Fin I.card → alpha) :
    orderedPathToFiniteSetHomeomorph I path = orderedPathToFiniteSet I path := by
  ext t
  change (Equiv.piCongrLeft (fun _ : I ↦ alpha) (I.orderIsoOfFin rfl).toEquiv path) t = _
  rw [Equiv.piCongrLeft_apply]
  simp only [orderedPathToFiniteSet]
  rw [eqRec_eq_cast, cast_eq]
  rfl

/-- Pull a compactly supported test on finite-set coordinates back to increasing coordinates. -/
noncomputable def pullbackFiniteSetCompactTest
    {alpha : Type*} [TopologicalSpace alpha] (I : Finset NNReal)
    (f : C_c(I → alpha, ℝ)) : C_c(Fin I.card → alpha, ℝ) :=
  f.comp (orderedPathToFiniteSetHomeomorph I).toCocompactMap

/-- Evaluation of a compact test pulled back to increasing coordinates. -/
@[simp]
theorem pullbackFiniteSetCompactTest_apply
    {alpha : Type*} [TopologicalSpace alpha] (I : Finset NNReal)
    (f : C_c(I → alpha, ℝ)) (path : Fin I.card → alpha) :
    pullbackFiniteSetCompactTest I f path = f (orderedPathToFiniteSet I path) := by
  rw [pullbackFiniteSetCompactTest]
  exact congr_arg f (orderedPathToFiniteSetHomeomorph_apply I path)

/-- Integration against the mapped ordered-coordinate law equals integration of the pulled-back
compact test. -/
theorem integral_map_orderedPathToFiniteSet
    {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
    (I : Finset NNReal) (f : C_c(I → alpha, ℝ))
    (mu : Measure (Fin I.card → alpha)) :
    ∫ y, f y ∂mu.map (orderedPathToFiniteSet I) =
      ∫ path, pullbackFiniteSetCompactTest I f path ∂mu := by
  rw [integral_map (measurable_orderedPathToFiniteSet I).aemeasurable
    (stronglyMeasurable_compactlySupported_pi f).aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun path ↦ (pullbackFiniteSetCompactTest_apply I f path).symm

/-- A compact-test integral against `finiteSetKernel` is the corresponding pulled-back integral
against `finiteTimeKernel`. -/
theorem integral_finiteSetKernel_eq_integral_pullbackFiniteSetCompactTest
    {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
    (P : SubMarkovKernelSemigroup alpha) (I : Finset NNReal)
    (f : C_c(I → alpha, ℝ)) (x : alpha) :
    ∫ y, f y ∂finiteSetKernel P I x =
      ∫ path, pullbackFiniteSetCompactTest I f path
        ∂finiteTimeKernel P (finiteSetTimes I) x := by
  rw [finiteSetKernel_eq_map, Kernel.map_apply _ (measurable_orderedPathToFiniteSet I)]
  exact integral_map_orderedPathToFiniteSet I f (finiteTimeKernel P (finiteSetTimes I) x)

end MarkovProcess.SubMarkovKernelSemigroup
