/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.CoordinatePolynomialMeasure
public import LeanPool.MarkovProcess.MarkovProcess.DenseTime.PhysicalReindex
public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.FiniteProductCoordinateNormalForm
public import Mathlib.MeasureTheory.Integral.CompactlySupported


/-!
# Compact-test transport from physical to dense-time coordinates

This file identifies finite paths labelled by physical rational times with paths labelled by the
corresponding dense times. It pulls compactly supported tests back across this homeomorphism and
rewrites integrals against mapped finite-set kernels.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported

namespace MarkovProcess.DenseTimePath

open SubMarkovKernelSemigroup

/-- Reindexing finite paths from physical rational times to dense-time labels is a
homeomorphism. -/
noncomputable def pullbackPhysicalSetHomeomorph
    {alpha : Type*} [TopologicalSpace alpha] (J : Finset DenseTime) :
    (denseTimePhysicalSet J → alpha) ≃ₜ (J → alpha) :=
  Homeomorph.piCongrLeft (Y := fun _ : J ↦ alpha) (DenseTime.physicalSetEquiv J).symm

/-- The physical-coordinate homeomorphism has underlying function `pullbackPhysicalSet`. -/
@[simp]
theorem pullbackPhysicalSetHomeomorph_apply
    {alpha : Type*} [TopologicalSpace alpha] (J : Finset DenseTime)
    (path : denseTimePhysicalSet J → alpha) :
    pullbackPhysicalSetHomeomorph J path = pullbackPhysicalSet J path := by
  ext t
  change (Equiv.piCongrLeft (fun _ : J ↦ alpha)
    (DenseTime.physicalSetEquiv J).symm path) t = _
  rw [Equiv.piCongrLeft_apply]
  simp only [pullbackPhysicalSet]
  rw [eqRec_eq_cast, cast_eq]
  rfl

/-- Pull a compactly supported test on dense-time labels back to physical-time labels. -/
noncomputable def pullbackPhysicalSetCompactTest
    {alpha : Type*} [TopologicalSpace alpha] (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    C_c(denseTimePhysicalSet J → alpha, ℝ) :=
  f.comp (pullbackPhysicalSetHomeomorph J).toCocompactMap

/-- Evaluation of a compact test pulled back to physical-time labels. -/
@[simp]
theorem pullbackPhysicalSetCompactTest_apply
    {alpha : Type*} [TopologicalSpace alpha] (J : Finset DenseTime) (f : C_c(J → alpha, ℝ))
    (path : denseTimePhysicalSet J → alpha) :
    pullbackPhysicalSetCompactTest J f path = f (pullbackPhysicalSet J path) := by
  rw [pullbackPhysicalSetCompactTest]
  exact congr_arg f (pullbackPhysicalSetHomeomorph_apply J path)

/-- Integration after physical-to-dense reindexing equals integration of the pulled-back compact
test. -/
theorem integral_map_pullbackPhysicalSet
    {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ))
    (mu : Measure (denseTimePhysicalSet J → alpha)) :
    ∫ y, f y ∂mu.map (pullbackPhysicalSet J) =
      ∫ path, pullbackPhysicalSetCompactTest J f path ∂mu := by
  rw [integral_map (measurable_pullbackPhysicalSet J).aemeasurable
    (stronglyMeasurable_compactlySupported_pi f).aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun path ↦ (pullbackPhysicalSetCompactTest_apply J f path).symm

/-- A compact-test integral against a physically indexed finite-set kernel mapped back to dense
labels is the pulled-back integral against the original finite-set kernel. -/
theorem integral_map_finiteSetKernel_pullbackPhysicalSet
    {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
    (P : SubMarkovKernelSemigroup alpha) (J : Finset DenseTime)
    (f : C_c(J → alpha, ℝ)) (x : alpha) :
    ∫ y, f y ∂(finiteSetKernel P (denseTimePhysicalSet J)).map
        (pullbackPhysicalSet J) x =
      ∫ path, pullbackPhysicalSetCompactTest J f path
        ∂finiteSetKernel P (denseTimePhysicalSet J) x := by
  rw [Kernel.map_apply _ (measurable_pullbackPhysicalSet J)]
  exact integral_map_pullbackPhysicalSet J f
    (finiteSetKernel P (denseTimePhysicalSet J) x)

end MarkovProcess.DenseTimePath
