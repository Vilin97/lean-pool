/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.SimplexGeometry
import LeanPool.Feige.Grunbaum.Main
import LeanPool.Feige.Grunbaum.Sharpness
import LeanPool.Feige.Grunbaum.SimplexCentroidCoordinates
import LeanPool.Feige.Grunbaum.StrictBoundaryBridge

/-!
# Basic interface to the Grünbaum formalization

This file registers the first, purely measure-theoretic part of the bridge
between the coordinate-function model used by `Feige` and Mathlib's
`EuclideanSpace` model used by `Grunbaum`.
-/

open Set MeasureTheory

namespace Feige

/-- The canonical passage from coordinate functions to Euclidean space. -/
def simplexToEuclidean (n : ℕ) :
    (Fin n → ℝ) → Grunbaum.SimplexE n :=
  WithLp.toLp 2

theorem measurable_simplexToEuclidean (n : ℕ) :
    Measurable (simplexToEuclidean n) :=
  by
    simpa [simplexToEuclidean] using
      (PiLp.volume_preserving_toLp (Fin n)).measurable

@[simp]
theorem simplexToEuclidean_apply
    (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    simplexToEuclidean n x i = x i :=
  PiLp.toLp_apply 2 (fun _ : Fin n => ℝ) x i

/-- The two projects use exactly the same standard simplex, modulo the
canonical `PiLp.toLp` wrapper. -/
theorem simplexToEuclidean_mem_simplexSet_iff
    (n : ℕ) (x : Fin n → ℝ) :
    simplexToEuclidean n x ∈ Grunbaum.simplexSet n ↔
      x ∈ fullSimplex (Fin n) := by
  simp only [Grunbaum.mem_simplexSet, fullSimplex,
    Set.mem_ofPred_eq, Grunbaum.coordinateSum_apply,
    simplexToEuclidean_apply]

theorem simplexToEuclidean_preimage_simplexSet (n : ℕ) :
    simplexToEuclidean n ⁻¹' Grunbaum.simplexSet n =
      fullSimplex (Fin n) := by
  ext x
  exact simplexToEuclidean_mem_simplexSet_iff n x

/-- Lebesgue volume of the simplex is unchanged by the canonical
coordinate-function/Euclidean-space identification. -/
theorem volume_simplexSet_eq_volume_fullSimplex (n : ℕ) :
    volume (Grunbaum.simplexSet n) =
      volume (fullSimplex (Fin n)) := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (Grunbaum.isClosed_simplexSet n).measurableSet.nullMeasurableSet]
  change volume (simplexToEuclidean n ⁻¹' Grunbaum.simplexSet n) =
    volume (fullSimplex (Fin n))
  rw [simplexToEuclidean_preimage_simplexSet]

/-- Transport of intersections with the standard simplex.  This is the
form needed to compare the two normalized halfspace-volume ratios. -/
theorem volume_simplexSet_inter_eq_volume_fullSimplex_inter_preimage
    (n : ℕ) {A : Set (Grunbaum.SimplexE n)}
    (hA : MeasurableSet A) :
    volume (Grunbaum.simplexSet n ∩ A) =
      volume (fullSimplex (Fin n) ∩ simplexToEuclidean n ⁻¹' A) := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    ((Grunbaum.isClosed_simplexSet n).measurableSet.inter hA).nullMeasurableSet]
  change
    volume (simplexToEuclidean n ⁻¹'
      (Grunbaum.simplexSet n ∩ A)) =
      volume (fullSimplex (Fin n) ∩ simplexToEuclidean n ⁻¹' A)
  rw [preimage_inter, simplexToEuclidean_preimage_simplexSet]

end Feige
