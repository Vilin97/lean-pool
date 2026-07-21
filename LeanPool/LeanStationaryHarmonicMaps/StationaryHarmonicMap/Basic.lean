/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Basic definitions for stationary harmonic maps

Foundational measure-theoretic lemmas and the domain Euclidean space `ℝⁿ` used
throughout the monotonicity-formula development: the vector-measure pushforward
computation behind the coarea/radial representation, together with the ambient
Sobolev setup on which the later files build.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Applying the pushforward of the signed/vector measure `μ.withDensityᵥ f`
to a measurable set is the same as integrating `f` over the preimage.  This is
the basic computation behind the radial signed pushforward used in the coarea
step. -/
theorem vectorMeasure_map_withDensity_apply
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {f : α → ℝ} {φ : α → β} {s : Set β}
    (hf : Integrable f μ) (hφ : Measurable φ) (hs : MeasurableSet s) :
    ((μ.withDensityᵥ f).map φ) s = ∫ x in φ ⁻¹' s, f x ∂μ := by
  rw [MeasureTheory.VectorMeasure.map_apply (μ.withDensityᵥ f) hφ hs,
    MeasureTheory.withDensityᵥ_apply hf (hφ hs)]

/-- The domain Euclidean space `ℝⁿ`. -/
abbrev Domain (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The target Euclidean space `ℝᵐ`. -/
abbrev Target (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- A pointwise gradient matrix: the `i`-th entry is the derivative in the
`i`-th domain coordinate, valued in the target Euclidean space.  This is the
object that will later be supplied by a weak derivative. -/
abbrev Gradient (n m : ℕ) := Fin n → Target m

/-- The radial signed pushforward of an integrable density on a ball, evaluated
on a measurable radius set. -/
theorem radialVectorMeasure_apply
    {n : ℕ} {f : Domain n → ℝ} {R0 : ℝ} {s : Set ℝ}
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume)
    (hs : MeasurableSet s) :
    (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
        (fun x : Domain n => norm x)) s =
      ∫ x in {x : Domain n | norm x ∈ s}, f x
        ∂(volume.restrict (Metric.ball (0 : Domain n) R0)) := by
  exact vectorMeasure_map_withDensity_apply
      (μ := volume.restrict (Metric.ball (0 : Domain n) R0))
      (f := f) (φ := fun x : Domain n => norm x) (s := s)
      hf continuous_norm.measurable hs

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps
