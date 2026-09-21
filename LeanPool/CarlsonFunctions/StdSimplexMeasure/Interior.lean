/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.IntrinsicMeasure

/-!
# The positive-coordinate interior of the standard simplex

The definition and measurability result are independent of Dirichlet parameters.
The historical `ProbabilityTheory` declaration names are retained for compatibility.
-/

@[expose] public noncomputable section

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- The interior of `Convexity.StdSimplex.coordinateSet ℝ ι` relative to its affine hull. -/
def stdSimplexInterior : Set (ι → ℝ) :=
  {u | u ∈ Convexity.StdSimplex.coordinateSet ℝ ι ∧ ∀ i, 0 < u i}

/-- The `stdSimplexInterior` is a measurable set. -/
theorem measurableSet_stdSimplexInterior :
    MeasurableSet (stdSimplexInterior (ι := ι)) := by
  have hpos : IsOpen {u : ι → ℝ | ∀ i, 0 < u i} := by
    rw [show {u : ι → ℝ | ∀ i, 0 < u i} =
        ⋂ i, {u : ι → ℝ | 0 < u i} by
      ext u
      simp]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_apply i)
  change MeasurableSet (Convexity.StdSimplex.coordinateSet ℝ ι ∩ {u : ι → ℝ | ∀ i, 0 < u i})
  exact (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet.inter hpos.measurableSet

/-- Permuting coordinates preserves the positive-coordinate simplex interior. -/
theorem mem_stdSimplexInterior_perm (σ : Equiv.Perm ι) (u : ι → ℝ) :
    (u ∘ σ) ∈ stdSimplexInterior ↔ u ∈ stdSimplexInterior := by
  have hsimp : (u ∘ σ) ∈ Convexity.StdSimplex.coordinateSet ℝ ι ↔ u ∈
    Convexity.StdSimplex.coordinateSet ℝ ι := by
    change u ∈ (fun v ↦ v ∘ σ) ⁻¹' Convexity.StdSimplex.coordinateSet ℝ ι ↔ _
    rw [preimage_stdSimplex_perm]
  constructor
  · rintro ⟨hu, hp⟩
    exact ⟨hsimp.mp hu, fun i ↦ by simpa using hp (σ.symm i)⟩
  · rintro ⟨hu, hp⟩
    exact ⟨hsimp.mpr hu, fun i ↦ hp (σ i)⟩

/-- Almost every point of the simplex is in its positive-coordinate interior.
For an empty index type the simplex measure is zero. -/
theorem ae_mem_stdSimplexInterior :
    ∀ᵐ u ∂MeasureTheory.Measure.stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι),
      u ∈ stdSimplexInterior := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [MeasureTheory.Measure.stdSimplexMeasure_empty]
  | inr hι =>
      let _ := hι
      filter_upwards [MeasureTheory.self_mem_ae_restrict
        (μ := MeasureTheory.Measure.stdSimplexMeasure)
          (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet,
        MeasureTheory.Measure.ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hp
      exact ⟨hu, hp⟩

end ProbabilityTheory

namespace Convexity.StdSimplex
variable {ι : Type*} [Fintype ι]

/-- The positive-coordinate interior as a set of intrinsic simplex points. -/
def positiveInterior : Set (StdSimplex ℝ ι) := {s | ∀ i, 0 < s.weights i}

omit [Fintype ι] in
theorem isOpen_positiveInterior [Finite ι] : IsOpen (positiveInterior (ι := ι)) := by
  classical
  let _ := Fintype.ofFinite ι
  have hset : positiveInterior (ι := ι) =
      ⋂ i, {s : StdSimplex ℝ ι | 0 < s.coordinates i} := by ext; simp [positiveInterior,
        coordinates]
  rw [hset]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const
    ((continuous_apply i).comp continuous_coordinates))

/-- The intrinsic interior has exactly the existing ambient positive-coordinate image. -/
theorem image_coordinates_positiveInterior :
    coordinates '' positiveInterior (ι := ι) = ProbabilityTheory.stdSimplexInterior := by
  ext u
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.coordinates_mem, hs⟩
  · rintro ⟨hu, hp⟩
    exact ⟨ofCoordinates u hu, hp, rfl⟩

/-- Almost every intrinsic point has strictly positive coordinates. -/
theorem ae_mem_positiveInterior : ∀ᵐ s ∂(coordinateMeasure (ι := ι)), s ∈ positiveInterior := by
  have h := ProbabilityTheory.ae_mem_stdSimplexInterior (ι := ι)
  rw [← map_coordinates_coordinateMeasure,
    measurableEmbedding_coordinates.ae_map_iff] at h
  exact h.mono (fun _ hs => hs.2)

end Convexity.StdSimplex

end
