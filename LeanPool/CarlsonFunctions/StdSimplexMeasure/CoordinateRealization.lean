/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Intrinsic
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Aggregation
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Coordinates

/-!
# Coordinate realization of the standard simplex

This file connects ambient coordinate charts to the intrinsic
`Convexity.StdSimplex`. The coordinate carrier is used for restricting the
hyperplane measure and for ambient calculus. The chart homeomorphism targets
the intrinsic simplex itself.
-/

@[expose] public noncomputable section StdSimplexCoordinateRealization

variable {ι : Type*} [Fintype ι]
variable {R : Type*}


section OrderedSemiring

variable [Semiring R] [PartialOrder R]

/-- The coordinate realization of the standard simplex is invariant under precomposition by a
permutation of its coordinates. -/
@[simp] theorem preimage_stdSimplex_perm (σ : Equiv.Perm ι) :
    (fun u : ι → R => u ∘ σ) ⁻¹' Convexity.StdSimplex.coordinateSet R ι = Convexity.StdSimplex.coordinateSet R ι := by
  ext u
  simp only [Set.mem_preimage, Convexity.StdSimplex.coordinateSet, Set.mem_ofPred_eq, Function.comp_apply,
    Equiv.sum_comp σ u]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun i => by simpa using h1 (σ.symm i), h2⟩,
    fun ⟨h1, h2⟩ => ⟨fun i => h1 (σ i), h2⟩⟩

end OrderedSemiring

section OrderedRing

variable [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-- The preimage of the coordinate realization of the standard simplex under
`stdSimplexCoordMap i` is `stdSimplexFreeCoords i`. -/
@[simp] theorem preimage_stdSimplexCoordMap (i : ι) :
    stdSimplexCoordMap i ⁻¹' Convexity.StdSimplex.coordinateSet R ι = stdSimplexFreeCoords i := by
  ext x
  simp only [Set.mem_preimage, Convexity.StdSimplex.coordinateSet, stdSimplexFreeCoords, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hpos, hsum⟩
    refine ⟨?_, ?_⟩
    · intro j
      have hj := hpos j.1
      rw [stdSimplexCoordMap_apply_of_ne i j.1 j.2 x] at hj
      exact hj
    · have hi := hpos i
      rw [stdSimplexCoordMap_apply_self] at hi
      exact sub_nonneg.mp hi
  · rintro ⟨hpos, hsum⟩
    refine ⟨?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst j
        rw [stdSimplexCoordMap_apply_self]
        exact sub_nonneg.mpr hsum
      · simpa [stdSimplexCoordMap_apply_of_ne, hji] using hpos ⟨j, hji⟩
    · exact sum_stdSimplexCoordMap i x

/-- Pointwise form of `preimage_stdSimplexCoordMap`. -/
@[simp] theorem stdSimplexCoordMap_mem_stdSimplex_iff
    (i : ι) (x : {j : ι // j ≠ i} → R) :
    stdSimplexCoordMap i x ∈ Convexity.StdSimplex.coordinateSet R ι ↔ x ∈ stdSimplexFreeCoords i := by
  change x ∈ stdSimplexCoordMap i ⁻¹' Convexity.StdSimplex.coordinateSet R ι ↔ _
  rw [preimage_stdSimplexCoordMap]

open scoped Classical in
/-- Coordinate aggregation sends the coordinate realization of the standard simplex on `ι`
into the coordinate realization on `κ`. -/
theorem stdSimplexAggregate_mem_stdSimplex {κ : Type*} [Fintype κ]
    {f : ι → κ} {u : ι → R} (hu : u ∈ Convexity.StdSimplex.coordinateSet R ι) :
    stdSimplexAggregate f u ∈ Convexity.StdSimplex.coordinateSet R κ := by
  refine ⟨?_, ?_⟩
  · intro k
    rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
    exact Finset.sum_nonneg (fun i _ => hu.1 i)
  · simp only [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply, ← hu.2]
    exact Finset.sum_fiberwise Finset.univ f u

end OrderedRing

namespace Convexity.StdSimplex

section IntrinsicAggregation

variable {κ : Type*} [Fintype κ]
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

/-- Intrinsic aggregation is realized by summing ambient coordinates over fibers. -/
@[simp] theorem coordinates_map (f : ι → κ) (s : StdSimplex R ι) :
    coordinates (s.map f) = stdSimplexAggregate f (coordinates s) :=
  weights_map_eq_stdSimplexAggregate f s

end IntrinsicAggregation

end Convexity.StdSimplex

section RealTopology

namespace Convexity.StdSimplex

/-- The omitted-coordinate chart identifies the filled free-coordinate simplex
with the intrinsic standard simplex. -/
def homeomorphFreeCoords (i : ι) :
    stdSimplexFreeCoords (R := ℝ) i ≃ₜ StdSimplex ℝ ι where
  toEquiv := equivFreeCoords i
  continuous_toFun := by
    apply isEmbedding_coordinates.isInducing.continuous_iff.mpr
    exact (continuous_stdSimplexCoordMap i).comp continuous_subtype_val
  continuous_invFun :=
    ((continuous_stdSimplexCoordProj i).comp continuous_coordinates).subtype_mk _

@[simp] theorem coordinates_homeomorphFreeCoords (i : ι)
    (x : stdSimplexFreeCoords (R := ℝ) i) :
    coordinates (homeomorphFreeCoords i x) = stdSimplexCoordMap i x.1 := rfl

@[simp] theorem coe_homeomorphFreeCoords_symm (i : ι) (s : StdSimplex ℝ ι) :
    ((homeomorphFreeCoords i).symm s : {j : ι // j ≠ i} → ℝ) =
      stdSimplexCoordProj i (coordinates s) := rfl

end Convexity.StdSimplex

end RealTopology

end StdSimplexCoordinateRealization
