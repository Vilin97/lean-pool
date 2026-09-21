/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The intrinsic simplex and its finite coordinate realization

`Convexity.StdSimplex` is the simplex object. Its `coordinateSet` is the carrier
of its realization in the ambient vector space, used for measures, restrictions,
and neighborhoods. The membership description is kept explicit for ambient
calculus; `range_coordinates` identifies it with the intrinsic object.

The intrinsic simplex uses Mathlib's topology and compactness instance. For finite
index types, Mathlib's coordinate embedding identifies this topology with the
topology induced by the weights.
-/

@[expose] public noncomputable section
open scoped Classical
namespace Convexity.StdSimplex
section Semiring
variable {R : Type*} [Semiring R] [PartialOrder R]
variable {ι : Type*} [Fintype ι]

/-- The ambient coordinate function of an intrinsic simplex point. -/
def coordinates (s : StdSimplex R ι) : ι → R := fun i => s.weights i

/-- The coordinate carrier of the intrinsic simplex, not a second simplex type. -/
def coordinateSet (R : Type*) (ι : Type*) [Semiring R] [PartialOrder R] [Fintype ι] :
    Set (ι → R) := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1}

theorem mem_coordinateSet {u : ι → R} :
    u ∈ coordinateSet R ι ↔ (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1 := Iff.rfl

theorem coordinates_mem (s : StdSimplex R ι) : coordinates s ∈ coordinateSet R ι := by
  refine ⟨s.nonneg, ?_⟩
  simpa [coordinates, Finsupp.sum_fintype] using s.total

/-- Recover an intrinsic point from its ambient coordinates and membership proof. -/
def ofCoordinates (u : ι → R) (hu : u ∈ coordinateSet R ι) : StdSimplex R ι where
  weights := Finsupp.equivFunOnFinite.symm u
  nonneg i := by simpa using hu.1 i
  total := by simpa [Finsupp.sum_fintype] using hu.2

@[simp] theorem coordinates_ofCoordinates (u : ι → R) (hu : u ∈ coordinateSet R ι) :
    coordinates (ofCoordinates u hu) = u := rfl

@[simp] theorem ofCoordinates_coordinates (s : StdSimplex R ι) :
    ofCoordinates (coordinates s) (coordinates_mem s) = s := by
  ext i
  rfl

omit [Fintype ι] in
theorem coordinates_injective : Function.Injective (coordinates (R := R) (ι := ι)) := by
  intro s t h
  ext i
  exact congrFun h i

theorem range_coordinates :
    Set.range (coordinates (R := R) (ι := ι)) = coordinateSet R ι := by
  ext u
  exact ⟨fun ⟨s, h⟩ => h ▸ coordinates_mem s,
    fun hu => ⟨ofCoordinates u hu, coordinates_ofCoordinates u hu⟩⟩

/-- The intrinsic simplex is equivalent to its coordinate carrier. -/
def coordinateEquiv : StdSimplex R ι ≃ coordinateSet R ι where
  toFun s := ⟨coordinates s, coordinates_mem s⟩
  invFun u := ofCoordinates u.1 u.2
  left_inv := ofCoordinates_coordinates
  right_inv _ := rfl

theorem mem_Icc_of_mem_coordinateSet [IsOrderedAddMonoid R]
    {u : ι → R} (hu : u ∈ coordinateSet R ι) (i : ι) : u i ∈ Set.Icc 0 1 :=
  ⟨hu.1 i, hu.2 ▸ Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)⟩

theorem coordinateSet_empty [Nontrivial R] [IsEmpty ι] : coordinateSet R ι = ∅ := by
  ext u
  simp [coordinateSet]

section Topology
variable [TopologicalSpace R] [OrderClosedTopology R] [ContinuousAdd R]

variable (R ι) in
theorem isClosed_coordinateSet : IsClosed (coordinateSet R ι) := by
  have hset : coordinateSet R ι =
      (⋂ i, {u : ι → R | 0 ≤ u i}) ∩ {u | ∑ i, u i = 1} := by ext; simp [coordinateSet]
  rw [hset]
  exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
    (isClosed_eq (by fun_prop) continuous_const)

variable (R ι) in
theorem isCompact_coordinateSet [CompactIccSpace R] [IsOrderedAddMonoid R] :
    IsCompact (coordinateSet R ι) :=
  isCompact_Icc.of_isClosed_subset (isClosed_coordinateSet R ι)
    (fun _ hu => ⟨fun i => hu.1 i, fun i => (mem_Icc_of_mem_coordinateSet hu i).2⟩)

instance [CompactIccSpace R] [IsOrderedAddMonoid R] : CompactSpace (coordinateSet R ι) :=
  isCompact_iff_compactSpace.mp (isCompact_coordinateSet R ι)

end Topology

end Semiring

variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type*} [Fintype ι]

theorem isEmbedding_coordinates :
    Topology.IsEmbedding (coordinates (R := R) (ι := ι)) :=
  isEmbedding_toFun_comp_weights R ι

@[fun_prop] theorem continuous_coordinates :
    Continuous (coordinates (R := R) (ι := ι)) :=
  isEmbedding_coordinates.continuous

/-- The intrinsic simplex and its coordinate realization have the same topology. -/
def coordinateHomeomorph : StdSimplex R ι ≃ₜ coordinateSet R ι where
  toEquiv := coordinateEquiv
  continuous_toFun := continuous_coordinates.subtype_mk _
  continuous_invFun := by
    apply isEmbedding_coordinates.isInducing.continuous_iff.mpr
    exact continuous_subtype_val

theorem isClosedEmbedding_coordinates [OrderClosedTopology R] :
    Topology.IsClosedEmbedding (coordinates (R := R) (ι := ι)) :=
  isClosedEmbedding_toFun_comp_weights R ι

instance : MeasurableSpace (StdSimplex ℝ ι) := borel _
instance : BorelSpace (StdSimplex ℝ ι) := ⟨rfl⟩

theorem measurableEmbedding_coordinates :
    MeasurableEmbedding (coordinates (R := ℝ) (ι := ι)) :=
  isClosedEmbedding_coordinates.measurableEmbedding

end Convexity.StdSimplex
end
