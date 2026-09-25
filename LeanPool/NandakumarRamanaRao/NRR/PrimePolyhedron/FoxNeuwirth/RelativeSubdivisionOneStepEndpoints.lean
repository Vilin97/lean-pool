/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeSubdivisionOneStepCells
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EndpointFaceRefinement
/-!
# Endpoint facets of the one-step relative subdivision cylinder

This module identifies the two external horizontal boundaries of the explicit recursive cylinder
constructed in `RelativeSubdivisionOneStepCells`.

The lower boundary is the coarse level-`N` Fox--Neuwirth simplex.  The upper boundary is the first
barycentric subdivision, indexed by level-`N + 1` top cells.  The definitions are made at the
quotient-facet level, while the geometric theorems are stated for arbitrary representatives of the
canonical occurrences.  The signed boundary formula is supplied in the following module.
-/

@[expose] public section

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeSubdivisionOneStepEndpoints

open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open ExplicitAffineRelativeCollar
open EndpointFaceRefinement
open RefinedAffineMap
open EquivariantPrismVertexParameters


variable {p : Nat}

private theorem cylinderPoint_ext {x y : CylinderPoint p}
    (hspatial : x.spatial = y.spatial) (htime : x.time = y.time) : x = y := by
  rcases x with ⟨xs, xt⟩
  rcases y with ⟨ys, yt⟩
  simp_all

private theorem localWeight_vertex_succ
    {n : Nat} (hp : Nat.Prime (n + 1)) (i : Fin (n + 1)) :
    RelativeSubdivisionOneStepCells.localWeight hp
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) i.succ) =
      SphereOddDegree.FiniteSimplex.vertex (S := Real) i.succ := by
  simp [RelativeSubdivisionOneStepCells.localWeight]

private theorem localPoint_lower_vertex
    {n : Nat} (hp : Nat.Prime (n + 1)) (i : Fin (n + 1)) :
    RelativeSubdivisionOneStepCells.localPoint hp
        (RelativeSubdivisionCylinderCombinatorics.lowerCell n)
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) i.succ) =
      RelativeSubdivisionCylinderCombinatorics.lowerBoundaryVertex n i := by
  unfold RelativeSubdivisionOneStepCells.localPoint
  rw [localWeight_vertex_succ hp i]
  change RelativeSubdivisionCylinderCombinatorics.chart n
      (RelativeSubdivisionCylinderCombinatorics.lowerCell n)
      (SphereOddDegree.FiniteSimplex.vertex (S := Real) i.succ) = _
  exact (RelativeSubdivisionCylinderCombinatorics.chart_vertex n
    (RelativeSubdivisionCylinderCombinatorics.lowerCell n) i.succ).trans
    (RelativeSubdivisionCylinderCombinatorics.vertex_succ_lower n i)

private theorem localPoint_upper_vertex
    {n : Nat} (hp : Nat.Prime (n + 1))
    (pi : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    RelativeSubdivisionOneStepCells.localPoint hp
        (RelativeSubdivisionCylinderCombinatorics.upperCell n pi)
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) i.succ) =
      RelativeSubdivisionCylinderCombinatorics.upperBoundaryVertex n pi i := by
  unfold RelativeSubdivisionOneStepCells.localPoint
  rw [localWeight_vertex_succ hp i]
  change RelativeSubdivisionCylinderCombinatorics.chart n
      (RelativeSubdivisionCylinderCombinatorics.upperCell n pi)
      (SphereOddDegree.FiniteSimplex.vertex (S := Real) i.succ) = _
  exact (RelativeSubdivisionCylinderCombinatorics.chart_vertex n
    (RelativeSubdivisionCylinderCombinatorics.upperCell n pi) i.succ).trans
    (RelativeSubdivisionCylinderCombinatorics.vertex_succ_upper n pi i)

/-- Split a level-`N + 1` top cell into its level-`N` prefix and final subdivision permutation. -/
noncomputable def splitTopCellEquiv
    (hp : Nat.Prime p) (N : Nat) :
    TopCell hp (N + 1) ≃ TopCell hp N × Equiv.Perm (Fin p) where
  toFun q := ((q.1, fun i => q.2 i.castSucc), q.2 (Fin.last N))
  invFun q := (q.1.1, Fin.snoc q.1.2 q.2)
  left_inv := by
    rintro ⟨orbit, rho⟩
    apply Prod.ext
    · rfl
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv := by
    rintro ⟨⟨orbit, rho⟩, pi⟩
    simp

/-- The subdivision sign factors when one final permutation is appended. -/
theorem subdivisionSign_snoc
    (N : Nat) (rho : RefinementWord p N) (pi : Equiv.Perm (Fin p)) :
    subdivisionSign (N + 1) (Fin.snoc rho pi) =
      subdivisionSign N rho * ((Equiv.Perm.sign pi : Int) : ZMod p) := by
  rw [subdivisionSign, Fin.prod_univ_castSucc]
  simp [subdivisionSign]

/-- Refined Fox--Neuwirth coefficients factor under one final subdivision step. -/
theorem coefficient_snoc
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N)
    (pi : Equiv.Perm (Fin p)) :
    RefinedAffineMap.coefficient hp (N + 1) (q.1, Fin.snoc q.2 pi) =
      RefinedAffineMap.coefficient hp N q *
        ((Equiv.Perm.sign pi : Int) : ZMod p) := by
  simp [RefinedAffineMap.coefficient, subdivisionSign_snoc]
  ring

/-- Canonical lower horizontal occurrence over a level-`N` top cell. -/
noncomputable def lowerOccurrence
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence :=
  ((q, RelativeSubdivisionCylinderCombinatorics.lowerCell (p - 1)), 0)

/-- Canonical upper horizontal occurrence over a level-`N` cell and one final subdivision
permutation. -/
noncomputable def upperOccurrenceBase
    (hp : Nat.Prime p) (N : Nat)
    (q : TopCell hp N) (pi : Equiv.Perm (Fin p)) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence :=
  ((q, RelativeSubdivisionCylinderCombinatorics.upperCell (p - 1) (by
      simpa [Nat.sub_add_cancel hp.pos] using pi)), 0)

/-- Canonical upper horizontal occurrence indexed by a level-`N + 1` top cell. -/
noncomputable def upperOccurrence
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp (N + 1)) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence :=
  let data := splitTopCellEquiv hp N q
  upperOccurrenceBase hp N data.1 data.2

/-- Canonical lower quotient facet. -/
noncomputable def lowerFacet
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet :=
  (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass (lowerOccurrence hp N q)

/-- Canonical upper quotient facet. -/
noncomputable def upperFacet
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp (N + 1)) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet :=
  (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass (upperOccurrence hp N q)

/-- The canonical lower occurrence lies entirely in the time-zero boundary. -/
theorem lowerOccurrence_isLower
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).IsLowerFacetOccurrence (lowerOccurrence hp
      N q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp.pos)
  intro i
  simp [lowerOccurrence, RelativeSubdivisionOneStepCells.cellSystem,
    RelativeAffineCellSystem.facetSignature, RelativeSubdivisionOneStepCells.vertex,
    RelativeSubdivisionOneStepCells.chart, RelativeSubdivisionOneStepCells.liftPoint,
    localPoint_lower_vertex hp i, CylinderPoint.ofProd,
    RelativeSubdivisionCylinderCombinatorics.lowerBoundaryVertex]

/-- The canonical upper occurrence lies entirely in the time-one boundary. -/
theorem upperOccurrenceBase_isUpper
    (hp : Nat.Prime p) (N : Nat)
    (q : TopCell hp N) (pi : Equiv.Perm (Fin p)) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).IsUpperFacetOccurrence
      (upperOccurrenceBase hp N q pi) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp.pos)
  intro i
  simp [upperOccurrenceBase, RelativeSubdivisionOneStepCells.cellSystem,
    RelativeAffineCellSystem.facetSignature, RelativeSubdivisionOneStepCells.vertex,
    RelativeSubdivisionOneStepCells.chart, RelativeSubdivisionOneStepCells.liftPoint,
    localPoint_upper_vertex hp pi i, CylinderPoint.ofProd,
    RelativeSubdivisionCylinderCombinatorics.upperBoundaryVertex]

/-- The canonical upper occurrence indexed by a refined top cell is horizontal at time one. -/
theorem upperOccurrence_isUpper
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp (N + 1)) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).IsUpperFacetOccurrence (upperOccurrence hp
      N q) := by
  let data := splitTopCellEquiv hp N q
  change (RelativeSubdivisionOneStepCells.cellSystem hp N).IsUpperFacetOccurrence
    (upperOccurrenceBase hp N data.1 data.2)
  exact upperOccurrenceBase_isUpper hp N data.1 data.2

/-- Every canonical lower quotient facet is lower-horizontal. -/
theorem lowerFacet_isLower
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).IsLowerFacet (lowerFacet hp N q) := by
  change (RelativeSubdivisionOneStepCells.cellSystem hp N).IsLowerFacet
    ((RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass (lowerOccurrence hp N q))
  exact lowerOccurrence_isLower hp N q

/-- Every canonical upper quotient facet is upper-horizontal. -/
theorem upperFacet_isUpper
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp (N + 1)) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).IsUpperFacet (upperFacet hp N q) := by
  change (RelativeSubdivisionOneStepCells.cellSystem hp N).IsUpperFacet
    ((RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass (upperOccurrence hp N q))
  exact upperOccurrence_isUpper hp N q

/-- Vertex signature of the coarse lower endpoint. -/
theorem lowerOccurrence_facetSignature
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N) (i : Fin p) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature (lowerOccurrence hp N q) i =
      lowerCylinderPoint (RefinedAffineMap.vertex hp N q
        (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp.pos)
  change CylinderPoint.ofProd
      (RefinedAffineMap.chart hp N q
          (RelativeSubdivisionOneStepCells.localPoint hp
            (RelativeSubdivisionCylinderCombinatorics.lowerCell n)
            (SphereOddDegree.FiniteSimplex.vertex (S := Real) i.succ)).1,
        (RelativeSubdivisionOneStepCells.localPoint hp
          (RelativeSubdivisionCylinderCombinatorics.lowerCell n)
          (SphereOddDegree.FiniteSimplex.vertex (S := Real) i.succ)).2) = _
  rw [localPoint_lower_vertex hp i]
  rfl

/-- Appending one permutation to a refinement word is the recursive `affineCompMap` step. -/
theorem refinedChart_snoc_vertex
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N)
    (pi : Equiv.Perm (Fin p)) (i : Fin p) :
    RefinedAffineMap.chart hp N q
        (prefixBarycenter (p - 1) (Simplex.refinementIndexPerm pi)
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) =
      RefinedAffineMap.vertex hp (N + 1) (q.1, Fin.snoc q.2 pi)
        (Fin.cast (Nat.sub_add_cancel hp.pos).symm i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp.pos)
  simp [RefinedAffineMap.vertex, RefinedAffineMap.chart,
    Simplex.refinedContinuousMap, Simplex.refinementIndexPerm,
    affineCompMap_snoc, affineSubdivContinuousMap, affineSubdivMap_vertex]

/-- Vertex signature of the refined upper endpoint before reindexing by level-`N + 1` top cells. -/
theorem upperOccurrenceBase_facetSignature
    (hp : Nat.Prime p) (N : Nat)
    (q : TopCell hp N) (pi : Equiv.Perm (Fin p)) (i : Fin p) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature (upperOccurrenceBase hp N q
      pi) i =
      upperCylinderPoint
        (RefinedAffineMap.vertex hp (N + 1) (q.1, Fin.snoc q.2 pi)
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp.pos)
  apply cylinderPoint_ext
  · change RefinedAffineMap.chart hp N q
        (RelativeSubdivisionOneStepCells.localPoint hp
          (RelativeSubdivisionCylinderCombinatorics.upperCell n pi)
          (SphereOddDegree.FiniteSimplex.vertex (S := Real) i.succ)).1 = _
    rw [localPoint_upper_vertex hp pi i]
    exact refinedChart_snoc_vertex hp N q pi i
  · change (RelativeSubdivisionOneStepCells.localPoint hp
        (RelativeSubdivisionCylinderCombinatorics.upperCell n pi)
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) i.succ)).2 = _
    rw [localPoint_upper_vertex hp pi i]
    rfl

/-- Vertex signature of the canonical upper endpoint indexed by a level-`N + 1` top cell. -/
theorem upperOccurrence_facetSignature
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp (N + 1)) (i : Fin p) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature (upperOccurrence hp N q) i =
      upperCylinderPoint (RefinedAffineMap.vertex hp (N + 1) q
        (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  let data := splitTopCellEquiv hp N q
  have hdata : (data.1.1, Fin.snoc data.1.2 data.2) = q := by
    exact (splitTopCellEquiv hp N).left_inv q
  change (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature
      (upperOccurrenceBase hp N data.1 data.2) i = _
  rw [upperOccurrenceBase_facetSignature hp N data.1 data.2 i, hdata]

/-- Every lower-horizontal occurrence is the canonical lower occurrence of its level-`N` spatial
cell. -/
theorem lowerOccurrence_exhaustive
    (hp : Nat.Prime p) (N : Nat)
    (o : (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence)
    (ho : (RelativeSubdivisionOneStepCells.cellSystem hp N).IsLowerFacetOccurrence o) :
    ∃ q : TopCell hp N,
      (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o = lowerFacet hp N q := by
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ n =>
    rcases o with ⟨⟨q, r⟩, j⟩
    have hlocal : ∀ i : Fin (n + 1),
        (RelativeSubdivisionCylinderCombinatorics.vertex n r (j.succAbove i)).2.1 = 0 := by
      intro i
      simpa [RelativeSubdivisionOneStepCells.cellSystem, RelativeAffineCellSystem.facetSignature,
        RelativeSubdivisionOneStepCells.vertex, RelativeSubdivisionOneStepCells.chart,
        RelativeSubdivisionOneStepCells.liftPoint, RelativeSubdivisionOneStepCells.localPoint,
        RelativeSubdivisionOneStepCells.localWeight,
        RelativeSubdivisionCylinderCombinatorics.chart_vertex, CylinderPoint.ofProd]
        using ho i
    rcases RelativeSubdivisionCylinderCombinatorics.lowerFacet_classification n r j hlocal with
      ⟨hr, hj⟩
    subst r
    subst j
    exact ⟨q, rfl⟩

/-- Every upper-horizontal occurrence is the canonical upper occurrence of a unique final
subdivision permutation over its level-`N` spatial prefix. -/
theorem upperOccurrence_exhaustive
    (hp : Nat.Prime p) (N : Nat)
    (o : (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence)
    (ho : (RelativeSubdivisionOneStepCells.cellSystem hp N).IsUpperFacetOccurrence o) :
    ∃ q : TopCell hp (N + 1),
      (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o = upperFacet hp N q := by
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ n =>
    rcases o with ⟨⟨q, r⟩, j⟩
    have hlocal : ∀ i : Fin (n + 1),
        (RelativeSubdivisionCylinderCombinatorics.vertex n r (j.succAbove i)).2.1 = 1 := by
      intro i
      simpa [RelativeSubdivisionOneStepCells.cellSystem, RelativeAffineCellSystem.facetSignature,
        RelativeSubdivisionOneStepCells.vertex, RelativeSubdivisionOneStepCells.chart,
        RelativeSubdivisionOneStepCells.liftPoint, RelativeSubdivisionOneStepCells.localPoint,
        RelativeSubdivisionOneStepCells.localWeight,
        RelativeSubdivisionCylinderCombinatorics.chart_vertex, CylinderPoint.ofProd]
        using ho i
    rcases RelativeSubdivisionCylinderCombinatorics.upperFacet_classification n r j hlocal with
      ⟨hj, pi, hr⟩
    subst j
    subst r
    let pi' : Equiv.Perm (Fin (n + 1)) := pi
    let q' : TopCell hp (N + 1) := (q.1, Fin.snoc q.2 pi')
    refine ⟨q', ?_⟩
    have hsplit : splitTopCellEquiv hp N q' = (q, pi') := by
      simp [q', splitTopCellEquiv]
    simp [upperFacet, upperOccurrence, hsplit, upperOccurrenceBase, pi']


/-- Every lower-horizontal quotient facet is represented by a canonical lower endpoint cell. -/
theorem lowerFacet_exhaustive
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet)
    (hs : (RelativeSubdivisionOneStepCells.cellSystem hp N).IsLowerFacet s) :
    ∃ q : TopCell hp N, lowerFacet hp N q = s := by
  refine Quotient.inductionOn s ?_ hs
  intro o ho
  rcases lowerOccurrence_exhaustive hp N o ho with ⟨q, hq⟩
  exact ⟨q, hq.symm⟩

/-- Every upper-horizontal quotient facet is represented by a canonical upper endpoint cell. -/
theorem upperFacet_exhaustive
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet)
    (hs : (RelativeSubdivisionOneStepCells.cellSystem hp N).IsUpperFacet s) :
    ∃ q : TopCell hp (N + 1), upperFacet hp N q = s := by
  refine Quotient.inductionOn s ?_ hs
  intro o ho
  rcases upperOccurrence_exhaustive hp N o ho with ⟨q, hq⟩
  exact ⟨q, hq.symm⟩

/-- Any representative of a canonical lower quotient facet has the prescribed endpoint geometry,
up to one simultaneous prime relabelling. -/
theorem lowerFacetOccurrenceVertex_eq
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N)
    (o : (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence)
    (ho : (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o = lowerFacet hp N q) :
    ∃ g : PrimeSymmetry p, ∀ i,
      (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature o i =
        g • lowerCylinderPoint (RefinedAffineMap.vertex hp N q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  have hclass : (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o =
      (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass (lowerOccurrence hp N q) := ho
  rcases Quotient.exact hclass with ⟨g, hg⟩
  refine ⟨g⁻¹, ?_⟩
  intro i
  have hi := congrFun hg i
  have hend := lowerOccurrence_facetSignature hp N q i
  have hgi := congrArg (fun z : EquivariantPrismVertexParameters.CylinderPoint p => g⁻¹ • z) hi
  rw [hend] at hgi
  simpa [mul_smul] using hgi

/-- Any representative of a canonical upper quotient facet has the prescribed endpoint geometry,
up to one simultaneous prime relabelling. -/
theorem upperFacetOccurrenceVertex_eq
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp (N + 1))
    (o : (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence)
    (ho : (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o = upperFacet hp N q) :
    ∃ g : PrimeSymmetry p, ∀ i,
      (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature o i =
        g • upperCylinderPoint (RefinedAffineMap.vertex hp (N + 1) q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  have hclass : (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o =
      (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass (upperOccurrence hp N q) := ho
  rcases Quotient.exact hclass with ⟨g, hg⟩
  refine ⟨g⁻¹, ?_⟩
  intro i
  have hi := congrFun hg i
  have hend := upperOccurrence_facetSignature hp N q i
  have hgi := congrArg (fun z : EquivariantPrismVertexParameters.CylinderPoint p => g⁻¹ • z) hi
  rw [hend] at hgi
  simpa [mul_smul] using hgi

end RelativeSubdivisionOneStepEndpoints
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
