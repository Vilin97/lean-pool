/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeSubdivisionCylinderCombinatorics
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.FiniteSimplexDoubleBoundary
/-!
# Oriented boundary of the recursive one-step subdivision cylinder

The recursive cylinder is a cone over a triangulated boundary chain.  This file proves its exact
weighted boundary formula in two finite steps.

1. The triangulated boundary chain is closed.  The upper barycentric boundary is moved to the
   original faces by `oneStep_weighted_boundary`; the recursively triangulated side boundaries are
   replaced by the induction hypothesis; codimension-two side terms cancel by
   `double_boundary_weighted_zero`.
2. The non-base facets of the cone are cones over the boundary of that closed boundary chain.
   Their weighted sum therefore vanishes, leaving precisely the cone-base chain.

The theorem is stated for arbitrary weights on ordered geometric vertex tuples.  Taking the weight
to be the characteristic function of one quotient-facet class gives the pointwise incidence
identity needed by the global Fox--Neuwirth collar.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace RelativeSubdivisionCylinderBoundary

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open EquivariantPrismNonhorizontalCancellation
open EquivariantPrismStableRelativeBoundary.FiniteSimplexDoubleBoundary


/-- Delete one entry from an ordered vertex tuple. -/
def deleteTuple
    {X : Type} {n : Nat} (v : Fin (n + 2) → X) (j : Fin (n + 2)) :
    Fin (n + 1) → X :=
  fun i => v (j.succAbove i)

/-- Prepend a cone apex to an ordered base tuple. -/
def coneTuple
    {X : Type} {n : Nat} (a : X) (v : Fin n → X) :
    Fin (n + 1) → X :=
  Fin.cases a v

/-- Ordered full facet of one recursive cylinder cell. -/
noncomputable def facetTuple
    (d : Nat) (q : RelativeSubdivisionCylinderCombinatorics.Cell d) (j : Fin (d + 2)) :
    Fin (d + 1) → Delta d × Set.Icc (0 : Real) 1 :=
  deleteTuple (RelativeSubdivisionCylinderCombinatorics.vertex d q) j

/-- Alternating weighted boundary of the complete recursive cylinder chain. -/
noncomputable def fullBoundaryPairing
    (R : Type) [CommRing R] (d : Nat)
    (W : (Fin (d + 1) → Delta d × Set.Icc (0 : Real) 1) → R) : R :=
  ∑ q : RelativeSubdivisionCylinderCombinatorics.Cell d,
    RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R d q *
      ∑ j : Fin (d + 2),
        SimplicialChain.faceSign j * W (facetTuple d q j)

/-- Weighted cone-base chain. -/
noncomputable def basePairing
    (R : Type) [CommRing R] (d : Nat)
    (W : (Fin (d + 1) → Delta d × Set.Icc (0 : Real) 1) → R) : R :=
  ∑ q : RelativeSubdivisionCylinderCombinatorics.Cell d, RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R d q * W (RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetVertex d q)

/-- Boundary weight of one ordered `d`-simplex tuple. -/
def tupleBoundaryWeight
    {R X : Type} [CommRing R] (d : Nat)
    (W : (Fin d → X) → R) (v : Fin (d + 1) → X) : R :=
  ∑ j : Fin (d + 1), ((-1 : R) ^ j.1) *
    W (fun i : Fin d => v (j.succAbove i))

/-- The triangulated cone-base chain is closed in positive dimension. -/
def BaseChainClosed (R : Type) [CommRing R] (d : Nat) : Prop :=
  match d with
  | 0 => True
  | n + 1 => ∀ W :
      (Fin (n + 1) → Delta (n + 1) × Set.Icc (0 : Real) 1) → R,
      RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetPairing R (n + 1) (tupleBoundaryWeight (n + 1) W) = 0

/-- Every non-base facet is the cone over the corresponding facet of the base tuple. -/
theorem facetTuple_succ_eq_coneTuple
    (d : Nat) (q : RelativeSubdivisionCylinderCombinatorics.Cell d) (j : Fin (d + 1)) :
    facetTuple d q j.succ =
      coneTuple (RelativeSubdivisionCylinderCombinatorics.apex d)
        (fun i : Fin d =>
          RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetVertex d q
            (j.succAbove i)) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [facetTuple, deleteTuple, coneTuple, RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetVertex]
  · simp [facetTuple, deleteTuple, coneTuple, RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetVertex,
      Fin.succ_succAbove_succ]

/-- The base facet is the declared triangulated-boundary simplex. -/
theorem facetTuple_zero_eq_base
    (d : Nat) (q : RelativeSubdivisionCylinderCombinatorics.Cell d) :
    facetTuple d q 0 = RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetVertex d q := by
  funext i
  simp [facetTuple, deleteTuple, RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetVertex]

/-- Successor face signs differ from the corresponding base-boundary signs by a minus sign. -/
theorem faceSign_succ
    {R : Type} [CommRing R] {n : Nat} (j : Fin (n + 1)) :
    (SimplicialChain.faceSign j.succ : R) =
      -((-1 : R) ^ j.1) := by
  simp [SimplicialChain.faceSign, pow_succ]

/-- Closedness of the cone-base chain kills every radial cone facet. -/
theorem radialPairing_eq_zero_of_baseClosed
    (R : Type) [CommRing R] (d : Nat)
    (hclosed : BaseChainClosed R d)
    (W : (Fin (d + 1) → Delta d × Set.Icc (0 : Real) 1) → R) :
    (∑ q : RelativeSubdivisionCylinderCombinatorics.Cell d,
      RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R d q *
        ∑ j : Fin (d + 1),
          SimplicialChain.faceSign j.succ * W (facetTuple d q j.succ)) = 0 := by
  cases d with
  | zero =>
      simp_rw [facetTuple_succ_eq_coneTuple]
      have hcone :
          coneTuple (RelativeSubdivisionCylinderCombinatorics.apex 0)
              (fun i : Fin 0 =>
                RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetVertex 0
                  (Sum.inl PUnit.unit) i.succ) =
          coneTuple (RelativeSubdivisionCylinderCombinatorics.apex 0)
              (fun i : Fin 0 =>
                RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetVertex 0
                  (Sum.inr (1 : Equiv.Perm (Fin 1))) i.succ) := by
        funext i
        refine Fin.cases ?_ (fun j => Fin.elim0 j) i
        rfl
      simp [RelativeSubdivisionCylinderCombinatorics.Cell,
        RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient,
        SimplicialChain.faceSign, hcone, permSignCoeff]
  | succ n =>
      have hbase := hclosed
        (fun v => W (coneTuple (RelativeSubdivisionCylinderCombinatorics.apex (n + 1)) v))
      simp_rw [facetTuple_succ_eq_coneTuple, faceSign_succ]
      calc
        (∑ q : RelativeSubdivisionCylinderCombinatorics.Cell (n + 1),
          RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R (n + 1) q *
            ∑ j : Fin (n + 2),
              -((-1 : R) ^ j.1) *
                W (coneTuple (RelativeSubdivisionCylinderCombinatorics.apex (n + 1))
                  (fun i : Fin (n + 1) =>
                    RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetVertex
                      (n + 1) q (j.succAbove i)))) =
          - RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetPairing R (n + 1)
              (tupleBoundaryWeight (n + 1)
                (fun v => W (coneTuple (RelativeSubdivisionCylinderCombinatorics.apex (n + 1)) v))) := by
            unfold RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetPairing tupleBoundaryWeight
            simp only [Finset.mul_sum]
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro q hq
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            ring
        _ = 0 := by rw [hbase]; simp

/-- Once the base boundary chain is closed, the full cylinder boundary is exactly its cone-base
chain. -/
theorem fullBoundaryPairing_eq_base_of_closed
    (R : Type) [CommRing R] (d : Nat)
    (hclosed : BaseChainClosed R d)
    (W : (Fin (d + 1) → Delta d × Set.Icc (0 : Real) 1) → R) :
    fullBoundaryPairing R d W = basePairing R d W := by
  classical
  unfold fullBoundaryPairing basePairing
  have hrad := radialPairing_eq_zero_of_baseClosed R d hclosed W
  calc
    (∑ q : RelativeSubdivisionCylinderCombinatorics.Cell d,
      RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R d q *
        ∑ j : Fin (d + 2),
          SimplicialChain.faceSign j * W (facetTuple d q j)) =
      (∑ q : RelativeSubdivisionCylinderCombinatorics.Cell d,
        RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R d q * W (RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetVertex d q)) +
      (∑ q : RelativeSubdivisionCylinderCombinatorics.Cell d,
        RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R d q *
          ∑ j : Fin (d + 1),
            SimplicialChain.faceSign j.succ * W (facetTuple d q j.succ)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro q hq
        rw [Fin.sum_univ_succ]
        rw [facetTuple_zero_eq_base]
        simp [SimplicialChain.faceSign]
        ring
    _ = _ := by rw [hrad, add_zero]

/-! ## Recursive closedness of the cone-base chain -/

/-- Embed an ordered tuple into the side opposite `k`. -/
noncomputable def sideTuple
    (d : Nat) (k : Fin (d + 2))
    (v : Fin (d + 1) → Delta d × Set.Icc (0 : Real) 1) :
    Fin (d + 1) → Delta (d + 1) × Set.Icc (0 : Real) 1 :=
  fun i => RelativeSubdivisionCylinderCombinatorics.sidePoint d k (v i)

/-- Deleting a vertex from an embedded side tuple commutes with the side embedding. -/
theorem delete_sideTuple
    (d : Nat) (k : Fin (d + 2))
    (v : Fin (d + 2) → Delta d × Set.Icc (0 : Real) 1)
    (j : Fin (d + 2)) :
    sideTuple d k (deleteTuple v j) =
      fun i : Fin (d + 1) =>
        RelativeSubdivisionCylinderCombinatorics.sidePoint d k
          (v (j.succAbove i)) := by
  rfl

/-- Boundary of an upper barycentric tuple, expressed on the original boundary faces. -/
theorem upper_boundary_pairing
    (R : Type) [CommRing R] (d : Nat)
    (W : (Fin (d + 1) → Delta (d + 1) × Set.Icc (0 : Real) 1) → R) :
    (∑ pi : Equiv.Perm (Fin (d + 2)),
      permSignCoeff R pi *
        tupleBoundaryWeight (d + 1) W (RelativeSubdivisionCylinderCombinatorics.upperBoundaryVertex (d + 1) pi)) =
      ∑ k : Fin (d + 2),
        SimplicialChain.faceSign k *
          ∑ rho : Equiv.Perm (Fin (d + 1)),
            permSignCoeff R rho *
              W (fun i => RelativeSubdivisionCylinderCombinatorics.sidePoint d k (RelativeSubdivisionCylinderCombinatorics.upperBoundaryVertex d rho i)) := by
  let Wmap : (Delta d → Delta (d + 1) × Set.Icc (0 : Real) 1) → R :=
    fun tau => W (fun i => tau (SphereOddDegree.FiniteSimplex.vertex (S := Real) i))
  have h := oneStep_weighted_boundary (R := R) d
    (fun x : Delta (d + 1) => (x, ⟨1, by norm_num⟩)) Wmap
  simpa [Wmap, tupleBoundaryWeight, iteratedFacetMap, iteratedBoundaryMap,
    RelativeSubdivisionCylinderCombinatorics.upperBoundaryVertex, RelativeSubdivisionCylinderCombinatorics.sidePoint, cofacePoint,
    affineCompMap_succ, affineSubdivContinuousMap_apply,
    affineSubdivMap_vertex, SimplicialChain.faceSign] using h

/-- A lower boundary face is the lower boundary tuple in the corresponding spatial side. -/
theorem delete_lowerBoundaryVertex_eq_side
    (d : Nat) (k : Fin (d + 2)) :
    deleteTuple (RelativeSubdivisionCylinderCombinatorics.lowerBoundaryVertex (d + 1)) k =
      sideTuple d k (RelativeSubdivisionCylinderCombinatorics.lowerBoundaryVertex d) := by
  funext i
  apply Prod.ext
  · simp [deleteTuple, sideTuple, RelativeSubdivisionCylinderCombinatorics.lowerBoundaryVertex, RelativeSubdivisionCylinderCombinatorics.sidePoint,
      SphereOddDegree.FiniteSimplex.map, SphereOddDegree.FiniteSimplex.vertex]
  · rfl

/-- A recursively triangulated codimension-two side occurs twice with opposite total sign. -/
theorem recursive_side_side_zero
    (R : Type) [CommRing R] (n : Nat)
    (W : (Fin (n + 2) → Delta (n + 2) × Set.Icc (0 : Real) 1) → R) :
    (∑ k : Fin (n + 3),
      SimplicialChain.faceSign k *
        ∑ l : Fin (n + 2),
          SimplicialChain.faceSign l *
            ∑ q : RelativeSubdivisionCylinderCombinatorics.Cell n,
              RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R n q *
                W (fun i => RelativeSubdivisionCylinderCombinatorics.sidePoint (n + 1) k
                  (RelativeSubdivisionCylinderCombinatorics.sidePoint n l (RelativeSubdivisionCylinderCombinatorics.vertex n q i)))) = 0 := by
  classical
  let F : Fin (n + 3) → Fin (n + 2) →
      RelativeSubdivisionCylinderCombinatorics.Cell n → R :=
    fun k l q => W (fun i => RelativeSubdivisionCylinderCombinatorics.sidePoint (n + 1) k
      (RelativeSubdivisionCylinderCombinatorics.sidePoint n l
        (RelativeSubdivisionCylinderCombinatorics.vertex n q i)))
  change (∑ k : Fin (n + 3), SimplicialChain.faceSign k *
    ∑ l : Fin (n + 2), SimplicialChain.faceSign l *
      ∑ q : RelativeSubdivisionCylinderCombinatorics.Cell n,
        RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R n q * F k l q) = 0
  have hq : ∀ q : RelativeSubdivisionCylinderCombinatorics.Cell n,
      (∑ k : Fin (n + 3), SimplicialChain.faceSign k *
        ∑ l : Fin (n + 2), SimplicialChain.faceSign l * F k l q) = 0 := by
    intro q
    let Wq : (Delta n → Delta (n + 2)) → R := fun tau =>
      W (fun i => (tau (RelativeSubdivisionCylinderCombinatorics.vertex n q i).1,
        (RelativeSubdivisionCylinderCombinatorics.vertex n q i).2))
    have h := double_boundary_weighted_zero (R := R) n
      (fun x : Delta (n + 2) => x) Wq
    simpa [F, Wq, RelativeSubdivisionCylinderCombinatorics.sidePoint, cofacePoint,
      SphereOddDegree.FiniteSimplex.map, SimplicialChain.faceSign] using h
  calc
    (∑ k : Fin (n + 3), SimplicialChain.faceSign k *
      ∑ l : Fin (n + 2), SimplicialChain.faceSign l *
        ∑ q : RelativeSubdivisionCylinderCombinatorics.Cell n,
          RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R n q * F k l q) =
      ∑ q : RelativeSubdivisionCylinderCombinatorics.Cell n,
        RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R n q *
          ∑ k : Fin (n + 3), SimplicialChain.faceSign k *
            ∑ l : Fin (n + 2), SimplicialChain.faceSign l * F k l q := by
        simp_rw [Finset.mul_sum]
        calc
          (∑ k : Fin (n + 3), ∑ l : Fin (n + 2),
            ∑ q : RelativeSubdivisionCylinderCombinatorics.Cell n,
              SimplicialChain.faceSign k *
                (SimplicialChain.faceSign l *
                  (RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R n q * F k l q))) =
            ∑ k : Fin (n + 3), ∑ q : RelativeSubdivisionCylinderCombinatorics.Cell n,
              ∑ l : Fin (n + 2), SimplicialChain.faceSign k *
                (SimplicialChain.faceSign l *
                  (RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R n q * F k l q)) := by
              apply Finset.sum_congr rfl
              intro k hk
              exact Finset.sum_comm
          _ = ∑ q : RelativeSubdivisionCylinderCombinatorics.Cell n,
              ∑ k : Fin (n + 3), ∑ l : Fin (n + 2), SimplicialChain.faceSign k *
                (SimplicialChain.faceSign l *
                  (RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R n q * F k l q)) :=
            Finset.sum_comm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro q hqmem
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro l hl
            ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro q hqmem
      rw [hq q, mul_zero]

/-- The lower coarse boundary of a tuple boundary is the signed sum of the lower boundaries
inside the ambient spatial sides. -/
theorem lowerPairing_tupleBoundaryWeight
    (R : Type) [CommRing R] (d : Nat)
    (W : (Fin (d + 1) → Delta (d + 1) × Set.Icc (0 : Real) 1) → R) :
    RelativeSubdivisionCylinderCombinatorics.Oriented.lowerPairing R (d + 1)
        (tupleBoundaryWeight (d + 1) W) =
      ∑ k : Fin (d + 2), SimplicialChain.faceSign k *
        RelativeSubdivisionCylinderCombinatorics.Oriented.lowerPairing R d
          (fun v => W (sideTuple d k v)) := by
  classical
  unfold RelativeSubdivisionCylinderCombinatorics.Oriented.lowerPairing tupleBoundaryWeight
  simp only [SimplicialChain.faceSign]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  change -((-1 : R) ^ (k : Nat) * W
      (deleteTuple (RelativeSubdivisionCylinderCombinatorics.lowerBoundaryVertex (d + 1)) k)) = _
  rw [delete_lowerBoundaryVertex_eq_side]
  ring

/-- The upper barycentric boundary of a tuple boundary is the signed sum of the upper boundaries
inside the ambient spatial sides. -/
theorem upperPairing_tupleBoundaryWeight
    (R : Type) [CommRing R] (d : Nat)
    (W : (Fin (d + 1) → Delta (d + 1) × Set.Icc (0 : Real) 1) → R) :
    RelativeSubdivisionCylinderCombinatorics.Oriented.upperPairing R (d + 1)
        (tupleBoundaryWeight (d + 1) W) =
      ∑ k : Fin (d + 2), SimplicialChain.faceSign k *
        RelativeSubdivisionCylinderCombinatorics.Oriented.upperPairing R d
          (fun v => W (sideTuple d k v)) := by
  unfold RelativeSubdivisionCylinderCombinatorics.Oriented.upperPairing
  unfold sideTuple
  exact upper_boundary_pairing R d W

/-- Taking the boundary of every recursive side cell gives the negative signed sum of the complete
lower-dimensional cylinder boundaries in the ambient spatial sides. -/
theorem sidePairing_tupleBoundaryWeight
    (R : Type) [CommRing R] (d : Nat)
    (W : (Fin (d + 1) → Delta (d + 1) × Set.Icc (0 : Real) 1) → R) :
    RelativeSubdivisionCylinderCombinatorics.Oriented.sidePairing R d
        (tupleBoundaryWeight (d + 1) W) =
      -(∑ k : Fin (d + 2), SimplicialChain.faceSign k *
        fullBoundaryPairing R d (fun v => W (sideTuple d k v))) := by
  classical
  unfold RelativeSubdivisionCylinderCombinatorics.Oriented.sidePairing
    tupleBoundaryWeight fullBoundaryPairing
  simp only [SimplicialChain.faceSign, facetTuple, deleteTuple]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring_nf; rfl

/-- Expanding the remaining negative weighted recursive-side sum produces exactly the
codimension-two side-side sum. -/
theorem neg_weighted_sidePairing_eq_recursive_side_side
    (R : Type) [CommRing R] (n : Nat)
    (W : (Fin (n + 2) → Delta (n + 2) × Set.Icc (0 : Real) 1) → R) :
    -(∑ k : Fin (n + 3), SimplicialChain.faceSign k *
      RelativeSubdivisionCylinderCombinatorics.Oriented.sidePairing R n
        (fun v => W (sideTuple (n + 1) k v))) =
      ∑ k : Fin (n + 3), SimplicialChain.faceSign k *
        ∑ l : Fin (n + 2), SimplicialChain.faceSign l *
          ∑ q : RelativeSubdivisionCylinderCombinatorics.Cell n,
            RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R n q *
              W (fun i => RelativeSubdivisionCylinderCombinatorics.sidePoint (n + 1) k
                (RelativeSubdivisionCylinderCombinatorics.sidePoint n l
                  (RelativeSubdivisionCylinderCombinatorics.vertex n q i))) := by
  classical
  unfold RelativeSubdivisionCylinderCombinatorics.Oriented.sidePairing
  simp only [SimplicialChain.faceSign]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring_nf; rfl

/-- The triangulated boundary chain of the recursive cylinder is closed in every dimension. -/
theorem baseChainClosed
    (R : Type) [CommRing R] : ∀ d : Nat, BaseChainClosed R d := by
  intro d
  induction d with
  | zero => trivial
  | succ d ih =>
      change ∀ W : (Fin (d + 1) → Delta (d + 1) × Set.Icc (0 : Real) 1) → R,
        RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetPairing R (d + 1)
          (tupleBoundaryWeight (d + 1) W) = 0
      intro W
      rw [RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetPairing_succ]
      rw [lowerPairing_tupleBoundaryWeight, upperPairing_tupleBoundaryWeight,
        sidePairing_tupleBoundaryWeight]
      have hfull (k : Fin (d + 2)) :
          fullBoundaryPairing R d (fun v => W (sideTuple d k v)) =
            RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetPairing R d
              (fun v => W (sideTuple d k v)) := by
        rw [fullBoundaryPairing_eq_base_of_closed R d ih]
        rfl
      simp_rw [hfull]
      cases d with
      | zero =>
          simp_rw [RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetPairing_zero,
            mul_add, Finset.sum_add_distrib]
          ring
      | succ n =>
          calc
            _ = -(∑ k : Fin (n + 3), SimplicialChain.faceSign k *
                RelativeSubdivisionCylinderCombinatorics.Oriented.sidePairing R n
                  (fun v => W (sideTuple (n + 1) k v))) := by
                simp_rw [RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetPairing_succ,
                  mul_add, Finset.sum_add_distrib]
                ring
            _ = ∑ k : Fin (n + 3), SimplicialChain.faceSign k *
                ∑ l : Fin (n + 2), SimplicialChain.faceSign l *
                  ∑ q : RelativeSubdivisionCylinderCombinatorics.Cell n,
                    RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient R n q *
                      W (fun i => RelativeSubdivisionCylinderCombinatorics.sidePoint (n + 1) k
                        (RelativeSubdivisionCylinderCombinatorics.sidePoint n l
                          (RelativeSubdivisionCylinderCombinatorics.vertex n q i))) :=
              neg_weighted_sidePairing_eq_recursive_side_side R n W
            _ = 0 := recursive_side_side_zero R n W

/-- Exact arbitrary-weight boundary formula for the recursive one-step cylinder. -/
theorem fullBoundaryPairing_eq_base
    (R : Type) [CommRing R] (d : Nat)
    (W : (Fin (d + 1) → Delta d × Set.Icc (0 : Real) 1) → R) :
    fullBoundaryPairing R d W = basePairing R d W :=
  fullBoundaryPairing_eq_base_of_closed R d (baseChainClosed R d) W

end RelativeSubdivisionCylinderBoundary
end FoxNeuwirthOrderComplex
end NRR
