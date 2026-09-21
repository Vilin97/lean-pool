/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBCanonicalCoordinateSplit
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Measure.Prod
/-!
# Route B: measurability of the complete mixed-face bad set

The existential witness ranges over the compact standard simplex.  Strict
positivity is exhausted by countably many closed threshold conditions.  Each
threshold relation is closed in parameter space times the simplex, and its
projection is closed because the simplex is compact.  Hence the complete bad
set is a countable union of closed sets.
-/

namespace NRR

open FoxNeuwirthOrderComplex
open MeasureTheory
open scoped BigOperators

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar
namespace RouteB

open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open Parameters
open Polynomials
open RelativeGenericity

variable {p N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

/-- One coordinate of the joint affine value as a function of the movable
assignment and the simplex witness. -/
noncomputable def jointAffineCoordinate
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (z : MovableParameterSpace hp C × StandardSimplex p) (j : Fin p) : Real :=
  affineValue
    (localVertexMap hp C
      (assignmentOfMovableParameters hp C base z.1) κ.cell) z.2 j

/-- Joint deviation coordinate. -/
noncomputable def jointDeviation
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (z : MovableParameterSpace hp C × StandardSimplex p)
    (r : Fin (p - 1)) : Real :=
  deviation hp (fun j => jointAffineCoordinate hp C base κ z j) r

/-- Joint mean coordinate. -/
noncomputable def jointMean
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (z : MovableParameterSpace hp C × StandardSimplex p) : Real :=
  mean hp (fun j => jointAffineCoordinate hp C base κ z j)

/-- Joint affine coordinates are continuous in both the movable parameters and
the simplex witness. -/
theorem continuous_jointAffineCoordinate
    (base : Assignment hp C) (κ : MixedFaceCase hp C) (j : Fin p) :
    Continuous (fun z : MovableParameterSpace hp C × StandardSimplex p =>
      jointAffineCoordinate hp C base κ z j) := by
  unfold jointAffineCoordinate affineValue
  exact continuous_finsetSum _ fun i _ => by
    have hw : Continuous (fun z : MovableParameterSpace hp C × StandardSimplex p =>
        (z.2 : Fin (p + 1) → Real) i) :=
      (continuous_apply i).comp (continuous_induced_dom.comp continuous_snd)
    have ha : Continuous (fun z : MovableParameterSpace hp C × StandardSimplex p =>
        assignmentOfMovableParameters hp C base z.1
          (localParameter hp C κ.cell i j)) :=
      (continuous_assignmentOfMovableParameters_apply hp C base
        (localParameter hp C κ.cell i j)).comp continuous_fst
    simp only [localVertexMap_value_apply_eq_assignment_localParameter]
    change Continuous ((fun z : MovableParameterSpace hp C × StandardSimplex p => z.2 i) *
      fun z => assignmentOfMovableParameters hp C base z.1
        (localParameter hp C κ.cell i j))
    exact hw.mul ha

/-- Joint deviations are continuous. -/
theorem continuous_jointDeviation
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (r : Fin (p - 1)) :
    Continuous (fun z : MovableParameterSpace hp C × StandardSimplex p =>
      jointDeviation hp C base κ z r) := by
  unfold jointDeviation deviation
  exact
    (continuous_jointAffineCoordinate hp C base κ
      (ReferenceAffineOrbitCount.coordinateLabel hp r)).sub
    (continuous_jointAffineCoordinate hp C base κ
      (ReferenceAffineOrbitCount.lastLabel hp))

/-- The joint mean is continuous. -/
theorem continuous_jointMean
    (base : Assignment hp C) (κ : MixedFaceCase hp C) :
    Continuous (fun z : MovableParameterSpace hp C × StandardSimplex p =>
      jointMean hp C base κ z) := by
  unfold jointMean mean coordinateMean
  exact (continuous_finsetSum _ fun j _ =>
    continuous_jointAffineCoordinate hp C base κ j).div_const (p : Real)

/-- Closed threshold relation.  The natural numbers replace the two strict
positivity conditions by positive lower bounds. -/
def mixedFaceThresholdRelation
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (n m : Nat) :
    Set (MovableParameterSpace hp C × StandardSimplex p) :=
  ((({z | z.2 κ.omitted₀ = 0} ∩
      {z | z.2 κ.omitted₁ = 0}) ∩
      {z | 1 / ((n : Real) + 1) ≤ z.2 κ.retained}) ∩
      (⋂ r : Fin (p - 1), {z | jointDeviation hp C base κ z r = 0})) ∩
      {z | 1 / ((m : Real) + 1) ≤ jointMean hp C base κ z}

/-- Every threshold relation is closed. -/
theorem isClosed_mixedFaceThresholdRelation
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (n m : Nat) :
    IsClosed (mixedFaceThresholdRelation hp C base κ n m) := by
  have h0 : IsClosed {z : MovableParameterSpace hp C × StandardSimplex p |
      z.2 κ.omitted₀ = 0} :=
    isClosed_eq
      ((continuous_apply κ.omitted₀).comp
        (continuous_induced_dom.comp continuous_snd)) continuous_const
  have h1 : IsClosed {z : MovableParameterSpace hp C × StandardSimplex p |
      z.2 κ.omitted₁ = 0} :=
    isClosed_eq
      ((continuous_apply κ.omitted₁).comp
        (continuous_induced_dom.comp continuous_snd)) continuous_const
  have hret : IsClosed {z : MovableParameterSpace hp C × StandardSimplex p |
      1 / ((n : Real) + 1) ≤ z.2 κ.retained} :=
    isClosed_le continuous_const
      ((continuous_apply κ.retained).comp
        (continuous_induced_dom.comp continuous_snd))
  have hdev : IsClosed (⋂ r : Fin (p - 1),
      {z : MovableParameterSpace hp C × StandardSimplex p |
        jointDeviation hp C base κ z r = 0}) :=
    isClosed_iInter fun r =>
      isClosed_eq (continuous_jointDeviation hp C base κ r) continuous_const
  have hmean : IsClosed {z : MovableParameterSpace hp C × StandardSimplex p |
      1 / ((m : Real) + 1) ≤ jointMean hp C base κ z} :=
    isClosed_le continuous_const (continuous_jointMean hp C base κ)
  exact (((h0.inter h1).inter hret).inter hdev).inter hmean

/-- Projection of one closed threshold relation to movable parameter space. -/
def mixedFaceThresholdBadSet
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (n m : Nat) : Set (MovableParameterSpace hp C) :=
  Prod.fst '' mixedFaceThresholdRelation hp C base κ n m

/-- Compactness of the simplex makes every threshold projection closed. -/
theorem isClosed_mixedFaceThresholdBadSet
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (n m : Nat) :
    IsClosed (mixedFaceThresholdBadSet hp C base κ n m) := by
  have hcompact : IsCompact (Set.univ : Set (StandardSimplex p)) := by
    let f : SphereOddDegree.AffineBarycentricSubdivision.Delta p → StandardSimplex p :=
      StandardSimplex.ofDelta
    have hf : Continuous f := by
      rw [continuous_induced_rng]
      exact continuous_subtype_val
    have hrange : Set.range f = Set.univ := by
      ext w
      constructor
      · exact fun _ => Set.mem_univ _
      · intro _
        exact ⟨StandardSimplex.toDelta w, StandardSimplex.ofDelta_toDelta w⟩
    letI : CompactSpace (SphereOddDegree.AffineBarycentricSubdivision.Delta p) :=
      isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin (p + 1)))
    simpa [hrange] using (isCompact_range hf)
  letI : CompactSpace (StandardSimplex p) :=
    isCompact_univ_iff.mp hcompact
  exact isClosedMap_fst_of_compactSpace
    (mixedFaceThresholdRelation hp C base κ n m)
    (isClosed_mixedFaceThresholdRelation hp C base κ n m)

/-- The complete existential bad set is exhausted by the closed threshold
projections. -/
theorem mixedFaceBadSet_eq_iUnion_threshold
    (base : Assignment hp C) (κ : MixedFaceCase hp C) :
    mixedFaceBadSet hp C base κ =
      ⋃ n : Nat, ⋃ m : Nat, mixedFaceThresholdBadSet hp C base κ n m := by
  ext x
  constructor
  · rintro ⟨w, h0, h1, hret, hdev, hmean⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hret
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hmean
    apply Set.mem_iUnion.mpr
    refine ⟨n, Set.mem_iUnion.mpr ⟨m, ?_⟩⟩
    refine ⟨(x, w), ?_, rfl⟩
    simp only [mixedFaceThresholdRelation, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨⟨⟨⟨h0, h1⟩, le_of_lt hn⟩, hdev⟩, le_of_lt hm⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨m, hx⟩
    rcases hx with ⟨z, hz, rfl⟩
    rcases z with ⟨x, w⟩
    simp only [mixedFaceThresholdRelation, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_iInter] at hz
    rcases hz with ⟨⟨⟨⟨h0, h1⟩, hret⟩, hdev⟩, hmean⟩
    have hnpos : 0 < 1 / ((n : Real) + 1) := by positivity
    have hmpos : 0 < 1 / ((m : Real) + 1) := by positivity
    exact ⟨w, h0, h1, lt_of_lt_of_le hnpos hret, hdev,
      lt_of_lt_of_le hmpos hmean⟩

/-- The complete mixed-face bad set is measurable. -/
theorem measurableSet_mixedFaceBadSet
    (base : Assignment hp C) (κ : MixedFaceCase hp C) :
    MeasurableSet (mixedFaceBadSet hp C base κ) := by
  rw [mixedFaceBadSet_eq_iUnion_threshold hp C base κ]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
    (isClosed_mixedFaceThresholdBadSet hp C base κ n m).measurableSet

end RouteB
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
