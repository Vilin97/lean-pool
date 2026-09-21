/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarThinSlabs
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarMiddlePrismBoundary
/-!
# Signed boundary of a thin-time stack

A thin stack is a disjoint union of unrefined staircase prisms whose geometric copies meet along
successive time slices.  This file proves its pointwise signed boundary formula without classifying
all quotient facets.  For one quotient facet `s`, pull its characteristic function back to every
slab and apply the arbitrary prime-invariant weighted boundary theorem for the ordinary staircase
prism.  The upper endpoint term of slab `r` is literally the lower endpoint term of slab `r+1`, so
the finite sum telescopes.  Only time zero and time one remain.
-/

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeCollarThinSlabsBoundary

open ExplicitAffineRelativeCollar
open EquivariantPrismGlobalCancellation
open EquivariantPrismNonhorizontalCancellation
open EquivariantPrismHorizontalEndpointIdentification
open RelativeCollarMiddlePrism
open RelativeCollarMiddlePrismBoundary
open RelativeCollarMiddlePrismEndpoints
open RelativeCollarThinSlabs
open RefinedAffineMap
open EquivariantPrismVertexParameters

variable {p : Nat}

/-- The unrefined staircase-prism cell system used in every slab. -/
noncomputable abbrev BaseCells (hp : Nat.Prime p) (N : Nat) :=
  RelativeCollarMiddlePrism.cellSystem hp N 0

/-- The complete `m`-slab cell system. -/
noncomputable abbrev StackCells (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m) :=
  RelativeCollarThinSlabs.cellSystem hp N m hm

/-- Apply the affine time rescaling of slab `r` to an arbitrary facet map. -/
noncomputable def slabFacetMap
    (m : Nat) (hm : 0 < m) (r : Fin m)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) :
    Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1 :=
  fun x => ((tau x).1, slabTime m hm r (tau x).2)

@[simp] theorem slabFacetMap_fst
    (m : Nat) (hm : 0 < m) (r : Fin m)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1)
    (x : Delta (p - 1)) :
    (slabFacetMap m hm r tau x).1 = (tau x).1 :=
  rfl

@[simp] theorem slabFacetMap_time
    (m : Nat) (hm : 0 < m) (r : Fin m)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1)
    (x : Delta (p - 1)) :
    (slabFacetMap m hm r tau x).2.1 =
      ((r.1 : Real) + (tau x).2.1) / (m : Real) :=
  rfl

/-- Slab rescaling commutes with simultaneous prime translation. -/
theorem slabFacetMap_translate
    (hp : Nat.Prime p) (m : Nat) (hm : 0 < m) (r : Fin m)
    (g : PrimeSymmetry p)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) :
    slabFacetMap m hm r
        (EquivariantPrismNonhorizontalCancellation.translateFacetMap hp g tau) =
      EquivariantPrismNonhorizontalCancellation.translateFacetMap
        hp g (slabFacetMap m hm r tau) :=
  rfl

/-- Embed one base-prism facet occurrence into slab `r`. -/
def stackOccurrence
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (r : Fin m) (o : (BaseCells hp N).FacetOccurrence) :
    (StackCells hp N m hm).FacetOccurrence :=
  ((r, o.1), o.2)

/-- Ordered geometric vertices of an embedded occurrence are the rescaled base vertices. -/
theorem facetSignature_stackOccurrence
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (r : Fin m) (o : (BaseCells hp N).FacetOccurrence) :
    (StackCells hp N m hm).facetSignature
        (stackOccurrence hp N m hm r o) =
      fun i => slabPoint m hm r ((BaseCells hp N).facetSignature o i) := by
  funext i
  rfl

/-- The transformed old occurrence map and the explicit stack occurrence have the same ordered
geometric vertex tuple. -/
theorem mapVertexSignature_slabOccurrence
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (r : Fin m) (o : (BaseCells hp N).FacetOccurrence) :
    EquivariantPrismNonhorizontalCancellation.mapVertexSignature
        (slabFacetMap m hm r
          (EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap hp N 0 o)) =
      (StackCells hp N m hm).facetSignature
        (stackOccurrence hp N m hm r o) := by
  have hbase :
      EquivariantPrismNonhorizontalCancellation.mapVertexSignature
          (EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap hp N 0 o) =
        (BaseCells hp N).facetSignature o := by
    rw [EquivariantPrismNonhorizontalCancellation.mapVertexSignature_occurrenceFacetMap]
    rfl
  funext i
  change
    RelativeCollarThinSlabs.slabPoint m hm r
        (EquivariantPrismNonhorizontalCancellation.mapVertexSignature
            (EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap hp N 0 o) i) =
      RelativeCollarThinSlabs.slabPoint m hm r
        ((BaseCells hp N).facetSignature o i)
  rw [congrFun hbase i]

/-- Characteristic weight of one ordered prime-orbit facet of the complete thin stack. -/
noncomputable def stackFacetOrbitIndicator
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet)
    (tau : Delta (p - 1) →
      Realization p × Set.Icc (0 : Real) 1) : ZMod p := by
  classical
  exact if ∃ o : (StackCells hp N m hm).FacetOccurrence,
      (StackCells hp N m hm).facetClass o = s ∧
        ∃ g : PrimeSymmetry p,
          EquivariantPrismNonhorizontalCancellation.mapVertexSignature tau =
            fun i =>
              g • (StackCells hp N m hm).facetSignature o i
    then 1
    else 0

/-- The stack characteristic weight is invariant under simultaneous prime translation. -/
theorem stackFacetOrbitIndicator_translate
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet)
    (g : PrimeSymmetry p)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) :
    stackFacetOrbitIndicator hp N m hm s (EquivariantPrismNonhorizontalCancellation.translateFacetMap hp g tau) =
      stackFacetOrbitIndicator hp N m hm s tau := by
  classical
  unfold stackFacetOrbitIndicator
  have hiff :
      (∃ o : (StackCells hp N m hm).FacetOccurrence,
          (StackCells hp N m hm).facetClass o = s ∧
            ∃ h : PrimeSymmetry p,
              EquivariantPrismNonhorizontalCancellation.mapVertexSignature (EquivariantPrismNonhorizontalCancellation.translateFacetMap hp g tau) =
                fun i => h • (StackCells hp N m hm).facetSignature o i) ↔
      (∃ o : (StackCells hp N m hm).FacetOccurrence,
          (StackCells hp N m hm).facetClass o = s ∧
            ∃ h : PrimeSymmetry p,
              EquivariantPrismNonhorizontalCancellation.mapVertexSignature tau =
                fun i => h • (StackCells hp N m hm).facetSignature o i) := by
    constructor
    · rintro ⟨o, ho, h, hh⟩
      refine ⟨o, ho, g⁻¹ * h, ?_⟩
      funext i
      have hi := congrFun hh i
      simp only [EquivariantPrismNonhorizontalCancellation.mapVertexSignature_translateFacetMap] at hi
      have hi' := congrArg (fun z : EquivariantPrismVertexParameters.CylinderPoint p => g⁻¹ • z) hi
      simpa [mul_smul] using hi'
    · rintro ⟨o, ho, h, hh⟩
      refine ⟨o, ho, g * h, ?_⟩
      funext i
      simp [EquivariantPrismNonhorizontalCancellation.mapVertexSignature_translateFacetMap, hh, mul_smul]
  simp only [hiff]

/-- Pull the stack-facet characteristic weight back to the ordinary prism maps in slab `r`. -/
noncomputable def slabFacetOrbitIndicator
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet) (r : Fin m)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) : ZMod p :=
  stackFacetOrbitIndicator hp N m hm s (slabFacetMap m hm r tau)

/-- The pulled-back characteristic weight is prime invariant. -/
theorem slabFacetOrbitIndicator_translate
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet) (r : Fin m)
    (g : PrimeSymmetry p)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) :
    slabFacetOrbitIndicator hp N m hm s r (EquivariantPrismNonhorizontalCancellation.translateFacetMap hp g tau) =
      slabFacetOrbitIndicator hp N m hm s r tau := by
  unfold slabFacetOrbitIndicator
  rw [slabFacetMap_translate]
  exact stackFacetOrbitIndicator_translate hp N m hm s g
    (slabFacetMap m hm r tau)

/-- On an actual stack occurrence, the characteristic weight is the Kronecker delta of its
quotient-facet class. -/
theorem stackFacetOrbitIndicator_occurrence
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet)
    (o : (StackCells hp N m hm).FacetOccurrence)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1)
    (htau : EquivariantPrismNonhorizontalCancellation.mapVertexSignature tau = (StackCells hp N m hm).facetSignature o) :
    stackFacetOrbitIndicator hp N m hm s tau =
      if (StackCells hp N m hm).facetClass o = s then 1 else 0 := by
  classical
  by_cases hos : (StackCells hp N m hm).facetClass o = s
  · have hex : ∃ o' : (StackCells hp N m hm).FacetOccurrence,
        (StackCells hp N m hm).facetClass o' = s ∧
          ∃ g : PrimeSymmetry p,
            EquivariantPrismNonhorizontalCancellation.mapVertexSignature tau =
              fun i => g • (StackCells hp N m hm).facetSignature o' i := by
      refine ⟨o, hos, 1, ?_⟩
      simpa using htau
    unfold stackFacetOrbitIndicator
    rw [if_pos hex, if_pos hos]
  · have hnot : ¬ ∃ o' : (StackCells hp N m hm).FacetOccurrence,
        (StackCells hp N m hm).facetClass o' = s ∧
          ∃ g : PrimeSymmetry p,
            EquivariantPrismNonhorizontalCancellation.mapVertexSignature tau =
              fun i => g • (StackCells hp N m hm).facetSignature o' i := by
      rintro ⟨o', ho', g, hg⟩
      apply hos
      have hsig :
          (fun i => g • (StackCells hp N m hm).facetSignature o' i) =
            (StackCells hp N m hm).facetSignature o := by
        rw [← htau]
        exact hg.symm
      have hclass : (StackCells hp N m hm).facetClass o' =
          (StackCells hp N m hm).facetClass o :=
        Quotient.sound ⟨g, hsig⟩
      exact hclass.symm.trans ho'
    unfold stackFacetOrbitIndicator
    rw [if_neg hnot, if_neg hos]

/-- On an actual base occurrence embedded in slab `r`, the pulled-back weight is the Kronecker
weight of its stack quotient facet. -/
theorem slabFacetOrbitIndicator_occurrence
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet) (r : Fin m)
    (o : (BaseCells hp N).FacetOccurrence) :
    slabFacetOrbitIndicator hp N m hm s r (EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap hp N 0 o) =
      if (StackCells hp N m hm).facetClass
          (stackOccurrence hp N m hm r o) = s then 1 else 0 := by
  unfold slabFacetOrbitIndicator
  exact stackFacetOrbitIndicator_occurrence hp N m hm s
    (stackOccurrence hp N m hm r o)
    (slabFacetMap m hm r (EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap hp N 0 o))
    (mapVertexSignature_slabOccurrence hp N m hm r o)

/-- The signed incidence of a stack quotient facet is the sum of the ordinary staircase occurrence
pairings pulled back from each slab. -/
theorem facetIncidence_eq_sum_slabOccurrencePairing
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet) :
    (StackCells hp N m hm).facetIncidence s =
      ∑ r : Fin m,
        occurrencePairing hp N 0 (slabFacetOrbitIndicator hp N m hm s r) := by
  classical
  unfold RelativeAffineCellSystem.facetIncidence
    RelativeCollarMiddlePrismBoundary.occurrencePairing

  change
    (∑ x : (Fin m × (BaseCells hp N).Cell) × Fin (p + 1),
      if (StackCells hp N m hm).facetClass x = s then
        (StackCells hp N m hm).coefficient x.1 *
          RelativeAffineCellSystem.alternatingSign x.2
      else 0) = _
  conv_lhs =>
    rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  conv_rhs =>
    enter [2, r]
    rw [Fintype.sum_prod_type]

  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro k hk
  rw [slabFacetOrbitIndicator_occurrence]
  simp [stackOccurrence, RelativeCollarThinSlabs.cellSystem,
    RelativeCollarThinSlabs.Cell, occurrenceCoefficient,
    RelativeAffineCellSystem.alternatingSign,
    SimplicialChain.faceSign, RelativeCollarMiddlePrism.cellSystem]
  change
    (if (StackCells hp N m hm).facetClass ((r, q), k) = s then
        prismCoefficient hp N 0 q * (-1) ^ (k : Nat)
      else 0) =
      prismCoefficient hp N 0 q * (-1) ^ (k : Nat) *
        (if (StackCells hp N m hm).facetClass ((r, q), k) = s then 1 else 0)
  split_ifs <;> simp



/-! ## Mesh endpoint terms and telescoping -/

/-- The `k`-th time node of the uniform `m`-slab mesh. -/
noncomputable def meshTime
    (m : Nat) (hm : 0 < m) (k : Fin (m + 1)) : Set.Icc (0 : Real) 1 := by
  refine ⟨(k.1 : Real) / (m : Real), ?_, ?_⟩
  · positivity
  · have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hm
    apply (div_le_one hmR).2
    exact_mod_cast (Nat.le_of_lt_succ k.2)

@[simp] theorem meshTime_val
    (m : Nat) (hm : 0 < m) (k : Fin (m + 1)) :
    (meshTime m hm k).1 = (k.1 : Real) / (m : Real) :=
  rfl

/-- Place a spatial facet map on one node of the uniform time mesh. -/
noncomputable def meshEndpointMap
    (m : Nat) (hm : 0 < m) (k : Fin (m + 1))
    (sigma : Delta (p - 1) → Realization p) :
    Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1 :=
  fun x => (sigma x, meshTime m hm k)

/-- The lower face of slab `r` is mesh node `r`. -/
theorem slabFacetMap_lowerEndpointMap
    (m : Nat) (hm : 0 < m) (r : Fin m)
    (sigma : Delta (p - 1) → Realization p) :
    slabFacetMap m hm r (lowerEndpointMap sigma) =
      meshEndpointMap m hm r.castSucc sigma := by
  funext x
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [slabFacetMap, meshEndpointMap, meshTime, lowerEndpointMap]

/-- The upper face of slab `r` is mesh node `r+1`. -/
theorem slabFacetMap_upperEndpointMap
    (m : Nat) (hm : 0 < m) (r : Fin m)
    (sigma : Delta (p - 1) → Realization p) :
    slabFacetMap m hm r (upperEndpointMap sigma) =
      meshEndpointMap m hm r.succ sigma := by
  funext x
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [slabFacetMap, meshEndpointMap, meshTime, upperEndpointMap]

/-- Pair the spatial Fox--Neuwirth chain at level `N` with one stack quotient facet on a fixed mesh
node. -/
noncomputable def meshEndpointPairing
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet) (k : Fin (m + 1)) : ZMod p :=
  ∑ q : TopCell hp N,
    coefficient hp N q *
      stackFacetOrbitIndicator hp N m hm s
        (meshEndpointMap m hm k (RefinedAffineMap.chart hp N q))

/-- At refinement length zero, a slab's lower endpoint pairing is its lower mesh-node pairing. -/
theorem lowerEndpointPairing_slab_eq_mesh
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet) (r : Fin m) :
    lowerEndpointPairing hp N 0 (slabFacetOrbitIndicator hp N m hm s r) =
      meshEndpointPairing hp N m hm s r.castSucc := by
  classical
  unfold lowerEndpointPairing meshEndpointPairing slabFacetOrbitIndicator
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  have hsub : ∀ eta : Fin 0 → Equiv.Perm (Fin p),
      eta = RelativeCollarMiddlePrismEndpoints.emptyEndpointRefinementWord p :=
    fun eta => Subsingleton.elim _ _
  simp_rw [hsub]
  have htop :
      EndpointFaceRefinement.endpointTopCell hp N 0 q
          (RelativeCollarMiddlePrismEndpoints.emptyEndpointRefinementWord p) = q := by
    rcases q with ⟨c, rho⟩
    apply Prod.ext
    · rfl
    · funext i
      change Fin.addCases rho
        (RelativeCollarMiddlePrismEndpoints.emptyEndpointRefinementWord p)
          (Fin.castAdd 0 i) = rho i
      exact Fin.addCases_left i
  have hspatial :
      endpointSpatialMap hp N 0 q
          (RelativeCollarMiddlePrismEndpoints.emptyEndpointRefinementWord p) =
        RefinedAffineMap.chart hp N q := by
    rw [EndpointFaceRefinement.endpointSpatialMap_eq_chart, htop]
    rfl
  rw [hspatial]
  simp [
    RefinedAffineMap.subdivisionSign,
    slabFacetMap_lowerEndpointMap
  ]

/-- At refinement length zero, a slab's upper endpoint pairing is its upper mesh-node pairing. -/
theorem upperEndpointPairing_slab_eq_mesh
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet) (r : Fin m) :
    upperEndpointPairing hp N 0 (slabFacetOrbitIndicator hp N m hm s r) =
      meshEndpointPairing hp N m hm s r.succ := by
  classical
  unfold upperEndpointPairing meshEndpointPairing slabFacetOrbitIndicator
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  have hsub : ∀ eta : Fin 0 → Equiv.Perm (Fin p),
      eta = RelativeCollarMiddlePrismEndpoints.emptyEndpointRefinementWord p :=
    fun eta => Subsingleton.elim _ _
  simp_rw [hsub]
  have htop :
      EndpointFaceRefinement.endpointTopCell hp N 0 q
          (RelativeCollarMiddlePrismEndpoints.emptyEndpointRefinementWord p) = q := by
    rcases q with ⟨c, rho⟩
    apply Prod.ext
    · rfl
    · funext i
      change Fin.addCases rho
        (RelativeCollarMiddlePrismEndpoints.emptyEndpointRefinementWord p)
          (Fin.castAdd 0 i) = rho i
      exact Fin.addCases_left i
  have hspatial :
      endpointSpatialMap hp N 0 q
          (RelativeCollarMiddlePrismEndpoints.emptyEndpointRefinementWord p) =
        RefinedAffineMap.chart hp N q := by
    rw [EndpointFaceRefinement.endpointSpatialMap_eq_chart, htop]
    rfl
  rw [hspatial]
  simp [
    RefinedAffineMap.subdivisionSign,
    slabFacetMap_upperEndpointMap
  ]

/-- Finite telescoping identity in the indexing form used by a uniform slab stack. -/
theorem sum_fin_succ_sub
    {R : Type} [AddCommGroup R]
    (m : Nat) (a : Fin (m + 1) → R) :
    (∑ r : Fin m, (a r.succ - a (Fin.castSucc r))) =
      a (Fin.last m) - a 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (fun k : Fin (m + 1) => a k.succ)
      have htail' :
          (∑ i : Fin m, (a i.succ.succ - a i.succ.castSucc)) =
            a (Fin.last m).succ - a (Fin.succ 0) := by
        rw [← htail]
        apply Finset.sum_congr rfl
        intro i hi
        congr 2
      rw [htail']
      simp only [Fin.succ_zero_eq_one]
      have hlast : (Fin.last m).succ = Fin.last (m + 1) := by
        apply Fin.ext
        rfl
      have hzero : Fin.castSucc (0 : Fin (m + 1)) = (0 : Fin (m + 2)) := rfl
      rw [hlast, hzero]
      abel

/-- Pointwise boundary formula for the complete thin stack: all internal time nodes telescope. -/
theorem facetIncidence_eq_last_sub_first_mesh
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet) :
    (StackCells hp N m hm).facetIncidence s =
      meshEndpointPairing hp N m hm s (Fin.last m) -
        meshEndpointPairing hp N m hm s 0 := by
  rw [facetIncidence_eq_sum_slabOccurrencePairing hp N m hm s]
  simp_rw [occurrencePairing_eq_upper_sub_lower hp N 0
    (slabFacetOrbitIndicator hp N m hm s _)
    (slabFacetOrbitIndicator_translate hp N m hm s _)]
  simp_rw [upperEndpointPairing_slab_eq_mesh hp N m hm s,
    lowerEndpointPairing_slab_eq_mesh hp N m hm s]
  exact sum_fin_succ_sub m (meshEndpointPairing hp N m hm s)

/-- External lower boundary coefficient of a thin stack. -/
noncomputable def lowerBoundaryCoefficient
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet) : ZMod p :=
  meshEndpointPairing hp N m hm s 0

/-- External upper boundary coefficient of a thin stack. -/
noncomputable def upperBoundaryCoefficient
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet) : ZMod p :=
  meshEndpointPairing hp N m hm s (Fin.last m)

/-- A nonzero lower external coefficient forces the represented stack facet to lie at time zero. -/
theorem isLowerFacet_of_meshFirstIndicator_ne_zero
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet)
    (sigma : Delta (p - 1) → Realization p)
    (h : stackFacetOrbitIndicator hp N m hm s
        (meshEndpointMap m hm 0 sigma) ≠ 0) :
    (StackCells hp N m hm).IsLowerFacet s := by
  classical
  unfold stackFacetOrbitIndicator at h
  split_ifs at h with hex
  · rcases hex with ⟨o, ho, g, hg⟩
    rw [← ho]
    change (StackCells hp N m hm).IsLowerFacetOccurrence o
    intro i
    have hi := congrFun hg i
    have ht := congrArg
      (fun z : EquivariantPrismVertexParameters.CylinderPoint p => z.time.1) hi
    simpa [EquivariantPrismNonhorizontalCancellation.mapVertexSignature,
      meshEndpointMap, meshTime,
      EquivariantPrismVertexParameters.CylinderPoint.ofProd] using ht.symm
  · exact (h rfl).elim

/-- A nonzero upper external coefficient forces the represented stack facet to lie at time one. -/
theorem isUpperFacet_of_meshLastIndicator_ne_zero
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet)
    (sigma : Delta (p - 1) → Realization p)
    (h : stackFacetOrbitIndicator hp N m hm s
        (meshEndpointMap m hm (Fin.last m) sigma) ≠ 0) :
    (StackCells hp N m hm).IsUpperFacet s := by
  classical
  unfold stackFacetOrbitIndicator at h
  split_ifs at h with hex
  · rcases hex with ⟨o, ho, g, hg⟩
    rw [← ho]
    change (StackCells hp N m hm).IsUpperFacetOccurrence o
    intro i
    have hi := congrFun hg i
    have ht := congrArg
      (fun z : EquivariantPrismVertexParameters.CylinderPoint p => z.time.1) hi
    have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hm
    simpa [EquivariantPrismNonhorizontalCancellation.mapVertexSignature,
      meshEndpointMap, meshTime,
      EquivariantPrismVertexParameters.CylinderPoint.ofProd,
      Fin.last, div_self (ne_of_gt hmR)] using ht.symm
  · exact (h rfl).elim

/-- Lower coefficients vanish away from the external lower boundary. -/
theorem lowerBoundaryCoefficient_zero_of_not_lower
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet)
    (hs : ¬ (StackCells hp N m hm).IsLowerFacet s) :
    lowerBoundaryCoefficient hp N m hm s = 0 := by
  classical
  unfold lowerBoundaryCoefficient meshEndpointPairing
  apply Finset.sum_eq_zero
  intro q hq
  have hindicator : stackFacetOrbitIndicator hp N m hm s
      (meshEndpointMap m hm 0 (RefinedAffineMap.chart hp N q)) = 0 := by
    by_contra hne
    exact hs (isLowerFacet_of_meshFirstIndicator_ne_zero hp N m hm s _ hne)
  rw [hindicator, mul_zero]

/-- Upper coefficients vanish away from the external upper boundary. -/
theorem upperBoundaryCoefficient_zero_of_not_upper
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet)
    (hs : ¬ (StackCells hp N m hm).IsUpperFacet s) :
    upperBoundaryCoefficient hp N m hm s = 0 := by
  classical
  unfold upperBoundaryCoefficient meshEndpointPairing
  apply Finset.sum_eq_zero
  intro q hq
  have hindicator : stackFacetOrbitIndicator hp N m hm s
      (meshEndpointMap m hm (Fin.last m) (RefinedAffineMap.chart hp N q)) = 0 := by
    by_contra hne
    exact hs (isUpperFacet_of_meshLastIndicator_ne_zero hp N m hm s _ hne)
  rw [hindicator, mul_zero]

/-- The complete thin-time stack as a pointwise Fox--Neuwirth relative affine collar. -/
noncomputable def collar
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m) :
    FoxNeuwirthRelativeAffineCollar hp N N N m where
  cells := StackCells hp N m hm
  lowerBoundaryCoefficient := lowerBoundaryCoefficient hp N m hm
  upperBoundaryCoefficient := upperBoundaryCoefficient hp N m hm
  lower_zero_of_not_lower := lowerBoundaryCoefficient_zero_of_not_lower hp N m hm
  upper_zero_of_not_upper := upperBoundaryCoefficient_zero_of_not_upper hp N m hm
  incidence_eq_boundary := by
    intro s
    exact facetIncidence_eq_last_sub_first_mesh hp N m hm s


end RelativeCollarThinSlabsBoundary
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
