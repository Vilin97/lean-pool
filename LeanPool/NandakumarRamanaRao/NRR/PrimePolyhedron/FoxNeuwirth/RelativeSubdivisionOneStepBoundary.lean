/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeSubdivisionOneStepBoundaryBase
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeSubdivisionCylinderBoundary
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismNonhorizontalCancellation
/-!
# Pointwise boundary of the one-step relative subdivision cylinder

This module lifts the arbitrary-weight boundary theorem for the recursive standard-simplex
cylinder over every refined Fox--Neuwirth top cell.  A characteristic weight of one ordered
prime-orbit facet converts that weighted identity into the pointwise facet-incidence formula.

The only global term not already contained in the local cylinder theorem is the recursively
triangulated spatial-side chain.  It vanishes after summing over the refined Fox--Neuwirth orbit
cycle: iterated barycentric-subdivision boundary moves it to the original orbit-cycle boundary,
and prime invariance of the quotient-facet characteristic weight lets
`orbit_boundary_pairing_eq_zero` apply.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeSubdivisionOneStepBoundary

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open ExplicitAffineRelativeCollar
open EquivariantPrismVertexParameters
open RefinedAffineMap
open EquivariantPrismNonhorizontalCancellation


variable {p : Nat}

/-- Lift an ordered local-cylinder tuple through one refined Fox--Neuwirth chart. -/
noncomputable def liftTuple
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N)
    (v : Fin (p - 1 + 1) →
      Delta (p - 1) × Set.Icc (0 : Real) 1) :
    Fin p →
      EquivariantPrismVertexParameters.CylinderPoint p :=
  fun i =>
    RelativeSubdivisionOneStepCells.liftPoint hp N q
      (v (Fin.cast
        (Nat.sub_add_cancel hp.pos).symm i))

/-- Characteristic weight of one ordered prime-orbit facet, evaluated on an arbitrary geometric
vertex tuple.  The existential formulation makes it available to the local arbitrary-weight
boundary theorem without choosing a quotient representative. -/
noncomputable def facetOrbitIndicator
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet)
    (v : Fin p →
      EquivariantPrismVertexParameters.CylinderPoint p) :
    ZMod p := by
  classical
  exact if ∃ o :
      (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence,
      (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o = s ∧
        ∃ g : PrimeSymmetry p,
          v =
            fun i =>
              g •
                (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature o i
    then 1
    else 0

/-- Simultaneous prime translation does not change the quotient-facet characteristic weight. -/
theorem facetOrbitIndicator_smul
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet)
    (g : PrimeSymmetry p) (v : Fin p → CylinderPoint p) :
    facetOrbitIndicator hp N s (fun i => g • v i) =
      facetOrbitIndicator hp N s v := by
  classical
  unfold facetOrbitIndicator
  have hiff :
      (∃ o : (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence,
          (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o = s ∧
            ∃ h : PrimeSymmetry p,
              (fun i => g • v i) =
                fun i => h • (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature o i) ↔
      (∃ o : (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence,
          (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o = s ∧
            ∃ h : PrimeSymmetry p,
              v = fun i => h • (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature o i) := by
    constructor
    · rintro ⟨o, ho, h, hh⟩
      refine ⟨o, ho, g⁻¹ * h, ?_⟩
      funext i
      have hi := congrFun hh i
      have hgi := congrArg (fun z : CylinderPoint p => g⁻¹ • z) hi
      simpa [mul_smul] using hgi
    · rintro ⟨o, ho, h, hh⟩
      refine ⟨o, ho, g * h, ?_⟩
      funext i
      simp [hh, mul_smul]
  exact if_congr hiff rfl rfl

private def fullFacetIndexEquiv
    (hp : Nat.Prime p) :
    Fin (p + 1) ≃ Fin (p - 1 + 2) :=
  finCongr (by
    have := hp.pos
    omega)

/-- A local cylinder facet lifted through a refined top chart is exactly the corresponding global
facet occurrence signature. -/
theorem liftTuple_facetTuple
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N)
    (r : RelativeSubdivisionCylinderCombinatorics.Cell
      (p - 1))
    (j : Fin (p + 1)) :
    liftTuple hp N q
        (RelativeSubdivisionCylinderBoundary.facetTuple
          (p - 1) r (fullFacetIndexEquiv hp j)) =
      (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature ((q, r), j) := by
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ p =>
    funext i
    simp [
      liftTuple,
      RelativeSubdivisionCylinderBoundary.facetTuple,
      RelativeSubdivisionCylinderBoundary.deleteTuple,
      RelativeAffineCellSystem.facetSignature,
      RelativeSubdivisionOneStepCells.cellSystem,
      RelativeSubdivisionOneStepCells.vertex,
      RelativeSubdivisionOneStepCells.chart,
      RelativeSubdivisionOneStepCells.localPoint,
      RelativeSubdivisionOneStepCells.localWeight,
      RelativeSubdivisionCylinderCombinatorics.chart_vertex,
      fullFacetIndexEquiv
    ]


/-- On every actual global facet occurrence, the characteristic weight is the Kronecker delta of
its quotient-facet class. -/
theorem facetOrbitIndicator_occurrence
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet)
    (o : (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence) :
    facetOrbitIndicator hp N s ((RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature o) =
      if (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o = s then 1 else 0 := by
  classical
  by_cases hos : (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o = s
  · have hex : ∃ o' : (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence,
        (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o' = s ∧
          ∃ g : PrimeSymmetry p,
            (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature o =
              fun i => g • (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature o' i := by
      exact ⟨o, hos, 1, by funext i; simp⟩
    unfold facetOrbitIndicator
    rw [ite_eq_left hex, ite_eq_left hos]
  · have hnot : ¬ ∃ o' : (RelativeSubdivisionOneStepCells.cellSystem hp N).FacetOccurrence,
        (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o' = s ∧
          ∃ g : PrimeSymmetry p,
            (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature o =
              fun i => g • (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature o' i := by
      rintro ⟨o', ho', g, hg⟩
      apply hos
      have hclass : (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o =
          (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass o' :=
        Quotient.sound ⟨g⁻¹, by
          funext i
          have hi := congrFun hg i
          have hgi := congrArg (fun z : CylinderPoint p => g⁻¹ • z) hi
          simpa [mul_smul] using hgi⟩
      exact hclass.trans ho'
    unfold facetOrbitIndicator
    rw [ite_eq_right hnot, ite_eq_right hos]

/-- Local tuple weight induced by one global quotient-facet class. -/
noncomputable def localTupleWeight
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) (q : TopCell hp N)
    (v : Fin (p - 1 + 1) → Delta (p - 1) × Set.Icc (0 : Real) 1) : ZMod p :=
  facetOrbitIndicator hp N s (liftTuple hp N q v)

/-- The explicit global incidence is the sum of the local full-boundary pairings over refined
Fox--Neuwirth top cells. -/
theorem facetIncidence_eq_localFullBoundary
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).facetIncidence s =
      ∑ q : TopCell hp N,
        RefinedAffineMap.coefficient hp N q *
          NRR.FoxNeuwirthOrderComplex.RelativeSubdivisionCylinderBoundary.fullBoundaryPairing (ZMod p) (p - 1)
            (localTupleWeight hp N s q) := by
  classical
  unfold RelativeAffineCellSystem.facetIncidence
  change
    (∑ x : (TopCell hp N ×
        RelativeSubdivisionCylinderCombinatorics.Cell (p - 1)) × Fin (p + 1),
      if (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass x = s then
        (RelativeSubdivisionOneStepCells.cellSystem hp N).coefficient x.1 *
          RelativeAffineCellSystem.alternatingSign x.2
      else 0) = _
  conv_lhs =>
    rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q hq
  unfold RelativeSubdivisionCylinderBoundary.fullBoundaryPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  have hfaces :
      (∑ j : Fin (p - 1 + 2),
        SimplicialChain.faceSign j *
          localTupleWeight hp N s q
            (RelativeSubdivisionCylinderBoundary.facetTuple
              (p - 1) r j)) =
        ∑ j : Fin (p + 1),
          SimplicialChain.faceSign (fullFacetIndexEquiv hp j) *
            localTupleWeight hp N s q
              (RelativeSubdivisionCylinderBoundary.facetTuple
                (p - 1) r (fullFacetIndexEquiv hp j)) := by
    symm
    apply Fintype.sum_equiv (fullFacetIndexEquiv hp)
    intro j
    rfl
  rw [← Finset.mul_sum, ← mul_assoc, hfaces, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change _ = _ * _ * (_ * facetOrbitIndicator hp N s
    (liftTuple hp N q
      (RelativeSubdivisionCylinderBoundary.facetTuple
        (p - 1) r (fullFacetIndexEquiv hp j))))
  rw [liftTuple_facetTuple, facetOrbitIndicator_occurrence]
  have hsign :
      (SimplicialChain.faceSign
        (R := ZMod p) (fullFacetIndexEquiv hp j)) =
        ((-1 : ZMod p) ^ j.1) := by
    simp [SimplicialChain.faceSign, fullFacetIndexEquiv]
  rw [hsign]
  change (if _ then
      RelativeSubdivisionOneStepCells.coefficient hp N (q, r) *
        ((-1 : ZMod p) ^ j.1) else 0) = _
  simp [RelativeSubdivisionOneStepCells.coefficient]
  rfl

/-- After applying the local recursive-cylinder theorem, global incidence is the pairing with all
cone-base facets. -/
theorem facetIncidence_eq_localBase
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).facetIncidence s =
      ∑ q : TopCell hp N,
        RefinedAffineMap.coefficient hp N q *
          NRR.FoxNeuwirthOrderComplex.RelativeSubdivisionCylinderBoundary.basePairing (ZMod p) (p - 1)
            (localTupleWeight hp N s q) := by
  rw [facetIncidence_eq_localFullBoundary]
  apply Finset.sum_congr rfl
  intro q hq
  rw [NRR.FoxNeuwirthOrderComplex.RelativeSubdivisionCylinderBoundary.fullBoundaryPairing_eq_base]

/-- Quotient-facet Kronecker delta. -/
noncomputable def quotientIndicator {hp : Nat.Prime p}
    (s t : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) : ZMod p :=
  if t = s then 1 else 0

/-- The local cone-base sum is exactly the previously defined global cone-base pairing. -/
theorem localBase_eq_globalBase
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) :
    (∑ q : TopCell hp N,
      RefinedAffineMap.coefficient hp N q *
        NRR.FoxNeuwirthOrderComplex.RelativeSubdivisionCylinderBoundary.basePairing (ZMod p) (p - 1)
          (localTupleWeight hp N s q)) =
      RelativeSubdivisionOneStepBoundaryBase.basePairing hp N (quotientIndicator s) := by
  classical
  unfold NRR.FoxNeuwirthOrderComplex.RelativeSubdivisionCylinderBoundary.basePairing
    RelativeSubdivisionOneStepBoundaryBase.basePairing
  change _ =
    ∑ q : TopCell hp N ×
        RelativeSubdivisionCylinderCombinatorics.Cell (p - 1),
      RelativeSubdivisionOneStepCells.coefficient hp N q *
        quotientIndicator s
          ((RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass
            (RelativeSubdivisionOneStepBoundaryBase.baseOccurrence hp N q))
  conv_rhs =>
    rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have htuple :
      liftTuple hp N q (RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetVertex (p - 1) r) =
        (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature (RelativeSubdivisionOneStepBoundaryBase.baseOccurrence hp N (q, r)) := by
    rw [← NRR.FoxNeuwirthOrderComplex.RelativeSubdivisionCylinderBoundary.facetTuple_zero_eq_base]
    exact liftTuple_facetTuple hp N q r 0
  change _ * (_ * facetOrbitIndicator hp N s
    (liftTuple hp N q
      (RelativeSubdivisionCylinderCombinatorics.Oriented.baseFacetVertex (p - 1) r))) = _
  rw [htuple, facetOrbitIndicator_occurrence]
  simp [ quotientIndicator, RelativeSubdivisionOneStepBoundaryBase.baseOccurrence,
    RelativeSubdivisionOneStepCells.coefficient]
  exact (mul_assoc _ _ _).symm

/-- Pointwise incidence is the global cone-base pairing. -/
theorem facetIncidence_eq_basePairing
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).facetIncidence s =
      RelativeSubdivisionOneStepBoundaryBase.basePairing hp N (quotientIndicator s) := by
  rw [facetIncidence_eq_localBase, localBase_eq_globalBase]

/-! ## Cancellation of the recursive spatial-side chain -/

/-- Geometric tuple obtained by attaching the time coordinates of one lower-dimensional local
cylinder cell to an arbitrary spatial facet map. -/
noncomputable def sideCylinderTuple
    (hp : Nat.Prime p)
    (r : RelativeSubdivisionCylinderCombinatorics.Cell
      (p - 2))
    (tau : Delta (p - 2) → Realization p) :
    Fin p →
      EquivariantPrismVertexParameters.CylinderPoint p :=
  fun i =>
    let i' :
        Fin (p - 2 + 2) :=
      EquivariantPrismNonhorizontalCancellation.orbitFacetIndex hp i
    EquivariantPrismVertexParameters.CylinderPoint.ofProd
      (tau
          (RelativeSubdivisionCylinderCombinatorics.vertex
            (p - 2) r i').1,
        (RelativeSubdivisionCylinderCombinatorics.vertex
          (p - 2) r i').2)

/-- Quotient-facet weight induced on a spatial facet map by one recursive side-cylinder cell. -/
noncomputable def sideMapWeight
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) (r : RelativeSubdivisionCylinderCombinatorics.Cell (p - 2))
    (tau : Delta (p - 2) → Realization p) : ZMod p :=
  facetOrbitIndicator hp N s (sideCylinderTuple hp r tau)

/-- The side-map weight is invariant under prime relabelling. -/
theorem sideMapWeight_smul
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) (r : RelativeSubdivisionCylinderCombinatorics.Cell (p - 2))
    (g : PrimeSymmetry p) (tau : Delta (p - 2) → Realization p) :
    sideMapWeight hp N s r (fun x => g • tau x) =
      sideMapWeight hp N s r tau := by
  have htuple :
      sideCylinderTuple hp r (fun x => g • tau x) =
        fun i => g • sideCylinderTuple hp r tau i := by
    funext i
    rfl
  unfold sideMapWeight
  rw [htuple, facetOrbitIndicator_smul hp N s g]


private theorem sideDimension_eq (hp : Nat.Prime p) :
    p - 2 + 1 = p - 1 := by
  have h := hp.two_le
  omega

private def sideDomainCast (hp : Nat.Prime p) :
    Delta (p - 2 + 1) → Delta (p - 1) :=
  fun x => (sideDimension_eq hp) ▸ x

private def sideRefinementCast (hp : Nat.Prime p)
    (rho : Equiv.Perm (Fin p)) :
    Equiv.Perm (Fin (p - 2 + 2)) :=
  let e : Fin (p - 2 + 2) ≃ Fin p :=
    Equiv.cast (congrArg Fin (by
      have := hp.two_le
      omega))
  e.trans (rho.trans e.symm)

/-- The prime-orbit boundary pairing vanishes for each fixed refinement word. -/
private theorem fixed_side_refinement_cancels (d : ℕ) (hp : Nat.Prime (d + 2)) (N : ℕ)
  (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) (r : RelativeSubdivisionCylinderCombinatorics.Cell d)
  (theta : Fin N → Equiv.Perm (Fin (d + 1))) :
  ∑ x,
      ∑ x_1,
        (PrimeOrbitCycle.orbitCycle hp).coefficient x *
          (SimplicialChain.faceSign x_1 *
            (iteratedSign (ZMod (d + 2)) N theta *
              sideMapWeight hp N s r
                (iteratedBoundaryMap d N (⇑(ReferenceAffineOrbitCount.topRepr hp x).realizationContinuousMap) x_1
                  theta))) =
    0 := by
  classical
  let W : Simplex (d + 2) d → ZMod (d + 2) :=
    fun f => sideMapWeight hp N s r
      (fun x => f.realizationPoint
        (StandardSimplex.ofDelta (affineCompMap d N theta x)))
  have hW : ∀ (g : PrimeSymmetry (d + 2)) (f : Simplex (d + 2) d),
      W (g • f) = W f := by
    intro g f
    dsimp [W]
    have heq :
        (fun x => (g • f).realizationPoint
          (StandardSimplex.ofDelta (affineCompMap d N theta x))) =
          fun x => g • f.realizationPoint
            (StandardSimplex.ofDelta (affineCompMap d N theta x)) := by
      funext x
      exact realizationPoint_prime_smul_any (d + 2) g f _
    exact (congrArg (sideMapWeight hp N s r) heq).trans
      (sideMapWeight_smul hp N s r g _)
  have hz := EquivariantPrismNonhorizontalCancellation.orbit_boundary_pairing_eq_zero hp W hW
  have hmap (orbit : PrimeOrbitCycle.TopOrbit hp) (j : Fin (d + 2)) :
      sideMapWeight hp N s r
          (EquivariantPrismNonhorizontalCancellation.iteratedBoundaryMap d N
            (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
            j theta) =
        W ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
          (FaceMap.delete j)) := by
    congr 1
    funext x
    apply Realization.ext
    intro c
    simp [ EquivariantPrismNonhorizontalCancellation.iteratedBoundaryMap,
      ReferenceAffineOrbitCount.topRepr,
      Simplex.realizationContinuousMap, Simplex.realizationPoint,
      Simplex.chartWeight, cofacePoint]
    change (∑ i : Fin (d + 2),
      if (ReferenceAffineOrbitCount.topRepr hp orbit) i = c then
        (StandardSimplex.ofDelta
          (SphereOddDegree.FiniteSimplex.map j.succAbove (affineCompMap d N theta x))) i else 0) = _
    have hs := Fin.sum_univ_succAbove (fun i : Fin (d + 2) =>
      if (ReferenceAffineOrbitCount.topRepr hp orbit) i = c then
        (StandardSimplex.ofDelta
          (SphereOddDegree.FiniteSimplex.map j.succAbove (affineCompMap d N theta x))) i else 0) j
    rw [hs]
    have hdeleted :
        (StandardSimplex.ofDelta
          (SphereOddDegree.FiniteSimplex.map j.succAbove (affineCompMap d N theta x))) j = 0 := by
      change (cofacePoint d j (affineCompMap d N theta x)) j = 0
      exact cofacePoint_apply_deleted d j (affineCompMap d N theta x)
    simp only [hdeleted, ite_self, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    change (if (ReferenceAffineOrbitCount.topRepr hp orbit) (j.succAbove i) = c
      then _ else 0) = if (ReferenceAffineOrbitCount.topRepr hp orbit)
        (j.succAbove i) = c then _ else 0
    by_cases hic : (ReferenceAffineOrbitCount.topRepr hp orbit) (j.succAbove i) = c
    · rw [ite_eq_left hic, ite_eq_left hic]
      change SphereOddDegree.FiniteSimplex.map (S := Real) j.succAbove
        (affineCompMap d N theta x) (j.succAbove i) =
          affineCompMap d N theta x i
      rw [SphereOddDegree.FiniteSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
      exact Finset.sum_eq_single i (by
        intro q hq hqi
        have hsucc : j.succAbove q ≠ j.succAbove i := by
          intro heq
          exact hqi (Fin.succAbove_right_injective heq)
        have hq' : j.succAbove q = j.succAbove i := by simpa using hq
        exact (hsucc hq').elim) (by simp)
    · rw [ite_eq_right hic, ite_eq_right hic]
  simp_rw [hmap]
  calc
    _ =
        (EquivariantPrismNonhorizontalCancellation.iteratedSign
            (ZMod (d + 2)) N theta) *
          (∑ orbit,
            (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
              ∑ k : Fin (d + 2),
                SimplicialChain.faceSign
                    (orbitFacetIndex hp k) *
                  W
                    ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                      (FaceMap.delete
                        (orbitFacetIndex hp k)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro orbit horbit
      rw [Finset.mul_sum]

      have hreindex :
          (∑ j : Fin (d + 2),
            (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
              (SimplicialChain.faceSign j *
                (EquivariantPrismNonhorizontalCancellation.iteratedSign
                    (ZMod (d + 2)) N theta *
                  W
                    ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                      (FaceMap.delete j))))) =
            ∑ k : Fin (d + 2),
              (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
                (SimplicialChain.faceSign
                    (orbitFacetIndex hp k) *
                  (EquivariantPrismNonhorizontalCancellation.iteratedSign
                      (ZMod (d + 2)) N theta *
                    W
                      ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                        (FaceMap.delete
                          (orbitFacetIndex hp k))))) := by
        exact
          (Equiv.sum_comp
            (orbitFacetEquiv hp)
            (fun j =>
              (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
                (SimplicialChain.faceSign j *
                  (EquivariantPrismNonhorizontalCancellation.iteratedSign
                      (ZMod (d + 2)) N theta *
                    W
                      ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                        (FaceMap.delete j)))))).symm

      calc
        _ =
            ∑ j : Fin (d + 2),
              (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
                (SimplicialChain.faceSign j *
                  (EquivariantPrismNonhorizontalCancellation.iteratedSign
                      (ZMod (d + 2)) N theta *
                    W
                      ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                        (FaceMap.delete j)))) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring

        _ = _ := hreindex

        _ =
            (EquivariantPrismNonhorizontalCancellation.iteratedSign
                (ZMod (d + 2)) N theta) *
              ((PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
                ∑ k : Fin (d + 2),
                  SimplicialChain.faceSign
                      (orbitFacetIndex hp k) *
                    W
                      ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                        (FaceMap.delete
                          (orbitFacetIndex hp k)))) := by
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring

        _ = _ := by
          congr 1
          rw [Finset.mul_sum]

    _ = 0 := by
      simpa only [hz, mul_zero]

/-- Dimension-normalized form of fixed-side cancellation. -/
private theorem fixedSideCell_sum_eq_zero_dim
    (d : Nat) (hp : Nat.Prime (d + 2)) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet)
    (r : RelativeSubdivisionCylinderCombinatorics.Cell d) :
    (∑ c : PrimeOrbitCycle.TopOrbit hp,
      (PrimeOrbitCycle.orbitCycle hp).coefficient c *
        ∑ rho : RefinementWord (d + 2) N,
          RefinedAffineMap.subdivisionSign N rho *
            ∑ k : Fin (d + 2),
              SimplicialChain.faceSign
                  (EquivariantPrismNonhorizontalCancellation.orbitFacetIndex hp k) *
                sideMapWeight hp N s r
                  (EquivariantPrismNonhorizontalCancellation.iteratedFacetMap d N
                    (ReferenceAffineOrbitCount.topRepr hp c).realizationContinuousMap rho
                    (EquivariantPrismNonhorizontalCancellation.orbitFacetIndex hp k))) = 0 := by
  classical
  simp only [
    RefinedAffineMap.subdivisionSign
  ]
  have hreindex (c : PrimeOrbitCycle.TopOrbit hp) :
      (∑ rho : RefinementWord (d + 2) N,
        RefinedAffineMap.subdivisionSign N rho *
          ∑ k : Fin (d + 2),
            SimplicialChain.faceSign
                (EquivariantPrismNonhorizontalCancellation.orbitFacetIndex hp k) *
              sideMapWeight hp N s r
                (EquivariantPrismNonhorizontalCancellation.iteratedFacetMap d N
                  (ReferenceAffineOrbitCount.topRepr hp c).realizationContinuousMap rho
                  (EquivariantPrismNonhorizontalCancellation.orbitFacetIndex hp k))) =
        ∑ rho : RefinementWord (d + 2) N,
          RefinedAffineMap.subdivisionSign N rho *
            ∑ j : Fin (d + 2), SimplicialChain.faceSign j *
              sideMapWeight hp N s r
                (EquivariantPrismNonhorizontalCancellation.iteratedFacetMap d N
                  (ReferenceAffineOrbitCount.topRepr hp c).realizationContinuousMap rho j) := by
    apply Finset.sum_congr rfl
    intro rho hrho
    exact congrArg (fun z => RefinedAffineMap.subdivisionSign N rho * z)
      ((Equiv.sum_comp
        (EquivariantPrismNonhorizontalCancellation.orbitFacetEquiv hp)
        (fun j => SimplicialChain.faceSign j *
          sideMapWeight hp N s r
            (EquivariantPrismNonhorizontalCancellation.iteratedFacetMap d N
              (ReferenceAffineOrbitCount.topRepr hp c).realizationContinuousMap rho j))).symm)
  change (∑ c : PrimeOrbitCycle.TopOrbit hp,
      (PrimeOrbitCycle.orbitCycle hp).coefficient c *
        ∑ rho : RefinementWord (d + 2) N,
          RefinedAffineMap.subdivisionSign N rho *
            ∑ k : Fin (d + 2),
              SimplicialChain.faceSign
                  (EquivariantPrismNonhorizontalCancellation.orbitFacetIndex hp k) *
                sideMapWeight hp N s r
                  (EquivariantPrismNonhorizontalCancellation.iteratedFacetMap d N
                    (ReferenceAffineOrbitCount.topRepr hp c).realizationContinuousMap rho
                    (EquivariantPrismNonhorizontalCancellation.orbitFacetIndex hp k))) = 0
  rw [show (∑ c : PrimeOrbitCycle.TopOrbit hp,
      (PrimeOrbitCycle.orbitCycle hp).coefficient c *
        ∑ rho : RefinementWord (d + 2) N,
          RefinedAffineMap.subdivisionSign N rho *
            ∑ k : Fin (d + 2),
              SimplicialChain.faceSign
                  (EquivariantPrismNonhorizontalCancellation.orbitFacetIndex hp k) *
                sideMapWeight hp N s r
                  (EquivariantPrismNonhorizontalCancellation.iteratedFacetMap d N
                    (ReferenceAffineOrbitCount.topRepr hp c).realizationContinuousMap rho
                    (EquivariantPrismNonhorizontalCancellation.orbitFacetIndex hp k))) = _ by
    apply Finset.sum_congr rfl
    intro c hc
    rw [hreindex c]]
  rw [show (∑ c : PrimeOrbitCycle.TopOrbit hp,
      (PrimeOrbitCycle.orbitCycle hp).coefficient c *
        ∑ rho : RefinementWord (d + 2) N,
          RefinedAffineMap.subdivisionSign N rho *
            ∑ j : Fin (d + 2), SimplicialChain.faceSign j *
              sideMapWeight hp N s r
                (EquivariantPrismNonhorizontalCancellation.iteratedFacetMap d N
                  (ReferenceAffineOrbitCount.topRepr hp c).realizationContinuousMap rho j)) =
      ∑ c : PrimeOrbitCycle.TopOrbit hp,
        (PrimeOrbitCycle.orbitCycle hp).coefficient c *
          ∑ j : Fin (d + 2), SimplicialChain.faceSign j *
            ∑ eta : Fin N → Equiv.Perm (Fin (d + 1)),
              EquivariantPrismNonhorizontalCancellation.iteratedSign (ZMod (d + 2)) N eta *
                sideMapWeight hp N s r
                  (EquivariantPrismNonhorizontalCancellation.iteratedBoundaryMap d N
                    (ReferenceAffineOrbitCount.topRepr hp c).realizationContinuousMap j eta) by
    apply Finset.sum_congr rfl
    intro c hc
    congr 1
    exact EquivariantPrismNonhorizontalCancellation.iterated_weighted_boundary
      (R := ZMod (d + 2)) d N
      (ReferenceAffineOrbitCount.topRepr hp c).realizationContinuousMap
      (sideMapWeight hp N s r)]
  simp_rw [Finset.mul_sum]
  conv_lhs =>
    enter [2, c]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro theta htheta
  exact fixed_side_refinement_cancels d hp N s r theta

/-- For one fixed recursive side cell, the signed side contribution of the refined orbit cycle
vanishes. -/
theorem fixedSideCell_sum_eq_zero
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet)
    (r : RelativeSubdivisionCylinderCombinatorics.Cell (p - 2)) :
    (∑ c : PrimeOrbitCycle.TopOrbit hp,
      (PrimeOrbitCycle.orbitCycle hp).coefficient c *
        ∑ rho : RefinementWord p N,
          RefinedAffineMap.subdivisionSign N rho *
            ∑ k : Fin p,
              SimplicialChain.faceSign
                  (EquivariantPrismNonhorizontalCancellation.orbitFacetIndex hp k) *
                sideMapWeight hp N s r
                  (EquivariantPrismNonhorizontalCancellation.iteratedFacetMap (p - 2) N
                    (fun x =>
                      (ReferenceAffineOrbitCount.topRepr hp c).realizationContinuousMap
                        (sideDomainCast hp x))
                    (fun i => sideRefinementCast hp (rho i))
                    (EquivariantPrismNonhorizontalCancellation.orbitFacetIndex hp k))) = 0 := by
  obtain ⟨d, hd⟩ : ∃ d, p = d + 2 :=
    ⟨p - 2, (Nat.sub_add_cancel hp.two_le).symm⟩
  subst p
  convert fixedSideCell_sum_eq_zero_dim d hp N s r using 1
  apply Finset.sum_congr rfl
  intro c hc
  congr 1

private theorem sideMapWeight_baseOccurrence_sideCell
    (d N : Nat) (hp : Nat.Prime (d + 2))
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet)
    (orbit : PrimeOrbitCycle.TopOrbit hp)
    (rho : RefinementWord (d + 2) N)
    (j : Fin (d + 2))
    (r : RelativeSubdivisionCylinderCombinatorics.Cell d) :
    sideMapWeight hp N s r
        (iteratedFacetMap d N
          (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap rho j) =
      quotientIndicator s
        ((RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass
          (RelativeSubdivisionOneStepBoundaryBase.baseOccurrence hp N
            ((orbit, rho),
              RelativeSubdivisionCylinderCombinatorics.sideCell d j r))) := by
  have htuple :
      sideCylinderTuple hp r
          (iteratedFacetMap d N
            (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap rho j) =
        (RelativeSubdivisionOneStepCells.cellSystem hp N).facetSignature
          (RelativeSubdivisionOneStepBoundaryBase.baseOccurrence hp N
            ((orbit, rho), RelativeSubdivisionCylinderCombinatorics.sideCell d j r)) := by
    funext i
    simp [sideCylinderTuple, iteratedFacetMap,
      RelativeSubdivisionOneStepBoundaryBase.baseOccurrence,
      RelativeAffineCellSystem.facetSignature,
      RelativeSubdivisionOneStepCells.cellSystem,
      RelativeSubdivisionCylinderCombinatorics.sidePoint,
      RelativeSubdivisionOneStepCells.liftPoint,
      RelativeSubdivisionOneStepCells.localPoint,
      RelativeSubdivisionOneStepCells.localWeight,
      RelativeSubdivisionOneStepCells.chart,
      RelativeSubdivisionOneStepCells.vertex,
      RelativeSubdivisionCylinderCombinatorics.chart_vertex,
      RefinedAffineMap.chart, Simplex.refinedContinuousMap,
      Simplex.realizationContinuousMap]
    congr 2 <;> simp [orbitFacetIndex, orbitFacetEquiv]
  unfold sideMapWeight quotientIndicator
  rw [htuple, facetOrbitIndicator_occurrence]
private theorem fixedSideCell_weighted_sum_eq_zero_dim
    (d : Nat) (hp : Nat.Prime (d + 2)) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet)
    (r : RelativeSubdivisionCylinderCombinatorics.Cell d) :
      (∑ c : PrimeOrbitCycle.TopOrbit hp,
        (PrimeOrbitCycle.orbitCycle hp).coefficient c *
          ∑ rho : RefinementWord (d + 2) N,
            RefinedAffineMap.subdivisionSign N rho *
              ∑ j : Fin (d + 2),
                SimplicialChain.faceSign j *
                  sideMapWeight hp N s r
                    (iteratedFacetMap d N
                      (ReferenceAffineOrbitCount.topRepr hp c).realizationContinuousMap rho j)) = 0 := by
  classical
  have hz := fixedSideCell_sum_eq_zero_dim d hp N s r
  rw [← hz]
  apply Finset.sum_congr rfl
  intro c hc
  congr 1

open scoped Classical in
private theorem sidePairing_summand_zero (d : ℕ) (hp : Nat.Prime (d + 2)) (N : ℕ)
  (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet)
  (hbridge :
    ∀ (orbit : PrimeOrbitCycle.TopOrbit hp) (rho : RefinementWord (d + 2) N) (j : Fin (d + 2))
      (r : RelativeSubdivisionCylinderCombinatorics.Cell d),
      sideMapWeight hp N s r
          (iteratedFacetMap d N (⇑(ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap) rho j) =
        if
            (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass
                (((orbit, rho), RelativeSubdivisionCylinderCombinatorics.sideCell d j r), 0) =
              s then
          1
        else 0)
  (r : RelativeSubdivisionCylinderCombinatorics.Cell d) :
  (∑ x : PrimeOrbitCycle.TopOrbit hp,
      ∑ x_1 : RefinementWord (d + 2) N,
        ∑ x_2 : Fin (d + 2),
          coefficient hp N (x, x_1) *
              ((-1) ^ (x_2 : ℕ) *
                RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient (ZMod (d + 2)) d (x_2, r).2) *
            if
                (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass
                    (((x, x_1), Sum.inr (Sum.inr (x_2, r))), 0) =
                  s then
              1
            else 0) =
    0 := by
  classical
  have hz' := fixedSideCell_weighted_sum_eq_zero_dim d hp N s r
  have hz'' := congrArg
    (fun z => RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient
      (ZMod (d + 2)) d r * z) hz'
  rw [mul_zero] at hz''
  refine Eq.trans ?_ hz''
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro orbit horbit
  apply Finset.sum_congr rfl
  intro rho hrho
  apply Finset.sum_congr rfl
  intro j hj
  rw [hbridge]
  simp only [RefinedAffineMap.coefficient, SimplicialChain.faceSign,
    RelativeSubdivisionCylinderCombinatorics.sideCell]
  ring
  rfl

private theorem sideBasePairing_eq_zero_dim
    (d : Nat) (hp : Nat.Prime (d + 2)) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) :
    RelativeSubdivisionOneStepBoundaryBase.sideBasePairing hp N (quotientIndicator s) = 0 := by
  classical
  unfold RelativeSubdivisionOneStepBoundaryBase.sideBasePairing RelativeSubdivisionOneStepBoundaryBase.IsEndpointCell
  rw [Fintype.sum_prod_type]
  simp [RelativeSubdivisionCylinderCombinatorics.Cell,
    RelativeSubdivisionCylinderCombinatorics.lowerCell,
    RelativeSubdivisionCylinderCombinatorics.upperCell,
    RelativeSubdivisionOneStepCells.coefficient,
    RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient,
    RelativeSubdivisionOneStepBoundaryBase.baseOccurrence, quotientIndicator]
  rw [Fintype.sum_prod_type]
  conv_lhs =>
    enter [2, orbit]
    enter [2, rho]
    rw [Fintype.sum_prod_type]
  have hbridge (orbit : PrimeOrbitCycle.TopOrbit hp)
      (rho : RefinementWord (d + 2) N) (j : Fin (d + 2))
      (r : RelativeSubdivisionCylinderCombinatorics.Cell d) :
      sideMapWeight hp N s r
          (iteratedFacetMap d N
            (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap rho j) =
        (if (RelativeSubdivisionOneStepCells.cellSystem hp N).facetClass
            (((orbit, rho), RelativeSubdivisionCylinderCombinatorics.sideCell d j r), 0) = s
          then 1 else 0) := by
    exact sideMapWeight_baseOccurrence_sideCell d N hp s orbit rho j r
  conv_lhs =>
    enter [2, orbit]
    enter [2, rho]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, orbit]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r hr
  exact sidePairing_summand_zero d hp N s hbridge r

/-- The complete recursive spatial-side part of the one-step cone-base chain vanishes. -/
theorem sideBasePairing_eq_zero
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) :
    RelativeSubdivisionOneStepBoundaryBase.sideBasePairing hp N (quotientIndicator s) = 0 := by
  obtain ⟨d, hd⟩ : ∃ d, p = d + 2 :=
    ⟨p - 2, (Nat.sub_add_cancel hp.two_le).symm⟩
  subst p
  exact sideBasePairing_eq_zero_dim d hp N s

/-! ## Pointwise collar boundary -/

/-- Lower boundary coefficient of one quotient facet. -/
noncomputable def lowerBoundaryCoefficient
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) : ZMod p :=
  RelativeSubdivisionOneStepBoundaryBase.lowerEndpointPairing hp N (quotientIndicator s)

/-- Upper boundary coefficient of one quotient facet. -/
noncomputable def upperBoundaryCoefficient
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) : ZMod p :=
  RelativeSubdivisionOneStepBoundaryBase.upperEndpointPairing hp N (quotientIndicator s)

/-- Exact pointwise boundary formula for the one-step relative subdivision cylinder. -/
theorem incidence_eq_boundary
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet) :
    (RelativeSubdivisionOneStepCells.cellSystem hp N).facetIncidence s =
      upperBoundaryCoefficient hp N s - lowerBoundaryCoefficient hp N s := by
  rw [facetIncidence_eq_basePairing,
    RelativeSubdivisionOneStepBoundaryBase.basePairing_eq_upper_sub_lower_add_side,
    sideBasePairing_eq_zero]
  simp [upperBoundaryCoefficient, lowerBoundaryCoefficient]

end RelativeSubdivisionOneStepBoundary
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
