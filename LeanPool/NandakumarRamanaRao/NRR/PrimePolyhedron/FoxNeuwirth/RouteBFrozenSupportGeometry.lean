/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EndpointStackIteratedAffinePullback
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBSmallGenericPerturbation
/-!
# Frozen positive-support safety for endpoint stacks and composed collars

The Route B frozen-support condition is proved one-sidedly.  A lower endpoint stack is safe when
all positive barycentric support lies at time zero; reversal gives the corresponding upper safety.
Collar composition then converts those two one-sided statements into the global frozen-parameter
condition because the two half-cylinder embeddings have no other horizontal points.
-/

@[expose] public section

namespace NRR

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RouteBFrozenSupportGeometry

open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open ExplicitAffineRelativeCollarCompose
open ExplicitAffineRelativeCollarAssignmentCompose
open ExplicitAffineRelativeCollarReverse
open ExplicitAffineRelativeCollarAssignmentReverse
open ExplicitAffineRelativeCollar.RouteB
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open CompatibleRefinedChartHomotopy
open CompatibleChartMapOneStep
open EndpointStackIteratedAffinePullback


variable {p N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)

/-- Lower one-sided version of frozen positive-support safety. -/
def LowerPositiveSupportRaySafe
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C) : Prop :=
  ∀ (q : C.Cell) (w : StandardSimplex p)
      (i j : Fin (p + 1)), i ≠ j →
    (∀ r : Fin (p - 1),
      deviation hp (affineValue (localVertexMap hp C a q) w) r = 0) →
    0 < mean p (affineValue (localVertexMap hp C a q) w) →
    (∀ k : Fin (p + 1), 0 < w k → (C.vertex q k).time.1 = 0) →
    ¬ (w i = 0 ∧ w j = 0)

/-- Upper one-sided version of frozen positive-support safety. -/
def UpperPositiveSupportRaySafe
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C) : Prop :=
  ∀ (q : C.Cell) (w : StandardSimplex p)
      (i j : Fin (p + 1)), i ≠ j →
    (∀ r : Fin (p - 1),
      deviation hp (affineValue (localVertexMap hp C a q) w) r = 0) →
    0 < mean p (affineValue (localVertexMap hp C a q) w) →
    (∀ k : Fin (p + 1), 0 < w k → (C.vertex q k).time.1 = 1) →
    ¬ (w i = 0 ∧ w j = 0)

/-- Every simplex weight has a positive coordinate. -/
theorem exists_positive_coordinate (w : StandardSimplex p) :
    ∃ k : Fin (p + 1), 0 < w k := by
  by_contra h
  push Not at h
  have hz : ∀ k : Fin (p + 1), w k = 0 := by
    intro k
    exact le_antisymm (h k) (w.nonneg k)
  have hone := w.sum_eq_one
  simp [hz] at hone

/-- In one local subdivision cylinder, positive support at time zero together with two vanishing
source coordinates maps to a proper face of the coarse lower simplex. -/
theorem lowerSpatialWeight_not_interior
    (d : Nat) (q : RelativeSubdivisionCylinderCombinatorics.Cell d)
    (w : Delta (d + 1))
    (i j : Fin (d + 2)) (hij : i ≠ j)
    (hzeros : w i = 0 ∧ w j = 0)
    (hsupport : ∀ k : Fin (d + 2), 0 < w k →
      (RelativeSubdivisionCylinderCombinatorics.vertex d q k).2.1 = 0) :
    ¬ StandardSimplex.IsInterior
      (StandardSimplex.ofDelta (RelativeSubdivisionCylinderCombinatorics.spatialPoint d q w)) := by
  classical
  let active : Finset (Fin (d + 2)) := Finset.univ.filter (fun k => 0 < w k)
  have hi_not : i ∉ active := by simp [active, hzeros.1]
  have hj_not : j ∉ active := by simp [active, hzeros.2]
  have hsubset : active ⊆ (Finset.univ.erase i).erase j := by
    intro k hk
    have hkpos : 0 < w k := (Finset.mem_filter.mp hk).2
    have hki : k ≠ i := by
      intro h
      subst k
      linarith
    have hkj : k ≠ j := by
      intro h
      subst k
      linarith
    simp [hki, hkj]
  have hcard : active.card ≤ d := by
    have hle := Finset.card_le_card hsubset
    have hjmem : j ∈ (Finset.univ.erase i : Finset (Fin (d + 2))) := by
      simp [hij.symm]
    simpa [Finset.card_erase_of_mem, hjmem] using hle
  let lowerIndex : {k // k ∈ active} → Fin (d + 1) := fun k =>
    Classical.choose
      (RelativeSubdivisionCylinderCombinatorics.vertex_eq_lowerBoundaryVertex_of_time_eq_zero
      d q k.1 (hsupport k.1 ((Finset.mem_filter.mp k.2).2)))
  have lowerIndex_spec : ∀ k : {k // k ∈ active},
      RelativeSubdivisionCylinderCombinatorics.vertex d q k.1 =
        RelativeSubdivisionCylinderCombinatorics.lowerBoundaryVertex d (lowerIndex k) := by
    intro k
    exact Classical.choose_spec
      (RelativeSubdivisionCylinderCombinatorics.vertex_eq_lowerBoundaryVertex_of_time_eq_zero
        d q k.1 (hsupport k.1 ((Finset.mem_filter.mp k.2).2)))
  have hinj : Function.Injective lowerIndex := by
    intro a b hab
    apply Subtype.ext
    apply RelativeSubdivisionCylinderCombinatorics.vertex_injective_all d q
    rw [lowerIndex_spec a, lowerIndex_spec b, hab]
  let image : Finset (Fin (d + 1)) := Finset.univ.image lowerIndex
  have himage_card : image.card ≤ d := by
    calc
      image.card ≤ Fintype.card {k // k ∈ active} := Finset.card_image_le
      _ = active.card := Fintype.card_coe active
      _ ≤ d := hcard
  have hmissing : ∃ c : Fin (d + 1), c ∉ image := by
    by_contra h
    push Not at h
    have hall : (Finset.univ : Finset (Fin (d + 1))) ⊆ image := by
      intro c hc
      exact h c
    have hc := Finset.card_le_card hall
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨c, hc⟩ := hmissing
  intro hinterior
  have hcoord : RelativeSubdivisionCylinderCombinatorics.spatialPoint d q w c = 0 := by
    change (∑ k : Fin (d + 2), w k *
      (RelativeSubdivisionCylinderCombinatorics.vertex d q k).1 c) = 0
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hkw : 0 < w k
    · have hka : k ∈ active := by simp [active, hkw]
      let ks : {k // k ∈ active} := ⟨k, hka⟩
      have hne : lowerIndex ks ≠ c := by
        intro heq
        apply hc
        exact Finset.mem_image.mpr ⟨ks, Finset.mem_univ _, heq⟩
      rw [lowerIndex_spec ks]
      simp [RelativeSubdivisionCylinderCombinatorics.lowerBoundaryVertex,
        SphereOddDegree.FiniteSimplex.vertex, hne]
    · have hw0 : w k = 0 := le_antisymm (le_of_not_gt hkw)
        (SphereOddDegree.FiniteSimplex.zero_le w k)
      simp [hw0]
  have hcpos : 0 < RelativeSubdivisionCylinderCombinatorics.spatialPoint d q w c :=
    hinterior c
  rw [hcoord] at hcpos
  exact lt_irrefl 0 hcpos

/-- The first affine-pullback endpoint layer is lower-support safe. -/
theorem oneStep_lowerPositiveSupportRaySafe
    {F : ContinuousCoordinateMap p}
    (A : StableRegularApproximation hp F) :
    LowerPositiveSupportRaySafe hp (RelativeSubdivisionOneStepCells.cellSystem hp
      A.toRegularApproximation.level)
      (CompatibleChartMapOneStep.assignment hp
        (baseOriginalPLMap hp A.toRegularApproximation)) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  intro q w i j hij hdev hmean hsupport hzeros
  let u : StandardSimplex m := StandardSimplex.ofDelta
    (RelativeSubdivisionOneStepCells.localPoint hp q.2 (StandardSimplex.toDelta w)).1
  have huBoundary : ¬ StandardSimplex.IsInterior u := by
    apply lowerSpatialWeight_not_interior m q.2
      (RelativeSubdivisionOneStepCells.localWeight hp (StandardSimplex.toDelta w)) i j
    · exact hij
    · change (w : Fin (m + 1 + 1) → Real) i = 0 ∧
          (w : Fin (m + 1 + 1) → Real) j = 0
      exact hzeros
    · intro k hk
      have htime := hsupport k (by
        change 0 < (StandardSimplex.toDelta w) k
        exact hk)
      simpa [RelativeSubdivisionOneStepCells.cellSystem,
        RelativeSubdivisionOneStepCells.vertex, RelativeSubdivisionOneStepCells.chart,
        RelativeSubdivisionOneStepCells.liftPoint,
        RelativeSubdivisionOneStepCells.localPoint,
        CompatibleChartMapOneStep.localWeight_succ,
        EquivariantPrismVertexParameters.CylinderPoint.ofProd] using htime
  have hvalue := CompatibleChartMapOneStep.affineValue_localVertexMap_assignment
    hp (baseOriginalPLMap hp A.toRegularApproximation)
      (baseOriginalPLMap_isAffine hp A.toRegularApproximation) q w
  apply huBoundary
  apply A.positiveRaySkeletonFree q.1 u
  · intro r
    have hz := hdev r
    rw [hvalue] at hz
    simpa [baseOriginalPLMap, RefinedAffineMap.value,
      AffinePositiveRayBoundary.VertexMap.deviation, sub_eq_zero, u] using hz
  · have hm := hmean
    rw [hvalue] at hm
    simpa [baseOriginalPLMap, RefinedAffineMap.value,
      AffinePositiveRayBoundary.VertexMap.mean, u] using hm

/-- Lower safety is inherited by a composition from its left component. -/
theorem lowerSafe_combined_left
    {Nmid M₀ L₀ M₁ L₁ : Nat}
    (C : RelativeAffineCellSystem hp N₀ Nmid M₀ L₀)
    (D : RelativeAffineCellSystem hp Nmid N₁ M₁ L₁)
    (a : Assignment hp C) (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b))
    (hC : LowerPositiveSupportRaySafe hp C a) :
    LowerPositiveSupportRaySafe hp (combinedCells C D)
      (combinedAssignment C D a b hseam) := by
  intro q w i j hij hdev hmean hsupport hzeros
  cases q with
  | inl q =>
      apply hC q w i j hij
      · simpa [localVertexMap_combinedAssignment_left] using hdev
      · simpa [localVertexMap_combinedAssignment_left] using hmean
      · intro k hk
        have h := hsupport k hk
        change (C.vertex q k).time.1 / 2 = 0 at h
        linarith
      · exact hzeros
  | inr q =>
      obtain ⟨k, hk⟩ := exists_positive_coordinate w
      have h := hsupport k hk
      have hnonneg := (D.vertex q k).time.2.1
      change (1 + (D.vertex q k).time.1) / 2 = 0 at h
      exfalso
      linarith

/-- Reversal converts lower-support safety into upper-support safety. -/
theorem upperSafe_reverse
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C)
    (hC : LowerPositiveSupportRaySafe hp C a) :
    UpperPositiveSupportRaySafe hp (reverseCells C) (reverseAssignment C a) := by
  intro q w i j hij hdev hmean hsupport hzeros
  apply hC q w i j hij
  · simpa [localVertexMap_reverseAssignment] using hdev
  · simpa [localVertexMap_reverseAssignment] using hmean
  · intro k hk
    have h := hsupport k hk
    change 1 - (C.vertex q k).time.1 = 1 at h
    linarith
  · exact hzeros

/-- Composing a lower-safe left collar and an upper-safe right collar gives the exact frozen
positive-support condition used by Route B. -/
theorem frozenSafe_combined
    {Nmid M₀ L₀ M₁ L₁ : Nat}
    (C : RelativeAffineCellSystem hp N₀ Nmid M₀ L₀)
    (D : RelativeAffineCellSystem hp Nmid N₁ M₁ L₁)
    (a : Assignment hp C) (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b))
    (hC : LowerPositiveSupportRaySafe hp C a)
    (hD : UpperPositiveSupportRaySafe hp D b) :
    FrozenPositiveSupportRaySafe hp (combinedCells C D)
      (combinedAssignment C D a b hseam) := by
  intro q w i j hij hdev hmean hsupport hzeros
  cases q with
  | inl q =>
      apply hC q w i j hij
      · simpa [localVertexMap_combinedAssignment_left] using hdev
      · simpa [localVertexMap_combinedAssignment_left] using hmean
      · intro k hk
        have hf := hsupport k hk (⟨0, hp.pos⟩ : Fin p)
        have hh := (isFrozenParameter_localParameter_iff hp
          (combinedCells C D) (Sum.inl q) k (⟨0, hp.pos⟩ : Fin p)).1 hf
        rcases hh with hh | hh
        · change (C.vertex q k).time.1 / 2 = 0 at hh
          linarith
        · have hle := (C.vertex q k).time.2.2
          change (C.vertex q k).time.1 / 2 = 1 at hh
          exfalso
          linarith
      · exact hzeros
  | inr q =>
      apply hD q w i j hij
      · simpa [localVertexMap_combinedAssignment_right] using hdev
      · simpa [localVertexMap_combinedAssignment_right] using hmean
      · intro k hk
        have hf := hsupport k hk (⟨0, hp.pos⟩ : Fin p)
        have hh := (isFrozenParameter_localParameter_iff hp
          (combinedCells C D) (Sum.inr q) k (⟨0, hp.pos⟩ : Fin p)).1 hf
        rcases hh with hh | hh
        · have hge := (D.vertex q k).time.2.1
          change (1 + (D.vertex q k).time.1) / 2 = 0 at hh
          exfalso
          linarith
        · change (1 + (D.vertex q k).time.1) / 2 = 1 at hh
          linarith
      · exact hzeros

/-- Every iterated positive endpoint stack is lower-support safe. -/
theorem build_lowerPositiveSupportRaySafe
    {F : ContinuousCoordinateMap p}
    (A : StableRegularApproximation hp F) :
    ∀ k : Nat,
      LowerPositiveSupportRaySafe hp
        (positiveWitness hp A.toRegularApproximation.level k).collar.cells
        (build hp A.toRegularApproximation k).assignment
  | 0 => by
      simpa [positiveWitness, EndpointStackIteratedAffinePullback.build,
        RelativeSubdivisionEndpointCollar.oneStepWitness,
        RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar,
        RelativeSubdivisionOneStepCollar.relativeCollar] using
        oneStep_lowerPositiveSupportRaySafe hp A
  | k + 1 => by
      let D0 := build hp A.toRegularApproximation k
      let K := baseOriginalPLMap hp A.toRegularApproximation
      let C0 := (positiveWitness hp A.toRegularApproximation.level k).collar
      let E := (RelativeSubdivisionEndpointCollar.oneStepWitness hp
        (A.toRegularApproximation.level + (k + 1))).collar
      let b : Assignment hp E.cells := by
        simpa [E, RelativeSubdivisionEndpointCollar.oneStepWitness,
          RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar,
          RelativeSubdivisionOneStepCollar.relativeCollar] using
          CompatibleChartMapOneStep.assignment hp (K.refine (k + 1))
      have hbRep : ChartMapCollarRepresentation.Represents E.cells K
          (vectorValue hp E.cells b) := by
        simpa [E, b, RelativeSubdivisionEndpointCollar.oneStepWitness,
          RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar,
          RelativeSubdivisionOneStepCollar.relativeCollar] using
          oneStepAssignment_represents_base hp K (k + 1)
      let hseam := ChartMapCollarRepresentation.seamCompatible C0.cells E.cells K
        (vectorValue hp C0.cells D0.assignment) (vectorValue hp E.cells b)
        D0.represents hbRep
      simpa [positiveWitness, EndpointStackIteratedAffinePullback.build,
        C0, E, b, hseam,
        RelativeSubdivisionEndpointCollar.composeWitness,
        ExplicitAffineRelativeCollarCompose.endpointIdentifiedCollar,
        ExplicitAffineRelativeCollarCompose.relativeCollar] using
        lowerSafe_combined_left hp C0.cells E.cells D0.assignment b hseam
          (build_lowerPositiveSupportRaySafe A k)

end RouteBFrozenSupportGeometry
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
