/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableFullCollarOriginMargin

/-!
# Relative-mesh completion of the fine full collar

This module isolates the geometric certificate for a boundary-preserving fine relative mesh.  The assignment is the globally defined patched
homotopy assignment.  A relative mesh certificate records:

* exact agreement of every local vertex sample with the patched zero-free homotopy;
* a positive global norm margin for that homotopy; and
* sufficiently small oscillation on every affine collar cell.

The affine interpolation estimate is independent of the particular middle-prism cell system.
Consequently any endpoint-identified relative collar satisfying this certificate yields an actual
`FineFullCollarData` term, including literal horizontal endpoint values and cellwise origin
avoidance.

The construction problem is geometric: construct a boundary-preserving
relative triangulation fine enough to satisfy `cellOscillation` and prove its local vertices have the
stated patched-sample representation.  No overlap or seam assumption is hidden in the adapter.
-/

namespace NRR

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableFullCollarRelativeMesh

open EquivariantCoordinateHomotopy
open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open AffinePositiveRayBoundary
open StablePatchedHomotopyBoundary
open StablePatchedHomotopyFineMargin
open StableFullCollarOriginMargin
open EquivariantPrismSubdivisionMargin
open ExplicitAffineRelativeCollar.Polynomials
open AffinePositiveRayBoundary.VertexMap

variable {p : Nat}

/-- A fixed positive global norm margin for the patched homotopy. -/
noncomputable def patchedHomotopyMargin
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) : Real :=
  Classical.choose
    (exists_positive_homotopy_norm_margin hp
      (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁))

/-- The chosen patched-homotopy margin is positive. -/
theorem patchedHomotopyMargin_pos
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    0 < patchedHomotopyMargin hp F₀ F₁ H A₀ A₁ :=
  (Classical.choose_spec
    (exists_positive_homotopy_norm_margin hp
      (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁))).1

/-- The chosen margin bounds the norm of every patched-homotopy value. -/
theorem patchedHomotopyMargin_le_norm
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (z : Realization p × Set.Icc (0 : Real) 1) :
    patchedHomotopyMargin hp F₀ F₁ H A₀ A₁ ≤
      ‖(stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map z‖ :=
  (Classical.choose_spec
    (exists_positive_homotopy_norm_margin hp
      (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁))).2 z

/-- On an arbitrary affine collar cell, vertexwise samples of a continuous homotopy are uniformly
close to the homotopy value whenever the homotopy oscillates by less than `eps` on that cell. -/
theorem norm_localAffineValue_sub_homotopy_le_of_oscillation
    {N₀ N₁ M L : Nat}
    (hp : Nat.Prime p)
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    {G₀ G₁ : ZeroFreeMap hp}
    (K : ZeroFreeHomotopy hp G₀ G₁)
    (a : Assignment hp C)
    (q : C.Cell)
    (eps : Real)
    (hsample : ∀ i : Fin (p + 1),
      (localVertexMap hp C a q).value i =
        K.map (EquivariantPrismVertexParameters.CylinderPoint.toProd (C.vertex q i)))
    (hosc : ∀ u v : StandardSimplex p,
      dist
        (K.map (EquivariantPrismVertexParameters.CylinderPoint.toProd
          (C.chart q (StandardSimplex.toDelta u))))
        (K.map (EquivariantPrismVertexParameters.CylinderPoint.toProd
          (C.chart q (StandardSimplex.toDelta v)))) < eps)
    (w : StandardSimplex p) :
    ‖affineValue (localVertexMap hp C a q) w -
      K.map (EquivariantPrismVertexParameters.CylinderPoint.toProd
        (C.chart q (StandardSimplex.toDelta w)))‖ ≤ eps := by
  classical
  let y : Fin p → Real :=
    K.map (EquivariantPrismVertexParameters.CylinderPoint.toProd
      (C.chart q (StandardSimplex.toDelta w)))
  have hid :
      affineValue (localVertexMap hp C a q) w - y =
        ∑ i : Fin (p + 1), w i •
          (K.map (EquivariantPrismVertexParameters.CylinderPoint.toProd (C.vertex q i)) - y) := by
    funext j
    simp only [affineValue, hsample, y, Pi.sub_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, w.sum_eq_one, one_mul]
  rw [hid]
  calc
    ‖∑ i : Fin (p + 1), w i •
        (K.map (EquivariantPrismVertexParameters.CylinderPoint.toProd (C.vertex q i)) - y)‖
        ≤ ∑ i : Fin (p + 1),
          ‖w i • (K.map (EquivariantPrismVertexParameters.CylinderPoint.toProd (C.vertex q i)) - y)‖ :=
      norm_sum_le _ _
    _ = ∑ i : Fin (p + 1),
        w i * ‖K.map (EquivariantPrismVertexParameters.CylinderPoint.toProd (C.vertex q i)) - y‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (w.nonneg i)]
    _ ≤ ∑ i : Fin (p + 1), w i * eps := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (le_of_lt (by
          have h := hosc
            (StandardSimplex.ofDelta (stdSimplex.vertex (S := Real) i)) w
          simpa [dist_eq_norm, C.chart_vertex, y] using h))
        (w.nonneg i)
    _ = eps := by
      rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

/-- A cellwise reference-control certificate for the exact fine full collar.

This is the robust analytic interface for item 4.  Different classes of collar cells may use
*different* zero-free reference maps: endpoint cells can be compared with the already constructed
endpoint PL maps, while interior cells can be compared with the patched homotopy.  This avoids the
false requirement that one global continuous reference have arbitrarily small oscillation across
an unsplit horizontal boundary facet. -/
structure FineFullCollarReferenceControlData
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) where
  commonLevel : Nat
  timeLevel : Nat
  collar : EndpointIdentifiedRelativeAffineCollar hp
    A₀.toRegularApproximation.level A₁.toRegularApproximation.level
    commonLevel timeLevel
  assignment : Assignment hp collar.cells
  horizontalVertexFixed : HorizontalVertexFixed hp A₀ A₁ collar assignment
  margin : Real
  margin_pos : 0 < margin
  referenceValue : collar.cells.Cell → StandardSimplex p → Fin p → Real
  referenceNormMargin : ∀ (q : collar.cells.Cell) (w : StandardSimplex p),
    margin ≤ ‖referenceValue q w‖
  affineClose : ∀ (q : collar.cells.Cell) (w : StandardSimplex p),
    ‖affineValue (localVertexMap hp collar.cells assignment q) w -
      referenceValue q w‖ ≤ margin / 2

namespace FineFullCollarReferenceControlData

/-- Half-margin closeness to a cellwise zero-free reference implies origin avoidance. -/
theorem assignment_avoidsOrigin
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (D : FineFullCollarReferenceControlData hp H A₀ A₁)
    (q : D.collar.cells.Cell) :
    AvoidsOrigin (localVertexMap hp D.collar.cells D.assignment q) := by
  intro w
  let y : Fin p → Real := D.referenceValue q w
  let z : Fin p → Real :=
    affineValue (localVertexMap hp D.collar.cells D.assignment q) w
  have hclose : ‖z - y‖ ≤ D.margin / 2 := by
    simpa [z, y] using D.affineClose q w
  have hy : D.margin ≤ ‖y‖ := by
    simpa [y] using D.referenceNormMargin q w
  have hy_le : ‖y‖ ≤ ‖z - y‖ + ‖z‖ := by
    calc
      ‖y‖ = ‖-(z - y) + z‖ := by
        congr 1
        module
      _ ≤ ‖-(z - y)‖ + ‖z‖ := norm_add_le _ _
      _ = ‖z - y‖ + ‖z‖ := by rw [norm_neg]
  have hz : D.margin / 2 ≤ ‖z‖ := by
    linarith
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (half_pos D.margin_pos) hz
  have hzneq : z ≠ 0 := norm_pos_iff.mp hzpos
  simpa [z] using hzneq

/-- A reference-controlled collar is already the exact item-4 output. -/
noncomputable def toFineFullCollarData
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (D : FineFullCollarReferenceControlData hp H A₀ A₁) :
    FineFullCollarData hp H A₀ A₁ where
  commonLevel := D.commonLevel
  timeLevel := D.timeLevel
  collar := D.collar
  assignment := D.assignment
  horizontalVertexFixed := D.horizontalVertexFixed
  baseAvoidsOrigin := D.assignment_avoidsOrigin

end FineFullCollarReferenceControlData

/-- Concrete relative-mesh certificate sufficient for the full fine-collar construction.

Unlike the earlier one-step last-vertex interface, this certificate is stable under gluing: every
local value is the value of one global patched homotopy at the represented cylinder vertex. -/
structure FineRelativePatchedMeshData
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) where
  commonLevel : Nat
  timeLevel : Nat
  collar : EndpointIdentifiedRelativeAffineCollar hp
    A₀.toRegularApproximation.level A₁.toRegularApproximation.level
    commonLevel timeLevel
  localSampleAgreement :
    ∀ (q : collar.cells.Cell) (i : Fin (p + 1)),
      (localVertexMap hp collar.cells
        (patchedBoundaryAssignment hp collar.cells F₀ F₁ H A₀ A₁) q).value i =
        (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
          (EquivariantPrismVertexParameters.CylinderPoint.toProd (collar.cells.vertex q i))
  cellOscillation :
    ∀ (q : collar.cells.Cell) (u v : StandardSimplex p),
      dist
        ((stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
          (EquivariantPrismVertexParameters.CylinderPoint.toProd
            (collar.cells.chart q (StandardSimplex.toDelta u))))
        ((stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
          (EquivariantPrismVertexParameters.CylinderPoint.toProd
            (collar.cells.chart q (StandardSimplex.toDelta v)))) <
        patchedHomotopyMargin hp F₀ F₁ H A₀ A₁ / 2

namespace FineRelativePatchedMeshData


/-- A globally sampled patched mesh is a special case of cellwise reference control. -/
noncomputable def toReferenceControlData
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (D : FineRelativePatchedMeshData hp H A₀ A₁) :
    FineFullCollarReferenceControlData hp H A₀ A₁ where
  commonLevel := D.commonLevel
  timeLevel := D.timeLevel
  collar := D.collar
  assignment := patchedBoundaryAssignment hp D.collar.cells F₀ F₁ H A₀ A₁
  horizontalVertexFixed :=
    horizontalVertexFixed_patchedBoundaryAssignment hp F₀ F₁ H A₀ A₁ D.collar
  margin := patchedHomotopyMargin hp F₀ F₁ H A₀ A₁
  margin_pos := patchedHomotopyMargin_pos hp F₀ F₁ H A₀ A₁
  referenceValue := fun q w =>
    (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
      (EquivariantPrismVertexParameters.CylinderPoint.toProd
        (D.collar.cells.chart q (StandardSimplex.toDelta w)))
  referenceNormMargin := by
    intro q w
    exact patchedHomotopyMargin_le_norm hp F₀ F₁ H A₀ A₁ _
  affineClose := by
    intro q w
    exact norm_localAffineValue_sub_homotopy_le_of_oscillation
      hp D.collar.cells
      (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁)
      (patchedBoundaryAssignment hp D.collar.cells F₀ F₁ H A₀ A₁)
      q (patchedHomotopyMargin hp F₀ F₁ H A₀ A₁ / 2)
      (D.localSampleAgreement q) (D.cellOscillation q) w

/-- The patched affine assignment on every certified relative-mesh cell avoids the origin. -/
theorem patchedAssignment_avoidsOrigin
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (D : FineRelativePatchedMeshData hp H A₀ A₁)
    (q : D.collar.cells.Cell) :
    AvoidsOrigin
      (localVertexMap hp D.collar.cells
        (patchedBoundaryAssignment hp D.collar.cells F₀ F₁ H A₀ A₁) q) :=
  D.toReferenceControlData.assignment_avoidsOrigin q

/-- A certified fine relative mesh produces the exact item-4 output. -/
noncomputable def toFineFullCollarData
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (D : FineRelativePatchedMeshData hp H A₀ A₁) :
    FineFullCollarData hp H A₀ A₁ :=
  D.toReferenceControlData.toFineFullCollarData

end FineRelativePatchedMeshData

/-- General construction target for the relative mesh.  The geometric proof may use the
endpoint PL maps as references on boundary-adjacent cells and the patched homotopy on interior
cells. -/
def FineFullCollarReferenceControlConstructionTheorem : Prop :=
  ∀ {p : Nat} (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map),
      Nonempty (FineFullCollarReferenceControlData hp H A₀ A₁)

/-- Cellwise reference control is sufficient for the original item-4 proposition. -/
theorem fineFullCollarConstruction_of_referenceControl
    (HR : FineFullCollarReferenceControlConstructionTheorem) :
    FineFullCollarConstructionTheorem := by
  intro p hp F₀ F₁ H A₀ A₁
  exact ⟨(Classical.choice (HR hp F₀ F₁ H A₀ A₁)).toFineFullCollarData⟩

/-- A stronger, globally sampled relative-mesh existence target.  It is useful for a collar whose
boundary cells are also sufficiently fine, but is not required by the general reference-control
formulation. -/
def FineRelativePatchedMeshConstructionTheorem : Prop :=
  ∀ {p : Nat} (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map),
      Nonempty (FineRelativePatchedMeshData hp H A₀ A₁)

/-- The concrete relative-mesh theorem closes the original item-4 construction proposition. -/
theorem fineFullCollarConstruction_of_relativePatchedMesh
    (HM : FineRelativePatchedMeshConstructionTheorem) :
    FineFullCollarConstructionTheorem := by
  intro p hp F₀ F₁ H A₀ A₁
  exact ⟨(Classical.choice (HM hp F₀ F₁ H A₀ A₁)).toFineFullCollarData⟩

end StableFullCollarRelativeMesh
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
