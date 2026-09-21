/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StablePatchedHomotopyBoundary
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarMiddlePrismEndpoints
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarGenericity
/-!
# Fine middle-prism control and quantitative origin margins

The endpoint-identified collar is assembled from two relative subdivision stacks and a common-level
middle prism.  This file supplies the quantitative part of the middle-prism construction for the
continuous patched homotopy.

For every preselected spatial level, sufficiently deep staircase subdivision makes the patched
homotopy oscillate by less than any prescribed positive amount on every middle-prism simplex.  The
assignment obtained by sampling the patched homotopy at the relative-cell vertices is then uniformly
close to the continuous patched homotopy on each simplex.  Compact zero-freeness therefore gives a
strict positive coordinate margin.  Any full assignment, in particular any boundary-fixed movable
replacement, within half that margin remains origin-free on every middle-prism cell.

The lower and upper relative subdivision stacks require their separate endpoint-control argument;
that assembly is intentionally not hidden in the middle-prism theorem below.
-/

namespace NRR

open scoped BigOperators
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StablePatchedHomotopyFineMargin

open EquivariantCoordinateHomotopy
open RefinedAffineMap
open StablePatchedHomotopyBoundary
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open ExplicitAffineRelativeCollar.RelativeGenericity
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open RelativeCollarMiddlePrism
open SubdivisionPrismCharts
open EquivariantPrismSubdivisionMargin
open EquivariantPrismGenericPerturbation

variable {p : Nat}

/-- Scalar sample of a zero-free homotopy on one relative middle-prism parameter site. -/
noncomputable def middleHomotopySiteValue
    (hp : Nat.Prime p) (N L : Nat)
    {G₀ G₁ : ZeroFreeMap hp} (K : ZeroFreeHomotopy hp G₀ G₁)
    (s : ScalarSite hp (RelativeCollarMiddlePrism.cellSystem hp N L)) : Real :=
  K.map
    (EquivariantPrismVertexParameters.CylinderPoint.toProd
      (globalPoint hp (RelativeCollarMiddlePrism.cellSystem hp N L) s.1)) s.2

/-- Middle-prism homotopy samples are constant on diagonal prime orbits. -/
theorem middleHomotopySiteValue_eq_of_orbitRel
    (hp : Nat.Prime p) (N L : Nat)
    {G₀ G₁ : ZeroFreeMap hp} (K : ZeroFreeHomotopy hp G₀ G₁)
    {a b : ScalarSite hp (RelativeCollarMiddlePrism.cellSystem hp N L)}
    (hab : MulAction.orbitRel (PrimeSymmetry hp)
      (ScalarSite hp (RelativeCollarMiddlePrism.cellSystem hp N L)) a b) :
    middleHomotopySiteValue hp N L K a =
      middleHomotopySiteValue hp N L K b := by
  rw [MulAction.orbitRel_apply] at hab
  rcases hab with ⟨g, hgab⟩
  subst a
  change K.map
      (EquivariantPrismVertexParameters.CylinderPoint.toProd
        (globalPoint hp (RelativeCollarMiddlePrism.cellSystem hp N L) (g • b.1)))
      (g • b.2) =
    K.map
      (EquivariantPrismVertexParameters.CylinderPoint.toProd
        (globalPoint hp (RelativeCollarMiddlePrism.cellSystem hp N L) b.1)) b.2
  rw [globalPoint_smul]
  have heq := K.equivariant g
    (globalPoint hp (RelativeCollarMiddlePrism.cellSystem hp N L) b.1).spatial
    (globalPoint hp (RelativeCollarMiddlePrism.cellSystem hp N L) b.1).time
  have hj := congrFun heq (g • b.2)
  simpa [EquivariantPrismVertexParameters.CylinderPoint.toProd, PrimeSymmetry.smul_coordinate_apply,
    PrimeSymmetry.smul_label] using hj

/-- Relative-cell assignment obtained by sampling a zero-free homotopy on every middle-prism
vertex. -/
noncomputable def middleHomotopyAssignment
    (hp : Nat.Prime p) (N L : Nat)
    {G₀ G₁ : ZeroFreeMap hp} (K : ZeroFreeHomotopy hp G₀ G₁) :
    Assignment hp (RelativeCollarMiddlePrism.cellSystem hp N L) :=
  fun q => Quotient.liftOn q (middleHomotopySiteValue hp N L K) (by
    intro a b hab
    exact middleHomotopySiteValue_eq_of_orbitRel hp N L K hab)

/-- Reconstructing the relative middle-prism assignment gives the original homotopy sample at every
sampled global vertex. -/
theorem vectorValue_middleHomotopyAssignment
    (hp : Nat.Prime p) (N L : Nat)
    {G₀ G₁ : ZeroFreeMap hp} (K : ZeroFreeHomotopy hp G₀ G₁)
    (x : GlobalVertex hp (RelativeCollarMiddlePrism.cellSystem hp N L)) :
    vectorValue hp (RelativeCollarMiddlePrism.cellSystem hp N L)
        (middleHomotopyAssignment hp N L K) x =
      K.map
        (EquivariantPrismVertexParameters.CylinderPoint.toProd
          (globalPoint hp (RelativeCollarMiddlePrism.cellSystem hp N L) x)) := by
  funext j
  rfl

/-- On every local relative middle-prism vertex, the sampled assignment is exactly the homotopy
value at the corresponding staircase-prism vertex. -/
theorem localVertexMap_middleHomotopyAssignment
    (hp : Nat.Prime p) (N L : Nat)
    {G₀ G₁ : ZeroFreeMap hp} (K : ZeroFreeHomotopy hp G₀ G₁)
    (q : PrismCell hp N L) (i : Fin (p + 1)) :
    (localVertexMap hp (RelativeCollarMiddlePrism.cellSystem hp N L)
      (middleHomotopyAssignment hp N L K) q).value i =
      K.map (SubdivisionPrismCharts.vertex hp N L q i) := by
  change vectorValue hp (RelativeCollarMiddlePrism.cellSystem hp N L)
      (middleHomotopyAssignment hp N L K)
      (sampleVertex hp (RelativeCollarMiddlePrism.cellSystem hp N L) (q, i)) = _
  rw [vectorValue_middleHomotopyAssignment]
  simp [RelativeCollarMiddlePrism.cellSystem,
    RelativeAffineCellSystem.slotPoint,
    RelativeCollarMiddlePrism.vertex,
    EquivariantPrismVertexParameters.CylinderPoint.toProd,
    EquivariantPrismVertexParameters.CylinderPoint.ofProd]

/-- Fine-middle oscillation for the patched homotopy at a prescribed initial spatial level. -/
theorem exists_patchedMiddle_refinement_oscillation
    (hp : Nat.Prime p) (N : Nat)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    {eps : Real} (heps : 0 < eps) :
    ∃ L : Nat, ∀ (q : PrismCell hp N L)
      (u v : StandardSimplex p),
      dist
        ((stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
          (SubdivisionPrismCharts.chart hp N L q (StandardSimplex.toDelta u)))
        ((stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
          (SubdivisionPrismCharts.chart hp N L q (StandardSimplex.toDelta v))) < eps :=
  exists_staircase_refinement_oscillation hp N
    (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁) heps

/-- On one middle-prism simplex, an oscillation bound controls the error between affine vertex
interpolation and the continuous homotopy. -/
theorem norm_middleAffineValue_sub_homotopy_le_of_oscillation
    (hp : Nat.Prime p) (N L : Nat)
    {G₀ G₁ : ZeroFreeMap hp} (K : ZeroFreeHomotopy hp G₀ G₁)
    (q : PrismCell hp N L) (eps : Real)
    (hosc : ∀ u v : StandardSimplex p,
      dist
        (K.map (SubdivisionPrismCharts.chart hp N L q (StandardSimplex.toDelta u)))
        (K.map (SubdivisionPrismCharts.chart hp N L q (StandardSimplex.toDelta v))) < eps)
    (w : StandardSimplex p) :
    ‖affineValue
        (localVertexMap hp (RelativeCollarMiddlePrism.cellSystem hp N L)
          (middleHomotopyAssignment hp N L K) q) w -
      K.map (SubdivisionPrismCharts.chart hp N L q (StandardSimplex.toDelta w))‖ ≤ eps := by
  classical
  let y : Fin p → Real :=
    K.map (SubdivisionPrismCharts.chart hp N L q (StandardSimplex.toDelta w))
  have hid :
      affineValue
          (localVertexMap hp (RelativeCollarMiddlePrism.cellSystem hp N L)
            (middleHomotopyAssignment hp N L K) q) w - y =
        ∑ i : Fin (p + 1),
          w i • (K.map (SubdivisionPrismCharts.vertex hp N L q i) - y) := by
    funext j
    have hw : ∑ i : Fin (p + 1), (w : Fin (p + 1) → Real) i = 1 := w.sum_eq_one
    simp only [affineValue, localVertexMap_middleHomotopyAssignment, y,
      Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul]
  rw [hid]
  calc
    ‖∑ i : Fin (p + 1),
        w i • (K.map (SubdivisionPrismCharts.vertex hp N L q i) - y)‖
        ≤ ∑ i : Fin (p + 1),
          ‖w i • (K.map (SubdivisionPrismCharts.vertex hp N L q i) - y)‖ :=
      norm_sum_le _ _
    _ = ∑ i : Fin (p + 1),
        w i * ‖K.map (SubdivisionPrismCharts.vertex hp N L q i) - y‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (w.nonneg i)]
    _ ≤ ∑ i : Fin (p + 1), w i * eps := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (le_of_lt (by
          simpa [dist_eq_norm, SubdivisionPrismCharts.vertex, y] using
            hosc
              (StandardSimplex.ofDelta (stdSimplex.vertex (S := Real) i)) w))
        (w.nonneg i)
    _ = eps := by
      rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

/-- For every prescribed initial spatial level, some fully refined middle prism has a positive
coordinate margin for the sampled patched homotopy. -/
theorem exists_patchedMiddle_refinement_coordinateNormMargin
    (hp : Nat.Prime p) (N : Nat)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    ∃ (L : Nat) (m : Real), 0 < m ∧
      LocalAffineCoordinateNormMargin hp
        (RelativeCollarMiddlePrism.cellSystem hp N L)
        (middleHomotopyAssignment hp N L
          (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁)) m := by
  classical
  let K := stablePatchedHomotopy hp F₀ F₁ H A₀ A₁
  obtain ⟨M, hM, hmargin⟩ :=
    exists_positive_homotopy_norm_margin hp K
  obtain ⟨L, hosc⟩ :=
    exists_patchedMiddle_refinement_oscillation hp N F₀ F₁ H A₀ A₁
      (show 0 < M / 2 by positivity)
  refine ⟨L, M / 2, by positivity, ?_⟩
  intro q w
  let y : Fin p → Real :=
    K.map (SubdivisionPrismCharts.chart hp N L q (StandardSimplex.toDelta w))
  let z : Fin p → Real :=
    affineValue
      (localVertexMap hp (RelativeCollarMiddlePrism.cellSystem hp N L)
        (middleHomotopyAssignment hp N L K) q) w
  have hclose : ‖z - y‖ ≤ M / 2 := by
    simpa [z, y, K] using
      norm_middleAffineValue_sub_homotopy_le_of_oscillation
        hp N L K q (M / 2) (hosc q) w
  have hy : M ≤ ‖y‖ := hmargin _
  have hy_le : ‖y‖ ≤ ‖z - y‖ + ‖z‖ := by
    calc
      ‖y‖ = ‖-(z - y) + z‖ := by
        congr 1
        module
      _ ≤ ‖-(z - y)‖ + ‖z‖ := norm_add_le _ _
      _ = ‖z - y‖ + ‖z‖ := by rw [norm_neg]
  have hz : M / 2 ≤ ‖z‖ := by linarith
  obtain ⟨j, hj⟩ := exists_coordinate_abs_ge_norm hp z
  refine ⟨j, le_trans hz ?_⟩
  simpa [z, Real.norm_eq_abs] using hj

/-- Any assignment within half of a positive local coordinate margin remains origin-free on every
cell. -/
theorem avoidsOrigin_of_assignmentClose_half_margin
    {N₀ N₁ M L : Nat}
    (hp : Nat.Prime p)
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (base perturbed : Assignment hp C)
    {margin : Real} (hmargin : 0 < margin)
    (hbase : LocalAffineCoordinateNormMargin hp C base margin)
    (hclose : AssignmentClose perturbed base (margin / 2)) :
    ∀ q : C.Cell, AvoidsOrigin (localVertexMap hp C perturbed q) := by
  have hretainedRaw := retain_localAffineCoordinateNormMargin hp C
    perturbed base hbase hclose
  have hretained : LocalAffineCoordinateNormMargin hp C perturbed (margin / 2) := by
    convert hretainedRaw using 1; ring
  intro q
  exact avoidsOrigin_of_localAffineCoordinateNormMargin hp C
    perturbed (half_pos hmargin) hretained q

/-- In particular, a boundary-fixed movable replacement within half of the middle-prism margin
remains origin-free cellwise. -/
theorem middle_replaceMovable_avoidsOrigin
    (hp : Nat.Prime p) (N L : Nat)
    {G₀ G₁ : ZeroFreeMap hp} (K : ZeroFreeHomotopy hp G₀ G₁)
    {margin : Real} (hmargin : 0 < margin)
    (hbase : LocalAffineCoordinateNormMargin hp
      (RelativeCollarMiddlePrism.cellSystem hp N L)
      (middleHomotopyAssignment hp N L K) margin)
    (move : MovableParameter hp (RelativeCollarMiddlePrism.cellSystem hp N L) → Real)
    (hclose : AssignmentClose
      (replaceMovable hp (RelativeCollarMiddlePrism.cellSystem hp N L)
        (middleHomotopyAssignment hp N L K) move)
      (middleHomotopyAssignment hp N L K) (margin / 2)) :
    ∀ q : PrismCell hp N L,
      AvoidsOrigin
        (localVertexMap hp (RelativeCollarMiddlePrism.cellSystem hp N L)
          (replaceMovable hp (RelativeCollarMiddlePrism.cellSystem hp N L)
            (middleHomotopyAssignment hp N L K) move) q) :=
  avoidsOrigin_of_assignmentClose_half_margin hp
    (RelativeCollarMiddlePrism.cellSystem hp N L)
    (middleHomotopyAssignment hp N L K)
    (replaceMovable hp (RelativeCollarMiddlePrism.cellSystem hp N L)
      (middleHomotopyAssignment hp N L K) move)
    hmargin hbase hclose

end StablePatchedHomotopyFineMargin
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
