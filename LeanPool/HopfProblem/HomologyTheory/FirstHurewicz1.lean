/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3

/-!
# Hopf problem: homology theory · first hurewicz 1

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

public
theorem SphereHomology.singularHomologyMap_zero_injective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] [PathConnectedSpace Y] (f : C(X, Y)) :
    Function.Injective (SingularMayerVietoris.singularHomologyMap f 0) := by
  intro a b h
  apply (PeriodTorusHigherHomology.connectedHomologyZeroEquiv X).injective
  simpa only [PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural] using
    congrArg (PeriodTorusHigherHomology.connectedHomologyZeroEquiv Y) h

private theorem SphereHomology.singularHomologyMap_zero_surjective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] [PathConnectedSpace Y] (f : C(X, Y)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap f 0) := by
  intro b
  refine
    ⟨(PeriodTorusHigherHomology.connectedHomologyZeroEquiv X).symm
        (PeriodTorusHigherHomology.connectedHomologyZeroEquiv Y b),
      ?_⟩
  apply (PeriodTorusHigherHomology.connectedHomologyZeroEquiv Y).injective
  rw [PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural, LinearEquiv.apply_symm_apply]

private theorem SphereHomology.singularHomologyMap_zero_bijective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] [PathConnectedSpace Y] (f : C(X, Y)) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap f 0) :=
  ⟨singularHomologyMap_zero_injective f, singularHomologyMap_zero_surjective f⟩

private theorem SphereHomology.leftHomologyMap_zero_injective {X : Type} [TopologicalSpace X]
    (U V : Set X) [PathConnectedSpace (U ∩ V : Set X)] [PathConnectedSpace U] :
    Function.Injective (SingularMayerVietoris.leftHomologyMap U V 0) := by
  intro a b h
  apply
    singularHomologyMap_zero_injective
      (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U))
  simpa only [SingularMayerVietoris.leftHomologyMap_apply] using congrArg Prod.fst h

private theorem
    SphereHomology.leftHomologyMap_zero_ker {X : Type} [TopologicalSpace X] (U V : Set X)
    [PathConnectedSpace (U ∩ V : Set X)] [PathConnectedSpace U] :
    LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (leftHomologyMap_zero_injective U V)

private def FirstHurewicz.lowerTriangleMap : C(Simplex 2, unitInterval × unitInterval)
    where
  toFun s := (simplexCoordinate 2 2 s, unitInterval.symm (simplexCoordinate 2 0 s))
  continuous_toFun :=
    (simplexCoordinate 2 2).continuous.prodMk
      (unitInterval.continuous_symm.comp (simplexCoordinate 2 0).continuous)

private def FirstHurewicz.upperTriangleMap : C(Simplex 2, unitInterval × unitInterval)
    where
  toFun s := (unitInterval.symm (simplexCoordinate 2 0 s), simplexCoordinate 2 2 s)
  continuous_toFun :=
    (unitInterval.continuous_symm.comp (simplexCoordinate 2 0).continuous).prodMk
      (simplexCoordinate 2 2).continuous

private theorem FirstHurewicz.lowerTriangle_face_zero (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 0 s) = (simplexCoordinate 1 1 s, 1) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 0 s 2 = s 1
    exact congrFun (simplexFace_one_zero s) 2
  · change 1 - simplexFace 1 0 s 0 = 1
    rw [simplexFace_apply_self]
    ring

private theorem FirstHurewicz.lowerTriangle_face_one (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 1 s) = (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 1 s 2 = s 1
    exact congrFun (simplexFace_one_one s) 2
  · change 1 - simplexFace 1 1 s 0 = s 1
    have h0 : simplexFace 1 1 s 0 = s 0 := congrFun (simplexFace_one_one s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]

private theorem FirstHurewicz.lowerTriangle_face_two (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 2 s) = (0, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 2 s 2 = 0
    exact simplexFace_apply_self 1 2 s
  · change 1 - simplexFace 1 2 s 0 = s 1
    have h0 : simplexFace 1 2 s 0 = s 0 := congrFun (simplexFace_one_two s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]

private theorem FirstHurewicz.upperTriangle_face_zero (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 0 s) = (1, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 0 s 0 = 1
    rw [simplexFace_apply_self]
    ring
  · change simplexFace 1 0 s 2 = s 1
    exact congrFun (simplexFace_one_zero s) 2

private theorem FirstHurewicz.upperTriangle_face_one (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 1 s) = (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 1 s 0 = s 1
    have h0 : simplexFace 1 1 s 0 = s 0 := congrFun (simplexFace_one_one s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]
  · change simplexFace 1 1 s 2 = s 1
    exact congrFun (simplexFace_one_one s) 2

private theorem FirstHurewicz.upperTriangle_face_two (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 2 s) = (simplexCoordinate 1 1 s, 0) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 2 s 0 = s 1
    have h0 : simplexFace 1 2 s 0 = s 0 := congrFun (simplexFace_one_two s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]
  · change simplexFace 1 2 s 2 = 0
    exact simplexFace_apply_self 1 2 s

private def
    FirstHurewicz.homotopyLowerSimplex {X : Type*} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (H : p.Homotopy q) : C(Simplex 2, X) :=
  H.toHomotopy.toContinuousMap.comp lowerTriangleMap

private def
    FirstHurewicz.homotopyUpperSimplex {X : Type*} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (H : p.Homotopy q) : C(Simplex 2, X) :=
  H.toHomotopy.toContinuousMap.comp upperTriangleMap

private def FirstHurewicz.homotopyDiagonalSimplex {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) : C(Simplex 1, X)
    where
  toFun s := H (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s)
  continuous_toFun :=
    H.continuous.comp
      ((simplexCoordinate 1 1).continuous.prodMk (simplexCoordinate 1 1).continuous)

@[simp]
private theorem
    FirstHurewicz.homotopyLowerSimplex_face_zero {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 0) = ContinuousMap.const (Simplex 1) y := by
  apply ContinuousMap.ext
  intro s
  change H (lowerTriangleMap (simplexFace 1 0 s)) = y
  rw [lowerTriangle_face_zero, H.target]

@[simp]
private theorem
    FirstHurewicz.homotopyLowerSimplex_face_one {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 1) = homotopyDiagonalSimplex H := by
  apply ContinuousMap.ext
  intro s
  change H (lowerTriangleMap (simplexFace 1 1 s)) = _
  rw [lowerTriangle_face_one]
  rfl

@[simp]
private theorem
    FirstHurewicz.homotopyLowerSimplex_face_two {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 2) = pathSimplex p := by
  apply ContinuousMap.ext
  intro s
  change H (lowerTriangleMap (simplexFace 1 2 s)) = pathSimplex p s
  rw [lowerTriangle_face_two]
  exact H.map_zero_left _

@[simp]
private theorem
    FirstHurewicz.homotopyUpperSimplex_face_zero {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 0) = pathSimplex q := by
  apply ContinuousMap.ext
  intro s
  change H (upperTriangleMap (simplexFace 1 0 s)) = pathSimplex q s
  rw [upperTriangle_face_zero]
  exact H.map_one_left _

@[simp]
private theorem
    FirstHurewicz.homotopyUpperSimplex_face_one {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 1) = homotopyDiagonalSimplex H := by
  apply ContinuousMap.ext
  intro s
  change H (upperTriangleMap (simplexFace 1 1 s)) = _
  rw [upperTriangle_face_one]
  rfl

@[simp]
private theorem
    FirstHurewicz.homotopyUpperSimplex_face_two {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 2) = ContinuousMap.const (Simplex 1) x := by
  apply ContinuousMap.ext
  intro s
  change H (upperTriangleMap (simplexFace 1 2 s)) = x
  rw [upperTriangle_face_two, H.source]

private def FirstHurewicz.pointChain {X : Type} [TopologicalSpace X] (x : X) : Chains X 0 :=
  simplexChain X 0 (ContinuousMap.const (Simplex 0) x)

private def FirstHurewicz.pathChain {X : Type} [TopologicalSpace X] {x y : X} (p : Path x y) :
    Chains X 1 :=
  simplexChain X 1 (pathSimplex p)

private theorem FirstHurewicz.boundaryOne_pathChain {X : Type} [TopologicalSpace X] {x y : X}
    (p : Path x y) : boundaryOne X (pathChain p) = pointChain y - pointChain x := by
  rw [pathChain, boundaryOne_simplex, pathSimplex_face_zero, pathSimplex_face_one]
  rfl

private theorem
    FirstHurewicz.boundaryOne_loop {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) :
    boundaryOne X (pathChain p) = 0 := by rw [boundaryOne_pathChain, sub_self]

private def FirstHurewicz.concatChain {X : Type} [TopologicalSpace X] {x y z : X} (p : Path x y)
    (q : Path y z) : Chains X 2 :=
  simplexChain X 2 (concatSimplex p q)

private theorem FirstHurewicz.boundaryTwo_concatChain {X : Type} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) :
    boundaryTwo X (concatChain p q) = pathChain q - pathChain (p.trans q) + pathChain p := by
  rw [concatChain, boundaryTwo_simplex, concatSimplex_face_zero, concatSimplex_face_one,
    concatSimplex_face_two]
  rfl

private def FirstHurewicz.constantEdgeChain {X : Type} [TopologicalSpace X] (x : X) : Chains X 1 :=
  simplexChain X 1 (ContinuousMap.const (Simplex 1) x)

private def
    FirstHurewicz.constantTriangleChain {X : Type} [TopologicalSpace X] (x : X) : Chains X 2 :=
  simplexChain X 2 (ContinuousMap.const (Simplex 2) x)

private theorem
    FirstHurewicz.boundaryTwo_constantTriangleChain {X : Type} [TopologicalSpace X] (x : X) :
    boundaryTwo X (constantTriangleChain x) = constantEdgeChain x := by
  rw [constantTriangleChain, boundaryTwo_simplex]
  change constantEdgeChain x - constantEdgeChain x + constantEdgeChain x = _
  abel

@[simp]
private theorem FirstHurewicz.pathChain_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathChain (Path.refl x) = constantEdgeChain x :=
  rfl

private def FirstHurewicz.homotopyChain {X : Type} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (H : p.Homotopy q) : Chains X 2 :=
  simplexChain X 2 (homotopyLowerSimplex H) - simplexChain X 2 (homotopyUpperSimplex H)

private theorem FirstHurewicz.boundaryTwo_homotopyChain {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    boundaryTwo X (homotopyChain H) =
      pathChain p - pathChain q + constantEdgeChain y - constantEdgeChain x := by
  rw [homotopyChain, map_sub, boundaryTwo_simplex, boundaryTwo_simplex,
    homotopyLowerSimplex_face_zero, homotopyLowerSimplex_face_one, homotopyLowerSimplex_face_two,
    homotopyUpperSimplex_face_zero, homotopyUpperSimplex_face_one, homotopyUpperSimplex_face_two]
  change
    constantEdgeChain y - simplexChain X 1 (homotopyDiagonalSimplex H) + pathChain p -
        (pathChain q - simplexChain X 1 (homotopyDiagonalSimplex H) + constantEdgeChain x) =
      _
  abel

private def FirstHurewicz.correctedHomotopyChain {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) : Chains X 2 :=
  homotopyChain H - constantTriangleChain y + constantTriangleChain x

private theorem
    FirstHurewicz.boundaryTwo_correctedHomotopyChain {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    boundaryTwo X (correctedHomotopyChain H) = pathChain p - pathChain q := by
  rw [correctedHomotopyChain, map_add, map_sub, boundaryTwo_homotopyChain,
    boundaryTwo_constantTriangleChain, boundaryTwo_constantTriangleChain]
  abel

private theorem FirstHurewicz.boundaryTwo_loopHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {p q : Path x x} (H : p.Homotopy q) :
    boundaryTwo X (homotopyChain H) = pathChain p - pathChain q := by
  rw [boundaryTwo_homotopyChain]
  abel

end Mathoverflow1973

end
