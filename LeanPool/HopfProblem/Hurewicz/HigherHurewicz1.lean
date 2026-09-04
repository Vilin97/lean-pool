/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology3
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.Hurewicz.SecondHurewicz
import all LeanPool.HopfProblem.Hurewicz.ThirdHurewicz
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology5
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology3
import all Mathlib.Data.Fin.Tuple.Sort

/-!
# Hopf problem: hurewicz · higher hurewicz 1

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

private theorem
    ThirdHurewicz.basedFourSimplex_signed_relation {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    ∑ i : Fin 5, (-1 : ℤ) ^ i.val • basedThreeSimplexClass (basedFourSimplexFace τ i) = 0 := by
  have h := basedFourSimplex_boundary_relation τ
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h

private theorem
    ThirdHurewicz.normalizedThreeSimplex_boundary_relation {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) :
    ∑ i : Fin 5,
        (-1 : ℤ) ^ i.val •
          basedThreeSimplexClass
            (normalizedThreeSimplex x (smp.comp (FirstHurewicz.simplexFace 3 i))) =
      0 := by
  simpa only [normalizedFourSimplex_face] using
    basedFourSimplex_signed_relation (normalizedFourSimplex x smp)

private theorem ThirdHurewicz.threeSimplexClassOperator_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (b : FirstHurewicz.Chains X 4) :
    threeSimplexClassOperator x (((FirstHurewicz.singularComplex X).d 4 3).hom b) = 0 := by
  have h : (threeSimplexClassOperator x).comp ((FirstHurewicz.singularComplex X).d 4 3).hom = 0 :=
    by
    apply FirstHurewicz.chainMap_ext X 4
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundary_simplex, map_sum, map_zsmul,
      threeSimplexClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedThreeSimplex_boundary_relation x smp
  exact LinearMap.congr_fun h b

private def ThirdHurewicz.cylinderHomotopy {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (H : C((unitInterval) × A, X)) :
    ContinuousMap.Homotopy (SecondHurewicz.SimplyConnected.timeSlice H 0)
      (SecondHurewicz.SimplyConnected.timeSlice H 1)
    where
  toContinuousMap := H
  map_zero_left _ := rfl
  map_one_left _ := rfl

private theorem ThirdHurewicz.homotopyTrans_compContinuousMap {A B X : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace X] {f₀ f₁ f₂ : C(A, X)} (F : f₀.Homotopy f₁)
    (G : f₁.Homotopy f₂) (f : C(B, A)) :
    (F.trans G).toContinuousMap.comp ((ContinuousMap.id (unitInterval)).prodMap f) =
      ((F.compContinuousMap f).trans (G.compContinuousMap f)).toContinuousMap := by
  ext z
  change (F.trans G) (z.1, f z.2) = ((F.compContinuousMap f).trans (G.compContinuousMap f)) z
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> rfl

private theorem
    ThirdHurewicz.homotopyTrans_const {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    {f₀ f₁ f₂ : C(A, X)} (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (x : X)
    (hF : F.toContinuousMap = ContinuousMap.const ((unitInterval) × A) x)
    (hG : G.toContinuousMap = ContinuousMap.const ((unitInterval) × A) x) :
    (F.trans G).toContinuousMap = ContinuousMap.const ((unitInterval) × A) x := by
  ext z
  change (F.trans G) z = x
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact ContinuousMap.congr_fun hF _
  · exact ContinuousMap.congr_fun hG _

private theorem
    ThirdHurewicz.homotopyTrans_congr {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    {f₀ f₁ f₂ g₀ g₁ g₂ : C(A, X)} (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (F' : g₀.Homotopy g₁)
    (G' : g₁.Homotopy g₂) (hF : F.toContinuousMap = F'.toContinuousMap)
    (hG : G.toContinuousMap = G'.toContinuousMap) :
    (F.trans G).toContinuousMap = (F'.trans G').toContinuousMap := by
  ext z
  change (F.trans G) z = (F'.trans G') z
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact ContinuousMap.congr_fun hF _
  · exact ContinuousMap.congr_fun hG _

private def ThirdHurewicz.simplexFamilyHomotopy {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (h₀ : ∀ smp s, H smp (0, s) = smp s) (smp : FirstHurewicz.SingularSimplex X n) :
    smp.Homotopy (SecondHurewicz.SimplyConnected.timeSlice (H smp) 1) :=
  (cylinderHomotopy (H smp)).cast (by ext s; exact h₀ smp s) rfl

private def ThirdHurewicz.composeSimplexHomotopies {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X n) : C((unitInterval) × FirstHurewicz.Simplex n, X) :=
  ((simplexFamilyHomotopy H hH₀ smp).trans
      (simplexFamilyHomotopy G hG₀
        (SecondHurewicz.SimplyConnected.timeSlice (H smp) 1))).toContinuousMap

@[simp]
private theorem ThirdHurewicz.composeSimplexHomotopies_zero {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X n) (s : FirstHurewicz.Simplex n) :
    composeSimplexHomotopies H G hH₀ hG₀ smp (0, s) = smp s :=
  ContinuousMap.Homotopy.apply_zero _ s

@[simp]
private theorem ThirdHurewicz.composeSimplexHomotopies_one {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X n) (s : FirstHurewicz.Simplex n) :
    composeSimplexHomotopies H G hH₀ hG₀ smp (1, s) =
      G (SecondHurewicz.SimplyConnected.timeSlice (H smp) 1) (1, s) :=
  ContinuousMap.Homotopy.apply_one _ s

@[simp]
private theorem ThirdHurewicz.timeSlice_composeSimplexHomotopies_one {X : Type} [TopologicalSpace X]
    {n : ℕ}
    (H G : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X n) :
    SecondHurewicz.SimplyConnected.timeSlice (composeSimplexHomotopies H G hH₀ hG₀ smp) 1 =
      SecondHurewicz.SimplyConnected.timeSlice
        (G (SecondHurewicz.SimplyConnected.timeSlice (H smp) 1)) 1 := by
  ext s
  exact composeSimplexHomotopies_one H G hH₀ hG₀ smp s

private theorem ThirdHurewicz.composeSimplexHomotopies_face {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' G' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (hH'₀ : ∀ smp s, H' smp (0, s) = smp s) (hG'₀ : ∀ smp s, G' smp (0, s) = smp s)
    (hH : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hG : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n G G') :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n
      (composeSimplexHomotopies H G hH₀ hG₀) (composeSimplexHomotopies H' G' hH'₀ hG'₀) := by
  intro smp i
  unfold composeSimplexHomotopies
  rw [homotopyTrans_compContinuousMap]
  apply homotopyTrans_congr
  · change
      (H' smp).comp ((ContinuousMap.id (unitInterval)).prodMap (FirstHurewicz.simplexFace n i)) =
        H (smp.comp (FirstHurewicz.simplexFace n i))
    exact hH smp i
  · change
      (G' (SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)).comp
          ((ContinuousMap.id (unitInterval)).prodMap (FirstHurewicz.simplexFace n i)) =
        G
          (SecondHurewicz.SimplyConnected.timeSlice (H (smp.comp (FirstHurewicz.simplexFace n i)))
            1)
    rw [hG (SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1) i,
      SecondHurewicz.SimplyConnected.timeSlice_face hH smp i 1]

private theorem ThirdHurewicz.composeSimplexHomotopies_const {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s) (x : X)
    (hH :
      H (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (hG :
      G (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x) :
    composeSimplexHomotopies H G hH₀ hG₀ (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x := by
  have h₁ :
    SecondHurewicz.SimplyConnected.timeSlice (H (ContinuousMap.const (FirstHurewicz.Simplex n) x))
        1 =
      ContinuousMap.const (FirstHurewicz.Simplex n) x := by
    rw [hH]
    rfl
  unfold composeSimplexHomotopies
  apply homotopyTrans_const
  · exact hH
  · change
      G
          (SecondHurewicz.SimplyConnected.timeSlice
            (H (ContinuousMap.const (FirstHurewicz.Simplex n) x)) 1) =
        _
    rw [h₁]
    exact hG

private def ThirdHurewicz.vertexEdgeTriangleHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X) :=
  composeSimplexHomotopies (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 2)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero x 2)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_zero x)

private def ThirdHurewicz.vertexEdgeThreeSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    FirstHurewicz.SingularSimplex X 3 → C((unitInterval) × FirstHurewicz.Simplex 3, X) :=
  composeSimplexHomotopies (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 3)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero x 3)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero x)

@[simp]
private theorem ThirdHurewicz.vertexEdgeTriangleHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 2)
    (s : FirstHurewicz.Simplex 2) : vertexEdgeTriangleHomotopy x smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp]
private theorem ThirdHurewicz.vertexEdgeThreeSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 3)
    (s : FirstHurewicz.Simplex 3) : vertexEdgeThreeSimplexHomotopy x smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

private theorem ThirdHurewicz.vertexEdgeHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 (vertexEdgeTriangleHomotopy x)
      (vertexEdgeThreeSimplexHomotopy x) :=
  composeSimplexHomotopies_face (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 2)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 3)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero x 2)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_zero x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero x 3)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_face x 2)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face x)

@[simp]
private theorem ThirdHurewicz.vertexEdgeTriangleHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    vertexEdgeTriangleHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x :=
  composeSimplexHomotopies_const (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 2)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero x 2)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_zero x) x
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_const x 2)
    (edgeTriangleHomotopy_const x)

@[simp]
private theorem
    ThirdHurewicz.vertexEdgeThreeSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 3) :
    SecondHurewicz.SimplyConnected.timeSlice (vertexEdgeThreeSimplexHomotopy x smp) 1 =
      SecondHurewicz.SimplyConnected.normalizedTetrahedronMap x smp := by
  rw [vertexEdgeThreeSimplexHomotopy, timeSlice_composeSimplexHomotopies_one]
  rfl

private def ThirdHurewicz.normalizationTriangleHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X) :=
  composeSimplexHomotopies (vertexEdgeTriangleHomotopy x) (triangleStraighteningHomotopy x)
    (vertexEdgeTriangleHomotopy_zero x) (triangleStraighteningHomotopy_zero x)

private def ThirdHurewicz.normalizationThreeSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    FirstHurewicz.SingularSimplex X 3 → C((unitInterval) × FirstHurewicz.Simplex 3, X) :=
  composeSimplexHomotopies (vertexEdgeThreeSimplexHomotopy x) (triangleThreeSimplexHomotopy x)
    (vertexEdgeThreeSimplexHomotopy_zero x) (triangleThreeSimplexHomotopy_zero x)

@[simp]
private theorem ThirdHurewicz.normalizationThreeSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 3) (s : FirstHurewicz.Simplex 3) :
    normalizationThreeSimplexHomotopy x smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

private theorem ThirdHurewicz.normalizationHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 (normalizationTriangleHomotopy x)
      (normalizationThreeSimplexHomotopy x) :=
  composeSimplexHomotopies_face (vertexEdgeTriangleHomotopy x) (triangleStraighteningHomotopy x)
    (vertexEdgeThreeSimplexHomotopy x) (triangleThreeSimplexHomotopy x)
    (vertexEdgeTriangleHomotopy_zero x) (triangleStraighteningHomotopy_zero x)
    (vertexEdgeThreeSimplexHomotopy_zero x) (triangleThreeSimplexHomotopy_zero x)
    (vertexEdgeHomotopy_face x) (triangleThreeSimplexHomotopy_face x)

@[simp]
private theorem ThirdHurewicz.normalizationTriangleHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    normalizationTriangleHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x :=
  composeSimplexHomotopies_const (vertexEdgeTriangleHomotopy x) (triangleStraighteningHomotopy x)
    (vertexEdgeTriangleHomotopy_zero x) (triangleStraighteningHomotopy_zero x) x
    (vertexEdgeTriangleHomotopy_const x) (triangleStraighteningHomotopy_const x)

@[simp]
private theorem
    ThirdHurewicz.normalizationThreeSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 3) :
    SecondHurewicz.SimplyConnected.timeSlice (normalizationThreeSimplexHomotopy x smp) 1 =
      (normalizedThreeSimplex x smp).val := by
  rw [normalizationThreeSimplexHomotopy, timeSlice_composeSimplexHomotopies_one,
    vertexEdgeThreeSimplexHomotopy_endpoint]
  rfl

private abbrev ThirdHurewicz.CubeTriangulation.SortedCoordinates {α : Type*} [LinearOrder α]
    (u : Fin 3 → α) (e : Equiv.Perm (Fin 3)) : Prop :=
  u (e 2) ≤ u (e 1) ∧ u (e 1) ≤ u (e 0)

private theorem ThirdHurewicz.CubeTriangulation.exists_sortedPermutation {α : Type*} [LinearOrder α]
    (u : Fin 3 → α) : ∃ e : Equiv.Perm (Fin 3), SortedCoordinates u e := by
  rcases le_total (u 0) (u 1) with h01 | h10
  · rcases le_total (u 1) (u 2) with h12 | h21
    · refine ⟨Equiv.swap 0 2, ?_⟩
      simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h01 h12
    · rcases le_total (u 0) (u 2) with h02 | h20
      · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2), ?_⟩
        simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h02 h21
      · refine ⟨Equiv.swap 0 1, ?_⟩
        simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h20 h01
  · rcases le_total (u 0) (u 2) with h02 | h20
    · refine ⟨(Equiv.swap 0 2).trans (Equiv.swap 0 1), ?_⟩
      simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h10 h02
    · rcases le_total (u 1) (u 2) with h12 | h21
      · refine ⟨Equiv.swap 1 2, ?_⟩
        simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h12 h20
      · exact ⟨Equiv.refl (Fin 3), h21, h10⟩

private def ThirdHurewicz.CubeTriangulation.cubeOrderedRegion (e : Equiv.Perm (Fin 3)) :
    Set ThirdHurewicz.Geometry.Cube3 :=
  {u | SortedCoordinates u e}

private theorem ThirdHurewicz.CubeTriangulation.continuous_cubeCoordinate (i : Fin 3) :
    Continuous (fun u : ThirdHurewicz.Geometry.Cube3 => (u i : ℝ)) :=
  continuous_subtype_val.comp (continuous_apply i)

private def ThirdHurewicz.CubeTriangulation.cubeBarycentric (e : Equiv.Perm (Fin 3))
    (u : ThirdHurewicz.Geometry.Cube3) : Fin 4 → ℝ :=
  ![1 - (u (e 0) : ℝ), (u (e 0) : ℝ) - u (e 1), (u (e 1) : ℝ) - u (e 2), (u (e 2) : ℝ)]

private theorem ThirdHurewicz.CubeTriangulation.cubeBarycentric_nonneg (e : Equiv.Perm (Fin 3))
    (u : ThirdHurewicz.Geometry.Cube3) (h : SortedCoordinates u e) (i : Fin 4) :
    0 ≤ cubeBarycentric e u i := by
  fin_cases i
  · exact sub_nonneg.mpr (u (e 0)).property.2
  · exact sub_nonneg.mpr h.2
  · exact sub_nonneg.mpr h.1
  · exact (u (e 2)).property.1

private theorem ThirdHurewicz.CubeTriangulation.cubeBarycentric_sum (e : Equiv.Perm (Fin 3))
    (u : ThirdHurewicz.Geometry.Cube3) : ∑ i, cubeBarycentric e u i = 1 := by
  simp [cubeBarycentric, Fin.sum_univ_succ]

private def ThirdHurewicz.CubeTriangulation.cubeTetrahedronInverse (e : Equiv.Perm (Fin 3)) :
    C(↥(cubeOrderedRegion e), FirstHurewicz.Simplex 3)
    where
  toFun
    u :=
    ⟨cubeBarycentric e u.val,
      ⟨cubeBarycentric_nonneg e u.val u.property, cubeBarycentric_sum e u.val⟩⟩
  continuous_toFun := by
    have hc (i : Fin 3) : Continuous (fun u : ↥(cubeOrderedRegion e) => (u.val i : ℝ)) :=
      (continuous_cubeCoordinate i).comp continuous_subtype_val
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const.sub (hc (e 0))
    · exact (hc (e 0)).sub (hc (e 1))
    · exact (hc (e 1)).sub (hc (e 2))
    · exact hc (e 2)

private theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_sorted (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) :
    SortedCoordinates (ThirdHurewicz.Geometry.cubeTetrahedron e s) e :=
  ⟨ThirdHurewicz.Geometry.cubeTetrahedron_order_second e s,
    ThirdHurewicz.Geometry.cubeTetrahedron_order_first e s⟩

@[simp]
private theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_inverse (e : Equiv.Perm (Fin 3))
    (u : ↥(cubeOrderedRegion e)) :
    ThirdHurewicz.Geometry.cubeTetrahedron e (cubeTetrahedronInverse e u) = u.val := by
  funext k
  obtain ⟨j, rfl⟩ := e.surjective k
  apply Subtype.ext
  fin_cases j
  · change
      (ThirdHurewicz.Geometry.cubeTetrahedron e (cubeTetrahedronInverse e u) (e 0) : ℝ) =
        (u.val (e 0) : ℝ)
    rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero]
    change
      ((u.val (e 0) : ℝ) - u.val (e 1)) + ((u.val (e 1) : ℝ) - u.val (e 2)) + u.val (e 2) =
        (u.val (e 0) : ℝ)
    ring
  · change
      (ThirdHurewicz.Geometry.cubeTetrahedron e (cubeTetrahedronInverse e u) (e 1) : ℝ) =
        (u.val (e 1) : ℝ)
    rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one]
    change ((u.val (e 1) : ℝ) - u.val (e 2)) + u.val (e 2) = (u.val (e 1) : ℝ)
    ring
  · change
      (ThirdHurewicz.Geometry.cubeTetrahedron e (cubeTetrahedronInverse e u) (e 2) : ℝ) =
        (u.val (e 2) : ℝ)
    rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two]
    rfl

@[simp]
private theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedronInverse_tetrahedron
    (e : Equiv.Perm (Fin 3)) (s : FirstHurewicz.Simplex 3) :
    cubeTetrahedronInverse e
        ⟨ThirdHurewicz.Geometry.cubeTetrahedron e s, cubeTetrahedron_sorted e s⟩ =
      s := by
  apply Subtype.ext
  funext i
  change cubeBarycentric e (ThirdHurewicz.Geometry.cubeTetrahedron e s) i = s i
  fin_cases i
  · change 1 - (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 0) : ℝ) = s 0
    rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero]
    have hs := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
    linarith
  · change
      (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 0) : ℝ) -
          ThirdHurewicz.Geometry.cubeTetrahedron e s (e 1) =
        s 1
    rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero,
      ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one]
    ring
  · change
      (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 1) : ℝ) -
          ThirdHurewicz.Geometry.cubeTetrahedron e s (e 2) =
        s 2
    rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one,
      ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two]
    ring
  · change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 2) : ℝ) = s 3
    exact ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two e s

private theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_injective (e : Equiv.Perm (Fin 3)) :
    Function.Injective (ThirdHurewicz.Geometry.cubeTetrahedron e) := by
  intro s t h
  have hh :
    (⟨ThirdHurewicz.Geometry.cubeTetrahedron e s, cubeTetrahedron_sorted e s⟩ :
        ↥(cubeOrderedRegion e)) =
      ⟨ThirdHurewicz.Geometry.cubeTetrahedron e t, cubeTetrahedron_sorted e t⟩ :=
    Subtype.ext h
  simpa only [cubeTetrahedronInverse_tetrahedron] using congrArg (cubeTetrahedronInverse e) hh

private theorem ThirdHurewicz.CubeTriangulation.exists_cubeTetrahedron
    (u : ThirdHurewicz.Geometry.Cube3) :
    ∃ e : Equiv.Perm (Fin 3),
      ∃ s : FirstHurewicz.Simplex 3, ThirdHurewicz.Geometry.cubeTetrahedron e s = u := by
  obtain ⟨e, he⟩ := exists_sortedPermutation u
  exact ⟨e, cubeTetrahedronInverse e ⟨u, he⟩, cubeTetrahedron_inverse e ⟨u, he⟩⟩

private def ThirdHurewicz.CubeTriangulation.cubeTetrahedronCylinder (e : Equiv.Perm (Fin 3)) :
    C((unitInterval) × FirstHurewicz.Simplex 3, (unitInterval) × ThirdHurewicz.Geometry.Cube3) :=
  (ContinuousMap.id (unitInterval)).prodMap (ThirdHurewicz.Geometry.cubeTetrahedron e)

private def ThirdHurewicz.CubeTriangulation.cubeCylinderCover :
    C((Σ _e : Equiv.Perm (Fin 3), (unitInterval) × FirstHurewicz.Simplex 3),
      (unitInterval) × ThirdHurewicz.Geometry.Cube3)
    where
  toFun a := cubeTetrahedronCylinder a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (cubeTetrahedronCylinder e).continuous

private theorem ThirdHurewicz.CubeTriangulation.cubeCylinderCover_surjective :
    Function.Surjective cubeCylinderCover := by
  rintro ⟨r, u⟩
  obtain ⟨e, s, rfl⟩ := exists_cubeTetrahedron u
  exact ⟨⟨e, (r, s)⟩, rfl⟩

private theorem ThirdHurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap :
    Topology.IsQuotientMap cubeCylinderCover :=
  Topology.IsQuotientMap.of_surjective_continuous cubeCylinderCover_surjective
    cubeCylinderCover.continuous

private def ThirdHurewicz.CubeGluing.CubeCompatible {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X)) : Prop :=
  ∀ (e f : Equiv.Perm (Fin 3)) (s t : FirstHurewicz.Simplex 3),
    ThirdHurewicz.Geometry.cubeTetrahedron e s = ThirdHurewicz.Geometry.cubeTetrahedron f t →
      ∀ r : (unitInterval), F e (r, s) = F f (r, t)

private def ThirdHurewicz.CubeGluing.cubeFamilyMap {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X)) :
    C((Σ _e : Equiv.Perm (Fin 3), (unitInterval) × FirstHurewicz.Simplex 3), X)
    where
  toFun a := F a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (F e).continuous

private theorem
    ThirdHurewicz.CubeGluing.cubeFamilyMap_factorsThrough {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hF : CubeCompatible F) :
    Function.FactorsThrough (cubeFamilyMap F) ThirdHurewicz.CubeTriangulation.cubeCylinderCover :=
  by
  rintro ⟨e, r, s⟩ ⟨f, q, t⟩ h
  have hr : r = q := congrArg Prod.fst h
  have hs :
    ThirdHurewicz.Geometry.cubeTetrahedron e s = ThirdHurewicz.Geometry.cubeTetrahedron f t :=
    congrArg Prod.snd h
  subst q
  exact hF e f s t hs r

private def ThirdHurewicz.CubeGluing.glueCubeHomotopies {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hF : CubeCompatible F) : C((unitInterval) × ThirdHurewicz.Geometry.Cube3, X) :=
  ThirdHurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap.lift (cubeFamilyMap F)
    (cubeFamilyMap_factorsThrough F hF)

@[simp]
private theorem ThirdHurewicz.CubeGluing.glueCubeHomotopies_cell {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hF : CubeCompatible F) (e : Equiv.Perm (Fin 3)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex 3) :
    glueCubeHomotopies F hF (r, ThirdHurewicz.Geometry.cubeTetrahedron e s) = F e (r, s) :=
  DFunLike.congr_fun
    (ThirdHurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap.lift_comp (cubeFamilyMap F)
      (cubeFamilyMap_factorsThrough F hF))
    ⟨e, (r, s)⟩

private theorem ThirdHurewicz.CubeGluing.glueCubeHomotopies_time {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hF : CubeCompatible F) (r : (unitInterval)) (g : ThirdHurewicz.Geometry.Cube3 → X)
    (h :
      ∀ (e : Equiv.Perm (Fin 3)) (s : FirstHurewicz.Simplex 3),
        F e (r, s) = g (ThirdHurewicz.Geometry.cubeTetrahedron e s))
    (u : ThirdHurewicz.Geometry.Cube3) : glueCubeHomotopies F hF (r, u) = g u := by
  obtain ⟨e, s, rfl⟩ := ThirdHurewicz.CubeTriangulation.exists_cubeTetrahedron u
  exact (glueCubeHomotopies_cell F hF e r s).trans (h e s)

private theorem ThirdHurewicz.CubeGluing.glueCubeHomotopies_zero {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hF : CubeCompatible F) (g : C(ThirdHurewicz.Geometry.Cube3, X))
    (h :
      ∀ (e : Equiv.Perm (Fin 3)) (s : FirstHurewicz.Simplex 3),
        F e (0, s) = g (ThirdHurewicz.Geometry.cubeTetrahedron e s))
    (u : ThirdHurewicz.Geometry.Cube3) : glueCubeHomotopies F hF (0, u) = g u :=
  glueCubeHomotopies_time F hF 0 g h u

private theorem
    ThirdHurewicz.CubeTriangulation.cubeTetrahedron_mem_boundary_iff (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) :
    ThirdHurewicz.Geometry.cubeTetrahedron e s ∈ Cube.boundary (Fin 3) ↔ s 0 = 0 ∨ s 3 = 0 := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    have h0 := stdSimplex.zero_le s 0
    have h1 := stdSimplex.zero_le s 1
    have h2 := stdSimplex.zero_le s 2
    have h3 := stdSimplex.zero_le s 3
    have hs := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
    fin_cases j
    · rcases hi with hi | hi
      · right
        have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
        change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 0) : ℝ) = 0 at hr
        rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero] at hr
        linarith
      · left
        have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
        change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 0) : ℝ) = 1 at hr
        rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero] at hr
        linarith
    · rcases hi with hi | hi
      · right
        have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
        change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 1) : ℝ) = 0 at hr
        rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one] at hr
        linarith
      · left
        have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
        change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 1) : ℝ) = 1 at hr
        rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one] at hr
        linarith
    · rcases hi with hi | hi
      · right
        have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
        change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 2) : ℝ) = 0 at hr
        rwa [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two] at hr
      · left
        have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
        change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 2) : ℝ) = 1 at hr
        rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two] at hr
        linarith
  · rintro (hs | hs)
    · have ht :=
        ThirdHurewicz.Geometry.cubeTetrahedron_face_zero_boundary e
          (SecondHurewicz.SimplyConnected.simplexFaceInverse 2 0 ⟨s, hs⟩)
      simpa only [SecondHurewicz.SimplyConnected.simplexFace_inverse] using ht
    · have ht :=
        ThirdHurewicz.Geometry.cubeTetrahedron_face_three_boundary e
          (SecondHurewicz.SimplyConnected.simplexFaceInverse 2 3 ⟨s, hs⟩)
      simpa only [SecondHurewicz.SimplyConnected.simplexFace_inverse] using ht

private theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_tie_first (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3)
    (h :
      ThirdHurewicz.Geometry.cubeTetrahedron e s (e 0) =
        ThirdHurewicz.Geometry.cubeTetrahedron e s (e 1)) :
    s 1 = 0 := by
  have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) h
  rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero,
    ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one] at hr
  linarith

private theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_tie_second (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3)
    (h :
      ThirdHurewicz.Geometry.cubeTetrahedron e s (e 1) =
        ThirdHurewicz.Geometry.cubeTetrahedron e s (e 2)) :
    s 2 = 0 := by
  have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) h
  rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one,
    ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two] at hr
  linarith

private theorem
    ThirdHurewicz.CubeGluing.cubeOriginal_face_zero {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)).comp (FirstHurewicz.simplexFace 2 0) =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  ext s
  exact GenLoop.boundary p _ (ThirdHurewicz.Geometry.cubeTetrahedron_face_zero_boundary e s)

private theorem
    ThirdHurewicz.CubeGluing.cubeOriginal_face_three {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)).comp (FirstHurewicz.simplexFace 2 3) =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  ext s
  exact GenLoop.boundary p _ (ThirdHurewicz.Geometry.cubeTetrahedron_face_three_boundary e s)

private theorem ThirdHurewicz.CubeGluing.cubeOriginal_face_one_swap {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)).comp (FirstHurewicz.simplexFace 2 1) =
      (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron ((Equiv.swap 0 1).trans e))).comp
        (FirstHurewicz.simplexFace 2 1) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg (fun f : C(FirstHurewicz.Simplex 2, ThirdHurewicz.Geometry.Cube3) => p.val.comp f)
      (ThirdHurewicz.Geometry.cubeTetrahedron_face_one_swap e)

private theorem ThirdHurewicz.CubeGluing.cubeOriginal_face_two_swap {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)).comp (FirstHurewicz.simplexFace 2 2) =
      (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron ((Equiv.swap 1 2).trans e))).comp
        (FirstHurewicz.simplexFace 2 2) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg (fun f : C(FirstHurewicz.Simplex 2, ThirdHurewicz.Geometry.Cube3) => p.val.comp f)
      (ThirdHurewicz.Geometry.cubeTetrahedron_face_two_swap e)

private theorem
    ThirdHurewicz.CubeGluing.coherentCubeCell_face {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) (i : Fin 4) (r : (unitInterval))
    (s : FirstHurewicz.Simplex 2) :
    H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e))
        (r, FirstHurewicz.simplexFace 2 i s) =
      H₂
        ((p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)).comp
          (FirstHurewicz.simplexFace 2 i))
        (r, s) :=
  DFunLike.congr_fun (hface (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) i) (r, s)

private theorem
    ThirdHurewicz.CubeGluing.coherentCubeCell_one_swap {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex 3) (hs : s 1 = 0) :
    H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) (r, s) =
      H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron ((Equiv.swap 0 1).trans e)))
        (r, s) := by
  let t := SecondHurewicz.SimplyConnected.simplexFaceInverse 2 1 ⟨s, hs⟩
  have ht : FirstHurewicz.simplexFace 2 1 t = s :=
    SecondHurewicz.SimplyConnected.simplexFace_inverse 2 1 ⟨s, hs⟩
  rw [← ht, coherentCubeCell_face H₂ H₃ hface, coherentCubeCell_face H₂ H₃ hface,
    cubeOriginal_face_one_swap]

private theorem
    ThirdHurewicz.CubeGluing.coherentCubeCell_two_swap {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex 3) (hs : s 2 = 0) :
    H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) (r, s) =
      H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron ((Equiv.swap 1 2).trans e)))
        (r, s) := by
  let t := SecondHurewicz.SimplyConnected.simplexFaceInverse 2 2 ⟨s, hs⟩
  have ht : FirstHurewicz.simplexFace 2 2 t = s :=
    SecondHurewicz.SimplyConnected.simplexFace_inverse 2 2 ⟨s, hs⟩
  rw [← ht, coherentCubeCell_face H₂ H₃ hface, coherentCubeCell_face H₂ H₃ hface,
    cubeOriginal_face_two_swap]

private theorem
    ThirdHurewicz.CubeGluing.coherentCubeCell_boundary {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (hconst :
      H₂ (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x)
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex 3)
    (hs : ThirdHurewicz.Geometry.cubeTetrahedron e s ∈ Cube.boundary (Fin 3)) :
    H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) (r, s) = x := by
  rcases (ThirdHurewicz.CubeTriangulation.cubeTetrahedron_mem_boundary_iff e s).mp hs with hs | hs
  · let t := SecondHurewicz.SimplyConnected.simplexFaceInverse 2 0 ⟨s, hs⟩
    have ht : FirstHurewicz.simplexFace 2 0 t = s :=
      SecondHurewicz.SimplyConnected.simplexFace_inverse 2 0 ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₂ H₃ hface, cubeOriginal_face_zero, hconst]
    rfl
  · let t := SecondHurewicz.SimplyConnected.simplexFaceInverse 2 3 ⟨s, hs⟩
    have ht : FirstHurewicz.simplexFace 2 3 t = s :=
      SecondHurewicz.SimplyConnected.simplexFace_inverse 2 3 ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₂ H₃ hface, cubeOriginal_face_three, hconst]
    rfl

private theorem
    ThirdHurewicz.CubeTriangulation.SortedCoordinates.le_first {α : Type*} [LinearOrder α]
    {u : Fin 3 → α} {e : Equiv.Perm (Fin 3)}
    (he : ThirdHurewicz.CubeTriangulation.SortedCoordinates u e) (i : Fin 3) : u i ≤ u (e 0) := by
  obtain ⟨j, rfl⟩ := e.surjective i
  fin_cases j
  · exact le_rfl
  · exact he.2
  · exact he.1.trans he.2

private theorem ThirdHurewicz.CubeTriangulation.sorted_first_value_eq {α : Type*} [LinearOrder α]
    (u : Fin 3 → α) {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e)
    (hf : SortedCoordinates u f) : u (e 0) = u (f 0) :=
  le_antisymm (hf.le_first (e 0)) (he.le_first (f 0))

private theorem ThirdHurewicz.CubeTriangulation.SortedCoordinates.swap01 {α : Type*} [LinearOrder α]
    {u : Fin 3 → α} {e : Equiv.Perm (Fin 3)}
    (he : ThirdHurewicz.CubeTriangulation.SortedCoordinates u e) (ht : u (e 0) = u (e 1)) :
    ThirdHurewicz.CubeTriangulation.SortedCoordinates u ((Equiv.swap 0 1).trans e) := by
  simpa [ThirdHurewicz.CubeTriangulation.SortedCoordinates, Equiv.swap_apply_def] using
    And.intro (he.1.trans he.2) ht.le

private theorem ThirdHurewicz.CubeTriangulation.SortedCoordinates.swap12 {α : Type*} [LinearOrder α]
    {u : Fin 3 → α} {e : Equiv.Perm (Fin 3)}
    (he : ThirdHurewicz.CubeTriangulation.SortedCoordinates u e) (ht : u (e 1) = u (e 2)) :
    ThirdHurewicz.CubeTriangulation.SortedCoordinates u ((Equiv.swap 1 2).trans e) := by
  simpa [ThirdHurewicz.CubeTriangulation.SortedCoordinates, Equiv.swap_apply_def] using
    And.intro ht.le (he.1.trans he.2)

private theorem ThirdHurewicz.CubeTriangulation.permutation_ext_zero_one_mo1973_7620
    {e f : Equiv.Perm (Fin 3)} (h0 : e 0 = f 0) (h1 : e 1 = f 1) : e = f := by
  apply Equiv.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · obtain ⟨j, hj⟩ := f.surjective (e 2)
    fin_cases j
    · exact ((by decide : (0 : Fin 3) ≠ 2) (e.injective (h0.trans hj))).elim
    · exact ((by decide : (1 : Fin 3) ≠ 2) (e.injective (h1.trans hj))).elim
    · exact hj.symm

private theorem ThirdHurewicz.CubeTriangulation.eq_of_sorted_same_first_mo1973_7621 {α : Type*}
    [LinearOrder α] (u : Fin 3 → α) {A : Type*} (F : Equiv.Perm (Fin 3) → A)
    (h12 : ∀ e, SortedCoordinates u e → u (e 1) = u (e 2) → F e = F ((Equiv.swap 1 2).trans e))
    {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e) (hf : SortedCoordinates u f)
    (h0 : e 0 = f 0) : F e = F f := by
  obtain ⟨i, hi⟩ := e.surjective (f 1)
  fin_cases i
  · exact ((by decide : (0 : Fin 3) ≠ 1) (f.injective (h0.symm.trans hi))).elim
  · exact congrArg F (permutation_ext_zero_one_mo1973_7620 h0 hi)
  · have hp : (Equiv.swap 1 2).trans e = f :=
      permutation_ext_zero_one_mo1973_7620 (by simpa [Equiv.swap_apply_def] using h0)
        (by simpa [Equiv.swap_apply_def] using hi)
    have hrev : u (e 1) ≤ u (e 2) := by
      have hh := hf.1
      rw [← hp] at hh
      simpa [Equiv.swap_apply_def] using hh
    exact (h12 e he (le_antisymm hrev he.1)).trans (congrArg F hp)

private theorem ThirdHurewicz.CubeTriangulation.eq_of_sorted_adjacent {α : Type*} [LinearOrder α]
    (u : Fin 3 → α) {A : Type*} (F : Equiv.Perm (Fin 3) → A)
    (h01 : ∀ e, SortedCoordinates u e → u (e 0) = u (e 1) → F e = F ((Equiv.swap 0 1).trans e))
    (h12 : ∀ e, SortedCoordinates u e → u (e 1) = u (e 2) → F e = F ((Equiv.swap 1 2).trans e))
    {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e) (hf : SortedCoordinates u f) :
    F e = F f := by
  obtain ⟨i, hi⟩ := e.surjective (f 0)
  fin_cases i
  · exact eq_of_sorted_same_first_mo1973_7621 u F h12 he hf hi
  · change e 1 = f 0 at hi
    have ht : u (e 0) = u (e 1) := by
      rw [hi]
      exact sorted_first_value_eq u he hf
    have hg := he.swap01 ht
    have hg0 : ((Equiv.swap 0 1).trans e) 0 = f 0 := by simpa [Equiv.swap_apply_def] using hi
    exact (h01 e he ht).trans (eq_of_sorted_same_first_mo1973_7621 u F h12 hg hf hg0)
  · change e 2 = f 0 at hi
    have ht : u (e 0) = u (e 2) := by
      rw [hi]
      exact sorted_first_value_eq u he hf
    have ht12 : u (e 1) = u (e 2) := le_antisymm (he.2.trans ht.le) he.1
    have hg := he.swap12 ht12
    have ht01 : u (((Equiv.swap 1 2).trans e) 0) = u (((Equiv.swap 1 2).trans e) 1) := by
      simpa [Equiv.swap_apply_def] using ht
    have hh := hg.swap01 ht01
    have hh0 : ((Equiv.swap 0 1).trans ((Equiv.swap 1 2).trans e)) 0 = f 0 := by
      simpa [Equiv.swap_apply_def] using hi
    exact
      (h12 e he ht12).trans
        ((h01 _ hg ht01).trans (eq_of_sorted_same_first_mo1973_7621 u F h12 hh hf hh0))

private theorem ThirdHurewicz.CubeTriangulation.sorted_values_eq {α : Type*} [LinearOrder α]
    (u : Fin 3 → α) {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e)
    (hf : SortedCoordinates u f) : ∀ i : Fin 3, u (e i) = u (f i) := by
  have hfun : (fun i => u (e i)) = (fun i => u (f i)) :=
    eq_of_sorted_adjacent u (fun g i => u (g i))
      (fun g _ ht => by
        funext i
        fin_cases i <;> simp [Equiv.swap_apply_def, ht])
      (fun g _ ht => by
        funext i
        fin_cases i <;> simp [Equiv.swap_apply_def, ht])
      he hf
  exact congrFun hfun

private theorem ThirdHurewicz.CubeTriangulation.cubeBarycentric_eq_of_sorted
    (u : ThirdHurewicz.Geometry.Cube3) {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e)
    (hf : SortedCoordinates u f) : cubeBarycentric e u = cubeBarycentric f u := by
  simp only [cubeBarycentric, sorted_values_eq u he hf 0, sorted_values_eq u he hf 1,
    sorted_values_eq u he hf 2]

private theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedronInverse_sorted_eq
    (u : ThirdHurewicz.Geometry.Cube3) {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e)
    (hf : SortedCoordinates u f) :
    cubeTetrahedronInverse e ⟨u, he⟩ = cubeTetrahedronInverse f ⟨u, hf⟩ :=
  Subtype.ext (cubeBarycentric_eq_of_sorted u he hf)

private theorem
    ThirdHurewicz.CubeTriangulation.cubeTetrahedron_eq_of_sorted (e f : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3)
    (hf : SortedCoordinates (ThirdHurewicz.Geometry.cubeTetrahedron e s) f) :
    ThirdHurewicz.Geometry.cubeTetrahedron f s = ThirdHurewicz.Geometry.cubeTetrahedron e s := by
  have hp : cubeTetrahedronInverse f ⟨ThirdHurewicz.Geometry.cubeTetrahedron e s, hf⟩ = s :=
    (cubeTetrahedronInverse_sorted_eq (ThirdHurewicz.Geometry.cubeTetrahedron e s) hf
          (cubeTetrahedron_sorted e s)).trans
      (cubeTetrahedronInverse_tetrahedron e s)
  simpa only [hp] using cubeTetrahedron_inverse f ⟨ThirdHurewicz.Geometry.cubeTetrahedron e s, hf⟩

private theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_overlap_preimage
    (e f : Equiv.Perm (Fin 3)) (s t : FirstHurewicz.Simplex 3)
    (h :
      ThirdHurewicz.Geometry.cubeTetrahedron e s = ThirdHurewicz.Geometry.cubeTetrahedron f t) :
    s = t := by
  have hf : SortedCoordinates (ThirdHurewicz.Geometry.cubeTetrahedron e s) f := by
    rw [h]
    exact cubeTetrahedron_sorted f t
  exact cubeTetrahedron_injective f ((cubeTetrahedron_eq_of_sorted e f s hf).trans h)

private theorem
    ThirdHurewicz.CubeGluing.coherentCubeFamily_compatible {X : Type} [TopologicalSpace X]
    {x : X} (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (p : GenLoop (Fin 3) X x) :
    CubeCompatible (fun e => H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e))) := by
  intro e f s t h r
  have hst := ThirdHurewicz.CubeTriangulation.cubeTetrahedron_overlap_preimage e f s t h
  subst t
  have hf :
    ThirdHurewicz.CubeTriangulation.SortedCoordinates (ThirdHurewicz.Geometry.cubeTetrahedron e s)
      f := by
    rw [h]
    exact ThirdHurewicz.CubeTriangulation.cubeTetrahedron_sorted f s
  apply
    ThirdHurewicz.CubeTriangulation.eq_of_sorted_adjacent
      (ThirdHurewicz.Geometry.cubeTetrahedron e s)
      (fun g => H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron g)) (r, s)) ?_ ?_
      (ThirdHurewicz.CubeTriangulation.cubeTetrahedron_sorted e s) hf
  · intro g hg ht
    apply coherentCubeCell_one_swap H₂ H₃ hface p g r s
    apply ThirdHurewicz.CubeTriangulation.cubeTetrahedron_tie_first g s
    simpa only [ThirdHurewicz.CubeTriangulation.cubeTetrahedron_eq_of_sorted e g s hg] using ht
  · intro g hg ht
    apply coherentCubeCell_two_swap H₂ H₃ hface p g r s
    apply ThirdHurewicz.CubeTriangulation.cubeTetrahedron_tie_second g s
    simpa only [ThirdHurewicz.CubeTriangulation.cubeTetrahedron_eq_of_sorted e g s hg] using ht

private def ThirdHurewicz.CubeGluing.coherentCubeHomotopyMap {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (p : GenLoop (Fin 3) X x) : C((unitInterval) × ThirdHurewicz.Geometry.Cube3, X) :=
  glueCubeHomotopies (fun e => H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)))
    (coherentCubeFamily_compatible H₂ H₃ hface p)

@[simp]
private theorem
    ThirdHurewicz.CubeGluing.coherentCubeHomotopyMap_cell {X : Type} [TopologicalSpace X]
    {x : X} (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex 3) :
    coherentCubeHomotopyMap H₂ H₃ hface p (r, ThirdHurewicz.Geometry.cubeTetrahedron e s) =
      H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) (r, s) :=
  glueCubeHomotopies_cell _ _ e r s

private theorem
    ThirdHurewicz.CubeGluing.coherentCubeHomotopyMap_zero {X : Type} [TopologicalSpace X]
    {x : X} (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (hzero :
      ∀ (smp : C(FirstHurewicz.Simplex 3, X)) (s : FirstHurewicz.Simplex 3),
        H₃ smp (0, s) = smp s)
    (p : GenLoop (Fin 3) X x) (u : ThirdHurewicz.Geometry.Cube3) :
    coherentCubeHomotopyMap H₂ H₃ hface p (0, u) = p u :=
  glueCubeHomotopies_zero _ _ p.val
    (fun e s => hzero (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) s) u

private theorem
    ThirdHurewicz.CubeGluing.coherentCubeHomotopyMap_boundary {X : Type} [TopologicalSpace X]
    {x : X} (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (hconst :
      H₂ (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x)
    (p : GenLoop (Fin 3) X x) (r : (unitInterval)) (u : ThirdHurewicz.Geometry.Cube3)
    (hu : u ∈ Cube.boundary (Fin 3)) : coherentCubeHomotopyMap H₂ H₃ hface p (r, u) = x := by
  obtain ⟨e, s, rfl⟩ := ThirdHurewicz.CubeTriangulation.exists_cubeTetrahedron u
  rw [coherentCubeHomotopyMap_cell]
  exact coherentCubeCell_boundary H₂ H₃ hface hconst p e r s hu

private def ThirdHurewicz.CubeGluing.coherentCubeEndpoint {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (hconst :
      H₂ (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x)
    (p : GenLoop (Fin 3) X x) : GenLoop (Fin 3) X x :=
  ⟨SecondHurewicz.SimplyConnected.timeSlice (coherentCubeHomotopyMap H₂ H₃ hface p) 1, fun u hu =>
    coherentCubeHomotopyMap_boundary H₂ H₃ hface hconst p 1 u hu⟩

private theorem
    ThirdHurewicz.CubeGluing.coherentCubeEndpoint_cell {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (hconst :
      H₂ (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x)
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (coherentCubeEndpoint H₂ H₃ hface hconst p).val.comp
        (ThirdHurewicz.Geometry.cubeTetrahedron e) =
      SecondHurewicz.SimplyConnected.timeSlice
        (H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e))) 1 := by
  ext s
  exact coherentCubeHomotopyMap_cell H₂ H₃ hface p e 1 s

private def ThirdHurewicz.CubeGluing.coherentCubeHomotopy {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (hconst :
      H₂ (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x)
    (hzero :
      ∀ (smp : C(FirstHurewicz.Simplex 3, X)) (s : FirstHurewicz.Simplex 3),
        H₃ smp (0, s) = smp s)
    (p : GenLoop (Fin 3) X x) :
    p.val.HomotopyRel (coherentCubeEndpoint H₂ H₃ hface hconst p).val (Cube.boundary (Fin 3))
    where
  toHomotopy :=
    { toContinuousMap := coherentCubeHomotopyMap H₂ H₃ hface p
      map_zero_left := coherentCubeHomotopyMap_zero H₂ H₃ hface hzero p
      map_one_left _ := rfl }
  prop' r u
    hu :=
    (coherentCubeHomotopyMap_boundary H₂ H₃ hface hconst p r u hu).trans
      (GenLoop.boundary p u hu).symm

private theorem ThirdHurewicz.cubeTetrahedron_coordinate_equality_boundary (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) (i j : Fin 3) (hij : i ≠ j)
    (hu : Geometry.cubeTetrahedron e s i = Geometry.cubeTetrahedron e s j) :
    s ∈ threeSimplexBoundary := by
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  have hab : a ≠ b := fun h => hij (congrArg e h)
  have hcoords :
    (fun k : Fin 3 => (Geometry.cubeTetrahedron e s (e k) : ℝ)) =
      ![s 1 + s 2 + s 3, s 2 + s 3, s 3] := by
    funext k
    fin_cases k
    · exact Geometry.cubeTetrahedron_coordinate_zero e s
    · exact Geometry.cubeTetrahedron_coordinate_one e s
    · exact Geometry.cubeTetrahedron_coordinate_two e s
  have hv := congrArg (fun t : (unitInterval) => (t : ℝ)) hu
  change
    (fun k : Fin 3 => (Geometry.cubeTetrahedron e s (e k) : ℝ)) a =
      (fun k : Fin 3 => (Geometry.cubeTetrahedron e s (e k) : ℝ)) b at hv
  rw [hcoords] at hv
  fin_cases a <;> fin_cases b
  all_goals try exact (hab rfl).elim
  all_goals
    dsimp at hv
    first
    | exact ⟨1, by linarith [stdSimplex.zero_le s 1, stdSimplex.zero_le s 2]⟩
    | exact ⟨2, by linarith [stdSimplex.zero_le s 1, stdSimplex.zero_le s 2]⟩

private def
    ThirdHurewicz.normalizedCube {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) : GenLoop (Fin 3) X x :=
  CubeGluing.coherentCubeEndpoint (normalizationTriangleHomotopy x)
    (normalizationThreeSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationTriangleHomotopy_const x) p

private theorem
    ThirdHurewicz.normalizedCube_cell {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (normalizedCube x p).val.comp (Geometry.cubeTetrahedron e) =
      (normalizedThreeSimplex x (p.val.comp (Geometry.cubeTetrahedron e))).val := by
  exact
    (CubeGluing.coherentCubeEndpoint_cell (normalizationTriangleHomotopy x)
          (normalizationThreeSimplexHomotopy x) (normalizationHomotopy_face x)
          (normalizationTriangleHomotopy_const x) p e).trans
      (normalizationThreeSimplexHomotopy_endpoint x _)

private def ThirdHurewicz.normalizationCubeHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) :
    p.val.HomotopyRel (normalizedCube x p).val (Cube.boundary (Fin 3)) :=
  CubeGluing.coherentCubeHomotopy (normalizationTriangleHomotopy x)
    (normalizationThreeSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationTriangleHomotopy_const x) (normalizationThreeSimplexHomotopy_zero x) p

private theorem ThirdHurewicz.normalizedCube_cell_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x)
    (e : Equiv.Perm (Fin 3)) (s : FirstHurewicz.Simplex 3) (hs : s ∈ threeSimplexBoundary) :
    normalizedCube x p (Geometry.cubeTetrahedron e s) = x := by
  have h := congrArg (fun f : C(FirstHurewicz.Simplex 3, X) => f s) (normalizedCube_cell x p e)
  exact
    h.trans ((normalizedThreeSimplex x (p.val.comp (Geometry.cubeTetrahedron e))).property s hs)

private theorem ThirdHurewicz.normalizedCube_internalBased {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) :
    NativeCubeInternalBased (normalizedCube x p) := by
  intro u i j hij hu
  obtain ⟨e, s, rfl⟩ := CubeTriangulation.exists_cubeTetrahedron u
  exact
    normalizedCube_cell_boundary x p e s
      (cubeTetrahedron_coordinate_equality_boundary e s i j hij hu)

private theorem
    ThirdHurewicz.threeSimplexClassOperator_cubeChain_sum {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) :
    threeSimplexClassOperator x (cubeChain p) =
      ∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e •
          basedThreeSimplexClass
            (normalizedThreeSimplex x (p.val.comp (Geometry.cubeTetrahedron e))) := by
  rw [CubeSubdivision.cubeChain_eq_sum_tetrahedra]
  simp only [map_sum, map_zsmul, threeSimplexClassOperator_simplex]

private theorem ThirdHurewicz.normalizedCube_tetrahedron {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x)
    (e : Equiv.Perm (Fin 3)) :
    nativeBasedCubeTetrahedron (normalizedCube x p) (normalizedCube_internalBased x p) e =
      normalizedThreeSimplex x (p.val.comp (Geometry.cubeTetrahedron e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x p e

private theorem ThirdHurewicz.threeSimplexClassOperator_cubeChain {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) :
    threeSimplexClassOperator x (cubeChain p) = Additive.ofMul (⟦p⟧ : π_ 3 X x) := by
  have h :=
    nativeCubeSubdivision_homotopy_class p (normalizedCube x p) (normalizationCubeHomotopy x p)
      (normalizedCube_internalBased x p)
  simp only [normalizedCube_tetrahedron] at h
  exact (threeSimplexClassOperator_cubeChain_sum x p).trans h.symm

private def
    ThirdHurewicz.hurewiczInverse {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    SingularMayerVietoris.SingularHomology X 3 →ₗ[ℤ] Additive (π_ 3 X x) :=
  thirdHomologyDesc (threeSimplexClassOperator x) (threeSimplexClassOperator_boundary x)

@[simp]
private theorem ThirdHurewicz.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    hurewiczInverse x
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c) =
      threeSimplexClassOperator x c.val :=
  thirdHomologyDesc_cycleClass _ _ c

private theorem ThirdHurewicz.hurewiczMap_comp_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    (hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  comp_thirdHomologyDesc_eq_id (threeSimplexClassOperator x)
    (threeSimplexClassOperator_boundary x) (hurewiczMap x)
    (hurewiczMap_threeSimplexClassOperator_cycle x)

@[simp]
private theorem ThirdHurewicz.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.SingularHomology X 3) : hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

private theorem ThirdHurewicz.hurewiczInverse_hurewiczMap_mk {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) :
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 3 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 3 X x) := by
  rw [hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact threeSimplexClassOperator_cubeChain x p

@[simp]
private theorem ThirdHurewicz.hurewiczInverse_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (a : Additive (π_ 3 X x)) :
    hurewiczInverse x (hurewiczMap x a) = a := by
  change
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
      Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

private theorem ThirdHurewicz.hurewiczInverse_comp_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    (hurewiczInverse x).comp (hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a


private def ThirdHurewicz.hurewiczPi3Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] :
    π_ 3 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 3)
    where
  __ := hurewiczPi3 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv
    c := congrArg Multiplicative.ofAdd (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))

@[simp]
private theorem FourthHurewicz.lowerThreeSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    ThirdHurewicz.normalizationThreeSimplexHomotopy x
        (ContinuousMap.const (FirstHurewicz.Simplex 3) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 3) x := by
  have hVE :
    ThirdHurewicz.vertexEdgeThreeSimplexHomotopy x
        (ContinuousMap.const (FirstHurewicz.Simplex 3) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 3) x :=
    ThirdHurewicz.composeSimplexHomotopies_const
      (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 3)
      (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
      (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero x 3)
      (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero x) x
      (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_const x 3)
      (ThirdHurewicz.edgeTetrahedronHomotopy_const x)
  exact
    ThirdHurewicz.composeSimplexHomotopies_const (ThirdHurewicz.vertexEdgeThreeSimplexHomotopy x)
      (ThirdHurewicz.triangleThreeSimplexHomotopy x)
      (ThirdHurewicz.vertexEdgeThreeSimplexHomotopy_zero x)
      (ThirdHurewicz.triangleThreeSimplexHomotopy_zero x) x hVE
      (ThirdHurewicz.triangleThreeSimplexHomotopy_const x)

private def FourthHurewicz.lowerFourSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) : C((unitInterval) × FirstHurewicz.Simplex 4, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (ThirdHurewicz.normalizationTriangleHomotopy x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (ThirdHurewicz.normalizationHomotopy_face x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x) smp

@[simp]
private theorem FourthHurewicz.lowerFourSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) (s : FirstHurewicz.Simplex 4) :
    lowerFourSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

private theorem FourthHurewicz.lowerFourSimplexHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 3
      (ThirdHurewicz.normalizationThreeSimplexHomotopy x) (lowerFourSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (ThirdHurewicz.normalizationTriangleHomotopy x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (ThirdHurewicz.normalizationHomotopy_face x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x)

@[simp]
private theorem FourthHurewicz.lowerFourSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    lowerFourSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 4) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 4) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (ThirdHurewicz.normalizationTriangleHomotopy x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (ThirdHurewicz.normalizationHomotopy_face x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x) x (lowerThreeSimplexHomotopy_const x)

private def FourthHurewicz.lowerFiveSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) : C((unitInterval) × FirstHurewicz.Simplex 5, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x) (lowerFourSimplexHomotopy x)
    (lowerFourSimplexHomotopy_face x) (lowerFourSimplexHomotopy_zero x) smp

@[simp]
private theorem FourthHurewicz.lowerFiveSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) (s : FirstHurewicz.Simplex 5) :
    lowerFiveSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

private theorem FourthHurewicz.lowerFiveSimplexHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 4 (lowerFourSimplexHomotopy x)
      (lowerFiveSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x) (lowerFourSimplexHomotopy x)
    (lowerFourSimplexHomotopy_face x) (lowerFourSimplexHomotopy_zero x)

@[simp]
private theorem FourthHurewicz.lowerFiveSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    lowerFiveSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 5) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 5) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x) (lowerFourSimplexHomotopy x)
    (lowerFourSimplexHomotopy_face x) (lowerFourSimplexHomotopy_zero x) x
    (lowerFourSimplexHomotopy_const x)

private def HigherHurewicz.nativeCubeNullHomotopy {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    [hπ : Subsingleton (π_ n X x)] (p : GenLoop (Fin n) X x) :
    p.val.HomotopyRel (ContinuousMap.const (Fin n → (unitInterval)) x) (Cube.boundary (Fin n)) :=
  Classical.choice
    (show GenLoop.Homotopic p GenLoop.const from
      Quotient.exact (@Subsingleton.elim (π_ n X x) hπ ⟦p⟧ ⟦GenLoop.const⟧))

private def
    HigherHurewicz.nativeCubeNullHomotopy_comp {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    {A : Type*} [TopologicalSpace A] [Subsingleton (π_ n X x)] (p : GenLoop (Fin n) X x)
    (r : C(A, Fin n → (unitInterval))) (S : Set A) (hr : Set.MapsTo r S (Cube.boundary (Fin n))) :
    (p.val.comp r).HomotopyRel (ContinuousMap.const A x) S
    where
  toFun z := nativeCubeNullHomotopy p (z.1, r z.2)
  continuous_toFun :=
    (nativeCubeNullHomotopy p).continuous.comp
      (continuous_fst.prodMk (r.continuous.comp continuous_snd))
  map_zero_left a := (nativeCubeNullHomotopy p).apply_zero (r a)
  map_one_left a := (nativeCubeNullHomotopy p).apply_one (r a)
  prop' t _ ha := (nativeCubeNullHomotopy p).eq_fst t (hr ha)

private def HigherHurewicz.basedSimplexNativeLoop {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSimplex n x) : GenLoop (Fin n) X x :=
  ⟨τ.val.comp ⟨(simplexCubeHomeomorph n).symm, (simplexCubeHomeomorph n).symm.continuous⟩,
    fun u hu => τ.property _ ((simplexCubeHomeomorph_symm_boundary_iff n u).mpr hu)⟩

private theorem HigherHurewicz.basedSimplexNativeLoop_comp_homeomorph {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedSimplex n x) :
    (basedSimplexNativeLoop τ).val.comp
        ⟨simplexCubeHomeomorph n, (simplexCubeHomeomorph n).continuous⟩ =
      τ.val := by
  apply ContinuousMap.ext
  intro s
  change τ.val ((simplexCubeHomeomorph n).symm (simplexCubeHomeomorph n s)) = τ.val s
  rw [Homeomorph.symm_apply_apply]

private def
    HigherHurewicz.simplexNullHomotopyUnnormalized {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) :
    τ.val.HomotopyRel (ContinuousMap.const (FirstHurewicz.Simplex n) x)
      (SecondHurewicz.SimplyConnected.simplexBoundary n) :=
  ContinuousMap.HomotopyRel.cast
    (nativeCubeNullHomotopy_comp (basedSimplexNativeLoop τ)
      ⟨simplexCubeHomeomorph n, (simplexCubeHomeomorph n).continuous⟩
      (SecondHurewicz.SimplyConnected.simplexBoundary n)
      (fun s hs => (simplexCubeHomeomorph_boundary_iff n s).mpr hs))
    (basedSimplexNativeLoop_comp_homeomorph τ) rfl

private def HigherHurewicz.simplexNullHomotopy {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) :
    τ.val.HomotopyRel (ContinuousMap.const (FirstHurewicz.Simplex n) x)
      (SecondHurewicz.SimplyConnected.simplexBoundary n) := by
  classical
    exact
    if h : τ = constantBasedSimplex n x then
      ContinuousMap.HomotopyRel.cast
        (ContinuousMap.HomotopyRel.refl (ContinuousMap.const (FirstHurewicz.Simplex n) x)
          (SecondHurewicz.SimplyConnected.simplexBoundary n))
        (congrArg (fun υ : BasedSimplex n x => υ.val) h).symm rfl
    else simplexNullHomotopyUnnormalized τ

private theorem
    HigherHurewicz.simplexNullHomotopy_zero {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) (s : FirstHurewicz.Simplex n) :
    simplexNullHomotopy τ (0, s) = τ.val s :=
  (simplexNullHomotopy τ).apply_zero s

private theorem
    HigherHurewicz.simplexNullHomotopy_one {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) (s : FirstHurewicz.Simplex n) :
    simplexNullHomotopy τ (1, s) = x :=
  (simplexNullHomotopy τ).apply_one s

@[simp]
private theorem HigherHurewicz.simplexNullHomotopy_constant {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] :
    simplexNullHomotopy (constantBasedSimplex n x) =
      ContinuousMap.HomotopyRel.refl (ContinuousMap.const (FirstHurewicz.Simplex n) x)
        (SecondHurewicz.SimplyConnected.simplexBoundary n) := by
  classical
  unfold simplexNullHomotopy
  rw [dite_eq_left rfl]
  rfl

private theorem HigherHurewicz.simplexNullHomotopy_constant_toContinuousMap {X : Type}
    [TopologicalSpace X] (n : ℕ) (x : X) [Subsingleton (π_ n X x)] :
    (simplexNullHomotopy (constantBasedSimplex n x)).toContinuousMap =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x := by
  rw [simplexNullHomotopy_constant]
  rfl

private def
    HigherHurewicz.simplexStraighteningHomotopy {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    [Subsingleton (π_ n X x)] (smp : FirstHurewicz.SingularSimplex X n) :
    C((unitInterval) × FirstHurewicz.Simplex n, X) := by
  classical
    exact
    if h : ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n, smp s = x then
      (simplexNullHomotopy (⟨smp, h⟩ : BasedSimplex n x)).toContinuousMap
    else SecondHurewicz.SimplyConnected.stationarySimplexHomotopy n smp

@[simp]
private theorem
    HigherHurewicz.simplexStraighteningHomotopy_zero {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] (smp : FirstHurewicz.SingularSimplex X n)
    (s : FirstHurewicz.Simplex n) : simplexStraighteningHomotopy n x smp (0, s) = smp s := by
  classical
  unfold simplexStraighteningHomotopy
  split
  · rename_i h
    exact simplexNullHomotopy_zero (⟨smp, h⟩ : BasedSimplex n x) s
  · rfl

private theorem
    HigherHurewicz.simplexStraighteningHomotopy_one {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] (smp : FirstHurewicz.SingularSimplex X n)
    (h : ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n, smp s = x)
    (s : FirstHurewicz.Simplex n) : simplexStraighteningHomotopy n x smp (1, s) = x := by
  classical
  rw [simplexStraighteningHomotopy, dite_eq_left h]
  exact simplexNullHomotopy_one (⟨smp, h⟩ : BasedSimplex n x) s

private theorem HigherHurewicz.simplexStraighteningHomotopy_boundary {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X) [Subsingleton (π_ n X x)] (smp : FirstHurewicz.SingularSimplex X n)
    (r : (unitInterval)) (s : FirstHurewicz.Simplex n)
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n) :
    simplexStraighteningHomotopy n x smp (r, s) = smp s := by
  classical
  unfold simplexStraighteningHomotopy
  split
  · rename_i h
    exact (simplexNullHomotopy (⟨smp, h⟩ : BasedSimplex n x)).eq_fst r hs
  · rfl

@[simp]
private theorem
    HigherHurewicz.simplexStraighteningHomotopy_const {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] :
    simplexStraighteningHomotopy n x (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x := by
  classical
  have h :
    ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n,
      (ContinuousMap.const (FirstHurewicz.Simplex n) x) s = x :=
    fun _ _ => rfl
  rw [simplexStraighteningHomotopy, dite_eq_left h]
  exact simplexNullHomotopy_constant_toContinuousMap n x

private theorem
    HigherHurewicz.simplexStraighteningHomotopy_face {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ (n + 1) X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n
      (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy n)
      (simplexStraighteningHomotopy (n + 1) x) := by
  intro smp i
  ext u
  change
    simplexStraighteningHomotopy (n + 1) x smp (u.1, FirstHurewicz.simplexFace n i u.2) =
      smp (FirstHurewicz.simplexFace n i u.2)
  exact
    simplexStraighteningHomotopy_boundary (n + 1) x smp u.1 _
      ⟨i, FirstHurewicz.simplexFace_apply_self n i u.2⟩

private def FourthHurewicz.threeFourSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] (smp : FirstHurewicz.SingularSimplex X 4) :
    C((unitInterval) × FirstHurewicz.Simplex 4, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 2)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 2 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x) smp

@[simp]
private theorem FourthHurewicz.threeFourSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] (smp : FirstHurewicz.SingularSimplex X 4)
    (s : FirstHurewicz.Simplex 4) : threeFourSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

private theorem FourthHurewicz.threeFourSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 3
      (HigherHurewicz.simplexStraighteningHomotopy 3 x) (threeFourSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 2)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 2 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x)

@[simp]
private theorem
    FourthHurewicz.threeFourSimplexHomotopy_const {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] :
    threeFourSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 4) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 4) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 2)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 2 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x) x
    (HigherHurewicz.simplexStraighteningHomotopy_const 3 x)

private def FourthHurewicz.threeFiveSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] (smp : FirstHurewicz.SingularSimplex X 5) :
    C((unitInterval) × FirstHurewicz.Simplex 5, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (HigherHurewicz.simplexStraighteningHomotopy 3 x) (threeFourSimplexHomotopy x)
    (threeFourSimplexHomotopy_face x) (threeFourSimplexHomotopy_zero x) smp

@[simp]
private theorem FourthHurewicz.threeFiveSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] (smp : FirstHurewicz.SingularSimplex X 5)
    (s : FirstHurewicz.Simplex 5) : threeFiveSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

private theorem FourthHurewicz.threeFiveSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 4 (threeFourSimplexHomotopy x)
      (threeFiveSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (HigherHurewicz.simplexStraighteningHomotopy 3 x) (threeFourSimplexHomotopy x)
    (threeFourSimplexHomotopy_face x) (threeFourSimplexHomotopy_zero x)

@[simp]
private theorem
    FourthHurewicz.threeFiveSimplexHomotopy_const {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] :
    threeFiveSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 5) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 5) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (HigherHurewicz.simplexStraighteningHomotopy 3 x) (threeFourSimplexHomotopy x)
    (threeFourSimplexHomotopy_face x) (threeFourSimplexHomotopy_zero x) x
    (threeFourSimplexHomotopy_const x)

private def FourthHurewicz.normalizationThreeSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    FirstHurewicz.SingularSimplex X 3 → C((unitInterval) × FirstHurewicz.Simplex 3, X) :=
  ThirdHurewicz.composeSimplexHomotopies (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x)

private def FourthHurewicz.normalizationFourSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    FirstHurewicz.SingularSimplex X 4 → C((unitInterval) × FirstHurewicz.Simplex 4, X) :=
  ThirdHurewicz.composeSimplexHomotopies (lowerFourSimplexHomotopy x) (threeFourSimplexHomotopy x)
    (lowerFourSimplexHomotopy_zero x) (threeFourSimplexHomotopy_zero x)

private def FourthHurewicz.normalizationFiveSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    FirstHurewicz.SingularSimplex X 5 → C((unitInterval) × FirstHurewicz.Simplex 5, X) :=
  ThirdHurewicz.composeSimplexHomotopies (lowerFiveSimplexHomotopy x) (threeFiveSimplexHomotopy x)
    (lowerFiveSimplexHomotopy_zero x) (threeFiveSimplexHomotopy_zero x)

@[simp]
private theorem FourthHurewicz.normalizationFourSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) (s : FirstHurewicz.Simplex 4) :
    normalizationFourSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp]
private theorem FourthHurewicz.normalizationFiveSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) (s : FirstHurewicz.Simplex 5) :
    normalizationFiveSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

private theorem FourthHurewicz.normalizationHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 3
      (normalizationThreeSimplexHomotopy x) (normalizationFourSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x) (lowerFourSimplexHomotopy x)
    (threeFourSimplexHomotopy x) (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x) (lowerFourSimplexHomotopy_zero x)
    (threeFourSimplexHomotopy_zero x) (lowerFourSimplexHomotopy_face x)
    (threeFourSimplexHomotopy_face x)

private theorem FourthHurewicz.normalizationFiveHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 4 (normalizationFourSimplexHomotopy x)
      (normalizationFiveSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face (lowerFourSimplexHomotopy x)
    (threeFourSimplexHomotopy x) (lowerFiveSimplexHomotopy x) (threeFiveSimplexHomotopy x)
    (lowerFourSimplexHomotopy_zero x) (threeFourSimplexHomotopy_zero x)
    (lowerFiveSimplexHomotopy_zero x) (threeFiveSimplexHomotopy_zero x)
    (lowerFiveSimplexHomotopy_face x) (threeFiveSimplexHomotopy_face x)

@[simp]
private theorem
    FourthHurewicz.normalizationThreeSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    normalizationThreeSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 3) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 3) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x) x (lowerThreeSimplexHomotopy_const x)
    (HigherHurewicz.simplexStraighteningHomotopy_const 3 x)

@[simp]
private theorem
    FourthHurewicz.normalizationFourSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    normalizationFourSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 4) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 4) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (lowerFourSimplexHomotopy x)
    (threeFourSimplexHomotopy x) (lowerFourSimplexHomotopy_zero x)
    (threeFourSimplexHomotopy_zero x) x (lowerFourSimplexHomotopy_const x)
    (threeFourSimplexHomotopy_const x)

@[simp]
private theorem
    FourthHurewicz.normalizationFiveSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    normalizationFiveSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 5) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 5) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (lowerFiveSimplexHomotopy x)
    (threeFiveSimplexHomotopy x) (lowerFiveSimplexHomotopy_zero x)
    (threeFiveSimplexHomotopy_zero x) x (lowerFiveSimplexHomotopy_const x)
    (threeFiveSimplexHomotopy_const x)

@[simp]
private theorem
    FourthHurewicz.normalizationThreeSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 3) :
    SecondHurewicz.SimplyConnected.timeSlice (normalizationThreeSimplexHomotopy x smp) 1 =
      ContinuousMap.const (FirstHurewicz.Simplex 3) x := by
  rw [normalizationThreeSimplexHomotopy, ThirdHurewicz.timeSlice_composeSimplexHomotopies_one,
    ThirdHurewicz.normalizationThreeSimplexHomotopy_endpoint]
  ext s
  exact
    HigherHurewicz.simplexStraighteningHomotopy_one 3 x
      (ThirdHurewicz.normalizedThreeSimplex x smp).val
      (ThirdHurewicz.normalizedThreeSimplex x smp).property s

private def
    HigherHurewicz.SimplexGeometry.prefixMinimum {n : ℕ} (u : Fin n → (unitInterval)) (k : ℕ) :
    (unitInterval) :=
  (Finset.univ.filter fun i : Fin n => i.val < k).inf u

@[simp]
private theorem
    HigherHurewicz.SimplexGeometry.prefixMinimum_zero {n : ℕ} (u : Fin n → (unitInterval)) :
    prefixMinimum u 0 = 1 := by
  simp [prefixMinimum]
  rfl

private theorem HigherHurewicz.SimplexGeometry.prefixMinimum_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) : Antitone (prefixMinimum u) := by
  intro k l hkl
  apply Finset.inf_mono
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans_le hkl

private theorem HigherHurewicz.SimplexGeometry.prefixMinimum_le_coordinate {n : ℕ}
    (u : Fin n → (unitInterval)) (k : ℕ) (i : Fin n) (hi : i.val < k) : prefixMinimum u k ≤ u i :=
  Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

private theorem
    HigherHurewicz.SimplexGeometry.prefixMinimum_succ {n : ℕ} (u : Fin n → (unitInterval))
    (k : ℕ) (hk : k < n) : prefixMinimum u (k + 1) = Min.min (prefixMinimum u k) (u ⟨k, hk⟩) := by
  have hs :
    (Finset.univ.filter fun i : Fin n => i.val < k + 1) =
      Insert.insert ⟨k, hk⟩ (Finset.univ.filter fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold prefixMinimum
  rw [hs, Finset.inf_insert]
  exact min_comm _ _

private theorem HigherHurewicz.SimplexGeometry.continuous_prefixMinimum (n k : ℕ) :
    Continuous (fun u : Fin n → (unitInterval) => prefixMinimum u k) :=
  Continuous.finset_inf_apply (fun i _ => continuous_apply i)

private def
    HigherHurewicz.SimplexGeometry.extendedMinimum {n : ℕ} (u : Fin n → (unitInterval)) (k : ℕ) :
    (unitInterval) :=
  if k ≤ n then prefixMinimum u k else 0

private theorem
    HigherHurewicz.SimplexGeometry.extendedMinimum_of_le {n : ℕ} (u : Fin n → (unitInterval))
    (k : ℕ) (hk : k ≤ n) : extendedMinimum u k = prefixMinimum u k :=
  ite_eq_left hk

@[simp]
private theorem
    HigherHurewicz.SimplexGeometry.extendedMinimum_zero {n : ℕ} (u : Fin n → (unitInterval)) :
    extendedMinimum u 0 = 1 := by simp [extendedMinimum]

@[simp]
private theorem HigherHurewicz.SimplexGeometry.extendedMinimum_last_succ {n : ℕ}
    (u : Fin n → (unitInterval)) : extendedMinimum u (n + 1) = 0 := by simp [extendedMinimum]

private theorem HigherHurewicz.SimplexGeometry.extendedMinimum_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) : Antitone (extendedMinimum u) := by
  intro k l hkl
  by_cases hl : l ≤ n
  · have hk := hkl.trans hl
    simpa only [extendedMinimum, ite_eq_left hk, ite_eq_left hl] using prefixMinimum_antitone u hkl
  · rw [show extendedMinimum u l = 0 from ite_eq_right hl]
    exact bot_le

private theorem HigherHurewicz.SimplexGeometry.continuous_extendedMinimum (n k : ℕ) :
    Continuous (fun u : Fin n → (unitInterval) => extendedMinimum u k) := by
  by_cases hk : k ≤ n
  · simpa only [extendedMinimum, ite_eq_left hk] using continuous_prefixMinimum n k
  · simpa only [extendedMinimum, ite_eq_right hk] using
      (continuous_const : Continuous (fun _ : Fin n → (unitInterval) => (0 : (unitInterval))))

private def HigherHurewicz.SimplexGeometry.simplexQuotient (n : ℕ) :
    C(Fin n → (unitInterval), FirstHurewicz.Simplex n)
    where
  toFun
    u :=
    ⟨fun i => (extendedMinimum u i.val : ℝ) - (extendedMinimum u (i.val + 1) : ℝ),
      by
      constructor
      · intro i
        exact sub_nonneg.mpr (extendedMinimum_antitone u (Nat.le_succ i.val))
      · calc
          (∑ i : Fin (n + 1),
                ((extendedMinimum u i.val : ℝ) - (extendedMinimum u (i.val + 1) : ℝ))) =
              ∑ i ∈ Finset.range (n + 1),
                ((extendedMinimum u i : ℝ) - (extendedMinimum u (i + 1) : ℝ)) :=
            Fin.sum_univ_eq_sum_range
              (fun k : ℕ => (extendedMinimum u k : ℝ) - (extendedMinimum u (k + 1) : ℝ)) (n + 1)
          _ = (extendedMinimum u 0 : ℝ) - (extendedMinimum u (n + 1) : ℝ) :=
            (Finset.sum_range_sub' _ _)
          _ = 1 := by simp⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact
      (continuous_subtype_val.comp (continuous_extendedMinimum n i.val)).sub
        (continuous_subtype_val.comp (continuous_extendedMinimum n (i.val + 1)))

private theorem
    HigherHurewicz.SimplexGeometry.simplexQuotient_apply {n : ℕ} (u : Fin n → (unitInterval))
    (i : Fin (n + 1)) :
    simplexQuotient n u i = (extendedMinimum u i.val : ℝ) - (extendedMinimum u (i.val + 1) : ℝ) :=
  rfl

private theorem HigherHurewicz.SimplexGeometry.simplexQuotient_castSucc {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) :
    simplexQuotient n u i.castSucc =
      (prefixMinimum u i.val : ℝ) - (prefixMinimum u (i.val + 1) : ℝ) := by
  rw [simplexQuotient_apply]
  exact
    congrArg₂ (fun a b : (unitInterval) => (a : ℝ) - (b : ℝ))
      (extendedMinimum_of_le u i.val i.isLt.le) (extendedMinimum_of_le u (i.val + 1) i.isLt)

@[simp]
private theorem
    HigherHurewicz.SimplexGeometry.simplexQuotient_last {n : ℕ} (u : Fin n → (unitInterval)) :
    simplexQuotient n u (Fin.last n) = (prefixMinimum u n : ℝ) := by
  rw [simplexQuotient_apply]
  simp only [Fin.val_last, extendedMinimum_last_succ, extendedMinimum_of_le u n le_rfl]
  exact sub_zero _

private theorem HigherHurewicz.SimplexGeometry.simplexQuotient_boundary_of_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 0) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  have hp : prefixMinimum u n = 0 :=
    le_antisymm (hi ▸ prefixMinimum_le_coordinate u n i i.isLt) bot_le
  exact ⟨Fin.last n, by rw [simplexQuotient_last, hp]; rfl⟩

private theorem HigherHurewicz.SimplexGeometry.simplexQuotient_boundary_of_one {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 1) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  refine ⟨i.castSucc, ?_⟩
  rw [simplexQuotient_castSucc, prefixMinimum_succ u i.val i.isLt]
  change
    (prefixMinimum u i.val : ℝ) - (Min.min (prefixMinimum u i.val) (u i) : (unitInterval)) = 0
  rw [hi, min_eq_left (show prefixMinimum u i.val ≤ 1 from (prefixMinimum u i.val).property.2)]
  exact sub_self _

private theorem HigherHurewicz.SimplexGeometry.simplexQuotient_boundary {n : ℕ}
    (u : Fin n → (unitInterval)) (hu : u ∈ Cube.boundary (Fin n)) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact simplexQuotient_boundary_of_zero u i hi
  · exact simplexQuotient_boundary_of_one u i hi

private def HigherHurewicz.SimplexGeometry.BasedSimplex (n : ℕ) {X : Type*} [TopologicalSpace X]
    (x : X) :=
  { τ : C(FirstHurewicz.Simplex n, X) //
    ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n, τ s = x }

private def HigherHurewicz.SimplexGeometry.basedSimplexLoop {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplex n x) : GenLoop (Fin n) X x :=
  ⟨τ.val.comp (simplexQuotient n), fun u hu => τ.property _ (simplexQuotient_boundary u hu)⟩

private def
    HigherHurewicz.SimplexGeometry.basedSimplexClass {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplex n x) : Additive (π_ n X x) :=
  Additive.ofMul (⟦basedSimplexLoop τ⟧ : π_ n X x)

private theorem
    HigherHurewicz.SimplexGeometry.basedSimplex_face {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplex (n + 1) x) (i : Fin (n + 2)) :
    τ.val.comp (FirstHurewicz.simplexFace n i) =
      ContinuousMap.const (FirstHurewicz.Simplex n) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ ⟨i, FirstHurewicz.simplexFace_apply_self n i s⟩

private abbrev FourthHurewicz.fourSimplexBoundary : Set (FirstHurewicz.Simplex 4) :=
  SecondHurewicz.SimplyConnected.simplexBoundary 4

private abbrev FourthHurewicz.BasedFourSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplex 4 x

private abbrev FourthHurewicz.basedFourSimplexLoop {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : GenLoop (Fin 4) X x :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoop τ

private abbrev FourthHurewicz.basedFourSimplexClass {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : Additive (π_ 4 X x) :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass τ

private theorem FourthHurewicz.basedFourSimplex_face {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) (i : Fin 5) :
    τ.val.comp (FirstHurewicz.simplexFace 3 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 3) x :=
  HigherHurewicz.SimplexGeometry.basedSimplex_face τ i

private theorem HigherHurewicz.simplexEndpoint_face_constant {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H') (x : X)
    (hone :
      ∀ smp,
        SecondHurewicz.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (FirstHurewicz.Simplex n) x)
    (smp : FirstHurewicz.SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1).comp (FirstHurewicz.simplexFace n i) =
      ContinuousMap.const (FirstHurewicz.Simplex n) x :=
  (SecondHurewicz.SimplyConnected.timeSlice_face hface smp i 1).trans (hone _)

private theorem HigherHurewicz.simplexEndpoint_boundary {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H') (x : X)
    (hone :
      ∀ smp,
        SecondHurewicz.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (FirstHurewicz.Simplex n) x)
    (smp : FirstHurewicz.SingularSimplex X (n + 1)) (s : FirstHurewicz.Simplex (n + 1))
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary (n + 1)) :
    SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1 s = x := by
  obtain ⟨i, t, ht⟩ :=
    SecondHurewicz.SimplyConnected.simplexBoundary_exists_face n
      (⟨s, hs⟩ : SecondHurewicz.SimplyConnected.SimplexBoundary (n + 1))
  have he : FirstHurewicz.simplexFace n i t = s := congrArg Subtype.val ht
  rw [← he]
  exact
    congrArg (fun f : C(FirstHurewicz.Simplex n, X) => f t)
      (simplexEndpoint_face_constant H H' hface x hone smp i)

private def
    FourthHurewicz.normalizedFourSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) : BasedFourSimplex x :=
  ⟨SecondHurewicz.SimplyConnected.timeSlice (normalizationFourSimplexHomotopy x smp) 1,
    HigherHurewicz.simplexEndpoint_boundary (normalizationThreeSimplexHomotopy x)
      (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x) x
      (normalizationThreeSimplexHomotopy_endpoint x) smp⟩

private theorem
    FourthHurewicz.normalizationFourSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) :
    SecondHurewicz.SimplyConnected.timeSlice (normalizationFourSimplexHomotopy x smp) 1 =
      (normalizedFourSimplex x smp).val :=
  rfl

private def FourthHurewicz.normalizedFiveSimplexMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) : FirstHurewicz.SingularSimplex X 5 :=
  SecondHurewicz.SimplyConnected.timeSlice (normalizationFiveSimplexHomotopy x smp) 1

private theorem FourthHurewicz.normalizedFiveSimplexMap_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) (i : Fin 6) :
    (normalizedFiveSimplexMap x smp).comp (FirstHurewicz.simplexFace 4 i) =
      (normalizedFourSimplex x (smp.comp (FirstHurewicz.simplexFace 4 i))).val :=
  SecondHurewicz.SimplyConnected.timeSlice_face (normalizationFiveHomotopy_face x) smp i 1

private theorem
    FourthHurewicz.normalizedFiveSimplexMap_face_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) (i : Fin 6) (s : FirstHurewicz.Simplex 4)
    (hs : s ∈ fourSimplexBoundary) :
    normalizedFiveSimplexMap x smp (FirstHurewicz.simplexFace 4 i s) = x := by
  have hf :=
    congrArg (fun f : C(FirstHurewicz.Simplex 4, X) => f s)
      (normalizedFiveSimplexMap_face x smp i)
  exact
    hf.trans ((normalizedFourSimplex x (smp.comp (FirstHurewicz.simplexFace 4 i))).property s hs)

private def FourthHurewicz.fourSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    FirstHurewicz.Chains X 4 →ₗ[ℤ] Additive (π_ 4 X x) :=
  FirstHurewicz.chainLift X 4 fun smp => basedFourSimplexClass (normalizedFourSimplex x smp)

@[simp]
private theorem FourthHurewicz.fourSimplexClassOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) :
    fourSimplexClassOperator x (FirstHurewicz.simplexChain X 4 smp) =
      basedFourSimplexClass (normalizedFourSimplex x smp) :=
  FirstHurewicz.chainLift_simplex X 4 _ smp

private def HigherHurewicz.straightenedCycle {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) (n + 1)
    (SecondHurewicz.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 c.1)
    (by
      have hc : ((FirstHurewicz.singularComplex X).d (n + 1) n).hom c.1 = 0 := by
        exact
          SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X)
            (n + 1) c
      rw [Nat.add_sub_cancel,
        SecondHurewicz.SimplyConnected.simplexEndpointOperator_boundary n H H' h, hc, map_zero])

@[simp]
private theorem HigherHurewicz.straightenedCycle_val {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    (straightenedCycle n H H' h c).1 =
      SecondHurewicz.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 c.1 :=
  rfl

private theorem HigherHurewicz.straightenedCycle_boundary {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp, SecondHurewicz.SimplyConnected.timeSlice (H' smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    ((FirstHurewicz.singularComplex X).d (n + 2) (n + 1)).hom
        (SecondHurewicz.SimplyConnected.simplexPrismOperator (n + 1) H' c.1) =
      (straightenedCycle n H H' h c).1 - c.1 := by
  have hc : ((FirstHurewicz.singularComplex X).d (n + 1) n).hom c.1 = 0 := by
    exact
      SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X)
        (n + 1) c
  rw [SecondHurewicz.SimplyConnected.simplexPrismOperator_boundary n H H' h,
    SecondHurewicz.SimplyConnected.simplexEndpointOperator_zero (n + 1) H' h₀, hc, map_zero,
    sub_zero]
  rfl

private theorem HigherHurewicz.straightenedCycle_class {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp, SecondHurewicz.SimplyConnected.timeSlice (H' smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) (n + 1)
        (straightenedCycle n H H' h c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) (n + 1)
        c := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X)
        (n + 1) _ _).mpr
  exact
    ⟨SecondHurewicz.SimplyConnected.simplexPrismOperator (n + 1) H' c.1,
      straightenedCycle_boundary n H H' h h₀ c⟩

private def
    FourthHurewicz.normalizedFourChain {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    FirstHurewicz.Chains X 4 →ₗ[ℤ] FirstHurewicz.Chains X 4 :=
  FirstHurewicz.chainLift X 4 fun smp =>
    FirstHurewicz.simplexChain X 4 (normalizedFourSimplex x smp).val

private def
    FourthHurewicz.normalizedFourCycle {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4 :=
  HigherHurewicz.straightenedCycle 3 (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x) c

@[simp]
private theorem FourthHurewicz.normalizedFourCycle_val {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    (normalizedFourCycle x c).val = normalizedFourChain x c.val :=
  rfl

private theorem FourthHurewicz.normalizedFourCycle_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
        (normalizedFourCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4 c := by
  apply
    HigherHurewicz.straightenedCycle_class 3 (normalizationThreeSimplexHomotopy x)
      (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x) _ c
  intro smp
  ext s
  exact normalizationFourSimplexHomotopy_zero x smp s

private def HigherHurewicz.singularHomologyDesc {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (F : FirstHurewicz.Chains X n →ₗ[ℤ] M)
    (hF :
      ∀ b : FirstHurewicz.Chains X (n + 1),
        F (((FirstHurewicz.singularComplex X).d (n + 1) n).hom b) = 0) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] M :=
  PeriodTorusHigherHomology.homologyDesc (FirstHurewicz.singularComplex X) n
    (F.comp
      (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n).subtype)
    (fun b => hF b)

@[simp]
private theorem
    HigherHurewicz.singularHomologyDesc_cycleClass {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (F : FirstHurewicz.Chains X n →ₗ[ℤ] M)
    (hF :
      ∀ b : FirstHurewicz.Chains X (n + 1),
        F (((FirstHurewicz.singularComplex X).d (n + 1) n).hom b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    singularHomologyDesc n F hF
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n c) =
      F c.1 :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass (FirstHurewicz.singularComplex X) n _ _ c

private theorem
    HigherHurewicz.comp_singularHomologyDesc_eq_id {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (F : FirstHurewicz.Chains X n →ₗ[ℤ] M)
    (hF :
      ∀ b : FirstHurewicz.Chains X (n + 1),
        F (((FirstHurewicz.singularComplex X).d (n + 1) n).hom b) = 0)
    (g : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n)
    (hg :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n,
        g (F c.1) =
          SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n c) :
    g.comp (singularHomologyDesc n F hF) = LinearMap.id := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (FirstHurewicz.singularComplex X) n
  intro c
  simpa only [LinearMap.comp_apply, singularHomologyDesc_cycleClass, LinearMap.id_apply] using
    hg c

private theorem HigherHurewicz.boundarySignSum_even (n : ℕ) (hn : Even (n + 1)) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) = 1 := by
  rw [Fin.sum_neg_one_pow]
  have h : ¬Even (n + 2) := Nat.not_even_iff_odd.mpr hn.add_one
  exact ite_eq_right h

private theorem HigherHurewicz.boundarySignSum_odd (n : ℕ) (hn : Odd (n + 1)) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) = 0 := by
  rw [Fin.sum_neg_one_pow]
  have h : Even (n + 2) := hn.add_one
  exact ite_eq_left h

private def HigherHurewicz.constantSimplexChain {X : Type} [TopologicalSpace X] (n : ℕ) (x : X) :
    FirstHurewicz.Chains X n :=
  FirstHurewicz.simplexChain X n (ContinuousMap.const (FirstHurewicz.Simplex n) x)

private theorem HigherHurewicz.boundary_constantSimplexChain {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) :
    ((FirstHurewicz.singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) • constantSimplexChain n x := by
  rw [constantSimplexChain, FirstHurewicz.boundary_simplex]
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • constantSimplexChain n x) = _
  exact
    (map_sum (zmultiplesHom (FirstHurewicz.Chains X n) (constantSimplexChain n x))
        (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val) Finset.univ).symm

private theorem
    HigherHurewicz.boundary_constantSimplexChain_even {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (hn : Even (n + 1)) :
    ((FirstHurewicz.singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) =
      constantSimplexChain n x := by
  rw [boundary_constantSimplexChain, boundarySignSum_even n hn, one_smul]

private theorem
    HigherHurewicz.boundary_constantSimplexChain_odd {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (hn : Odd (n + 1)) :
    ((FirstHurewicz.singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) = 0 := by
  rw [boundary_constantSimplexChain, boundarySignSum_odd n hn, zero_smul]

private theorem HigherHurewicz.constantSimplexChain_cycle_condition {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X) (hn : Odd n) :
    ((FirstHurewicz.singularComplex X).d n (n - 1)).hom (constantSimplexChain n x) = 0 := by
  cases n with
  | zero => simp at hn
  | succ n => exact boundary_constantSimplexChain_odd n x hn

private def HigherHurewicz.constantSimplexCycle {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (hn : Odd n) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) n
    (constantSimplexChain n x) (constantSimplexChain_cycle_condition n x hn)

@[simp]
private theorem
    HigherHurewicz.constantSimplexCycle_val {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (hn : Odd n) : (constantSimplexCycle n x hn).1 = constantSimplexChain n x :=
  rfl

@[simp]
private theorem
    HigherHurewicz.constantSimplexCycle_class {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (hn : Odd n) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
        (constantSimplexCycle n x hn) =
      0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        n _).mpr
  exact ⟨constantSimplexChain (n + 1) x, boundary_constantSimplexChain_even n x hn.add_one⟩

private def HigherHurewicz.correctedSimplexChain {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (smp : FirstHurewicz.SingularSimplex X n) : FirstHurewicz.Chains X n :=
  FirstHurewicz.simplexChain X n smp - constantSimplexChain n x

private theorem
    HigherHurewicz.correctedSimplexChain_boundary {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (smp : FirstHurewicz.SingularSimplex X (n + 1))
    (hfaces :
      ∀ i : Fin (n + 2),
        smp.comp (FirstHurewicz.simplexFace n i) =
          ContinuousMap.const (FirstHurewicz.Simplex n) x) :
    ((FirstHurewicz.singularComplex X).d (n + 1) n).hom (correctedSimplexChain (n + 1) x smp) =
      0 := by
  rw [correctedSimplexChain, map_sub, constantSimplexChain, FirstHurewicz.boundary_simplex,
    FirstHurewicz.boundary_simplex]
  simp only [hfaces, ContinuousMap.const_comp, sub_self]

private def HigherHurewicz.correctedSimplexCycle {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (smp : FirstHurewicz.SingularSimplex X (n + 1))
    (hfaces :
      ∀ i : Fin (n + 2),
        smp.comp (FirstHurewicz.simplexFace n i) =
          ContinuousMap.const (FirstHurewicz.Simplex n) x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) (n + 1)
    (correctedSimplexChain (n + 1) x smp) (correctedSimplexChain_boundary n x smp hfaces)

@[simp]
private theorem
    HigherHurewicz.correctedSimplexCycle_val {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (smp : FirstHurewicz.SingularSimplex X (n + 1))
    (hfaces :
      ∀ i : Fin (n + 2),
        smp.comp (FirstHurewicz.simplexFace n i) =
          ContinuousMap.const (FirstHurewicz.Simplex n) x) :
    (correctedSimplexCycle n x smp hfaces).1 =
      FirstHurewicz.simplexChain X (n + 1) smp - constantSimplexChain (n + 1) x :=
  rfl

private def FourthHurewicz.basedFourSimplexChain {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : FirstHurewicz.Chains X 4 :=
  HigherHurewicz.correctedSimplexChain 4 x τ.val

@[simp]
private theorem FourthHurewicz.basedFourSimplexChain_eq {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    basedFourSimplexChain τ =
      FirstHurewicz.simplexChain X 4 τ.val -
        FirstHurewicz.simplexChain X 4 (ContinuousMap.const (FirstHurewicz.Simplex 4) x) :=
  rfl

private def FourthHurewicz.basedFourSimplexCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4 :=
  HigherHurewicz.correctedSimplexCycle 3 x τ.val (basedFourSimplex_face τ)

@[simp]
private theorem FourthHurewicz.basedFourSimplexCycle_val {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : (basedFourSimplexCycle τ).1 = basedFourSimplexChain τ :=
  rfl

private theorem HigherHurewicz.chainAugmentation_boundary (X : Type) [TopologicalSpace X] (n : ℕ)
    (c : FirstHurewicz.Chains X (n + 1)) :
    SecondHurewicz.SimplyConnected.chainAugmentation X n
        (((FirstHurewicz.singularComplex X).d (n + 1) n).hom c) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) •
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c := by
  have h :
    (SecondHurewicz.SimplyConnected.chainAugmentation X n).comp
        ((FirstHurewicz.singularComplex X).d (n + 1) n).hom =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) •
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) := by
    apply FirstHurewicz.chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundary_simplex, map_sum, map_zsmul,
      SecondHurewicz.SimplyConnected.chainAugmentation_simplex, LinearMap.smul_apply,
      zsmul_eq_mul, mul_one, Int.cast_id]
  exact LinearMap.congr_fun h c

private theorem
    HigherHurewicz.chainAugmentation_boundary_even (X : Type) [TopologicalSpace X] (n : ℕ)
    (hn : Even (n + 1)) (c : FirstHurewicz.Chains X (n + 1)) :
    SecondHurewicz.SimplyConnected.chainAugmentation X n
        (((FirstHurewicz.singularComplex X).d (n + 1) n).hom c) =
      SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c := by
  rw [chainAugmentation_boundary, boundarySignSum_even n hn, one_smul]

private theorem HigherHurewicz.chainAugmentation_evenCycle (X : Type) [TopologicalSpace X] (n : ℕ)
    (hn : Even n) (hpos : 0 < n)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SecondHurewicz.SimplyConnected.chainAugmentation X n c.1 = 0 := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hpos)
  | succ n =>
    rw [← chainAugmentation_boundary_even X n hn]
    have hc : ((FirstHurewicz.singularComplex X).d (n + 1) n).hom c.1 = 0 :=
      SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X)
        (n + 1) c
    rw [hc, map_zero]

private theorem
    HigherHurewicz.chainLift_sub_constant_evenCycle (X : Type) [TopologicalSpace X] {M : Type}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (hn : Even n) (hpos : 0 < n)
    (f : FirstHurewicz.SingularSimplex X n → M) (m : M)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.chainLift X n (fun smp => f smp - m) c.1 = FirstHurewicz.chainLift X n f c.1 := by
  rw [SecondHurewicz.SimplyConnected.chainLift_sub_constant,
    chainAugmentation_evenCycle X n hn hpos, zero_smul, sub_zero]

private def FourthHurewicz.normalizedFourSimplexCycleOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    FirstHurewicz.Chains X 4 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4 :=
  FirstHurewicz.chainLift X 4 fun smp => basedFourSimplexCycle (normalizedFourSimplex x smp)

@[simp]
private theorem
    FourthHurewicz.normalizedFourSimplexCycleOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) :
    normalizedFourSimplexCycleOperator x (FirstHurewicz.simplexChain X 4 smp) =
      basedFourSimplexCycle (normalizedFourSimplex x smp) :=
  FirstHurewicz.chainLift_simplex X 4 _ smp

private theorem
    FourthHurewicz.normalizedFourSimplexCycleOperator_val {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : FirstHurewicz.Chains X 4) :
    (normalizedFourSimplexCycleOperator x c).val =
      FirstHurewicz.chainLift X 4
        (fun smp =>
          FirstHurewicz.simplexChain X 4 (normalizedFourSimplex x smp).val -
            FirstHurewicz.simplexChain X 4 (ContinuousMap.const (FirstHurewicz.Simplex 4) x))
        c := by
  have h :
    (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4).subtype.comp
        (normalizedFourSimplexCycleOperator x) =
      FirstHurewicz.chainLift X 4
        (fun smp =>
          FirstHurewicz.simplexChain X 4 (normalizedFourSimplex x smp).val -
            FirstHurewicz.simplexChain X 4 (ContinuousMap.const (FirstHurewicz.Simplex 4) x)) := by
    apply FirstHurewicz.chainMap_ext X 4
    intro smp
    simp only [LinearMap.comp_apply, normalizedFourSimplexCycleOperator_simplex,
      Submodule.subtype_apply, basedFourSimplexCycle_val, basedFourSimplexChain_eq,
      FirstHurewicz.chainLift_simplex]
  exact LinearMap.congr_fun h c

private theorem
    FourthHurewicz.normalizedFourSimplexCycleOperator_cycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    normalizedFourSimplexCycleOperator x c.val = normalizedFourCycle x c := by
  apply Subtype.ext
  rw [normalizedFourSimplexCycleOperator_val,
    HigherHurewicz.chainLift_sub_constant_evenCycle X 4 (by decide) (by decide),
    normalizedFourCycle_val]
  rfl

private theorem
    FourthHurewicz.normalizedFourSimplexCycleOperator_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
        (normalizedFourSimplexCycleOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4 c := by
  rw [normalizedFourSimplexCycleOperator_cycle, normalizedFourCycle_class]

private abbrev HigherHurewicz.CubeTriangulation.CubeN (n : ℕ) :=
  Fin n → (unitInterval)

private def
    HigherHurewicz.CubeTriangulation.cubeAffineSimplex {m n : ℕ} (v : Fin (m + 1) → CubeN n) :
    C(FirstHurewicz.Simplex m, CubeN n)
    where
  toFun s
    i :=
    ⟨∑ j, s j * (v j i : ℝ), by
      constructor
      · exact Finset.sum_nonneg fun j _ => mul_nonneg (stdSimplex.zero_le s j) (v j i).property.1
      · calc
          ∑ j, s j * (v j i : ℝ) ≤ ∑ j, s j * 1 :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (v j i).property.2 (stdSimplex.zero_le s j)
          _ = 1 := by simp only [mul_one, stdSimplex.sum_eq_one]⟩
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact
      continuous_finsetSum _ fun j _ =>
        ((continuous_apply j).comp continuous_subtype_val).mul continuous_const

@[simp]
private theorem HigherHurewicz.CubeTriangulation.cubeAffineSimplex_coordinate {m n : ℕ}
    (v : Fin (m + 1) → CubeN n) (s : FirstHurewicz.Simplex m) (i : Fin n) :
    (cubeAffineSimplex v s i : ℝ) = ∑ j, s j * (v j i : ℝ) :=
  rfl

@[simp]
private theorem HigherHurewicz.CubeTriangulation.cubeAffineSimplex_vertex {m n : ℕ}
    (v : Fin (m + 1) → CubeN n) (j : Fin (m + 1)) :
    cubeAffineSimplex v (SingularMayerVietoris.stdVertices m j) = v j := by
  funext i
  apply Subtype.ext
  simp [cubeAffineSimplex_coordinate, SingularMayerVietoris.stdVertices, stdSimplex.vertex,
    Pi.single_apply]

private theorem HigherHurewicz.CubeTriangulation.cubeAffineSimplex_face {m n : ℕ}
    (v : Fin (m + 2) → CubeN n) (i : Fin (m + 2)) :
    (cubeAffineSimplex v).comp (FirstHurewicz.simplexFace m i) =
      cubeAffineSimplex (fun j => v (i.succAbove j)) := by
  ext s k
  change
    (∑ j : Fin (m + 2), FirstHurewicz.simplexFace m i s j * (v j k : ℝ)) =
      ∑ j : Fin (m + 1), s j * (v (i.succAbove j) k : ℝ)
  rw [Fin.sum_univ_succAbove _ i]
  simp only [FirstHurewicz.simplexFace_apply_self, MulZeroClass.zero_mul,
    FirstHurewicz.simplexFace_apply_succAbove, zero_add]

private theorem HigherHurewicz.CubeTriangulation.cubeAffineSimplex_constant_coordinate {m n : ℕ}
    (v : Fin (m + 1) → CubeN n) (i : Fin n) (c : (unitInterval)) (h : ∀ j, v j i = c)
    (s : FirstHurewicz.Simplex m) : cubeAffineSimplex v s i = c := by
  apply Subtype.ext
  simp only [cubeAffineSimplex_coordinate, h, ← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

private def HigherHurewicz.CubeTriangulation.cubeVertex {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) : CubeN n := fun i => if (e.symm i).val < k.val then 1 else 0

private def HigherHurewicz.CubeTriangulation.cubeSimplex {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(FirstHurewicz.Simplex n, CubeN n) :=
  cubeAffineSimplex (cubeVertex e)

private theorem
    HigherHurewicz.CubeTriangulation.cubeSimplex_coordinate {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : FirstHurewicz.Simplex n) (i : Fin n) :
    (cubeSimplex e s (e i) : ℝ) = ∑ k : Fin (n + 1), if i.val < k.val then s k else 0 := by
  simp only [cubeSimplex, cubeAffineSimplex_coordinate, cubeVertex, Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

private theorem
    HigherHurewicz.CubeTriangulation.cubeSimplex_antitone {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : FirstHurewicz.Simplex n) : Antitone (fun i => cubeSimplex e s (e i)) := by
  intro i j hij
  change (cubeSimplex e s (e j) : ℝ) ≤ (cubeSimplex e s (e i) : ℝ)
  rw [cubeSimplex_coordinate, cubeSimplex_coordinate]
  apply Finset.sum_le_sum
  intro k _
  by_cases hj : j.val < k.val
  · have hi : i.val < k.val := lt_of_le_of_lt hij hj
    simp only [ite_eq_left hj, ite_eq_left hi, le_refl]
  · simp only [ite_eq_right hj]
    split_ifs
    · exact stdSimplex.zero_le s k
    · exact le_refl 0

private def HigherHurewicz.CubeTriangulation.cubeOrientation {n : ℕ} (e : Equiv.Perm (Fin n)) : ℤ :=
  Equiv.Perm.sign e

@[simp]
private theorem HigherHurewicz.CubeTriangulation.cubeOrientation_refl (n : ℕ) :
    cubeOrientation (Equiv.refl (Fin n)) = 1 := by simp [cubeOrientation]

private theorem
    HigherHurewicz.CubeTriangulation.cubeOrientation_swap {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j : Fin n} (h : i ≠ j) : cubeOrientation ((Equiv.swap i j).trans e) = -cubeOrientation e :=
  by simp [cubeOrientation, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap h]

private abbrev
    HigherHurewicz.CubeTriangulation.SortedCoordinates {n : ℕ} {α : Type*} [LinearOrder α]
    (u : Fin n → α) (e : Equiv.Perm (Fin n)) : Prop :=
  Antitone (fun i => u (e i))

private def HigherHurewicz.CubeTriangulation.sortedPermutation {n : ℕ} {α : Type*} [LinearOrder α]
    (u : Fin n → α) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => OrderDual.toDual (u i))

private theorem HigherHurewicz.CubeTriangulation.sortedPermutation_sorted {n : ℕ} {α : Type*}
    [LinearOrder α] (u : Fin n → α) : SortedCoordinates u (sortedPermutation u) :=
  Tuple.monotone_sort (fun i => OrderDual.toDual (u i))

private theorem HigherHurewicz.CubeTriangulation.exists_sortedPermutation {n : ℕ} {α : Type*}
    [LinearOrder α] (u : Fin n → α) : ∃ e : Equiv.Perm (Fin n), SortedCoordinates u e :=
  ⟨sortedPermutation u, sortedPermutation_sorted u⟩

private theorem
    HigherHurewicz.CubeTriangulation.sorted_values_eq {n : ℕ} {α : Type*} [LinearOrder α]
    (u : Fin n → α) {e f : Equiv.Perm (Fin n)} (he : SortedCoordinates u e)
    (hf : SortedCoordinates u f) : ∀ i : Fin n, u (e i) = u (f i) :=
  congrFun (Tuple.unique_antitone he hf)

private theorem HigherHurewicz.CubeTriangulation.sum_fin_differences {n : ℕ} (a : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (a i.castSucc - a i.succ) = a 0 - a (Fin.last n) := by
  rw [Finset.sum_sub_distrib]
  have h₀ := Fin.sum_univ_succ a
  have h₁ := Fin.sum_univ_castSucc a
  linarith

private theorem
    HigherHurewicz.CubeTriangulation.sum_fin_differences_tail (n : ℕ) (a : Fin (n + 1) → ℝ)
    (i : Fin n) :
    ∑ k : Fin n, (if i.val ≤ k.val then a k.castSucc - a k.succ else 0) =
      a i.castSucc - a (Fin.last n) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simpa only [Fin.val_zero, Nat.zero_le, ite_eq_left, Fin.castSucc_zero] using
        sum_fin_differences a
    | succ i =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, Nat.add_one_le_iff, Nat.not_lt_zero, ite_false,
        Nat.lt_succ_iff, zero_add, Fin.castSucc_succ]
      simpa only [Fin.succ_last] using ih (fun k => a k.succ) i

private def
    HigherHurewicz.CubeTriangulation.cubeExtendedCoordinates {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : CubeN n) : Fin (n + 2) → ℝ :=
  Fin.cons 1 (Fin.snoc (fun i => (u (e i) : ℝ)) 0)

@[simp]
private theorem HigherHurewicz.CubeTriangulation.cubeExtendedCoordinates_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) : cubeExtendedCoordinates e u 0 = 1 := by
  simp only [cubeExtendedCoordinates, Fin.cons_zero]

@[simp]
private theorem HigherHurewicz.CubeTriangulation.cubeExtendedCoordinates_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) : cubeExtendedCoordinates e u (Fin.last (n + 1)) = 0 :=
  by
  change cubeExtendedCoordinates e u (Fin.last n).succ = 0
  unfold cubeExtendedCoordinates
  simp only [Fin.cons_succ, Fin.snoc_last]

@[simp]
private theorem HigherHurewicz.CubeTriangulation.cubeExtendedCoordinates_inner {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) (i : Fin n) :
    cubeExtendedCoordinates e u i.castSucc.succ = (u (e i) : ℝ) := by
  simp only [cubeExtendedCoordinates, Fin.cons_succ, Fin.snoc_castSucc]

private theorem HigherHurewicz.CubeTriangulation.cubeExtendedCoordinates_nonneg {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) (i : Fin (n + 2)) :
    0 ≤ cubeExtendedCoordinates e u i := by
  cases i using Fin.cases with
  | zero => simp only [cubeExtendedCoordinates_zero, zero_le_one]
  | succ i =>
    cases i using Fin.lastCases with
    | last => simp only [cubeExtendedCoordinates, Fin.cons_succ, Fin.snoc_last, le_refl]
    | cast i => simpa only [cubeExtendedCoordinates_inner] using (u (e i)).property.1

private theorem HigherHurewicz.CubeTriangulation.cubeExtendedCoordinates_le_one {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) (i : Fin (n + 2)) :
    cubeExtendedCoordinates e u i ≤ 1 := by
  cases i using Fin.cases with
  | zero => simp only [cubeExtendedCoordinates_zero, le_refl]
  | succ i =>
    cases i using Fin.lastCases with
    | last => simp only [cubeExtendedCoordinates, Fin.cons_succ, Fin.snoc_last, zero_le_one]
    | cast i => simpa only [cubeExtendedCoordinates_inner] using (u (e i)).property.2

private theorem HigherHurewicz.CubeTriangulation.cubeExtendedCoordinates_antitone {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) (h : SortedCoordinates u e) :
    Antitone (cubeExtendedCoordinates e u) := by
  intro i j hij
  cases i using Fin.cases with
  | zero => exact cubeExtendedCoordinates_le_one e u j
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      have hh : i.val + 1 ≤ 0 := (Fin.le_iff_val_le_val).mp hij
      omega
    | succ j =>
      cases j using Fin.lastCases with
      | last =>
        simpa only [Fin.succ_last, cubeExtendedCoordinates_last] using
          cubeExtendedCoordinates_nonneg e u i.succ
      | cast j =>
        cases i using Fin.lastCases with
        | last =>
          have hj : j.val < n := j.isLt
          have hh := (Fin.le_iff_val_le_val).mp hij
          simp only [Fin.val_succ, Fin.val_last, Fin.val_castSucc] at hh
          omega
        | cast
          i =>
          have hh : i ≤ j := by
            simpa only [Fin.succ_le_succ_iff, Fin.castSucc_le_castSucc_iff] using hij
          have hreal : (u (e j) : ℝ) ≤ (u (e i) : ℝ) := h hh
          simpa only [cubeExtendedCoordinates_inner] using hreal

private def HigherHurewicz.CubeTriangulation.cubeBarycentric {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : CubeN n) : Fin (n + 1) → ℝ := fun i =>
  cubeExtendedCoordinates e u i.castSucc - cubeExtendedCoordinates e u i.succ

@[simp]
private theorem HigherHurewicz.CubeTriangulation.cubeBarycentric_zero {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : CubeN (n + 1)) :
    cubeBarycentric e u 0 = 1 - (u (e 0) : ℝ) := by
  simp only [cubeBarycentric, Fin.castSucc_zero, cubeExtendedCoordinates, Fin.cons_zero,
    Fin.cons_succ, Fin.snoc_apply_zero]

@[simp]
private theorem HigherHurewicz.CubeTriangulation.cubeBarycentric_last {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : CubeN (n + 1)) :
    cubeBarycentric e u (Fin.last (n + 1)) = (u (e (Fin.last n)) : ℝ) := by
  change
    cubeExtendedCoordinates e u (Fin.last n).castSucc.succ -
        cubeExtendedCoordinates e u (Fin.last (n + 2)) =
      _
  simp only [cubeExtendedCoordinates_inner, cubeExtendedCoordinates_last, sub_zero]

private theorem HigherHurewicz.CubeTriangulation.cubeBarycentric_inner {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : CubeN (n + 1)) (i : Fin n) :
    cubeBarycentric e u i.succ.castSucc = (u (e i.castSucc) : ℝ) - (u (e i.succ) : ℝ) := by
  change
    cubeExtendedCoordinates e u i.castSucc.castSucc.succ -
        cubeExtendedCoordinates e u i.succ.castSucc.succ =
      _
  simp only [cubeExtendedCoordinates_inner]

private theorem
    HigherHurewicz.CubeTriangulation.cubeBarycentric_nonneg {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : CubeN n) (h : SortedCoordinates u e) (i : Fin (n + 1)) : 0 ≤ cubeBarycentric e u i :=
  sub_nonneg.mpr (cubeExtendedCoordinates_antitone e u h (Nat.le_succ i.val))

private theorem
    HigherHurewicz.CubeTriangulation.cubeBarycentric_sum {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : CubeN n) : ∑ i, cubeBarycentric e u i = 1 := by
  unfold cubeBarycentric
  rw [sum_fin_differences]
  simp only [cubeExtendedCoordinates_zero, cubeExtendedCoordinates_last, sub_zero]

private theorem
    HigherHurewicz.CubeTriangulation.cubeBarycentric_tail {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : CubeN n) (i : Fin n) :
    ∑ k : Fin (n + 1), (if i.val < k.val then cubeBarycentric e u k else 0) = (u (e i) : ℝ) := by
  have h := sum_fin_differences_tail (n + 1) (cubeExtendedCoordinates e u) i.succ
  simpa only [Fin.val_succ, Nat.succ_le_iff, cubeBarycentric, Fin.castSucc_succ,
    cubeExtendedCoordinates_inner, cubeExtendedCoordinates_last, sub_zero] using h

private theorem HigherHurewicz.SimplexGeometry.cubeSimplex_quotient_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : Fin n → (unitInterval)) (i : Fin n) :
    (HigherHurewicz.CubeTriangulation.cubeSimplex e (simplexQuotient n u) (e i) : ℝ) =
      (prefixMinimum u (i.val + 1) : ℝ) := by
  rw [HigherHurewicz.CubeTriangulation.cubeSimplex_coordinate]
  have h :=
    HigherHurewicz.CubeTriangulation.sum_fin_differences_tail (n + 1)
      (fun k : Fin (n + 2) => (extendedMinimum u k.val : ℝ)) i.succ
  simpa only [simplexQuotient_apply, Fin.val_castSucc, Fin.val_succ, Nat.succ_le_iff,
    Fin.val_last, extendedMinimum_last_succ, show ((0 : (unitInterval)) : ℝ) = 0 from rfl,
    sub_zero, extendedMinimum_of_le u (i.val + 1) i.isLt] using h

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_coordinate_zero {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : FirstHurewicz.Simplex (n + 1)) :
    (cubeSimplex e s (e 0) : ℝ) = 1 - s 0 := by
  rw [cubeSimplex_coordinate, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.lt_irrefl, ite_false, Fin.val_succ, Nat.zero_lt_succ, ite_true,
    zero_add]
  have hs := stdSimplex.sum_eq_one s
  rw [Fin.sum_univ_succ] at hs
  linarith

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_coordinate_last {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : FirstHurewicz.Simplex (n + 1)) :
    (cubeSimplex e s (e (Fin.last n)) : ℝ) = s (Fin.last (n + 1)) := by
  rw [cubeSimplex_coordinate, Fin.sum_univ_castSucc]
  simp only [Fin.val_last, Fin.val_castSucc, Nat.lt_succ_self, ite_true]
  have hz : (∑ k : Fin (n + 1), if n < k.val then s k.castSucc else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    exact ite_eq_right (Nat.not_lt.mpr (Nat.le_of_lt_succ k.isLt))
  rw [hz, zero_add]

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_adjacent_difference {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : FirstHurewicz.Simplex (n + 1)) (i : Fin n) :
    (cubeSimplex e s (e i.castSucc) : ℝ) - (cubeSimplex e s (e i.succ) : ℝ) = s i.succ.castSucc :=
  by
  rw [cubeSimplex_coordinate, cubeSimplex_coordinate, ← Finset.sum_sub_distrib]
  calc
    ∑ k : Fin (n + 2),
          ((if i.castSucc.val < k.val then s k else 0) -
            (if i.succ.val < k.val then s k else 0)) =
        ∑ k : Fin (n + 2), if k = i.succ.castSucc then s k else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = i.succ.castSucc
      · subst k
        simp
      · have hv : k.val ≠ i.val + 1 := by
          intro h
          apply hk
          exact Fin.ext h
        by_cases h : i.val < k.val
        · have h' : i.val + 1 < k.val := by omega
          simp only [Fin.val_castSucc, Fin.val_succ, ite_eq_left h, ite_eq_left h',
            ite_eq_right hk, sub_self]
        · have h' : ¬i.val + 1 < k.val := by omega
          simp only [Fin.val_castSucc, Fin.val_succ, ite_eq_right h, ite_eq_right h',
            ite_eq_right hk, sub_zero]
    _ = s i.succ.castSucc := by simp

private def HigherHurewicz.CubeTriangulation.cubeOrderedRegion {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Set (CubeN n) :=
  {u | SortedCoordinates u e}

private theorem HigherHurewicz.CubeTriangulation.continuous_cubeCoordinate {n : ℕ} (i : Fin n) :
    Continuous (fun u : CubeN n => (u i : ℝ)) :=
  continuous_subtype_val.comp (continuous_apply i)

private theorem HigherHurewicz.CubeTriangulation.continuous_cubeExtendedCoordinates {n : ℕ}
    (e : Equiv.Perm (Fin n)) (i : Fin (n + 2)) :
    Continuous (fun u : CubeN n => cubeExtendedCoordinates e u i) := by
  cases i using Fin.cases with
  | zero =>
    simpa only [cubeExtendedCoordinates_zero] using
      (continuous_const : Continuous (fun _ : CubeN n => (1 : ℝ)))
  | succ i =>
    cases i using Fin.lastCases with
    | last =>
      simpa only [Fin.succ_last, cubeExtendedCoordinates_last] using
        (continuous_const : Continuous (fun _ : CubeN n => (0 : ℝ)))
    | cast i => simpa only [cubeExtendedCoordinates_inner] using continuous_cubeCoordinate (e i)

private theorem HigherHurewicz.CubeTriangulation.continuous_cubeBarycentric {n : ℕ}
    (e : Equiv.Perm (Fin n)) (i : Fin (n + 1)) :
    Continuous (fun u : CubeN n => cubeBarycentric e u i) :=
  (continuous_cubeExtendedCoordinates e i.castSucc).sub
    (continuous_cubeExtendedCoordinates e i.succ)

private def HigherHurewicz.CubeTriangulation.cubeSimplexInverse {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(↥(cubeOrderedRegion e), FirstHurewicz.Simplex n)
    where
  toFun
    u :=
    ⟨cubeBarycentric e u.val,
      ⟨cubeBarycentric_nonneg e u.val u.property, cubeBarycentric_sum e u.val⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_cubeBarycentric e i).comp continuous_subtype_val

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_sorted {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : FirstHurewicz.Simplex n) : SortedCoordinates (cubeSimplex e s) e :=
  cubeSimplex_antitone e s

@[simp]
private theorem
    HigherHurewicz.CubeTriangulation.cubeSimplex_inverse {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : ↥(cubeOrderedRegion e)) : cubeSimplex e (cubeSimplexInverse e u) = u.val := by
  funext k
  obtain ⟨i, rfl⟩ := e.surjective k
  apply Subtype.ext
  rw [cubeSimplex_coordinate]
  exact cubeBarycentric_tail e u.val i

@[simp]
private theorem HigherHurewicz.CubeTriangulation.cubeSimplexInverse_simplex {n : ℕ}
    (e : Equiv.Perm (Fin n)) (s : FirstHurewicz.Simplex n) :
    cubeSimplexInverse e ⟨cubeSimplex e s, cubeSimplex_sorted e s⟩ = s := by
  cases n with
  | zero =>
    exact
      (FirstHurewicz.simplexZero_eq_vertex _).trans (FirstHurewicz.simplexZero_eq_vertex s).symm
  | succ n =>
    apply Subtype.ext
    funext i
    change cubeBarycentric e (cubeSimplex e s) i = s i
    cases i using Fin.cases with
    | zero =>
      rw [cubeBarycentric_zero, cubeSimplex_coordinate_zero]
      ring
    | succ i =>
      cases i using Fin.lastCases with
      | last =>
        simpa only [Fin.succ_last, cubeBarycentric_last] using cubeSimplex_coordinate_last e s
      | cast i =>
        simpa only [← Fin.castSucc_succ, cubeBarycentric_inner] using
          cubeSimplex_adjacent_difference e s i

private theorem
    HigherHurewicz.CubeTriangulation.cubeSimplex_injective {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Function.Injective (cubeSimplex e) := by
  intro s t h
  have hh :
    (⟨cubeSimplex e s, cubeSimplex_sorted e s⟩ : ↥(cubeOrderedRegion e)) =
      ⟨cubeSimplex e t, cubeSimplex_sorted e t⟩ :=
    Subtype.ext h
  simpa only [cubeSimplexInverse_simplex] using congrArg (cubeSimplexInverse e) hh

private theorem HigherHurewicz.SimplexGeometry.prefixMinimum_of_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) (hu : Antitone u) (i : Fin n) :
    prefixMinimum u (i.val + 1) = u i := by
  apply le_antisymm (prefixMinimum_le_coordinate u (i.val + 1) i (Nat.lt_succ_self _))
  unfold prefixMinimum
  apply Finset.le_inf
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact hu (Nat.le_of_lt_succ hj)

private theorem HigherHurewicz.SimplexGeometry.cubeSimplex_quotient_of_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) (hu : Antitone u) :
    HigherHurewicz.CubeTriangulation.cubeSimplex (Equiv.refl (Fin n)) (simplexQuotient n u) = u :=
  by
  funext i
  apply Subtype.ext
  simpa only [Equiv.refl_apply, prefixMinimum_of_antitone u hu i] using
    cubeSimplex_quotient_coordinate (Equiv.refl (Fin n)) u i

private theorem HigherHurewicz.SimplexGeometry.simplexQuotient_cubeSimplex_refl (n : ℕ) :
    (simplexQuotient n).comp (HigherHurewicz.CubeTriangulation.cubeSimplex (Equiv.refl (Fin n))) =
      ContinuousMap.id (FirstHurewicz.Simplex n) := by
  apply ContinuousMap.ext
  intro s
  apply HigherHurewicz.CubeTriangulation.cubeSimplex_injective (Equiv.refl (Fin n))
  exact
    cubeSimplex_quotient_of_antitone _
      (HigherHurewicz.CubeTriangulation.cubeSimplex_antitone (Equiv.refl (Fin n)) s)

private theorem HigherHurewicz.SimplexGeometry.simplexQuotient_boundary_of_coordinate_le {n : ℕ}
    (u : Fin n → (unitInterval)) (i j : Fin n) (hij : i < j) (hu : u i ≤ u j) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  refine ⟨j.castSucc, ?_⟩
  rw [simplexQuotient_castSucc, prefixMinimum_succ u j.val j.isLt]
  have hp : prefixMinimum u j.val ≤ u j := (prefixMinimum_le_coordinate u j.val i hij).trans hu
  rw [min_eq_left hp]
  exact sub_self _

private theorem HigherHurewicz.SimplexGeometry.cubeSimplex_coordinate_inversion {n : ℕ}
    (e : Equiv.Perm (Fin n)) (he : e ≠ Equiv.refl (Fin n)) (s : FirstHurewicz.Simplex n) :
    ∃ i j : Fin n,
      i < j ∧
        HigherHurewicz.CubeTriangulation.cubeSimplex e s i ≤
          HigherHurewicz.CubeTriangulation.cubeSimplex e s j := by
  by_contra h
  have hu : StrictAnti (HigherHurewicz.CubeTriangulation.cubeSimplex e s) := by
    intro i j hij
    exact lt_of_not_ge (fun hle => h ⟨i, j, hij, hle⟩)
  have hm : Monotone e := by
    intro i j hij
    exact hu.le_iff_ge.mp (HigherHurewicz.CubeTriangulation.cubeSimplex_antitone e s hij)
  apply he
  apply Equiv.ext
  intro i
  exact (hm.strictMono_of_injective e.injective).apply_eq

private theorem HigherHurewicz.SimplexGeometry.simplexQuotient_cubeSimplex_boundary {n : ℕ}
    (e : Equiv.Perm (Fin n)) (he : e ≠ Equiv.refl (Fin n)) (s : FirstHurewicz.Simplex n) :
    simplexQuotient n (HigherHurewicz.CubeTriangulation.cubeSimplex e s) ∈
      SecondHurewicz.SimplyConnected.simplexBoundary n := by
  obtain ⟨i, j, hij, hu⟩ := cubeSimplex_coordinate_inversion e he s
  exact simplexQuotient_boundary_of_coordinate_le _ i j hij hu

private theorem HigherHurewicz.SimplexGeometry.basedSimplexLoop_cubeSimplex_refl {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplex n x) :
    (basedSimplexLoop τ).val.comp
        (HigherHurewicz.CubeTriangulation.cubeSimplex (Equiv.refl (Fin n))) =
      τ.val := by
  change (τ.val.comp (simplexQuotient n)).comp _ = _
  rw [ContinuousMap.comp_assoc, simplexQuotient_cubeSimplex_refl, ContinuousMap.comp_id]

private theorem HigherHurewicz.SimplexGeometry.basedSimplexLoop_cubeSimplex_other {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplex n x) (e : Equiv.Perm (Fin n))
    (he : e ≠ Equiv.refl (Fin n)) :
    (basedSimplexLoop τ).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e) =
      ContinuousMap.const (FirstHurewicz.Simplex n) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ (simplexQuotient_cubeSimplex_boundary e he s)

private theorem HigherHurewicz.SimplexGeometry.cubeOrientation_sum (n : ℕ) :
    ∑ e : Equiv.Perm (Fin (n + 2)), HigherHurewicz.CubeTriangulation.cubeOrientation e = 0 := by
  have hij : (0 : Fin (n + 2)) ≠ 1 := Fin.zero_ne_one
  have h :=
    Equiv.sum_comp (Equiv.mulRight (Equiv.swap (0 : Fin (n + 2)) 1))
      (HigherHurewicz.CubeTriangulation.cubeOrientation (n := n + 2))
  change
    (∑ e : Equiv.Perm (Fin (n + 2)),
        HigherHurewicz.CubeTriangulation.cubeOrientation ((Equiv.swap 0 1).trans e)) =
      ∑ e : Equiv.Perm (Fin (n + 2)), HigherHurewicz.CubeTriangulation.cubeOrientation e at h
  simp_rw [HigherHurewicz.CubeTriangulation.cubeOrientation_swap _ hij] at h
  rw [Finset.sum_neg_distrib] at h
  omega

private theorem HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplex (n + 2) x) :
    (∑ e : Equiv.Perm (Fin (n + 2)),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X (n + 2)
            ((basedSimplexLoop τ).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) =
      HigherHurewicz.correctedSimplexChain (n + 2) x τ.val := by
  classical
  let c := HigherHurewicz.constantSimplexChain (n + 2) x
  have heq (e : Equiv.Perm (Fin (n + 2))) :
    HigherHurewicz.CubeTriangulation.cubeOrientation e •
        FirstHurewicz.simplexChain X (n + 2)
          ((basedSimplexLoop τ).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) =
      (if e = Equiv.refl (Fin (n + 2)) then HigherHurewicz.correctedSimplexChain (n + 2) x τ.val
        else 0) +
        HigherHurewicz.CubeTriangulation.cubeOrientation e • c := by
    by_cases he : e = Equiv.refl (Fin (n + 2))
    · subst e
      rw [basedSimplexLoop_cubeSimplex_refl,
        HigherHurewicz.CubeTriangulation.cubeOrientation_refl, one_smul, ite_eq_left rfl, one_smul]
      change
        FirstHurewicz.simplexChain X (n + 2) τ.val =
          (FirstHurewicz.simplexChain X (n + 2) τ.val - c) + c
      exact (sub_add_cancel _ _).symm
    · rw [basedSimplexLoop_cubeSimplex_other τ e he, ite_eq_right he, zero_add]
      rfl
  calc
    _ =
        ∑ e : Equiv.Perm (Fin (n + 2)),
          ((if e = Equiv.refl (Fin (n + 2)) then
              HigherHurewicz.correctedSimplexChain (n + 2) x τ.val
            else 0) +
            HigherHurewicz.CubeTriangulation.cubeOrientation e • c) :=
      Finset.sum_congr rfl (fun e _ => heq e)
    _ =
        HigherHurewicz.correctedSimplexChain (n + 2) x τ.val +
          (∑ e : Equiv.Perm (Fin (n + 2)), HigherHurewicz.CubeTriangulation.cubeOrientation e) •
            c := by
      rw [Finset.sum_add_distrib]
      have hc :
        (∑ e : Equiv.Perm (Fin (n + 2)), HigherHurewicz.CubeTriangulation.cubeOrientation e) • c =
          ∑ e : Equiv.Perm (Fin (n + 2)),
            HigherHurewicz.CubeTriangulation.cubeOrientation e • c := by
        let f : ℤ →+ FirstHurewicz.Chains X (n + 2) :=
          { toFun := fun k => k • c
            map_zero' := zero_zsmul c
            map_add' := fun a b => add_zsmul c a b }
        exact map_sum f HigherHurewicz.CubeTriangulation.cubeOrientation Finset.univ
      rw [← hc]
      simp
    _ = HigherHurewicz.correctedSimplexChain (n + 2) x τ.val := by
      rw [cubeOrientation_sum n, zero_smul, add_zero]

private theorem
    FourthHurewicz.basedFourSimplex_simplexChain_sum {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    (∑ e : Equiv.Perm (Fin 4),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X 4
            ((basedFourSimplexLoop τ).val.comp
              (HigherHurewicz.CubeTriangulation.cubeSimplex e))) =
      basedFourSimplexChain τ :=
  HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum τ

private theorem
    FourthHurewicz.CubeSubdivision.signed_sum_eq_zero_of_swap_invariant {n : ℕ} {A : Type*}
    [AddCommGroup A] (i j : Fin n) (hij : i ≠ j) (f : Equiv.Perm (Fin n) → A)
    (hf : ∀ e, f ((Equiv.swap i j).trans e) = f e) :
    ∑ e, HigherHurewicz.CubeTriangulation.cubeOrientation e • f e = 0 := by
  classical
  apply Finset.sum_ninvolution (fun e => (Equiv.swap i j).trans e)
  · intro e
    rw [HigherHurewicz.CubeTriangulation.cubeOrientation_swap e hij, hf, neg_smul, add_neg_cancel]
  · intro e _ he
    have h := congrArg (fun k : Equiv.Perm (Fin n) => k i) he
    have h' : e j = e i := by simpa using h
    exact hij (e.injective h').symm
  · intro e
    exact Finset.mem_univ _
  · intro e
    ext k
    simp

private theorem
    FourthHurewicz.CubeSubdivision.signed_sum_constant_eq_zero {n : ℕ} [Nontrivial (Fin n)]
    {A : Type*} [AddCommGroup A] (a : A) :
    ∑ e : Equiv.Perm (Fin n), HigherHurewicz.CubeTriangulation.cubeOrientation e • a = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin n)
  exact signed_sum_eq_zero_of_swap_invariant i j hij (fun _ => a) (fun _ => rfl)

private theorem HigherHurewicz.CubeTriangulation.cubeVertex_swap_of_ne {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) (k : Fin (n + 2)) (hk : k ≠ i.succ.castSucc) :
    cubeVertex e k = cubeVertex ((Equiv.swap i.castSucc i.succ).trans e) k := by
  funext coord
  change
    (if (e.symm coord).val < k.val then (1 : (unitInterval)) else 0) =
      if ((Equiv.swap i.castSucc i.succ) (e.symm coord)).val < k.val then 1 else 0
  have hk' : k.val ≠ i.val + 1 := by
    intro h
    exact hk (Fin.ext h)
  by_cases h₀ : e.symm coord = i.castSucc
  · rw [h₀, Equiv.swap_apply_left]
    simp only [Fin.val_castSucc, Fin.val_succ]
    have h : i.val < k.val ↔ i.val + 1 < k.val := by omega
    simp only [h]
  by_cases h₁ : e.symm coord = i.succ
  · rw [h₁, Equiv.swap_apply_right]
    simp only [Fin.val_castSucc, Fin.val_succ]
    have h : i.val + 1 < k.val ↔ i.val < k.val := by omega
    simp only [h]
  · rw [Equiv.swap_apply_of_ne_of_ne h₀ h₁]

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_face_swap {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    (cubeSimplex e).comp (FirstHurewicz.simplexFace n i.succ.castSucc) =
      (cubeSimplex ((Equiv.swap i.castSucc i.succ).trans e)).comp
        (FirstHurewicz.simplexFace n i.succ.castSucc) := by
  simp only [cubeSimplex, cubeAffineSimplex_face]
  congr 1
  funext j
  exact cubeVertex_swap_of_ne e i _ (Fin.succAbove_ne _ _)

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_face_zero_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : FirstHurewicz.Simplex n) :
    cubeSimplex e (FirstHurewicz.simplexFace n 0 s) (e 0) = 1 := by
  change ((cubeAffineSimplex (cubeVertex e)).comp (FirstHurewicz.simplexFace n 0)) s (e 0) = 1
  rw [cubeAffineSimplex_face]
  apply cubeAffineSimplex_constant_coordinate
  intro j
  simp [cubeVertex]

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_face_last_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : FirstHurewicz.Simplex n) :
    cubeSimplex e (FirstHurewicz.simplexFace n (Fin.last (n + 1)) s) (e (Fin.last n)) = 0 := by
  change
    ((cubeAffineSimplex (cubeVertex e)).comp (FirstHurewicz.simplexFace n (Fin.last (n + 1)))) s
        (e (Fin.last n)) =
      0
  rw [cubeAffineSimplex_face]
  apply cubeAffineSimplex_constant_coordinate
  intro j
  simp only [cubeVertex, Equiv.symm_apply_apply, Fin.succAbove_last, Fin.val_castSucc,
    Fin.val_last]
  exact ite_eq_right (Nat.not_lt.mpr (Nat.le_of_lt_succ j.isLt))

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_face_zero_boundary {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : FirstHurewicz.Simplex n) :
    cubeSimplex e (FirstHurewicz.simplexFace n 0 s) ∈ Cube.boundary (Fin (n + 1)) :=
  ⟨e 0, Or.inr (cubeSimplex_face_zero_coordinate e s)⟩

private theorem HigherHurewicz.CubeTriangulation.cubeSimplex_face_last_boundary {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : FirstHurewicz.Simplex n) :
    cubeSimplex e (FirstHurewicz.simplexFace n (Fin.last (n + 1)) s) ∈
      Cube.boundary (Fin (n + 1)) :=
  ⟨e (Fin.last n), Or.inl (cubeSimplex_face_last_coordinate e s)⟩

private def FourthHurewicz.CubeSubdivision.prismCubeVertex {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : Fin 2 × Fin (n + 1)) : HigherHurewicz.CubeTriangulation.CubeN (n + 1) :=
  Fin.cases (FirstHurewicz.pathSimplex Path.id (SingularMayerVietoris.stdVertices 1 z.1))
    (HigherHurewicz.CubeTriangulation.cubeVertex e z.2)

@[simp]
private theorem FourthHurewicz.CubeSubdivision.prismCubeVertex_succ {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : Fin 2 × Fin (n + 1)) (i : Fin n) :
    prismCubeVertex e z i.succ = HigherHurewicz.CubeTriangulation.cubeVertex e z.2 i :=
  rfl

private def FourthHurewicz.CubeSubdivision.prismCubeSimplex {m n : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    C(FirstHurewicz.Simplex m, HigherHurewicz.CubeTriangulation.CubeN (n + 1)) :=
  HigherHurewicz.CubeTriangulation.cubeAffineSimplex (fun j => prismCubeVertex e (v j))

private theorem FourthHurewicz.CubeSubdivision.prismCubeVertex_swap_of_ne {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) (z : Fin 2 × Fin (n + 2))
    (hz : z.2 ≠ i.succ.castSucc) :
    prismCubeVertex e z = prismCubeVertex ((Equiv.swap i.castSucc i.succ).trans e) z := by
  funext coord
  refine Fin.cases ?_ (fun k => ?_) coord
  · rfl
  · exact congrFun (HigherHurewicz.CubeTriangulation.cubeVertex_swap_of_ne e i z.2 hz) k

private theorem FourthHurewicz.CubeSubdivision.prismCubeSimplex_swap_of_omitted {m n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) (v : Fin (m + 1) → Fin 2 × Fin (n + 2))
    (hv : ∀ j, (v j).2 ≠ i.succ.castSucc) :
    prismCubeSimplex e v = prismCubeSimplex ((Equiv.swap i.castSucc i.succ).trans e) v := by
  apply congrArg HigherHurewicz.CubeTriangulation.cubeAffineSimplex
  funext j
  exact prismCubeVertex_swap_of_ne e i (v j) (hv j)

private theorem FourthHurewicz.CubeSubdivision.prismCubeSimplex_zero_of_left_zero {m n : ℕ}
    (e : Equiv.Perm (Fin n)) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) (hv : ∀ j, (v j).1 = 0)
    (s : FirstHurewicz.Simplex m) : prismCubeSimplex e v s 0 = 0 := by
  apply HigherHurewicz.CubeTriangulation.cubeAffineSimplex_constant_coordinate
  intro j
  simp [prismCubeVertex, hv j, SingularMayerVietoris.stdVertices]

private theorem FourthHurewicz.CubeSubdivision.prismCubeSimplex_zero_of_last_omitted {m n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (v : Fin (m + 1) → Fin 2 × Fin (n + 2))
    (hv : ∀ j, (v j).2 ≠ Fin.last (n + 1)) (s : FirstHurewicz.Simplex m) :
    prismCubeSimplex e v s (e (Fin.last n)).succ = 0 := by
  apply HigherHurewicz.CubeTriangulation.cubeAffineSimplex_constant_coordinate
  intro j
  simp only [prismCubeVertex_succ, HigherHurewicz.CubeTriangulation.cubeVertex,
    Equiv.symm_apply_apply, Fin.val_last]
  apply ite_eq_right
  have hne : (v j).2.val ≠ n + 1 := by
    intro h
    exact hv j (Fin.ext h)
  have hlt := (v j).2.isLt
  omega

private def
    FourthHurewicz.CubeSubdivision.prismCubeRealization {X : Type} [TopologicalSpace X] {n : ℕ}
    (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X)) (e : Equiv.Perm (Fin n)) (m : ℕ) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin (n + 1)) (m + 1) →ₗ[ℤ]
      FirstHurewicz.Chains X m :=
  SingularMayerVietoris.formalLift fun v =>
    FirstHurewicz.simplexChain X m (p.comp (prismCubeSimplex e v))

@[simp]
private theorem FourthHurewicz.CubeSubdivision.prismCubeRealization_simplex {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) (m : ℕ) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    prismCubeRealization p e m (SingularMayerVietoris.formalSimplex v) =
      FirstHurewicz.simplexChain X m (p.comp (prismCubeSimplex e v)) :=
  SingularMayerVietoris.formalLift_simplex _ _

private def FourthHurewicz.CubeSubdivision.orientedPrismRealization {X : Type} [TopologicalSpace X]
    {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X)) (m : ℕ) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin (n + 1)) (m + 1) →ₗ[ℤ]
      FirstHurewicz.Chains X m :=
  SingularMayerVietoris.formalLift fun v =>
    ∑ e : Equiv.Perm (Fin n),
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        FirstHurewicz.simplexChain X m (p.comp (prismCubeSimplex e v))

@[simp]
private theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_simplex {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (m : ℕ) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    orientedPrismRealization p m (SingularMayerVietoris.formalSimplex v) =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X m (p.comp (prismCubeSimplex e v)) :=
  SingularMayerVietoris.formalLift_simplex _ _

private abbrev FourthHurewicz.Remaining :=
  { j : Fin 4 // j ≠ 0 }

private def
    FourthHurewicz.remainingCoordinates : C(Fin 3 → (unitInterval), Remaining → (unitInterval))
    where
  toFun u j := u (j.val.pred j.property)
  continuous_toFun := by fun_prop

@[simp]
private theorem FourthHurewicz.remainingCoordinates_succ (u : Fin 3 → (unitInterval)) (i : Fin 3) :
    remainingCoordinates u ⟨i.succ, Fin.succ_ne_zero i⟩ = u i := by simp [remainingCoordinates]

private theorem FourthHurewicz.remainingCoordinates_boundary {u : Fin 3 → (unitInterval)}
    (h : u ∈ Cube.boundary (Fin 3)) : remainingCoordinates u ∈ Cube.boundary Remaining := by
  obtain ⟨i, hi⟩ := h
  exact ⟨⟨i.succ, Fin.succ_ne_zero i⟩, by simpa using hi⟩

private abbrev FourthHurewicz.BasedLoopSpace {X : Type} [TopologicalSpace X] (x : X) :=
  GenLoop Remaining X x

private def FourthHurewicz.evaluation {X : Type} [TopologicalSpace X] (x : X) :
    C(BasedLoopSpace x × (Fin 3 → (unitInterval)), X)
    where
  toFun z := z.1 (remainingCoordinates z.2)
  continuous_toFun := by fun_prop

private theorem FourthHurewicz.evaluation_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    evaluation x (p, u) = x :=
  GenLoop.boundary p _ (remainingCoordinates_boundary hu)

private theorem FourthHurewicz.evaluation_comp_boundary {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (x : X) (f : C(A, Fin 3 → (unitInterval)))
    (hf : ∀ a, f a ∈ Cube.boundary (Fin 3)) :
    (evaluation x).comp ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) =
      ContinuousMap.const (BasedLoopSpace x × A) x := by
  ext z
  exact evaluation_boundary x z.1 (f z.2) (hf z.2)

private def FourthHurewicz.cubeCoordinates :
    C((unitInterval) × (Fin 3 → (unitInterval)), Fin 4 → (unitInterval))
    where
  toFun z := Cube.insertAt (0 : Fin 4) (z.1, remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp]
private theorem
    FourthHurewicz.cubeCoordinates_zero (z : (unitInterval) × (Fin 3 → (unitInterval))) :
    cubeCoordinates z 0 = z.1 := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp]
private theorem FourthHurewicz.cubeCoordinates_succ (z : (unitInterval) × (Fin 3 → (unitInterval)))
    (i : Fin 3) : cubeCoordinates z i.succ = z.2 i := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply, remainingCoordinates]

private def
    FourthHurewicz.cubeMap {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) :
    C((unitInterval) × (Fin 3 → (unitInterval)), X) :=
  p.val.comp cubeCoordinates

private theorem FourthHurewicz.evaluation_comp_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 4) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 4) p).toContinuousMap.prodMap
          (ContinuousMap.id (Fin 3 → (unitInterval)))) =
      cubeMap p := by
  ext z
  rfl

private theorem FourthHurewicz.CubeSubdivision.cubeCoordinates_boundary_right (s : (unitInterval))
    {u : Fin 3 → (unitInterval)} (hu : u ∈ Cube.boundary (Fin 3)) :
    FourthHurewicz.cubeCoordinates (s, u) ∈ Cube.boundary (Fin 4) := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨i.succ, by simpa only [FourthHurewicz.cubeCoordinates_succ] using hi⟩

private def FourthHurewicz.CubeSubdivision.curryLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 4) X x) :
    GenLoop (Fin 3) C((unitInterval), X) (ContinuousMap.const (unitInterval) x) :=
  ⟨((FourthHurewicz.cubeMap p).comp ContinuousMap.prodSwap).curry,
    by
    intro u hu
    apply ContinuousMap.ext
    intro s
    exact GenLoop.boundary p _ (cubeCoordinates_boundary_right s hu)⟩

private def FourthHurewicz.CubeSubdivision.evalLeft (X : Type) [TopologicalSpace X] :
    C((unitInterval) × C((unitInterval), X), X)
    where
  toFun z := z.2 z.1
  continuous_toFun := by fun_prop

private theorem
    FourthHurewicz.CubeSubdivision.evalLeft_comp_curryLoop {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 4) X x) :
    (evalLeft X).comp ((ContinuousMap.id (unitInterval)).prodMap (curryLoop p).val) =
      FourthHurewicz.cubeMap p := by
  ext z
  rfl

private theorem FourthHurewicz.CubeSubdivision.cubeAffineSimplex_comp {k m n : ℕ}
    (v : Fin (n + 1) → HigherHurewicz.CubeTriangulation.CubeN k)
    (w : Fin (m + 1) → FirstHurewicz.Simplex n) :
    (HigherHurewicz.CubeTriangulation.cubeAffineSimplex v).comp
        (SingularMayerVietoris.affineSimplex w) =
      HigherHurewicz.CubeTriangulation.cubeAffineSimplex
        (fun j => HigherHurewicz.CubeTriangulation.cubeAffineSimplex v (w j)) := by
  ext t i
  change
    (HigherHurewicz.CubeTriangulation.cubeAffineSimplex v
          (SingularMayerVietoris.affineSimplex w t) i :
        ℝ) =
      (HigherHurewicz.CubeTriangulation.cubeAffineSimplex
          (fun j => HigherHurewicz.CubeTriangulation.cubeAffineSimplex v (w j)) t i :
        ℝ)
  simp only [HigherHurewicz.CubeTriangulation.cubeAffineSimplex_coordinate,
    SingularMayerVietoris.affineSimplex_coordinate, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private theorem FourthHurewicz.CubeSubdivision.cubeAffineSimplex_comp_selectedVertices {k m n : ℕ}
    (v : Fin (n + 1) → HigherHurewicz.CubeTriangulation.CubeN k) (a : Fin (m + 1) → Fin (n + 1)) :
    (HigherHurewicz.CubeTriangulation.cubeAffineSimplex v).comp
        (SingularMayerVietoris.affineSimplex
          (fun j => SingularMayerVietoris.stdVertices n (a j))) =
      HigherHurewicz.CubeTriangulation.cubeAffineSimplex (fun j => v (a j)) := by
  rw [cubeAffineSimplex_comp]
  simp only [HigherHurewicz.CubeTriangulation.cubeAffineSimplex_vertex]

private def FourthHurewicz.CubeSubdivision.prismCubeMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(FirstHurewicz.Simplex 1 × FirstHurewicz.Simplex n,
      HigherHurewicz.CubeTriangulation.CubeN (n + 1))
    where
  toFun
    z :=
    Fin.cases (FirstHurewicz.pathSimplex Path.id z.1)
      (HigherHurewicz.CubeTriangulation.cubeSimplex e z.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (FirstHurewicz.pathSimplex Path.id).continuous.comp continuous_fst
    · exact
        (continuous_apply j).comp
          ((HigherHurewicz.CubeTriangulation.cubeSimplex e).continuous.comp continuous_snd)

private theorem
    FourthHurewicz.CubeSubdivision.prismCubeMap_affine {m n : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    (prismCubeMap e).comp
        (PeriodTorusHigherHomology.productAffineSimplex
          (fun j =>
            (SingularMayerVietoris.stdVertices 1 (v j).1,
              SingularMayerVietoris.stdVertices n (v j).2))) =
      prismCubeSimplex e v := by
  apply ContinuousMap.ext
  intro t
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · apply Subtype.ext
    change
      SingularMayerVietoris.affineSimplex (fun j => SingularMayerVietoris.stdVertices 1 (v j).1) t
          1 =
        ∑ j, t j * SingularMayerVietoris.stdVertices 1 (v j).1 1
    exact SingularMayerVietoris.affineSimplex_coordinate _ _ _
  · change
      ((HigherHurewicz.CubeTriangulation.cubeAffineSimplex
                (HigherHurewicz.CubeTriangulation.cubeVertex e)).comp
            (SingularMayerVietoris.affineSimplex
              (fun j => SingularMayerVietoris.stdVertices n (v j).2)))
          t k =
        _
    rw [cubeAffineSimplex_comp_selectedVertices]
    rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FourthHurewicz.remainingCubeSideFirst (t : (unitInterval)) :
    C(Fin 2 → (unitInterval), Fin 3 → (unitInterval)) :=
  ThirdHurewicz.cubeCoordinates.comp (PeriodTorusHigherHomology.crossInsertLeft t)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FourthHurewicz.remainingCubeSide (f : C((unitInterval), Fin 2 → (unitInterval))) :
    C((unitInterval) × (unitInterval), Fin 3 → (unitInterval)) :=
  ThirdHurewicz.cubeCoordinates.comp ((ContinuousMap.id (unitInterval)).prodMap f)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FourthHurewicz.remainingCubeSideFirst_boundary (t : (unitInterval)) (ht : t = 0 ∨ t = 1)
    (u : Fin 2 → (unitInterval)) : remainingCubeSideFirst t u ∈ Cube.boundary (Fin 3) := by
  refine ⟨0, ?_⟩
  change ThirdHurewicz.cubeCoordinates (t, u) 0 = 0 ∨ ThirdHurewicz.cubeCoordinates (t, u) 0 = 1
  simpa only [ThirdHurewicz.cubeCoordinates_zero] using ht

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FourthHurewicz.remainingCubeSide_boundary (f : C((unitInterval), Fin 2 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 2)) (z : (unitInterval) × (unitInterval)) :
    remainingCubeSide f z ∈ Cube.boundary (Fin 3) := by
  obtain ⟨i, hi⟩ := hf z.2
  refine ⟨i.succ, ?_⟩
  change
    ThirdHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 0 ∨
      ThirdHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 1
  simpa only [ThirdHurewicz.cubeCoordinates_succ] using hi

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FourthHurewicz.remainingCubeSide_chain (f : C((unitInterval), Fin 2 → (unitInterval))) :
    FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 2
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 2 → (unitInterval)) 1
          SecondHurewicz.intervalChain
          (FirstHurewicz.inducedChain f 1 SecondHurewicz.intervalChain)) =
      FirstHurewicz.inducedChain (remainingCubeSide f) 2 SecondHurewicz.productSquareChain := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval)) f 1
      SecondHurewicz.intervalChain SecondHurewicz.intervalChain
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 2).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (unitInterval)).prodMap f) 2))
        SecondHurewicz.productSquareChain =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.remainingCubeChain_boundary :
    ((FirstHurewicz.singularComplex (Fin 3 → (unitInterval))).d 3 2).hom
        ThirdHurewicz.fundamentalCubeChain =
      FirstHurewicz.inducedChain (remainingCubeSideFirst 1) 2
            SecondHurewicz.fundamentalSquareChain -
          FirstHurewicz.inducedChain (remainingCubeSideFirst 0) 2
            SecondHurewicz.fundamentalSquareChain -
        (FirstHurewicz.inducedChain (remainingCubeSide (ThirdHurewicz.squareSideLeft 1)) 2
              SecondHurewicz.productSquareChain -
            FirstHurewicz.inducedChain (remainingCubeSide (ThirdHurewicz.squareSideLeft 0)) 2
              SecondHurewicz.productSquareChain -
          (FirstHurewicz.inducedChain (remainingCubeSide (ThirdHurewicz.squareSideRight 1)) 2
              SecondHurewicz.productSquareChain -
            FirstHurewicz.inducedChain (remainingCubeSide (ThirdHurewicz.squareSideRight 0)) 2
              SecondHurewicz.productSquareChain)) := by
  have hpoint (t : (unitInterval)) :
    PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (Fin 2 → (unitInterval)) 2
        (FirstHurewicz.pointChain t) SecondHurewicz.fundamentalSquareChain =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) 2
        SecondHurewicz.fundamentalSquareChain := by
    rw [FirstHurewicz.pointChain, PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left]
    rfl
  have hfirst (t : (unitInterval)) :
    FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 2
        (FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) 2
          SecondHurewicz.fundamentalSquareChain) =
      FirstHurewicz.inducedChain (remainingCubeSideFirst t) 2
        SecondHurewicz.fundamentalSquareChain := by
    rw [remainingCubeSideFirst, FirstHurewicz.inducedChain_comp]
    rfl
  rw [ThirdHurewicz.fundamentalCubeChain, ← FirstHurewicz.inducedChain_boundary]
  change
    FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 2
        (((FirstHurewicz.singularComplex ((unitInterval) × (Fin 2 → (unitInterval)))).d 3 2).hom
          (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 2 → (unitInterval)) 2
            SecondHurewicz.intervalChain SecondHurewicz.fundamentalSquareChain)) =
      _
  rw [PeriodTorusHigherHomology.crossProductEdge_boundary 1]
  change
    FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 2
        (PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (Fin 2 → (unitInterval)) 2
            (FirstHurewicz.boundaryOne (unitInterval) SecondHurewicz.intervalChain)
            SecondHurewicz.fundamentalSquareChain -
          PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 2 → (unitInterval)) 1
            SecondHurewicz.intervalChain
            (FirstHurewicz.boundaryTwo (Fin 2 → (unitInterval))
              SecondHurewicz.fundamentalSquareChain)) =
      _
  rw [SecondHurewicz.intervalChain_boundary, ThirdHurewicz.fundamentalSquareChain_boundary]
  simp only [map_sub, LinearMap.sub_apply, hpoint, hfirst, remainingCubeSide_chain]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.evaluated_edge_boundaryMap {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (b : FirstHurewicz.Chains A 2) (f : C(A, Fin 3 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 3)) :
    FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 3 → (unitInterval)) 2
          a (FirstHurewicz.inducedChain f 2 b)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) 3
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) A 2 a b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (BasedLoopSpace x)) f 2 a
      b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 3).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) 3))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.evaluated_triangle_boundaryMap {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2)
    (b : FirstHurewicz.Chains A 2) (f : C(A, Fin 3 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 3)) :
    FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 3 → (unitInterval)) 2 a (FirstHurewicz.inducedChain f 2 b)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) 4
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) A 2 a b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductTriangle_natural (ContinuousMap.id (BasedLoopSpace x)) f
      2 a b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 4).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) 4))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FourthHurewicz.evaluated_edge_cubeBoundary_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 3 → (unitInterval)) 2
          a
          (((FirstHurewicz.singularComplex (Fin 3 → (unitInterval))).d 3 2).hom
            ThirdHurewicz.fundamentalCubeChain)) =
      0 := by
  have hF (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a SecondHurewicz.fundamentalSquareChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a SecondHurewicz.productSquareChain
      (remainingCubeSide (ThirdHurewicz.squareSideLeft t))
      (remainingCubeSide_boundary _ (ThirdHurewicz.squareSideLeft_boundary t ht))
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a SecondHurewicz.productSquareChain
      (remainingCubeSide (ThirdHurewicz.squareSideRight t))
      (remainingCubeSide_boundary _ (ThirdHurewicz.squareSideRight_boundary t ht))
  simp only [remainingCubeChain_boundary, map_sub, hF 1 (Or.inr rfl), hF 0 (Or.inl rfl),
    hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FourthHurewicz.evaluated_triangle_cubeBoundary_cancel {X : Type} [TopologicalSpace X]
    (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 3 → (unitInterval)) 2 a
          (((FirstHurewicz.singularComplex (Fin 3 → (unitInterval))).d 3 2).hom
            ThirdHurewicz.fundamentalCubeChain)) =
      0 := by
  have hF (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a SecondHurewicz.fundamentalSquareChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a SecondHurewicz.productSquareChain
      (remainingCubeSide (ThirdHurewicz.squareSideLeft t))
      (remainingCubeSide_boundary _ (ThirdHurewicz.squareSideLeft_boundary t ht))
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a SecondHurewicz.productSquareChain
      (remainingCubeSide (ThirdHurewicz.squareSideRight t))
      (remainingCubeSide_boundary _ (ThirdHurewicz.squareSideRight_boundary t ht))
  simp only [remainingCubeChain_boundary, map_sub, hF 1 (Or.inr rfl), hF 0 (Or.inl rfl),
    hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FourthHurewicz.suspensionOne {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 1 →ₗ[ℤ] FirstHurewicz.Chains X 4 :=
  (FirstHurewicz.inducedChain (evaluation x) 4).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 3 → (unitInterval)) 3)
      ThirdHurewicz.fundamentalCubeChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem FourthHurewicz.suspensionOne_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    suspensionOne x a =
      FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 3 → (unitInterval)) 3
          a ThirdHurewicz.fundamentalCubeChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FourthHurewicz.suspensionTwo {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 2 →ₗ[ℤ] FirstHurewicz.Chains X 5 :=
  (FirstHurewicz.inducedChain (evaluation x) 5).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (Fin 3 → (unitInterval))
        3)
      ThirdHurewicz.fundamentalCubeChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem FourthHurewicz.suspensionTwo_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a =
      FirstHurewicz.inducedChain (evaluation x) 5
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 3 → (unitInterval)) 3 a ThirdHurewicz.fundamentalCubeChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FourthHurewicz.boundaryFour_suspensionOne_of_cycle {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (ha : FirstHurewicz.boundaryOne (BasedLoopSpace x) a = 0) :
    ((FirstHurewicz.singularComplex X).d 4 3).hom (suspensionOne x a) = 0 := by
  rw [suspensionOne_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary 2]
  change
    FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductZeroLeft (BasedLoopSpace x)
            (Fin 3 → (unitInterval)) 3 (FirstHurewicz.boundaryOne (BasedLoopSpace x) a)
            ThirdHurewicz.fundamentalCubeChain -
          PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 3 → (unitInterval)) 2
            a
            (((FirstHurewicz.singularComplex (Fin 3 → (unitInterval))).d 3 2).hom
              ThirdHurewicz.fundamentalCubeChain)) =
      0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg, evaluated_edge_cubeBoundary_cancel,
    neg_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.boundaryFive_suspensionTwo {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    ((FirstHurewicz.singularComplex X).d 5 4).hom (suspensionTwo x a) =
      suspensionOne x (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductTriangle_boundary 2]
  change
    FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 3 → (unitInterval)) 3
            (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) ThirdHurewicz.fundamentalCubeChain +
          PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
            (Fin 3 → (unitInterval)) 2 a
            (((FirstHurewicz.singularComplex (Fin 3 → (unitInterval))).d 3 2).hom
              ThirdHurewicz.fundamentalCubeChain)) =
      _
  rw [map_add, evaluated_triangle_cubeBoundary_cancel, add_zero]
  rfl

private def FourthHurewicz.pathCubeCycle {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 4
    (suspensionOne x (FirstHurewicz.pathChain p))
    (boundaryFour_suspensionOne_of_cycle x (FirstHurewicz.pathChain p)
      (FirstHurewicz.boundaryOne_loop p))

@[simp]
private theorem FourthHurewicz.pathCubeCycle_val {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathCubeCycle x p).1 = suspensionOne x (FirstHurewicz.pathChain p) :=
  rfl

private def FourthHurewicz.pathCubeClass {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.SingularHomology X 4 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
    (pathCubeCycle x p)

private theorem FourthHurewicz.pathCube_homotopy_boundary {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((FirstHurewicz.singularComplex X).d 5 4).hom
        (suspensionTwo x (FirstHurewicz.homotopyChain H)) =
      (pathCubeCycle x p).1 - (pathCubeCycle x q).1 := by
  rw [boundaryFive_suspensionTwo, FirstHurewicz.boundaryTwo_loopHomotopy, map_sub]
  rfl

private theorem FourthHurewicz.pathCubeClass_homotopy {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathCubeClass x p = pathCubeClass x q :=
  (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 4 _
        _).mpr
    ⟨suspensionTwo x (FirstHurewicz.homotopyChain H), pathCube_homotopy_boundary x H⟩

private theorem FourthHurewicz.pathCubeClass_homotopic {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathCubeClass x p = pathCubeClass x q := by
  obtain ⟨H⟩ := h
  exact pathCubeClass_homotopy x H

@[simp]
private theorem FourthHurewicz.pathCubeClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathCubeClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        4 _).mpr
  refine
    ⟨suspensionTwo x (FirstHurewicz.constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundaryFive_suspensionTwo, FirstHurewicz.boundaryTwo_constantTriangleChain]
  rfl

private theorem FourthHurewicz.pathCube_concat_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((FirstHurewicz.singularComplex X).d 5 4).hom
        (-suspensionTwo x (FirstHurewicz.concatChain p q)) =
      (pathCubeCycle x (p.trans q)).1 - ((pathCubeCycle x p).1 + (pathCubeCycle x q).1) := by
  rw [map_neg, boundaryFive_suspensionTwo, FirstHurewicz.boundaryTwo_concatChain, map_add,
    map_sub]
  simp only [pathCubeCycle_val]
  abel

private theorem FourthHurewicz.pathCubeClass_trans {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathCubeClass x (p.trans q) = pathCubeClass x p + pathCubeClass x q := by
  unfold pathCubeClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 4 _
        _).mpr
  exact ⟨-suspensionTwo x (FirstHurewicz.concatChain p q), pathCube_concat_boundary x p q⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FourthHurewicz.productCubeChain :
    FirstHurewicz.Chains ((unitInterval) × (Fin 3 → (unitInterval))) 4 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 3 → (unitInterval)) 3
    SecondHurewicz.intervalChain ThirdHurewicz.fundamentalCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FourthHurewicz.fundamentalCubeChain : FirstHurewicz.Chains (Fin 4 → (unitInterval)) 4 :=
  FirstHurewicz.inducedChain cubeCoordinates 4 productCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.suspensionOne_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 4) X x) :
    suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 4) p)) =
      FirstHurewicz.inducedChain (cubeMap p) 4 productCubeChain := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural
      (GenLoop.toLoop (0 : Fin 4) p).toContinuousMap (ContinuousMap.id (Fin 3 → (unitInterval))) 3
      SecondHurewicz.intervalChain ThirdHurewicz.fundamentalCubeChain
  rw [SecondHurewicz.induced_intervalChain, FirstHurewicz.inducedChain_id,
    LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 4).comp
          (FirstHurewicz.inducedChain
            ((GenLoop.toLoop (0 : Fin 4) p).toContinuousMap.prodMap
              (ContinuousMap.id (Fin 3 → (unitInterval))))
            4))
        productCubeChain =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_toLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    FourthHurewicz.cubeChain {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) :
    FirstHurewicz.Chains X 4 :=
  suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 4) p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.cubeChain_eq_induced {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 4) X x) :
    cubeChain p = FirstHurewicz.inducedChain p.val 4 fundamentalCubeChain := by
  rw [cubeChain, suspensionOne_toLoop]
  change
    FirstHurewicz.inducedChain (p.val.comp cubeCoordinates) 4 productCubeChain =
      ((FirstHurewicz.inducedChain p.val 4).comp (FirstHurewicz.inducedChain cubeCoordinates 4))
        productCubeChain
  rw [FirstHurewicz.inducedChain_comp]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    FourthHurewicz.cubeCycle {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4 :=
  pathCubeCycle x (GenLoop.toLoop (0 : Fin 4) p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FourthHurewicz.cubeHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 4) X x) : SingularMayerVietoris.SingularHomology X 4 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
    (cubeCycle p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FourthHurewicz.cubeHomologyClass_eq_pathCubeClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 4) X x) :
    cubeHomologyClass p = pathCubeClass x (GenLoop.toLoop (0 : Fin 4) p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.cubeHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 4) X x} (h : GenLoop.Homotopic p q) :
    cubeHomologyClass p = cubeHomologyClass q :=
  pathCubeClass_homotopic x (GenLoop.homotopicTo (0 : Fin 4) h)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.toLoop_const {X : Type} [TopologicalSpace X] {x : X} :
    GenLoop.toLoop (0 : Fin 4) (GenLoop.const : GenLoop (Fin 4) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem FourthHurewicz.cubeHomologyClass_const {X : Type} [TopologicalSpace X] {x : X} :
    cubeHomologyClass (GenLoop.const : GenLoop (Fin 4) X x) = 0 := by
  rw [cubeHomologyClass_eq_pathCubeClass, toLoop_const, pathCubeClass_refl]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.toLoop_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 4) X x) :
    GenLoop.toLoop (0 : Fin 4) (GenLoop.transAt (0 : Fin 4) p q) =
      (GenLoop.toLoop (0 : Fin 4) p).trans (GenLoop.toLoop (0 : Fin 4) q) := by
  have h :=
    congrArg (GenLoop.toLoop (0 : Fin 4))
      (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 4)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.cubeHomologyClass_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 4) X x) :
    cubeHomologyClass (GenLoop.transAt (0 : Fin 4) p q) =
      cubeHomologyClass p + cubeHomologyClass q := by
  simp only [cubeHomologyClass_eq_pathCubeClass, toLoop_transAt, pathCubeClass_trans]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.CubeSubdivision.evalLeft_crossProductEdge_curryLoop {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) (n : ℕ)
    (b : FirstHurewicz.Chains (Fin 3 → (unitInterval)) n) :
    FirstHurewicz.inducedChain (evalLeft X) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) n
          SecondHurewicz.intervalChain (FirstHurewicz.inducedChain (curryLoop p).val n b)) =
      FirstHurewicz.inducedChain (FourthHurewicz.cubeMap p) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 3 → (unitInterval)) n
          SecondHurewicz.intervalChain b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval))
      (curryLoop p).val n SecondHurewicz.intervalChain b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evalLeft X) (n + 1)).comp
          (FirstHurewicz.inducedChain
            ((ContinuousMap.id (unitInterval)).prodMap (curryLoop p).val) (n + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evalLeft_comp_curryLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.CubeSubdivision.cubeChain_eq_curriedCrossProduct {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) :
    FourthHurewicz.cubeChain p =
      FirstHurewicz.inducedChain (evalLeft X) 4
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) 3
          SecondHurewicz.intervalChain (ThirdHurewicz.cubeChain (curryLoop p))) := by
  rw [ThirdHurewicz.cubeChain_eq_induced, evalLeft_crossProductEdge_curryLoop,
    FourthHurewicz.cubeChain_eq_induced, FourthHurewicz.fundamentalCubeChain]
  change
    (FirstHurewicz.inducedChain p.val 4)
        ((FirstHurewicz.inducedChain FourthHurewicz.cubeCoordinates 4)
          FourthHurewicz.productCubeChain) =
      (FirstHurewicz.inducedChain (p.val.comp FourthHurewicz.cubeCoordinates) 4)
        FourthHurewicz.productCubeChain
  rw [FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def FourthHurewicz.CubeSubdivision.intervalTetrahedronChain {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 3)) : FirstHurewicz.Chains X 4 :=
  FirstHurewicz.inducedChain (evalLeft X) 4
    (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) 3
      SecondHurewicz.intervalChain
      (FirstHurewicz.simplexChain C((unitInterval), X) 3
        ((curryLoop p).val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.CubeSubdivision.intervalTetrahedronChain_eq_original {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 3)) :
    intervalTetrahedronChain p e =
      FirstHurewicz.inducedChain (FourthHurewicz.cubeMap p) 4
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 3 → (unitInterval)) 3
          SecondHurewicz.intervalChain
          (FirstHurewicz.simplexChain (Fin 3 → (unitInterval)) 3
            (ThirdHurewicz.Geometry.cubeTetrahedron e))) := by
  rw [intervalTetrahedronChain, ← FirstHurewicz.inducedChain_simplex,
    evalLeft_crossProductEdge_curryLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FourthHurewicz.CubeSubdivision.cubeChain_eq_sum_prisms {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 4) X x) :
    FourthHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 3),
        ThirdHurewicz.Geometry.cubeOrientation e • intervalTetrahedronChain p e := by
  rw [cubeChain_eq_curriedCrossProduct, ThirdHurewicz.CubeSubdivision.cubeChain_eq_sum_tetrahedra]
  simp only [map_sum, map_zsmul, intervalTetrahedronChain]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.CubeSubdivision.prismCubeRealization_eq_induced {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) (m : ℕ) :
    prismCubeRealization p e m =
      (FirstHurewicz.inducedChain (p.comp (prismCubeMap e)) m).comp
        ((PeriodTorusHigherHomology.productAffineChainMap 1 n m).comp
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.stdVertices 1) (SingularMayerVietoris.stdVertices n))
            (m + 1))) := by
  apply SingularMayerVietoris.formalChains_ext
  intro v
  simp only [prismCubeRealization_simplex, LinearMap.comp_apply,
    SingularMayerVietoris.formalMap_simplex,
    PeriodTorusHigherHomology.productAffineChainMap_simplex, FirstHurewicz.inducedChain_simplex]
  apply congrArg (FirstHurewicz.simplexChain X m)
  change
    p.comp (prismCubeSimplex e v) =
      p.comp
        ((prismCubeMap e).comp
          (PeriodTorusHigherHomology.productAffineSimplex
            (fun j =>
              (SingularMayerVietoris.stdVertices 1 (v j).1,
                SingularMayerVietoris.stdVertices n (v j).2))))
  rw [prismCubeMap_affine]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.CubeSubdivision.prismCubeRealization_edgeCrossProduct {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) :
    prismCubeRealization p e (n + 1)
        (PeriodTorusHigherHomology.formalEdgeCrossProduct n
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin (n + 1) => j))) =
      FirstHurewicz.inducedChain (p.comp (prismCubeMap e)) (n + 1)
        (PeriodTorusHigherHomology.productAffineChainMap 1 n (n + 1)
          (PeriodTorusHigherHomology.formalEdgeCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) := by
  rw [prismCubeRealization_eq_induced]
  simp only [LinearMap.comp_apply]
  rw [PeriodTorusHigherHomology.formalMap_edgeCrossProduct]
  simp only [SingularMayerVietoris.formalMap_simplex, Function.comp_def]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem FourthHurewicz.CubeSubdivision.prismCubeMap_three (e : Equiv.Perm (Fin 3)) :
    FourthHurewicz.cubeCoordinates.comp
        ((FirstHurewicz.pathSimplex Path.id).prodMap (ThirdHurewicz.Geometry.cubeTetrahedron e)) =
      prismCubeMap e := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact FourthHurewicz.cubeCoordinates_zero _
  · change
      FourthHurewicz.cubeCoordinates
          (FirstHurewicz.pathSimplex Path.id z.1, ThirdHurewicz.Geometry.cubeTetrahedron e z.2)
          j.succ =
        _
    rw [FourthHurewicz.cubeCoordinates_succ]
    rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    FourthHurewicz.CubeSubdivision.intervalTetrahedronChain_eq_prismCubeRealization {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 3)) :
    intervalTetrahedronChain p e =
      prismCubeRealization p.val e 4
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 3
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 4 => j))) := by
  rw [intervalTetrahedronChain_eq_original, SecondHurewicz.intervalChain, FirstHurewicz.pathChain,
    PeriodTorusHigherHomology.crossProductEdge_simplex, prismCubeRealization_edgeCrossProduct]
  change
    ((FirstHurewicz.inducedChain (FourthHurewicz.cubeMap p) 4).comp
          (FirstHurewicz.inducedChain
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (ThirdHurewicz.Geometry.cubeTetrahedron e))
            4))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  change
    FirstHurewicz.inducedChain
        (p.val.comp
          (FourthHurewicz.cubeCoordinates.comp
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (ThirdHurewicz.Geometry.cubeTetrahedron e))))
        4 _ =
      _
  rw [prismCubeMap_three]

private def FourthHurewicz.CubeSubdivision.badPrism (q m : ℕ) :
    Submodule ℤ (SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m) :=
  SingularMayerVietoris.formalChainsSupported {z | z.1 = 0} m ⊔
    ⨆ i : { i : Fin (q + 1) // i ≠ 0 },
      SingularMayerVietoris.formalChainsSupported {z | z.2 ≠ i.val} m

private theorem FourthHurewicz.CubeSubdivision.mem_badPrism_of_left_zero {q m : ℕ}
    {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m}
    (hc : c ∈ SingularMayerVietoris.formalChainsSupported {z | z.1 = 0} m) : c ∈ badPrism q m :=
  Submodule.mem_sup_left hc

private theorem FourthHurewicz.CubeSubdivision.mem_badPrism_of_omit {q m : ℕ} (i : Fin (q + 1))
    (hi : i ≠ 0) {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m}
    (hc : c ∈ SingularMayerVietoris.formalChainsSupported {z | z.2 ≠ i} m) : c ∈ badPrism q m :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ⟨i, hi⟩ hc)

private theorem FourthHurewicz.CubeSubdivision.badPrism_le {q m : ℕ}
    {P : Submodule ℤ (SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m)}
    (hzero : SingularMayerVietoris.formalChainsSupported {z | z.1 = 0} m ≤ P)
    (homit :
      ∀ i : Fin (q + 1),
        i ≠ 0 → SingularMayerVietoris.formalChainsSupported {z | z.2 ≠ i} m ≤ P) :
    badPrism q m ≤ P :=
  sup_le hzero (iSup_le fun i => homit i.val i.property)

private theorem
    FourthHurewicz.CubeSubdivision.badPrism_le_ker {q m : ℕ} {M : Type*} [AddCommGroup M]
    [Module ℤ M] (f : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m →ₗ[ℤ] M)
    (hzero : ∀ v, (∀ j, (v j).1 = 0) → f (SingularMayerVietoris.formalSimplex v) = 0)
    (homit :
      ∀ i : Fin (q + 1),
        i ≠ 0 → ∀ v, (∀ j, (v j).2 ≠ i) → f (SingularMayerVietoris.formalSimplex v) = 0) :
    badPrism q m ≤ LinearMap.ker f := by
  apply badPrism_le
  · exact SingularMayerVietoris.formalChainsSupported_le hzero
  · intro i hi
    exact SingularMayerVietoris.formalChainsSupported_le (homit i hi)

private theorem FourthHurewicz.CubeSubdivision.formalCone_mem_badPrism {q m : ℕ}
    {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m} (hc : c ∈ badPrism q m) :
    SingularMayerVietoris.formalCone (0, 0) m c ∈ badPrism q (m + 1) := by
  have hle :
    badPrism q m ≤ (badPrism q (m + 1)).comap (SingularMayerVietoris.formalCone (0, 0) m) := by
    apply badPrism_le
    · intro d hd
      exact
        mem_badPrism_of_left_zero
          (SingularMayerVietoris.formalCone_mem_supported (S :=
            {z : Fin 2 × Fin (q + 1) | z.1 = 0}) (a := (0, 0)) rfl hd)
    · intro i hi d hd
      exact
        mem_badPrism_of_omit i hi (SingularMayerVietoris.formalCone_mem_supported (Ne.symm hi) hd)
  exact hle hc

private theorem FourthHurewicz.CubeSubdivision.formalMap_succ_mem_badPrism {q m : ℕ}
    {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m} (hc : c ∈ badPrism q m) :
    SingularMayerVietoris.formalMap (Prod.map id (Fin.succ : Fin (q + 1) → Fin (q + 2))) m c ∈
      badPrism (q + 1) m := by
  have hle :
    badPrism q m ≤
      (badPrism (q + 1) m).comap
        (SingularMayerVietoris.formalMap (Prod.map id (Fin.succ : Fin (q + 1) → Fin (q + 2)))
          m) := by
    apply badPrism_le
    · intro d hd
      apply mem_badPrism_of_left_zero
      exact
        SingularMayerVietoris.formalMap_mem_supported (S := {z : Fin 2 × Fin (q + 1) | z.1 = 0})
          (T := {z : Fin 2 × Fin (q + 2) | z.1 = 0}) (Prod.map id Fin.succ) (fun _ hz => hz) hd
    · intro i hi d hd
      apply mem_badPrism_of_omit i.succ (Fin.succ_ne_zero i)
      exact
        SingularMayerVietoris.formalMap_mem_supported (S := {z : Fin 2 × Fin (q + 1) | z.2 ≠ i})
          (T := {z : Fin 2 × Fin (q + 2) | z.2 ≠ i.succ}) (Prod.map id Fin.succ)
          (fun _ hz h => hz (Fin.succ_injective _ h)) hd
  exact hle hc

private theorem FourthHurewicz.CubeSubdivision.formalEdgeCrossProduct_mem_badPrism_of_omit {q r : ℕ}
    (i : Fin (q + 1)) (hi : i ≠ 0) (c : SingularMayerVietoris.FormalChains (Fin 2) 2)
    {d : SingularMayerVietoris.FormalChains (Fin (q + 1)) (r + 1)}
    (hd : d ∈ SingularMayerVietoris.formalChainsSupported {j | j ≠ i} (r + 1)) :
    PeriodTorusHigherHomology.formalEdgeCrossProduct r c d ∈ badPrism q (r + 2) := by
  apply mem_badPrism_of_omit i hi
  apply
    SingularMayerVietoris.formalChainsSupported_mono (S :=
      (Set.univ : Set (Fin 2)) ×ˢ {j : Fin (q + 1) | j ≠ i}) (fun _ hz => hz.2)
  exact
    PeriodTorusHigherHomology.formalEdgeCrossProduct_mem_supported r (S := Set.univ) (by simp) hd

private def FourthHurewicz.CubeSubdivision.retainedFirstBoundary {W : Type*} (q : ℕ) :
    SingularMayerVietoris.FormalChains W (q + 2) →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W (q + 1) :=
  SingularMayerVietoris.formalLift fun w =>
    ∑ i : Fin (q + 1),
      (-1 : ℤ) ^ (i.val + 1) • SingularMayerVietoris.formalSimplex (w ∘ i.succ.succAbove)

@[simp]
private theorem FourthHurewicz.CubeSubdivision.retainedFirstBoundary_simplex {W : Type*} (q : ℕ)
    (w : Fin (q + 2) → W) :
    retainedFirstBoundary q (SingularMayerVietoris.formalSimplex w) =
      ∑ i : Fin (q + 1),
        (-1 : ℤ) ^ (i.val + 1) • SingularMayerVietoris.formalSimplex (w ∘ i.succ.succAbove) :=
  SingularMayerVietoris.formalLift_simplex _ _

private theorem
    FourthHurewicz.CubeSubdivision.formalBoundary_firstFace_split_simplex {W : Type*} (q : ℕ)
    (w : Fin (q + 2) → W) :
    SingularMayerVietoris.formalBoundary (q + 1) (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex (Fin.tail w) +
        retainedFirstBoundary q (SingularMayerVietoris.formalSimplex w) := by
  rw [SingularMayerVietoris.formalBoundary_simplex, Fin.sum_univ_succ,
    retainedFirstBoundary_simplex]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Fin.succAbove_zero]
  rfl

private def
    FourthHurewicz.CubeSubdivision.shufflePrismVertices {V W : Type*} {q : ℕ} (v : Fin 2 → V)
    (w : Fin (q + 1) → W) (i : Fin (q + 1)) : Fin (q + 2) → V × W := fun k =>
  (if k ≤ i.castSucc then v 0 else v 1, w (i.predAbove k))

@[simp]
private theorem FourthHurewicz.CubeSubdivision.shufflePrismVertices_first {V W : Type*} {q : ℕ}
    (v : Fin 2 → V) (w : Fin (q + 1) → W) (i : Fin (q + 1)) :
    shufflePrismVertices v w i 0 = (v 0, w 0) := by simp [shufflePrismVertices]

private theorem FourthHurewicz.CubeSubdivision.shufflePrismVertices_zero_index {V W : Type*} {q : ℕ}
    (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    shufflePrismVertices v w 0 = Fin.cons (v 0, w 0) (fun j => (v 1, w j)) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp [shufflePrismVertices]

private theorem FourthHurewicz.CubeSubdivision.shufflePrismVertices_succ_index {V W : Type*} {q : ℕ}
    (v : Fin 2 → V) (w : Fin (q + 2) → W) (i : Fin (q + 1)) :
    shufflePrismVertices v w i.succ =
      Fin.cons (v 0, w 0) (shufflePrismVertices v (Fin.tail w) i) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp [shufflePrismVertices, Fin.tail, Fin.le_castSucc_iff]

private theorem FourthHurewicz.CubeSubdivision.shufflePrismVertices_map {V W V' W' : Type*} {q : ℕ}
    (f : V → V') (g : W → W') (v : Fin 2 → V) (w : Fin (q + 1) → W) (i : Fin (q + 1)) :
    Prod.map f g ∘ shufflePrismVertices v w i = shufflePrismVertices (f ∘ v) (g ∘ w) i := by
  funext k
  simp only [shufflePrismVertices, Function.comp_apply, Prod.map_apply]
  split_ifs <;> rfl

private def FourthHurewicz.CubeSubdivision.standardPrism {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 1) → W) : SingularMayerVietoris.FormalChains (V × W) (q + 2) :=
  ∑ i : Fin (q + 1),
    (-1 : ℤ) ^ i.val • SingularMayerVietoris.formalSimplex (shufflePrismVertices v w i)

private theorem FourthHurewicz.CubeSubdivision.standardPrism_zero {V W : Type*} (v : Fin 2 → V)
    (w : Fin 1 → W) :
    standardPrism 0 v w = SingularMayerVietoris.formalSimplex (fun i => (v i, w 0)) := by
  rw [standardPrism, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, shufflePrismVertices_zero_index]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rw [Fin.eq_zero j]
    rfl

private theorem
    FourthHurewicz.CubeSubdivision.standardPrism_succ {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 2) → W) :
    standardPrism (q + 1) v w =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (SingularMayerVietoris.formalMap (fun z => (v 1, z)) (q + 2)
            (SingularMayerVietoris.formalSimplex w) -
          standardPrism q v (Fin.tail w)) := by
  rw [standardPrism, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, shufflePrismVertices_zero_index, map_sub,
    SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalCone_simplex,
    standardPrism, map_sum, map_smul, SingularMayerVietoris.formalCone_simplex]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, shufflePrismVertices_succ_index]

private theorem
    FourthHurewicz.CubeSubdivision.formalMap_standardPrism {V W V' W' : Type*} (f : V → V')
    (g : W → W') (q : ℕ) (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    SingularMayerVietoris.formalMap (Prod.map f g) (q + 2) (standardPrism q v w) =
      standardPrism q (f ∘ v) (g ∘ w) := by
  simp only [standardPrism, map_sum, map_smul, SingularMayerVietoris.formalMap_simplex,
    shufflePrismVertices_map]

private def FourthHurewicz.CubeSubdivision.prismDiscrepancy {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 1) → W) : SingularMayerVietoris.FormalChains (V × W) (q + 2) :=
  PeriodTorusHigherHomology.formalEdgeCrossProduct q (SingularMayerVietoris.formalSimplex v)
      (SingularMayerVietoris.formalSimplex w) -
    standardPrism q v w

@[simp]
private theorem FourthHurewicz.CubeSubdivision.prismDiscrepancy_zero {V W : Type*} (v : Fin 2 → V)
    (w : Fin 1 → W) : prismDiscrepancy 0 v w = 0 := by
  simp only [prismDiscrepancy,
    PeriodTorusHigherHomology.formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, standardPrism_zero, Function.comp_def, sub_self]

private theorem
    FourthHurewicz.CubeSubdivision.formalMap_prismDiscrepancy {V W V' W' : Type*} (f : V → V')
    (g : W → W') (q : ℕ) (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    SingularMayerVietoris.formalMap (Prod.map f g) (q + 2) (prismDiscrepancy q v w) =
      prismDiscrepancy q (f ∘ v) (g ∘ w) := by
  simp only [prismDiscrepancy, map_sub, PeriodTorusHigherHomology.formalMap_edgeCrossProduct,
    formalMap_standardPrism, SingularMayerVietoris.formalMap_simplex]

private def FourthHurewicz.CubeSubdivision.canonicalPrismDiscrepancy (q : ℕ) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) (q + 2) :=
  prismDiscrepancy q (fun i => i) (fun j => j)

@[simp]
private theorem FourthHurewicz.CubeSubdivision.canonicalPrismDiscrepancy_zero :
    canonicalPrismDiscrepancy 0 = 0 :=
  prismDiscrepancy_zero _ _

private theorem
    FourthHurewicz.CubeSubdivision.prismDiscrepancy_eq_map_canonical {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    prismDiscrepancy q v w =
      SingularMayerVietoris.formalMap (Prod.map v w) (q + 2) (canonicalPrismDiscrepancy q) := by
  simpa only [canonicalPrismDiscrepancy, Function.comp_def] using
    (formalMap_prismDiscrepancy v w q (fun i => i) (fun j => j)).symm

private theorem
    FourthHurewicz.CubeSubdivision.prismDiscrepancy_succ {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 2) → W) :
    prismDiscrepancy (q + 1) v w =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (-SingularMayerVietoris.formalMap (fun z => (v 0, z)) (q + 2)
                (SingularMayerVietoris.formalSimplex w) -
            PeriodTorusHigherHomology.formalEdgeCrossProduct q
              (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalBoundary (q + 1)
                (SingularMayerVietoris.formalSimplex w)) +
          standardPrism q v (Fin.tail w)) := by
  rw [prismDiscrepancy, PeriodTorusHigherHomology.formalEdgeCrossProduct_simplex_succ,
    PeriodTorusHigherHomology.formalPointCrossProduct_edge_boundary, standardPrism_succ]
  simp only [map_sub, map_add, map_neg]
  abel

private theorem FourthHurewicz.CubeSubdivision.prismDiscrepancy_succ_retained {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 2) → W) :
    prismDiscrepancy (q + 1) v w =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (-SingularMayerVietoris.formalMap (fun z => (v 0, z)) (q + 2)
                (SingularMayerVietoris.formalSimplex w) -
            prismDiscrepancy q v (Fin.tail w) -
          PeriodTorusHigherHomology.formalEdgeCrossProduct q
            (SingularMayerVietoris.formalSimplex v)
            (retainedFirstBoundary q (SingularMayerVietoris.formalSimplex w))) := by
  rw [prismDiscrepancy_succ, formalBoundary_firstFace_split_simplex, map_add, prismDiscrepancy]
  simp only [map_sub, map_add, map_neg]
  abel

private theorem FourthHurewicz.CubeSubdivision.canonicalPrismDiscrepancy_succ (q : ℕ) :
    canonicalPrismDiscrepancy (q + 1) =
      SingularMayerVietoris.formalCone ((0 : Fin 2), (0 : Fin (q + 2))) (q + 2)
        (-SingularMayerVietoris.formalSimplex (fun j : Fin (q + 2) => ((0 : Fin 2), j)) -
            SingularMayerVietoris.formalMap (Prod.map (fun i : Fin 2 => i) Fin.succ) (q + 2)
              (canonicalPrismDiscrepancy q) -
          ∑ i : Fin (q + 1),
            (-1 : ℤ) ^ (i.val + 1) •
              PeriodTorusHigherHomology.formalEdgeCrossProduct q
                (SingularMayerVietoris.formalSimplex (fun j : Fin 2 => j))
                (SingularMayerVietoris.formalSimplex i.succ.succAbove)) := by
  change prismDiscrepancy (q + 1) (fun i : Fin 2 => i) (fun j : Fin (q + 2) => j) = _
  rw [prismDiscrepancy_succ_retained, prismDiscrepancy_eq_map_canonical]
  simp only [retainedFirstBoundary_simplex, map_sum, map_smul,
    SingularMayerVietoris.formalMap_simplex, Function.comp_def]
  rfl

private theorem FourthHurewicz.CubeSubdivision.canonicalPrismDiscrepancy_mem_badPrism (q : ℕ) :
    canonicalPrismDiscrepancy q ∈ badPrism q (q + 2) := by
  induction q with
  | zero =>
    rw [canonicalPrismDiscrepancy_zero]
    exact Submodule.zero_mem _
  | succ q ih =>
    rw [canonicalPrismDiscrepancy_succ]
    apply formalCone_mem_badPrism
    apply Submodule.sub_mem
    · apply Submodule.sub_mem
      · apply Submodule.neg_mem
        exact
          mem_badPrism_of_left_zero
            (SingularMayerVietoris.formalSimplex_mem_supported fun _ => rfl)
      · exact formalMap_succ_mem_badPrism ih
    · apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      exact
        formalEdgeCrossProduct_mem_badPrism_of_omit i.succ (Fin.succ_ne_zero i) _
          (SingularMayerVietoris.formalSimplex_mem_supported fun j => Fin.succAbove_ne i.succ j)

private theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_left_zero {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x)
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).1 = 0) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  have hconst (e : Equiv.Perm (Fin (n + 2))) :
    p.val.comp (prismCubeSimplex e v) = ContinuousMap.const (FirstHurewicz.Simplex m) x := by
    ext s
    exact GenLoop.boundary p _ ⟨0, Or.inl (prismCubeSimplex_zero_of_left_zero e v hv s)⟩
  simp only [orientedPrismRealization_simplex, hconst]
  exact signed_sum_constant_eq_zero _

private theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_last_omitted {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x)
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).2 ≠ Fin.last (n + 2)) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  have hconst (e : Equiv.Perm (Fin (n + 2))) :
    p.val.comp (prismCubeSimplex e v) = ContinuousMap.const (FirstHurewicz.Simplex m) x := by
    ext s
    exact
      GenLoop.boundary p _
        ⟨(e (Fin.last (n + 1))).succ, Or.inl (prismCubeSimplex_zero_of_last_omitted e v hv s)⟩
  simp only [orientedPrismRealization_simplex, hconst]
  exact signed_sum_constant_eq_zero _

private theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_interior_omitted {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x) (i : Fin (n + 1))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).2 ≠ i.succ.castSucc) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  rw [orientedPrismRealization_simplex]
  apply
    signed_sum_eq_zero_of_swap_invariant i.castSucc i.succ
      (by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega)
  intro e
  exact
    congrArg (fun f => FirstHurewicz.simplexChain X m (p.val.comp f))
      (prismCubeSimplex_swap_of_omitted e i v hv).symm

private theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_nonzero_omitted {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x) (i : Fin (n + 3))
    (hi : i ≠ 0) (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).2 ≠ i) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  by_cases hlast : i = Fin.last (n + 2)
  · subst i
    exact orientedPrismRealization_last_omitted p v hv
  have hi0 : i.val ≠ 0 := by
    intro h
    exact hi (Fin.ext h)
  have hilast : i.val ≠ n + 2 := by
    intro h
    exact hlast (Fin.ext h)
  have hi_lt := i.isLt
  let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hj : j.succ.castSucc = i := by
    apply Fin.ext
    dsimp [j]
    omega
  apply orientedPrismRealization_interior_omitted p j v
  simpa only [hj] using hv

private theorem FourthHurewicz.CubeSubdivision.badPrism_le_ker_orientedPrismRealization {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin (n + 3)) X x) (m : ℕ) :
    badPrism (n + 2) (m + 1) ≤ LinearMap.ker (orientedPrismRealization p.val m) :=
  badPrism_le_ker _ (fun v hv => orientedPrismRealization_left_zero p v hv)
    (fun i hi v hv => orientedPrismRealization_nonzero_omitted p i hi v hv)

private theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_canonicalPrismDiscrepancy
    {X : Type} [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin (n + 3)) X x) :
    orientedPrismRealization p.val (n + 3) (canonicalPrismDiscrepancy (n + 2)) = 0 :=
  badPrism_le_ker_orientedPrismRealization p (n + 3)
    (canonicalPrismDiscrepancy_mem_badPrism (n + 2))

private theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_edge_eq_standard {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin (n + 3)) X x) :
    orientedPrismRealization p.val (n + 3)
        (PeriodTorusHigherHomology.formalEdgeCrossProduct (n + 2)
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin (n + 3) => j))) =
      orientedPrismRealization p.val (n + 3)
        (standardPrism (n + 2) (fun i : Fin 2 => i) (fun j : Fin (n + 3) => j)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact orientedPrismRealization_canonicalPrismDiscrepancy p

private theorem FourthHurewicz.CubeSubdivision.linearMap_zsmul_apply_mo1973_8057 {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N] (r : ℤ) (f : M →ₗ[ℤ] N) (a : M) :
    (r • f) a = r • f a :=
  map_zsmul (LinearMap.evalAddMonoidHom a) r f

private theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_eq_sum {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (m : ℕ) (c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (n + 1)) (m + 1)) :
    orientedPrismRealization p m c =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e • prismCubeRealization p e m c := by
  classical
  have h :
    orientedPrismRealization p m =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e • prismCubeRealization p e m := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [orientedPrismRealization_simplex, LinearMap.sum_apply,
      linearMap_zsmul_apply_mo1973_8057, prismCubeRealization_simplex]
  simpa only [LinearMap.sum_apply, linearMap_zsmul_apply_mo1973_8057] using
    LinearMap.congr_fun h c

private def FourthHurewicz.CubeSubdivision.PermutationInsertion.insert {n : ℕ} (k : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, e) * k.cycleRange

@[simp]
private theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_apply_self {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e k = 0 := by
  simp [FourthHurewicz.CubeSubdivision.PermutationInsertion.insert]

@[simp]
private theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_apply_succAbove {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (j : Fin n) :
    FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e (k.succAbove j) = (e j).succ :=
  by simp [FourthHurewicz.CubeSubdivision.PermutationInsertion.insert]

@[simp]
private theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_symm_apply_zero {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e).symm 0 = k := by
  apply (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e).injective
  simp

@[simp]
private theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_symm_apply_succ {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (j : Fin n) :
    (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e).symm j.succ =
      k.succAbove (e.symm j) := by
  apply (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e).injective
  simp

@[simp]
private theorem
    FourthHurewicz.CubeSubdivision.PermutationInsertion.sign_insert {n : ℕ} (k : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e) =
      (-1) ^ (k : ℕ) * Equiv.Perm.sign e := by
  simp [FourthHurewicz.CubeSubdivision.PermutationInsertion.insert, mul_comm]

private theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.sign_insert_int {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e) : ℤ) =
      (-1 : ℤ) ^ (k : ℕ) * (Equiv.Perm.sign e : ℤ) := by simp

private theorem
    FourthHurewicz.CubeSubdivision.lt_predAbove_iff_succAbove_lt {n : ℕ} (k : Fin (n + 1))
    (j : Fin n) (r : Fin (n + 2)) : j.val < (k.predAbove r).val ↔ (k.succAbove j).val < r.val := by
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

private theorem
    FourthHurewicz.CubeSubdivision.prismCubeVertex_shuffle {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) (r : Fin (n + 2)) :
    prismCubeVertex e (shufflePrismVertices (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j) k r) =
      HigherHurewicz.CubeTriangulation.cubeVertex (PermutationInsertion.insert k e) r := by
  funext coord
  refine Fin.cases ?_ (fun j => ?_) coord
  · by_cases h : r ≤ k.castSucc
    · have h' : ¬k.val < r.val := by
        simpa only [prismCubeVertex, Fin.le_def, Fin.val_castSucc, not_lt] using h
      simp [prismCubeVertex, shufflePrismVertices, h, HigherHurewicz.CubeTriangulation.cubeVertex,
        h', SingularMayerVietoris.stdVertices]
    · have h' : k.val < r.val := by
        simpa only [prismCubeVertex, Fin.le_def, Fin.val_castSucc, not_le] using h
      simp [prismCubeVertex, shufflePrismVertices, h, HigherHurewicz.CubeTriangulation.cubeVertex,
        h', SingularMayerVietoris.stdVertices]
  · simp only [shufflePrismVertices, prismCubeVertex_succ,
      HigherHurewicz.CubeTriangulation.cubeVertex, PermutationInsertion.insert_symm_apply_succ]
    simp only [lt_predAbove_iff_succAbove_lt]

private theorem
    FourthHurewicz.CubeSubdivision.prismCubeSimplex_shuffle {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) :
    prismCubeSimplex e (shufflePrismVertices (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j) k) =
      HigherHurewicz.CubeTriangulation.cubeSimplex (PermutationInsertion.insert k e) := by
  apply congrArg HigherHurewicz.CubeTriangulation.cubeAffineSimplex
  funext r
  exact prismCubeVertex_shuffle e k r

private theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_injective {n : ℕ} :
    Function.Injective
      (fun p : Fin (n + 1) × Equiv.Perm (Fin n) =>
        FourthHurewicz.CubeSubdivision.PermutationInsertion.insert p.1 p.2) := by
  rintro ⟨k, e⟩ ⟨l, f⟩ h
  have hk : k = l := by simpa using congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ.symm 0) h
  subst l
  refine Prod.ext rfl ?_
  apply Equiv.ext
  intro j
  apply Fin.succ_injective n
  simpa using congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ (k.succAbove j)) h

private theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_bijective {n : ℕ} :
    Function.Bijective
      (fun p : Fin (n + 1) × Equiv.Perm (Fin n) =>
        FourthHurewicz.CubeSubdivision.PermutationInsertion.insert p.1 p.2) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨insert_injective, by simp [Fintype.card_perm, Nat.factorial_succ]⟩

private theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.sum_insert {n : ℕ} {A : Type*}
    [AddCommMonoid A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          f (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), f σ := by
  rw [← Fintype.sum_prod_type']
  exact insert_bijective.sum_comp f

private theorem
    FourthHurewicz.CubeSubdivision.PermutationInsertion.sum_sign_insert {n : ℕ} {A : Type*}
    [AddCommGroup A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          ((-1 : ℤ) ^ (k : ℕ) * (Equiv.Perm.sign e : ℤ)) •
            f (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • f σ := by
  simpa only [sign_insert_int] using sum_insert (fun σ => (Equiv.Perm.sign σ : ℤ) • f σ)

private theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.sum_sign_smul_insert {n : ℕ}
    {A : Type*} [AddCommGroup A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          (-1 : ℤ) ^ (k : ℕ) •
            ((Equiv.Perm.sign e : ℤ) •
              f (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e))) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • f σ := by
  simpa only [SemigroupAction.mul_smul] using sum_sign_insert f

private theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_standardPrism {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X)) :
    orientedPrismRealization p (n + 1)
        (standardPrism n (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j)) =
      ∑ perm : Equiv.Perm (Fin (n + 1)),
        HigherHurewicz.CubeTriangulation.cubeOrientation perm •
          FirstHurewicz.simplexChain X (n + 1)
            (p.comp (HigherHurewicz.CubeTriangulation.cubeSimplex perm)) := by
  simp only [standardPrism, map_sum, map_zsmul, orientedPrismRealization_simplex,
    prismCubeSimplex_shuffle, ← Finset.sum_zsmul,
    HigherHurewicz.CubeTriangulation.cubeOrientation]
  exact
    PermutationInsertion.sum_sign_smul_insert
      (fun perm =>
        FirstHurewicz.simplexChain X (n + 1)
          (p.comp (HigherHurewicz.CubeTriangulation.cubeSimplex perm)))

private theorem FourthHurewicz.CubeSubdivision.cubeChain_eq_orientedPrismRealization {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) :
    FourthHurewicz.cubeChain p =
      orientedPrismRealization p.val 4
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 3
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 4 => j))) := by
  rw [cubeChain_eq_sum_prisms, orientedPrismRealization_eq_sum]
  simp only [intervalTetrahedronChain_eq_prismCubeRealization,
    ThirdHurewicz.Geometry.cubeOrientation, HigherHurewicz.CubeTriangulation.cubeOrientation]

private theorem
    FourthHurewicz.CubeSubdivision.cubeChain_eq_sum_simplices {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 4) X x) :
    FourthHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 4),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X 4
            (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  rw [cubeChain_eq_orientedPrismRealization, orientedPrismRealization_edge_eq_standard (n := 1) p,
    orientedPrismRealization_standardPrism]

private def FourthHurewicz.hurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    π_ 4 X x → SingularMayerVietoris.SingularHomology X 4 :=
  Quotient.lift cubeHomologyClass (fun _ _ h => cubeHomologyClass_homotopic h)

private def FourthHurewicz.hurewiczPi4 {X : Type} [TopologicalSpace X] (x : X) :
    π_ 4 X x →* Multiplicative (SingularMayerVietoris.SingularHomology X 4)
    where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (cubeHomologyClass_const (x := x))
  map_mul' a
    b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine
      (congrArg (fun c : π_ 4 X x => Multiplicative.ofAdd (hurewiczFunction x c))
            (HomotopyGroup.mul_spec (i := (0 : Fin 4)) (p := p) (q := q))).trans
        ?_
    change
      Multiplicative.ofAdd (cubeHomologyClass (GenLoop.transAt (0 : Fin 4) q p)) =
        Multiplicative.ofAdd (cubeHomologyClass p + cubeHomologyClass q)
    rw [cubeHomologyClass_transAt, add_comm]

private def FourthHurewicz.hurewiczMap {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ 4 X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 4
    where
  toFun := (hurewiczPi4 x).toAdditiveLeft
  map_add' := (hurewiczPi4 x).toAdditiveLeft.map_add
  map_smul' n a := by simpa using map_intCast_smul (hurewiczPi4 x).toAdditiveLeft ℤ ℤ n a

private theorem FourthHurewicz.hurewiczMap_representative {X : Type} [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin 4) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 4 X x)) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
        (cubeCycle p) :=
  rfl

private theorem
    FourthHurewicz.cubeChain_basedFourSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : cubeChain (basedFourSimplexLoop τ) = basedFourSimplexChain τ := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, basedFourSimplex_simplexChain_sum]

private theorem
    FourthHurewicz.cubeCycle_basedFourSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : cubeCycle (basedFourSimplexLoop τ) = basedFourSimplexCycle τ := by
  apply Subtype.ext
  exact cubeChain_basedFourSimplexLoop τ

private theorem
    FourthHurewicz.hurewicz_basedFourSimplexClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    hurewiczMap x (basedFourSimplexClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
        (basedFourSimplexCycle τ) := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
        (cubeCycle (basedFourSimplexLoop τ)) =
      _
  rw [cubeCycle_basedFourSimplexLoop]

private theorem
    FourthHurewicz.hurewiczMap_comp_fourSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    (hurewiczMap x).comp (fourSimplexClassOperator x) =
      (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4).comp
        (normalizedFourSimplexCycleOperator x) := by
  apply FirstHurewicz.chainMap_ext X 4
  intro smp
  simp only [LinearMap.comp_apply, fourSimplexClassOperator_simplex,
    normalizedFourSimplexCycleOperator_simplex]
  exact hurewicz_basedFourSimplexClass (normalizedFourSimplex x smp)

private theorem
    FourthHurewicz.hurewiczMap_fourSimplexClassOperator_cycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    hurewiczMap x (fourSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_fourSimplexClassOperator x) c.val
  change
    hurewiczMap x (fourSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
        (normalizedFourSimplexCycleOperator x c.val) at h
  exact h.trans (normalizedFourSimplexCycleOperator_class x c)

private def
    HigherHurewicz.CubicalBoundary.cubeFacet (n : ℕ) (i : Fin (n + 1)) (ε : (unitInterval)) :
    C(Fin n → (unitInterval), Fin (n + 1) → (unitInterval))
    where
  toFun u := Fin.insertNth (α := fun _ => (unitInterval)) i ε u
  continuous_toFun := by
    apply continuous_pi
    intro j
    refine Fin.succAboveCases i ?_ (fun k => ?_) j
    · simpa only [Fin.insertNth_apply_same] using
        (continuous_const : Continuous fun _ : Fin n → (unitInterval) => ε)
    · simpa only [Fin.insertNth_apply_succAbove] using
        (continuous_apply k : Continuous fun u : Fin n → (unitInterval) => u k)

@[simp]
private theorem HigherHurewicz.CubicalBoundary.cubeFacet_apply_self (n : ℕ) (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) : cubeFacet n i ε u i = ε :=
  Fin.insertNth_apply_same (α := fun _ => (unitInterval)) i ε u

@[simp]
private theorem HigherHurewicz.CubicalBoundary.cubeFacet_apply_succAbove (n : ℕ) (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) (j : Fin n) :
    cubeFacet n i ε u (i.succAbove j) = u j :=
  Fin.insertNth_apply_succAbove (α := fun _ => (unitInterval)) i ε u j

private def
    HigherHurewicz.SimplexGeometry.simplexTwoBoundary (n : ℕ) : Set (FirstHurewicz.Simplex n) :=
  {s | ∃ i j : Fin (n + 1), i ≠ j ∧ s i = 0 ∧ s j = 0}

private theorem HigherHurewicz.SimplexGeometry.simplexFace_simplexBoundary (n : ℕ) (i : Fin (n + 2))
    (s : FirstHurewicz.Simplex n) (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n) :
    FirstHurewicz.simplexFace n i s ∈ simplexTwoBoundary (n + 1) := by
  obtain ⟨j, hj⟩ := hs
  exact
    ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, FirstHurewicz.simplexFace_apply_self n i s,
      (FirstHurewicz.simplexFace_apply_succAbove n i s j).trans hj⟩

private theorem HigherHurewicz.SimplexGeometry.prefixMinimum_eq_zero_of_coordinate {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 0) (k : ℕ) (hik : i.val < k) :
    prefixMinimum u k = 0 :=
  le_antisymm (hi ▸ prefixMinimum_le_coordinate u k i hik) bot_le

private theorem HigherHurewicz.SimplexGeometry.simplexQuotient_last_eq_zero_of_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 0) :
    simplexQuotient n u (Fin.last n) = 0 := by
  rw [simplexQuotient_last, prefixMinimum_eq_zero_of_coordinate u i hi n i.isLt]
  rfl

private theorem HigherHurewicz.SimplexGeometry.simplexQuotient_castSucc_eq_zero_of_one {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 1) :
    simplexQuotient n u i.castSucc = 0 := by
  rw [simplexQuotient_castSucc, prefixMinimum_succ u i.val i.isLt]
  change
    (prefixMinimum u i.val : ℝ) - (Min.min (prefixMinimum u i.val) (u i) : (unitInterval)) = 0
  rw [hi, min_eq_left (show prefixMinimum u i.val ≤ 1 from (prefixMinimum u i.val).property.2)]
  exact sub_self _

private theorem
    HigherHurewicz.SimplexGeometry.simplexQuotient_castSucc_eq_zero_of_earlier_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (i j : Fin n) (hij : i < j) (hi : u i = 0) :
    simplexQuotient n u j.castSucc = 0 := by
  rw [simplexQuotient_castSucc, prefixMinimum_eq_zero_of_coordinate u i hi j.val hij,
    prefixMinimum_eq_zero_of_coordinate u i hi (j.val + 1)
      ((show i.val < j.val from hij).trans_le (Nat.le_succ j.val))]
  exact sub_self _

private theorem HigherHurewicz.SimplexGeometry.simplexQuotient_codimTwo {n : ℕ}
    (u : Fin n → (unitInterval))
    (hu : ∃ i j : Fin n, i ≠ j ∧ (u i = 0 ∨ u i = 1) ∧ (u j = 0 ∨ u j = 1)) :
    simplexQuotient n u ∈ simplexTwoBoundary n := by
  obtain ⟨i, j, hij, hi | hi, hj | hj⟩ := hu
  · rcases lt_or_gt_of_ne hij with hij' | hji'
    · exact
        ⟨j.castSucc, Fin.last n, Fin.castSucc_ne_last j,
          simplexQuotient_castSucc_eq_zero_of_earlier_zero u i j hij' hi,
          simplexQuotient_last_eq_zero_of_zero u i hi⟩
    · exact
        ⟨i.castSucc, Fin.last n, Fin.castSucc_ne_last i,
          simplexQuotient_castSucc_eq_zero_of_earlier_zero u j i hji' hj,
          simplexQuotient_last_eq_zero_of_zero u j hj⟩
  · exact
      ⟨j.castSucc, Fin.last n, Fin.castSucc_ne_last j,
        simplexQuotient_castSucc_eq_zero_of_one u j hj,
        simplexQuotient_last_eq_zero_of_zero u i hi⟩
  · exact
      ⟨i.castSucc, Fin.last n, Fin.castSucc_ne_last i,
        simplexQuotient_castSucc_eq_zero_of_one u i hi,
        simplexQuotient_last_eq_zero_of_zero u j hj⟩
  · exact
      ⟨i.castSucc, j.castSucc, fun h => hij (Fin.castSucc_injective n h),
        simplexQuotient_castSucc_eq_zero_of_one u i hi,
        simplexQuotient_castSucc_eq_zero_of_one u j hj⟩

private theorem HigherHurewicz.SimplexGeometry.simplexQuotient_bottom_not_last_twoBoundary (n : ℕ)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n) (u : Fin n → (unitInterval)) :
    simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n i 0 u) ∈
      simplexTwoBoundary (n + 1) := by
  have hil : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hi
  exact
    ⟨(Fin.last n).castSucc, Fin.last (n + 1), Fin.castSucc_ne_last _,
      simplexQuotient_castSucc_eq_zero_of_earlier_zero
        (HigherHurewicz.CubicalBoundary.cubeFacet n i 0 u) i (Fin.last n) hil
        (HigherHurewicz.CubicalBoundary.cubeFacet_apply_self n i 0 u),
      simplexQuotient_last_eq_zero_of_zero (HigherHurewicz.CubicalBoundary.cubeFacet n i 0 u) i
        (HigherHurewicz.CubicalBoundary.cubeFacet_apply_self n i 0 u)⟩

private def
    HigherHurewicz.SimplexGeometry.BasedSimplexBoundary (n : ℕ) {X : Type*} [TopologicalSpace X]
    (x : X) :=
  { τ : C(FirstHurewicz.Simplex n, X) // ∀ s ∈ simplexTwoBoundary n, τ s = x }

private def HigherHurewicz.SimplexGeometry.basedSimplexBoundaryFace {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) (i : Fin (n + 2)) : BasedSimplex n x :=
  ⟨τ.val.comp (FirstHurewicz.simplexFace n i), fun s hs =>
    τ.property _ (simplexFace_simplexBoundary n i s hs)⟩

private def
    HigherHurewicz.SimplexGeometry.BasedSimplexBoundary.ofFaces {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (τ : C(FirstHurewicz.Simplex (n + 1), X))
    (h :
      ∀ i : Fin (n + 2),
        ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n,
          (τ.comp (FirstHurewicz.simplexFace n i)) s = x) :
    HigherHurewicz.SimplexGeometry.BasedSimplexBoundary (n + 1) x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := SecondHurewicz.SimplyConnected.simplexFaceInverse n i ⟨s, hi⟩
    have ht : t ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (FirstHurewicz.simplexFace n i t) = x at he
    rw [show FirstHurewicz.simplexFace n i t = s from
        SecondHurewicz.SimplyConnected.simplexFace_inverse n i ⟨s, hi⟩] at he
    exact he⟩

private abbrev FourthHurewicz.BasedFiveSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplexBoundary 5 x

private abbrev FourthHurewicz.basedFiveSimplexFace {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) (i : Fin 6) : BasedFourSimplex x :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundaryFace τ i

private def FourthHurewicz.BasedFiveSimplex.ofFaces {X : Type*} [TopologicalSpace X] {x : X}
    (τ : C(FirstHurewicz.Simplex 5, X))
    (h :
      ∀ i : Fin 6,
        ∀ s ∈ FourthHurewicz.fourSimplexBoundary,
          (τ.comp (FirstHurewicz.simplexFace 4 i)) s = x) :
    FourthHurewicz.BasedFiveSimplex x :=
  HigherHurewicz.SimplexGeometry.BasedSimplexBoundary.ofFaces τ h

private def
    FourthHurewicz.normalizedFiveSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) : BasedFiveSimplex x :=
  BasedFiveSimplex.ofFaces (normalizedFiveSimplexMap x smp)
    (normalizedFiveSimplexMap_face_boundary x smp)

@[simp]
private theorem FourthHurewicz.normalizedFiveSimplex_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) (i : Fin 6) :
    basedFiveSimplexFace (normalizedFiveSimplex x smp) i =
      normalizedFourSimplex x (smp.comp (FirstHurewicz.simplexFace 4 i)) := by
  apply Subtype.ext
  exact normalizedFiveSimplexMap_face x smp i

private def HigherHurewicz.NativeSubdivision.nativeCubePair {N : Type*} (i j : N) :
    C(N → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun u := ![u i, u j]
  continuous_toFun := by
    apply continuous_pi
    intro k
    fin_cases k <;> exact continuous_apply _

private def
    HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap {N : Type*} [DecidableEq N]
    (i j : N) : C((unitInterval) × (N → (unitInterval)), N → (unitInterval))
    where
  toFun z
    k :=
    if k = i then
      SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, nativeCubePair i j z.2) 0
    else
      if k = j then
        SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, nativeCubePair i j z.2) 1
      else z.2 k
  continuous_toFun := by
    apply continuous_pi
    intro k
    by_cases hi : k = i
    · simp only [ite_eq_left hi]
      exact
        (continuous_apply (0 : Fin 2)).comp
          (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap.continuous.comp
            (continuous_fst.prodMk ((nativeCubePair i j).continuous.comp continuous_snd)))
    · by_cases hj : k = j
      · simp only [ite_eq_right hi, ite_eq_left hj]
        exact
          (continuous_apply (1 : Fin 2)).comp
            (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap.continuous.comp
              (continuous_fst.prodMk ((nativeCubePair i j).continuous.comp continuous_snd)))
      · simp only [ite_eq_right hi, ite_eq_right hj]
        exact (continuous_apply k).comp continuous_snd

@[simp]
private theorem HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap_zero {N : Type*}
    [DecidableEq N] (i j : N) (u : N → (unitInterval)) :
    nativeCubeQuarterTurnHomotopyMap i j (0, u) = u := by
  funext k
  change
    (if k = i then
        SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (0, nativeCubePair i j u) 0
      else
        if k = j then
          SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (0, nativeCubePair i j u) 1
        else u k) =
      u k
  simp only [SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_zero]
  change (if k = i then u i else if k = j then u j else u k) = u k
  split_ifs with hi hj <;> simp_all

@[simp]
private theorem HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap_one {N : Type*}
    [DecidableEq N] (i j : N) (u : N → (unitInterval)) :
    nativeCubeQuarterTurnHomotopyMap i j (1, u) = fun k =>
      if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k := by
  funext k
  simp [nativeCubeQuarterTurnHomotopyMap, nativeCubePair]

private theorem
    HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap_boundary {N : Type*}
    [DecidableEq N] (i j : N) (hij : i ≠ j) (t : (unitInterval)) (u : N → (unitInterval))
    (hu : u ∈ Cube.boundary N) : nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary N := by
  have hp (h : nativeCubePair i j u ∈ Cube.boundary (Fin 2)) :
    nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary N := by
    obtain ⟨k, hk⟩ :=
      SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary t (nativeCubePair i j u) h
    fin_cases k
    · exact ⟨i, by simpa [nativeCubeQuarterTurnHomotopyMap] using hk⟩
    · exact ⟨j, by simpa [nativeCubeQuarterTurnHomotopyMap, hij.symm] using hk⟩
  obtain ⟨k, hk⟩ := hu
  by_cases hi : k = i
  · subst k
    exact hp ⟨0, by simpa [nativeCubePair] using hk⟩
  · by_cases hj : k = j
    · subst k
      exact hp ⟨1, by simpa [nativeCubePair] using hk⟩
    · exact ⟨k, by simpa [nativeCubeQuarterTurnHomotopyMap, hi, hj] using hk⟩

private def HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnLoop {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    GenLoop N X x :=
  ⟨⟨fun u => p (nativeCubeQuarterTurnHomotopyMap i j (1, u)),
      p.val.continuous.comp
        ((nativeCubeQuarterTurnHomotopyMap i j).continuous.comp
          (continuous_const.prodMk continuous_id))⟩,
    fun u hu => p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij 1 u hu)⟩

@[simp]
private theorem HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnLoop_apply {N : Type*}
    [DecidableEq N] {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i j : N)
    (hij : i ≠ j) (u : N → (unitInterval)) :
    nativeCubeQuarterTurnLoop p i j hij u =
      p (fun k => if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k) := by
  change p (nativeCubeQuarterTurnHomotopyMap i j (1, u)) = _
  rw [nativeCubeQuarterTurnHomotopyMap_one]

private def
    HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopy {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    p.val.HomotopyRel (nativeCubeQuarterTurnLoop p i j hij).val (Cube.boundary N)
    where
  toFun z := p (nativeCubeQuarterTurnHomotopyMap i j z)
  continuous_toFun := p.val.continuous.comp (nativeCubeQuarterTurnHomotopyMap i j).continuous
  map_zero_left u := congrArg p (nativeCubeQuarterTurnHomotopyMap_zero i j u)
  map_one_left _ := rfl
  prop' t u
    hu :=
    (p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij t u hu)).trans
      (p.property u hu).symm

private abbrev HigherHurewicz.NativeSubdivision.NativeCube (N : Type*) :=
  N → (unitInterval)

private def HigherHurewicz.NativeSubdivision.nativeClass {N X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop N X x) : Additive (HomotopyGroup N X x) :=
  Additive.ofMul (⟦p⟧ : HomotopyGroup N X x)

private theorem
    HigherHurewicz.NativeSubdivision.nativeClass_homotopic {N X : Type*} [TopologicalSpace X]
    {x : X} {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) : nativeClass p = nativeClass q :=
  congrArg (fun a : HomotopyGroup N X x => Additive.ofMul a) (Quotient.sound h)

private theorem
    HigherHurewicz.NativeSubdivision.nativeClass_transAt {N X : Type*} [TopologicalSpace X]
    {x : X} [DecidableEq N] [Nontrivial N] (i : N) (p q : GenLoop N X x) :
    nativeClass (GenLoop.transAt i p q) = nativeClass p + nativeClass q :=
  congrArg Additive.ofMul
    ((HomotopyGroup.mul_spec (i := i) (p := q) (q := p)).symm.trans (mul_comm _ _))

private theorem
    HigherHurewicz.NativeSubdivision.nativeClass_symmAt {N X : Type*} [TopologicalSpace X]
    {x : X} [DecidableEq N] [Nonempty N] (i : N) (p : GenLoop N X x) :
    nativeClass (GenLoop.symmAt i p) = -nativeClass p :=
  congrArg Additive.ofMul (HomotopyGroup.inv_spec (i := i) (p := p)).symm

@[simp]
private theorem
    HigherHurewicz.NativeSubdivision.nativeClass_const {N X : Type*} [TopologicalSpace X]
    {x : X} [DecidableEq N] [Nonempty N] : nativeClass (GenLoop.const : GenLoop N X x) = 0 :=
  rfl

private def
    HigherHurewicz.NativeSubdivision.NativeCubeInternalBased {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) : Prop :=
  ∀ u : NativeCube N, ∀ i j : N, i ≠ j → u i = u j → p u = x

private inductive
    HigherHurewicz.NativeSubdivision.NativeCubeSameFlat {N : Type*} (a b : NativeCube N) :
    Prop
  | zero (i : N) (ha : a i = 0) (hb : b i = 0)
  | one (i : N) (ha : a i = 1) (hb : b i = 1)
  | equal (i j : N) (hij : i ≠ j) (ha : a i = a j) (hb : b i = b j)

private def HigherHurewicz.NativeSubdivision.nativeCubeBlend {N : Type*} (t : (unitInterval))
    (a b : NativeCube N) : NativeCube N := fun i => Set.Icc.convexComb (a i) (b i) t

@[simp]
private theorem
    HigherHurewicz.NativeSubdivision.nativeCubeBlend_zero {N : Type*} (a b : NativeCube N) :
    nativeCubeBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

@[simp]
private theorem
    HigherHurewicz.NativeSubdivision.nativeCubeBlend_one {N : Type*} (a b : NativeCube N) :
    nativeCubeBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

private def HigherHurewicz.NativeSubdivision.nativeCubeBlendMap {N : Type*}
    (f g : C(NativeCube N, NativeCube N)) : C((unitInterval) × NativeCube N, NativeCube N)
    where
  toFun u := nativeCubeBlend u.1 (f u.2) (g u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (f.continuous.comp continuous_snd)).prodMk
          (((continuous_apply i).comp (g.continuous.comp continuous_snd)).prodMk continuous_fst))

private theorem
    HigherHurewicz.NativeSubdivision.nativeCubeBlend_based {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (hp : NativeCubeInternalBased p) {a b : NativeCube N}
    (h : NativeCubeSameFlat a b) (t : (unitInterval)) : p (nativeCubeBlend t a b) = x := by
  cases h with
  | zero i ha hb => exact p.property _ ⟨i, Or.inl (by simp [nativeCubeBlend, ha, hb])⟩
  | one i ha hb => exact p.property _ ⟨i, Or.inr (by simp [nativeCubeBlend, ha, hb])⟩
  | equal i j hij ha hb => exact hp _ i j hij (by simp only [nativeCubeBlend, ha, hb])

private def
    HigherHurewicz.NativeSubdivision.nativeCubePullbackLoop {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (f : C(NativeCube N, NativeCube N))
    (hf : ∀ u ∈ Cube.boundary N, p (f u) = x) : GenLoop N X x :=
  ⟨p.val.comp f, hf⟩

private def
    HigherHurewicz.NativeSubdivision.nativeCubeLinearHomotopy {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (hp : NativeCubeInternalBased p)
    (f g : C(NativeCube N, NativeCube N)) (hf : ∀ u ∈ Cube.boundary N, p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary N, p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary N, NativeCubeSameFlat (f u) (g u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel (nativeCubePullbackLoop p g hg).val
      (Cube.boundary N)
    where
  toFun u := p (nativeCubeBlend u.1 (f u.2) (g u.2))
  continuous_toFun := p.val.continuous.comp (nativeCubeBlendMap f g).continuous
  map_zero_left
    u := by
    change p (nativeCubeBlend 0 (f u) (g u)) = p (f u)
    rw [nativeCubeBlend_zero]
  map_one_left
    u := by
    change p (nativeCubeBlend 1 (f u) (g u)) = p (g u)
    rw [nativeCubeBlend_one]
  prop' t u hu := (nativeCubeBlend_based p hp (hfg u hu) t).trans (hf u hu).symm

private def HigherHurewicz.NativeSubdivision.permuteCubeCoordinates {N : Type*} (e : Equiv.Perm N) :
    C(N → (unitInterval), N → (unitInterval))
    where
  toFun u i := u (e i)
  continuous_toFun := by fun_prop

private theorem HigherHurewicz.NativeSubdivision.permuteCubeCoordinates_boundary {N : Type*}
    (e : Equiv.Perm N) (u : N → (unitInterval)) (hu : u ∈ Cube.boundary N) :
    permuteCubeCoordinates e u ∈ Cube.boundary N := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨e.symm i, by simpa [permuteCubeCoordinates] using hi⟩

private def
    HigherHurewicz.NativeSubdivision.permuteCubeLoop {N : Type*} {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (e : Equiv.Perm N) : GenLoop N X x :=
  ⟨p.val.comp (permuteCubeCoordinates e), fun u hu =>
    p.property _ (permuteCubeCoordinates_boundary e u hu)⟩

@[simp]
private theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_apply {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (e : Equiv.Perm N) (u : N → (unitInterval)) :
    permuteCubeLoop p e u = p (fun i => u (e i)) :=
  rfl

@[simp]
private theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_one {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) : permuteCubeLoop p 1 = p := by
  apply GenLoop.ext
  intro u
  rfl

private theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_mul {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (e f : Equiv.Perm N) :
    permuteCubeLoop p (e * f) = permuteCubeLoop (permuteCubeLoop p f) e := by
  apply GenLoop.ext
  intro u
  rfl

private theorem
    HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnLoop_eq_symmAt_permute {N : Type*}
    {X : Type*} [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i j : N)
    (hij : i ≠ j) :
    nativeCubeQuarterTurnLoop p i j hij = GenLoop.symmAt i (permuteCubeLoop p (Equiv.swap i j)) :=
  by
  apply GenLoop.ext
  intro u
  rw [nativeCubeQuarterTurnLoop_apply]
  change
    p (fun k => if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k) =
      p
        (fun k =>
          if Equiv.swap i j k = i then (unitInterval.symm) (u i) else u (Equiv.swap i j k))
  congr 1
  funext k
  by_cases hi : k = i
  · subst k
    simp [hij.symm]
  · by_cases hj : k = j
    · subst k
      simp [hij.symm]
    · simp [hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj]

private theorem HigherHurewicz.NativeSubdivision.nativeClass_quarterTurn {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    nativeClass (nativeCubeQuarterTurnLoop p i j hij) = nativeClass p :=
  (nativeClass_homotopic ⟨nativeCubeQuarterTurnHomotopy p i j hij⟩).symm

private theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_swap_additiveClass {N : Type*}
    {X : Type*} [TopologicalSpace X] {x : X} [DecidableEq N] [Nontrivial N] (p : GenLoop N X x)
    (i j : N) (hij : i ≠ j) : nativeClass (permuteCubeLoop p (Equiv.swap i j)) = -nativeClass p :=
  by
  have h := nativeClass_quarterTurn p i j hij
  rw [nativeCubeQuarterTurnLoop_eq_symmAt_permute, nativeClass_symmAt] at h
  simpa only [neg_neg] using congrArg Neg.neg h

private theorem
    HigherHurewicz.NativeSubdivision.permuteCubeLoop_additiveClass {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] [Nontrivial N] [Fintype N] (p : GenLoop N X x)
    (e : Equiv.Perm N) :
    nativeClass (permuteCubeLoop p e) = ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeClass p := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul e i j hij
    ih =>
    rw [permuteCubeLoop_mul, permuteCubeLoop_swap_additiveClass _ i j hij, ih]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]

private def HigherHurewicz.CubicalBoundary.BasedCubicalCell (n : ℕ) {X : Type*} [TopologicalSpace X]
    (x : X) :=
  { F : C(Fin n → (unitInterval), X) //
    ∀ u i j, i ≠ j → (u i = 0 ∨ u i = 1) → (u j = 0 ∨ u j = 1) → F u = x }

private def
    HigherHurewicz.CubicalBoundary.cubicalFace {X : Type*} [TopologicalSpace X] {x : X} {n : ℕ}
    (F : BasedCubicalCell (n + 1) x) (i : Fin (n + 1)) (ε : (unitInterval)) (hε : ε = 0 ∨ ε = 1) :
    GenLoop (Fin n) X x :=
  ⟨F.val.comp (cubeFacet n i ε), fun u ⟨j, hj⟩ =>
    by
    apply F.property _ i (i.succAbove j) (Fin.ne_succAbove i j)
    · simpa only [cubeFacet_apply_self] using hε
    · simpa only [cubeFacet_apply_succAbove] using hj⟩

@[simp]
private theorem
    HigherHurewicz.CubicalBoundary.cubicalFace_apply {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (F : BasedCubicalCell (n + 1) x) (i : Fin (n + 1)) (ε : (unitInterval))
    (hε : ε = 0 ∨ ε = 1) (u : Fin n → (unitInterval)) :
    cubicalFace F i ε hε u = F.val (cubeFacet n i ε u) :=
  rfl

private abbrev
    HigherHurewicz.CubicalBoundary.cubicalLowerFace {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (F : BasedCubicalCell (n + 1) x) (i : Fin (n + 1)) : GenLoop (Fin n) X x :=
  cubicalFace F i 0 (Or.inl rfl)

private abbrev
    HigherHurewicz.CubicalBoundary.cubicalUpperFace {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (F : BasedCubicalCell (n + 1) x) (i : Fin (n + 1)) : GenLoop (Fin n) X x :=
  cubicalFace F i 1 (Or.inr rfl)

private structure
    HigherHurewicz.CubicalBoundary.CubicalEvaluator {X : Type*} [TopologicalSpace X] (n : ℕ)
    (x : X) (A : Type*) [AddCommGroup A] where
  evaluate : GenLoop (Fin n) X x → A
  map_const : evaluate GenLoop.const = 0
  map_homotopic : ∀ {p q}, GenLoop.Homotopic p q → evaluate p = evaluate q
  map_transAt : ∀ i p q, evaluate (GenLoop.transAt i p q) = evaluate p + evaluate q
  map_symmAt : ∀ i p, evaluate (GenLoop.symmAt i p) = -evaluate p
  map_swap :
    ∀ p i j,
      i ≠ j →
        evaluate (HigherHurewicz.NativeSubdivision.permuteCubeLoop p (Equiv.swap i j)) =
          -evaluate p

private instance HigherHurewicz.CubicalBoundary.instCoeFun1 {X : Type*} [TopologicalSpace X] {n : ℕ}
    {x : X} {A : Type*} [AddCommGroup A] :
    CoeFun (CubicalEvaluator n x A) (fun _ => GenLoop (Fin n) X x → A) :=
  ⟨CubicalEvaluator.evaluate⟩

private theorem HigherHurewicz.CubicalBoundary.CubicalEvaluator.map_permutation {X : Type*}
    [TopologicalSpace X] {n : ℕ} {x : X} {A : Type*} [AddCommGroup A]
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator n x A) (p : GenLoop (Fin n) X x)
    (e : Equiv.Perm (Fin n)) :
    E (HigherHurewicz.NativeSubdivision.permuteCubeLoop p e) =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • E p := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul e i j hij
    ih =>
    rw [HigherHurewicz.NativeSubdivision.permuteCubeLoop_mul, E.map_swap _ i j hij, ih]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]

private theorem HigherHurewicz.CubicalBoundary.CubicalEvaluator.map_finRotate {X : Type*}
    [TopologicalSpace X] {n : ℕ} {x : X} {A : Type*} [AddCommGroup A]
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator n x A) (p : GenLoop (Fin n) X x) :
    E (HigherHurewicz.NativeSubdivision.permuteCubeLoop p (finRotate n)) =
      (-1 : ℤ) ^ (n - 1) • E p := by
  rw [E.map_permutation, sign_finRotate]
  simp

private def
    HigherHurewicz.CubicalBoundary.cubicalBoundaryValue {X : Type*} [TopologicalSpace X] {n : ℕ}
    {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator n x A)
    (F : BasedCubicalCell (n + 1) x) : A :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • (E (cubicalUpperFace F i) - E (cubicalLowerFace F i))

private def
    HigherHurewicz.CubicalBoundary.nativeCubicalEvaluator {X : Type*} [TopologicalSpace X] (n : ℕ)
    (x : X) : CubicalEvaluator (n + 2) x (Additive (π_ (n + 2) X x))
    where
  evaluate := HigherHurewicz.NativeSubdivision.nativeClass
  map_const := HigherHurewicz.NativeSubdivision.nativeClass_const
  map_homotopic := HigherHurewicz.NativeSubdivision.nativeClass_homotopic
  map_transAt := HigherHurewicz.NativeSubdivision.nativeClass_transAt
  map_symmAt := HigherHurewicz.NativeSubdivision.nativeClass_symmAt
  map_swap := HigherHurewicz.NativeSubdivision.permuteCubeLoop_swap_additiveClass

private theorem HigherHurewicz.SimplexGeometry.succAbove_lt_prefix_iff_mo1973_8180 {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) (k : ℕ) (h : k ≤ i.val) : (i.succAbove j).val < k ↔ j.val < k :=
  by
  by_cases hji : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt i j hji]
    rfl
  · rw [Fin.succAbove_of_le_castSucc i j (le_of_not_gt hji)]
    simp only [Fin.lt_def, Fin.val_castSucc] at hji
    simp only [Fin.val_succ]
    omega

private theorem HigherHurewicz.SimplexGeometry.succAbove_lt_prefix_succ_iff_mo1973_8181 {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) (k : ℕ) (h : i.val ≤ k) :
    (i.succAbove j).val < k + 1 ↔ j.val < k := by
  by_cases hji : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt i j hji]
    simp only [Fin.lt_def, Fin.val_castSucc] at hji
    simp only [Fin.val_castSucc]
    omega
  · rw [Fin.succAbove_of_le_castSucc i j (le_of_not_gt hji)]
    simp only [Fin.val_succ, Nat.add_lt_add_iff_right]

private theorem HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_le {n : ℕ} (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) (k : ℕ) (h : k ≤ i.val) :
    prefixMinimum (Fin.insertNth i ε u) k = prefixMinimum u k := by
  apply eq_of_forall_le_iff
  intro a
  simp only [prefixMinimum, Finset.le_inf_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    succAbove_lt_prefix_iff_mo1973_8180 i _ k h, not_lt_of_ge h, false_implies, true_and]

private theorem
    HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_succ {n : ℕ} (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) (k : ℕ) (h : i.val ≤ k) :
    prefixMinimum (Fin.insertNth i ε u) (k + 1) = Min.min ε (prefixMinimum u k) := by
  apply eq_of_forall_le_iff
  intro a
  simp only [prefixMinimum, Finset.le_inf_iff, Finset.mem_filter, Finset.mem_univ, true_and,
    le_min_iff]
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    succAbove_lt_prefix_succ_iff_mo1973_8181 i _ k h, Nat.lt_succ_of_le h, true_implies]

private theorem
    HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_one_le {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → (unitInterval)) (k : ℕ) (h : k ≤ i.val) :
    prefixMinimum (Fin.insertNth i 1 u) k = prefixMinimum u k :=
  prefixMinimum_insertNth_le i 1 u k h

private theorem
    HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_one_succ {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → (unitInterval)) (k : ℕ) (h : i.val ≤ k) :
    prefixMinimum (Fin.insertNth i 1 u) (k + 1) = prefixMinimum u k := by
  rw [prefixMinimum_insertNth_succ i 1 u k h]
  exact min_eq_right (show prefixMinimum u k ≤ (⊤ : (unitInterval)) from le_top)

private theorem HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_last_le {n : ℕ}
    (u : Fin n → (unitInterval)) (ε : (unitInterval)) (k : ℕ) (hk : k ≤ n) :
    prefixMinimum (Fin.insertNth (Fin.last n) ε u) k = prefixMinimum u k :=
  prefixMinimum_insertNth_le (Fin.last n) ε u k hk

private theorem
    HigherHurewicz.SimplexGeometry.extendedMinimum_cubeFacet_one_le {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → (unitInterval)) (k : ℕ) (hk : k ≤ i.val) :
    extendedMinimum (HigherHurewicz.CubicalBoundary.cubeFacet n i 1 u) k = extendedMinimum u k := by
  have hkn : k ≤ n := hk.trans (Nat.le_of_lt_succ i.isLt)
  rw [extendedMinimum_of_le _ k (hkn.trans (Nat.le_succ n)), extendedMinimum_of_le u k hkn]
  exact prefixMinimum_insertNth_one_le i u k hk

private theorem HigherHurewicz.SimplexGeometry.extendedMinimum_cubeFacet_one_succ {n : ℕ}
    (i : Fin (n + 1)) (u : Fin n → (unitInterval)) (k : ℕ) (hk : i.val ≤ k) :
    extendedMinimum (HigherHurewicz.CubicalBoundary.cubeFacet n i 1 u) (k + 1) =
      extendedMinimum u k := by
  by_cases hkn : k ≤ n
  · rw [extendedMinimum_of_le _ (k + 1) (Nat.succ_le_succ hkn), extendedMinimum_of_le u k hkn]
    exact prefixMinimum_insertNth_one_succ i u k hk
  · simp only [extendedMinimum, ite_eq_right hkn,
      ite_eq_right (show ¬k + 1 ≤ n + 1 from fun h => hkn (Nat.succ_le_succ_iff.mp h))]

private theorem HigherHurewicz.SimplexGeometry.extendedMinimum_cubeFacet_last_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (k : ℕ) :
    extendedMinimum (HigherHurewicz.CubicalBoundary.cubeFacet n (Fin.last n) 0 u) k =
      extendedMinimum u k := by
  by_cases hkn : k ≤ n
  · rw [extendedMinimum_of_le _ k (hkn.trans (Nat.le_succ n)), extendedMinimum_of_le u k hkn]
    exact prefixMinimum_insertNth_last_le u 0 k hkn
  · by_cases hks : k ≤ n + 1
    · have hk : k = n + 1 := by omega
      subst k
      rw [extendedMinimum_of_le _ (n + 1) le_rfl, extendedMinimum_last_succ]
      change prefixMinimum (Fin.insertNth (Fin.last n) 0 u) (n + 1) = 0
      rw [prefixMinimum_insertNth_succ (Fin.last n) 0 u n le_rfl]
      exact min_eq_left (show (0 : (unitInterval)) ≤ prefixMinimum u n from bot_le)
    · simp only [extendedMinimum, ite_eq_right hkn, ite_eq_right hks]

private theorem HigherHurewicz.SimplexGeometry.simplexQuotient_cubeFacet_one_apply (n : ℕ)
    (i : Fin (n + 1)) (u : Fin n → (unitInterval)) :
    simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n i 1 u) =
      FirstHurewicz.simplexFace n i.castSucc (simplexQuotient n u) := by
  apply Subtype.ext
  funext k
  change
    simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n i 1 u) k =
      FirstHurewicz.simplexFace n i.castSucc (simplexQuotient n u) k
  refine Fin.succAboveCases i.castSucc ?_ (fun j => ?_) k
  · rw [FirstHurewicz.simplexFace_apply_self]
    exact
      simplexQuotient_castSucc_eq_zero_of_one _ i
        (HigherHurewicz.CubicalBoundary.cubeFacet_apply_self n i 1 u)
  · rw [FirstHurewicz.simplexFace_apply_succAbove]
    by_cases hji : j < i
    · rw [Fin.succAbove_of_castSucc_lt i.castSucc j (show j.castSucc < i.castSucc from hji)]
      simp only [simplexQuotient_apply, Fin.val_castSucc]
      rw [extendedMinimum_cubeFacet_one_le i u j.val (le_of_lt hji),
        extendedMinimum_cubeFacet_one_le i u (j.val + 1) (Nat.succ_le_of_lt hji)]
    · rw [Fin.succAbove_of_le_castSucc i.castSucc j
          (show i.castSucc ≤ j.castSucc from le_of_not_gt hji)]
      simp only [simplexQuotient_apply, Fin.val_succ]
      rw [extendedMinimum_cubeFacet_one_succ i u j.val (le_of_not_gt hji),
        extendedMinimum_cubeFacet_one_succ i u (j.val + 1)
          ((show i.val ≤ j.val from le_of_not_gt hji).trans (Nat.le_succ j.val))]

private theorem HigherHurewicz.SimplexGeometry.simplexQuotient_cubeFacet_last_zero_apply (n : ℕ)
    (u : Fin n → (unitInterval)) :
    simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n (Fin.last n) 0 u) =
      FirstHurewicz.simplexFace n (Fin.last (n + 1)) (simplexQuotient n u) := by
  apply Subtype.ext
  funext k
  change
    simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n (Fin.last n) 0 u) k =
      FirstHurewicz.simplexFace n (Fin.last (n + 1)) (simplexQuotient n u) k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [FirstHurewicz.simplexFace_apply_self]
    exact
      simplexQuotient_last_eq_zero_of_zero _ (Fin.last n)
        (HigherHurewicz.CubicalBoundary.cubeFacet_apply_self n (Fin.last n) 0 u)
  · rw [show j.castSucc = (Fin.last (n + 1)).succAbove j by simp,
      FirstHurewicz.simplexFace_apply_succAbove]
    simp only [Fin.succAbove_last, simplexQuotient_apply, Fin.val_castSucc,
      extendedMinimum_cubeFacet_last_zero]

private def
    HigherHurewicz.SimplexGeometry.simplexBoundaryCube {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplexBoundary n x) :
    HigherHurewicz.CubicalBoundary.BasedCubicalCell n x :=
  ⟨τ.val.comp (simplexQuotient n), fun u i j hij hi hj =>
    τ.property _ (simplexQuotient_codimTwo u ⟨i, j, hij, hi, hj⟩)⟩

private theorem
    HigherHurewicz.SimplexGeometry.simplexBoundaryCube_upper {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) (i : Fin (n + 1)) :
    HigherHurewicz.CubicalBoundary.cubicalUpperFace (simplexBoundaryCube τ) i =
      basedSimplexLoop (basedSimplexBoundaryFace τ i.castSucc) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n i 1 u)) =
      τ.val (FirstHurewicz.simplexFace n i.castSucc (simplexQuotient n u))
  rw [simplexQuotient_cubeFacet_one_apply]

private theorem HigherHurewicz.SimplexGeometry.simplexBoundaryCube_lower_last {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) :
    HigherHurewicz.CubicalBoundary.cubicalLowerFace (simplexBoundaryCube τ) (Fin.last n) =
      basedSimplexLoop (basedSimplexBoundaryFace τ (Fin.last (n + 1))) := by
  apply GenLoop.ext
  intro u
  change
    τ.val
        (simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n (Fin.last n) 0 u)) =
      τ.val (FirstHurewicz.simplexFace n (Fin.last (n + 1)) (simplexQuotient n u))
  rw [simplexQuotient_cubeFacet_last_zero_apply]

private theorem HigherHurewicz.SimplexGeometry.simplexBoundaryCube_lower_constant {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) (i : Fin (n + 1))
    (hi : i ≠ Fin.last n) :
    HigherHurewicz.CubicalBoundary.cubicalLowerFace (simplexBoundaryCube τ) i = GenLoop.const := by
  apply GenLoop.ext
  intro u
  exact τ.property _ (simplexQuotient_bottom_not_last_twoBoundary n i hi u)

private theorem HigherHurewicz.SimplexGeometry.simplexBoundaryCube_boundaryValue {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] {n : ℕ}
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator n x A)
    (τ : BasedSimplexBoundary (n + 1) x) :
    HigherHurewicz.CubicalBoundary.cubicalBoundaryValue E (simplexBoundaryCube τ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • E (basedSimplexLoop (basedSimplexBoundaryFace τ i)) :=
  by
  have hzero (i : Fin n) :
    E (HigherHurewicz.CubicalBoundary.cubicalLowerFace (simplexBoundaryCube τ) i.castSucc) = 0 := by
    rw [simplexBoundaryCube_lower_constant τ i.castSucc (Fin.castSucc_ne_last i)]
    exact E.map_const
  have hlower :
    (∑ i : Fin (n + 1),
        (-1 : ℤ) ^ i.val •
          E (HigherHurewicz.CubicalBoundary.cubicalLowerFace (simplexBoundaryCube τ) i)) =
      (-1 : ℤ) ^ n • E (basedSimplexLoop (basedSimplexBoundaryFace τ (Fin.last (n + 1)))) := by
    rw [Fin.sum_univ_castSucc]
    simp only [hzero, smul_zero, Finset.sum_const_zero, zero_add, Fin.val_last,
      simplexBoundaryCube_lower_last]
  unfold HigherHurewicz.CubicalBoundary.cubicalBoundaryValue
  simp_rw [simplexBoundaryCube_upper, smul_sub]
  rw [Finset.sum_sub_distrib, hlower]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, pow_succ', neg_mul, one_mul, neg_smul,
    sub_eq_add_neg]

private def HigherHurewicz.CubicalBoundary.whiskerStartTrack :
    Path ((0 : (unitInterval)), (0 : (unitInterval))) ((0 : (unitInterval)), (1 : (unitInterval)))
    where
  toFun s := (0, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

private def HigherHurewicz.CubicalBoundary.whiskerMiddleTrack :
    Path ((0 : (unitInterval)), (1 : (unitInterval))) ((1 : (unitInterval)), (1 : (unitInterval)))
    where
  toFun s := (s, 1)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

private def HigherHurewicz.CubicalBoundary.whiskerFinishTrack :
    Path ((1 : (unitInterval)), (0 : (unitInterval))) ((1 : (unitInterval)), (1 : (unitInterval)))
    where
  toFun s := (1, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

private def HigherHurewicz.CubicalBoundary.whiskerTrack :
    Path ((0 : (unitInterval)), (0 : (unitInterval)))
      ((1 : (unitInterval)), (0 : (unitInterval))) :=
  whiskerStartTrack.trans (whiskerMiddleTrack.trans whiskerFinishTrack.symm)

private theorem HigherHurewicz.CubicalBoundary.whiskerTrack_boundary (s : (unitInterval)) :
    ((whiskerTrack s).1 = 0 ∨ (whiskerTrack s).1 = 1) ∨ (whiskerTrack s).2 = 1 := by
  unfold whiskerTrack
  rw [Path.trans_apply]
  split_ifs
  · exact Or.inl (Or.inl rfl)
  · rw [Path.trans_apply]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (Or.inr rfl)

private def HigherHurewicz.CubicalBoundary.whiskerMap (n : ℕ) :
    C((Fin (n + 1) → (unitInterval)) × (unitInterval), Fin (n + 2) → (unitInterval))
    where
  toFun
    z :=
    Fin.cons (whiskerTrack z.2).1
      (Fin.snoc (Fin.init z.1) ((whiskerTrack z.2).2 * z.1 (Fin.last n)))
  continuous_toFun := by
    apply Continuous.finCons
    · exact (whiskerTrack.continuous.comp continuous_snd).fst
    · apply Continuous.finSnoc
      · apply continuous_pi
        intro i
        exact (continuous_apply i.castSucc).comp continuous_fst
      · apply Continuous.subtype_mk
        exact
          (continuous_subtype_val.comp (whiskerTrack.continuous.comp continuous_snd).snd).mul
            (continuous_subtype_val.comp ((continuous_apply (Fin.last n)).comp continuous_fst))

@[simp]
private theorem
    HigherHurewicz.CubicalBoundary.whiskerMap_apply (n : ℕ) (u : Fin (n + 1) → (unitInterval))
    (s : (unitInterval)) :
    whiskerMap n (u, s) =
      Fin.cons (whiskerTrack s).1 (Fin.snoc (Fin.init u) ((whiskerTrack s).2 * u (Fin.last n))) :=
  rfl

@[simp]
private theorem
    HigherHurewicz.CubicalBoundary.whiskerMap_first (n : ℕ) (u : Fin (n + 1) → (unitInterval))
    (s : (unitInterval)) : whiskerMap n (u, s) 0 = (whiskerTrack s).1 := by simp

@[simp]
private theorem HigherHurewicz.CubicalBoundary.whiskerMap_middle (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (i : Fin n) :
    whiskerMap n (u, s) i.castSucc.succ = u i.castSucc := by simp [Fin.init]

private theorem HigherHurewicz.CubicalBoundary.whiskerMap_start (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) :
    whiskerMap n (u, 0) = Fin.cons 0 (Fin.snoc (Fin.init u) 0) := by simp

private theorem HigherHurewicz.CubicalBoundary.whiskerMap_finish (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) :
    whiskerMap n (u, 1) = Fin.cons 1 (Fin.snoc (Fin.init u) 0) := by simp

private theorem HigherHurewicz.CubicalBoundary.whiskerMap_last_zero (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (hu : u (Fin.last n) = 0) :
    whiskerMap n (u, s) (Fin.last n).succ = 0 := by simp [hu]

private theorem HigherHurewicz.CubicalBoundary.whiskerCorner_based {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (ε : (unitInterval))
    (hε : ε = 0 ∨ ε = 1) (v : Fin n → (unitInterval)) : F.val (Fin.cons ε (Fin.snoc v 0)) = x := by
  apply F.property _ 0 (Fin.last n).succ (by simp)
  · simpa only [Fin.cons_zero] using hε
  · exact Or.inl (by simp)

private theorem HigherHurewicz.CubicalBoundary.whiskerMap_based_of_two_prefix {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (i j : Fin n) (hij : i ≠ j)
    (hi : u i.castSucc = 0 ∨ u i.castSucc = 1) (hj : u j.castSucc = 0 ∨ u j.castSucc = 1) :
    F.val (whiskerMap n (u, s)) = x := by
  apply F.property _ i.castSucc.succ j.castSucc.succ (by simpa using hij)
  · simpa only [whiskerMap_middle] using hi
  · simpa only [whiskerMap_middle] using hj

private theorem HigherHurewicz.CubicalBoundary.whiskerMap_based_of_prefix_last {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (i : Fin n)
    (hi : u i.castSucc = 0 ∨ u i.castSucc = 1) (hz : u (Fin.last n) = 0 ∨ u (Fin.last n) = 1) :
    F.val (whiskerMap n (u, s)) = x := by
  rcases hz with hz | hz
  · apply F.property _ i.castSucc.succ (Fin.last n).succ (by simp)
    · simpa only [whiskerMap_middle] using hi
    · exact Or.inl (whiskerMap_last_zero n u s hz)
  · rcases whiskerTrack_boundary s with ht | hr
    · apply F.property _ 0 i.castSucc.succ (Fin.succ_ne_zero i.castSucc).symm
      · simpa only [whiskerMap_first] using ht
      · simpa only [whiskerMap_middle] using hi
    · apply F.property _ i.castSucc.succ (Fin.last n).succ (by simp)
      · simpa only [whiskerMap_middle] using hi
      · exact Or.inr (by simp [hr, hz])

private theorem HigherHurewicz.CubicalBoundary.whiskerMap_codimTwo_based {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (i j : Fin (n + 1)) (hij : i ≠ j)
    (hi : u i = 0 ∨ u i = 1) (hj : u j = 0 ∨ u j = 1) : F.val (whiskerMap n (u, s)) = x := by
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j => exact whiskerMap_based_of_prefix_last F u s j hj hi
  | cast i =>
    cases j using Fin.lastCases with
    | last => exact whiskerMap_based_of_prefix_last F u s i hi hj
    | cast j => exact whiskerMap_based_of_two_prefix F u s i j (by simpa using hij) hi hj

private theorem HigherHurewicz.CubicalBoundary.cubeFacet_succ_cons (n : ℕ) (i : Fin (n + 1))
    (ε s : (unitInterval)) (u : Fin n → (unitInterval)) :
    cubeFacet (n + 1) i.succ ε (Fin.cons s u) = Fin.cons s (cubeFacet n i ε u) :=
  Fin.insertNth_succ_cons i ε s u

private theorem HigherHurewicz.CubicalBoundary.whiskerFacetNormal_arm_based {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (i : Fin (n + 1))
    (ε : (unitInterval)) (hε : ε = 0 ∨ ε = 1) (h : i ≠ Fin.last n ∨ ε = 0)
    (u : Fin n → (unitInterval)) (a : (unitInterval)) (ha : a = 0 ∨ a = 1) (r : (unitInterval)) :
    F.val
        (Fin.cons a
          (Fin.snoc (Fin.init (cubeFacet n i ε u)) (r * cubeFacet n i ε u (Fin.last n)))) =
      x := by
  cases i using Fin.lastCases with
  | last =>
    have hzero : ε = 0 := h.resolve_left (not_not_intro rfl)
    subst ε
    apply F.property _ 0 (Fin.last n).succ (by simp)
    · simpa only [Fin.cons_zero] using ha
    · exact Or.inl (by simp)
  | cast i =>
    apply F.property _ 0 i.castSucc.succ (Fin.succ_ne_zero i.castSucc).symm
    · simpa only [Fin.cons_zero] using ha
    · simpa [Fin.init] using hε

private def
    HigherHurewicz.CubicalBoundary.whiskeredLoop {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    (F : BasedCubicalCell (n + 2) x) (u : Fin (n + 1) → (unitInterval)) : GenLoop (Fin 1) X x :=
  ⟨⟨fun q => F.val (whiskerMap n (u, q 0)), by fun_prop⟩,
    by
    intro q hq
    obtain ⟨i, hi⟩ := hq
    have he : i = 0 := Subsingleton.elim _ _
    subst i
    rcases hi with hi | hi
    · change F.val (whiskerMap n (u, q 0)) = x
      rw [hi, whiskerMap_start]
      exact whiskerCorner_based F 0 (Or.inl rfl) (Fin.init u)
    · change F.val (whiskerMap n (u, q 0)) = x
      rw [hi, whiskerMap_finish]
      exact whiskerCorner_based F 1 (Or.inr rfl) (Fin.init u)⟩

private def HigherHurewicz.CubicalBoundary.whiskeredLoopMap {n : ℕ} {X : Type*} [TopologicalSpace X]
    {x : X} (F : BasedCubicalCell (n + 2) x) :
    C(Fin (n + 1) → (unitInterval), GenLoop (Fin 1) X x)
    where
  toFun := whiskeredLoop F
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change
      Continuous
        (fun z : (Fin (n + 1) → (unitInterval)) × (Fin 1 → (unitInterval)) =>
          F.val (whiskerMap n (z.1, z.2 0)))
    exact F.val.continuous.comp ((whiskerMap n).continuous.comp (by fun_prop))

private def
    HigherHurewicz.CubicalBoundary.whiskeredCell {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    (F : BasedCubicalCell (n + 2) x) :
    BasedCubicalCell (n + 1) (GenLoop.const : GenLoop (Fin 1) X x) :=
  ⟨whiskeredLoopMap F, by
    intro u i j hij hi hj
    apply GenLoop.ext
    intro q
    exact whiskerMap_codimTwo_based F u (q 0) i j hij hi hj⟩

@[simp]
private theorem HigherHurewicz.CubicalBoundary.whiskeredCell_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) (q : Fin 1 → (unitInterval)) :
    (whiskeredCell F).val u q = F.val (whiskerMap n (u, q 0)) :=
  rfl

private theorem HigherHurewicz.CubicalBoundary.whiskerTrack_concat (s : (unitInterval)) :
    whiskerTrack s =
      if (s : ℝ) ≤ 1 / 2 then (0, Set.projIcc 0 1 zero_le_one (2 * (s : ℝ)))
      else
        let t := Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) - 1)
        if (t : ℝ) ≤ 1 / 2 then (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)), 1)
        else (1, (unitInterval.symm) (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1))) :=
  rfl

private theorem HigherHurewicz.CubicalBoundary.whiskerMap_concat (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) :
    whiskerMap n (u, s) =
      if (s : ℝ) ≤ 1 / 2 then
        Fin.cons 0
          (Fin.snoc (Fin.init u) (Set.projIcc 0 1 zero_le_one (2 * (s : ℝ)) * u (Fin.last n)))
      else
        let t := Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) - 1)
        if (t : ℝ) ≤ 1 / 2 then Fin.cons (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))) u
        else
          Fin.cons 1
            (Fin.snoc (Fin.init u)
              ((unitInterval.symm) (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) *
                u (Fin.last n))) := by
  rw [whiskerMap_apply, whiskerTrack_concat]
  dsimp only
  split_ifs
  · rfl
  · simp only [one_mul, Fin.snoc_init_self]
  · rfl

private def
    HigherHurewicz.CubicalBoundary.uncurryLoop {X : Type*} [TopologicalSpace X] {x : X} {n : ℕ}
    (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) : GenLoop (Fin (n + 1)) X x :=
  ⟨⟨fun u => p (fun i => u i.succ) (fun _ => u 0), by fun_prop⟩,
    by
    intro u hu
    obtain ⟨i, hi⟩ := hu
    cases i using Fin.cases with
    | zero => exact GenLoop.boundary (p (fun i => u i.succ)) (fun _ => u 0) ⟨0, hi⟩
    | succ j =>
      change p (fun i => u i.succ) (fun _ => u 0) = x
      rw [GenLoop.boundary p _ ⟨j, hi⟩]
      rfl⟩

@[simp]
private theorem
    HigherHurewicz.CubicalBoundary.uncurryLoop_apply {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const)
    (u : Fin (n + 1) → (unitInterval)) : uncurryLoop p u = p (fun i => u i.succ) (fun _ => u 0) :=
  rfl

@[simp]
private theorem
    HigherHurewicz.CubicalBoundary.uncurryLoop_const {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} :
    uncurryLoop (GenLoop.const : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) =
      (GenLoop.const : GenLoop (Fin (n + 1)) X x) := by
  apply GenLoop.ext
  intro u
  rfl

private def
    HigherHurewicz.CubicalBoundary.uncurryLoopHomotopy {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} {p q : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) :
    (uncurryLoop p).val.HomotopyRel (uncurryLoop q).val (Cube.boundary (Fin (n + 1)))
    where
  toFun z := H (z.1, fun i => z.2 i.succ) (fun _ => z.2 0)
  continuous_toFun := by fun_prop
  map_zero_left
    u := by
    change H (0, fun i => u i.succ) (fun _ => u 0) = _
    rw [ContinuousMap.HomotopyWith.apply_zero]
    rfl
  map_one_left
    u := by
    change H (1, fun i => u i.succ) (fun _ => u 0) = _
    rw [ContinuousMap.HomotopyWith.apply_one]
    rfl
  prop' t u
    hu := by
    change H (t, fun i => u i.succ) (fun _ => u 0) = uncurryLoop p u
    rw [GenLoop.boundary (uncurryLoop p) u hu]
    obtain ⟨i, hi⟩ := hu
    cases i using Fin.cases with
    | zero => exact GenLoop.boundary (H (t, fun i => u i.succ)) (fun _ => u 0) ⟨0, hi⟩
    | succ j =>
      rw [H.eq_fst t ⟨j, hi⟩]
      change p (fun i => u i.succ) (fun _ => u 0) = x
      rw [GenLoop.boundary p _ ⟨j, hi⟩]
      rfl

private theorem
    HigherHurewicz.CubicalBoundary.uncurryLoop_homotopic {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} {p q : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (uncurryLoop p) (uncurryLoop q) := by
  obtain ⟨H⟩ := h
  exact ⟨uncurryLoopHomotopy H⟩

private theorem HigherHurewicz.CubicalBoundary.whiskeredCell_face_normal {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (i : Fin (n + 1))
    (ε : (unitInterval)) (hε : ε = 0 ∨ ε = 1) (h : i ≠ Fin.last n ∨ ε = 0) :
    uncurryLoop (cubicalFace (whiskeredCell F) i ε hε) =
      GenLoop.transAt 0 GenLoop.const
        (GenLoop.transAt 0 (cubicalFace F i.succ ε hε) GenLoop.const) := by
  apply GenLoop.ext
  intro u
  have hcons (s : (unitInterval)) : Function.update u 0 s = Fin.cons s (fun j => u j.succ) := by
    funext j
    cases j using Fin.cases with
    | zero => simp
    | succ j => simp
  change
    F.val (whiskerMap n (cubeFacet n i ε (fun j => u j.succ), u 0)) =
      GenLoop.transAt 0 GenLoop.const
        (GenLoop.transAt 0 (cubicalFace F i.succ ε hε) GenLoop.const) u
  rw [whiskerMap_concat]
  simp only [GenLoop.transAt, GenLoop.coe_copy, GenLoop.const_apply, Function.update_self,
    Function.update_idem]
  split_ifs with hs ht
  · exact whiskerFacetNormal_arm_based F i ε hε h _ 0 (Or.inl rfl) _
  · rw [cubicalFace_apply, hcons, cubeFacet_succ_cons]
  · exact whiskerFacetNormal_arm_based F i ε hε h _ 1 (Or.inr rfl) _

private theorem HigherHurewicz.CubicalBoundary.whiskerFacet_rotate_coordinates {n : ℕ}
    (u : Fin (n + 1) → (unitInterval)) :
    (fun i => u (finRotate (n + 1) i)) = Fin.snoc (Fin.tail u) (u 0) := by
  simpa only [Fin.cons_self_tail] using (Fin.snoc_eq_cons_rotate (Fin.tail u) (u 0)).symm

private theorem
    HigherHurewicz.CubicalBoundary.whiskerFacet_zero_coordinates {n : ℕ} (ε : (unitInterval))
    (u : Fin (n + 1) → (unitInterval)) : cubeFacet (n + 1) 0 ε u = Fin.cons ε u :=
  Fin.insertNth_zero' ε u

private theorem
    HigherHurewicz.CubicalBoundary.whiskerFacet_last_coordinates {n : ℕ} (ε : (unitInterval))
    (u : Fin n → (unitInterval)) : cubeFacet n (Fin.last n) ε u = Fin.snoc u ε :=
  Fin.insertNth_last' ε u

private theorem HigherHurewicz.CubicalBoundary.whiskerFacet_rotated_face_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (ε : (unitInterval))
    (hε : ε = 0 ∨ ε = 1) (u : Fin (n + 1) → (unitInterval)) :
    HigherHurewicz.NativeSubdivision.permuteCubeLoop (cubicalFace F 0 ε hε) (finRotate (n + 1))
        u =
      F.val (Fin.cons ε (Fin.snoc (Fin.tail u) (u 0))) := by
  rw [HigherHurewicz.NativeSubdivision.permuteCubeLoop_apply, cubicalFace_apply,
    whiskerFacet_zero_coordinates, whiskerFacet_rotate_coordinates]

private theorem HigherHurewicz.CubicalBoundary.whiskerFacet_last_upper_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) :
    cubicalUpperFace F (Fin.last (n + 1)) u = F.val (Fin.cons (u 0) (Fin.snoc (Fin.tail u) 1)) := by
  rw [cubicalFace_apply, whiskerFacet_last_coordinates, Fin.cons_snoc_eq_snoc_cons,
    Fin.cons_self_tail]

public
theorem HigherHurewicz.CubicalBoundary.whiskerFacet_symmAt_zero_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin (n + 1)) X x)
    (u : Fin (n + 1) → (unitInterval)) :
    GenLoop.symmAt 0 p u = p (Function.update u 0 ((unitInterval.symm) (u 0))) := by
  change p (fun j => if j = 0 then (unitInterval.symm) (u 0) else u j) = _
  congr 1
  funext j
  simp only [Function.update_apply]

private theorem HigherHurewicz.CubicalBoundary.whiskerFacet_reflected_rotated_face_apply {n : ℕ}
    {X : Type*} [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (ε : (unitInterval))
    (hε : ε = 0 ∨ ε = 1) (u : Fin (n + 1) → (unitInterval)) :
    GenLoop.symmAt 0
        (HigherHurewicz.NativeSubdivision.permuteCubeLoop (cubicalFace F 0 ε hε)
          (finRotate (n + 1)))
        u =
      F.val (Fin.cons ε (Fin.snoc (Fin.tail u) ((unitInterval.symm) (u 0)))) := by
  rw [whiskerFacet_symmAt_zero_apply, whiskerFacet_rotated_face_apply]
  simp only [Fin.tail_update_zero, Function.update_self]

private theorem
    HigherHurewicz.CubicalBoundary.whiskerFacet_last_upper_uncurry_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) :
    uncurryLoop (cubicalUpperFace (whiskeredCell F) (Fin.last n)) u =
      F.val (Fin.cons (whiskerTrack (u 0)).1 (Fin.snoc (Fin.tail u) (whiskerTrack (u 0)).2)) := by
  rw [uncurryLoop_apply, cubicalFace_apply, whiskeredCell_apply, whiskerFacet_last_coordinates,
    whiskerMap_apply]
  simp only [Fin.init_snoc, Fin.snoc_last, mul_one]
  rfl

end Mathoverflow1973

end
