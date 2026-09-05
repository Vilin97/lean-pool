/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.PeriodFamily.Core5
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.Hurewicz.SecondHurewicz
import all LeanPool.HopfProblem.PeriodFamily.Core5

/-!
# Hopf problem: hurewicz · third hurewicz

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

@[simp]
private theorem ThirdHurewicz.edgeTriangleHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x
        (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x :=
  extendCoherentSimplexHomotopy_const (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 0)
    (SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_face x)
    (SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_zero x) x
    (SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_const x)

@[simp]
private theorem ThirdHurewicz.edgeTetrahedronHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x
        (ContinuousMap.const (FirstHurewicz.Simplex 3) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 3) x :=
  extendCoherentSimplexHomotopy_const (SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_face x)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_zero x) x
    (edgeTriangleHomotopy_const x)

private def
    ThirdHurewicz.edgeFourSimplexHomotopy {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (smp : FirstHurewicz.SingularSimplex X 4) :
    C((unitInterval) × FirstHurewicz.Simplex 4, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero x) smp

private theorem ThirdHurewicz.edgeFourSimplexHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 3
      (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
      (edgeFourSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero x)

private def ThirdHurewicz.edgeNormalizedFourSimplexMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 4) :
    FirstHurewicz.SingularSimplex X 4 :=
  SecondHurewicz.SimplyConnected.timeSlice
    (edgeFourSimplexHomotopy x (SecondHurewicz.SimplyConnected.vertexNormalizedSimplex x 4 smp)) 1

private theorem ThirdHurewicz.edgeNormalizedFourSimplexMap_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 4) (i : Fin 5) :
    (edgeNormalizedFourSimplexMap x smp).comp (FirstHurewicz.simplexFace 3 i) =
      SecondHurewicz.SimplyConnected.normalizedTetrahedronMap x
        (smp.comp (FirstHurewicz.simplexFace 3 i)) := by
  change
    (SecondHurewicz.SimplyConnected.timeSlice
            (edgeFourSimplexHomotopy x
              (SecondHurewicz.SimplyConnected.vertexNormalizedSimplex x 4 smp))
            1).comp
        (FirstHurewicz.simplexFace 3 i) =
      _
  rw [SecondHurewicz.SimplyConnected.timeSlice_face (edgeFourSimplexHomotopy_face x),
    SecondHurewicz.SimplyConnected.vertexNormalizedSimplex_face]
  rfl

private theorem ThirdHurewicz.triangleReturn_first_mem (s : FirstHurewicz.Simplex 2) :
    s 1 + Max.max (s 2 - s 0) 0 ∈ unitInterval := by
  constructor
  · exact add_nonneg (stdSimplex.zero_le s 1) (le_max_right _ _)
  · have hm : Max.max (s 2 - s 0) 0 ≤ s 2 :=
      max_le (sub_le_self _ (stdSimplex.zero_le s 0)) (stdSimplex.zero_le s 2)
    have h0 := stdSimplex.zero_le s 0
    have hs := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change s 0 + (s 1 + s 2) = 1 at hs
    linarith

private theorem ThirdHurewicz.triangleReturn_second_mem (s : FirstHurewicz.Simplex 2) :
    s 2 + Min.min (s 0) (s 2) ∈ unitInterval := by
  constructor
  · exact
      add_nonneg (stdSimplex.zero_le s 2)
        (le_min (stdSimplex.zero_le s 0) (stdSimplex.zero_le s 2))
  · have hm : Min.min (s 0) (s 2) ≤ s 0 := min_le_left _ _
    have h1 := stdSimplex.zero_le s 1
    have hs := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change s 0 + (s 1 + s 2) = 1 at hs
    linarith

private def ThirdHurewicz.triangleCubicalReturn : C(FirstHurewicz.Simplex 2, Fin 2 → (unitInterval))
    where
  toFun
    s :=
    ![⟨s 1 + Max.max (s 2 - s 0) 0, triangleReturn_first_mem s⟩,
      ⟨s 2 + Min.min (s 0) (s 2), triangleReturn_second_mem s⟩]
  continuous_toFun := by
    have hc (j : Fin 3) : Continuous (fun s : FirstHurewicz.Simplex 2 => s j) :=
      (continuous_apply j).comp continuous_subtype_val
    apply continuous_pi
    intro i
    fin_cases i <;> apply Continuous.subtype_mk
    · change Continuous fun s : FirstHurewicz.Simplex 2 => s 1 + Max.max (s 2 - s 0) 0
      exact (hc 1).add (((hc 2).sub (hc 0)).max continuous_const)
    · change Continuous fun s : FirstHurewicz.Simplex 2 => s 2 + Min.min (s 0) (s 2)
      exact (hc 2).add ((hc 0).min (hc 2))

private theorem ThirdHurewicz.triangleCubicalReturn_face_zero (s : FirstHurewicz.Simplex 2)
    (hs : s 0 = 0) : triangleCubicalReturn s 0 = 1 := by
  apply Subtype.ext
  change s 1 + Max.max (s 2 - s 0) 0 = 1
  rw [hs, sub_zero, max_eq_left (stdSimplex.zero_le s 2)]
  have hsum := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change s 0 + (s 1 + s 2) = 1 at hsum
  simpa only [hs, zero_add] using hsum

private theorem ThirdHurewicz.triangleCubicalReturn_face_two (s : FirstHurewicz.Simplex 2)
    (hs : s 2 = 0) : triangleCubicalReturn s 1 = 0 := by
  apply Subtype.ext
  change s 2 + Min.min (s 0) (s 2) = 0
  rw [hs, min_eq_right (stdSimplex.zero_le s 0), zero_add]

private theorem ThirdHurewicz.triangleCubicalReturn_face_one (s : FirstHurewicz.Simplex 2)
    (hs : s 1 = 0) : triangleCubicalReturn s 0 = 0 ∨ triangleCubicalReturn s 1 = 1 := by
  rcases le_total (s 2) (s 0) with h | h
  · left
    apply Subtype.ext
    change s 1 + Max.max (s 2 - s 0) 0 = 0
    rw [hs, max_eq_right (sub_nonpos.mpr h), zero_add]
  · right
    apply Subtype.ext
    change s 2 + Min.min (s 0) (s 2) = 1
    rw [min_eq_left h]
    have hsum := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
    change s 0 + (s 1 + s 2) = 1 at hsum
    linarith

private theorem ThirdHurewicz.triangleCubicalReturn_boundary (s : FirstHurewicz.Simplex 2)
    (hs : s ∈ SecondHurewicz.SimplyConnected.triangleBoundary) :
    triangleCubicalReturn s ∈ Cube.boundary (Fin 2) := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨0, Or.inr (triangleCubicalReturn_face_zero s hi)⟩
  · rcases triangleCubicalReturn_face_one s hi with h | h
    · exact ⟨0, Or.inl h⟩
    · exact ⟨1, Or.inr h⟩
  · exact ⟨1, Or.inl (triangleCubicalReturn_face_two s hi)⟩

private theorem ThirdHurewicz.triangleCubicalReturn_quotient_zero (s : FirstHurewicz.Simplex 2)
    (i : Fin 3) (hi : s i = 0) :
    SecondHurewicz.SimplyConnected.triangleCubeQuotient (triangleCubicalReturn s) i = 0 := by
  fin_cases i
  · change 1 - (triangleCubicalReturn s 0 : ℝ) = 0
    rw [triangleCubicalReturn_face_zero s hi]
    norm_num
  · change
      (triangleCubicalReturn s 0 : ℝ) -
          Min.min (triangleCubicalReturn s 0 : ℝ) (triangleCubicalReturn s 1 : ℝ) =
        0
    rcases triangleCubicalReturn_face_one s hi with h | h
    · rw [h]
      change 0 - Min.min 0 (triangleCubicalReturn s 1 : ℝ) = 0
      rw [min_eq_left (triangleCubicalReturn s 1).property.1, sub_self]
    · rw [h]
      change (triangleCubicalReturn s 0 : ℝ) - Min.min (triangleCubicalReturn s 0 : ℝ) 1 = 0
      rw [min_eq_left (triangleCubicalReturn s 0).property.2, sub_self]
  · change Min.min (triangleCubicalReturn s 0 : ℝ) (triangleCubicalReturn s 1 : ℝ) = 0
    rw [triangleCubicalReturn_face_two s hi]
    change Min.min (triangleCubicalReturn s 0 : ℝ) 0 = 0
    exact min_eq_right (triangleCubicalReturn s 0).property.1

private def ThirdHurewicz.triangleReturnComposition :
    C(FirstHurewicz.Simplex 2, FirstHurewicz.Simplex 2) :=
  SecondHurewicz.SimplyConnected.triangleCubeQuotient.comp triangleCubicalReturn

private def ThirdHurewicz.triangleReturnInterpolation :
    C((unitInterval) × FirstHurewicz.Simplex 2, FirstHurewicz.Simplex 2) :=
  SecondHurewicz.SimplyConnected.tetrahedronSimplexBlendMap
    (ContinuousMap.id (FirstHurewicz.Simplex 2)) triangleReturnComposition

@[simp]
private theorem ThirdHurewicz.triangleReturnInterpolation_zero (s : FirstHurewicz.Simplex 2) :
    triangleReturnInterpolation (0, s) = s :=
  SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero s (triangleReturnComposition s)

@[simp]
private theorem ThirdHurewicz.triangleReturnInterpolation_one (s : FirstHurewicz.Simplex 2) :
    triangleReturnInterpolation (1, s) = triangleReturnComposition s :=
  SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_one s (triangleReturnComposition s)

private theorem ThirdHurewicz.triangleReturnInterpolation_coordinate_zero (t : (unitInterval))
    (s : FirstHurewicz.Simplex 2) (i : Fin 3) (hi : s i = 0) :
    triangleReturnInterpolation (t, s) i = 0 :=
  SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate t s
    (triangleReturnComposition s) i hi (triangleCubicalReturn_quotient_zero s i hi)

private theorem ThirdHurewicz.triangleReturnInterpolation_boundary (t : (unitInterval))
    (s : FirstHurewicz.Simplex 2) (hs : s ∈ SecondHurewicz.SimplyConnected.triangleBoundary) :
    triangleReturnInterpolation (t, s) ∈ SecondHurewicz.SimplyConnected.triangleBoundary := by
  obtain ⟨i, hi⟩ := hs
  exact ⟨i, triangleReturnInterpolation_coordinate_zero t s i hi⟩

private def ThirdHurewicz.triangleReturnHomotopy {X : Type} [TopologicalSpace X] {x : X}
    (τ : SecondHurewicz.SimplyConnected.BasedTriangle x) :
    τ.val.HomotopyRel
      ((SecondHurewicz.SimplyConnected.basedTriangleLoop τ).val.comp triangleCubicalReturn)
      SecondHurewicz.SimplyConnected.triangleBoundary
    where
  toFun z := τ.val (triangleReturnInterpolation z)
  continuous_toFun := τ.val.continuous.comp triangleReturnInterpolation.continuous
  map_zero_left s := congrArg τ.val (triangleReturnInterpolation_zero s)
  map_one_left s := congrArg τ.val (triangleReturnInterpolation_one s)
  prop' t s
    hs :=
    (τ.property _ (triangleReturnInterpolation_boundary t s hs)).trans (τ.property s hs).symm

private def ThirdHurewicz.nativeSquareNullHomotopy {X : Type*} [TopologicalSpace X] {x : X}
    [hπ : Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel (ContinuousMap.const (Fin 2 → (unitInterval)) x) (Cube.boundary (Fin 2)) :=
  Classical.choice
    (show GenLoop.Homotopic p GenLoop.const from
      Quotient.exact (@Subsingleton.elim (π_ 2 X x) hπ ⟦p⟧ ⟦GenLoop.const⟧))

private def ThirdHurewicz.nativeSquareNullHomotopy_comp {X : Type*} [TopologicalSpace X] {x : X}
    {A : Type*} [TopologicalSpace A] [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 2) X x)
    (r : C(A, Fin 2 → (unitInterval))) (S : Set A) (hr : Set.MapsTo r S (Cube.boundary (Fin 2))) :
    (p.val.comp r).HomotopyRel (ContinuousMap.const A x) S
    where
  toFun z := nativeSquareNullHomotopy p (z.1, r z.2)
  continuous_toFun :=
    (nativeSquareNullHomotopy p).continuous.comp
      (continuous_fst.prodMk (r.continuous.comp continuous_snd))
  map_zero_left a := (nativeSquareNullHomotopy p).apply_zero (r a)
  map_one_left a := (nativeSquareNullHomotopy p).apply_one (r a)
  prop' t _ ha := (nativeSquareNullHomotopy p).eq_fst t (hr ha)

private def ThirdHurewicz.triangleNullHomotopyUnnormalized {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ 2 X x)] (τ : SecondHurewicz.SimplyConnected.BasedTriangle x) :
    τ.val.HomotopyRel (ContinuousMap.const (FirstHurewicz.Simplex 2) x)
      SecondHurewicz.SimplyConnected.triangleBoundary :=
  ContinuousMap.HomotopyRel.trans (triangleReturnHomotopy τ)
    (nativeSquareNullHomotopy_comp (SecondHurewicz.SimplyConnected.basedTriangleLoop τ)
      triangleCubicalReturn SecondHurewicz.SimplyConnected.triangleBoundary
      (fun _ hs => triangleCubicalReturn_boundary _ hs))

private def ThirdHurewicz.triangleNullHomotopy {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ 2 X x)] (τ : SecondHurewicz.SimplyConnected.BasedTriangle x) :
    τ.val.HomotopyRel (ContinuousMap.const (FirstHurewicz.Simplex 2) x)
      SecondHurewicz.SimplyConnected.triangleBoundary := by
  classical
    exact
    if h : τ = SecondHurewicz.SimplyConnected.constantBasedTriangle x then
      ContinuousMap.HomotopyRel.cast
        (ContinuousMap.HomotopyRel.refl (ContinuousMap.const (FirstHurewicz.Simplex 2) x)
          SecondHurewicz.SimplyConnected.triangleBoundary)
        (congrArg (fun υ : SecondHurewicz.SimplyConnected.BasedTriangle x => υ.val) h).symm rfl
    else triangleNullHomotopyUnnormalized τ

private theorem ThirdHurewicz.triangleNullHomotopy_zero {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ 2 X x)] (τ : SecondHurewicz.SimplyConnected.BasedTriangle x)
    (s : FirstHurewicz.Simplex 2) : triangleNullHomotopy τ (0, s) = τ.val s :=
  (triangleNullHomotopy τ).apply_zero s

private theorem ThirdHurewicz.triangleNullHomotopy_one {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ 2 X x)] (τ : SecondHurewicz.SimplyConnected.BasedTriangle x)
    (s : FirstHurewicz.Simplex 2) : triangleNullHomotopy τ (1, s) = x :=
  (triangleNullHomotopy τ).apply_one s

@[simp]
private theorem ThirdHurewicz.triangleNullHomotopy_constant {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    triangleNullHomotopy (SecondHurewicz.SimplyConnected.constantBasedTriangle x) =
      ContinuousMap.HomotopyRel.refl (ContinuousMap.const (FirstHurewicz.Simplex 2) x)
        SecondHurewicz.SimplyConnected.triangleBoundary := by
  classical
  unfold triangleNullHomotopy
  rw [dite_eq_left rfl]
  rfl

private theorem ThirdHurewicz.triangleNullHomotopy_constant_toContinuousMap {X : Type}
    [TopologicalSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    (triangleNullHomotopy
          (SecondHurewicz.SimplyConnected.constantBasedTriangle x)).toContinuousMap =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x := by
  rw [triangleNullHomotopy_constant]
  rfl

private def ThirdHurewicz.triangleStraighteningHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 2) :
    C((unitInterval) × FirstHurewicz.Simplex 2, X) := by
  classical
    exact
    if h : ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary, smp s = x then
      (triangleNullHomotopy
          (⟨smp, h⟩ : SecondHurewicz.SimplyConnected.BasedTriangle x)).toContinuousMap
    else SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 2 smp

@[simp]
private theorem
    ThirdHurewicz.triangleStraighteningHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 2)
    (s : FirstHurewicz.Simplex 2) : triangleStraighteningHomotopy x smp (0, s) = smp s := by
  classical
  unfold triangleStraighteningHomotopy
  split
  · rename_i h
    exact triangleNullHomotopy_zero (⟨smp, h⟩ : SecondHurewicz.SimplyConnected.BasedTriangle x) s
  · rfl

private theorem
    ThirdHurewicz.triangleStraighteningHomotopy_one {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 2)
    (h : ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary, smp s = x)
    (s : FirstHurewicz.Simplex 2) : triangleStraighteningHomotopy x smp (1, s) = x := by
  classical
  rw [triangleStraighteningHomotopy, dite_eq_left h]
  exact triangleNullHomotopy_one (⟨smp, h⟩ : SecondHurewicz.SimplyConnected.BasedTriangle x) s

private theorem ThirdHurewicz.triangleStraighteningHomotopy_boundary {X : Type} [TopologicalSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 2)
    (r : (unitInterval)) (s : FirstHurewicz.Simplex 2)
    (hs : s ∈ SecondHurewicz.SimplyConnected.triangleBoundary) :
    triangleStraighteningHomotopy x smp (r, s) = smp s := by
  classical
  unfold triangleStraighteningHomotopy
  split
  · rename_i h
    exact
      (triangleNullHomotopy (⟨smp, h⟩ : SecondHurewicz.SimplyConnected.BasedTriangle x)).eq_fst r
        hs
  · rfl

@[simp]
private theorem
    ThirdHurewicz.triangleStraighteningHomotopy_const {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    triangleStraighteningHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x := by
  classical
  have h :
    ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary,
      (ContinuousMap.const (FirstHurewicz.Simplex 2) x) s = x :=
    fun _ _ => rfl
  rw [triangleStraighteningHomotopy, dite_eq_left h]
  exact triangleNullHomotopy_constant_toContinuousMap x

private theorem
    ThirdHurewicz.triangleStraighteningHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 1
      (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 1)
      (triangleStraighteningHomotopy x) := by
  intro smp i
  ext u
  change
    triangleStraighteningHomotopy x smp (u.1, FirstHurewicz.simplexFace 1 i u.2) =
      smp (FirstHurewicz.simplexFace 1 i u.2)
  exact
    triangleStraighteningHomotopy_boundary x smp u.1 _
      ⟨i, FirstHurewicz.simplexFace_apply_self 1 i u.2⟩

private def ThirdHurewicz.threeSimplexBoundary : Set (FirstHurewicz.Simplex 3) :=
  {s | ∃ i, s i = 0}

private def ThirdHurewicz.BasedThreeSimplex {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(FirstHurewicz.Simplex 3, X) // ∀ s ∈ threeSimplexBoundary, τ s = x }

private def ThirdHurewicz.threeSimplexQuotient : C(Fin 3 → (unitInterval), FirstHurewicz.Simplex 3)
    where
  toFun
    u :=
    ⟨![1 - (u 0 : ℝ), (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ),
        Min.min (u 0 : ℝ) (u 1 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)),
        Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ))],
      by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (u 0).property.2
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact sub_nonneg.mpr (min_le_min_left _ (min_le_left _ _))
        · exact le_min (u 0).property.1 (le_min (u 1).property.1 (u 2).property.1)
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
private theorem ThirdHurewicz.threeSimplexQuotient_zero (u : Fin 3 → (unitInterval)) :
    threeSimplexQuotient u 0 = 1 - (u 0 : ℝ) :=
  rfl

@[simp]
private theorem ThirdHurewicz.threeSimplexQuotient_one (u : Fin 3 → (unitInterval)) :
    threeSimplexQuotient u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) :=
  rfl

@[simp]
private theorem ThirdHurewicz.threeSimplexQuotient_two (u : Fin 3 → (unitInterval)) :
    threeSimplexQuotient u 2 =
      Min.min (u 0 : ℝ) (u 1 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
  rfl

@[simp]
private theorem ThirdHurewicz.threeSimplexQuotient_three (u : Fin 3 → (unitInterval)) :
    threeSimplexQuotient u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
  rfl

private theorem ThirdHurewicz.threeSimplexQuotient_boundary (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) : threeSimplexQuotient u ∈ threeSimplexBoundary := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨3, ?_⟩
      rw [threeSimplexQuotient_three, hi]
      exact min_eq_left (le_min (u 1).property.1 (u 2).property.1)
    · change u 1 = 0 at hi
      refine ⟨3, ?_⟩
      rw [threeSimplexQuotient_three, hi]
      change Min.min (u 0 : ℝ) (Min.min (0 : ℝ) (u 2 : ℝ)) = 0
      rw [min_eq_left (u 2).property.1]
      exact min_eq_right (u 0).property.1
    · change u 2 = 0 at hi
      refine ⟨3, ?_⟩
      rw [threeSimplexQuotient_three, hi]
      change Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (0 : ℝ)) = 0
      rw [min_eq_right (u 1).property.1]
      exact min_eq_right (u 0).property.1
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨0, ?_⟩
      rw [threeSimplexQuotient_zero, hi]
      norm_num
    · change u 1 = 1 at hi
      refine ⟨1, ?_⟩
      rw [threeSimplexQuotient_one, hi]
      change (u 0 : ℝ) - Min.min (u 0 : ℝ) (1 : ℝ) = 0
      rw [min_eq_left (u 0).property.2, sub_self]
    · change u 2 = 1 at hi
      refine ⟨2, ?_⟩
      rw [threeSimplexQuotient_two, hi]
      change Min.min (u 0 : ℝ) (u 1 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (1 : ℝ)) = 0
      rw [min_eq_left (u 1).property.2, sub_self]

private theorem ThirdHurewicz.threeSimplexQuotient_boundary_of_first_le (u : Fin 3 → (unitInterval))
    (h : (u 0 : ℝ) ≤ u 1) : threeSimplexQuotient u ∈ threeSimplexBoundary :=
  ⟨1, by rw [threeSimplexQuotient_one, min_eq_left h, sub_self]⟩

private theorem
    ThirdHurewicz.threeSimplexQuotient_boundary_of_second_le (u : Fin 3 → (unitInterval))
    (h : (u 1 : ℝ) ≤ u 2) : threeSimplexQuotient u ∈ threeSimplexBoundary :=
  ⟨2, by rw [threeSimplexQuotient_two, min_eq_left h, sub_self]⟩

private def ThirdHurewicz.basedThreeSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : GenLoop (Fin 3) X x :=
  ⟨τ.val.comp threeSimplexQuotient, fun u hu => τ.property _ (threeSimplexQuotient_boundary u hu)⟩

private def ThirdHurewicz.basedThreeSimplexClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : Additive (π_ 3 X x) :=
  Additive.ofMul (⟦basedThreeSimplexLoop τ⟧ : π_ 3 X x)

private theorem ThirdHurewicz.basedThreeSimplex_face {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) (i : Fin 4) :
    τ.val.comp (FirstHurewicz.simplexFace 2 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ ⟨i, FirstHurewicz.simplexFace_apply_self 2 i s⟩

private def ThirdHurewicz.constantBasedThreeSimplex {X : Type} [TopologicalSpace X] (x : X) :
    BasedThreeSimplex x :=
  ⟨ContinuousMap.const (FirstHurewicz.Simplex 3) x, fun _ _ => rfl⟩

private def ThirdHurewicz.triangleThreeSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 3) :
    C((unitInterval) × FirstHurewicz.Simplex 3, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 1) (triangleStraighteningHomotopy x)
    (triangleStraighteningHomotopy_face x) (triangleStraighteningHomotopy_zero x) smp

@[simp]
private theorem
    ThirdHurewicz.triangleThreeSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 3)
    (s : FirstHurewicz.Simplex 3) : triangleThreeSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

private theorem
    ThirdHurewicz.triangleThreeSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 (triangleStraighteningHomotopy x)
      (triangleThreeSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 1) (triangleStraighteningHomotopy x)
    (triangleStraighteningHomotopy_face x) (triangleStraighteningHomotopy_zero x)

@[simp]
private theorem
    ThirdHurewicz.triangleThreeSimplexHomotopy_const {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    triangleThreeSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 3) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 3) x :=
  extendCoherentSimplexHomotopy_const (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 1)
    (triangleStraighteningHomotopy x) (triangleStraighteningHomotopy_face x)
    (triangleStraighteningHomotopy_zero x) x (triangleStraighteningHomotopy_const x)

private def ThirdHurewicz.triangleFourSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 4) :
    C((unitInterval) × FirstHurewicz.Simplex 4, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy (triangleStraighteningHomotopy x)
    (triangleThreeSimplexHomotopy x) (triangleThreeSimplexHomotopy_face x)
    (triangleThreeSimplexHomotopy_zero x) smp

private theorem
    ThirdHurewicz.triangleFourSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 3 (triangleThreeSimplexHomotopy x)
      (triangleFourSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (triangleStraighteningHomotopy x) (triangleThreeSimplexHomotopy x)
    (triangleThreeSimplexHomotopy_face x) (triangleThreeSimplexHomotopy_zero x)

private theorem ThirdHurewicz.triangleThreeSimplexHomotopy_one_face {X : Type} [TopologicalSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 3)
    (h :
      ∀ i : Fin 4,
        ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary,
          (smp.comp (FirstHurewicz.simplexFace 2 i)) s = x)
    (i : Fin 4) :
    (SecondHurewicz.SimplyConnected.timeSlice (triangleThreeSimplexHomotopy x smp) 1).comp
        (FirstHurewicz.simplexFace 2 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  rw [SecondHurewicz.SimplyConnected.timeSlice_face (triangleThreeSimplexHomotopy_face x)]
  ext s
  exact triangleStraighteningHomotopy_one x (smp.comp (FirstHurewicz.simplexFace 2 i)) (h i) s

private theorem
    ThirdHurewicz.triangleThreeSimplexHomotopy_one_boundary {X : Type} [TopologicalSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 3)
    (h :
      ∀ i : Fin 4,
        ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary,
          (smp.comp (FirstHurewicz.simplexFace 2 i)) s = x)
    (s : FirstHurewicz.Simplex 3) (hs : s ∈ threeSimplexBoundary) :
    SecondHurewicz.SimplyConnected.timeSlice (triangleThreeSimplexHomotopy x smp) 1 s = x := by
  obtain ⟨i, t, ht⟩ :=
    SecondHurewicz.SimplyConnected.simplexBoundary_exists_face 2
      (⟨s, hs⟩ : SecondHurewicz.SimplyConnected.SimplexBoundary 3)
  have he : FirstHurewicz.simplexFace 2 i t = s := congrArg Subtype.val ht
  rw [← he]
  exact
    congrArg (fun f : C(FirstHurewicz.Simplex 2, X) => f t)
      (triangleThreeSimplexHomotopy_one_face x smp h i)

private def ThirdHurewicz.triangleStraightenedThreeSimplex {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 3)
    (h :
      ∀ i : Fin 4,
        ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary,
          (smp.comp (FirstHurewicz.simplexFace 2 i)) s = x) :
    BasedThreeSimplex x :=
  ⟨SecondHurewicz.SimplyConnected.timeSlice (triangleThreeSimplexHomotopy x smp) 1,
    triangleThreeSimplexHomotopy_one_boundary x smp h⟩

private def
    ThirdHurewicz.normalizedThreeSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 3) :
    BasedThreeSimplex x :=
  triangleStraightenedThreeSimplex x
    (SecondHurewicz.SimplyConnected.normalizedTetrahedronMap x smp)
    (SecondHurewicz.SimplyConnected.normalizedTetrahedronMap_face_boundary x smp)

private def ThirdHurewicz.normalizedFourSimplexMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) : FirstHurewicz.SingularSimplex X 4 :=
  SecondHurewicz.SimplyConnected.timeSlice
    (triangleFourSimplexHomotopy x (edgeNormalizedFourSimplexMap x smp)) 1

private theorem ThirdHurewicz.normalizedFourSimplexMap_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) (i : Fin 5) :
    (normalizedFourSimplexMap x smp).comp (FirstHurewicz.simplexFace 3 i) =
      (normalizedThreeSimplex x (smp.comp (FirstHurewicz.simplexFace 3 i))).val := by
  change
    (SecondHurewicz.SimplyConnected.timeSlice
            (triangleFourSimplexHomotopy x (edgeNormalizedFourSimplexMap x smp)) 1).comp
        (FirstHurewicz.simplexFace 3 i) =
      _
  rw [SecondHurewicz.SimplyConnected.timeSlice_face (triangleFourSimplexHomotopy_face x),
    edgeNormalizedFourSimplexMap_face]
  rfl

private theorem ThirdHurewicz.normalizedFourSimplexMap_face_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) (i : Fin 5) (s : FirstHurewicz.Simplex 3)
    (hs : s ∈ threeSimplexBoundary) :
    normalizedFourSimplexMap x smp (FirstHurewicz.simplexFace 3 i s) = x := by
  have hf :=
    congrArg (fun f : C(FirstHurewicz.Simplex 3, X) => f s)
      (normalizedFourSimplexMap_face x smp i)
  exact
    hf.trans ((normalizedThreeSimplex x (smp.comp (FirstHurewicz.simplexFace 3 i))).property s hs)

private def ThirdHurewicz.threeSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    FirstHurewicz.Chains X 3 →ₗ[ℤ] Additive (π_ 3 X x) :=
  FirstHurewicz.chainLift X 3 fun smp => basedThreeSimplexClass (normalizedThreeSimplex x smp)

@[simp]
private theorem ThirdHurewicz.threeSimplexClassOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 3) :
    threeSimplexClassOperator x (FirstHurewicz.simplexChain X 3 smp) =
      basedThreeSimplexClass (normalizedThreeSimplex x smp) :=
  FirstHurewicz.chainLift_simplex X 3 _ smp

private def ThirdHurewicz.straightenedThreeCycle {X : Type} [TopologicalSpace X]
    (H₂ : FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : FirstHurewicz.SingularSimplex X 3 → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 3
    (SecondHurewicz.SimplyConnected.simplexEndpointOperator 3 H₃ 1 c.1)
    (by
      rw [SecondHurewicz.SimplyConnected.simplexEndpointOperator_boundary 2 H₂ H₃ h,
        SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 3
          c,
        map_zero])

private theorem ThirdHurewicz.straightenedThreeCycle_boundary {X : Type} [TopologicalSpace X]
    (H₂ : FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : FirstHurewicz.SingularSimplex X 3 → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (h₀ : ∀ smp, SecondHurewicz.SimplyConnected.timeSlice (H₃ smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    ((FirstHurewicz.singularComplex X).d 4 3).hom
        (SecondHurewicz.SimplyConnected.simplexPrismOperator 3 H₃ c.1) =
      (straightenedThreeCycle H₂ H₃ h c).1 - c.1 := by
  rw [SecondHurewicz.SimplyConnected.simplexPrismOperator_boundary 2 H₂ H₃ h,
    SecondHurewicz.SimplyConnected.simplexEndpointOperator_zero 3 H₃ h₀,
    SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 3 c,
    map_zero, sub_zero]
  rfl

private theorem ThirdHurewicz.straightenedThreeCycle_class {X : Type} [TopologicalSpace X]
    (H₂ : FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : FirstHurewicz.SingularSimplex X 3 → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (h₀ : ∀ smp, SecondHurewicz.SimplyConnected.timeSlice (H₃ smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (straightenedThreeCycle H₂ H₃ h c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 3 _
        _).mpr
  exact
    ⟨SecondHurewicz.SimplyConnected.simplexPrismOperator 3 H₃ c.1,
      straightenedThreeCycle_boundary H₂ H₃ h h₀ c⟩

private def
    ThirdHurewicz.normalizedThreeChain {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] : FirstHurewicz.Chains X 3 →ₗ[ℤ] FirstHurewicz.Chains X 3 :=
  FirstHurewicz.chainLift X 3 fun smp =>
    FirstHurewicz.simplexChain X 3 (normalizedThreeSimplex x smp).val

@[simp]
private theorem ThirdHurewicz.normalizedThreeChain_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 3) :
    normalizedThreeChain x (FirstHurewicz.simplexChain X 3 smp) =
      FirstHurewicz.simplexChain X 3 (normalizedThreeSimplex x smp).val :=
  FirstHurewicz.chainLift_simplex X 3 _ smp

private theorem ThirdHurewicz.normalizedThreeChain_eq {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    normalizedThreeChain x =
      (SecondHurewicz.SimplyConnected.simplexEndpointOperator 3 (triangleThreeSimplexHomotopy x)
            1).comp
        ((SecondHurewicz.SimplyConnected.simplexEndpointOperator 3
              (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x) 1).comp
          (SecondHurewicz.SimplyConnected.simplexEndpointOperator 3
            (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 3) 1)) := by
  apply FirstHurewicz.chainMap_ext X 3
  intro smp
  simp only [normalizedThreeChain_simplex, LinearMap.comp_apply,
    SecondHurewicz.SimplyConnected.simplexEndpointOperator_simplex]
  rfl

private def ThirdHurewicz.vertexNormalizedThreeCycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  straightenedThreeCycle (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 2)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 3)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_face x 2) c

private theorem ThirdHurewicz.vertexNormalizedThreeCycle_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (vertexNormalizedThreeCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c :=
  straightenedThreeCycle_class _ _
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_face x 2)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_timeSlice_zero x 3) c

private def ThirdHurewicz.edgeNormalizedThreeCycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  straightenedThreeCycle (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face x)
    (vertexNormalizedThreeCycle x c)

private theorem ThirdHurewicz.edgeNormalizedThreeCycle_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (edgeNormalizedThreeCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c := by
  have h₀ :
    ∀ smp,
      SecondHurewicz.SimplyConnected.timeSlice
          (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x smp) 0 =
        smp := by
    intro smp
    ext s
    exact SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero x smp s
  exact
    (straightenedThreeCycle_class _ _
          (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face x) h₀
          (vertexNormalizedThreeCycle x c)).trans
      (vertexNormalizedThreeCycle_class x c)

private def
    ThirdHurewicz.normalizedThreeCycle {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  straightenedThreeCycle (triangleStraighteningHomotopy x) (triangleThreeSimplexHomotopy x)
    (triangleThreeSimplexHomotopy_face x) (edgeNormalizedThreeCycle x c)

@[simp]
private theorem ThirdHurewicz.normalizedThreeCycle_val {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    (normalizedThreeCycle x c).val = normalizedThreeChain x c.val := by
  rw [normalizedThreeChain_eq]
  rfl

private theorem ThirdHurewicz.normalizedThreeCycle_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (normalizedThreeCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c := by
  have h₀ :
    ∀ smp,
      SecondHurewicz.SimplyConnected.timeSlice (triangleThreeSimplexHomotopy x smp) 0 = smp := by
    intro smp
    ext s
    exact triangleThreeSimplexHomotopy_zero x smp s
  exact
    (straightenedThreeCycle_class _ _ (triangleThreeSimplexHomotopy_face x) h₀
          (edgeNormalizedThreeCycle x c)).trans
      (edgeNormalizedThreeCycle_class x c)

private theorem ThirdHurewicz.basedThreeSimplex_boundary {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom (FirstHurewicz.simplexChain X 3 τ.val) = 0 := by
  change (FirstHurewicz.singularComplex X).d 3 2 (FirstHurewicz.simplexChain X 3 τ.val) = 0
  rw [FirstHurewicz.boundary_simplex]
  simp [basedThreeSimplex_face, Fin.sum_univ_succ]

private def ThirdHurewicz.basedThreeSimplexChain {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : FirstHurewicz.Chains X 3 :=
  FirstHurewicz.simplexChain X 3 τ.val -
    FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x)

private theorem
    ThirdHurewicz.basedThreeSimplexChain_boundary {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom (basedThreeSimplexChain τ) = 0 := by
  rw [basedThreeSimplexChain, map_sub, basedThreeSimplex_boundary]
  have hc := basedThreeSimplex_boundary (constantBasedThreeSimplex x)
  change
    ((FirstHurewicz.singularComplex X).d 3 2).hom
        (FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x)) =
      0 at hc
  rw [hc, sub_self]

private def ThirdHurewicz.basedThreeSimplexCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 3
    (basedThreeSimplexChain τ) (basedThreeSimplexChain_boundary τ)

@[simp]
private theorem ThirdHurewicz.basedThreeSimplexCycle_val {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    (basedThreeSimplexCycle τ).val =
      FirstHurewicz.simplexChain X 3 τ.val -
        FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x) :=
  rfl

private def
    ThirdHurewicz.thirdHomologyDesc {X : Type} [TopologicalSpace X] {M : Type*} [AddCommGroup M]
    [Module ℤ M] (F : FirstHurewicz.Chains X 3 →ₗ[ℤ] M)
    (hF :
      ∀ b : FirstHurewicz.Chains X 4, F (((FirstHurewicz.singularComplex X).d 4 3).hom b) = 0) :
    SingularMayerVietoris.SingularHomology X 3 →ₗ[ℤ] M :=
  PeriodTorusHigherHomology.homologyDesc (FirstHurewicz.singularComplex X) 3
    (F.comp
      (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3).subtype)
    (fun b => hF b)

@[simp]
private theorem
    ThirdHurewicz.thirdHomologyDesc_cycleClass {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (F : FirstHurewicz.Chains X 3 →ₗ[ℤ] M)
    (hF : ∀ b : FirstHurewicz.Chains X 4, F (((FirstHurewicz.singularComplex X).d 4 3).hom b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    thirdHomologyDesc F hF
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c) =
      F c.1 :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass (FirstHurewicz.singularComplex X) 3 _ _ c

private theorem
    ThirdHurewicz.comp_thirdHomologyDesc_eq_id {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (F : FirstHurewicz.Chains X 3 →ₗ[ℤ] M)
    (hF : ∀ b : FirstHurewicz.Chains X 4, F (((FirstHurewicz.singularComplex X).d 4 3).hom b) = 0)
    (g : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 3)
    (hg :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3,
        g (F c.1) =
          SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c) :
    g.comp (thirdHomologyDesc F hF) = LinearMap.id := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (FirstHurewicz.singularComplex X) 3
  intro c
  simpa only [LinearMap.comp_apply, thirdHomologyDesc_cycleClass, LinearMap.id_apply] using hg c

private def ThirdHurewicz.constantThreeChain {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains X 3 :=
  FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x)

private def ThirdHurewicz.constantFourChain {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains X 4 :=
  FirstHurewicz.simplexChain X 4 (ContinuousMap.const (FirstHurewicz.Simplex 4) x)

private theorem
    ThirdHurewicz.boundaryThree_constantThreeChain {X : Type} [TopologicalSpace X] (x : X) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom (constantThreeChain x) = 0 := by
  rw [constantThreeChain, FirstHurewicz.boundary_simplex]
  change
    (∑ i : Fin 4,
        (-1 : ℤ) ^ i.val •
          FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x)) =
      0
  simp [Fin.sum_univ_succ]

private theorem
    ThirdHurewicz.boundaryFour_constantFourChain {X : Type} [TopologicalSpace X] (x : X) :
    ((FirstHurewicz.singularComplex X).d 4 3).hom (constantFourChain x) = constantThreeChain x := by
  rw [constantFourChain, FirstHurewicz.boundary_simplex]
  change (∑ i : Fin 5, (-1 : ℤ) ^ i.val • constantThreeChain x) = constantThreeChain x
  simp [Fin.sum_univ_succ]

private def ThirdHurewicz.constantThreeCycle {X : Type} [TopologicalSpace X] (x : X) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 3
    (constantThreeChain x) (boundaryThree_constantThreeChain x)

@[simp]
private theorem ThirdHurewicz.constantThreeCycle_val {X : Type} [TopologicalSpace X] (x : X) :
    (constantThreeCycle x).1 = constantThreeChain x :=
  rfl

@[simp]
private theorem ThirdHurewicz.constantThreeCycle_class {X : Type} [TopologicalSpace X] (x : X) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (constantThreeCycle x) =
      0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        3 _).mpr
  exact ⟨constantFourChain x, boundaryFour_constantFourChain x⟩

private def ThirdHurewicz.normalizedThreeSimplexCycleOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    FirstHurewicz.Chains X 3 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  FirstHurewicz.chainLift X 3 fun smp => basedThreeSimplexCycle (normalizedThreeSimplex x smp)

@[simp]
private theorem
    ThirdHurewicz.normalizedThreeSimplexCycleOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 3) :
    normalizedThreeSimplexCycleOperator x (FirstHurewicz.simplexChain X 3 smp) =
      basedThreeSimplexCycle (normalizedThreeSimplex x smp) :=
  FirstHurewicz.chainLift_simplex X 3 _ smp

private theorem
    ThirdHurewicz.normalizedThreeSimplexCycleOperator_val {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (c : FirstHurewicz.Chains X 3) :
    (normalizedThreeSimplexCycleOperator x c).val =
      FirstHurewicz.chainLift X 3
        (fun smp =>
          FirstHurewicz.simplexChain X 3 (normalizedThreeSimplex x smp).val -
            FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x))
        c := by
  have h :
    (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3).subtype.comp
        (normalizedThreeSimplexCycleOperator x) =
      FirstHurewicz.chainLift X 3
        (fun smp =>
          FirstHurewicz.simplexChain X 3 (normalizedThreeSimplex x smp).val -
            FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x)) := by
    apply FirstHurewicz.chainMap_ext X 3
    intro smp
    simp only [LinearMap.comp_apply, normalizedThreeSimplexCycleOperator_simplex,
      Submodule.subtype_apply, basedThreeSimplexCycle_val, FirstHurewicz.chainLift_simplex]
  exact LinearMap.congr_fun h c

private theorem
    ThirdHurewicz.normalizedThreeSimplexCycleOperator_cycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    normalizedThreeSimplexCycleOperator x c.val =
      normalizedThreeCycle x c -
        SecondHurewicz.SimplyConnected.chainAugmentation X 3 c.val • constantThreeCycle x := by
  apply Subtype.ext
  change
    (normalizedThreeSimplexCycleOperator x c.val).val =
      (normalizedThreeCycle x c).val -
        SecondHurewicz.SimplyConnected.chainAugmentation X 3 c.val • (constantThreeCycle x).val
  rw [normalizedThreeSimplexCycleOperator_val,
    SecondHurewicz.SimplyConnected.chainLift_sub_constant, normalizedThreeCycle_val,
    constantThreeCycle_val]
  rfl

private theorem
    ThirdHurewicz.normalizedThreeSimplexCycleOperator_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (normalizedThreeSimplexCycleOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c := by
  rw [normalizedThreeSimplexCycleOperator_cycle, map_sub, map_zsmul, constantThreeCycle_class,
    zsmul_zero, sub_zero, normalizedThreeCycle_class]

private abbrev ThirdHurewicz.Geometry.Cube3 :=
  Fin 3 → (unitInterval)

private def ThirdHurewicz.Geometry.cubeAffineSimplex {n : ℕ} (v : Fin (n + 1) → Cube3) :
    C(FirstHurewicz.Simplex n, Cube3)
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
private theorem
    ThirdHurewicz.Geometry.cubeAffineSimplex_coordinate {n : ℕ} (v : Fin (n + 1) → Cube3)
    (s : FirstHurewicz.Simplex n) (i : Fin 3) :
    (cubeAffineSimplex v s i : ℝ) = ∑ j, s j * (v j i : ℝ) :=
  rfl

private theorem ThirdHurewicz.Geometry.cubeAffineSimplex_face {n : ℕ} (v : Fin (n + 2) → Cube3)
    (i : Fin (n + 2)) :
    (cubeAffineSimplex v).comp (FirstHurewicz.simplexFace n i) =
      cubeAffineSimplex (fun j => v (i.succAbove j)) := by
  ext s k
  change
    (∑ j : Fin (n + 2), FirstHurewicz.simplexFace n i s j * (v j k : ℝ)) =
      ∑ j : Fin (n + 1), s j * (v (i.succAbove j) k : ℝ)
  rw [Fin.sum_univ_succAbove _ i]
  simp only [FirstHurewicz.simplexFace_apply_self, MulZeroClass.zero_mul,
    FirstHurewicz.simplexFace_apply_succAbove, zero_add]

private theorem ThirdHurewicz.Geometry.cubeAffineSimplex_constant_coordinate {n : ℕ}
    (v : Fin (n + 1) → Cube3) (i : Fin 3) (c : (unitInterval)) (h : ∀ j, v j i = c)
    (s : FirstHurewicz.Simplex n) : cubeAffineSimplex v s i = c := by
  apply Subtype.ext
  simp only [cubeAffineSimplex_coordinate, h, ← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

private def
    ThirdHurewicz.Geometry.cubeVertex (e : Equiv.Perm (Fin 3)) (k : Fin 4) : Cube3 := fun i =>
  if (e.symm i).val < k.val then 1 else 0

private def ThirdHurewicz.Geometry.cubeTetrahedron (e : Equiv.Perm (Fin 3)) :
    C(FirstHurewicz.Simplex 3, Cube3) :=
  cubeAffineSimplex (cubeVertex e)

@[simp]
private theorem ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) : (cubeTetrahedron e s (e 0) : ℝ) = s 1 + s 2 + s 3 := by
  simp [cubeTetrahedron, cubeAffineSimplex_coordinate, cubeVertex, Fin.sum_univ_succ, add_assoc]

@[simp]
private theorem ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) : (cubeTetrahedron e s (e 1) : ℝ) = s 2 + s 3 := by
  simp [cubeTetrahedron, cubeAffineSimplex_coordinate, cubeVertex, Fin.sum_univ_succ]

@[simp]
private theorem ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) : (cubeTetrahedron e s (e 2) : ℝ) = s 3 := by
  simp [cubeTetrahedron, cubeAffineSimplex_coordinate, cubeVertex, Fin.sum_univ_succ]

private theorem ThirdHurewicz.Geometry.cubeTetrahedron_order_first (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) : cubeTetrahedron e s (e 1) ≤ cubeTetrahedron e s (e 0) := by
  change (cubeTetrahedron e s (e 1) : ℝ) ≤ (cubeTetrahedron e s (e 0) : ℝ)
  rw [cubeTetrahedron_coordinate_one, cubeTetrahedron_coordinate_zero]
  linarith [stdSimplex.zero_le s 1]

private theorem ThirdHurewicz.Geometry.cubeTetrahedron_order_second (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) : cubeTetrahedron e s (e 2) ≤ cubeTetrahedron e s (e 1) := by
  change (cubeTetrahedron e s (e 2) : ℝ) ≤ (cubeTetrahedron e s (e 1) : ℝ)
  rw [cubeTetrahedron_coordinate_two, cubeTetrahedron_coordinate_one]
  exact le_add_of_nonneg_left (stdSimplex.zero_le s 2)

private theorem ThirdHurewicz.Geometry.cubeTetrahedron_face_zero_coordinate (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 2) :
    cubeTetrahedron e (FirstHurewicz.simplexFace 2 0 s) (e 0) = 1 := by
  change ((cubeAffineSimplex (cubeVertex e)).comp (FirstHurewicz.simplexFace 2 0)) s (e 0) = 1
  rw [cubeAffineSimplex_face]
  apply cubeAffineSimplex_constant_coordinate
  intro j
  fin_cases j <;> simp [cubeVertex, Fin.succAbove]

private theorem
    ThirdHurewicz.Geometry.cubeTetrahedron_face_three_coordinate (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 2) :
    cubeTetrahedron e (FirstHurewicz.simplexFace 2 3 s) (e 2) = 0 := by
  change ((cubeAffineSimplex (cubeVertex e)).comp (FirstHurewicz.simplexFace 2 3)) s (e 2) = 0
  rw [cubeAffineSimplex_face]
  apply cubeAffineSimplex_constant_coordinate
  intro j
  fin_cases j <;> simp [cubeVertex, Fin.succAbove]

private theorem ThirdHurewicz.Geometry.cubeTetrahedron_face_zero_boundary (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 2) :
    cubeTetrahedron e (FirstHurewicz.simplexFace 2 0 s) ∈ Cube.boundary (Fin 3) :=
  ⟨e 0, Or.inr (cubeTetrahedron_face_zero_coordinate e s)⟩

private theorem ThirdHurewicz.Geometry.cubeTetrahedron_face_three_boundary (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 2) :
    cubeTetrahedron e (FirstHurewicz.simplexFace 2 3 s) ∈ Cube.boundary (Fin 3) :=
  ⟨e 2, Or.inl (cubeTetrahedron_face_three_coordinate e s)⟩

private theorem ThirdHurewicz.Geometry.cubeTetrahedron_face_one_swap (e : Equiv.Perm (Fin 3)) :
    (cubeTetrahedron e).comp (FirstHurewicz.simplexFace 2 1) =
      (cubeTetrahedron ((Equiv.swap 0 1).trans e)).comp (FirstHurewicz.simplexFace 2 1) := by
  simp only [cubeTetrahedron, cubeAffineSimplex_face]
  congr 1
  funext j i
  obtain ⟨k, rfl⟩ := e.surjective i
  fin_cases j <;> fin_cases k <;> simp [cubeVertex, Equiv.swap_apply_def, Fin.succAbove]

private theorem ThirdHurewicz.Geometry.cubeTetrahedron_face_two_swap (e : Equiv.Perm (Fin 3)) :
    (cubeTetrahedron e).comp (FirstHurewicz.simplexFace 2 2) =
      (cubeTetrahedron ((Equiv.swap 1 2).trans e)).comp (FirstHurewicz.simplexFace 2 2) := by
  simp only [cubeTetrahedron, cubeAffineSimplex_face]
  congr 1
  funext j i
  obtain ⟨k, rfl⟩ := e.surjective i
  fin_cases j <;> fin_cases k <;> simp [cubeVertex, Equiv.swap_apply_def, Fin.succAbove]

private def ThirdHurewicz.Geometry.cubeOrientation (e : Equiv.Perm (Fin 3)) : ℤ :=
  Equiv.Perm.sign e

@[simp]
private theorem
    ThirdHurewicz.Geometry.cubeOrientation_refl : cubeOrientation (Equiv.refl (Fin 3)) = 1 := by
  simp [cubeOrientation]

private theorem ThirdHurewicz.Geometry.cubeOrientation_swap (e : Equiv.Perm (Fin 3)) {i j : Fin 3}
    (h : i ≠ j) : cubeOrientation ((Equiv.swap i j).trans e) = -cubeOrientation e := by
  simp [cubeOrientation, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap h]

private theorem ThirdHurewicz.threeSimplex_coordinate_sum (s : FirstHurewicz.Simplex 3) :
    s 0 + (s 1 + s 2 + s 3) = 1 := by
  have hs := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
  linarith

private theorem ThirdHurewicz.threeSimplexQuotient_cubeTetrahedron_refl :
    threeSimplexQuotient.comp (Geometry.cubeTetrahedron (Equiv.refl (Fin 3))) =
      ContinuousMap.id (FirstHurewicz.Simplex 3) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  funext i
  have h₁ : s 2 + s 3 ≤ s 1 + s 2 + s 3 := by linarith [stdSimplex.zero_le s 1]
  have h₂ : s 3 ≤ s 2 + s 3 := le_add_of_nonneg_left (stdSimplex.zero_le s 2)
  have h₃ : s 3 ≤ s 1 + s 2 + s 3 := h₂.trans h₁
  have hu₀ := Geometry.cubeTetrahedron_coordinate_zero (Equiv.refl (Fin 3)) s
  have hu₁ := Geometry.cubeTetrahedron_coordinate_one (Equiv.refl (Fin 3)) s
  have hu₂ := Geometry.cubeTetrahedron_coordinate_two (Equiv.refl (Fin 3)) s
  change (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ) = _ at hu₀
  change (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ) = _ at hu₁
  change (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 2 : ℝ) = _ at hu₂
  fin_cases i
  · change 1 - (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ) = s 0
    rw [hu₀]
    linarith [threeSimplex_coordinate_sum s]
  · change
      (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ) -
          Min.min (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ)
            (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ) =
        s 1
    rw [hu₀, hu₁, min_eq_right h₁]
    ring
  · change
      Min.min (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ)
            (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ) -
          Min.min (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ)
            (Min.min (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ)
              (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 2 : ℝ)) =
        s 2
    rw [hu₀, hu₁, hu₂, min_eq_right h₁, min_eq_right h₂, min_eq_right h₃]
    ring
  · change
      Min.min (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ)
          (Min.min (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ)
            (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 2 : ℝ)) =
        s 3
    rw [hu₀, hu₁, hu₂, min_eq_right h₂, min_eq_right h₃]

private theorem ThirdHurewicz.cubeTetrahedron_coordinates_antitone (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) :
    Antitone (fun i => (Geometry.cubeTetrahedron e s (e i) : ℝ)) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  fin_cases i
  · exact Geometry.cubeTetrahedron_order_first e s
  · exact Geometry.cubeTetrahedron_order_second e s

private theorem ThirdHurewicz.cubeTetrahedron_coordinate_inversion (e : Equiv.Perm (Fin 3))
    (he : e ≠ Equiv.refl (Fin 3)) (s : FirstHurewicz.Simplex 3) :
    (Geometry.cubeTetrahedron e s 0 : ℝ) ≤ Geometry.cubeTetrahedron e s 1 ∨
      (Geometry.cubeTetrahedron e s 1 : ℝ) ≤ Geometry.cubeTetrahedron e s 2 := by
  by_contra h
  obtain ⟨h₁, h₂⟩ := not_or.mp h
  have hu : StrictAnti (fun i => (Geometry.cubeTetrahedron e s i : ℝ)) := by
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    fin_cases i
    · exact lt_of_not_ge h₁
    · exact lt_of_not_ge h₂
  have hm : Monotone e := by
    intro i j hij
    exact hu.le_iff_ge.mp (cubeTetrahedron_coordinates_antitone e s hij)
  apply he
  apply Equiv.ext
  intro i
  exact (hm.strictMono_of_injective e.injective).apply_eq

private theorem ThirdHurewicz.threeSimplexQuotient_cubeTetrahedron_boundary (e : Equiv.Perm (Fin 3))
    (he : e ≠ Equiv.refl (Fin 3)) (s : FirstHurewicz.Simplex 3) :
    threeSimplexQuotient (Geometry.cubeTetrahedron e s) ∈ threeSimplexBoundary := by
  rcases cubeTetrahedron_coordinate_inversion e he s with h | h
  · exact threeSimplexQuotient_boundary_of_first_le _ h
  · exact threeSimplexQuotient_boundary_of_second_le _ h

private theorem
    ThirdHurewicz.basedThreeSimplexLoop_cubeTetrahedron_refl {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedThreeSimplex x) :
    (basedThreeSimplexLoop τ).val.comp (Geometry.cubeTetrahedron (Equiv.refl (Fin 3))) = τ.val := by
  change (τ.val.comp threeSimplexQuotient).comp _ = _
  rw [ContinuousMap.comp_assoc, threeSimplexQuotient_cubeTetrahedron_refl, ContinuousMap.comp_id]

private theorem
    ThirdHurewicz.basedThreeSimplexLoop_cubeTetrahedron_other {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedThreeSimplex x) (e : Equiv.Perm (Fin 3)) (he : e ≠ Equiv.refl (Fin 3)) :
    (basedThreeSimplexLoop τ).val.comp (Geometry.cubeTetrahedron e) =
      ContinuousMap.const (FirstHurewicz.Simplex 3) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ (threeSimplexQuotient_cubeTetrahedron_boundary e he s)

private theorem ThirdHurewicz.threeCubeOrientation_sum :
    ∑ e : Equiv.Perm (Fin 3), Geometry.cubeOrientation e = 0 := by
  have h := Equiv.sum_comp (Equiv.mulRight (Equiv.swap (0 : Fin 3) 1)) Geometry.cubeOrientation
  change
    (∑ e : Equiv.Perm (Fin 3), Geometry.cubeOrientation ((Equiv.swap 0 1).trans e)) =
      ∑ e : Equiv.Perm (Fin 3), Geometry.cubeOrientation e at h
  simp_rw [Geometry.cubeOrientation_swap _ (by decide : (0 : Fin 3) ≠ 1)] at h
  rw [Finset.sum_neg_distrib] at h
  omega

private theorem ThirdHurewicz.basedThreeSimplex_tetrahedronChain_sum {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedThreeSimplex x) :
    (∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e •
          FirstHurewicz.simplexChain X 3
            ((basedThreeSimplexLoop τ).val.comp (Geometry.cubeTetrahedron e))) =
      basedThreeSimplexChain τ := by
  classical
  let c := FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x)
  have heq (e : Equiv.Perm (Fin 3)) :
    Geometry.cubeOrientation e •
        FirstHurewicz.simplexChain X 3
          ((basedThreeSimplexLoop τ).val.comp (Geometry.cubeTetrahedron e)) =
      (if e = Equiv.refl (Fin 3) then basedThreeSimplexChain τ else 0) +
        Geometry.cubeOrientation e • c := by
    by_cases he : e = Equiv.refl (Fin 3)
    · subst e
      rw [basedThreeSimplexLoop_cubeTetrahedron_refl, Geometry.cubeOrientation_refl, one_smul,
        ite_eq_left rfl, one_smul]
      change FirstHurewicz.simplexChain X 3 τ.val = (FirstHurewicz.simplexChain X 3 τ.val - c) + c
      abel
    · rw [basedThreeSimplexLoop_cubeTetrahedron_other τ e he, ite_eq_right he, zero_add]
  calc
    _ =
        ∑ e : Equiv.Perm (Fin 3),
          ((if e = Equiv.refl (Fin 3) then basedThreeSimplexChain τ else 0) +
            Geometry.cubeOrientation e • c) :=
      Finset.sum_congr rfl (fun e _ => heq e)
    _ = basedThreeSimplexChain τ + (∑ e : Equiv.Perm (Fin 3), Geometry.cubeOrientation e) • c := by
      rw [Finset.sum_add_distrib]
      have hc :
        (∑ e : Equiv.Perm (Fin 3), Geometry.cubeOrientation e) • c =
          ∑ e : Equiv.Perm (Fin 3), Geometry.cubeOrientation e • c := by
        let f : ℤ →+ FirstHurewicz.Chains X 3 :=
          { toFun := fun n => n • c
            map_zero' := zero_zsmul c
            map_add' := fun a b => add_zsmul c a b }
        exact map_sum f Geometry.cubeOrientation Finset.univ
      rw [← hc]
      simp
    _ = basedThreeSimplexChain τ := by rw [threeCubeOrientation_sum, zero_smul, add_zero]

private abbrev ThirdHurewicz.Remaining :=
  { j : Fin 3 // j ≠ 0 }

private def
    ThirdHurewicz.remainingCoordinates : C(Fin 2 → (unitInterval), Remaining → (unitInterval))
    where
  toFun u j := u (j.val.pred j.property)
  continuous_toFun := by fun_prop

@[simp]
private theorem ThirdHurewicz.remainingCoordinates_succ (u : Fin 2 → (unitInterval)) (i : Fin 2) :
    remainingCoordinates u ⟨i.succ, Fin.succ_ne_zero i⟩ = u i := by simp [remainingCoordinates]

private theorem ThirdHurewicz.remainingCoordinates_boundary {u : Fin 2 → (unitInterval)}
    (h : u ∈ Cube.boundary (Fin 2)) : remainingCoordinates u ∈ Cube.boundary Remaining := by
  obtain ⟨i, hi⟩ := h
  exact ⟨⟨i.succ, Fin.succ_ne_zero i⟩, by simpa using hi⟩

private abbrev ThirdHurewicz.BasedLoopSpace {X : Type} [TopologicalSpace X] (x : X) :=
  GenLoop Remaining X x

private def ThirdHurewicz.evaluation {X : Type} [TopologicalSpace X] (x : X) :
    C(BasedLoopSpace x × (Fin 2 → (unitInterval)), X)
    where
  toFun z := z.1 (remainingCoordinates z.2)
  continuous_toFun := by fun_prop

private theorem ThirdHurewicz.evaluation_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    evaluation x (p, u) = x :=
  GenLoop.boundary p _ (remainingCoordinates_boundary hu)

private theorem ThirdHurewicz.evaluation_comp_boundary {X : Type} [TopologicalSpace X] (x : X)
    (f : C((unitInterval), Fin 2 → (unitInterval))) (hf : ∀ t, f t ∈ Cube.boundary (Fin 2)) :
    (evaluation x).comp ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) =
      ContinuousMap.const (BasedLoopSpace x × (unitInterval)) x := by
  ext z
  exact evaluation_boundary x z.1 (f z.2) (hf z.2)

private def ThirdHurewicz.cubeCoordinates :
    C((unitInterval) × (Fin 2 → (unitInterval)), Fin 3 → (unitInterval))
    where
  toFun z := Cube.insertAt (0 : Fin 3) (z.1, remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp]
private theorem ThirdHurewicz.cubeCoordinates_zero (z : (unitInterval) × (Fin 2 → (unitInterval))) :
    cubeCoordinates z 0 = z.1 := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp]
private theorem ThirdHurewicz.cubeCoordinates_succ (z : (unitInterval) × (Fin 2 → (unitInterval)))
    (i : Fin 2) : cubeCoordinates z i.succ = z.2 i := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply, remainingCoordinates]

private def
    ThirdHurewicz.cubeMap {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) :
    C((unitInterval) × (Fin 2 → (unitInterval)), X) :=
  p.val.comp cubeCoordinates

private theorem ThirdHurewicz.evaluation_comp_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 3) p).toContinuousMap.prodMap
          (ContinuousMap.id (Fin 2 → (unitInterval)))) =
      cubeMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def ThirdHurewicz.squareSideLeft (t : (unitInterval)) :
    C((unitInterval), Fin 2 → (unitInterval)) :=
  SecondHurewicz.squareCoordinates.comp (PeriodTorusHigherHomology.crossInsertLeft t)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def ThirdHurewicz.squareSideRight (t : (unitInterval)) :
    C((unitInterval), Fin 2 → (unitInterval)) :=
  SecondHurewicz.squareCoordinates.comp (PeriodTorusHigherHomology.crossInsertRight t)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.squareSideLeft_boundary (t : (unitInterval)) (ht : t = 0 ∨ t = 1)
    (s : (unitInterval)) : squareSideLeft t s ∈ Cube.boundary (Fin 2) := by
  refine ⟨0, ?_⟩
  change
    SecondHurewicz.squareCoordinates (t, s) 0 = 0 ∨ SecondHurewicz.squareCoordinates (t, s) 0 = 1
  simpa only [SecondHurewicz.squareCoordinates_zero] using ht

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.squareSideRight_boundary (t : (unitInterval)) (ht : t = 0 ∨ t = 1)
    (s : (unitInterval)) : squareSideRight t s ∈ Cube.boundary (Fin 2) := by
  refine ⟨1, ?_⟩
  change
    SecondHurewicz.squareCoordinates (s, t) 1 = 0 ∨ SecondHurewicz.squareCoordinates (s, t) 1 = 1
  simpa only [SecondHurewicz.squareCoordinates_one] using ht

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.fundamentalSquareChain_boundary :
    FirstHurewicz.boundaryTwo (Fin 2 → (unitInterval)) SecondHurewicz.fundamentalSquareChain =
      FirstHurewicz.inducedChain (squareSideLeft 1) 1 SecondHurewicz.intervalChain -
          FirstHurewicz.inducedChain (squareSideLeft 0) 1 SecondHurewicz.intervalChain -
        (FirstHurewicz.inducedChain (squareSideRight 1) 1 SecondHurewicz.intervalChain -
          FirstHurewicz.inducedChain (squareSideRight 0) 1 SecondHurewicz.intervalChain) := by
  change
    ((FirstHurewicz.singularComplex (Fin 2 → (unitInterval))).d 2 1).hom
        (FirstHurewicz.inducedChain SecondHurewicz.squareCoordinates 2
          SecondHurewicz.productSquareChain) =
      _
  rw [← FirstHurewicz.inducedChain_boundary]
  change
    FirstHurewicz.inducedChain SecondHurewicz.squareCoordinates 1
        (FirstHurewicz.boundaryTwo ((unitInterval) × (unitInterval))
          SecondHurewicz.productSquareChain) =
      _
  rw [SecondHurewicz.productSquareChain_boundary]
  simp only [map_sub, squareSideLeft, squareSideRight, FirstHurewicz.inducedChain_comp,
    LinearMap.comp_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.evaluated_edge_boundaryMap {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (f : C((unitInterval), Fin 2 → (unitInterval))) (hf : ∀ t, f t ∈ Cube.boundary (Fin 2)) :
    FirstHurewicz.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 2 → (unitInterval)) 1
          a (FirstHurewicz.inducedChain f 1 SecondHurewicz.intervalChain)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × (unitInterval)) x) 2
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1 a
          SecondHurewicz.intervalChain) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (BasedLoopSpace x)) f 1 a
      SecondHurewicz.intervalChain
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 2).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) 2))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.evaluated_triangle_boundaryMap {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2)
    (f : C((unitInterval), Fin 2 → (unitInterval))) (hf : ∀ t, f t ∈ Cube.boundary (Fin 2)) :
    FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 2 → (unitInterval)) 1 a
          (FirstHurewicz.inducedChain f 1 SecondHurewicz.intervalChain)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × (unitInterval)) x) 3
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 1 a
          SecondHurewicz.intervalChain) := by
  have h :=
    PeriodTorusHigherHomology.crossProductTriangle_natural (ContinuousMap.id (BasedLoopSpace x)) f
      1 a SecondHurewicz.intervalChain
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
private theorem
    ThirdHurewicz.evaluated_edge_squareBoundary_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    FirstHurewicz.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 2 → (unitInterval)) 1
          a
          (FirstHurewicz.boundaryTwo (Fin 2 → (unitInterval))
            SecondHurewicz.fundamentalSquareChain)) =
      0 := by
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a (squareSideLeft t) (squareSideLeft_boundary t ht)
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a (squareSideRight t) (squareSideRight_boundary t ht)
  simp only [fundamentalSquareChain_boundary, map_sub, hL 1 (Or.inr rfl), hL 0 (Or.inl rfl),
    hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    ThirdHurewicz.evaluated_triangle_squareBoundary_cancel {X : Type} [TopologicalSpace X]
    (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 2 → (unitInterval)) 1 a
          (FirstHurewicz.boundaryTwo (Fin 2 → (unitInterval))
            SecondHurewicz.fundamentalSquareChain)) =
      0 := by
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a (squareSideLeft t) (squareSideLeft_boundary t ht)
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a (squareSideRight t) (squareSideRight_boundary t ht)
  simp only [fundamentalSquareChain_boundary, map_sub, hL 1 (Or.inr rfl), hL 0 (Or.inl rfl),
    hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def ThirdHurewicz.suspensionOne {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 1 →ₗ[ℤ] FirstHurewicz.Chains X 3 :=
  (FirstHurewicz.inducedChain (evaluation x) 3).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 2 → (unitInterval)) 2)
      SecondHurewicz.fundamentalSquareChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem ThirdHurewicz.suspensionOne_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    suspensionOne x a =
      FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 2 → (unitInterval)) 2
          a SecondHurewicz.fundamentalSquareChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def ThirdHurewicz.suspensionTwo {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 2 →ₗ[ℤ] FirstHurewicz.Chains X 4 :=
  (FirstHurewicz.inducedChain (evaluation x) 4).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (Fin 2 → (unitInterval))
        2)
      SecondHurewicz.fundamentalSquareChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem ThirdHurewicz.suspensionTwo_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a =
      FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 2 → (unitInterval)) 2 a SecondHurewicz.fundamentalSquareChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    ThirdHurewicz.boundaryThree_suspensionOne_of_cycle {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (ha : FirstHurewicz.boundaryOne (BasedLoopSpace x) a = 0) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom (suspensionOne x a) = 0 := by
  rw [suspensionOne_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary 1]
  change
    FirstHurewicz.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductZeroLeft (BasedLoopSpace x)
            (Fin 2 → (unitInterval)) 2 (FirstHurewicz.boundaryOne (BasedLoopSpace x) a)
            SecondHurewicz.fundamentalSquareChain -
          PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 2 → (unitInterval)) 1
            a
            (FirstHurewicz.boundaryTwo (Fin 2 → (unitInterval))
              SecondHurewicz.fundamentalSquareChain)) =
      0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg, evaluated_edge_squareBoundary_cancel,
    neg_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.boundaryFour_suspensionTwo {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    ((FirstHurewicz.singularComplex X).d 4 3).hom (suspensionTwo x a) =
      suspensionOne x (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductTriangle_boundary 1]
  change
    FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 2 → (unitInterval)) 2
            (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a)
            SecondHurewicz.fundamentalSquareChain +
          PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
            (Fin 2 → (unitInterval)) 1 a
            (FirstHurewicz.boundaryTwo (Fin 2 → (unitInterval))
              SecondHurewicz.fundamentalSquareChain)) =
      _
  rw [map_add, evaluated_triangle_squareBoundary_cancel, add_zero]
  rfl

private def ThirdHurewicz.pathCubeCycle {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 3
    (suspensionOne x (FirstHurewicz.pathChain p))
    (boundaryThree_suspensionOne_of_cycle x (FirstHurewicz.pathChain p)
      (FirstHurewicz.boundaryOne_loop p))

@[simp]
private theorem ThirdHurewicz.pathCubeCycle_val {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathCubeCycle x p).1 = suspensionOne x (FirstHurewicz.pathChain p) :=
  rfl

private def ThirdHurewicz.pathCubeClass {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.SingularHomology X 3 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
    (pathCubeCycle x p)

private theorem ThirdHurewicz.pathCube_homotopy_boundary {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((FirstHurewicz.singularComplex X).d 4 3).hom
        (suspensionTwo x (FirstHurewicz.homotopyChain H)) =
      (pathCubeCycle x p).1 - (pathCubeCycle x q).1 := by
  rw [boundaryFour_suspensionTwo, FirstHurewicz.boundaryTwo_loopHomotopy, map_sub]
  rfl

private theorem ThirdHurewicz.pathCubeClass_homotopy {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathCubeClass x p = pathCubeClass x q :=
  (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 3 _
        _).mpr
    ⟨suspensionTwo x (FirstHurewicz.homotopyChain H), pathCube_homotopy_boundary x H⟩

private theorem ThirdHurewicz.pathCubeClass_homotopic {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathCubeClass x p = pathCubeClass x q := by
  obtain ⟨H⟩ := h
  exact pathCubeClass_homotopy x H

@[simp]
private theorem ThirdHurewicz.pathCubeClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathCubeClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        3 _).mpr
  refine
    ⟨suspensionTwo x (FirstHurewicz.constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundaryFour_suspensionTwo, FirstHurewicz.boundaryTwo_constantTriangleChain]
  rfl

private theorem ThirdHurewicz.pathCube_concat_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((FirstHurewicz.singularComplex X).d 4 3).hom
        (-suspensionTwo x (FirstHurewicz.concatChain p q)) =
      (pathCubeCycle x (p.trans q)).1 - ((pathCubeCycle x p).1 + (pathCubeCycle x q).1) := by
  rw [map_neg, boundaryFour_suspensionTwo, FirstHurewicz.boundaryTwo_concatChain, map_add,
    map_sub]
  simp only [pathCubeCycle_val]
  abel

private theorem ThirdHurewicz.pathCubeClass_trans {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathCubeClass x (p.trans q) = pathCubeClass x p + pathCubeClass x q := by
  unfold pathCubeClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 3 _
        _).mpr
  exact ⟨-suspensionTwo x (FirstHurewicz.concatChain p q), pathCube_concat_boundary x p q⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def ThirdHurewicz.productCubeChain :
    FirstHurewicz.Chains ((unitInterval) × (Fin 2 → (unitInterval))) 3 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 2 → (unitInterval)) 2
    SecondHurewicz.intervalChain SecondHurewicz.fundamentalSquareChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def ThirdHurewicz.fundamentalCubeChain : FirstHurewicz.Chains (Fin 3 → (unitInterval)) 3 :=
  FirstHurewicz.inducedChain cubeCoordinates 3 productCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.suspensionOne_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) :
    suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 3) p)) =
      FirstHurewicz.inducedChain (cubeMap p) 3 productCubeChain := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural
      (GenLoop.toLoop (0 : Fin 3) p).toContinuousMap (ContinuousMap.id (Fin 2 → (unitInterval))) 2
      SecondHurewicz.intervalChain SecondHurewicz.fundamentalSquareChain
  rw [SecondHurewicz.induced_intervalChain, FirstHurewicz.inducedChain_id,
    LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 3).comp
          (FirstHurewicz.inducedChain
            ((GenLoop.toLoop (0 : Fin 3) p).toContinuousMap.prodMap
              (ContinuousMap.id (Fin 2 → (unitInterval))))
            3))
        productCubeChain =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_toLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    ThirdHurewicz.cubeChain {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) :
    FirstHurewicz.Chains X 3 :=
  suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 3) p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.cubeChain_eq_induced {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) :
    cubeChain p = FirstHurewicz.inducedChain p.val 3 fundamentalCubeChain := by
  rw [cubeChain, suspensionOne_toLoop]
  change
    FirstHurewicz.inducedChain (p.val.comp cubeCoordinates) 3 productCubeChain =
      ((FirstHurewicz.inducedChain p.val 3).comp (FirstHurewicz.inducedChain cubeCoordinates 3))
        productCubeChain
  rw [FirstHurewicz.inducedChain_comp]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    ThirdHurewicz.cubeCycle {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  pathCubeCycle x (GenLoop.toLoop (0 : Fin 3) p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def ThirdHurewicz.cubeHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : SingularMayerVietoris.SingularHomology X 3 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
    (cubeCycle p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    ThirdHurewicz.cubeHomologyClass_eq_pathCubeClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) :
    cubeHomologyClass p = pathCubeClass x (GenLoop.toLoop (0 : Fin 3) p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.cubeHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 3) X x} (h : GenLoop.Homotopic p q) :
    cubeHomologyClass p = cubeHomologyClass q :=
  pathCubeClass_homotopic x (GenLoop.homotopicTo (0 : Fin 3) h)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.toLoop_const {X : Type} [TopologicalSpace X] {x : X} :
    GenLoop.toLoop (0 : Fin 3) (GenLoop.const : GenLoop (Fin 3) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem ThirdHurewicz.cubeHomologyClass_const {X : Type} [TopologicalSpace X] {x : X} :
    cubeHomologyClass (GenLoop.const : GenLoop (Fin 3) X x) = 0 := by
  rw [cubeHomologyClass_eq_pathCubeClass, toLoop_const, pathCubeClass_refl]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.toLoop_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) :
    GenLoop.toLoop (0 : Fin 3) (GenLoop.transAt (0 : Fin 3) p q) =
      (GenLoop.toLoop (0 : Fin 3) p).trans (GenLoop.toLoop (0 : Fin 3) q) := by
  have h :=
    congrArg (GenLoop.toLoop (0 : Fin 3))
      (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 3)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.cubeHomologyClass_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) :
    cubeHomologyClass (GenLoop.transAt (0 : Fin 3) p q) =
      cubeHomologyClass p + cubeHomologyClass q := by
  simp only [cubeHomologyClass_eq_pathCubeClass, toLoop_transAt, pathCubeClass_trans]

private def ThirdHurewicz.Geometry.cubeBitVertex (v : Fin 3 → Fin 2) : Cube3 := fun i =>
  FirstHurewicz.pathSimplex Path.id (SingularMayerVietoris.stdVertices 1 (v i))

@[simp]
private theorem ThirdHurewicz.Geometry.cubeBitVertex_coordinate (v : Fin 3 → Fin 2) (i : Fin 3) :
    (cubeBitVertex v i : ℝ) = SingularMayerVietoris.stdVertices 1 (v i) 1 :=
  rfl

@[simp]
private theorem
    ThirdHurewicz.Geometry.cubeBitVertex_zero (v : Fin 3 → Fin 2) {i : Fin 3} (h : v i = 0) :
    cubeBitVertex v i = 0 := by simp [cubeBitVertex, h, SingularMayerVietoris.stdVertices]

@[simp]
private theorem
    ThirdHurewicz.Geometry.cubeBitVertex_one (v : Fin 3 → Fin 2) {i : Fin 3} (h : v i = 1) :
    cubeBitVertex v i = 1 := by simp [cubeBitVertex, h, SingularMayerVietoris.stdVertices]

private def ThirdHurewicz.Geometry.cubeTrianglePrism (v : Fin 3 → Fin 2 × Fin 2) :
    C(FirstHurewicz.Simplex 1 × FirstHurewicz.Simplex 2, Cube3) :=
  ThirdHurewicz.cubeCoordinates.comp
    ((FirstHurewicz.pathSimplex Path.id).prodMap
      (SecondHurewicz.squareCoordinates.comp
        (SecondHurewicz.SimplyConnected.squareAffineTriangle v)))

private theorem ThirdHurewicz.Geometry.affineSimplex_comp_selectedVertices {m n p : ℕ}
    (v : Fin (n + 1) → FirstHurewicz.Simplex p) (a : Fin (m + 1) → Fin (n + 1)) :
    (SingularMayerVietoris.affineSimplex v).comp
        (SingularMayerVietoris.affineSimplex
          (fun j => SingularMayerVietoris.stdVertices n (a j))) =
      SingularMayerVietoris.affineSimplex (fun j => v (a j)) := by
  rw [SingularMayerVietoris.affineSimplex_comp]
  congr 1
  funext j
  exact SingularMayerVietoris.affineSimplex_vertex v (a j)

private theorem ThirdHurewicz.Geometry.cubeTrianglePrism_affine {n : ℕ} (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin (n + 1) → Fin 2 × Fin 3) :
    (cubeTrianglePrism v).comp
        (PeriodTorusHigherHomology.productAffineSimplex
          (fun j =>
            (SingularMayerVietoris.stdVertices 1 (w j).1,
              SingularMayerVietoris.stdVertices 2 (w j).2))) =
      cubeAffineSimplex (fun j => cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2]) := by
  ext s i
  fin_cases i
  · change
      SingularMayerVietoris.affineSimplex (fun j => SingularMayerVietoris.stdVertices 1 (w j).1) s
          1 =
        _
    rw [SingularMayerVietoris.affineSimplex_coordinate]
    simp [cubeAffineSimplex_coordinate, cubeBitVertex_coordinate]
  · change
      SingularMayerVietoris.affineSimplex (fun j => SingularMayerVietoris.stdVertices 1 (v j).1)
          (SingularMayerVietoris.affineSimplex
            (fun j => SingularMayerVietoris.stdVertices 2 (w j).2) s)
          1 =
        _
    change
      ((SingularMayerVietoris.affineSimplex
                (fun j => SingularMayerVietoris.stdVertices 1 (v j).1)).comp
            (SingularMayerVietoris.affineSimplex
              (fun j => SingularMayerVietoris.stdVertices 2 (w j).2)))
          s 1 =
        _
    rw [affineSimplex_comp_selectedVertices, SingularMayerVietoris.affineSimplex_coordinate]
    simp [cubeAffineSimplex_coordinate, cubeBitVertex_coordinate]
  · change
      SingularMayerVietoris.affineSimplex (fun j => SingularMayerVietoris.stdVertices 1 (v j).2)
          (SingularMayerVietoris.affineSimplex
            (fun j => SingularMayerVietoris.stdVertices 2 (w j).2) s)
          1 =
        _
    change
      ((SingularMayerVietoris.affineSimplex
                (fun j => SingularMayerVietoris.stdVertices 1 (v j).2)).comp
            (SingularMayerVietoris.affineSimplex
              (fun j => SingularMayerVietoris.stdVertices 2 (w j).2)))
          s 1 =
        _
    rw [affineSimplex_comp_selectedVertices, SingularMayerVietoris.affineSimplex_coordinate]
    simp [cubeAffineSimplex_coordinate, cubeBitVertex_coordinate]

private theorem ThirdHurewicz.Geometry.cubeAffineSimplex_boundary_of_coordinate {n : ℕ}
    (v : Fin (n + 1) → Cube3) (i : Fin 3) (h : (∀ j, v j i = 0) ∨ (∀ j, v j i = 1))
    (s : FirstHurewicz.Simplex n) : cubeAffineSimplex v s ∈ Cube.boundary (Fin 3) := by
  rcases h with h | h
  · exact ⟨i, Or.inl (cubeAffineSimplex_constant_coordinate v i 0 h s)⟩
  · exact ⟨i, Or.inr (cubeAffineSimplex_constant_coordinate v i 1 h s)⟩

private theorem ThirdHurewicz.Geometry.loop_comp_cubeAffineSimplex_of_coordinate {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin 3) X x) (v : Fin (n + 1) → Cube3)
    (i : Fin 3) (h : (∀ j, v j i = 0) ∨ (∀ j, v j i = 1)) :
    p.val.comp (cubeAffineSimplex v) = ContinuousMap.const (FirstHurewicz.Simplex n) x := by
  ext s
  exact GenLoop.boundary p _ (cubeAffineSimplex_boundary_of_coordinate v i h s)

private theorem ThirdHurewicz.CubeSubdivision.formalEdgeCrossProduct_one_expansion_mo1973_7080
    {V W : Type*} (v : Fin 2 → V) (w : Fin 2 → W) :
    PeriodTorusHigherHomology.formalEdgeCrossProduct 1 (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 1, w 0), (v 1, w 1)] -
            SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 0, w 0), (v 0, w 1)] -
          SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 0, w 1), (v 1, w 1)] +
        SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 0, w 0), (v 1, w 0)] := by
  rw [PeriodTorusHigherHomology.formalEdgeCrossProduct_simplex_succ,
    PeriodTorusHigherHomology.formalPointCrossProduct_edge_boundary,
    PeriodTorusHigherHomology.formalBoundary_edge_simplex]
  simp only [map_sub, PeriodTorusHigherHomology.formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalCone_simplex]
  have hv₀ : (fun i : Fin 2 => (v 0, w i)) = ![(v 0, w 0), (v 0, w 1)] := by
    funext i
    fin_cases i <;> rfl
  have hv₁ : (fun i : Fin 2 => (v 1, w i)) = ![(v 1, w 0), (v 1, w 1)] := by
    funext i
    fin_cases i <;> rfl
  have hw₀ : (fun i : Fin 2 => (v i, w 0)) = ![(v 0, w 0), (v 1, w 0)] := by
    funext i
    fin_cases i <;> rfl
  have hw₁ : (fun i : Fin 2 => (v i, w 1)) = ![(v 0, w 1), (v 1, w 1)] := by
    funext i
    fin_cases i <;> rfl
  simp only [Function.comp_def, hv₀, hv₁, hw₀, hw₁]
  abel

private theorem ThirdHurewicz.CubeSubdivision.formalBoundary_triangle_simplex {W : Type*}
    (w : Fin 3 → W) :
    SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex ![w 1, w 2] -
          SingularMayerVietoris.formalSimplex ![w 0, w 2] +
        SingularMayerVietoris.formalSimplex ![w 0, w 1] := by
  have h₀ : w ∘ (0 : Fin 3).succAbove = ![w 1, w 2] := by
    funext i
    fin_cases i <;> rfl
  have h₁ : w ∘ (1 : Fin 3).succAbove = ![w 0, w 2] := by
    funext i
    fin_cases i <;> rfl
  have h₂ : w ∘ (2 : Fin 3).succAbove = ![w 0, w 1] := by
    funext i
    fin_cases i <;> rfl
  rw [SingularMayerVietoris.formalBoundary_simplex]
  change
    (∑ i : Fin 3, (-1 : ℤ) ^ i.val • SingularMayerVietoris.formalSimplex (w ∘ i.succAbove)) = _
  rw [Fin.sum_univ_succ, Fin.sum_univ_two]
  norm_num only [Fin.val_zero, Fin.val_succ, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_one_smul]
  change
    SingularMayerVietoris.formalSimplex (w ∘ (0 : Fin 3).succAbove) +
        (-SingularMayerVietoris.formalSimplex (w ∘ (1 : Fin 3).succAbove) +
          SingularMayerVietoris.formalSimplex (w ∘ (2 : Fin 3).succAbove)) =
      _
  rw [h₀, h₁, h₂]
  abel

private theorem ThirdHurewicz.CubeSubdivision.formalEdgeCrossProduct_two_expansion {V W : Type*}
    (v : Fin 2 → V) (w : Fin 3 → W) :
    PeriodTorusHigherHomology.formalEdgeCrossProduct 2 (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 1, w 0), (v 1, w 1), (v 1, w 2)] -
                            SingularMayerVietoris.formalSimplex
                              ![(v 0, w 0), (v 0, w 1), (v 1, w 1), (v 1, w 2)] +
                          SingularMayerVietoris.formalSimplex
                            ![(v 0, w 0), (v 0, w 1), (v 0, w 2), (v 1, w 2)] -
                        SingularMayerVietoris.formalSimplex
                          ![(v 0, w 0), (v 0, w 0), (v 0, w 1), (v 0, w 2)] +
                      SingularMayerVietoris.formalSimplex
                        ![(v 0, w 0), (v 0, w 1), (v 0, w 1), (v 0, w 2)] -
                    SingularMayerVietoris.formalSimplex
                      ![(v 0, w 0), (v 0, w 1), (v 0, w 1), (v 1, w 1)] +
                  SingularMayerVietoris.formalSimplex
                    ![(v 0, w 0), (v 0, w 0), (v 1, w 0), (v 1, w 2)] -
                SingularMayerVietoris.formalSimplex
                  ![(v 0, w 0), (v 0, w 0), (v 0, w 0), (v 0, w 2)] -
              SingularMayerVietoris.formalSimplex
                ![(v 0, w 0), (v 0, w 0), (v 0, w 2), (v 1, w 2)] -
            SingularMayerVietoris.formalSimplex
              ![(v 0, w 0), (v 0, w 0), (v 1, w 0), (v 1, w 1)] +
          SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 0, w 0), (v 0, w 0), (v 0, w 1)] +
        SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 0, w 0), (v 0, w 1), (v 1, w 1)] := by
  rw [PeriodTorusHigherHomology.formalEdgeCrossProduct_simplex_succ,
    PeriodTorusHigherHomology.formalPointCrossProduct_edge_boundary,
    formalBoundary_triangle_simplex]
  simp only [map_add, map_sub, formalEdgeCrossProduct_one_expansion_mo1973_7080,
    SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalCone_simplex]
  have hv₀ : (fun i : Fin 3 => (v 0, w i)) = ![(v 0, w 0), (v 0, w 1), (v 0, w 2)] := by
    funext i
    fin_cases i <;> rfl
  have hv₁ : (fun i : Fin 3 => (v 1, w i)) = ![(v 1, w 0), (v 1, w 1), (v 1, w 2)] := by
    funext i
    fin_cases i <;> rfl
  simp only [Function.comp_def, hv₀, hv₁, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.Fin.cons_vecCons]
  abel

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def ThirdHurewicz.CubeSubdivision.prismSimplex (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin 4 → Fin 2 × Fin 3) : C(FirstHurewicz.Simplex 3, ThirdHurewicz.Geometry.Cube3) :=
  ThirdHurewicz.Geometry.cubeAffineSimplex
    (fun j => ThirdHurewicz.Geometry.cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2])

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def ThirdHurewicz.CubeSubdivision.prismSimplexChain (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin 4 → Fin 2 × Fin 3) : FirstHurewicz.Chains ThirdHurewicz.Geometry.Cube3 3 :=
  FirstHurewicz.simplexChain ThirdHurewicz.Geometry.Cube3 3 (prismSimplex v w)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def ThirdHurewicz.CubeSubdivision.prismRealization (v : Fin 3 → Fin 2 × Fin 2) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin 3) 4 →ₗ[ℤ]
      FirstHurewicz.Chains ThirdHurewicz.Geometry.Cube3 3 :=
  (FirstHurewicz.inducedChain (ThirdHurewicz.Geometry.cubeTrianglePrism v) 3).comp
    ((PeriodTorusHigherHomology.productAffineChainMap 1 2 3).comp
      (SingularMayerVietoris.formalMap
        (fun z : Fin 2 × Fin 3 =>
          (SingularMayerVietoris.stdVertices 1 z.1, SingularMayerVietoris.stdVertices 2 z.2))
        4))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem ThirdHurewicz.CubeSubdivision.prismRealization_simplex (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin 4 → Fin 2 × Fin 3) :
    prismRealization v (SingularMayerVietoris.formalSimplex w) = prismSimplexChain v w := by
  simp only [prismRealization, LinearMap.comp_apply, SingularMayerVietoris.formalMap_simplex,
    PeriodTorusHigherHomology.productAffineChainMap_simplex, FirstHurewicz.inducedChain_simplex]
  change
    FirstHurewicz.simplexChain ThirdHurewicz.Geometry.Cube3 3
        ((ThirdHurewicz.Geometry.cubeTrianglePrism v).comp
          (PeriodTorusHigherHomology.productAffineSimplex
            (fun j =>
              (SingularMayerVietoris.stdVertices 1 (w j).1,
                SingularMayerVietoris.stdVertices 2 (w j).2)))) =
      _
  rw [ThirdHurewicz.Geometry.cubeTrianglePrism_affine]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def ThirdHurewicz.CubeSubdivision.intervalTriangleChain (v : Fin 3 → Fin 2 × Fin 2) :
    FirstHurewicz.Chains ThirdHurewicz.Geometry.Cube3 3 :=
  FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 3
    (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 2 → (unitInterval)) 2
      SecondHurewicz.intervalChain
      (FirstHurewicz.inducedChain SecondHurewicz.squareCoordinates 2
        (FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2
          (SecondHurewicz.SimplyConnected.squareAffineTriangle v))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.CubeSubdivision.intervalTriangleChain_eq_prismRealization
    (v : Fin 3 → Fin 2 × Fin 2) :
    intervalTriangleChain v =
      prismRealization v
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 2
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 3 => j))) := by
  have h :=
    PeriodTorusHigherHomology.formalMap_edgeCrossProduct (SingularMayerVietoris.stdVertices 1)
      (SingularMayerVietoris.stdVertices 2) 2
      (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
      (SingularMayerVietoris.formalSimplex (fun j : Fin 3 => j))
  simp only [SingularMayerVietoris.formalMap_simplex, Function.comp_def] at h
  rw [intervalTriangleChain, FirstHurewicz.inducedChain_simplex, SecondHurewicz.intervalChain,
    FirstHurewicz.pathChain, PeriodTorusHigherHomology.crossProductEdge_simplex]
  change
    ((FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 3).comp
          (FirstHurewicz.inducedChain
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (SecondHurewicz.squareCoordinates.comp
                (SecondHurewicz.SimplyConnected.squareAffineTriangle v)))
            3))
        (PeriodTorusHigherHomology.productAffineChainMap 1 2 3
          (PeriodTorusHigherHomology.formalEdgeCrossProduct 2
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2)))) =
      _
  rw [← FirstHurewicz.inducedChain_comp, ← h]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.CubeSubdivision.intervalTriangleChain_twelve_tetrahedra
    (v : Fin 3 → Fin 2 × Fin 2) :
    intervalTriangleChain v =
      prismSimplexChain v ![(0, 0), (1, 0), (1, 1), (1, 2)] -
                            prismSimplexChain v ![(0, 0), (0, 1), (1, 1), (1, 2)] +
                          prismSimplexChain v ![(0, 0), (0, 1), (0, 2), (1, 2)] -
                        prismSimplexChain v ![(0, 0), (0, 0), (0, 1), (0, 2)] +
                      prismSimplexChain v ![(0, 0), (0, 1), (0, 1), (0, 2)] -
                    prismSimplexChain v ![(0, 0), (0, 1), (0, 1), (1, 1)] +
                  prismSimplexChain v ![(0, 0), (0, 0), (1, 0), (1, 2)] -
                prismSimplexChain v ![(0, 0), (0, 0), (0, 0), (0, 2)] -
              prismSimplexChain v ![(0, 0), (0, 0), (0, 2), (1, 2)] -
            prismSimplexChain v ![(0, 0), (0, 0), (1, 0), (1, 1)] +
          prismSimplexChain v ![(0, 0), (0, 0), (0, 0), (0, 1)] +
        prismSimplexChain v ![(0, 0), (0, 0), (0, 1), (1, 1)] := by
  rw [intervalTriangleChain_eq_prismRealization]
  have h :=
    congrArg (prismRealization v)
      (formalEdgeCrossProduct_two_expansion (fun i : Fin 2 => i) (fun j : Fin 3 => j))
  simpa only [map_sub, map_add, prismRealization_simplex] using h

private def ThirdHurewicz.Geometry.cubePermutation : Fin 6 → Equiv.Perm (Fin 3) :=
  ![1, Equiv.swap 1 2, Equiv.swap 0 1, (Equiv.swap 0 1).trans (Equiv.swap 1 2),
    (Equiv.swap 1 2).trans (Equiv.swap 0 1), Equiv.swap 0 2]

private theorem
    ThirdHurewicz.Geometry.cubePermutation_injective : Function.Injective cubePermutation := by
  decide

private theorem
    ThirdHurewicz.Geometry.cubePermutation_bijective : Function.Bijective cubePermutation := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨cubePermutation_injective, by norm_num [Fintype.card_perm, Nat.factorial]⟩

private theorem ThirdHurewicz.Geometry.sum_cubePermutations {A : Type*} [AddCommMonoid A]
    (f : Equiv.Perm (Fin 3) → A) :
    ∑ e, f e =
      f 1 + f (Equiv.swap 1 2) + f (Equiv.swap 0 1) +
            f ((Equiv.swap 0 1).trans (Equiv.swap 1 2)) +
          f ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) +
        f (Equiv.swap 0 2) := by
  rw [← cubePermutation_bijective.sum_comp f]
  simp [cubePermutation, Fin.sum_univ_succ, add_assoc]

private theorem ThirdHurewicz.Geometry.cubeOrientation_cubePermutation (i : Fin 6) :
    cubeOrientation (cubePermutation i) = ![1, -1, -1, 1, 1, -1] i := by
  fin_cases i <;>
    simp [cubePermutation, cubeOrientation, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap']

private theorem ThirdHurewicz.Geometry.sum_oriented_cubePermutations {A : Type*} [AddCommGroup A]
    (f : Equiv.Perm (Fin 3) → A) :
    ∑ e, cubeOrientation e • f e =
      f 1 - f (Equiv.swap 1 2) - f (Equiv.swap 0 1) +
            f ((Equiv.swap 0 1).trans (Equiv.swap 1 2)) +
          f ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) -
        f (Equiv.swap 0 2) := by
  rw [sum_cubePermutations]
  simp [cubeOrientation, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap', sub_eq_add_neg, add_assoc]

private theorem ThirdHurewicz.CubeSubdivision.prismSimplex_lower_zero :
    prismSimplex ![(0, 0), (1, 0), (1, 1)] ![(0, 0), (1, 0), (1, 1), (1, 2)] =
      ThirdHurewicz.Geometry.cubeTetrahedron 1 := by
  change
    ThirdHurewicz.Geometry.cubeAffineSimplex _ =
      ThirdHurewicz.Geometry.cubeAffineSimplex
        (ThirdHurewicz.Geometry.cubeVertex (Equiv.refl (Fin 3)))
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [ThirdHurewicz.Geometry.cubeBitVertex, ThirdHurewicz.Geometry.cubeVertex,
      SingularMayerVietoris.stdVertices]

private theorem ThirdHurewicz.CubeSubdivision.prismSimplex_lower_one :
    prismSimplex ![(0, 0), (1, 0), (1, 1)] ![(0, 0), (0, 1), (1, 1), (1, 2)] =
      ThirdHurewicz.Geometry.cubeTetrahedron (Equiv.swap 0 1) := by
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [ThirdHurewicz.Geometry.cubeBitVertex, ThirdHurewicz.Geometry.cubeVertex,
      SingularMayerVietoris.stdVertices, Equiv.swap_apply_def]

private theorem ThirdHurewicz.CubeSubdivision.prismSimplex_lower_two :
    prismSimplex ![(0, 0), (1, 0), (1, 1)] ![(0, 0), (0, 1), (0, 2), (1, 2)] =
      ThirdHurewicz.Geometry.cubeTetrahedron ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) := by
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [ThirdHurewicz.Geometry.cubeBitVertex, ThirdHurewicz.Geometry.cubeVertex,
      SingularMayerVietoris.stdVertices, Equiv.swap_apply_def]

private theorem ThirdHurewicz.CubeSubdivision.prismSimplex_upper_zero :
    prismSimplex ![(0, 0), (0, 1), (1, 1)] ![(0, 0), (1, 0), (1, 1), (1, 2)] =
      ThirdHurewicz.Geometry.cubeTetrahedron (Equiv.swap 1 2) := by
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [ThirdHurewicz.Geometry.cubeBitVertex, ThirdHurewicz.Geometry.cubeVertex,
      SingularMayerVietoris.stdVertices, Equiv.swap_apply_def]

private theorem ThirdHurewicz.CubeSubdivision.prismSimplex_upper_one :
    prismSimplex ![(0, 0), (0, 1), (1, 1)] ![(0, 0), (0, 1), (1, 1), (1, 2)] =
      ThirdHurewicz.Geometry.cubeTetrahedron ((Equiv.swap 0 1).trans (Equiv.swap 1 2)) := by
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [ThirdHurewicz.Geometry.cubeBitVertex, ThirdHurewicz.Geometry.cubeVertex,
      SingularMayerVietoris.stdVertices, Equiv.swap_apply_def]

private theorem ThirdHurewicz.CubeSubdivision.prismSimplex_upper_two :
    prismSimplex ![(0, 0), (0, 1), (1, 1)] ![(0, 0), (0, 1), (0, 2), (1, 2)] =
      ThirdHurewicz.Geometry.cubeTetrahedron (Equiv.swap 0 2) := by
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [ThirdHurewicz.Geometry.cubeBitVertex, ThirdHurewicz.Geometry.cubeVertex,
      SingularMayerVietoris.stdVertices, Equiv.swap_apply_def]

private theorem ThirdHurewicz.CubeSubdivision.loop_prismSimplex_of_coordinate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin 4 → Fin 2 × Fin 3) (i : Fin 3)
    (h :
      (∀ j, ThirdHurewicz.Geometry.cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2] i = 0) ∨
        (∀ j,
          ThirdHurewicz.Geometry.cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2] i = 1)) :
    p.val.comp (prismSimplex v w) = ContinuousMap.const (FirstHurewicz.Simplex 3) x :=
  ThirdHurewicz.Geometry.loop_comp_cubeAffineSimplex_of_coordinate p _ i h

private theorem ThirdHurewicz.CubeSubdivision.induced_prismSimplexChain_of_coordinate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin 4 → Fin 2 × Fin 3) (i : Fin 3)
    (h :
      (∀ j, ThirdHurewicz.Geometry.cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2] i = 0) ∨
        (∀ j,
          ThirdHurewicz.Geometry.cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2] i = 1)) :
    FirstHurewicz.inducedChain p.val 3 (prismSimplexChain v w) =
      FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x) := by
  rw [prismSimplexChain, FirstHurewicz.inducedChain_simplex,
    loop_prismSimplex_of_coordinate p v w i h]

private theorem
    ThirdHurewicz.CubeSubdivision.loop_prismSimplex_of_fst {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2) (w : Fin 4 → Fin 2 × Fin 3)
    (h : (∀ j, (v j).1 = 0) ∨ (∀ j, (v j).1 = 1)) :
    p.val.comp (prismSimplex v w) = ContinuousMap.const (FirstHurewicz.Simplex 3) x := by
  apply loop_prismSimplex_of_coordinate p v w 1
  rcases h with h | h
  · exact Or.inl fun j => ThirdHurewicz.Geometry.cubeBitVertex_zero _ (i := 1) (h (w j).2)
  · exact Or.inr fun j => ThirdHurewicz.Geometry.cubeBitVertex_one _ (i := 1) (h (w j).2)

private theorem
    ThirdHurewicz.CubeSubdivision.loop_prismSimplex_of_snd {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2) (w : Fin 4 → Fin 2 × Fin 3)
    (h : (∀ j, (v j).2 = 0) ∨ (∀ j, (v j).2 = 1)) :
    p.val.comp (prismSimplex v w) = ContinuousMap.const (FirstHurewicz.Simplex 3) x := by
  apply loop_prismSimplex_of_coordinate p v w 2
  rcases h with h | h
  · exact Or.inl fun j => ThirdHurewicz.Geometry.cubeBitVertex_zero _ (i := 2) (h (w j).2)
  · exact Or.inr fun j => ThirdHurewicz.Geometry.cubeBitVertex_one _ (i := 2) (h (w j).2)

private theorem
  ThirdHurewicz.CubeSubdivision.induced_intervalTriangleChain_of_constant_mo1973_7106 {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2)
    (h : ∀ w, p.val.comp (prismSimplex v w) = ContinuousMap.const (FirstHurewicz.Simplex 3) x) :
    FirstHurewicz.inducedChain p.val 3 (intervalTriangleChain v) = 0 := by
  rw [intervalTriangleChain_twelve_tetrahedra]
  simp only [map_add, map_sub, prismSimplexChain, FirstHurewicz.inducedChain_simplex, h]
  abel

private theorem ThirdHurewicz.CubeSubdivision.induced_intervalTriangleChain_of_fst {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2)
    (h : (∀ j, (v j).1 = 0) ∨ (∀ j, (v j).1 = 1)) :
    FirstHurewicz.inducedChain p.val 3 (intervalTriangleChain v) = 0 :=
  induced_intervalTriangleChain_of_constant_mo1973_7106 p v fun w =>
    loop_prismSimplex_of_fst p v w h

private theorem ThirdHurewicz.CubeSubdivision.induced_intervalTriangleChain_of_snd {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2)
    (h : (∀ j, (v j).2 = 0) ∨ (∀ j, (v j).2 = 1)) :
    FirstHurewicz.inducedChain p.val 3 (intervalTriangleChain v) = 0 :=
  induced_intervalTriangleChain_of_constant_mo1973_7106 p v fun w =>
    loop_prismSimplex_of_snd p v w h

private theorem ThirdHurewicz.CubeSubdivision.prismSimplex_endpoints_eq (b c : Fin 2 × Fin 2)
    (w : Fin 4 → Fin 2 × Fin 3) (h : ∀ j, (w j).2 = 0 ∨ (w j).2 = 2) :
    prismSimplex ![(0, 0), b, (1, 1)] w = prismSimplex ![(0, 0), c, (1, 1)] w := by
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j
  rcases h j with hj | hj <;> simp [hj]

private def
    ThirdHurewicz.CubeSubdivision.diagonalPrismPrincipal {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (b : Fin 2 × Fin 2) : FirstHurewicz.Chains X 3 :=
  FirstHurewicz.inducedChain p.val 3
        (prismSimplexChain ![(0, 0), b, (1, 1)] ![(0, 0), (1, 0), (1, 1), (1, 2)]) -
      FirstHurewicz.inducedChain p.val 3
        (prismSimplexChain ![(0, 0), b, (1, 1)] ![(0, 0), (0, 1), (1, 1), (1, 2)]) +
    FirstHurewicz.inducedChain p.val 3
      (prismSimplexChain ![(0, 0), b, (1, 1)] ![(0, 0), (0, 1), (0, 2), (1, 2)])

private def
    ThirdHurewicz.CubeSubdivision.prismCommonCorrection {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : FirstHurewicz.Chains X 3 :=
  FirstHurewicz.inducedChain p.val 3
        (prismSimplexChain ![(0, 0), (0, 0), (1, 1)] ![(0, 0), (0, 0), (1, 0), (1, 2)]) -
      FirstHurewicz.inducedChain p.val 3
        (prismSimplexChain ![(0, 0), (0, 0), (1, 1)] ![(0, 0), (0, 0), (0, 2), (1, 2)]) -
    FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x)

private theorem
    ThirdHurewicz.CubeSubdivision.induced_diagonalPrism_eq_principal_add_correction {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (b : Fin 2 × Fin 2)
    (hb : b.1 = 0 ∨ b.2 = 0) :
    FirstHurewicz.inducedChain p.val 3 (intervalTriangleChain ![(0, 0), b, (1, 1)]) =
      diagonalPrismPrincipal p b + prismCommonCorrection p := by
  have htime (w : Fin 4 → Fin 2 × Fin 3) (hw : ∀ j, (w j).1 = 0) :
    FirstHurewicz.inducedChain p.val 3 (prismSimplexChain ![(0, 0), b, (1, 1)] w) =
      FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x) := by
    apply induced_prismSimplexChain_of_coordinate p _ w 0
    left
    intro j
    simp [ThirdHurewicz.Geometry.cubeBitVertex, SingularMayerVietoris.stdVertices, hw j]
  have hside (w : Fin 4 → Fin 2 × Fin 3) (hw : ∀ j, (w j).2 = 0 ∨ (w j).2 = 1) :
    FirstHurewicz.inducedChain p.val 3 (prismSimplexChain ![(0, 0), b, (1, 1)] w) =
      FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x) := by
    rcases hb with hb | hb
    · apply induced_prismSimplexChain_of_coordinate p _ w 1
      left
      intro j
      rcases hw j with hj | hj <;>
        simp [ThirdHurewicz.Geometry.cubeBitVertex, SingularMayerVietoris.stdVertices, hj, hb]
    · apply induced_prismSimplexChain_of_coordinate p _ w 2
      left
      intro j
      rcases hw j with hj | hj <;>
        simp [ThirdHurewicz.Geometry.cubeBitVertex, SingularMayerVietoris.stdVertices, hj, hb]
  have hdiag (w : Fin 4 → Fin 2 × Fin 3) (hw : ∀ j, (w j).2 = 0 ∨ (w j).2 = 2) :
    FirstHurewicz.inducedChain p.val 3 (prismSimplexChain ![(0, 0), b, (1, 1)] w) =
      FirstHurewicz.inducedChain p.val 3 (prismSimplexChain ![(0, 0), (0, 0), (1, 1)] w) := by
    simp only [prismSimplexChain, prismSimplex_endpoints_eq b (0, 0) w hw]
  rw [intervalTriangleChain_twelve_tetrahedra]
  simp only [map_add, map_sub]
  rw [htime ![(0, 0), (0, 0), (0, 1), (0, 2)] (by intro j; fin_cases j <;> rfl),
    htime ![(0, 0), (0, 1), (0, 1), (0, 2)] (by intro j; fin_cases j <;> rfl),
    hside ![(0, 0), (0, 1), (0, 1), (1, 1)] (by intro j; fin_cases j <;> simp),
    hdiag ![(0, 0), (0, 0), (1, 0), (1, 2)] (by intro j; fin_cases j <;> simp),
    htime ![(0, 0), (0, 0), (0, 0), (0, 2)] (by intro j; fin_cases j <;> rfl),
    hdiag ![(0, 0), (0, 0), (0, 2), (1, 2)] (by intro j; fin_cases j <;> simp),
    hside ![(0, 0), (0, 0), (1, 0), (1, 1)] (by intro j; fin_cases j <;> simp),
    htime ![(0, 0), (0, 0), (0, 0), (0, 1)] (by intro j; fin_cases j <;> rfl),
    hside ![(0, 0), (0, 0), (0, 1), (1, 1)] (by intro j; fin_cases j <;> simp)]
  unfold diagonalPrismPrincipal prismCommonCorrection
  abel

private theorem
    ThirdHurewicz.CubeSubdivision.induced_diagonalPrism_sub {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) :
    FirstHurewicz.inducedChain p.val 3 (intervalTriangleChain ![(0, 0), (1, 0), (1, 1)]) -
        FirstHurewicz.inducedChain p.val 3 (intervalTriangleChain ![(0, 0), (0, 1), (1, 1)]) =
      diagonalPrismPrincipal p (1, 0) - diagonalPrismPrincipal p (0, 1) := by
  rw [induced_diagonalPrism_eq_principal_add_correction p (1, 0) (Or.inr rfl),
    induced_diagonalPrism_eq_principal_add_correction p (0, 1) (Or.inl rfl)]
  abel

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.CubeSubdivision.fundamentalCubeChain_four_prisms :
    ThirdHurewicz.fundamentalCubeChain =
      intervalTriangleChain ![(0, 0), (1, 0), (1, 1)] -
            intervalTriangleChain ![(0, 0), (0, 0), (0, 1)] -
          intervalTriangleChain ![(0, 0), (0, 1), (1, 1)] +
        intervalTriangleChain ![(0, 0), (0, 0), (1, 0)] := by
  rw [ThirdHurewicz.fundamentalCubeChain, ThirdHurewicz.productCubeChain,
    SecondHurewicz.fundamentalSquareChain,
    SecondHurewicz.SimplyConnected.productSquareChain_four_triangles]
  simp only [map_add, map_sub]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem ThirdHurewicz.CubeSubdivision.induced_fundamentalCubeChain_eq_principal {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) :
    FirstHurewicz.inducedChain p.val 3 ThirdHurewicz.fundamentalCubeChain =
      diagonalPrismPrincipal p (1, 0) - diagonalPrismPrincipal p (0, 1) := by
  rw [fundamentalCubeChain_four_prisms]
  simp only [map_add, map_sub]
  rw [induced_intervalTriangleChain_of_fst p ![(0, 0), (0, 0), (0, 1)]
      (Or.inl (by intro j; fin_cases j <;> rfl)),
    induced_intervalTriangleChain_of_snd p ![(0, 0), (0, 0), (1, 0)]
      (Or.inl (by intro j; fin_cases j <;> rfl)),
    sub_zero, add_zero]
  exact induced_diagonalPrism_sub p

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    ThirdHurewicz.CubeSubdivision.cubeChain_six_tetrahedra {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) :
    ThirdHurewicz.cubeChain p =
      FirstHurewicz.simplexChain X 3 (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron 1)) -
                FirstHurewicz.simplexChain X 3
                  (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron (Equiv.swap 0 1))) +
              FirstHurewicz.simplexChain X 3
                (p.val.comp
                  (ThirdHurewicz.Geometry.cubeTetrahedron
                    ((Equiv.swap 1 2).trans (Equiv.swap 0 1)))) -
            FirstHurewicz.simplexChain X 3
              (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron (Equiv.swap 1 2))) +
          FirstHurewicz.simplexChain X 3
            (p.val.comp
              (ThirdHurewicz.Geometry.cubeTetrahedron
                ((Equiv.swap 0 1).trans (Equiv.swap 1 2)))) -
        FirstHurewicz.simplexChain X 3
          (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron (Equiv.swap 0 2))) := by
  rw [ThirdHurewicz.cubeChain_eq_induced, induced_fundamentalCubeChain_eq_principal]
  simp only [diagonalPrismPrincipal, prismSimplexChain, FirstHurewicz.inducedChain_simplex,
    prismSimplex_lower_zero, prismSimplex_lower_one, prismSimplex_lower_two,
    prismSimplex_upper_zero, prismSimplex_upper_one, prismSimplex_upper_two]
  abel

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    ThirdHurewicz.CubeSubdivision.cubeChain_eq_sum_tetrahedra {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) :
    ThirdHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 3),
        ThirdHurewicz.Geometry.cubeOrientation e •
          FirstHurewicz.simplexChain X 3
            (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) := by
  rw [cubeChain_six_tetrahedra, ThirdHurewicz.Geometry.sum_oriented_cubePermutations]
  abel

private def ThirdHurewicz.hurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    π_ 3 X x → SingularMayerVietoris.SingularHomology X 3 :=
  Quotient.lift cubeHomologyClass (fun _ _ h => cubeHomologyClass_homotopic h)

private def ThirdHurewicz.hurewiczPi3 {X : Type} [TopologicalSpace X] (x : X) :
    π_ 3 X x →* Multiplicative (SingularMayerVietoris.SingularHomology X 3)
    where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (cubeHomologyClass_const (x := x))
  map_mul' a
    b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine
      (congrArg (fun c : π_ 3 X x => Multiplicative.ofAdd (hurewiczFunction x c))
            (HomotopyGroup.mul_spec (i := (0 : Fin 3)) (p := p) (q := q))).trans
        ?_
    change
      Multiplicative.ofAdd (cubeHomologyClass (GenLoop.transAt (0 : Fin 3) q p)) =
        Multiplicative.ofAdd (cubeHomologyClass p + cubeHomologyClass q)
    rw [cubeHomologyClass_transAt, add_comm]

private def ThirdHurewicz.hurewiczMap {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ 3 X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 3
    where
  toFun := (hurewiczPi3 x).toAdditiveLeft
  map_add' := (hurewiczPi3 x).toAdditiveLeft.map_add
  map_smul' n a := by simpa using map_intCast_smul (hurewiczPi3 x).toAdditiveLeft ℤ ℤ n a

private theorem ThirdHurewicz.hurewiczMap_representative {X : Type} [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin 3) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 3 X x)) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (cubeCycle p) :=
  rfl

private theorem
    ThirdHurewicz.cubeChain_basedThreeSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : cubeChain (basedThreeSimplexLoop τ) = basedThreeSimplexChain τ := by
  rw [CubeSubdivision.cubeChain_eq_sum_tetrahedra, basedThreeSimplex_tetrahedronChain_sum]

private theorem
    ThirdHurewicz.cubeCycle_basedThreeSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : cubeCycle (basedThreeSimplexLoop τ) = basedThreeSimplexCycle τ := by
  apply Subtype.ext
  exact cubeChain_basedThreeSimplexLoop τ

private theorem
    ThirdHurewicz.hurewicz_basedThreeSimplexClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    hurewiczMap x (basedThreeSimplexClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (basedThreeSimplexCycle τ) := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (cubeCycle (basedThreeSimplexLoop τ)) =
      _
  rw [cubeCycle_basedThreeSimplexLoop]

private theorem
    ThirdHurewicz.hurewiczMap_comp_threeSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    (hurewiczMap x).comp (threeSimplexClassOperator x) =
      (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3).comp
        (normalizedThreeSimplexCycleOperator x) := by
  apply FirstHurewicz.chainMap_ext X 3
  intro smp
  simp only [LinearMap.comp_apply, threeSimplexClassOperator_simplex,
    normalizedThreeSimplexCycleOperator_simplex]
  exact hurewicz_basedThreeSimplexClass (normalizedThreeSimplex x smp)

private theorem
    ThirdHurewicz.hurewiczMap_threeSimplexClassOperator_cycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    hurewiczMap x (threeSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_threeSimplexClassOperator x) c.val
  change
    hurewiczMap x (threeSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (normalizedThreeSimplexCycleOperator x c.val) at h
  exact h.trans (normalizedThreeSimplexCycleOperator_class x c)

private def ThirdHurewicz.fourSimplexTwoSkeleton : Set (FirstHurewicz.Simplex 4) :=
  {s | ∃ i j : Fin 5, i ≠ j ∧ s i = 0 ∧ s j = 0}

private def ThirdHurewicz.BasedFourSimplex {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(FirstHurewicz.Simplex 4, X) // ∀ s ∈ fourSimplexTwoSkeleton, τ s = x }

private theorem
    ThirdHurewicz.simplexFace_threeSimplexBoundary (i : Fin 5) (s : FirstHurewicz.Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : FirstHurewicz.simplexFace 3 i s ∈ fourSimplexTwoSkeleton := by
  obtain ⟨j, hj⟩ := hs
  exact
    ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, FirstHurewicz.simplexFace_apply_self 3 i s,
      (FirstHurewicz.simplexFace_apply_succAbove 3 i s j).trans hj⟩

private def ThirdHurewicz.basedFourSimplexFace {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) (i : Fin 5) : BasedThreeSimplex x :=
  ⟨τ.val.comp (FirstHurewicz.simplexFace 3 i), fun s hs =>
    τ.property _ (simplexFace_threeSimplexBoundary i s hs)⟩

private def ThirdHurewicz.BasedFourSimplex.ofFaces {X : Type} [TopologicalSpace X] {x : X}
    (τ : C(FirstHurewicz.Simplex 4, X))
    (h :
      ∀ i : Fin 5,
        ∀ s ∈ ThirdHurewicz.threeSimplexBoundary,
          (τ.comp (FirstHurewicz.simplexFace 3 i)) s = x) :
    ThirdHurewicz.BasedFourSimplex x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := SecondHurewicz.SimplyConnected.simplexFaceInverse 3 i ⟨s, hi⟩
    have ht : t ∈ ThirdHurewicz.threeSimplexBoundary := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (FirstHurewicz.simplexFace 3 i t) = x at he
    rw [show FirstHurewicz.simplexFace 3 i t = s from
        SecondHurewicz.SimplyConnected.simplexFace_inverse 3 i ⟨s, hi⟩] at he
    exact he⟩

private def
    ThirdHurewicz.normalizedFourSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 4) :
    BasedFourSimplex x :=
  BasedFourSimplex.ofFaces (normalizedFourSimplexMap x smp)
    (normalizedFourSimplexMap_face_boundary x smp)

@[simp]
private theorem ThirdHurewicz.normalizedFourSimplex_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) (i : Fin 5) :
    basedFourSimplexFace (normalizedFourSimplex x smp) i =
      normalizedThreeSimplex x (smp.comp (FirstHurewicz.simplexFace 3 i)) := by
  apply Subtype.ext
  exact normalizedFourSimplexMap_face x smp i

private theorem ThirdHurewicz.fourSimplex_three_order_cases (a b c : ℝ) :
    (a ≤ b ∧ b ≤ c) ∨
      (a ≤ c ∧ c ≤ b) ∨ (b ≤ a ∧ a ≤ c) ∨ (b ≤ c ∧ c ≤ a) ∨ (c ≤ a ∧ a ≤ b) ∨ (c ≤ b ∧ b ≤ a) := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact Or.inl ⟨hab, hbc⟩
    · rcases le_total a c with hac | hca
      · exact Or.inr (Or.inl ⟨hac, hcb⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hca, hab⟩))))
  · rcases le_total a c with hac | hca
    · exact Or.inr (Or.inr (Or.inl ⟨hba, hac⟩))
    · rcases le_total b c with hbc | hcb
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hbc, hca⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hcb, hba⟩))))

private theorem ThirdHurewicz.fourSimplex_coordinates_sum_A (a b c : ℝ) :
    (1 - Max.max a b) + (a - Min.min a (Max.max b c)) + (b - Min.min b c) +
          (Min.min b c - Min.min a (Min.min b c)) +
        Min.min a c =
      1 := by
  rcases fourSimplex_three_order_cases a b c with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ |
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  all_goals
    have h₃ := h₁.trans h₂
    simp_all only [min_eq_left, min_eq_right, max_eq_left, max_eq_right]
    ring

private theorem ThirdHurewicz.fourSimplex_coordinates_sum_B (a b c : ℝ) :
    (a - Min.min a b) + (1 - Max.max a (Max.max b c)) + (b - Min.min b c) +
          Min.min a (Min.min b c) +
        (c - Min.min a c) =
      1 := by
  rcases fourSimplex_three_order_cases a b c with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ |
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  all_goals
    have h₃ := h₁.trans h₂
    simp_all only [min_eq_left, min_eq_right, max_eq_left, max_eq_right]
    ring

private def ThirdHurewicz.fourSimplexFillA : C(Fin 3 → (unitInterval), FirstHurewicz.Simplex 4)
    where
  toFun
    u :=
    ⟨![1 - Max.max (u 0 : ℝ) (u 1 : ℝ),
        (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)),
        (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ),
        Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)),
        Min.min (u 0 : ℝ) (u 2 : ℝ)],
      by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (max_le (u 0).property.2 (u 1).property.2)
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact sub_nonneg.mpr (min_le_right _ _)
        · exact le_min (u 0).property.1 (u 2).property.1
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        simpa only [add_assoc] using fourSimplex_coordinates_sum_A (u 0) (u 1) (u 2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

private def ThirdHurewicz.fourSimplexFillB : C(Fin 3 → (unitInterval), FirstHurewicz.Simplex 4)
    where
  toFun
    u :=
    ⟨![(u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ),
        1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)),
        (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ), Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)),
        (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ)],
      by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact
            sub_nonneg.mpr (max_le (u 0).property.2 (max_le (u 1).property.2 (u 2).property.2))
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact le_min (u 0).property.1 (le_min (u 1).property.1 (u 2).property.1)
        · exact sub_nonneg.mpr (min_le_right _ _)
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        simpa only [add_assoc] using fourSimplex_coordinates_sum_B (u 0) (u 1) (u 2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

private def
    ThirdHurewicz.fourSimplexReflectFirst : C(Fin 3 → (unitInterval), Fin 3 → (unitInterval))
    where
  toFun u := ![(unitInterval.symm) (u 0), u 1, u 2]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
private theorem ThirdHurewicz.fourSimplexReflectFirst_involutive (u : Fin 3 → (unitInterval)) :
    fourSimplexReflectFirst (fourSimplexReflectFirst u) = u := by
  funext i
  fin_cases i <;> simp [fourSimplexReflectFirst]

private theorem ThirdHurewicz.fourSimplexReflectFirst_boundary (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) : fourSimplexReflectFirst u ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact ⟨0, Or.inr (by simp [fourSimplexReflectFirst, hi])⟩
    · exact ⟨1, Or.inl (by simpa [fourSimplexReflectFirst] using hi)⟩
    · exact ⟨2, Or.inl (by simpa [fourSimplexReflectFirst] using hi)⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact ⟨0, Or.inl (by simp [fourSimplexReflectFirst, hi])⟩
    · exact ⟨1, Or.inr (by simpa [fourSimplexReflectFirst] using hi)⟩
    · exact ⟨2, Or.inr (by simpa [fourSimplexReflectFirst] using hi)⟩

private theorem
    ThirdHurewicz.fourSimplexFill_first_zero (u : Fin 3 → (unitInterval)) (hu : u 0 = 0) :
    fourSimplexFillA u 1 = 0 ∧
      fourSimplexFillA u 4 = 0 ∧
        fourSimplexFillB (fourSimplexReflectFirst u) 1 = 0 ∧
          fourSimplexFillB (fourSimplexReflectFirst u) 4 = 0 := by
  simp [fourSimplexFillA, fourSimplexFillB, fourSimplexReflectFirst, DFunLike.coe, hu,
    min_eq_left ((u 1).property.1.trans (le_max_left _ (u 2 : ℝ))), min_eq_left (u 2).property.1,
    max_eq_left (max_le (u 1).property.2 (u 2).property.2), min_eq_right (u 2).property.2]

private theorem
    ThirdHurewicz.fourSimplexFill_first_one (u : Fin 3 → (unitInterval)) (hu : u 0 = 1) :
    fourSimplexFillA u 0 = 0 ∧
      fourSimplexFillA u 3 = 0 ∧
        fourSimplexFillB (fourSimplexReflectFirst u) 0 = 0 ∧
          fourSimplexFillB (fourSimplexReflectFirst u) 3 = 0 := by
  simp [fourSimplexFillA, fourSimplexFillB, fourSimplexReflectFirst, DFunLike.coe, hu,
    max_eq_left (u 1).property.2,
    min_eq_right ((min_le_left (u 1 : ℝ) (u 2 : ℝ)).trans (u 1).property.2),
    min_eq_left (u 1).property.1, min_eq_left (le_min (u 1).property.1 (u 2).property.1)]

private theorem
    ThirdHurewicz.fourSimplexFill_second_zero (u : Fin 3 → (unitInterval)) (hu : u 1 = 0) :
    fourSimplexFillA u 2 = 0 ∧
      fourSimplexFillA u 3 = 0 ∧
        fourSimplexFillB (fourSimplexReflectFirst u) 2 = 0 ∧
          fourSimplexFillB (fourSimplexReflectFirst u) 3 = 0 := by
  simp [fourSimplexFillA, fourSimplexFillB, fourSimplexReflectFirst, DFunLike.coe, hu,
    min_eq_left (u 2).property.1, min_eq_right (u 0).property.1, (u 0).property.2]

private theorem
    ThirdHurewicz.fourSimplexFill_second_one (u : Fin 3 → (unitInterval)) (hu : u 1 = 1) :
    fourSimplexFillA u 0 = 0 ∧
      fourSimplexFillA u 1 = 0 ∧
        fourSimplexFillB (fourSimplexReflectFirst u) 0 = 0 ∧
          fourSimplexFillB (fourSimplexReflectFirst u) 1 = 0 := by
  simp [fourSimplexFillA, fourSimplexFillB, fourSimplexReflectFirst, DFunLike.coe, hu,
    max_eq_right (u 0).property.2, max_eq_left (u 2).property.2, min_eq_left (u 0).property.2,
    min_eq_left (sub_le_self 1 (u 0).property.1), max_eq_right (sub_le_self 1 (u 0).property.1)]

private theorem
    ThirdHurewicz.fourSimplexFill_third_zero (u : Fin 3 → (unitInterval)) (hu : u 2 = 0) :
    fourSimplexFillA u 3 = 0 ∧
      fourSimplexFillA u 4 = 0 ∧
        fourSimplexFillB (fourSimplexReflectFirst u) 3 = 0 ∧
          fourSimplexFillB (fourSimplexReflectFirst u) 4 = 0 := by
  simp [fourSimplexFillA, fourSimplexFillB, fourSimplexReflectFirst, DFunLike.coe, hu,
    min_eq_right (u 1).property.1, min_eq_right (u 0).property.1, (u 0).property.2]

private theorem
    ThirdHurewicz.fourSimplexFill_third_one (u : Fin 3 → (unitInterval)) (hu : u 2 = 1) :
    fourSimplexFillA u 1 = 0 ∧
      fourSimplexFillA u 2 = 0 ∧
        fourSimplexFillB (fourSimplexReflectFirst u) 1 = 0 ∧
          fourSimplexFillB (fourSimplexReflectFirst u) 2 = 0 := by
  simp [fourSimplexFillA, fourSimplexFillB, fourSimplexReflectFirst, DFunLike.coe, hu,
    max_eq_right (u 1).property.2, min_eq_left (u 0).property.2, min_eq_left (u 1).property.2,
    max_eq_right (sub_le_self 1 (u 0).property.1)]

private theorem ThirdHurewicz.fourSimplexFill_boundary_common_zeros (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) :
    ∃ i j : Fin 5,
      i ≠ j ∧
        fourSimplexFillA u i = 0 ∧
          fourSimplexFillA u j = 0 ∧
            fourSimplexFillB (fourSimplexReflectFirst u) i = 0 ∧
              fourSimplexFillB (fourSimplexReflectFirst u) j = 0 := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · exact ⟨1, 4, by decide, fourSimplexFill_first_zero u hi⟩
    · exact ⟨2, 3, by decide, fourSimplexFill_second_zero u hi⟩
    · exact ⟨3, 4, by decide, fourSimplexFill_third_zero u hi⟩
  · fin_cases i
    · exact ⟨0, 3, by decide, fourSimplexFill_first_one u hi⟩
    · exact ⟨0, 1, by decide, fourSimplexFill_second_one u hi⟩
    · exact ⟨1, 2, by decide, fourSimplexFill_third_one u hi⟩

private theorem ThirdHurewicz.fourSimplexFillA_first_eq_second (u : Fin 3 → (unitInterval))
    (hu : u 0 = u 1) : fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  refine ⟨1, 3, by decide, ?_, ?_⟩
  · simp [fourSimplexFillA, DFunLike.coe, hu]
  · simp [fourSimplexFillA, DFunLike.coe, hu]

private theorem ThirdHurewicz.fourSimplexFillA_first_eq_third (u : Fin 3 → (unitInterval))
    (hu : u 0 = u 2) : fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  refine ⟨1, 3, by decide, ?_, ?_⟩
  · simp [fourSimplexFillA, DFunLike.coe, hu]
  · simp [fourSimplexFillA, DFunLike.coe, hu]

private theorem ThirdHurewicz.fourSimplexFillA_second_eq_third (u : Fin 3 → (unitInterval))
    (hu : u 1 = u 2) : fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  rcases le_total (u 0 : ℝ) (u 2 : ℝ) with h | h
  · refine ⟨1, 2, by decide, ?_, ?_⟩
    · simp [fourSimplexFillA, DFunLike.coe, hu, min_eq_left h]
    · simp [fourSimplexFillA, DFunLike.coe, hu]
  · refine ⟨2, 3, by decide, ?_, ?_⟩
    · simp [fourSimplexFillA, DFunLike.coe, hu]
    · simp [fourSimplexFillA, DFunLike.coe, hu, min_eq_right h]

private theorem ThirdHurewicz.fourSimplexFillB_first_eq_second (u : Fin 3 → (unitInterval))
    (hu : u 0 = u 1) : fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  rcases le_total (u 1 : ℝ) (u 2 : ℝ) with h | h
  · refine ⟨0, 2, by decide, ?_, ?_⟩
    · simp [fourSimplexFillB, DFunLike.coe, hu]
    · simp [fourSimplexFillB, DFunLike.coe, min_eq_left h]
  · refine ⟨0, 4, by decide, ?_, ?_⟩
    · simp [fourSimplexFillB, DFunLike.coe, hu]
    · simp [fourSimplexFillB, DFunLike.coe, hu, min_eq_right h]

private theorem ThirdHurewicz.fourSimplexFillB_first_eq_third (u : Fin 3 → (unitInterval))
    (hu : u 0 = u 2) : fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  rcases le_total (u 2 : ℝ) (u 1 : ℝ) with h | h
  · refine ⟨0, 4, by decide, ?_, ?_⟩
    · simp [fourSimplexFillB, DFunLike.coe, hu, min_eq_left h]
    · simp [fourSimplexFillB, DFunLike.coe, hu]
  · refine ⟨2, 4, by decide, ?_, ?_⟩
    · simp [fourSimplexFillB, DFunLike.coe, min_eq_left h]
    · simp [fourSimplexFillB, DFunLike.coe, hu]

private theorem ThirdHurewicz.fourSimplexFillB_second_eq_third (u : Fin 3 → (unitInterval))
    (hu : u 1 = u 2) : fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  rcases le_total (u 0 : ℝ) (u 2 : ℝ) with h | h
  · refine ⟨0, 2, by decide, ?_, ?_⟩
    · simp [fourSimplexFillB, DFunLike.coe, hu, min_eq_left h]
    · simp [fourSimplexFillB, DFunLike.coe, hu]
  · refine ⟨2, 4, by decide, ?_, ?_⟩
    · simp [fourSimplexFillB, DFunLike.coe, hu]
    · simp [fourSimplexFillB, DFunLike.coe, min_eq_right h]

private theorem ThirdHurewicz.fourSimplexFillA_internal (u : Fin 3 → (unitInterval)) (i j : Fin 3)
    (hij : i ≠ j) (hu : u i = u j) : fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact fourSimplexFillA_first_eq_second u hu
  · exact fourSimplexFillA_first_eq_third u hu
  · exact fourSimplexFillA_first_eq_second u hu.symm
  · exact (hij rfl).elim
  · exact fourSimplexFillA_second_eq_third u hu
  · exact fourSimplexFillA_first_eq_third u hu.symm
  · exact fourSimplexFillA_second_eq_third u hu.symm
  · exact (hij rfl).elim

private theorem ThirdHurewicz.fourSimplexFillB_internal (u : Fin 3 → (unitInterval)) (i j : Fin 3)
    (hij : i ≠ j) (hu : u i = u j) : fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact fourSimplexFillB_first_eq_second u hu
  · exact fourSimplexFillB_first_eq_third u hu
  · exact fourSimplexFillB_first_eq_second u hu.symm
  · exact (hij rfl).elim
  · exact fourSimplexFillB_second_eq_third u hu
  · exact fourSimplexFillB_first_eq_third u hu.symm
  · exact fourSimplexFillB_second_eq_third u hu.symm
  · exact (hij rfl).elim

private theorem ThirdHurewicz.fourSimplexFillA_boundary (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) : fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  obtain ⟨i, j, hij, hi, hj, _, _⟩ := fourSimplexFill_boundary_common_zeros u hu
  exact ⟨i, j, hij, hi, hj⟩

private theorem ThirdHurewicz.fourSimplexFillB_boundary (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) : fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  obtain ⟨i, j, hij, _, _, hi, hj⟩ :=
    fourSimplexFill_boundary_common_zeros (fourSimplexReflectFirst u)
      (fourSimplexReflectFirst_boundary u hu)
  exact
    ⟨i, j, hij, by simpa only [fourSimplexReflectFirst_involutive] using hi, by
      simpa only [fourSimplexReflectFirst_involutive] using hj⟩

private theorem ThirdHurewicz.fourSimplexFill_blend_boundary (t : (unitInterval))
    (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend t (fourSimplexFillA u)
        (fourSimplexFillB (fourSimplexReflectFirst u)) ∈
      fourSimplexTwoSkeleton := by
  obtain ⟨i, j, hij, hai, haj, hbi, hbj⟩ := fourSimplexFill_boundary_common_zeros u hu
  exact
    ⟨i, j, hij,
      SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate t _ _ i hai hbi,
      SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate t _ _ j haj hbj⟩

private abbrev ThirdHurewicz.NativeCube :=
  Fin 3 → (unitInterval)

private def ThirdHurewicz.nativeCubeClass {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : Additive (π_ 3 X x) :=
  Additive.ofMul (⟦p⟧ : π_ 3 X x)

private theorem ThirdHurewicz.nativeCubeClass_homotopic {X : Type*} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 3) X x} (h : GenLoop.Homotopic p q) :
    nativeCubeClass p = nativeCubeClass q :=
  congrArg (fun a : π_ 3 X x => Additive.ofMul a) (Quotient.sound h)

private theorem
    ThirdHurewicz.nativeCubeClass_transAt {X : Type*} [TopologicalSpace X] {x : X} (i : Fin 3)
    (p q : GenLoop (Fin 3) X x) :
    nativeCubeClass (GenLoop.transAt i p q) = nativeCubeClass p + nativeCubeClass q :=
  congrArg Additive.ofMul
    ((HomotopyGroup.mul_spec (i := i) (p := q) (q := p)).symm.trans (mul_comm _ _))

private theorem
    ThirdHurewicz.nativeCubeClass_symmAt {X : Type*} [TopologicalSpace X] {x : X} (i : Fin 3)
    (p : GenLoop (Fin 3) X x) : nativeCubeClass (GenLoop.symmAt i p) = -nativeCubeClass p :=
  congrArg Additive.ofMul (HomotopyGroup.inv_spec (i := i) (p := p)).symm

private def ThirdHurewicz.NativeCubeInternalBased {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : Prop :=
  ∀ u : NativeCube, ∀ i j : Fin 3, i ≠ j → u i = u j → p u = x

private inductive ThirdHurewicz.NativeCubeSameFlat (a b : NativeCube) : Prop
  | zero (i : Fin 3) (ha : a i = 0) (hb : b i = 0)
  | one (i : Fin 3) (ha : a i = 1) (hb : b i = 1)
  | equal (i j : Fin 3) (hij : i ≠ j) (ha : a i = a j) (hb : b i = b j)

private def
    ThirdHurewicz.nativeCubeBlend (t : (unitInterval)) (a b : NativeCube) : NativeCube := fun i =>
  Set.Icc.convexComb (a i) (b i) t

@[simp]
private theorem
    ThirdHurewicz.nativeCubeBlend_zero (a b : NativeCube) : nativeCubeBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

@[simp]
private theorem
    ThirdHurewicz.nativeCubeBlend_one (a b : NativeCube) : nativeCubeBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

private def ThirdHurewicz.nativeCubeBlendMap (f g : C(NativeCube, NativeCube)) :
    C((unitInterval) × NativeCube, NativeCube)
    where
  toFun u := nativeCubeBlend u.1 (f u.2) (g u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (f.continuous.comp continuous_snd)).prodMk
          (((continuous_apply i).comp (g.continuous.comp continuous_snd)).prodMk continuous_fst))

private theorem ThirdHurewicz.nativeCubeBlend_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) {a b : NativeCube}
    (h : NativeCubeSameFlat a b) (t : (unitInterval)) : p (nativeCubeBlend t a b) = x := by
  cases h with
  | zero i ha hb => exact p.property _ ⟨i, Or.inl (by simp [nativeCubeBlend, ha, hb])⟩
  | one i ha hb => exact p.property _ ⟨i, Or.inr (by simp [nativeCubeBlend, ha, hb])⟩
  | equal i j hij ha hb => exact hp _ i j hij (by simp only [nativeCubeBlend, ha, hb])

private def ThirdHurewicz.nativeCubePullbackLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (f : C(NativeCube, NativeCube))
    (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x) : GenLoop (Fin 3) X x :=
  ⟨p.val.comp f, hf⟩

private def ThirdHurewicz.nativeCubeLinearHomotopy {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (f g : C(NativeCube, NativeCube))
    (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary (Fin 3), p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (g u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel (nativeCubePullbackLoop p g hg).val
      (Cube.boundary (Fin 3))
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

private def ThirdHurewicz.fourSimplexLoopA {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : GenLoop (Fin 3) X x :=
  ⟨τ.val.comp fourSimplexFillA, fun u hu => τ.property _ (fourSimplexFillA_boundary u hu)⟩

private def ThirdHurewicz.fourSimplexLoopB {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : GenLoop (Fin 3) X x :=
  ⟨τ.val.comp fourSimplexFillB, fun u hu => τ.property _ (fourSimplexFillB_boundary u hu)⟩

private theorem ThirdHurewicz.fourSimplexLoopA_internal {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) (u : Fin 3 → (unitInterval)) (i j : Fin 3) (hij : i ≠ j)
    (hu : u i = u j) : fourSimplexLoopA τ u = x :=
  τ.property _ (fourSimplexFillA_internal u i j hij hu)

private theorem ThirdHurewicz.fourSimplexLoopB_internal {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) (u : Fin 3 → (unitInterval)) (i j : Fin 3) (hij : i ≠ j)
    (hu : u i = u j) : fourSimplexLoopB τ u = x :=
  τ.property _ (fourSimplexFillB_internal u i j hij hu)

private theorem ThirdHurewicz.fourSimplexReflectFirst_eq_update (u : Fin 3 → (unitInterval)) :
    fourSimplexReflectFirst u = Function.update u 0 ((unitInterval.symm) (u 0)) := by
  funext i
  fin_cases i <;> simp [fourSimplexReflectFirst]

private def ThirdHurewicz.fourSimplexFillingsHomotopy {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    (fourSimplexLoopA τ).val.HomotopyRel (GenLoop.symmAt 0 (fourSimplexLoopB τ)).val
      (Cube.boundary (Fin 3))
    where
  toFun
    p :=
    τ.val
      (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend p.1 (fourSimplexFillA p.2)
        (fourSimplexFillB (fourSimplexReflectFirst p.2)))
  continuous_toFun :=
    τ.val.continuous.comp
      (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlendMap fourSimplexFillA
          (fourSimplexFillB.comp fourSimplexReflectFirst)).continuous
  map_zero_left
    u := by
    change
      τ.val (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend 0 _ _) =
        τ.val (fourSimplexFillA u)
    rw [SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero]
  map_one_left
    u := by
    change
      τ.val (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend 1 _ _) =
        τ.val (fourSimplexFillB (Function.update u 0 ((unitInterval.symm) (u 0))))
    rw [SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_one,
      fourSimplexReflectFirst_eq_update]
  prop' t u
    hu :=
    (τ.property _ (fourSimplexFill_blend_boundary t u hu)).trans
      ((fourSimplexLoopA τ).property u hu).symm

private theorem
    ThirdHurewicz.fourSimplexFillings_additiveClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    nativeCubeClass (fourSimplexLoopA τ) = -nativeCubeClass (fourSimplexLoopB τ) :=
  (nativeCubeClass_homotopic ⟨fourSimplexFillingsHomotopy τ⟩).trans
    (nativeCubeClass_symmAt 0 (fourSimplexLoopB τ))

private def ThirdHurewicz.nativeCubeTetrahedronQuotient (e : Equiv.Perm (Fin 3)) :
    C(NativeCube, NativeCube) :=
  (Geometry.cubeTetrahedron e).comp threeSimplexQuotient

@[simp]
private theorem ThirdHurewicz.nativeCubeTetrahedronQuotient_coordinate_zero (e : Equiv.Perm (Fin 3))
    (u : NativeCube) : nativeCubeTetrahedronQuotient e u (e 0) = u 0 := by
  apply Subtype.ext
  change (Geometry.cubeTetrahedron e (threeSimplexQuotient u) (e 0) : ℝ) = (u 0 : ℝ)
  rw [Geometry.cubeTetrahedron_coordinate_zero, threeSimplexQuotient_one,
    threeSimplexQuotient_two, threeSimplexQuotient_three]
  ring

@[simp]
private theorem ThirdHurewicz.nativeCubeTetrahedronQuotient_coordinate_one (e : Equiv.Perm (Fin 3))
    (u : NativeCube) : nativeCubeTetrahedronQuotient e u (e 1) = Min.min (u 0) (u 1) := by
  apply Subtype.ext
  change
    (Geometry.cubeTetrahedron e (threeSimplexQuotient u) (e 1) : ℝ) = Min.min (u 0 : ℝ) (u 1 : ℝ)
  rw [Geometry.cubeTetrahedron_coordinate_one, threeSimplexQuotient_two,
    threeSimplexQuotient_three]
  exact sub_add_cancel _ _

@[simp]
private theorem ThirdHurewicz.nativeCubeTetrahedronQuotient_coordinate_two (e : Equiv.Perm (Fin 3))
    (u : NativeCube) :
    nativeCubeTetrahedronQuotient e u (e 2) = Min.min (u 0) (Min.min (u 1) (u 2)) := by
  apply Subtype.ext
  change
    (Geometry.cubeTetrahedron e (threeSimplexQuotient u) (e 2) : ℝ) =
      Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ))
  rw [Geometry.cubeTetrahedron_coordinate_two, threeSimplexQuotient_three]

private theorem ThirdHurewicz.nativeCubeTetrahedron_coordinate_sum (s : FirstHurewicz.Simplex 3) :
    s 0 + s 1 + s 2 + s 3 = 1 := by
  have hs := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
  linarith

private theorem ThirdHurewicz.nativeCubeTetrahedron_based {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) (hs : s ∈ threeSimplexBoundary) :
    p (Geometry.cubeTetrahedron e s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨e 0, Or.inr ?_⟩
    apply Subtype.ext
    change (Geometry.cubeTetrahedron e s (e 0) : ℝ) = 1
    rw [Geometry.cubeTetrahedron_coordinate_zero]
    linarith [nativeCubeTetrahedron_coordinate_sum s]
  · change s 1 = 0 at hi
    apply hp _ (e 0) (e 1) (e.injective.ne (by decide))
    apply Subtype.ext
    simp [hi]
  · change s 2 = 0 at hi
    apply hp _ (e 1) (e 2) (e.injective.ne (by decide))
    apply Subtype.ext
    simp [hi]
  · change s 3 = 0 at hi
    apply p.property
    refine ⟨e 2, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi

private def ThirdHurewicz.nativeBasedCubeTetrahedron {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) :
    BasedThreeSimplex x :=
  ⟨p.val.comp (Geometry.cubeTetrahedron e), nativeCubeTetrahedron_based p hp e⟩

private theorem
    ThirdHurewicz.nativeCubeTetrahedronQuotient_based {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3))
    (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    p (nativeCubeTetrahedronQuotient e u) = x :=
  nativeCubeTetrahedron_based p hp e _ (threeSimplexQuotient_boundary u hu)

private def ThirdHurewicz.fourSimplexTetrahedronA {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) (e : Equiv.Perm (Fin 3)) : BasedThreeSimplex x :=
  nativeBasedCubeTetrahedron (fourSimplexLoopA τ) (fourSimplexLoopA_internal τ) e

private def ThirdHurewicz.fourSimplexTetrahedronB {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) (e : Equiv.Perm (Fin 3)) : BasedThreeSimplex x :=
  nativeBasedCubeTetrahedron (fourSimplexLoopB τ) (fourSimplexLoopB_internal τ) e

private theorem ThirdHurewicz.fourSimplexTetrahedron_coordinate_perm (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) (i : Fin 3) :
    (Geometry.cubeTetrahedron e s i : ℝ) = ![s 1 + s 2 + s 3, s 2 + s 3, s 3] (e.symm i) := by
  obtain ⟨j, rfl⟩ := e.surjective i
  fin_cases j <;> simp

private theorem ThirdHurewicz.fourSimplexTetrahedron_zero_coordinate (s : FirstHurewicz.Simplex 3)
    (i : Fin 3) :
    (Geometry.cubeTetrahedron (Geometry.cubePermutation 0) s i : ℝ) =
      ![s 1 + s 2 + s 3, s 2 + s 3, s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  rfl

private theorem ThirdHurewicz.fourSimplexTetrahedron_one_coordinate (s : FirstHurewicz.Simplex 3)
    (i : Fin 3) :
    (Geometry.cubeTetrahedron (Geometry.cubePermutation 1) s i : ℝ) =
      ![s 1 + s 2 + s 3, s 3, s 2 + s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [Geometry.cubePermutation, Equiv.swap_apply_def]

private theorem ThirdHurewicz.fourSimplexTetrahedron_two_coordinate (s : FirstHurewicz.Simplex 3)
    (i : Fin 3) :
    (Geometry.cubeTetrahedron (Geometry.cubePermutation 2) s i : ℝ) =
      ![s 2 + s 3, s 1 + s 2 + s 3, s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [Geometry.cubePermutation, Equiv.swap_apply_def]

private theorem ThirdHurewicz.fourSimplexTetrahedron_three_coordinate (s : FirstHurewicz.Simplex 3)
    (i : Fin 3) :
    (Geometry.cubeTetrahedron (Geometry.cubePermutation 3) s i : ℝ) =
      ![s 2 + s 3, s 3, s 1 + s 2 + s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [Geometry.cubePermutation, Equiv.swap_apply_def]

private theorem ThirdHurewicz.fourSimplexTetrahedron_four_coordinate (s : FirstHurewicz.Simplex 3)
    (i : Fin 3) :
    (Geometry.cubeTetrahedron (Geometry.cubePermutation 4) s i : ℝ) =
      ![s 3, s 1 + s 2 + s 3, s 2 + s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [Geometry.cubePermutation, Equiv.swap_apply_def]

private theorem ThirdHurewicz.fourSimplexTetrahedron_five_coordinate (s : FirstHurewicz.Simplex 3)
    (i : Fin 3) :
    (Geometry.cubeTetrahedron (Geometry.cubePermutation 5) s i : ℝ) =
      ![s 3, s 2 + s 3, s 1 + s 2 + s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [Geometry.cubePermutation, Equiv.swap_apply_def]

private theorem ThirdHurewicz.fourSimplexTetrahedron_tail_le_middle (s : FirstHurewicz.Simplex 3) :
    s 3 ≤ s 2 + s 3 :=
  le_add_of_nonneg_left (stdSimplex.zero_le s 2)

private theorem ThirdHurewicz.fourSimplexTetrahedron_middle_le_first (s : FirstHurewicz.Simplex 3) :
    s 2 + s 3 ≤ s 1 + s 2 + s 3 := by linarith [stdSimplex.zero_le s 1]

private theorem ThirdHurewicz.fourSimplexTetrahedron_tail_le_first (s : FirstHurewicz.Simplex 3) :
    s 3 ≤ s 1 + s 2 + s 3 :=
  (fourSimplexTetrahedron_tail_le_middle s).trans (fourSimplexTetrahedron_middle_le_first s)

private theorem ThirdHurewicz.fourSimplexTetrahedron_sum (s : FirstHurewicz.Simplex 3) :
    s 0 + s 1 + s 2 + s 3 = 1 := by
  have h := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  change s 0 + (s 1 + (s 2 + s 3)) = 1 at h
  linarith

private theorem ThirdHurewicz.fourSimplexFillA_tetrahedron_zero (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 0) s) : Fin 5 → ℝ) =
      ![s 0, s 1, s 2, 0, s 3] := by
  have fourSimplexFillA_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillA_one (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillA_two (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillA_three (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 3 =
      Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
    rfl
  have fourSimplexFillA_four (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 4 = Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillA_zero, fourSimplexFillA_one, fourSimplexFillA_two,
      fourSimplexFillA_three, fourSimplexFillA_four, fourSimplexTetrahedron_zero_coordinate,
      min_eq_right hca]
  all_goals linarith

private theorem ThirdHurewicz.fourSimplexFillB_tetrahedron_zero (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 0) s) : Fin 5 → ℝ) =
      ![s 1, s 0, s 2, s 3, 0] := by
  have fourSimplexFillB_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 0 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillB_one (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 1 = 1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_two (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillB_three (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_four (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 4 = (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillB_zero, fourSimplexFillB_one, fourSimplexFillB_two,
      fourSimplexFillB_three, fourSimplexFillB_four, fourSimplexTetrahedron_zero_coordinate,
      min_eq_right hca]
  all_goals linarith

private theorem ThirdHurewicz.fourSimplexFillA_tetrahedron_one (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 1) s) : Fin 5 → ℝ) =
      ![s 0, s 1, 0, 0, s 2 + s 3] := by
  have fourSimplexFillA_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillA_one (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillA_two (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillA_three (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 3 =
      Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
    rfl
  have fourSimplexFillA_four (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 4 = Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillA_zero, fourSimplexFillA_one, fourSimplexFillA_two,
      fourSimplexFillA_three, fourSimplexFillA_four, fourSimplexTetrahedron_one_coordinate,
      max_eq_left hca, min_eq_right hca]
  all_goals linarith

private theorem ThirdHurewicz.fourSimplexFillB_tetrahedron_one (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 1) s) : Fin 5 → ℝ) =
      ![s 1 + s 2, s 0, 0, s 3, 0] := by
  have fourSimplexFillB_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 0 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillB_one (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 1 = 1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_two (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillB_three (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_four (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 4 = (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillB_zero, fourSimplexFillB_one, fourSimplexFillB_two,
      fourSimplexFillB_three, fourSimplexFillB_four, fourSimplexTetrahedron_one_coordinate,
      min_eq_right hca]
  all_goals linarith

private theorem ThirdHurewicz.fourSimplexFillA_tetrahedron_two (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 2) s) : Fin 5 → ℝ) =
      ![s 0, 0, s 1 + s 2, 0, s 3] := by
  have fourSimplexFillA_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillA_one (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillA_two (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillA_three (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 3 =
      Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
    rfl
  have fourSimplexFillA_four (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 4 = Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillA_zero, fourSimplexFillA_one, fourSimplexFillA_two,
      fourSimplexFillA_three, fourSimplexFillA_four, fourSimplexTetrahedron_two_coordinate,
      max_eq_left hca, min_eq_right hca]
  all_goals linarith

private theorem ThirdHurewicz.fourSimplexFillB_tetrahedron_two (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 2) s) : Fin 5 → ℝ) =
      ![0, s 0, s 1 + s 2, s 3, 0] := by
  have fourSimplexFillB_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 0 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillB_one (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 1 = 1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_two (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillB_three (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_four (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 4 = (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillB_zero, fourSimplexFillB_one, fourSimplexFillB_two,
      fourSimplexFillB_three, fourSimplexFillB_four, fourSimplexTetrahedron_two_coordinate,
      max_eq_left hca, min_eq_right hca]
  all_goals linarith

private theorem ThirdHurewicz.fourSimplexFillA_tetrahedron_three (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 3) s) : Fin 5 → ℝ) =
      ![s 0 + s 1, 0, 0, 0, s 2 + s 3] := by
  have fourSimplexFillA_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillA_one (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillA_two (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillA_three (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 3 =
      Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
    rfl
  have fourSimplexFillA_four (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 4 = Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillA_zero, fourSimplexFillA_one, fourSimplexFillA_two,
      fourSimplexFillA_three, fourSimplexFillA_four, fourSimplexTetrahedron_three_coordinate,
      max_eq_right hca, min_eq_left hca]
  all_goals linarith

private theorem ThirdHurewicz.fourSimplexFillB_tetrahedron_three (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 3) s) : Fin 5 → ℝ) =
      ![s 2, s 0, 0, s 3, s 1] := by
  have fourSimplexFillB_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 0 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillB_one (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 1 = 1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_two (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillB_three (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_four (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 4 = (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillB_zero, fourSimplexFillB_one, fourSimplexFillB_two,
      fourSimplexFillB_three, fourSimplexFillB_four, fourSimplexTetrahedron_three_coordinate,
      max_eq_right hca, min_eq_left hca]
  all_goals linarith

private theorem ThirdHurewicz.fourSimplexFillA_tetrahedron_four (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 4) s) : Fin 5 → ℝ) =
      ![s 0, 0, s 1, s 2, s 3] := by
  have fourSimplexFillA_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillA_one (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillA_two (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillA_three (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 3 =
      Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
    rfl
  have fourSimplexFillA_four (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 4 = Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillA_zero, fourSimplexFillA_one, fourSimplexFillA_two,
      fourSimplexFillA_three, fourSimplexFillA_four, fourSimplexTetrahedron_four_coordinate,
      max_eq_right hca, min_eq_left hca]
  all_goals linarith

private theorem ThirdHurewicz.fourSimplexFillB_tetrahedron_four (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 4) s) : Fin 5 → ℝ) =
      ![0, s 0, s 1, s 3, s 2] := by
  have fourSimplexFillB_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 0 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillB_one (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 1 = 1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_two (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillB_three (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_four (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 4 = (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillB_zero, fourSimplexFillB_one, fourSimplexFillB_two,
      fourSimplexFillB_three, fourSimplexFillB_four, fourSimplexTetrahedron_four_coordinate,
      min_eq_left hca, max_eq_right hca]
  all_goals linarith

private theorem ThirdHurewicz.fourSimplexFillA_tetrahedron_five (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 5) s) : Fin 5 → ℝ) =
      ![s 0 + s 1, 0, 0, s 2, s 3] := by
  have fourSimplexFillA_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillA_one (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillA_two (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillA_three (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 3 =
      Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
    rfl
  have fourSimplexFillA_four (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 4 = Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillA_zero, fourSimplexFillA_one, fourSimplexFillA_two,
      fourSimplexFillA_three, fourSimplexFillA_four, fourSimplexTetrahedron_five_coordinate,
      min_eq_left hca]
  all_goals linarith

private theorem ThirdHurewicz.fourSimplexFillB_tetrahedron_five (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 5) s) : Fin 5 → ℝ) =
      ![0, s 0, 0, s 3, s 1 + s 2] := by
  have fourSimplexFillB_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 0 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillB_one (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 1 = 1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_two (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillB_three (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_four (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 4 = (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillB_zero, fourSimplexFillB_one, fourSimplexFillB_two,
      fourSimplexFillB_three, fourSimplexFillB_four, fourSimplexTetrahedron_five_coordinate,
      max_eq_right hca, min_eq_left hca]
  all_goals linarith

private theorem ThirdHurewicz.simplexFace_three_zero (s : FirstHurewicz.Simplex 3) :
    (FirstHurewicz.simplexFace 3 0 s : Fin 5 → ℝ) = ![0, s 0, s 1, s 2, s 3] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_self 3 0 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 0 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 0 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 0 s 2
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 0 s 3

private theorem ThirdHurewicz.simplexFace_three_one (s : FirstHurewicz.Simplex 3) :
    (FirstHurewicz.simplexFace 3 1 s : Fin 5 → ℝ) = ![s 0, 0, s 1, s 2, s 3] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 1 s 0
  · exact FirstHurewicz.simplexFace_apply_self 3 1 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 1 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 1 s 2
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 1 s 3

private theorem ThirdHurewicz.simplexFace_three_two (s : FirstHurewicz.Simplex 3) :
    (FirstHurewicz.simplexFace 3 2 s : Fin 5 → ℝ) = ![s 0, s 1, 0, s 2, s 3] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 2 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 2 s 1
  · exact FirstHurewicz.simplexFace_apply_self 3 2 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 2 s 2
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 2 s 3

private theorem ThirdHurewicz.simplexFace_three_three (s : FirstHurewicz.Simplex 3) :
    (FirstHurewicz.simplexFace 3 3 s : Fin 5 → ℝ) = ![s 0, s 1, s 2, 0, s 3] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 3 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 3 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 3 s 2
  · exact FirstHurewicz.simplexFace_apply_self 3 3 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 3 s 3

private theorem ThirdHurewicz.simplexFace_three_four (s : FirstHurewicz.Simplex 3) :
    (FirstHurewicz.simplexFace 3 4 s : Fin 5 → ℝ) = ![s 0, s 1, s 2, s 3, 0] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 4 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 4 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 4 s 2
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 4 s 3
  · exact FirstHurewicz.simplexFace_apply_self 3 4 s

private theorem ThirdHurewicz.fourSimplexTetrahedronA_zero {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (Geometry.cubePermutation 0) = basedFourSimplexFace τ 3 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change
    τ.val (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 0) s)) =
      τ.val (FirstHurewicz.simplexFace 3 3 s)
  apply congrArg τ.val
  apply Subtype.ext
  exact (fourSimplexFillA_tetrahedron_zero s).trans (simplexFace_three_three s).symm

private theorem ThirdHurewicz.fourSimplexTetrahedronA_one {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (Geometry.cubePermutation 1) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 1) s)) = x
  apply τ.property
  exact
    ⟨2, 3, by decide, (congrFun (fourSimplexFillA_tetrahedron_one s) 2).trans rfl,
      (congrFun (fourSimplexFillA_tetrahedron_one s) 3).trans rfl⟩

private theorem ThirdHurewicz.fourSimplexTetrahedronA_two {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (Geometry.cubePermutation 2) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 2) s)) = x
  apply τ.property
  exact
    ⟨1, 3, by decide, (congrFun (fourSimplexFillA_tetrahedron_two s) 1).trans rfl,
      (congrFun (fourSimplexFillA_tetrahedron_two s) 3).trans rfl⟩

private theorem ThirdHurewicz.fourSimplexTetrahedronA_three {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (Geometry.cubePermutation 3) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 3) s)) = x
  apply τ.property
  exact
    ⟨1, 2, by decide, (congrFun (fourSimplexFillA_tetrahedron_three s) 1).trans rfl,
      (congrFun (fourSimplexFillA_tetrahedron_three s) 2).trans rfl⟩

private theorem ThirdHurewicz.fourSimplexTetrahedronA_four {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (Geometry.cubePermutation 4) = basedFourSimplexFace τ 1 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change
    τ.val (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 4) s)) =
      τ.val (FirstHurewicz.simplexFace 3 1 s)
  apply congrArg τ.val
  apply Subtype.ext
  exact (fourSimplexFillA_tetrahedron_four s).trans (simplexFace_three_one s).symm

private theorem ThirdHurewicz.fourSimplexTetrahedronA_five {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (Geometry.cubePermutation 5) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 5) s)) = x
  apply τ.property
  exact
    ⟨1, 2, by decide, (congrFun (fourSimplexFillA_tetrahedron_five s) 1).trans rfl,
      (congrFun (fourSimplexFillA_tetrahedron_five s) 2).trans rfl⟩

private def ThirdHurewicz.cubeThirdCycle : C(Fin 3 → (unitInterval), Fin 3 → (unitInterval))
    where
  toFun u := ![u 1, u 2, u 0]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

private theorem ThirdHurewicz.cubeThirdCycle_boundary (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) : cubeThirdCycle u ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · exact ⟨2, by simpa [cubeThirdCycle] using hi⟩
  · exact ⟨0, by simpa [cubeThirdCycle] using hi⟩
  · exact ⟨1, by simpa [cubeThirdCycle] using hi⟩

private def ThirdHurewicz.cubeThirdCyclicReverse : C(Fin 3 → (unitInterval), Fin 3 → (unitInterval))
    where
  toFun u := ![u 1, u 2, (unitInterval.symm) (u 0)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

private theorem ThirdHurewicz.cubeThirdCyclicReverse_boundary (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) : cubeThirdCyclicReverse u ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · change u 0 = 0 ∨ u 0 = 1 at hi
    rcases hi with hi | hi
    · exact ⟨2, Or.inr (by simp [cubeThirdCyclicReverse, hi])⟩
    · exact ⟨2, Or.inl (by simp [cubeThirdCyclicReverse, hi])⟩
  · exact ⟨0, by simpa [cubeThirdCyclicReverse] using hi⟩
  · exact ⟨1, by simpa [cubeThirdCyclicReverse] using hi⟩

private def ThirdHurewicz.cyclicThreeLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : GenLoop (Fin 3) X x :=
  ⟨p.val.comp cubeThirdCycle, fun u hu => p.property _ (cubeThirdCycle_boundary u hu)⟩

private def ThirdHurewicz.cyclicReverseThreeLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : GenLoop (Fin 3) X x :=
  ⟨p.val.comp cubeThirdCyclicReverse, fun u hu =>
    p.property _ (cubeThirdCyclicReverse_boundary u hu)⟩

private theorem
    ThirdHurewicz.cubeInsert01_boundary (a : Fin 2 → (unitInterval)) (b : (unitInterval))
    (ha : a ∈ Cube.boundary (Fin 2)) : ![a 0, a 1, b] ∈ Cube.boundary (Fin 3) := by
  rcases ha with ⟨i, hi⟩
  fin_cases i
  · exact ⟨0, by simpa using hi⟩
  · exact ⟨1, by simpa using hi⟩

private theorem
    ThirdHurewicz.cubeInsert12_boundary (a : (unitInterval)) (b : Fin 2 → (unitInterval))
    (hb : b ∈ Cube.boundary (Fin 2)) : ![a, b 0, b 1] ∈ Cube.boundary (Fin 3) := by
  rcases hb with ⟨i, hi⟩
  fin_cases i
  · exact ⟨1, by simpa using hi⟩
  · exact ⟨2, by simpa using hi⟩

private def ThirdHurewicz.cubeQuarter01HomotopyMap :
    C((unitInterval) × (Fin 3 → (unitInterval)), Fin 3 → (unitInterval))
    where
  toFun
    z :=
    ![SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, ![z.2 0, z.2 1]) 0,
      SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, ![z.2 0, z.2 1]) 1, z.2 2]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
private theorem ThirdHurewicz.cubeQuarter01HomotopyMap_zero (u : Fin 3 → (unitInterval)) :
    cubeQuarter01HomotopyMap (0, u) = u := by
  funext i
  fin_cases i <;> simp [cubeQuarter01HomotopyMap]

@[simp]
private theorem ThirdHurewicz.cubeQuarter01HomotopyMap_one (u : Fin 3 → (unitInterval)) :
    cubeQuarter01HomotopyMap (1, u) = ![u 1, (unitInterval.symm) (u 0), u 2] := by
  funext i
  fin_cases i <;> simp [cubeQuarter01HomotopyMap]

private theorem ThirdHurewicz.cubeQuarter01HomotopyMap_boundary (t : (unitInterval))
    (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    cubeQuarter01HomotopyMap (t, u) ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · exact
      cubeInsert01_boundary _ _
        (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary t (![u 0, u 1])
          ⟨0, by simpa using hi⟩)
  · exact
      cubeInsert01_boundary _ _
        (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary t (![u 0, u 1])
          ⟨1, by simpa using hi⟩)
  · exact ⟨2, by simpa [cubeQuarter01HomotopyMap] using hi⟩

private def ThirdHurewicz.cubeQuarter12HomotopyMap :
    C((unitInterval) × (Fin 3 → (unitInterval)), Fin 3 → (unitInterval))
    where
  toFun
    z :=
    ![z.2 0, SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, ![z.2 1, z.2 2]) 0,
      SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, ![z.2 1, z.2 2]) 1]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
private theorem ThirdHurewicz.cubeQuarter12HomotopyMap_zero (u : Fin 3 → (unitInterval)) :
    cubeQuarter12HomotopyMap (0, u) = u := by
  funext i
  fin_cases i <;> simp [cubeQuarter12HomotopyMap]

@[simp]
private theorem ThirdHurewicz.cubeQuarter12HomotopyMap_one (u : Fin 3 → (unitInterval)) :
    cubeQuarter12HomotopyMap (1, u) = ![u 0, u 2, (unitInterval.symm) (u 1)] := by
  funext i
  fin_cases i <;> simp [cubeQuarter12HomotopyMap]

private theorem ThirdHurewicz.cubeQuarter12HomotopyMap_boundary (t : (unitInterval))
    (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    cubeQuarter12HomotopyMap (t, u) ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · exact ⟨0, by simpa [cubeQuarter12HomotopyMap] using hi⟩
  · exact
      cubeInsert12_boundary _ _
        (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary t (![u 1, u 2])
          ⟨0, by simpa using hi⟩)
  · exact
      cubeInsert12_boundary _ _
        (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary t (![u 1, u 2])
          ⟨1, by simpa using hi⟩)

private def ThirdHurewicz.cubeThirdCycleHomotopyMap :
    C((unitInterval) × (Fin 3 → (unitInterval)), Fin 3 → (unitInterval)) :=
  cubeQuarter12HomotopyMap.comp ⟨fun z => (z.1, cubeQuarter01HomotopyMap z), by fun_prop⟩

@[simp]
private theorem ThirdHurewicz.cubeThirdCycleHomotopyMap_zero (u : Fin 3 → (unitInterval)) :
    cubeThirdCycleHomotopyMap (0, u) = u := by
  change cubeQuarter12HomotopyMap (0, cubeQuarter01HomotopyMap (0, u)) = u
  rw [cubeQuarter01HomotopyMap_zero, cubeQuarter12HomotopyMap_zero]

@[simp]
private theorem ThirdHurewicz.cubeThirdCycleHomotopyMap_one (u : Fin 3 → (unitInterval)) :
    cubeThirdCycleHomotopyMap (1, u) = cubeThirdCycle u := by
  change cubeQuarter12HomotopyMap (1, cubeQuarter01HomotopyMap (1, u)) = _
  rw [cubeQuarter01HomotopyMap_one, cubeQuarter12HomotopyMap_one]
  simp [cubeThirdCycle]

private theorem ThirdHurewicz.cubeThirdCycleHomotopyMap_boundary (t : (unitInterval))
    (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    cubeThirdCycleHomotopyMap (t, u) ∈ Cube.boundary (Fin 3) :=
  cubeQuarter12HomotopyMap_boundary t _ (cubeQuarter01HomotopyMap_boundary t u hu)

private def ThirdHurewicz.cyclicThreeLoop_homotopy {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : p.val.HomotopyRel (cyclicThreeLoop p).val (Cube.boundary (Fin 3))
    where
  toFun z := p (cubeThirdCycleHomotopyMap z)
  continuous_toFun := p.val.continuous.comp cubeThirdCycleHomotopyMap.continuous
  map_zero_left u := congrArg p (cubeThirdCycleHomotopyMap_zero u)
  map_one_left u := congrArg p (cubeThirdCycleHomotopyMap_one u)
  prop' t u
    hu := (p.property _ (cubeThirdCycleHomotopyMap_boundary t u hu)).trans (p.property u hu).symm

private theorem ThirdHurewicz.cyclicThreeLoop_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : (⟦cyclicThreeLoop p⟧ : π_ 3 X x) = ⟦p⟧ := by
  have h : (⟦p⟧ : π_ 3 X x) = ⟦cyclicThreeLoop p⟧ :=
    Quotient.sound
      (show GenLoop.Homotopic p (cyclicThreeLoop p) from ⟨cyclicThreeLoop_homotopy p⟩)
  exact h.symm

private theorem ThirdHurewicz.cyclicReverseThreeLoop_eq {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) :
    cyclicReverseThreeLoop p = cyclicThreeLoop (GenLoop.symmAt (2 : Fin 3) p) := by
  apply GenLoop.ext
  intro u
  change
    p ![u 1, u 2, (unitInterval.symm) (u 0)] =
      p
        (fun j =>
          if j = (2 : Fin 3) then (unitInterval.symm) (![u 1, u 2, u 0] 2)
          else ![u 1, u 2, u 0] j)
  congr 1
  funext i
  fin_cases i <;> simp

private theorem ThirdHurewicz.cyclicReverseThreeLoop_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) :
    (⟦cyclicReverseThreeLoop p⟧ : π_ 3 X x) = ((·⁻¹) : π_ 3 X x → π_ 3 X x) ⟦p⟧ := by
  rw [cyclicReverseThreeLoop_eq, cyclicThreeLoop_class]
  exact (HomotopyGroup.inv_spec (i := (2 : Fin 3)) (p := p)).symm

private def ThirdHurewicz.threeSimplexCycle : C(FirstHurewicz.Simplex 3, FirstHurewicz.Simplex 3)
    where
  toFun
    s :=
    ⟨![s 1, s 2, s 3, s 0], by
      constructor
      · intro i
        fin_cases i <;> exact stdSimplex.zero_le s _
      · have hs := stdSimplex.sum_eq_one s
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
        change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
        linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply 1).comp continuous_subtype_val
    · exact (continuous_apply 2).comp continuous_subtype_val
    · exact (continuous_apply 3).comp continuous_subtype_val
    · exact (continuous_apply 0).comp continuous_subtype_val

private theorem ThirdHurewicz.threeSimplexCycle_boundary (s : FirstHurewicz.Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : threeSimplexCycle s ∈ threeSimplexBoundary := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨3, hi⟩
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩
  · exact ⟨2, hi⟩

private def ThirdHurewicz.basedThreeSimplexVertexCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : BasedThreeSimplex x :=
  ⟨τ.val.comp threeSimplexCycle, fun s hs => τ.property _ (threeSimplexCycle_boundary s hs)⟩

private theorem ThirdHurewicz.threeSimplexCycle_quotient_commonZero (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) :
    ∃ i : Fin 4,
      threeSimplexCycle (threeSimplexQuotient u) i = 0 ∧
        threeSimplexQuotient (cubeThirdCyclicReverse u) i = 0 := by
  have threeSimplexCycle_zero (s : FirstHurewicz.Simplex 3) : threeSimplexCycle s 0 = s 1 := rfl
  have threeSimplexCycle_one (s : FirstHurewicz.Simplex 3) : threeSimplexCycle s 1 = s 2 := rfl
  have threeSimplexCycle_two (s : FirstHurewicz.Simplex 3) : threeSimplexCycle s 2 = s 3 := rfl
  have threeSimplexCycle_three (s : FirstHurewicz.Simplex 3) : threeSimplexCycle s 3 = s 0 := rfl
  have cubeThirdCyclicReverse_apply (u : Fin 3 → (unitInterval)) :
    cubeThirdCyclicReverse u = ![u 1, u 2, (unitInterval.symm) (u 0)] := rfl
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨2, ?_, ?_⟩
      · simp [threeSimplexCycle_two, hi, min_eq_left (le_min (u 1).property.1 (u 2).property.1)]
      · simp [cubeThirdCyclicReverse_apply, hi, min_eq_left (u 2).property.2]
    · change u 1 = 0 at hi
      refine ⟨1, ?_, ?_⟩ <;>
        simp [threeSimplexCycle_one, cubeThirdCyclicReverse_apply, hi,
          min_eq_left (u 2).property.1, min_eq_right (u 0).property.1]
    · change u 2 = 0 at hi
      refine ⟨2, ?_, ?_⟩ <;>
        simp [threeSimplexCycle_two, cubeThirdCyclicReverse_apply, hi,
          min_eq_right (u 1).property.1, min_eq_right (u 0).property.1,
          min_eq_left (sub_nonneg.mpr (u 0).property.2)]
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨3, ?_, ?_⟩ <;>
        simp [threeSimplexCycle_three, cubeThirdCyclicReverse_apply, hi,
          min_eq_right (u 2).property.1, min_eq_right (u 1).property.1]
    · change u 1 = 1 at hi
      refine ⟨0, ?_, ?_⟩ <;>
        simp [threeSimplexCycle_zero, cubeThirdCyclicReverse_apply, hi,
          min_eq_left (u 0).property.2]
    · change u 2 = 1 at hi
      refine ⟨1, ?_, ?_⟩ <;>
        simp [threeSimplexCycle_one, cubeThirdCyclicReverse_apply, hi,
          min_eq_left (u 1).property.2]

private theorem ThirdHurewicz.threeSimplexCycle_quotient_blend_boundary (t : (unitInterval))
    (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend t
        (threeSimplexCycle (threeSimplexQuotient u))
        (threeSimplexQuotient (cubeThirdCyclicReverse u)) ∈
      threeSimplexBoundary := by
  obtain ⟨i, hi, hj⟩ := threeSimplexCycle_quotient_commonZero u hu
  exact ⟨i, SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate t _ _ i hi hj⟩

private def ThirdHurewicz.basedThreeSimplexVertexCycle_loopHomotopy {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedThreeSimplex x) :
    (basedThreeSimplexLoop (basedThreeSimplexVertexCycle τ)).val.HomotopyRel
      (cyclicReverseThreeLoop (basedThreeSimplexLoop τ)).val (Cube.boundary (Fin 3))
    where
  toFun
    z :=
    τ.val
      (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend z.1
        (threeSimplexCycle (threeSimplexQuotient z.2))
        (threeSimplexQuotient (cubeThirdCyclicReverse z.2)))
  continuous_toFun :=
    τ.val.continuous.comp
      (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlendMap
          (threeSimplexCycle.comp threeSimplexQuotient)
          (threeSimplexQuotient.comp cubeThirdCyclicReverse)).continuous
  map_zero_left
    u := by
    change
      τ.val (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend 0 _ _) =
        τ.val (threeSimplexCycle (threeSimplexQuotient u))
    rw [SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero]
  map_one_left
    u := by
    change
      τ.val (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend 1 _ _) =
        τ.val (threeSimplexQuotient (cubeThirdCyclicReverse u))
    rw [SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_one]
  prop' t u
    hu :=
    (τ.property _ (threeSimplexCycle_quotient_blend_boundary t u hu)).trans
      ((basedThreeSimplexLoop (basedThreeSimplexVertexCycle τ)).property u hu).symm

@[simp]
private theorem
    ThirdHurewicz.basedThreeSimplexVertexCycle_class {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    basedThreeSimplexClass (basedThreeSimplexVertexCycle τ) = -basedThreeSimplexClass τ := by
  have h :
    GenLoop.Homotopic (basedThreeSimplexLoop (basedThreeSimplexVertexCycle τ))
      (cyclicReverseThreeLoop (basedThreeSimplexLoop τ)) :=
    ⟨basedThreeSimplexVertexCycle_loopHomotopy τ⟩
  have he :
    (⟦basedThreeSimplexLoop (basedThreeSimplexVertexCycle τ)⟧ : π_ 3 X x) =
      ⟦cyclicReverseThreeLoop (basedThreeSimplexLoop τ)⟧ :=
    Quotient.sound h
  exact
    congrArg Additive.ofMul (he.trans (cyclicReverseThreeLoop_class (basedThreeSimplexLoop τ)))

private def ThirdHurewicz.threeSimplexSwapLast : C(FirstHurewicz.Simplex 3, FirstHurewicz.Simplex 3)
    where
  toFun
    s :=
    ⟨![s 0, s 1, s 3, s 2], by
      constructor
      · intro i
        fin_cases i <;> exact s.property.1 _
      · have hs := s.property.2
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
        change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
        simpa only [add_comm (s 2) (s 3)] using hs⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous fun s : FirstHurewicz.Simplex 3 => s 0
      exact (continuous_apply 0).comp continuous_subtype_val
    · change Continuous fun s : FirstHurewicz.Simplex 3 => s 1
      exact (continuous_apply 1).comp continuous_subtype_val
    · change Continuous fun s : FirstHurewicz.Simplex 3 => s 3
      exact (continuous_apply 3).comp continuous_subtype_val
    · change Continuous fun s : FirstHurewicz.Simplex 3 => s 2
      exact (continuous_apply 2).comp continuous_subtype_val

private theorem ThirdHurewicz.threeSimplexSwapLast_boundary (s : FirstHurewicz.Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : threeSimplexSwapLast s ∈ threeSimplexBoundary := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩
  · exact ⟨3, hi⟩
  · exact ⟨2, hi⟩

private def ThirdHurewicz.cubeThirdLastReverse : C(Fin 3 → (unitInterval), Fin 3 → (unitInterval))
    where
  toFun u := ![u 0, u 1, (unitInterval.symm) (u 2)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
private theorem ThirdHurewicz.cubeThirdLastReverse_zero (u : Fin 3 → (unitInterval)) :
    cubeThirdLastReverse u 0 = u 0 :=
  rfl

@[simp]
private theorem ThirdHurewicz.cubeThirdLastReverse_one (u : Fin 3 → (unitInterval)) :
    cubeThirdLastReverse u 1 = u 1 :=
  rfl

@[simp]
private theorem ThirdHurewicz.cubeThirdLastReverse_two (u : Fin 3 → (unitInterval)) :
    cubeThirdLastReverse u 2 = (unitInterval.symm) (u 2) :=
  rfl

private theorem ThirdHurewicz.threeSimplexSwapLast_commonZero (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) :
    ∃ i : Fin 4,
      threeSimplexSwapLast (threeSimplexQuotient u) i = 0 ∧
        threeSimplexQuotient (cubeThirdLastReverse u) i = 0 := by
  have threeSimplexSwapLast_zero (s : FirstHurewicz.Simplex 3) : threeSimplexSwapLast s 0 = s 0 :=
    rfl
  have threeSimplexSwapLast_one (s : FirstHurewicz.Simplex 3) : threeSimplexSwapLast s 1 = s 1 :=
    rfl
  have threeSimplexSwapLast_two (s : FirstHurewicz.Simplex 3) : threeSimplexSwapLast s 2 = s 3 :=
    rfl
  have threeSimplexSwapLast_three (s : FirstHurewicz.Simplex 3) :
    threeSimplexSwapLast s 3 = s 2 := rfl
  rcases hu with ⟨j, hj | hj⟩
  · fin_cases j
    · change u 0 = 0 at hj
      refine ⟨1, ?_, ?_⟩
      · simp [threeSimplexSwapLast_one, hj, min_eq_left (u 1).property.1]
      · simp [hj, min_eq_left (u 1).property.1]
    · change u 1 = 0 at hj
      refine ⟨2, ?_, ?_⟩
      · simp [threeSimplexSwapLast_two, hj, min_eq_left (u 2).property.1,
          min_eq_right (u 0).property.1]
      · simp only [threeSimplexQuotient_two, cubeThirdLastReverse_zero, cubeThirdLastReverse_one,
          cubeThirdLastReverse_two, hj]
        change
          Min.min (u 0 : ℝ) 0 - Min.min (u 0 : ℝ) (Min.min 0 ((unitInterval.symm) (u 2) : ℝ)) = 0
        rw [min_eq_right (u 0).property.1, min_eq_left ((unitInterval.symm) (u 2)).property.1,
          min_eq_right (u 0).property.1, sub_self]
    · change u 2 = 0 at hj
      refine ⟨2, ?_, ?_⟩
      · simp [threeSimplexSwapLast_two, hj, min_eq_right (u 1).property.1,
          min_eq_right (u 0).property.1]
      · simp [hj, min_eq_left (u 1).property.2]
  · fin_cases j
    · change u 0 = 1 at hj
      exact ⟨0, by simp [threeSimplexSwapLast_zero, hj], by simp [hj]⟩
    · change u 1 = 1 at hj
      exact
        ⟨1, by simp [threeSimplexSwapLast_one, hj, min_eq_left (u 0).property.2], by
          simp [hj, min_eq_left (u 0).property.2]⟩
    · change u 2 = 1 at hj
      refine ⟨3, ?_, ?_⟩
      · simp [threeSimplexSwapLast_three, hj, min_eq_left (u 1).property.2]
      · simp [hj, min_eq_right (u 1).property.1, min_eq_right (u 0).property.1]

private def ThirdHurewicz.basedThreeSimplexSwapLast {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : BasedThreeSimplex x :=
  ⟨τ.val.comp threeSimplexSwapLast, fun s hs => τ.property _ (threeSimplexSwapLast_boundary s hs)⟩

private theorem ThirdHurewicz.symmAt_last_apply {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (u : Fin 3 → (unitInterval)) :
    GenLoop.symmAt (2 : Fin 3) p u = p (cubeThirdLastReverse u) := by
  change p (fun j => if j = (2 : Fin 3) then (unitInterval.symm) (u 2) else u j) = _
  congr 1
  funext j
  fin_cases j <;> rfl

private def
    ThirdHurewicz.basedThreeSimplexSwapLast_loopHomotopy {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    (basedThreeSimplexLoop (basedThreeSimplexSwapLast τ)).val.HomotopyRel
      (GenLoop.symmAt (2 : Fin 3) (basedThreeSimplexLoop τ)).val (Cube.boundary (Fin 3))
    where
  toFun
    z :=
    τ.val
      (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend z.1
        (threeSimplexSwapLast (threeSimplexQuotient z.2))
        (threeSimplexQuotient (cubeThirdLastReverse z.2)))
  continuous_toFun :=
    τ.val.continuous.comp
      (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlendMap
          (threeSimplexSwapLast.comp threeSimplexQuotient)
          (threeSimplexQuotient.comp cubeThirdLastReverse)).continuous
  map_zero_left
    u := by
    change τ.val (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend 0 _ _) = _
    rw [SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero]
    rfl
  map_one_left
    u := by
    change
      τ.val (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend 1 _ _) =
        GenLoop.symmAt (2 : Fin 3) (basedThreeSimplexLoop τ) u
    rw [SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_one, symmAt_last_apply]
    rfl
  prop' t u
    hu := by
    obtain ⟨i, ha, hb⟩ := threeSimplexSwapLast_commonZero u hu
    exact
      (τ.property _
            ⟨i,
              SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate t _ _ i ha
                hb⟩).trans
        ((basedThreeSimplexLoop (basedThreeSimplexSwapLast τ)).property u hu).symm

private theorem
    ThirdHurewicz.basedThreeSimplexSwapLast_class {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    basedThreeSimplexClass (basedThreeSimplexSwapLast τ) = -basedThreeSimplexClass τ := by
  have h :
    (⟦basedThreeSimplexLoop (basedThreeSimplexSwapLast τ)⟧ : π_ 3 X x) =
      ⟦GenLoop.symmAt (2 : Fin 3) (basedThreeSimplexLoop τ)⟧ :=
    Quotient.sound ⟨basedThreeSimplexSwapLast_loopHomotopy τ⟩
  exact
    congrArg Additive.ofMul
      (h.trans (HomotopyGroup.inv_spec (i := (2 : Fin 3)) (p := basedThreeSimplexLoop τ)).symm)

private def
    ThirdHurewicz.threeSimplexSwapFirst : C(FirstHurewicz.Simplex 3, FirstHurewicz.Simplex 3) :=
  threeSimplexCycle.comp
    (threeSimplexCycle.comp
      (threeSimplexSwapLast.comp (threeSimplexCycle.comp threeSimplexCycle)))

private theorem ThirdHurewicz.threeSimplexSwapFirst_boundary (s : FirstHurewicz.Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : threeSimplexSwapFirst s ∈ threeSimplexBoundary :=
  threeSimplexCycle_boundary _
    (threeSimplexCycle_boundary _
      (threeSimplexSwapLast_boundary _
        (threeSimplexCycle_boundary _ (threeSimplexCycle_boundary _ hs))))

private def ThirdHurewicz.threeSimplexVertexOrder1302 :
    C(FirstHurewicz.Simplex 3, FirstHurewicz.Simplex 3) :=
  threeSimplexCycle.comp (threeSimplexSwapLast.comp threeSimplexCycle)

private theorem ThirdHurewicz.threeSimplexVertexOrder1302_boundary (s : FirstHurewicz.Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : threeSimplexVertexOrder1302 s ∈ threeSimplexBoundary :=
  threeSimplexCycle_boundary _ (threeSimplexSwapLast_boundary _ (threeSimplexCycle_boundary _ hs))

private def ThirdHurewicz.basedThreeSimplexSwapFirst {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : BasedThreeSimplex x :=
  ⟨τ.val.comp threeSimplexSwapFirst, fun s hs =>
    τ.property _ (threeSimplexSwapFirst_boundary s hs)⟩

private theorem
    ThirdHurewicz.basedThreeSimplexSwapFirst_word {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    basedThreeSimplexSwapFirst τ =
      basedThreeSimplexVertexCycle
        (basedThreeSimplexVertexCycle
          (basedThreeSimplexSwapLast
            (basedThreeSimplexVertexCycle (basedThreeSimplexVertexCycle τ)))) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rfl

@[simp]
private theorem
    ThirdHurewicz.basedThreeSimplexSwapFirst_class {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    basedThreeSimplexClass (basedThreeSimplexSwapFirst τ) = -basedThreeSimplexClass τ := by
  rw [basedThreeSimplexSwapFirst_word]
  simp only [basedThreeSimplexVertexCycle_class, basedThreeSimplexSwapLast_class, neg_neg]

private def ThirdHurewicz.basedThreeSimplexVertexOrder1302 {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : BasedThreeSimplex x :=
  ⟨τ.val.comp threeSimplexVertexOrder1302, fun s hs =>
    τ.property _ (threeSimplexVertexOrder1302_boundary s hs)⟩

private theorem ThirdHurewicz.basedThreeSimplexVertexOrder1302_word {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedThreeSimplex x) :
    basedThreeSimplexVertexOrder1302 τ =
      basedThreeSimplexVertexCycle (basedThreeSimplexSwapLast (basedThreeSimplexVertexCycle τ)) :=
  by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rfl

@[simp]
private theorem ThirdHurewicz.basedThreeSimplexVertexOrder1302_class {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedThreeSimplex x) :
    basedThreeSimplexClass (basedThreeSimplexVertexOrder1302 τ) = -basedThreeSimplexClass τ := by
  rw [basedThreeSimplexVertexOrder1302_word]
  simp only [basedThreeSimplexVertexCycle_class, basedThreeSimplexSwapLast_class, neg_neg]

private theorem ThirdHurewicz.fourSimplexTetrahedronB_zero {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (Geometry.cubePermutation 0) =
      basedThreeSimplexSwapFirst (basedFourSimplexFace τ 4) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change
    τ.val (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 0) s)) =
      τ.val (FirstHurewicz.simplexFace 3 4 (threeSimplexSwapFirst s))
  apply congrArg τ.val
  apply Subtype.ext
  exact
    (fourSimplexFillB_tetrahedron_zero s).trans
      (simplexFace_three_four (threeSimplexSwapFirst s)).symm

private theorem ThirdHurewicz.fourSimplexTetrahedronB_one {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (Geometry.cubePermutation 1) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 1) s)) = x
  apply τ.property
  exact
    ⟨2, 4, by decide, (congrFun (fourSimplexFillB_tetrahedron_one s) 2).trans rfl,
      (congrFun (fourSimplexFillB_tetrahedron_one s) 4).trans rfl⟩

private theorem ThirdHurewicz.fourSimplexTetrahedronB_two {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (Geometry.cubePermutation 2) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 2) s)) = x
  apply τ.property
  exact
    ⟨0, 4, by decide, (congrFun (fourSimplexFillB_tetrahedron_two s) 0).trans rfl,
      (congrFun (fourSimplexFillB_tetrahedron_two s) 4).trans rfl⟩

private theorem ThirdHurewicz.fourSimplexTetrahedronB_three {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (Geometry.cubePermutation 3) =
      basedThreeSimplexVertexOrder1302 (basedFourSimplexFace τ 2) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change
    τ.val (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 3) s)) =
      τ.val (FirstHurewicz.simplexFace 3 2 (threeSimplexVertexOrder1302 s))
  apply congrArg τ.val
  apply Subtype.ext
  exact
    (fourSimplexFillB_tetrahedron_three s).trans
      (simplexFace_three_two (threeSimplexVertexOrder1302 s)).symm

private theorem ThirdHurewicz.fourSimplexTetrahedronB_four {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (Geometry.cubePermutation 4) =
      basedThreeSimplexSwapLast (basedFourSimplexFace τ 0) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change
    τ.val (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 4) s)) =
      τ.val (FirstHurewicz.simplexFace 3 0 (threeSimplexSwapLast s))
  apply congrArg τ.val
  apply Subtype.ext
  exact
    (fourSimplexFillB_tetrahedron_four s).trans
      (simplexFace_three_zero (threeSimplexSwapLast s)).symm

private theorem ThirdHurewicz.fourSimplexTetrahedronB_five {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (Geometry.cubePermutation 5) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 5) s)) = x
  apply τ.property
  exact
    ⟨0, 2, by decide, (congrFun (fourSimplexFillB_tetrahedron_five s) 0).trans rfl,
      (congrFun (fourSimplexFillB_tetrahedron_five s) 2).trans rfl⟩

private theorem ThirdHurewicz.fourSimplexTetrahedraA_sum {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    ∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e • basedThreeSimplexClass (fourSimplexTetrahedronA τ e) =
      basedThreeSimplexClass (basedFourSimplexFace τ 3) +
        basedThreeSimplexClass (basedFourSimplexFace τ 1) := by
  have hconstant : basedThreeSimplexClass (constantBasedThreeSimplex x) = 0 := rfl
  rw [←
    Geometry.cubePermutation_bijective.sum_comp
      (fun e =>
        Geometry.cubeOrientation e • basedThreeSimplexClass (fourSimplexTetrahedronA τ e))]
  simp [hconstant, Fin.sum_univ_succ, Geometry.cubeOrientation_cubePermutation,
    fourSimplexTetrahedronA_zero, fourSimplexTetrahedronA_one, fourSimplexTetrahedronA_two,
    fourSimplexTetrahedronA_three, fourSimplexTetrahedronA_four, fourSimplexTetrahedronA_five]

private theorem ThirdHurewicz.fourSimplexTetrahedraB_sum {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    ∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e • basedThreeSimplexClass (fourSimplexTetrahedronB τ e) =
      -(basedThreeSimplexClass (basedFourSimplexFace τ 4) +
            basedThreeSimplexClass (basedFourSimplexFace τ 2) +
          basedThreeSimplexClass (basedFourSimplexFace τ 0)) := by
  have hconstant : basedThreeSimplexClass (constantBasedThreeSimplex x) = 0 := rfl
  rw [←
    Geometry.cubePermutation_bijective.sum_comp
      (fun e =>
        Geometry.cubeOrientation e • basedThreeSimplexClass (fourSimplexTetrahedronB τ e))]
  simp [hconstant, Fin.sum_univ_succ, Geometry.cubeOrientation_cubePermutation, add_assoc,
    fourSimplexTetrahedronB_zero, fourSimplexTetrahedronB_one, fourSimplexTetrahedronB_two,
    fourSimplexTetrahedronB_three, fourSimplexTetrahedronB_four, fourSimplexTetrahedronB_five,
    basedThreeSimplexSwapLast_class]
  abel

private def ThirdHurewicz.nativeDuffyCubeCanonical : C(NativeCube, NativeCube)
    where
  toFun u := ![u 0, u 0 * u 1, u 0 * u 1 * u 2]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · exact
        ((continuous_subtype_val.comp (continuous_apply 0)).mul
              (continuous_subtype_val.comp (continuous_apply 1))).subtype_mk
          _
    · exact
        (((continuous_subtype_val.comp (continuous_apply 0)).mul
                  (continuous_subtype_val.comp (continuous_apply 1))).mul
              (continuous_subtype_val.comp (continuous_apply 2))).subtype_mk
          _

private def ThirdHurewicz.nativeDuffyCube (e : Equiv.Perm (Fin 3)) : C(NativeCube, NativeCube)
    where
  toFun u i := nativeDuffyCubeCanonical u (e.symm i)
  continuous_toFun :=
    continuous_pi fun i => (continuous_apply (e.symm i)).comp nativeDuffyCubeCanonical.continuous

private theorem ThirdHurewicz.nativeDuffyCube_apply (e : Equiv.Perm (Fin 3)) (u : NativeCube)
    (i : Fin 3) : nativeDuffyCube e u i = ![u 0, u 0 * u 1, u 0 * u 1 * u 2] (e.symm i) :=
  rfl

@[simp]
private theorem
    ThirdHurewicz.nativeDuffyCube_coordinate_zero (e : Equiv.Perm (Fin 3)) (u : NativeCube) :
    nativeDuffyCube e u (e 0) = u 0 := by simp [nativeDuffyCube_apply]

@[simp]
private theorem
    ThirdHurewicz.nativeDuffyCube_coordinate_one (e : Equiv.Perm (Fin 3)) (u : NativeCube) :
    nativeDuffyCube e u (e 1) = u 0 * u 1 := by simp [nativeDuffyCube_apply]

@[simp]
private theorem
    ThirdHurewicz.nativeDuffyCube_coordinate_two (e : Equiv.Perm (Fin 3)) (u : NativeCube) :
    nativeDuffyCube e u (e 2) = u 0 * u 1 * u 2 := by simp [nativeDuffyCube_apply]

private theorem ThirdHurewicz.nativeDuffyCube_boundary (e : Equiv.Perm (Fin 3)) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    nativeDuffyCube e u ∈ Cube.boundary (Fin 3) ∨
      ∃ i j : Fin 3, i ≠ j ∧ nativeDuffyCube e u i = nativeDuffyCube e u j := by
  rcases hu with ⟨j, hj⟩
  fin_cases j
  · change u 0 = 0 ∨ u 0 = 1 at hj
    rcases hj with hj | hj
    · exact Or.inl ⟨e 0, Or.inl (by simpa using hj)⟩
    · exact Or.inl ⟨e 0, Or.inr (by simpa using hj)⟩
  · change u 1 = 0 ∨ u 1 = 1 at hj
    rcases hj with hj | hj
    · exact Or.inl ⟨e 1, Or.inl (by simp [hj])⟩
    · exact Or.inr ⟨e 0, e 1, e.injective.ne (by decide), by simp [hj]⟩
  · change u 2 = 0 ∨ u 2 = 1 at hj
    rcases hj with hj | hj
    · exact Or.inl ⟨e 2, Or.inl (by simp [hj])⟩
    · exact Or.inr ⟨e 1, e 2, e.injective.ne (by decide), by simp [hj]⟩

private theorem ThirdHurewicz.nativeDuffyCube_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3))
    (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) : p (nativeDuffyCube e u) = x := by
  rcases nativeDuffyCube_boundary e u hu with h | ⟨i, j, hij, h⟩
  · exact p.property _ h
  · exact hp _ i j hij h

private def ThirdHurewicz.nativeDuffyCubeLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) :
    GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeDuffyCube e) (nativeDuffyCube_based p hp e)

private def
    ThirdHurewicz.nativeCubePair (i j : Fin 3) : C(Fin 3 → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun u := ![u i, u j]
  continuous_toFun := by
    apply continuous_pi
    intro k
    fin_cases k <;> exact continuous_apply _

private def ThirdHurewicz.nativeCubeQuarterTurnHomotopyMap (i j : Fin 3) :
    C((unitInterval) × (Fin 3 → (unitInterval)), Fin 3 → (unitInterval))
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
private theorem ThirdHurewicz.nativeCubeQuarterTurnHomotopyMap_zero (i j : Fin 3)
    (u : Fin 3 → (unitInterval)) : nativeCubeQuarterTurnHomotopyMap i j (0, u) = u := by
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
private theorem ThirdHurewicz.nativeCubeQuarterTurnHomotopyMap_one (i j : Fin 3)
    (u : Fin 3 → (unitInterval)) :
    nativeCubeQuarterTurnHomotopyMap i j (1, u) = fun k =>
      if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k := by
  funext k
  simp [nativeCubeQuarterTurnHomotopyMap, nativeCubePair]

private theorem ThirdHurewicz.nativeCubeQuarterTurnHomotopyMap_boundary (i j : Fin 3) (hij : i ≠ j)
    (t : (unitInterval)) (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary (Fin 3) := by
  have hp (h : nativeCubePair i j u ∈ Cube.boundary (Fin 2)) :
    nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary (Fin 3) := by
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

private def ThirdHurewicz.nativeCubeQuarterTurnLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) : GenLoop (Fin 3) X x :=
  ⟨⟨fun u => p (nativeCubeQuarterTurnHomotopyMap i j (1, u)),
      p.val.continuous.comp
        ((nativeCubeQuarterTurnHomotopyMap i j).continuous.comp
          (continuous_const.prodMk continuous_id))⟩,
    fun u hu => p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij 1 u hu)⟩

@[simp]
private theorem
    ThirdHurewicz.nativeCubeQuarterTurnLoop_apply {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) (u : Fin 3 → (unitInterval)) :
    nativeCubeQuarterTurnLoop p i j hij u =
      p (fun k => if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k) := by
  change p (nativeCubeQuarterTurnHomotopyMap i j (1, u)) = _
  rw [nativeCubeQuarterTurnHomotopyMap_one]

private def ThirdHurewicz.nativeCubeQuarterTurnHomotopy {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) :
    p.val.HomotopyRel (nativeCubeQuarterTurnLoop p i j hij).val (Cube.boundary (Fin 3))
    where
  toFun z := p (nativeCubeQuarterTurnHomotopyMap i j z)
  continuous_toFun := p.val.continuous.comp (nativeCubeQuarterTurnHomotopyMap i j).continuous
  map_zero_left u := congrArg p (nativeCubeQuarterTurnHomotopyMap_zero i j u)
  map_one_left _ := rfl
  prop' t u
    hu :=
    (p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij t u hu)).trans
      (p.property u hu).symm

private theorem
    ThirdHurewicz.nativeCubeQuarterTurnLoop_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) :
    (⟦nativeCubeQuarterTurnLoop p i j hij⟧ : π_ 3 X x) = ⟦p⟧ := by
  exact
    (Quotient.sound
        (show GenLoop.Homotopic p (nativeCubeQuarterTurnLoop p i j hij) from
          ⟨nativeCubeQuarterTurnHomotopy p i j hij⟩)).symm

private theorem
    ThirdHurewicz.nativeCubeQuarterTurnLoop_additiveClass {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) :
    Additive.ofMul (⟦nativeCubeQuarterTurnLoop p i j hij⟧ : π_ 3 X x) =
      Additive.ofMul (⟦p⟧ : π_ 3 X x) :=
  congrArg Additive.ofMul (nativeCubeQuarterTurnLoop_class p i j hij)

private def ThirdHurewicz.permuteCubeCoordinates (e : Equiv.Perm (Fin 3)) :
    C(Fin 3 → (unitInterval), Fin 3 → (unitInterval))
    where
  toFun u i := u (e i)
  continuous_toFun := by fun_prop

private theorem ThirdHurewicz.permuteCubeCoordinates_boundary (e : Equiv.Perm (Fin 3))
    (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    permuteCubeCoordinates e u ∈ Cube.boundary (Fin 3) := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨e.symm i, by simpa [permuteCubeCoordinates] using hi⟩

private def ThirdHurewicz.permuteCubeLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) : GenLoop (Fin 3) X x :=
  ⟨p.val.comp (permuteCubeCoordinates e), fun u hu =>
    p.property _ (permuteCubeCoordinates_boundary e u hu)⟩

@[simp]
private theorem ThirdHurewicz.permuteCubeLoop_one {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : permuteCubeLoop p 1 = p := by
  apply GenLoop.ext
  intro u
  rfl

private theorem ThirdHurewicz.permuteCubeLoop_mul {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (e f : Equiv.Perm (Fin 3)) :
    permuteCubeLoop p (e * f) = permuteCubeLoop (permuteCubeLoop p f) e := by
  apply GenLoop.ext
  intro u
  rfl

private theorem
    ThirdHurewicz.nativeCubeQuarterTurnLoop_eq_symmAt_permute {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) :
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

private theorem ThirdHurewicz.nativeCubeClass_quarterTurn {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) :
    nativeCubeClass (nativeCubeQuarterTurnLoop p i j hij) = nativeCubeClass p :=
  nativeCubeQuarterTurnLoop_additiveClass p i j hij

private theorem
    ThirdHurewicz.permuteCubeLoop_swap_additiveClass {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) :
    nativeCubeClass (permuteCubeLoop p (Equiv.swap i j)) = -nativeCubeClass p := by
  have h := nativeCubeClass_quarterTurn p i j hij
  rw [nativeCubeQuarterTurnLoop_eq_symmAt_permute, nativeCubeClass_symmAt] at h
  simpa only [neg_neg] using congrArg Neg.neg h

private theorem ThirdHurewicz.permuteCubeLoop_additiveClass {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    nativeCubeClass (permuteCubeLoop p e) = ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeCubeClass p := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul e i j hij
    ih =>
    rw [permuteCubeLoop_mul, permuteCubeLoop_swap_additiveClass _ i j hij, ih]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]

private def ThirdHurewicz.nativeCubeCycle120 : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

private def ThirdHurewicz.nativeCubeCycle201 : Equiv.Perm (Fin 3) :=
  Equiv.swap 1 2 * Equiv.swap 0 1

@[fun_prop]
private theorem ThirdHurewicz.nativeInterval_continuous_mul {Y : Type*} [TopologicalSpace Y]
    {f g : Y → (unitInterval)} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun y => f y * g y := by
  apply Continuous.subtype_mk
  exact hf.subtype_val.mul hg.subtype_val

@[fun_prop]
private theorem ThirdHurewicz.nativeInterval_continuous_convexComb {Y : Type*} [TopologicalSpace Y]
    {f g t : Y → (unitInterval)} (hf : Continuous f) (hg : Continuous g) (ht : Continuous t) :
    Continuous fun y => Set.Icc.convexComb (f y) (g y) (t y) := by
  apply Continuous.subtype_mk
  exact
    ((continuous_const.sub ht.subtype_val).mul hf.subtype_val).add
      (ht.subtype_val.mul hg.subtype_val)

private def ThirdHurewicz.nativeLowerPrismMap : C(NativeCube, NativeCube)
    where
  toFun u := ![u 0, u 0 * u 1, u 2]
  continuous_toFun := by fun_prop

private def ThirdHurewicz.nativeUpperPrismMap : C(NativeCube, NativeCube)
    where
  toFun u := ![u 0, Set.Icc.convexComb (u 0) 1 (u 1), u 2]
  continuous_toFun := by fun_prop

private def ThirdHurewicz.nativeMiddleChamberMap : C(NativeCube, NativeCube)
    where
  toFun u := ![u 0, u 0 * u 1, u 0 * Set.Icc.convexComb (u 1) 1 (u 2)]
  continuous_toFun := by fun_prop

private def ThirdHurewicz.nativeHighChamberMap : C(NativeCube, NativeCube)
    where
  toFun u := ![u 0, u 0 * u 1, Set.Icc.convexComb (u 0) 1 (u 2)]
  continuous_toFun := by fun_prop

private def ThirdHurewicz.nativeUpperLowChamberMap : C(NativeCube, NativeCube)
    where
  toFun u := ![u 0, Set.Icc.convexComb (u 0) 1 (u 1), u 0 * u 2]
  continuous_toFun := by fun_prop

private def ThirdHurewicz.nativeUpperMiddleChamberMap : C(NativeCube, NativeCube)
    where
  toFun
    u :=
    ![u 0, Set.Icc.convexComb (u 0) 1 (u 1),
      Set.Icc.convexComb (u 0) (Set.Icc.convexComb (u 0) 1 (u 1)) (u 2)]
  continuous_toFun := by fun_prop

private def ThirdHurewicz.nativeUpperHighChamberMap : C(NativeCube, NativeCube)
    where
  toFun
    u :=
    ![u 0, Set.Icc.convexComb (u 0) 1 (u 1),
      Set.Icc.convexComb (Set.Icc.convexComb (u 0) 1 (u 1)) 1 (u 2)]
  continuous_toFun := by fun_prop

private def
    ThirdHurewicz.nativeOrderedDuffyMap (e : Equiv.Perm (Fin 3)) : C(NativeCube, NativeCube) :=
  (nativeDuffyCube e).comp (permuteCubeCoordinates e)

@[simp]
private theorem ThirdHurewicz.nativeOrderedDuffyMap_swap12 (u : NativeCube) :
    nativeOrderedDuffyMap (Equiv.swap 1 2) u = ![u 0, u 0 * u 2 * u 1, u 0 * u 2] := by
  funext i
  fin_cases i <;> rfl

@[simp]
private theorem ThirdHurewicz.nativeOrderedDuffyMap_cycle201 (u : NativeCube) :
    nativeOrderedDuffyMap nativeCubeCycle201 u = ![u 2 * u 0, u 2 * u 0 * u 1, u 2] := by
  funext i
  fin_cases i <;> rfl

@[simp]
private theorem ThirdHurewicz.nativeOrderedDuffyMap_swap01 (u : NativeCube) :
    nativeOrderedDuffyMap (Equiv.swap 0 1) u = ![u 1 * u 0, u 1, u 1 * u 0 * u 2] := by
  funext i
  fin_cases i <;> rfl

@[simp]
private theorem ThirdHurewicz.nativeOrderedDuffyMap_cycle120 (u : NativeCube) :
    nativeOrderedDuffyMap nativeCubeCycle120 u = ![u 1 * u 2 * u 0, u 1, u 1 * u 2] := by
  funext i
  fin_cases i <;> rfl

@[simp]
private theorem ThirdHurewicz.nativeOrderedDuffyMap_swap02 (u : NativeCube) :
    nativeOrderedDuffyMap (Equiv.swap 0 2) u = ![u 2 * u 1 * u 0, u 2 * u 1, u 2] := by
  funext i
  fin_cases i <;> rfl

private theorem ThirdHurewicz.nativeMiddleChamber_flats (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeMiddleChamberMap u) (nativeOrderedDuffyMap (Equiv.swap 1 2) u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .zero 1 (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .equal 1 2 (by decide) (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .one 0 (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .equal 1 2 (by decide) (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .equal 0 2 (by decide) (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])

private theorem
    ThirdHurewicz.nativeHighChamber_flats (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeHighChamberMap u) (nativeOrderedDuffyMap (nativeCubeCycle201) u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeHighChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .zero 1 (by simp [nativeHighChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .equal 0 2 (by decide) (by simp [nativeHighChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .equal 0 2 (by decide) (by simp [nativeHighChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .equal 0 1 (by decide) (by simp [nativeHighChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .one 2 (by simp [nativeHighChamberMap, hi]) (by simp [hi])

private theorem ThirdHurewicz.nativeUpperLowChamber_flats (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeUpperLowChamberMap u) (nativeOrderedDuffyMap (Equiv.swap 0 1) u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .zero 2 (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .one 1 (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .equal 0 2 (by decide) (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])

private theorem ThirdHurewicz.nativeUpperMiddleChamber_flats (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeUpperMiddleChamberMap u)
      (nativeOrderedDuffyMap nativeCubeCycle120 u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .equal 0 2 (by decide) (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .equal 0 2 (by decide) (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .one 1 (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .equal 1 2 (by decide) (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])

private theorem ThirdHurewicz.nativeUpperHighChamber_flats (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeUpperHighChamberMap u) (nativeOrderedDuffyMap (Equiv.swap 0 2) u) :=
  by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .equal 1 2 (by decide) (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .equal 1 2 (by decide) (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .one 2 (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])

private theorem
    ThirdHurewicz.nativeCubeMap_based_of_commonLeft {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) {f g : C(NativeCube, NativeCube)}
    (h : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (g u)) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) : p (f u) = x := by
  simpa only [nativeCubeBlend_zero] using nativeCubeBlend_based p hp (h u hu) 0

private theorem ThirdHurewicz.nativeDuffyCube_tetrahedron_sameFlat (e : Equiv.Perm (Fin 3))
    (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeDuffyCube e u) (nativeCubeTetrahedronQuotient e u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero (e 0) (by simp [hi]) (by simp [hi])
    · change u 1 = 0 at hi
      refine .zero (e 1) (by simp [hi]) ?_
      simp [hi]
    · change u 2 = 0 at hi
      refine .zero (e 2) (by simp [hi]) ?_
      simp [hi]
  · fin_cases i
    · change u 0 = 1 at hi
      exact .one (e 0) (by simp [hi]) (by simp [hi])
    · change u 1 = 1 at hi
      refine .equal (e 0) (e 1) (e.injective.ne (by decide)) (by simp [hi]) ?_
      simp [hi, min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)]
    · change u 2 = 1 at hi
      refine .equal (e 1) (e 2) (e.injective.ne (by decide)) (by simp [hi]) ?_
      simp [hi, min_eq_left (show u 1 ≤ (1 : (unitInterval)) from (u 1).property.2)]

private def ThirdHurewicz.nativeDuffyCubeTetrahedronHomotopy {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) :
    (nativeDuffyCubeLoop p hp e).val.HomotopyRel
      (basedThreeSimplexLoop (nativeBasedCubeTetrahedron p hp e)).val (Cube.boundary (Fin 3)) :=
  nativeCubeLinearHomotopy p hp (nativeDuffyCube e) (nativeCubeTetrahedronQuotient e)
    (nativeDuffyCube_based p hp e) (nativeCubeTetrahedronQuotient_based p hp e)
    (nativeDuffyCube_tetrahedron_sameFlat e)

private theorem ThirdHurewicz.nativeDuffyCube_homotopic_basedThreeSimplexLoop {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin 3)) :
    GenLoop.Homotopic (nativeDuffyCubeLoop p hp e)
      (basedThreeSimplexLoop (nativeBasedCubeTetrahedron p hp e)) :=
  ⟨nativeDuffyCubeTetrahedronHomotopy p hp e⟩

private theorem ThirdHurewicz.nativeDuffyCubeClass_eq_basedThreeSimplexClass {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin 3)) :
    nativeCubeClass (nativeDuffyCubeLoop p hp e) =
      basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp e) :=
  nativeCubeClass_homotopic (nativeDuffyCube_homotopic_basedThreeSimplexLoop p hp e)

private def ThirdHurewicz.nativeCubeOrderedDuffyHomotopy {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (f : C(NativeCube, NativeCube))
    (e : Equiv.Perm (Fin 3)) (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel
      (permuteCubeLoop (nativeDuffyCubeLoop p hp e) e).val (Cube.boundary (Fin 3)) :=
  nativeCubeLinearHomotopy p hp f (nativeOrderedDuffyMap e) hf
    (fun u hu => nativeDuffyCube_based p hp e _ (permuteCubeCoordinates_boundary e u hu)) hfg

private theorem
    ThirdHurewicz.nativeCubeClass_commonOrderedDuffy {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (f : C(NativeCube, NativeCube))
    (e : Equiv.Perm (Fin 3)) (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeCubeClass (nativeCubePullbackLoop p f hf) =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeCubeClass (nativeDuffyCubeLoop p hp e) :=
  (nativeCubeClass_homotopic ⟨nativeCubeOrderedDuffyHomotopy p hp f e hf hfg⟩).trans
    (permuteCubeLoop_additiveClass (nativeDuffyCubeLoop p hp e) e)

private theorem
    ThirdHurewicz.nativeCubeClass_commonOrderedTetrahedron {Y : Type} [TopologicalSpace Y]
    {y : Y} (p : GenLoop (Fin 3) Y y) (hp : NativeCubeInternalBased p)
    (f : C(NativeCube, NativeCube)) (e : Equiv.Perm (Fin 3))
    (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = y)
    (hfg : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeCubeClass (nativeCubePullbackLoop p f hf) =
      Geometry.cubeOrientation e • basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp e) := by
  simpa only [nativeDuffyCubeClass_eq_basedThreeSimplexClass, Geometry.cubeOrientation] using
    nativeCubeClass_commonOrderedDuffy p hp f e hf hfg

private theorem ThirdHurewicz.nativeLowerPrismMap_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) : p (nativeLowerPrismMap u) = x := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact p.property _ ⟨0, Or.inl (by simp [nativeLowerPrismMap, hi])⟩
    · change u 1 = 0 at hi
      exact p.property _ ⟨1, Or.inl (by simp [nativeLowerPrismMap, hi])⟩
    · change u 2 = 0 at hi
      exact p.property _ ⟨2, Or.inl (by simp [nativeLowerPrismMap, hi])⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact p.property _ ⟨0, Or.inr (by simp [nativeLowerPrismMap, hi])⟩
    · change u 1 = 1 at hi
      exact hp _ 0 1 (by decide) (by simp [nativeLowerPrismMap, hi])
    · change u 2 = 1 at hi
      exact p.property _ ⟨2, Or.inr (by simp [nativeLowerPrismMap, hi])⟩

private theorem ThirdHurewicz.nativeUpperPrismMap_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) : p (nativeUpperPrismMap u) = x := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact p.property _ ⟨0, Or.inl (by simp [nativeUpperPrismMap, hi])⟩
    · change u 1 = 0 at hi
      exact hp _ 0 1 (by decide) (by simp [nativeUpperPrismMap, hi])
    · change u 2 = 0 at hi
      exact p.property _ ⟨2, Or.inl (by simp [nativeUpperPrismMap, hi])⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact p.property _ ⟨0, Or.inr (by simp [nativeUpperPrismMap, hi])⟩
    · change u 1 = 1 at hi
      exact p.property _ ⟨1, Or.inr (by simp [nativeUpperPrismMap, hi])⟩
    · change u 2 = 1 at hi
      exact p.property _ ⟨2, Or.inr (by simp [nativeUpperPrismMap, hi])⟩

private def ThirdHurewicz.nativeLowerPrismLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeLowerPrismMap (nativeLowerPrismMap_based p hp)

private def ThirdHurewicz.nativeUpperPrismLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeUpperPrismMap (nativeUpperPrismMap_based p hp)

private def ThirdHurewicz.nativeMiddleChamberLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeMiddleChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeMiddleChamber_flats)

private def ThirdHurewicz.nativeHighChamberLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeHighChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeHighChamber_flats)

private def ThirdHurewicz.nativeUpperLowChamberLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeUpperLowChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeUpperLowChamber_flats)

private def ThirdHurewicz.nativeUpperMiddleChamberLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeUpperMiddleChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeUpperMiddleChamber_flats)

private def ThirdHurewicz.nativeUpperHighChamberLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeUpperHighChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeUpperHighChamber_flats)

private def ThirdHurewicz.nativeCubeRecoveryPermutation : Fin 6 → Equiv.Perm (Fin 3) :=
  Geometry.cubePermutation ∘ Equiv.swap 2 3

private theorem ThirdHurewicz.nativeCubeRecoveryPermutation_apply (i : Fin 6) :
    nativeCubeRecoveryPermutation i =
      ![1, Equiv.swap 1 2, nativeCubeCycle201, Equiv.swap 0 1, nativeCubeCycle120, Equiv.swap 0 2]
        i := by fin_cases i <;> rfl

private theorem ThirdHurewicz.nativeCubeRecoveryPermutation_bijective :
    Function.Bijective nativeCubeRecoveryPermutation :=
  Geometry.cubePermutation_bijective.comp (Equiv.swap 2 3).bijective

@[simp]
private theorem ThirdHurewicz.cubeOrientation_nativeCubeCycle120 :
    Geometry.cubeOrientation nativeCubeCycle120 = 1 := by
  simp [Geometry.cubeOrientation, nativeCubeCycle120, Equiv.Perm.sign_swap']

@[simp]
private theorem ThirdHurewicz.cubeOrientation_nativeCubeCycle201 :
    Geometry.cubeOrientation nativeCubeCycle201 = 1 := by
  simp [Geometry.cubeOrientation, nativeCubeCycle201, Equiv.Perm.sign_swap']

private theorem ThirdHurewicz.sum_nativeCubeRecoveryPermutations {A : Type*} [AddCommMonoid A]
    (F : Equiv.Perm (Fin 3) → A) :
    ∑ e, F e =
      F 1 + F (Equiv.swap 1 2) + F nativeCubeCycle201 + F (Equiv.swap 0 1) +
          F nativeCubeCycle120 +
        F (Equiv.swap 0 2) := by
  rw [← nativeCubeRecoveryPermutation_bijective.sum_comp F]
  simp [nativeCubeRecoveryPermutation_apply, Fin.sum_univ_succ, add_assoc]

private theorem
    ThirdHurewicz.sum_oriented_nativeCubeRecoveryPermutations {A : Type*} [AddCommGroup A]
    (F : Equiv.Perm (Fin 3) → A) :
    ∑ e, Geometry.cubeOrientation e • F e =
      F 1 - F (Equiv.swap 1 2) + F nativeCubeCycle201 - F (Equiv.swap 0 1) +
          F nativeCubeCycle120 -
        F (Equiv.swap 0 2) := by
  rw [sum_nativeCubeRecoveryPermutations]
  simp [Geometry.cubeOrientation, nativeCubeCycle120, nativeCubeCycle201, Equiv.Perm.sign_swap',
    sub_eq_add_neg]

private theorem ThirdHurewicz.nativeMiddleChamberLoop_class {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeMiddleChamberLoop p hp) =
      -basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp (Equiv.swap 1 2)) := by
  simpa [nativeMiddleChamberLoop, Geometry.cubeOrientation, Equiv.Perm.sign_swap'] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeMiddleChamberMap (Equiv.swap 1 2)
      (nativeCubeMap_based_of_commonLeft p hp nativeMiddleChamber_flats) nativeMiddleChamber_flats

private theorem ThirdHurewicz.nativeHighChamberLoop_class {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeHighChamberLoop p hp) =
      basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp nativeCubeCycle201) := by
  simpa [nativeHighChamberLoop] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeHighChamberMap nativeCubeCycle201
      (nativeCubeMap_based_of_commonLeft p hp nativeHighChamber_flats) nativeHighChamber_flats

private theorem
    ThirdHurewicz.nativeUpperLowChamberLoop_class {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeUpperLowChamberLoop p hp) =
      -basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp (Equiv.swap 0 1)) := by
  simpa [nativeUpperLowChamberLoop, Geometry.cubeOrientation, Equiv.Perm.sign_swap'] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeUpperLowChamberMap (Equiv.swap 0 1)
      (nativeCubeMap_based_of_commonLeft p hp nativeUpperLowChamber_flats)
      nativeUpperLowChamber_flats

private theorem
    ThirdHurewicz.nativeUpperMiddleChamberLoop_class {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeUpperMiddleChamberLoop p hp) =
      basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp nativeCubeCycle120) := by
  simpa [nativeUpperMiddleChamberLoop] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeUpperMiddleChamberMap nativeCubeCycle120
      (nativeCubeMap_based_of_commonLeft p hp nativeUpperMiddleChamber_flats)
      nativeUpperMiddleChamber_flats

private theorem
    ThirdHurewicz.nativeUpperHighChamberLoop_class {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeUpperHighChamberLoop p hp) =
      -basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp (Equiv.swap 0 2)) := by
  simpa [nativeUpperHighChamberLoop, Geometry.cubeOrientation, Equiv.Perm.sign_swap'] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeUpperHighChamberMap (Equiv.swap 0 2)
      (nativeCubeMap_based_of_commonLeft p hp nativeUpperHighChamber_flats)
      nativeUpperHighChamber_flats

private def ThirdHurewicz.NativeCubeCutIndependent (i : Fin 3) (a : C(NativeCube, (unitInterval))) :
    Prop :=
  ∀ u v, a (Function.update u i v) = a u

private def ThirdHurewicz.NativeCubeCutBased {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval))) : Prop :=
  ∀ u, p (Function.update u i (a u)) = x

private def ThirdHurewicz.nativeCubeCutLowerMap (i : Fin 3) (a : C(NativeCube, (unitInterval))) :
    C(NativeCube, NativeCube)
    where
  toFun u := Function.update u i (a u * u i)
  continuous_toFun :=
    continuous_id.update i
      (((continuous_subtype_val.comp a.continuous).mul
            (continuous_subtype_val.comp (continuous_apply i))).subtype_mk
        _)

private def ThirdHurewicz.nativeCubeCutMiddleMap (i : Fin 3) (a b : C(NativeCube, (unitInterval))) :
    C(NativeCube, NativeCube)
    where
  toFun u := Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))
  continuous_toFun :=
    continuous_id.update i
      (Set.Icc.continuous_convexComb_prod.comp
        (a.continuous.prodMk (b.continuous.prodMk (continuous_apply i))))

private def ThirdHurewicz.nativeCubeCutUpperMap (i : Fin 3) (b : C(NativeCube, (unitInterval))) :
    C(NativeCube, NativeCube)
    where
  toFun u := Function.update u i (Set.Icc.convexComb (b u) 1 (u i))
  continuous_toFun :=
    continuous_id.update i
      (Set.Icc.continuous_convexComb_prod.comp
        (b.continuous.prodMk (continuous_const.prodMk (continuous_apply i))))

private theorem ThirdHurewicz.nativeCubeCutLowerMap_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    p (nativeCubeCutLowerMap i a u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · exact p.property _ ⟨i, Or.inl (by simp [nativeCubeCutLowerMap, hj])⟩
    · simpa [nativeCubeCutLowerMap, hj] using ha u
  · exact p.property _ ⟨j, by simpa [nativeCubeCutLowerMap, hji] using hj⟩

private theorem ThirdHurewicz.nativeCubeCutMiddleMap_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (hb : NativeCubeCutBased p i b) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) : p (nativeCubeCutMiddleMap i a b u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · simpa [nativeCubeCutMiddleMap, hj] using ha u
    · simpa [nativeCubeCutMiddleMap, hj] using hb u
  · exact p.property _ ⟨j, by simpa [nativeCubeCutMiddleMap, hji] using hj⟩

private theorem ThirdHurewicz.nativeCubeCutUpperMap_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (b : C(NativeCube, (unitInterval)))
    (hb : NativeCubeCutBased p i b) (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    p (nativeCubeCutUpperMap i b u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · simpa [nativeCubeCutUpperMap, hj] using hb u
    · exact p.property _ ⟨i, Or.inr (by simp [nativeCubeCutUpperMap, hj])⟩
  · exact p.property _ ⟨j, by simpa [nativeCubeCutUpperMap, hji] using hj⟩

private def ThirdHurewicz.nativeCubeCutLowerLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeCubeCutLowerMap i a) (nativeCubeCutLowerMap_based p i a ha)

private def ThirdHurewicz.nativeCubeCutMiddleLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (hb : NativeCubeCutBased p i b) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeCubeCutMiddleMap i a b)
    (nativeCubeCutMiddleMap_based p i a b ha hb)

private def ThirdHurewicz.nativeCubeCutUpperLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (b : C(NativeCube, (unitInterval)))
    (hb : NativeCubeCutBased p i b) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeCubeCutUpperMap i b) (nativeCubeCutUpperMap_based p i b hb)

@[simp]
private theorem ThirdHurewicz.nativeCubeCutLowerLoop_apply {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (u : NativeCube) :
    nativeCubeCutLowerLoop p i a ha u = p (Function.update u i (a u * u i)) :=
  rfl

@[simp]
private theorem ThirdHurewicz.nativeCubeCutMiddleLoop_apply {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (hb : NativeCubeCutBased p i b) (u : NativeCube) :
    nativeCubeCutMiddleLoop p i a b ha hb u =
      p (Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))) :=
  rfl

@[simp]
private theorem ThirdHurewicz.nativeCubeCutUpperLoop_apply {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (b : C(NativeCube, (unitInterval)))
    (hb : NativeCubeCutBased p i b) (u : NativeCube) :
    nativeCubeCutUpperLoop p i b hb u =
      p (Function.update u i (Set.Icc.convexComb (b u) 1 (u i))) :=
  rfl

private def
    ThirdHurewicz.nativeCubeCutCoordinateMap (i : Fin 3) (w : C(NativeCube, (unitInterval))) :
    C(NativeCube, NativeCube)
    where
  toFun u := Function.update u i (w u)
  continuous_toFun := continuous_id.update i w.continuous

private theorem ThirdHurewicz.nativeCubeCutCoordinateMap_boundary (i : Fin 3)
    (w : C(NativeCube, (unitInterval))) (hzero : ∀ u, u i = 0 → w u = 0)
    (hone : ∀ u, u i = 1 → w u = 1) (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    nativeCubeCutCoordinateMap i w u ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · exact ⟨i, Or.inl (by simp [nativeCubeCutCoordinateMap, hzero u hj])⟩
    · exact ⟨i, Or.inr (by simp [nativeCubeCutCoordinateMap, hone u hj])⟩
  · exact ⟨j, by simpa [nativeCubeCutCoordinateMap, hji] using hj⟩

private def ThirdHurewicz.nativeCubeCutCoordinateLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (w : C(NativeCube, (unitInterval)))
    (hzero : ∀ u, u i = 0 → w u = 0) (hone : ∀ u, u i = 1 → w u = 1) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeCubeCutCoordinateMap i w)
    (fun u hu => p.property _ (nativeCubeCutCoordinateMap_boundary i w hzero hone u hu))

private def ThirdHurewicz.nativeCubeCutCoordinateHomotopy {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (w : C(NativeCube, (unitInterval)))
    (hzero : ∀ u, u i = 0 → w u = 0) (hone : ∀ u, u i = 1 → w u = 1) :
    p.val.HomotopyRel (nativeCubeCutCoordinateLoop p i w hzero hone).val (Cube.boundary (Fin 3))
    where
  toFun v := p (Function.update v.2 i (Set.Icc.convexComb (v.2 i) (w v.2) v.1))
  continuous_toFun :=
    p.val.continuous.comp
      (continuous_snd.update i
        (Set.Icc.continuous_convexComb_prod.comp
          (((continuous_apply i).comp continuous_snd).prodMk
            ((w.continuous.comp continuous_snd).prodMk continuous_fst))))
  map_zero_left u := by simp
  map_one_left
    u := by
    change
      p (Function.update u i (Set.Icc.convexComb (u i) (w u) 1)) = p (Function.update u i (w u))
    rw [Set.Icc.convexComb_one]
  prop' t u
    hu := by
    rw [p.property u hu]
    apply p.property
    rcases hu with ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      rcases hj with hj | hj
      · exact ⟨i, Or.inl (by simp [hj, hzero u hj])⟩
      · exact ⟨i, Or.inr (by simp [hj, hone u hj])⟩
    · exact ⟨j, by simpa [hji] using hj⟩

private def
    ThirdHurewicz.nativeCubeCutTwoWarpCoordinate (i : Fin 3) (a : C(NativeCube, (unitInterval))) :
    C(NativeCube, (unitInterval))
    where
  toFun u := SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate (a u, u i)
  continuous_toFun :=
    SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate.continuous.comp
      (a.continuous.prodMk (continuous_apply i))

private theorem ThirdHurewicz.nativeCubeCutTwoWarpCoordinate_zero (i : Fin 3)
    (a : C(NativeCube, (unitInterval))) (u : NativeCube) (hu : u i = 0) :
    nativeCubeCutTwoWarpCoordinate i a u = 0 := by simp [nativeCubeCutTwoWarpCoordinate, hu]

private theorem ThirdHurewicz.nativeCubeCutTwoWarpCoordinate_one (i : Fin 3)
    (a : C(NativeCube, (unitInterval))) (u : NativeCube) (hu : u i = 1) :
    nativeCubeCutTwoWarpCoordinate i a u = 1 := by simp [nativeCubeCutTwoWarpCoordinate, hu]

private def ThirdHurewicz.nativeCubeCutTwoWarpLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval))) :
    GenLoop (Fin 3) X x :=
  nativeCubeCutCoordinateLoop p i (nativeCubeCutTwoWarpCoordinate i a)
    (nativeCubeCutTwoWarpCoordinate_zero i a) (nativeCubeCutTwoWarpCoordinate_one i a)

private theorem
    ThirdHurewicz.nativeCubeCutTwoWarpLoop_eq_transAt {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (haInd : NativeCubeCutIndependent i a) :
    nativeCubeCutTwoWarpLoop p i a =
      GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha) (nativeCubeCutUpperLoop p i a ha) := by
  apply GenLoop.ext
  intro u
  change
    p
        (Function.update u i
          (SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate (a u, u i))) =
      if (u i : ℝ) ≤ 1 / 2 then
        nativeCubeCutLowerLoop p i a ha
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ))))
      else
        nativeCubeCutUpperLoop p i a ha
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) - 1)))
  split_ifs with h
  · rw [nativeCubeCutLowerLoop_apply, haInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_of_le_half (a u) (u i) h)
  · rw [nativeCubeCutUpperLoop_apply, haInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_of_half_lt (a u) (u i)
          (lt_of_not_ge h))

private theorem ThirdHurewicz.nativeCubeCutTwo_homotopic {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (haInd : NativeCubeCutIndependent i a) :
    GenLoop.Homotopic p
      (GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha) (nativeCubeCutUpperLoop p i a ha)) := by
  have h : GenLoop.Homotopic p (nativeCubeCutTwoWarpLoop p i a) :=
    ⟨nativeCubeCutCoordinateHomotopy p i (nativeCubeCutTwoWarpCoordinate i a)
        (nativeCubeCutTwoWarpCoordinate_zero i a) (nativeCubeCutTwoWarpCoordinate_one i a)⟩
  rwa [nativeCubeCutTwoWarpLoop_eq_transAt p i a ha haInd] at h

private theorem ThirdHurewicz.nativeCubeCutTwo_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (haInd : NativeCubeCutIndependent i a) :
    nativeCubeClass p =
      nativeCubeClass (nativeCubeCutLowerLoop p i a ha) +
        nativeCubeClass (nativeCubeCutUpperLoop p i a ha) :=
  (nativeCubeClass_homotopic (nativeCubeCutTwo_homotopic p i a ha haInd)).trans
    (nativeCubeClass_transAt i _ _)

private def ThirdHurewicz.subdivisionWarpThreeCoordinate :
    C(((unitInterval) × (unitInterval)) × (unitInterval), (unitInterval))
    where
  toFun
    p :=
    Set.Icc.convexComb (p.1.1 * Set.projIcc 0 1 zero_le_one (4 * (p.2 : ℝ)))
      (Set.Icc.convexComb p.1.2 1 (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1)))
      (Set.projIcc 0 1 zero_le_one (4 * (p.2 : ℝ) - 1))
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

private theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_apply (a b w : (unitInterval)) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      Set.Icc.convexComb (a * Set.projIcc 0 1 zero_le_one (4 * (w : ℝ)))
        (Set.Icc.convexComb b 1 (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1)))
        (Set.projIcc 0 1 zero_le_one (4 * (w : ℝ) - 1)) :=
  rfl

@[simp]
private theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_zero (a b : (unitInterval)) :
    subdivisionWarpThreeCoordinate ((a, b), 0) = 0 := by
  norm_num [subdivisionWarpThreeCoordinate, Set.projIcc, Set.Icc.convexComb]

@[simp]
private theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_one (a b : (unitInterval)) :
    subdivisionWarpThreeCoordinate ((a, b), 1) = 1 := by
  norm_num [subdivisionWarpThreeCoordinate, Set.projIcc, Set.Icc.convexComb]

private theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_of_le_quarter (a b w : (unitInterval))
    (hw : (w : ℝ) ≤ 1 / 4) :
    subdivisionWarpThreeCoordinate ((a, b), w) = a * Set.projIcc 0 1 zero_le_one (4 * (w : ℝ)) := by
  have hz : Set.projIcc 0 1 zero_le_one (4 * (w : ℝ) - 1) = (0 : (unitInterval)) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [subdivisionWarpThreeCoordinate_apply, hz, Set.Icc.convexComb_zero]

private theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_of_quarter_le_of_le_half
    (a b w : (unitInterval)) (hl : 1 / 4 ≤ (w : ℝ)) (hu : (w : ℝ) ≤ 1 / 2) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one (4 * (w : ℝ) - 1)) := by
  have hone : Set.projIcc 0 1 zero_le_one (4 * (w : ℝ)) = (1 : (unitInterval)) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  have hzero : Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1) = (0 : (unitInterval)) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [subdivisionWarpThreeCoordinate_apply, hone, hzero, mul_one, Set.Icc.convexComb_zero]

private theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_of_half_le (a b w : (unitInterval))
    (hw : 1 / 2 ≤ (w : ℝ)) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      Set.Icc.convexComb b 1 (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1)) := by
  have hone : Set.projIcc 0 1 zero_le_one (4 * (w : ℝ) - 1) = (1 : (unitInterval)) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  rw [subdivisionWarpThreeCoordinate_apply, hone, Set.Icc.convexComb_one]

private theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_of_half_lt (a b w : (unitInterval))
    (hw : 1 / 2 < (w : ℝ)) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      Set.Icc.convexComb b 1 (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1)) :=
  subdivisionWarpThreeCoordinate_of_half_le a b w hw.le

private theorem ThirdHurewicz.subdivisionWarpThree_clip_two_coe (w : (unitInterval))
    (hw : (w : ℝ) ≤ 1 / 2) : (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) = 2 * (w : ℝ) := by
  have hmem : 2 * (w : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [w.property.1], by linarith⟩
  exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hmem)

private theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_nested_lower (a b w : (unitInterval))
    (hw : (w : ℝ) ≤ 1 / 2) (hi : (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) ≤ 1 / 2) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      a * Set.projIcc 0 1 zero_le_one (2 * (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ)) := by
  have hc := subdivisionWarpThree_clip_two_coe w hw
  have hquarter : (w : ℝ) ≤ 1 / 4 := by rw [hc] at hi; linarith
  have he : 2 * (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) = 4 * (w : ℝ) := by rw [hc]; ring
  rw [he]
  exact subdivisionWarpThreeCoordinate_of_le_quarter a b w hquarter

private theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_nested_middle (a b w : (unitInterval))
    (hw : (w : ℝ) ≤ 1 / 2) (hi : 1 / 2 < (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ)) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      Set.Icc.convexComb a b
        (Set.projIcc 0 1 zero_le_one (2 * (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) - 1)) :=
  by
  have hc := subdivisionWarpThree_clip_two_coe w hw
  have hquarter : 1 / 4 ≤ (w : ℝ) := by rw [hc] at hi; linarith
  have he : 2 * (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) - 1 = 4 * (w : ℝ) - 1 := by
    rw [hc]; ring
  rw [he]
  exact subdivisionWarpThreeCoordinate_of_quarter_le_of_le_half a b w hquarter hw

private theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_nested_upper (a b w : (unitInterval))
    (hw : 1 / 2 < (w : ℝ)) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      Set.Icc.convexComb b 1 (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1)) :=
  subdivisionWarpThreeCoordinate_of_half_lt a b w hw

private def ThirdHurewicz.nativeCubeCutThreeWarpCoordinate (i : Fin 3)
    (a b : C(NativeCube, (unitInterval))) : C(NativeCube, (unitInterval))
    where
  toFun u := subdivisionWarpThreeCoordinate ((a u, b u), u i)
  continuous_toFun :=
    subdivisionWarpThreeCoordinate.continuous.comp
      ((a.continuous.prodMk b.continuous).prodMk (continuous_apply i))

private theorem ThirdHurewicz.nativeCubeCutThreeWarpCoordinate_zero (i : Fin 3)
    (a b : C(NativeCube, (unitInterval))) (u : NativeCube) (hu : u i = 0) :
    nativeCubeCutThreeWarpCoordinate i a b u = 0 := by simp [nativeCubeCutThreeWarpCoordinate, hu]

private theorem ThirdHurewicz.nativeCubeCutThreeWarpCoordinate_one (i : Fin 3)
    (a b : C(NativeCube, (unitInterval))) (u : NativeCube) (hu : u i = 1) :
    nativeCubeCutThreeWarpCoordinate i a b u = 1 := by simp [nativeCubeCutThreeWarpCoordinate, hu]

private def ThirdHurewicz.nativeCubeCutThreeWarpLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval))) :
    GenLoop (Fin 3) X x :=
  nativeCubeCutCoordinateLoop p i (nativeCubeCutThreeWarpCoordinate i a b)
    (nativeCubeCutThreeWarpCoordinate_zero i a b) (nativeCubeCutThreeWarpCoordinate_one i a b)

private theorem ThirdHurewicz.nativeCubeCutThreeWarpLoop_eq_transAt {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (hb : NativeCubeCutBased p i b)
    (haInd : NativeCubeCutIndependent i a) (hbInd : NativeCubeCutIndependent i b) :
    nativeCubeCutThreeWarpLoop p i a b =
      GenLoop.transAt i
        (GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha)
          (nativeCubeCutMiddleLoop p i a b ha hb))
        (nativeCubeCutUpperLoop p i b hb) := by
  apply GenLoop.ext
  intro u
  change
    p (Function.update u i (subdivisionWarpThreeCoordinate ((a u, b u), u i))) =
      if (u i : ℝ) ≤ 1 / 2 then
        (GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha)
            (nativeCubeCutMiddleLoop p i a b ha hb))
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ))))
      else
        nativeCubeCutUpperLoop p i b hb
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) - 1)))
  split_ifs with h
  · change
      p (Function.update u i (subdivisionWarpThreeCoordinate ((a u, b u), u i))) =
        if
            ((Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i : ℝ) ≤
              1 / 2 then
          nativeCubeCutLowerLoop p i a ha
            (Function.update (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i
              (Set.projIcc 0 1 zero_le_one
                (2 *
                  ((Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i : ℝ))))
        else
          nativeCubeCutMiddleLoop p i a b ha hb
            (Function.update (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i
              (Set.projIcc 0 1 zero_le_one
                (2 * ((Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i : ℝ) -
                  1)))
    simp only [Function.update_self]
    split_ifs with hi
    · simp only [nativeCubeCutLowerLoop_apply, Function.update_self, Function.update_idem]
      rw [haInd u _]
      exact
        congrArg (fun v => p (Function.update u i v))
          (subdivisionWarpThreeCoordinate_nested_lower (a u) (b u) (u i) h hi)
    · simp only [nativeCubeCutMiddleLoop_apply, Function.update_self, Function.update_idem]
      rw [haInd u _, hbInd u _]
      exact
        congrArg (fun v => p (Function.update u i v))
          (subdivisionWarpThreeCoordinate_nested_middle (a u) (b u) (u i) h (lt_of_not_ge hi))
  · rw [nativeCubeCutUpperLoop_apply, hbInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (subdivisionWarpThreeCoordinate_nested_upper (a u) (b u) (u i) (lt_of_not_ge h))

private theorem ThirdHurewicz.nativeCubeCutThree_homotopic {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (hb : NativeCubeCutBased p i b)
    (haInd : NativeCubeCutIndependent i a) (hbInd : NativeCubeCutIndependent i b) :
    GenLoop.Homotopic p
      (GenLoop.transAt i
        (GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha)
          (nativeCubeCutMiddleLoop p i a b ha hb))
        (nativeCubeCutUpperLoop p i b hb)) := by
  have h : GenLoop.Homotopic p (nativeCubeCutThreeWarpLoop p i a b) :=
    ⟨nativeCubeCutCoordinateHomotopy p i (nativeCubeCutThreeWarpCoordinate i a b)
        (nativeCubeCutThreeWarpCoordinate_zero i a b)
        (nativeCubeCutThreeWarpCoordinate_one i a b)⟩
  rwa [nativeCubeCutThreeWarpLoop_eq_transAt p i a b ha hb haInd hbInd] at h

private theorem ThirdHurewicz.nativeCubeCutThree_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (hb : NativeCubeCutBased p i b)
    (haInd : NativeCubeCutIndependent i a) (hbInd : NativeCubeCutIndependent i b) :
    nativeCubeClass p =
      nativeCubeClass (nativeCubeCutLowerLoop p i a ha) +
          nativeCubeClass (nativeCubeCutMiddleLoop p i a b ha hb) +
        nativeCubeClass (nativeCubeCutUpperLoop p i b hb) := by
  rw [nativeCubeClass_homotopic (nativeCubeCutThree_homotopic p i a b ha hb haInd hbInd),
    nativeCubeClass_transAt, nativeCubeClass_transAt]

private def ThirdHurewicz.nativePrismFirstCut : C(NativeCube, (unitInterval)) :=
  ⟨fun u => u 0, continuous_apply 0⟩

private def ThirdHurewicz.nativeLowerPrismCut : C(NativeCube, (unitInterval))
    where
  toFun u := u 0 * u 1
  continuous_toFun := by fun_prop

private def ThirdHurewicz.nativeUpperPrismCut : C(NativeCube, (unitInterval))
    where
  toFun u := Set.Icc.convexComb (u 0) 1 (u 1)
  continuous_toFun := by fun_prop

private theorem ThirdHurewicz.nativePrismFirstCut_independent (i : Fin 3) (hi : i ≠ 0) :
    NativeCubeCutIndependent i nativePrismFirstCut := by
  intro u v
  simp [nativePrismFirstCut, hi.symm]

private theorem ThirdHurewicz.nativeLowerPrismCut_independent :
    NativeCubeCutIndependent 2 nativeLowerPrismCut := by
  intro u v
  simp [nativeLowerPrismCut]

private theorem ThirdHurewicz.nativeUpperPrismCut_independent :
    NativeCubeCutIndependent 2 nativeUpperPrismCut := by
  intro u v
  simp [nativeUpperPrismCut]

public
theorem ThirdHurewicz.nativeInterval_convexComb_mul (a b t : (unitInterval)) :
    Set.Icc.convexComb (a * b) a t = a * Set.Icc.convexComb b 1 t := by
  apply Subtype.ext
  change
    (1 - (t : ℝ)) * ((a : ℝ) * (b : ℝ)) + (t : ℝ) * (a : ℝ) =
      (a : ℝ) * ((1 - (t : ℝ)) * (b : ℝ) + (t : ℝ) * 1)
  ring

private theorem ThirdHurewicz.nativePrismFirstCut_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased p 1 nativePrismFirstCut := by
  intro u
  exact hp _ 0 1 (by decide) (by simp [nativePrismFirstCut])

private theorem ThirdHurewicz.nativeLowerPrismCut_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased (nativeLowerPrismLoop p hp) 2 nativeLowerPrismCut := by
  intro u
  change p (nativeLowerPrismMap (Function.update u 2 (u 0 * u 1))) = x
  exact hp _ 1 2 (by decide) (by simp [nativeLowerPrismMap])

private theorem
    ThirdHurewicz.nativeLowerPrismFirstCut_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased (nativeLowerPrismLoop p hp) 2 nativePrismFirstCut := by
  intro u
  change p (nativeLowerPrismMap (Function.update u 2 (u 0))) = x
  exact hp _ 0 2 (by decide) (by simp [nativeLowerPrismMap])

private theorem
    ThirdHurewicz.nativeUpperPrismFirstCut_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased (nativeUpperPrismLoop p hp) 2 nativePrismFirstCut := by
  intro u
  change p (nativeUpperPrismMap (Function.update u 2 (u 0))) = x
  exact hp _ 0 2 (by decide) (by simp [nativeUpperPrismMap])

private theorem ThirdHurewicz.nativeUpperPrismCut_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased (nativeUpperPrismLoop p hp) 2 nativeUpperPrismCut := by
  intro u
  change p (nativeUpperPrismMap (Function.update u 2 (Set.Icc.convexComb (u 0) 1 (u 1)))) = x
  exact hp _ 1 2 (by decide) (by simp [nativeUpperPrismMap])

private theorem ThirdHurewicz.nativeCubeCutLowerLoop_eq_lowerPrism {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutLowerLoop p 1 nativePrismFirstCut (nativePrismFirstCut_based p hp) =
      nativeLowerPrismLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

private theorem ThirdHurewicz.nativeCubeCutUpperLoop_eq_upperPrism {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutUpperLoop p 1 nativePrismFirstCut (nativePrismFirstCut_based p hp) =
      nativeUpperPrismLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

private theorem ThirdHurewicz.nativeCubeClass_prisms {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass p =
      nativeCubeClass (nativeLowerPrismLoop p hp) + nativeCubeClass (nativeUpperPrismLoop p hp) :=
  by
  simpa only [nativeCubeCutLowerLoop_eq_lowerPrism p hp,
    nativeCubeCutUpperLoop_eq_upperPrism p hp] using
    nativeCubeCutTwo_class p 1 nativePrismFirstCut (nativePrismFirstCut_based p hp)
      (nativePrismFirstCut_independent 1 (by decide))

private theorem ThirdHurewicz.nativeLowerPrismCutLowerLoop_eq_duffy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutLowerLoop (nativeLowerPrismLoop p hp) 2 nativeLowerPrismCut
        (nativeLowerPrismCut_based p hp) =
      nativeDuffyCubeLoop p hp 1 := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

private theorem
    ThirdHurewicz.nativeLowerPrismCutMiddleLoop_eq_middle {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutMiddleLoop (nativeLowerPrismLoop p hp) 2 nativeLowerPrismCut nativePrismFirstCut
        (nativeLowerPrismCut_based p hp) (nativeLowerPrismFirstCut_based p hp) =
      nativeMiddleChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  change
    p ![u 0, u 0 * u 1, Set.Icc.convexComb (u 0 * u 1) (u 0) (u 2)] =
      p ![u 0, u 0 * u 1, u 0 * Set.Icc.convexComb (u 1) 1 (u 2)]
  rw [nativeInterval_convexComb_mul]

private theorem ThirdHurewicz.nativeLowerPrismCutUpperLoop_eq_high {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutUpperLoop (nativeLowerPrismLoop p hp) 2 nativePrismFirstCut
        (nativeLowerPrismFirstCut_based p hp) =
      nativeHighChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

private theorem ThirdHurewicz.nativeLowerPrismClass_eq {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeLowerPrismLoop p hp) =
      nativeCubeClass (nativeDuffyCubeLoop p hp 1) +
          nativeCubeClass (nativeMiddleChamberLoop p hp) +
        nativeCubeClass (nativeHighChamberLoop p hp) := by
  simpa only [nativeLowerPrismCutLowerLoop_eq_duffy, nativeLowerPrismCutMiddleLoop_eq_middle,
    nativeLowerPrismCutUpperLoop_eq_high] using
    nativeCubeCutThree_class (nativeLowerPrismLoop p hp) 2 nativeLowerPrismCut nativePrismFirstCut
      (nativeLowerPrismCut_based p hp) (nativeLowerPrismFirstCut_based p hp)
      nativeLowerPrismCut_independent (nativePrismFirstCut_independent 2 (by decide))

private theorem ThirdHurewicz.nativeUpperPrismCutLowerLoop_eq_lower {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutLowerLoop (nativeUpperPrismLoop p hp) 2 nativePrismFirstCut
        (nativeUpperPrismFirstCut_based p hp) =
      nativeUpperLowChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

private theorem
    ThirdHurewicz.nativeUpperPrismCutMiddleLoop_eq_middle {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutMiddleLoop (nativeUpperPrismLoop p hp) 2 nativePrismFirstCut nativeUpperPrismCut
        (nativeUpperPrismFirstCut_based p hp) (nativeUpperPrismCut_based p hp) =
      nativeUpperMiddleChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

private theorem ThirdHurewicz.nativeUpperPrismCutUpperLoop_eq_upper {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutUpperLoop (nativeUpperPrismLoop p hp) 2 nativeUpperPrismCut
        (nativeUpperPrismCut_based p hp) =
      nativeUpperHighChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

private theorem ThirdHurewicz.nativeUpperPrismClass_eq {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeUpperPrismLoop p hp) =
      nativeCubeClass (nativeUpperLowChamberLoop p hp) +
          nativeCubeClass (nativeUpperMiddleChamberLoop p hp) +
        nativeCubeClass (nativeUpperHighChamberLoop p hp) := by
  simpa only [nativeUpperPrismCutLowerLoop_eq_lower, nativeUpperPrismCutMiddleLoop_eq_middle,
    nativeUpperPrismCutUpperLoop_eq_upper] using
    nativeCubeCutThree_class (nativeUpperPrismLoop p hp) 2 nativePrismFirstCut nativeUpperPrismCut
      (nativeUpperPrismFirstCut_based p hp) (nativeUpperPrismCut_based p hp)
      (nativePrismFirstCut_independent 2 (by decide)) nativeUpperPrismCut_independent

private theorem
    ThirdHurewicz.nativeCubeClass_eq_sum_tetrahedra {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass p =
      ∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e • basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp e) :=
  by
  rw [sum_oriented_nativeCubeRecoveryPermutations, nativeCubeClass_prisms p hp,
    nativeLowerPrismClass_eq, nativeUpperPrismClass_eq,
    nativeDuffyCubeClass_eq_basedThreeSimplexClass, nativeMiddleChamberLoop_class,
    nativeHighChamberLoop_class, nativeUpperLowChamberLoop_class,
    nativeUpperMiddleChamberLoop_class, nativeUpperHighChamberLoop_class]
  simp only [sub_eq_add_neg, add_assoc]

private theorem ThirdHurewicz.nativeCubeSubdivision_class {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    Additive.ofMul (⟦p⟧ : π_ 3 X x) =
      ∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e • basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp e) :=
  nativeCubeClass_eq_sum_tetrahedra p hp

private theorem
    ThirdHurewicz.nativeCubeSubdivision_homotopy_class {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 3)))
    (hq : NativeCubeInternalBased q) :
    nativeCubeClass p =
      ∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e • basedThreeSimplexClass (nativeBasedCubeTetrahedron q hq e) :=
  (nativeCubeClass_homotopic ⟨H⟩).trans (nativeCubeClass_eq_sum_tetrahedra q hq)

private theorem ThirdHurewicz.fourSimplexLoopA_class {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    nativeCubeClass (fourSimplexLoopA τ) =
      basedThreeSimplexClass (basedFourSimplexFace τ 3) +
        basedThreeSimplexClass (basedFourSimplexFace τ 1) :=
  (nativeCubeSubdivision_class (fourSimplexLoopA τ) (fourSimplexLoopA_internal τ)).trans
    (fourSimplexTetrahedraA_sum τ)

private theorem ThirdHurewicz.fourSimplexLoopB_class {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    nativeCubeClass (fourSimplexLoopB τ) =
      -(basedThreeSimplexClass (basedFourSimplexFace τ 4) +
            basedThreeSimplexClass (basedFourSimplexFace τ 2) +
          basedThreeSimplexClass (basedFourSimplexFace τ 0)) :=
  (nativeCubeSubdivision_class (fourSimplexLoopB τ) (fourSimplexLoopB_internal τ)).trans
    (fourSimplexTetrahedraB_sum τ)

private theorem ThirdHurewicz.basedFourSimplex_pair_relation {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    basedThreeSimplexClass (basedFourSimplexFace τ 3) +
        basedThreeSimplexClass (basedFourSimplexFace τ 1) =
      basedThreeSimplexClass (basedFourSimplexFace τ 4) +
          basedThreeSimplexClass (basedFourSimplexFace τ 2) +
        basedThreeSimplexClass (basedFourSimplexFace τ 0) := by
  have h := fourSimplexFillings_additiveClass τ
  rw [fourSimplexLoopA_class, fourSimplexLoopB_class, neg_neg] at h
  exact h

private theorem
    ThirdHurewicz.basedFourSimplex_boundary_relation {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    basedThreeSimplexClass (basedFourSimplexFace τ 0) -
              basedThreeSimplexClass (basedFourSimplexFace τ 1) +
            basedThreeSimplexClass (basedFourSimplexFace τ 2) -
          basedThreeSimplexClass (basedFourSimplexFace τ 3) +
        basedThreeSimplexClass (basedFourSimplexFace τ 4) =
      0 := by
  calc
    _ =
        (basedThreeSimplexClass (basedFourSimplexFace τ 4) +
              basedThreeSimplexClass (basedFourSimplexFace τ 2) +
            basedThreeSimplexClass (basedFourSimplexFace τ 0)) -
          (basedThreeSimplexClass (basedFourSimplexFace τ 3) +
            basedThreeSimplexClass (basedFourSimplexFace τ 1)) := by abel
    _ = 0 := sub_eq_zero.mpr (basedFourSimplex_pair_relation τ).symm

end Mathoverflow1973

end
