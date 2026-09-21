/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph.Graph
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentL2
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentOrthogonality
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentTestWeakIdentity

/-! # Reflection Parent H1Graph -/

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

/-!
# Parent reflected `H¹` graph membership

This file proves the remaining parent-cube weak-gradient constraints for the
all-face coordinate-fold reflection.  The point is to avoid a separate
Sobolev trace/gluing theorem: parent test functions are folded back to the
original cube, the original weak derivative identity is applied to the signed
folded scalar test, and the graph constructor then recovers the parent
`H1Function` with the exact reflected representatives.
-/

private theorem memScalarL2_of_contDiff_hasCompactSupport {d : ℕ}
    (U : Set (Vec d)) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_compact : HasCompactSupport ψ) :
    MemScalarL2 U ψ := by
  simpa [MemScalarL2, volumeMeasureOn] using
    (hψ.continuous.memLp_of_hasCompactSupport hψ_compact).restrict U

private theorem memScalarL2_comp_cellFoldMap_of_contDiff_hasCompactSupport
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_compact : HasCompactSupport ψ) :
    MemScalarL2 (openCubeSet Q)
      (fun y => ψ (cubeFaceReflectionCellFoldMap Q choice y)) := by
  have hcomp_smooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y => ψ (cubeFaceReflectionCellFoldMap Q choice y)) := by
    simpa using contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hψ
  have hcomp_compact :
      HasCompactSupport
        (fun y => ψ (cubeFaceReflectionCellFoldMap Q choice y)) := by
    simpa using hasCompactSupport_comp_cubeFaceReflectionCellFoldMap
      Q choice hψ_compact
  exact memScalarL2_of_contDiff_hasCompactSupport
    (openCubeSet Q) hcomp_smooth hcomp_compact

private theorem integrable_openCubeSet_mul_deriv_comp_cellFoldMap
    {d : ℕ} {Q : TriadicCube d} {F φ : Vec d → ℝ}
    (hF : MemScalarL2 (openCubeSet Q) F)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (i : Fin d) (choice : Fin d → Fin 3) :
    MeasureTheory.Integrable
      (fun y =>
        F y *
          euclideanCoordDeriv i φ
            (cubeFaceReflectionCellFoldMap Q choice y))
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  have hD_smooth :
      ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i φ) :=
    contDiff_euclideanCoordDeriv hφ i
  have hD_compact :
      HasCompactSupport (euclideanCoordDeriv i φ) :=
    hasCompactSupport_euclideanCoordDeriv hφ_compact i
  have hD :
      MemScalarL2 (openCubeSet Q)
        (fun y =>
          euclideanCoordDeriv i φ
            (cubeFaceReflectionCellFoldMap Q choice y)) :=
    memScalarL2_comp_cellFoldMap_of_contDiff_hasCompactSupport
      Q choice hD_smooth hD_compact
  exact hF.integrable_mul hD

/-- Change variables on one reflection cell in the scalar pairing with a
parent coordinate derivative. -/
theorem setIntegral_cubeFaceReflectionCellCube_reflectedScalar_mul_deriv_eq
    {d : ℕ} {Q : TriadicCube d} {F φ : Vec d → ℝ}
    (i : Fin d) (choice : Fin d → Fin 3) :
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        cubeCoordinateFoldReflectedScalar Q F x *
          euclideanCoordDeriv i φ x ∂MeasureTheory.volume =
      ∫ y in openCubeSet Q,
        F y *
          euclideanCoordDeriv i φ
            (cubeFaceReflectionCellFoldMap Q choice y)
          ∂MeasureTheory.volume := by
  let T : Vec d → Vec d := cubeFaceReflectionCellFoldMap Q choice
  let g : Vec d → ℝ := fun y => F y * euclideanCoordDeriv i φ (T y)
  calc
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        cubeCoordinateFoldReflectedScalar Q F x *
          euclideanCoordDeriv i φ x ∂MeasureTheory.volume =
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        g (T x) ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
          intro x hx
          have hscalar :=
            cubeCoordinateFoldReflectedScalar_eq_cellFoldMap_of_mem_cellCube
              Q choice F hx
          simp [g, T, hscalar, cubeFaceReflectionCellFoldMap_involutive Q choice x]
    _ = ∫ y in openCubeSet Q, g y ∂MeasureTheory.volume := by
          simpa [g, T] using
            setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap Q choice g

/-- Scalar reflected pairing on the full reflection block, folded back to the
original cube. -/
theorem setIntegral_cubeFaceReflectionBlockSet_reflectedScalar_mul_deriv_eq_folded
    {d : ℕ} {Q : TriadicCube d} {F φ : Vec d → ℝ}
    (hF : MemScalarL2 (openCubeSet Q) F)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (i : Fin d) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x *
          euclideanCoordDeriv i φ x ∂MeasureTheory.volume =
      ∫ y in openCubeSet Q,
        F y *
          (∑ choice : Fin d → Fin 3,
            euclideanCoordDeriv i φ
              (cubeFaceReflectionCellFoldMap Q choice y))
          ∂MeasureTheory.volume := by
  classical
  let f : Vec d → ℝ := fun x =>
    cubeCoordinateFoldReflectedScalar Q F x *
      euclideanCoordDeriv i φ x
  have hfCell :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.Integrable f
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    intro choice
    let T : Vec d → Vec d := cubeFaceReflectionCellFoldMap Q choice
    let g : Vec d → ℝ := fun y => F y * euclideanCoordDeriv i φ (T y)
    have hg :
        MeasureTheory.Integrable g
          (MeasureTheory.volume.restrict (openCubeSet Q)) :=
      integrable_openCubeSet_mul_deriv_comp_cellFoldMap
        (Q := Q) (F := F) (φ := φ) hF hφ hφ_compact i choice
    have hcomp :
        MeasureTheory.Integrable (fun x => g (T x))
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) :=
      integrable_cubeFaceReflectionCellCube_comp_cellFoldMap
        (Q := Q) (choice := choice) (g := g) hg
    refine hcomp.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))]
      with x hx
    have hscalar :=
      cubeCoordinateFoldReflectedScalar_eq_cellFoldMap_of_mem_cellCube
        Q choice F hx
    simp [f, g, T, hscalar, cubeFaceReflectionCellFoldMap_involutive Q choice x]
  have hsplit :
      ∫ x in cubeFaceReflectionBlockSet Q, f x ∂MeasureTheory.volume =
        ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            f x ∂MeasureTheory.volume :=
    setIntegral_cubeFaceReflectionBlockSet_cellCube Q f hfCell
  have hsum :
      (∑ choice : Fin d → Fin 3,
          ∫ y in openCubeSet Q,
            F y *
              euclideanCoordDeriv i φ
                (cubeFaceReflectionCellFoldMap Q choice y)
              ∂MeasureTheory.volume) =
        ∫ y in openCubeSet Q,
          F y *
            (∑ choice : Fin d → Fin 3,
              euclideanCoordDeriv i φ
                (cubeFaceReflectionCellFoldMap Q choice y))
            ∂MeasureTheory.volume := by
    calc
      (∑ choice : Fin d → Fin 3,
          ∫ y in openCubeSet Q,
            F y *
              euclideanCoordDeriv i φ
                (cubeFaceReflectionCellFoldMap Q choice y)
              ∂MeasureTheory.volume) =
        ∫ y in openCubeSet Q,
          ∑ choice : Fin d → Fin 3,
            F y *
              euclideanCoordDeriv i φ
                (cubeFaceReflectionCellFoldMap Q choice y)
          ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_finsetSum]
          intro choice _hchoice
          exact
            integrable_openCubeSet_mul_deriv_comp_cellFoldMap
              (Q := Q) (F := F) (φ := φ) hF hφ hφ_compact i choice
      _ = ∫ y in openCubeSet Q,
          F y *
            (∑ choice : Fin d → Fin 3,
              euclideanCoordDeriv i φ
                (cubeFaceReflectionCellFoldMap Q choice y))
          ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet Q) ?_
          intro y _hy
          change
            (∑ choice : Fin d → Fin 3,
              F y *
                euclideanCoordDeriv i φ
                  (cubeFaceReflectionCellFoldMap Q choice y)) =
              F y *
                (∑ choice : Fin d → Fin 3,
                  euclideanCoordDeriv i φ
                    (cubeFaceReflectionCellFoldMap Q choice y))
          rw [Finset.mul_sum]
  calc
    ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x *
          euclideanCoordDeriv i φ x ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet Q, f x ∂MeasureTheory.volume := rfl
    _ = ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            f x ∂MeasureTheory.volume := hsplit
    _ = ∑ choice : Fin d → Fin 3,
          ∫ y in openCubeSet Q,
            F y *
              euclideanCoordDeriv i φ
                (cubeFaceReflectionCellFoldMap Q choice y)
              ∂MeasureTheory.volume := by
          apply Finset.sum_congr rfl
          intro choice _hchoice
          simpa [f] using
            setIntegral_cubeFaceReflectionCellCube_reflectedScalar_mul_deriv_eq
              (Q := Q) (F := F) (φ := φ) i choice
    _ = ∫ y in openCubeSet Q,
        F y *
          (∑ choice : Fin d → Fin 3,
            euclideanCoordDeriv i φ
              (cubeFaceReflectionCellFoldMap Q choice y))
          ∂MeasureTheory.volume := hsum

/-- Centered parent-cube form of the scalar reflected derivative pairing. -/
theorem setIntegral_originCube_succ_reflectedScalar_mul_deriv_eq_folded
    {d : ℕ} {m : ℤ} {F φ : Vec d → ℝ}
    (hF : MemScalarL2 (openCubeSet (originCube d m)) F)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (i : Fin d) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        cubeCoordinateFoldReflectedScalar (originCube d m) F x *
          euclideanCoordDeriv i φ x ∂MeasureTheory.volume =
      ∫ y in openCubeSet (originCube d m),
        F y *
          (∑ choice : Fin d → Fin 3,
            euclideanCoordDeriv i φ
              (cubeFaceReflectionCellFoldMap (originCube d m) choice y))
          ∂MeasureTheory.volume := by
  rw [setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
    (m := m)
    (f := fun x =>
      cubeCoordinateFoldReflectedScalar (originCube d m) F x *
        euclideanCoordDeriv i φ x)]
  exact
    setIntegral_cubeFaceReflectionBlockSet_reflectedScalar_mul_deriv_eq_folded
      (Q := originCube d m) (F := F) (φ := φ) hF hφ hφ_compact i

private theorem vecDot_smul_basisVec_left {d : ℕ}
    (i : Fin d) (a : ℝ) (v : Vec d) :
    vecDot (a • basisVec i) v = a * v i := by
  classical
  simp [vecDot, basisVec_apply]

private theorem cubeFaceReflectionCellFoldLinear_smul_basisVec {d : ℕ}
    (choice : Fin d → Fin 3) (i : Fin d) (a : ℝ) :
    cubeFaceReflectionCellFoldLinear choice (a • basisVec i) =
      (cubeFaceReflectionCellFoldSign choice i * a) • basisVec i := by
  rw [map_smul, cubeFaceReflectionCellFoldLinear_basisVec]
  by_cases h : choice i = 1 <;>
    simp [cubeFaceReflectionCellFoldSign, h, mul_comm]

/-- Folding the parent vector test `φ eᵢ` is the signed scalar fold in the
`i`th basis direction. -/
theorem cubeFaceReflectionFoldedParentVectorField_smul_basisVec
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (φ : Vec d → ℝ) (y : Vec d) :
    cubeFaceReflectionFoldedParentVectorField Q
        (fun x => φ x • basisVec i) y =
      cubeFaceReflectionFoldedParentScalarTest Q i φ y • basisVec i := by
  classical
  unfold cubeFaceReflectionFoldedParentVectorField
    cubeFaceReflectionFoldedParentScalarTest
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro choice _hchoice
  exact cubeFaceReflectionCellFoldLinear_smul_basisVec choice i
    (φ (cubeFaceReflectionCellFoldMap Q choice y))

/-- Component pairing form of the folded parent vector test `φ eᵢ`. -/
theorem vecDot_cubeFaceReflectionFoldedParentVectorField_smul_basisVec
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (φ : Vec d → ℝ)
    (G : Vec d) (y : Vec d) :
    vecDot
        (cubeFaceReflectionFoldedParentVectorField Q
          (fun x => φ x • basisVec i) y)
        G =
      cubeFaceReflectionFoldedParentScalarTest Q i φ y * G i := by
  rw [cubeFaceReflectionFoldedParentVectorField_smul_basisVec]
  exact vecDot_smul_basisVec_left i
    (cubeFaceReflectionFoldedParentScalarTest Q i φ y) G

private theorem memVectorL2_smul_basisVec_of_memScalarL2
    {d : ℕ} {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : MemScalarL2 U φ) (i : Fin d) :
    MemVectorL2 U (fun x => φ x • basisVec i) := by
  let L : ℝ →L[ℝ] Vec d := (1 : ℝ →L[ℝ] ℝ).smulRight (basisVec i)
  have hL := L.comp_memLp' hφ
  simpa [MemScalarL2, MemVectorL2, volumeMeasureOn, L, Function.comp_def,
    ContinuousLinearMap.smulRight_apply] using hL

/-- The parent vector reflected pairing in coordinate form, folded back to the
original cube against the signed folded scalar test. -/
theorem setIntegral_originCube_succ_reflectedVectorField_coord_mul_eq_folded
    {d : ℕ} {m : ℤ} {G : Vec d → Vec d} {φ : Vec d → ℝ}
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (i : Fin d) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        (cubeCoordinateFoldReflectedVectorField (originCube d m) G x) i *
          φ x ∂MeasureTheory.volume =
      ∫ y in openCubeSet (originCube d m),
        G y i *
          cubeFaceReflectionFoldedParentScalarTest (originCube d m) i φ y
          ∂MeasureTheory.volume := by
  let Q : TriadicCube d := originCube d m
  let Uparent : Set (Vec d) := openCubeSet (originCube d (m + 1))
  let g : Vec d → Vec d := fun x => φ x • basisVec i
  have hφL2 : MemScalarL2 Uparent φ :=
    memScalarL2_of_contDiff_hasCompactSupport Uparent hφ hφ_compact
  have hg : MemVectorL2 Uparent g :=
    memVectorL2_smul_basisVec_of_memScalarL2 hφL2 i
  have hpair :=
    setIntegral_originCube_succ_vecDot_field_reflectedVectorField_eq_folded
      (m := m) (g := g) (G := G) hg hG
  calc
    ∫ x in openCubeSet (originCube d (m + 1)),
        (cubeCoordinateFoldReflectedVectorField (originCube d m) G x) i *
          φ x ∂MeasureTheory.volume =
      ∫ x in openCubeSet (originCube d (m + 1)),
        vecDot (g x)
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x)
        ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (originCube d (m + 1))) ?_
          intro x _hx
          change
            (cubeCoordinateFoldReflectedVectorField (originCube d m) G x) i *
                φ x =
              vecDot (φ x • basisVec i)
                (cubeCoordinateFoldReflectedVectorField (originCube d m) G x)
          rw [vecDot_smul_basisVec_left]
          ring
    _ = ∫ y in openCubeSet (originCube d m),
        vecDot
          (cubeFaceReflectionFoldedParentVectorField (originCube d m) g y)
          (G y) ∂MeasureTheory.volume := hpair
    _ = ∫ y in openCubeSet (originCube d m),
        cubeFaceReflectionFoldedParentScalarTest (originCube d m) i φ y *
          G y i ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (originCube d m)) ?_
          intro y _hy
          exact
            vecDot_cubeFaceReflectionFoldedParentVectorField_smul_basisVec
              (originCube d m) i φ (G y) y
    _ = ∫ y in openCubeSet (originCube d m),
        G y i *
          cubeFaceReflectionFoldedParentScalarTest (originCube d m) i φ y
          ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (originCube d m)) ?_
          intro y _hy
          ring

/-- The all-face coordinate-fold reflection of an origin-cube `H¹` function
defines a point of the closed parent-cube weak-gradient graph. -/
theorem mem_h1GraphClosedSubmodule_cubeCoordinateFoldReflection_originCube
    {d : ℕ} {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m)))
    (hscalar :
      MemScalarL2 (openCubeSet (originCube d (m + 1)))
        (cubeCoordinateFoldReflectedScalar (originCube d m) u.toFun))
    (hvector :
      MemVectorL2 (openCubeSet (originCube d (m + 1)))
        (cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun y => u.grad y))) :
    (toScalarL2 hscalar, toHilbertVectorL2OfVecField hvector) ∈
      h1GraphClosedSubmodule (U := openCubeSet (originCube d (m + 1))) := by
  rw [mem_h1GraphClosedSubmodule_iff]
  intro i φ
  let Q : TriadicCube d := originCube d m
  let Uparent : Set (Vec d) := openCubeSet (originCube d (m + 1))
  let fR : Vec d → ℝ := cubeCoordinateFoldReflectedScalar Q u.toFun
  let GR : Vec d → Vec d :=
    cubeCoordinateFoldReflectedVectorField Q (fun y => u.grad y)
  have hrawScalar :
      ∫ x in Uparent,
          (toScalarL2 hscalar) x * φ.deriv i x ∂MeasureTheory.volume =
        ∫ x in Uparent,
          fR x * euclideanCoordDeriv i φ x ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [coeFn_toScalarL2 hscalar] with x hx
    rw [hx]
    simp [H1WeakTestFunction.deriv, euclideanCoordDeriv, fR, Q]
  have hrawVector :
      ∫ x in Uparent,
          (toHilbertVectorL2OfVecField hvector) x i * φ x
            ∂MeasureTheory.volume =
        ∫ x in Uparent, GR x i * φ x ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [coeFn_toHilbertVectorL2OfVecField hvector] with x hx
    rw [hx]
    simp [hilbertifyVecField, GR, Q]
  have hscalarFold :
      ∫ x in Uparent,
          fR x * euclideanCoordDeriv i φ x ∂MeasureTheory.volume =
        ∫ y in openCubeSet Q,
          u y *
            (∑ choice : Fin d → Fin 3,
              euclideanCoordDeriv i φ
                (cubeFaceReflectionCellFoldMap Q choice y))
            ∂MeasureTheory.volume := by
    simpa [Uparent, fR, Q] using
      setIntegral_originCube_succ_reflectedScalar_mul_deriv_eq_folded
        (m := m) (F := u.toFun) (φ := φ)
        (by simpa [MemScalarL2, volumeMeasureOn] using u.memL2)
        φ.smooth φ.compactSupport i
  have hvectorFold :
      ∫ x in Uparent, GR x i * φ x ∂MeasureTheory.volume =
        ∫ y in openCubeSet Q,
          u.grad y i *
            cubeFaceReflectionFoldedParentScalarTest Q i φ y
            ∂MeasureTheory.volume := by
    have hG : MemVectorL2 (openCubeSet Q) (fun y => u.grad y) := by
      simpa [MemVectorL2, volumeMeasureOn, Q] using u.grad_memVectorL2
    simpa [Uparent, GR, Q] using
      setIntegral_originCube_succ_reflectedVectorField_coord_mul_eq_folded
        (m := m) (G := fun y => u.grad y) (φ := φ)
        hG φ.smooth φ.compactSupport i
  have hweak :=
    u.integral_mul_foldedParentScalarTest_derivSum_eq_neg_integral_mul_originCube
      m i φ.smooth φ.compactSupport φ.support_subset
  calc
    h1WeakConstraintCLM
        (U := openCubeSet (originCube d (m + 1))) i φ
        (toScalarL2 hscalar, toHilbertVectorL2OfVecField hvector)
        =
      ∫ x in Uparent,
          (toScalarL2 hscalar) x * φ.deriv i x ∂MeasureTheory.volume +
        ∫ x in Uparent,
          (toHilbertVectorL2OfVecField hvector) x i * φ x
          ∂MeasureTheory.volume := by
          simpa [Uparent] using
            h1WeakConstraintCLM_apply_eq_integral
              (U := openCubeSet (originCube d (m + 1))) i φ
              (toScalarL2 hscalar, toHilbertVectorL2OfVecField hvector)
    _ =
      ∫ x in Uparent,
          fR x * euclideanCoordDeriv i φ x ∂MeasureTheory.volume +
        ∫ x in Uparent, GR x i * φ x ∂MeasureTheory.volume := by
          rw [hrawScalar, hrawVector]
    _ =
      ∫ y in openCubeSet Q,
          u y *
            (∑ choice : Fin d → Fin 3,
              euclideanCoordDeriv i φ
                (cubeFaceReflectionCellFoldMap Q choice y))
            ∂MeasureTheory.volume +
        ∫ y in openCubeSet Q,
          u.grad y i *
            cubeFaceReflectionFoldedParentScalarTest Q i φ y
            ∂MeasureTheory.volume := by
          rw [hscalarFold, hvectorFold]
    _ = 0 := by
          rw [hweak]
          ring

end

end Homogenization
