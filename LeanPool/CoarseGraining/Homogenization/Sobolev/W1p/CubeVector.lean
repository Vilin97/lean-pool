/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.WeakHessianFiniteP
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianGradientH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.H1GradientUpgrade
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.Normalized

/-!
# Vector-valued `W^{1,p}` functions on cubes

This file packages a vector field coordinatewise as genuine scalar
`W1pFunction` witnesses on an open cube.  Its Jacobian is the matrix of the
stored weak gradients.  All `L^p` statements use normalized cube measure, but
the carrier itself contains no cube-scale-dependent quantity.
-/

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

/-- A vector-valued `W^{1,p}` function on an open cube, represented by one
genuine scalar `W1pFunction` for each coordinate. -/
@[ext]
structure CubeVectorW1pFunction {d : ℕ} (Q : TriadicCube d)
    (p : FiniteLpExponent) where
  coord : Fin d → W1pFunction (openCubeSet Q) p.exponent

namespace CubeVectorW1pFunction

variable {d : ℕ} {Q : TriadicCube d} {p : FiniteLpExponent}

/-- The pointwise vector field represented by the coordinate witnesses. -/
def toField (F : CubeVectorW1pFunction Q p) : Vec d → Vec d :=
  fun x i ↦ F.coord i x

instance : CoeFun (CubeVectorW1pFunction Q p) (fun _ ↦ Vec d → Vec d) where
  coe := toField

/-- The pointwise Jacobian formed from the stored weak-gradient
representatives. -/
def jacobian (F : CubeVectorW1pFunction Q p) : Vec d → Mat d :=
  fun x i j ↦ (F.coord i).grad x j

@[simp] theorem toField_apply (F : CubeVectorW1pFunction Q p)
    (x : Vec d) (i : Fin d) :
    F.toField x i = F.coord i x :=
  rfl

@[simp] theorem coe_apply (F : CubeVectorW1pFunction Q p)
    (x : Vec d) (i : Fin d) :
    F x i = F.coord i x :=
  rfl

@[simp] theorem jacobian_apply (F : CubeVectorW1pFunction Q p)
    (x : Vec d) (i j : Fin d) :
    F.jacobian x i j = (F.coord i).grad x j :=
  rfl

@[simp] theorem jacobian_row (F : CubeVectorW1pFunction Q p)
    (x : Vec d) (i : Fin d) :
    F.jacobian x i = (F.coord i).grad x :=
  rfl

private theorem hilbertVec_memLp_normalizedCubeMeasure_of_coord
    (f : Vec d → Vec d)
    (hf : ∀ i : Fin d, MemLpOn (openCubeSet Q) p.exponent (fun x ↦ f x i)) :
    MeasureTheory.MemLp (fun x ↦ HilbertVec.ofVec (f x)) p.exponent
      (normalizedCubeMeasure Q) := by
  have hrestricted :
      MeasureTheory.MemLp (fun x ↦ HilbertVec.ofVec (f x)) p.exponent
        (cubeBoundedMeasurableDomain Q).restrictedVolume := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    simpa only [cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet,
      Function.comp_apply, HilbertVec.ofVec, PiLp.toLp_apply] using hf i
  have hnormalized :
      MeasureTheory.MemLp (fun x ↦ HilbertVec.ofVec (f x)) p.exponent
        (cubeBoundedMeasurableDomain Q).normalizedVolume :=
    ((cubeBoundedMeasurableDomain Q).memLp_normalizedVolume_iff
      p.exponent _).mpr hrestricted
  simpa only [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    using hnormalized

/-- The Hilbert realization of the represented vector field belongs to
normalized `L^p` on the cube. -/
theorem euclideanMemLp (F : CubeVectorW1pFunction Q p) :
    MeasureTheory.MemLp (fun x ↦ HilbertVec.ofVec (F.toField x)) p.exponent
      (normalizedCubeMeasure Q) := by
  exact hilbertVec_memLp_normalizedCubeMeasure_of_coord F.toField fun i ↦ by
    simpa only [toField_apply] using (F.coord i).memLp

/-- The Hilbert realization of one Jacobian row belongs to normalized `L^p`
on the cube. -/
theorem jacobianRowMemLp (F : CubeVectorW1pFunction Q p) (i : Fin d) :
    MeasureTheory.MemLp (fun x ↦ HilbertVec.ofVec (F.jacobian x i)) p.exponent
      (normalizedCubeMeasure Q) := by
  exact hilbertVec_memLp_normalizedCubeMeasure_of_coord
    (fun x ↦ F.jacobian x i) fun j ↦ by
      simpa only [jacobian_apply] using (F.coord i).gradMemLp j

/-- The Euclidean magnitude of one Jacobian row belongs to normalized `L^p`.
This is the norm-valued form of `jacobianRowMemLp`. -/
theorem jacobianRowEuclideanMemLp (F : CubeVectorW1pFunction Q p) (i : Fin d) :
    MeasureTheory.MemLp (fun x ↦ euclideanNorm (F.jacobian x i)) p.exponent
      (normalizedCubeMeasure Q) := by
  simpa only [euclideanNorm_eq_norm_ofVec] using (F.jacobianRowMemLp i).norm

/-- The Hilbert-matrix realization of the Jacobian belongs to normalized
`L^p` on the cube. -/
theorem jacobianHilbertMemLp (F : CubeVectorW1pFunction Q p) :
    MeasureTheory.MemLp (fun x ↦ HilbertMat.ofMat (F.jacobian x)) p.exponent
      (normalizedCubeMeasure Q) := by
  rw [MeasureTheory.memLp_piLp_iff]
  intro i
  simpa only [Function.comp_apply, HilbertMat.ofMat, PiLp.toLp_apply] using
    F.jacobianRowMemLp i

/-- The normalized `L^p` norm of the Jacobian is bounded by the finite sum of
the normalized `L^p` norms of its coordinate gradients. -/
theorem eLpNorm_jacobianHilbert_le_sum_grad
    (F : CubeVectorW1pFunction Q p) :
    MeasureTheory.eLpNorm (fun x ↦ HilbertMat.ofMat (F.jacobian x))
        p.exponent (normalizedCubeMeasure Q) ≤
      ∑ i : Fin d, MeasureTheory.eLpNorm
        (fun x ↦ HilbertVec.ofVec ((F.coord i).grad x))
        p.exponent (normalizedCubeMeasure Q) := by
  let row : Fin d → Vec d → HilbertVec d :=
    fun i x ↦ HilbertVec.ofVec ((F.coord i).grad x)
  let singleRow : Fin d → Vec d → HilbertMat d :=
    fun i x ↦ WithLp.toLp 2 (Pi.single i (row i x))
  have hsingleRow : ∀ i : Fin d,
      MeasureTheory.MemLp (singleRow i) p.exponent
        (normalizedCubeMeasure Q) := by
    intro i
    rw [MeasureTheory.memLp_piLp_iff]
    intro k
    by_cases hik : i = k
    · subst k
      simpa only [singleRow, row, Function.comp_apply, PiLp.toLp_apply,
        Pi.single_eq_same, jacobian_row] using F.jacobianRowMemLp i
    · have hzero : MeasureTheory.MemLp
          (fun _ : Vec d ↦ (0 : HilbertVec d)) p.exponent
          (normalizedCubeMeasure Q) :=
        MeasureTheory.MemLp.zero'
      simpa only [singleRow, Function.comp_apply, PiLp.toLp_apply,
        Pi.single_eq_of_ne (Ne.symm hik)] using hzero
  have hmatrix :
      (fun x ↦ HilbertMat.ofMat (F.jacobian x)) =
        ∑ i : Fin d, singleRow i := by
    funext x
    ext i j
    simp [singleRow, row]
  rw [hmatrix]
  calc
    MeasureTheory.eLpNorm (∑ i : Fin d, singleRow i) p.exponent
        (normalizedCubeMeasure Q) ≤
      ∑ i : Fin d, MeasureTheory.eLpNorm (singleRow i) p.exponent
        (normalizedCubeMeasure Q) := by
          exact MeasureTheory.eLpNorm_sum_le
            (fun i _ ↦ (hsingleRow i).aestronglyMeasurable) p.one_lt.le
    _ = ∑ i : Fin d, MeasureTheory.eLpNorm
        (fun x ↦ HilbertVec.ofVec ((F.coord i).grad x))
        p.exponent (normalizedCubeMeasure Q) := by
          apply Finset.sum_congr rfl
          intro i _
          apply MeasureTheory.eLpNorm_congr_norm_ae
          exact MeasureTheory.ae_of_all (normalizedCubeMeasure Q) fun x ↦ by
            simp [singleRow, row]

/-- Forget the weak-derivative witnesses and retain the represented normalized
Euclidean `L^p` vector field. -/
noncomputable def toCubeEuclideanLpField
    (F : CubeVectorW1pFunction Q p) : CubeEuclideanLpField Q p where
  toField := F.toField
  euclideanMemLp := F.euclideanMemLp

@[simp] theorem toCubeEuclideanLpField_toField
    (F : CubeVectorW1pFunction Q p) :
    F.toCubeEuclideanLpField.toField = F.toField :=
  rfl

private theorem weakHessianRowGradMemLpOn [NeZero d]
    {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (hrows : ∀ i : Fin d,
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        p.exponent (normalizedCubeMeasure Q))
    (i : Fin d) :
    GradMemLpOn (openCubeSet Q) p.exponent (H.gradCoordH1Function i).grad := by
  have hnormalized :
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        p.exponent (cubeBoundedMeasurableDomain Q).normalizedVolume := by
    simpa only [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      using hrows i
  have hrestricted :
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        p.exponent (cubeBoundedMeasurableDomain Q).restrictedVolume :=
    ((cubeBoundedMeasurableDomain Q).memLp_normalizedVolume_iff
      p.exponent _).mp hnormalized
  have hopen :
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        p.exponent (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa only [cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet]
      using hrestricted
  rw [MeasureTheory.memLp_piLp_iff] at hopen
  intro j
  simpa only [HasWeakHessianOn.gradCoordH1Function_grad_apply,
    Function.comp_apply, PiLp.toLp_apply] using hopen j

/-- Build a cube-vector `W^{1,p}` function from a weak Hessian whose rows have
normalized `L^p` membership.  The represented vector field is exactly the
stored weak gradient, and the represented Jacobian is exactly the stored weak
Hessian.  No separate `L^p` hypothesis on the gradient values is needed. -/
noncomputable def ofWeakHessian [NeZero d]
    {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (hrows : ∀ i : Fin d,
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        p.exponent (normalizedCubeMeasure Q)) :
    CubeVectorW1pFunction Q p where
  coord i := (H.gradCoordH1Function i).toW1pOfGradMemLp
    (isOpenBoundedConvexDomain_openCubeSet Q) p
    (weakHessianRowGradMemLpOn H hrows i)

@[simp] theorem ofWeakHessian_coord_toFun [NeZero d]
    {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (hrows : ∀ i : Fin d,
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        p.exponent (normalizedCubeMeasure Q))
    (i : Fin d) :
    ((ofWeakHessian H hrows).coord i).toFun = fun x ↦ u.grad x i :=
  rfl

@[simp] theorem ofWeakHessian_coord_grad [NeZero d]
    {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (hrows : ∀ i : Fin d,
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        p.exponent (normalizedCubeMeasure Q))
    (i : Fin d) :
    ((ofWeakHessian H hrows).coord i).grad = fun x j ↦ H.hess i j x :=
  rfl

@[simp] theorem ofWeakHessian_toField [NeZero d]
    {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (hrows : ∀ i : Fin d,
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        p.exponent (normalizedCubeMeasure Q)) :
    (ofWeakHessian H hrows).toField = u.grad := by
  funext x i
  rfl

@[simp] theorem ofWeakHessian_jacobian [NeZero d]
    {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (hrows : ∀ i : Fin d,
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        p.exponent (normalizedCubeMeasure Q)) :
    (ofWeakHessian H hrows).jacobian = fun x i j ↦ H.hess i j x := by
  funext x i j
  rfl

/-- For the weak-Hessian constructor, the generic Jacobian membership theorem
reduces to the existing finite-`p` weak-Hessian aggregation theorem without
changing representatives. -/
theorem ofWeakHessian_jacobianHilbertMemLp [NeZero d]
    {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (hrows : ∀ i : Fin d,
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        p.exponent (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp
      (fun x ↦ HilbertMat.ofMat ((ofWeakHessian H hrows).jacobian x))
      p.exponent (normalizedCubeMeasure Q) := by
  simpa only [ofWeakHessian_jacobian] using
    H.hessianHilbertMat_memLp_normalizedCubeMeasure_of_rows Q p hrows

/-- For the weak-Hessian constructor, the generic Jacobian row-sum bound is
exactly the existing finite-`p` weak-Hessian estimate. -/
theorem ofWeakHessian_eLpNorm_jacobianHilbert_le_sum_rows [NeZero d]
    {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (hrows : ∀ i : Fin d,
      MeasureTheory.MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        p.exponent (normalizedCubeMeasure Q)) :
    MeasureTheory.eLpNorm
        (fun x ↦ HilbertMat.ofMat ((ofWeakHessian H hrows).jacobian x))
        p.exponent (normalizedCubeMeasure Q) ≤
      ∑ i : Fin d, MeasureTheory.eLpNorm
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        p.exponent (normalizedCubeMeasure Q) := by
  simpa only [ofWeakHessian_jacobian] using
    H.eLpNorm_hessianHilbertMat_normalizedCubeMeasure_le_sum_rows Q p hrows

end CubeVectorW1pFunction

end

end Homogenization
