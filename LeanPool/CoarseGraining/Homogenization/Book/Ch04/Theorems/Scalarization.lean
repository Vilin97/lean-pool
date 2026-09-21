/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ScalarizationDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CoarseObservables
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.AdjointSymmetry.BasicAdjoint
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeOpenBridge

/-! # Scalarization -/

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Scalarization from isotropy

This file turns the structural symmetries of the law into the primitive
scalarization data used by the scalarized Chapter 4 moment surface.
-/

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

private theorem swap_mul_mul_swap_apply {d : ℕ} (i j r c : Fin d) (A : Mat d) :
    (Matrix.swap ℝ i j * A * Matrix.swap ℝ i j) r c =
      A (Equiv.swap i j r) (Equiv.swap i j c) := by
  by_cases hr_i : r = i
  · subst r
    by_cases hc_i : c = i
    · subst c
      simp
    · by_cases hc_j : c = j
      · subst c
        simp
      · simp [Matrix.mul_swap_of_ne hc_i hc_j, Equiv.swap_apply_of_ne_of_ne hc_i hc_j]
  · by_cases hr_j : r = j
    · subst r
      by_cases hc_i : c = i
      · subst c
        simp
      · by_cases hc_j : c = j
        · subst c
          simp
        · simp [Matrix.mul_swap_of_ne hc_i hc_j, Equiv.swap_apply_of_ne_of_ne hc_i hc_j]
    · by_cases hc_i : c = i
      · subst c
        simp [Matrix.swap_mul_of_ne hr_i hr_j, Equiv.swap_apply_of_ne_of_ne hr_i hr_j]
      · by_cases hc_j : c = j
        · subst c
          simp [Matrix.swap_mul_of_ne hr_i hr_j, Equiv.swap_apply_of_ne_of_ne hr_i hr_j]
        · simp [Matrix.swap_mul_of_ne hr_i hr_j, Matrix.mul_swap_of_ne hc_i hc_j,
            Equiv.swap_apply_of_ne_of_ne hr_i hr_j, Equiv.swap_apply_of_ne_of_ne hc_i hc_j]

private theorem rotateReg_toFun {d : ℕ} (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (a : RegCoeffField d) :
    (rotateReg R hR a).toFun = rotateCoeffField R a.toFun := rfl

private theorem adjointReg_toFun {d : ℕ} (a : RegCoeffField d) :
    (adjointReg a).toFun = adjointCoeffField a.toFun := rfl

private theorem coarseBlockMatrix_lowerRight_signFlip_cubeSet_originCube_of_exists
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i : Fin d) :
    (coarseBlockMatrix (cubeSet (originCube d n))
        (rotateCoeffField (signFlipMatrix i) a)).lowerRight =
      signFlipMatrix i *
        (coarseBlockMatrix (cubeSet (originCube d n)) a).lowerRight *
          signFlipMatrix i := by
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet,
    coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  exact coarseBlockMatrix_lowerRight_signFlip_openCubeSet_originCube_of_exists
    (n := n) (a := a) hex i

private theorem coarseBlockMatrix_lowerRight_swap_cubeSet_originCube_of_exists
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i j : Fin d) :
    (coarseBlockMatrix (cubeSet (originCube d n))
        (rotateCoeffField (Matrix.swap ℝ i j) a)).lowerRight =
      Matrix.swap ℝ i j *
        (coarseBlockMatrix (cubeSet (originCube d n)) a).lowerRight *
          Matrix.swap ℝ i j := by
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet,
    coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  exact coarseBlockMatrix_lowerRight_swap_openCubeSet_originCube_of_exists
    (n := n) (a := a) hex i j

private theorem coarseBlockMatrix_upperLeft_signFlip_cubeSet_originCube_of_exists
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i : Fin d) :
    (coarseBlockMatrix (cubeSet (originCube d n))
        (rotateCoeffField (signFlipMatrix i) a)).upperLeft =
      signFlipMatrix i *
        (coarseBlockMatrix (cubeSet (originCube d n)) a).upperLeft *
          signFlipMatrix i := by
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet,
    coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  exact coarseBlockMatrix_upperLeft_signFlip_openCubeSet_originCube_of_exists
    (n := n) (a := a) hex i

private theorem coarseBlockMatrix_upperLeft_swap_cubeSet_originCube_of_exists
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i j : Fin d) :
    (coarseBlockMatrix (cubeSet (originCube d n))
        (rotateCoeffField (Matrix.swap ℝ i j) a)).upperLeft =
      Matrix.swap ℝ i j *
        (coarseBlockMatrix (cubeSet (originCube d n)) a).upperLeft *
          Matrix.swap ℝ i j := by
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet,
    coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  exact coarseBlockMatrix_upperLeft_swap_openCubeSet_originCube_of_exists
    (n := n) (a := a) hex i j

private theorem coarseBlockMatrix_neg_lowerLeft_adjoint_cubeSet_originCube_of_exists
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar) :
    -((coarseBlockMatrix (cubeSet (originCube d n))
        (adjointCoeffField a)).lowerLeft) =
      -(-((coarseBlockMatrix (cubeSet (originCube d n)) a).lowerLeft)) := by
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet,
    coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  exact congrArg Neg.neg
    (coarseBlockMatrix_lowerLeft_adjointCoeffField_of_exists
      (U := openCubeSet (originCube d n)) (a := a) hex)

/-- **Hoisted invariance core (sign flip).**  The block observable is an
opaque function variable `F`; keeping the heavy `coarseBlockMatrix _ a.toFun`
term out of this proof avoids the `isDefEq` blow-up that the concrete
integrand triggers.  See the paper (Armstrong–Kuusi–Loher, to appear). -/
private theorem matrix_signFlip_conj_integral_eq {d : ℕ} [NeZero d]
    {P : RestrictionCoeffLaw d} (hIso : RestrictionIsotropicLaw P) (i : Fin d)
    (F : RegCoeffField d → Mat d)
    (hmeas : ∀ r c : Fin d, AEStronglyMeasurable (fun a => F a r c) P)
    (hcov : ∀ᵐ a ∂P,
      F (rotateReg (signFlipMatrix i) (isSignedPermutationMatrix_signFlipMatrix i) a) =
        signFlipMatrix i * F a * signFlipMatrix i) :
    signFlipMatrix i * (Matrix.of fun r c => ∫ a, F a r c ∂P) * signFlipMatrix i =
      Matrix.of fun r c => ∫ a, F a r c ∂P := by
  ext r c
  set s : ℝ := (if r = i then (-1 : ℝ) else 1) * (if c = i then (-1 : ℝ) else 1) with hs
  calc
    (signFlipMatrix i * (Matrix.of fun r c => ∫ a, F a r c ∂P) * signFlipMatrix i) r c
        = s * ∫ a, F a r c ∂P := by
          rw [signFlipMatrix_mul_mul_signFlipMatrix_apply, Matrix.of_apply, hs]; ring
    _ = ∫ a, s * F a r c ∂P := (MeasureTheory.integral_const_mul s _).symm
    _ = ∫ a, F (rotateReg (signFlipMatrix i)
          (isSignedPermutationMatrix_signFlipMatrix i) a) r c ∂P := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hcov] with a ha
          have hentry : F (rotateReg (signFlipMatrix i)
              (isSignedPermutationMatrix_signFlipMatrix i) a) r c =
              (signFlipMatrix i * F a * signFlipMatrix i) r c :=
            congrArg (fun M => M r c) ha
          rw [signFlipMatrix_mul_mul_signFlipMatrix_apply] at hentry
          rw [hentry, hs]; ring
    _ = ∫ a, F a r c ∂P :=
          hIso.integral_comp_rotateReg (isSignedPermutationMatrix_signFlipMatrix i)
            (fun a => F a r c) (hmeas r c)
    _ = (Matrix.of fun r c => ∫ a, F a r c ∂P) r c := (Matrix.of_apply (fun r c => ∫ a, F a r c ∂P) r c).symm

/-- **Hoisted invariance core (swap).**  Opaque block observable `F`, as in
`matrix_signFlip_conj_integral_eq`. -/
private theorem matrix_swap_conj_integral_eq {d : ℕ} [NeZero d]
    {P : RestrictionCoeffLaw d} (hIso : RestrictionIsotropicLaw P) (i j : Fin d)
    (F : RegCoeffField d → Mat d)
    (hmeas : ∀ r c : Fin d, AEStronglyMeasurable (fun a => F a r c) P)
    (hcov : ∀ᵐ a ∂P,
      F (rotateReg (Matrix.swap ℝ i j) (isSignedPermutationMatrix_swap i j) a) =
        Matrix.swap ℝ i j * F a * Matrix.swap ℝ i j) :
    Matrix.swap ℝ i j * (Matrix.of fun r c => ∫ a, F a r c ∂P) * Matrix.swap ℝ i j =
      Matrix.of fun r c => ∫ a, F a r c ∂P := by
  ext r c
  calc
    (Matrix.swap ℝ i j * (Matrix.of fun r c => ∫ a, F a r c ∂P) * Matrix.swap ℝ i j) r c
        = ∫ a, F a (Equiv.swap i j r) (Equiv.swap i j c) ∂P := by
          rw [swap_mul_mul_swap_apply, Matrix.of_apply]
    _ = ∫ a, F (rotateReg (Matrix.swap ℝ i j)
          (isSignedPermutationMatrix_swap i j) a) r c ∂P := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hcov] with a ha
          have hentry : F (rotateReg (Matrix.swap ℝ i j)
              (isSignedPermutationMatrix_swap i j) a) r c =
              (Matrix.swap ℝ i j * F a * Matrix.swap ℝ i j) r c :=
            congrArg (fun M => M r c) ha
          rw [swap_mul_mul_swap_apply] at hentry
          rw [hentry]
    _ = ∫ a, F a r c ∂P :=
          hIso.integral_comp_rotateReg (isSignedPermutationMatrix_swap i j)
            (fun a => F a r c) (hmeas r c)
    _ = (Matrix.of fun r c => ∫ a, F a r c ∂P) r c := (Matrix.of_apply (fun r c => ∫ a, F a r c ∂P) r c).symm

/-- **Hoisted vanishing core (adjoint).**  Opaque block observable `G`. -/
private theorem matrix_adjoint_neg_integral_eq_zero {d : ℕ} [NeZero d]
    {P : RestrictionCoeffLaw d} (hAdj : RestrictionAdjointInvariantLaw P)
    (G : RegCoeffField d → Mat d)
    (hmeas : ∀ r c : Fin d, AEStronglyMeasurable (fun a => G a r c) P)
    (hcov : ∀ᵐ a ∂P, G (adjointReg a) = -G a) :
    (Matrix.of fun r c => ∫ a, G a r c ∂P) = 0 := by
  ext r c
  simp only [Matrix.of_apply, Matrix.zero_apply]
  have hcomp : ∫ a, G (adjointReg a) r c ∂P = ∫ a, G a r c ∂P :=
    hAdj.integral_comp_adjointReg (fun a => G a r c) (hmeas r c)
  have hEq : (∫ a, G a r c ∂P) = -(∫ a, G a r c ∂P) := by
    calc
      (∫ a, G a r c ∂P) = ∫ a, G (adjointReg a) r c ∂P := hcomp.symm
      _ = ∫ a, -(G a r c) ∂P := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hcov] with a ha
            have hentry : G (adjointReg a) r c = (-G a) r c := congrArg (fun M => M r c) ha
            rw [hentry, Matrix.neg_apply]
      _ = -(∫ a, G a r c ∂P) := MeasureTheory.integral_neg _
  linarith

private theorem annealedSigmaStarInvAtScale_isSignFlipInvariant_of_covariant_ae
    {d : ℕ} [NeZero d] (P : RestrictionCoeffLaw d) (n : ℤ)
    (hIso : RestrictionIsotropicLaw P)
    (hmeas : ∀ r c : Fin d,
      AEStronglyMeasurable
        (fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).lowerRight r c) P)
    (hcov : ∀ i : Fin d, ∀ᵐ a ∂P,
      (coarseBlockMatrix (cubeSet (originCube d n))
          (rotateCoeffField (signFlipMatrix i) a.toFun)).lowerRight =
        signFlipMatrix i *
          (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).lowerRight *
            signFlipMatrix i) :
    IsSignFlipInvariant (annealedSigmaStarInvAtScale P n) := by
  intro i
  have hform : annealedSigmaStarInvAtScale P n =
      Matrix.of fun r c =>
        ∫ a, (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).lowerRight r c ∂P := by
    ext r c
    simp only [annealedSigmaStarInvAtScale, annealedSigmaStarInv_apply, Matrix.of_apply]
  rw [hform]
  exact matrix_signFlip_conj_integral_eq hIso i
    (fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).lowerRight) hmeas (hcov i)

private theorem annealedSigmaStarInvAtScale_isSwapInvariant_of_covariant_ae
    {d : ℕ} [NeZero d] (P : RestrictionCoeffLaw d) (n : ℤ)
    (hIso : RestrictionIsotropicLaw P)
    (hmeas : ∀ r c : Fin d,
      AEStronglyMeasurable
        (fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).lowerRight r c) P)
    (hcov : ∀ i j : Fin d, ∀ᵐ a ∂P,
      (coarseBlockMatrix (cubeSet (originCube d n))
          (rotateCoeffField (Matrix.swap ℝ i j) a.toFun)).lowerRight =
        Matrix.swap ℝ i j *
          (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).lowerRight *
            Matrix.swap ℝ i j) :
    IsSwapInvariant (annealedSigmaStarInvAtScale P n) := by
  intro i j
  have hform : annealedSigmaStarInvAtScale P n =
      Matrix.of fun r c =>
        ∫ a, (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).lowerRight r c ∂P := by
    ext r c
    simp only [annealedSigmaStarInvAtScale, annealedSigmaStarInv_apply, Matrix.of_apply]
  rw [hform]
  exact matrix_swap_conj_integral_eq hIso i j
    (fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).lowerRight) hmeas (hcov i j)

private theorem annealedBAtScale_isSignFlipInvariant_of_covariant_ae
    {d : ℕ} [NeZero d] (P : RestrictionCoeffLaw d) (n : ℤ)
    (hIso : RestrictionIsotropicLaw P)
    (hmeas : ∀ r c : Fin d,
      AEStronglyMeasurable
        (fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).upperLeft r c) P)
    (hcov : ∀ i : Fin d, ∀ᵐ a ∂P,
      (coarseBlockMatrix (cubeSet (originCube d n))
          (rotateCoeffField (signFlipMatrix i) a.toFun)).upperLeft =
        signFlipMatrix i *
          (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).upperLeft *
            signFlipMatrix i) :
    IsSignFlipInvariant (annealedBAtScale P n) := by
  intro i
  have hform : annealedBAtScale P n =
      Matrix.of fun r c =>
        ∫ a, (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).upperLeft r c ∂P := by
    ext r c
    simp only [annealedBAtScale, annealedB_apply, Matrix.of_apply]
  rw [hform]
  exact matrix_signFlip_conj_integral_eq hIso i
    (fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).upperLeft) hmeas (hcov i)

private theorem annealedBAtScale_isSwapInvariant_of_covariant_ae
    {d : ℕ} [NeZero d] (P : RestrictionCoeffLaw d) (n : ℤ)
    (hIso : RestrictionIsotropicLaw P)
    (hmeas : ∀ r c : Fin d,
      AEStronglyMeasurable
        (fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).upperLeft r c) P)
    (hcov : ∀ i j : Fin d, ∀ᵐ a ∂P,
      (coarseBlockMatrix (cubeSet (originCube d n))
          (rotateCoeffField (Matrix.swap ℝ i j) a.toFun)).upperLeft =
        Matrix.swap ℝ i j *
          (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).upperLeft *
            Matrix.swap ℝ i j) :
    IsSwapInvariant (annealedBAtScale P n) := by
  intro i j
  have hform : annealedBAtScale P n =
      Matrix.of fun r c =>
        ∫ a, (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).upperLeft r c ∂P := by
    ext r c
    simp only [annealedBAtScale, annealedB_apply, Matrix.of_apply]
  rw [hform]
  exact matrix_swap_conj_integral_eq hIso i j
    (fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).upperLeft) hmeas (hcov i j)

private theorem annealedSigmaStarInvKappaMeanAtScale_eq_zero_of_adjoint_covariant_ae
    {d : ℕ} [NeZero d] (P : RestrictionCoeffLaw d) (n : ℤ)
    (hAdj : RestrictionAdjointInvariantLaw P)
    (hmeas : ∀ r c : Fin d,
      AEStronglyMeasurable
        (fun a => -((coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).lowerLeft r c)) P)
    (hcov : ∀ᵐ a ∂P,
      -((coarseBlockMatrix (cubeSet (originCube d n))
          (adjointCoeffField a.toFun)).lowerLeft) =
        -(-((coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).lowerLeft))) :
    annealedSigmaStarInvKappaMeanAtScale P n = 0 := by
  have hform : annealedSigmaStarInvKappaMeanAtScale P n =
      Matrix.of fun r c =>
        ∫ a, (-(((coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).lowerLeft))) r c ∂P := by
    ext r c
    simp only [annealedSigmaStarInvKappaMeanAtScale, annealedSigmaStarInvKappaMean_apply,
      Matrix.of_apply, Matrix.neg_apply]
    rw [MeasureTheory.integral_neg]
  rw [hform]
  exact matrix_adjoint_neg_integral_eq_zero hAdj
    (fun a => -((coarseBlockMatrix (cubeSet (originCube d n)) a.toFun).lowerLeft)) hmeas hcov

/--
Isotropy and adjoint invariance scalarize the primitive annealed blocks at a
fixed scale.  The a.s. deterministic coarse-block existence needed by the
covariance identities is supplied by `RestrictionLawCarrier`.
-/
theorem Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hIso : RestrictionIsotropicLaw P) (hAdj : RestrictionAdjointInvariantLaw P) (n : ℤ) :
    Internal.AnnealedPrimitiveScalarizationData (d := d) P n :=
  let hex := hP.ae_exists_coarseBlockMatrix_openCubeSet_originCube n
  {
  sigmaStarInvFlip :=
    annealedSigmaStarInvAtScale_isSignFlipInvariant_of_covariant_ae P n hIso
      (fun r c =>
        (hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
          (originCube d n) r c).aestronglyMeasurable)
      (fun i => by
        filter_upwards [hex] with a ha
        exact coarseBlockMatrix_lowerRight_signFlip_cubeSet_originCube_of_exists
          (n := n) (a := a.toFun) ha i)
  sigmaStarInvSwap :=
    annealedSigmaStarInvAtScale_isSwapInvariant_of_covariant_ae P n hIso
      (fun r c =>
        (hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
          (originCube d n) r c).aestronglyMeasurable)
      (fun i j => by
        filter_upwards [hex] with a ha
        exact coarseBlockMatrix_lowerRight_swap_cubeSet_originCube_of_exists
          (n := n) (a := a.toFun) ha i j)
  bFlip :=
    annealedBAtScale_isSignFlipInvariant_of_covariant_ae P n hIso
      (fun r c =>
        (hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
          (originCube d n) r c).aestronglyMeasurable)
      (fun i => by
        filter_upwards [hex] with a ha
        exact coarseBlockMatrix_upperLeft_signFlip_cubeSet_originCube_of_exists
          (n := n) (a := a.toFun) ha i)
  bSwap :=
    annealedBAtScale_isSwapInvariant_of_covariant_ae P n hIso
      (fun r c =>
        (hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
          (originCube d n) r c).aestronglyMeasurable)
      (fun i j => by
        filter_upwards [hex] with a ha
        exact coarseBlockMatrix_upperLeft_swap_cubeSet_originCube_of_exists
          (n := n) (a := a.toFun) ha i j)
  sigmaStarInvKappaMean_eq_zero :=
    annealedSigmaStarInvKappaMeanAtScale_eq_zero_of_adjoint_covariant_ae P n hAdj
      (fun r c =>
        ((hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet
          (originCube d n) r c).neg).aestronglyMeasurable)
      (by
        filter_upwards [hex] with a ha
        exact coarseBlockMatrix_neg_lowerLeft_adjoint_cubeSet_originCube_of_exists
          (n := n) (a := a.toFun) ha) }

/-- Structural-law version of
`Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint`. -/
theorem Internal.annealedPrimitiveScalarizationData_of_structuralLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) :
    Internal.AnnealedPrimitiveScalarizationData (d := d) P n :=
  Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint hP
    hStruct.isotropic hStruct.adjoint_invariant n

/-- Isotropy and adjoint invariance give scalarization at a fixed scale. -/
theorem Internal.hasAnnealedScalarizationAtScale_of_isotropic_adjoint
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hIso : RestrictionIsotropicLaw P) (hAdj : RestrictionAdjointInvariantLaw P) (n : ℤ) :
    Internal.HasAnnealedScalarizationAtScale P n :=
  Internal.AnnealedScalarizationPrimitiveData.hasAnnealedScalarizationAtScale
    (Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint hP hIso hAdj n)

/-- Structural-law version of scalarization at a fixed scale. -/
theorem Internal.hasAnnealedScalarizationAtScale_of_structuralLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) :
    Internal.HasAnnealedScalarizationAtScale P n :=
  Internal.AnnealedScalarizationPrimitiveData.hasAnnealedScalarizationAtScale
    (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n)

/-- Isotropy and adjoint invariance give scalarization at every scale. -/
theorem Internal.annealedScalarizationTheory_of_isotropic_adjoint
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hIso : RestrictionIsotropicLaw P) (hAdj : RestrictionAdjointInvariantLaw P) :
    Internal.AnnealedScalarizationTheory P where
  scalarized n :=
    Internal.hasAnnealedScalarizationAtScale_of_isotropic_adjoint hP hIso hAdj n

/-- Structural-law version of scalarization at every scale. -/
theorem Internal.annealedScalarizationTheory_of_structuralLaw
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) :
    Internal.AnnealedScalarizationTheory P :=
  Internal.annealedScalarizationTheory_of_isotropic_adjoint hP
    hStruct.isotropic hStruct.adjoint_invariant

/-- Structural-law scalar `\bar\sigma_n`. -/
noncomputable def RestrictionLawCarrier.barSigmaAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) : ℝ :=
  (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct).barSigma n

/-- Structural-law scalar `\bar\sigma_{*,n}`. -/
noncomputable def RestrictionLawCarrier.barSigmaStarAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) : ℝ :=
  (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct).barSigmaStar n

/-- Structural-law scalar upper-left coefficient `\bar b_n`. -/
noncomputable def RestrictionLawCarrier.barBAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) : ℝ :=
  (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n).barB

/-- Structural-law scalar inverse-star coefficient `\bar\sigma_{*,n}^{-1}`. -/
noncomputable def RestrictionLawCarrier.barSigmaStarInvAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) : ℝ :=
  (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n).barSigmaStarInv

/-- Structural-law contrast `\Theta_n = \bar\sigma_n \bar\sigma_{*,n}^{-1}`. -/
noncomputable def RestrictionLawCarrier.thetaAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) : ℝ :=
  hP.barSigmaAtScale hStruct n * (hP.barSigmaStarAtScale hStruct n)⁻¹

/-- The structural-law scalar `\bar\sigma_n` scalarizes the annealed matrix. -/
theorem RestrictionLawCarrier.annealedSigmaAtScale_eq_barSigmaAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) :
    annealedSigmaAtScale P n = hP.barSigmaAtScale hStruct n • (1 : Mat d) := by
  simpa [RestrictionLawCarrier.barSigmaAtScale] using
    (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct).annealedSigma_eq n

/-- The structural-law scalar `\bar\sigma_{*,n}` scalarizes the annealed
starred matrix. -/
theorem RestrictionLawCarrier.annealedSigmaStarAtScale_eq_barSigmaStarAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) :
    annealedSigmaStarAtScale P n =
      hP.barSigmaStarAtScale hStruct n • (1 : Mat d) := by
  simpa [RestrictionLawCarrier.barSigmaStarAtScale] using
    (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct).annealedSigmaStar_eq n

/-- The structural-law scalar `\bar b_n` scalarizes the annealed upper-left
block. -/
theorem RestrictionLawCarrier.annealedBAtScale_eq_barBAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) :
    annealedBAtScale P n = hP.barBAtScale hStruct n • (1 : Mat d) := by
  simpa [RestrictionLawCarrier.barBAtScale] using
    (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n).b_eq

/-- The structural-law scalar `\bar\sigma_{*,n}^{-1}` scalarizes the annealed
inverse-star matrix. -/
theorem RestrictionLawCarrier.annealedSigmaStarInvAtScale_eq_barSigmaStarInvAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) :
    annealedSigmaStarInvAtScale P n =
      hP.barSigmaStarInvAtScale hStruct n • (1 : Mat d) := by
  simpa [RestrictionLawCarrier.barSigmaStarInvAtScale] using
    (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n).sigmaStarInv_eq

/-- Under the structural law, the scalarized conductivity agrees with the
primitive upper-left scalar. -/
theorem RestrictionLawCarrier.barSigmaAtScale_eq_barBAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) :
    hP.barSigmaAtScale hStruct n = hP.barBAtScale hStruct n := by
  simpa [RestrictionLawCarrier.barSigmaAtScale, RestrictionLawCarrier.barBAtScale] using
    Internal.AnnealedPrimitiveScalarizationData.barSigma_eq_barB
      (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct)
      (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n)

/-- Under the structural law, `\bar\sigma_{*,n}` is the inverse of the primitive
inverse-star scalar. -/
theorem RestrictionLawCarrier.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) :
    hP.barSigmaStarAtScale hStruct n =
      (hP.barSigmaStarInvAtScale hStruct n)⁻¹ := by
  simpa [RestrictionLawCarrier.barSigmaStarAtScale, RestrictionLawCarrier.barSigmaStarInvAtScale] using
    Internal.AnnealedPrimitiveScalarizationData.barSigmaStar_eq_inv_barSigmaStarInv
      (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct)
      (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n)

/-- Under the structural law, the annealed coupling matrix vanishes. -/
theorem RestrictionLawCarrier.annealedKappaAtScale_eq_zero
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) :
    annealedKappaAtScale P n = 0 := by
  simpa using
    (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct).annealedKappa_eq_zero n

/-- Internal compatibility between the structural-law contrast and the
scalarization route contrast. -/
theorem Internal.thetaAtScale_eq_scalarization_contrast
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (n : ℤ) :
    hP.thetaAtScale hStruct n =
      (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct).contrast n := by
  rfl

end

end Ch04
end Book
end Homogenization
