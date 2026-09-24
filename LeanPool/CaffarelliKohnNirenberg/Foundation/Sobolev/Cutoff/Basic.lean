/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.Support

/-!
# Quantitative smooth cutoff data

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port keeps the cutoff bundle and the explicit Euclidean
gradient API in the independent `CKN` namespace.

## Main definitions

* `CKN.vecEuclideanNorm`: the Euclidean norm on native coordinate vectors.
* `CKN.classicalGradient`: the coordinate gradient of a scalar function.
* `CKN.QuantitativeSmoothCutoff`: quantitative smooth cutoff data.

## Main results

* `QuantitativeSmoothCutoff.sq`: squaring a cutoff doubles its gradient bound.
* `QuantitativeSmoothCutoff.sq_toFun` and `QuantitativeSmoothCutoff.sq_apply`:
  the square operation has the expected pointwise form.
* `QuantitativeSmoothCutoff.mem_Icc`: every cutoff value lies in `[0, 1]`.
-/

@[expose] public section

open scoped BigOperators

namespace CKN

/-- The Euclidean dot product on native coordinate vectors. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

/-- The square of the Euclidean norm on native coordinate vectors. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

/-- The Euclidean norm on native coordinate vectors. -/
noncomputable def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)

theorem vecNormSq_eq_sum_sq {d : ℕ} (x : Vec d) :
    vecNormSq x = ∑ i, x i ^ 2 := by
  simp [vecNormSq, vecDot, pow_two]

theorem vecNormSq_nonneg {d : ℕ} (x : Vec d) :
    0 ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.sum_nonneg fun i _hi => sq_nonneg (x i)

theorem sq_apply_le_vecNormSq {d : ℕ} (x : Vec d) (i : Fin d) :
    x i ^ 2 ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg (x j))
    (Finset.mem_univ i)

theorem vecNormSq_eq_zero {d : ℕ} {x : Vec d}
    (h : vecNormSq x = 0) :
    x = 0 := by
  funext i
  have hi : x i ^ 2 ≤ 0 := by
    simpa [h] using sq_apply_le_vecNormSq x i
  exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg (x i)))

theorem vecNormSq_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    vecNormSq (c • x) = c ^ 2 * vecNormSq x := by
  rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq]
  calc
    (∑ i, (c • x) i ^ 2) = ∑ i, c ^ 2 * x i ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = c ^ 2 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]

/-- The Euclidean norm is nonnegative. -/
theorem vecEuclideanNorm_nonneg {d : ℕ} (x : Vec d) :
    0 ≤ vecEuclideanNorm x :=
  Real.sqrt_nonneg _

theorem vecEuclideanNorm_sq {d : ℕ} (x : Vec d) :
    vecEuclideanNorm x ^ 2 = vecNormSq x := by
  exact Real.sq_sqrt (vecNormSq_nonneg x)

/-- The Euclidean norm respects scalar multiplication. -/
theorem vecEuclideanNorm_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    vecEuclideanNorm (c • x) = |c| * vecEuclideanNorm x := by
  rw [vecEuclideanNorm, vecEuclideanNorm, vecNormSq_smul]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem vecEuclideanNorm_eq_zero_iff {d : ℕ} {x : Vec d} :
    vecEuclideanNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply vecNormSq_eq_zero
    rw [← vecEuclideanNorm_sq, h]
    norm_num
  · intro hx
    rw [hx]
    simp [vecEuclideanNorm, vecNormSq, vecDot]

theorem abs_apply_le_vecEuclideanNorm {d : ℕ}
    (x : Vec d) (i : Fin d) :
    |x i| ≤ vecEuclideanNorm x := by
  unfold vecEuclideanNorm
  exact Real.abs_le_sqrt (sq_apply_le_vecNormSq x i)

/-- The coordinate gradient of a scalar function in the native vector carrier. -/
noncomputable def classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)

@[simp]
theorem classicalGradient_apply {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) (i : Fin d) :
    classicalGradient f x i =
      (fderiv ℝ f x) (basisVec i) :=
  rfl

/-- A quantitative smooth cutoff between an inner and an outer set. -/
structure QuantitativeSmoothCutoff {d : ℕ}
    (inner outer : Set (Vec d)) (K : ℝ) where
  /-- The cutoff function. -/
  toFun : Vec d → ℝ
  /-- Smoothness to every order. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  /-- The cutoff has compact topological support. -/
  hasCompactSupport : HasCompactSupport toFun
  /-- The topological support lies in the prescribed outer set. -/
  tsupport_subset : tsupport toFun ⊆ outer
  /-- The cutoff is nonnegative. -/
  nonneg : ∀ x, 0 ≤ toFun x
  /-- The cutoff is at most one. -/
  le_one : ∀ x, toFun x ≤ 1
  /-- The cutoff equals one throughout the inner set. -/
  eq_one_on_inner : ∀ x ∈ inner, toFun x = 1
  /-- Pointwise explicit Euclidean gradient bound. -/
  gradient_bound :
    ∀ x, vecEuclideanNorm (classicalGradient toFun x) ≤ K

namespace QuantitativeSmoothCutoff

variable {d : ℕ}
variable {inner outer : Set (Vec d)}
variable {K : ℝ}

instance :
    CoeFun (QuantitativeSmoothCutoff inner outer K)
      (fun _ => Vec d → ℝ) where
  coe η := η.toFun

/-- Restrict the plateau set and enlarge the permitted support set. -/
def reindex
    {inner' outer' : Set (Vec d)}
    (η : QuantitativeSmoothCutoff inner outer K)
    (hinner : inner' ⊆ inner) (houter : outer ⊆ outer') :
    QuantitativeSmoothCutoff inner' outer' K where
  toFun := η.toFun
  smooth := η.smooth
  hasCompactSupport := η.hasCompactSupport
  tsupport_subset := η.tsupport_subset.trans houter
  nonneg := η.nonneg
  le_one := η.le_one
  eq_one_on_inner := fun x hx =>
    η.eq_one_on_inner x (hinner hx)
  gradient_bound := η.gradient_bound

@[simp]
theorem reindex_toFun
    {inner' outer' : Set (Vec d)}
    (η : QuantitativeSmoothCutoff inner outer K)
    (hinner : inner' ⊆ inner) (houter : outer ⊆ outer') :
    (η.reindex hinner houter).toFun = η.toFun :=
  rfl

private theorem classicalGradient_sq_toFun
    (η : QuantitativeSmoothCutoff inner outer K) (x : Vec d) :
    classicalGradient (fun y => η.toFun y ^ 2) x =
      (2 * η.toFun x) • classicalGradient η.toFun x := by
  have hηDiff : DifferentiableAt ℝ η.toFun x :=
    η.smooth.contDiffAt.differentiableAt (by simp)
  funext i
  simp only [classicalGradient_apply, Pi.smul_apply, smul_eq_mul]
  have hsquare :
      (fun y => η.toFun y ^ 2) = η.toFun * η.toFun := by
    funext y
    simp only [Pi.mul_apply, pow_two]
  rw [hsquare, fderiv_mul hηDiff hηDiff]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The square operation is used by the energy estimates. -/
def sq (η : QuantitativeSmoothCutoff inner outer K) :
    QuantitativeSmoothCutoff inner outer (2 * K) where
  toFun := fun x => η.toFun x ^ 2
  smooth := η.smooth.pow 2
  hasCompactSupport := by
    rw [show (fun x => η.toFun x ^ 2) = η.toFun * η.toFun by
      funext x
      simp [pow_two]]
    exact η.hasCompactSupport.mul_right (f' := η.toFun)
  tsupport_subset := by
    simpa only [pow_two] using
      (tsupport_mul_subset_left
        (f := η.toFun) (g := η.toFun)).trans η.tsupport_subset
  nonneg := fun x => sq_nonneg (η.toFun x)
  le_one := fun x =>
    (sq_le_one_iff₀ (η.nonneg x)).2 (η.le_one x)
  eq_one_on_inner := by
    intro x hx
    rw [η.eq_one_on_inner x hx]
    norm_num
  gradient_bound := by
    intro x
    rw [classicalGradient_sq_toFun, vecEuclideanNorm_smul]
    have hcoefficient : |2 * η.toFun x| ≤ 2 := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) (η.nonneg x))]
      exact mul_le_of_le_one_right (by norm_num) (η.le_one x)
    calc
      |2 * η.toFun x| *
            vecEuclideanNorm (classicalGradient η.toFun x) ≤
          2 * vecEuclideanNorm (classicalGradient η.toFun x) :=
        mul_le_mul_of_nonneg_right hcoefficient
          (vecEuclideanNorm_nonneg _)
      _ ≤ 2 * K :=
        mul_le_mul_of_nonneg_left (η.gradient_bound x) (by norm_num)

@[simp]
theorem sq_toFun
    (η : QuantitativeSmoothCutoff inner outer K) :
    η.sq.toFun = fun x => η.toFun x ^ 2 :=
  rfl

@[simp]
theorem sq_apply
    (η : QuantitativeSmoothCutoff inner outer K) (x : Vec d) :
    η.sq x = η x ^ 2 :=
  rfl

/-- Every cutoff value belongs to the interval `[0, 1]`. -/
theorem mem_Icc
    (η : QuantitativeSmoothCutoff inner outer K) (x : Vec d) :
    η x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨η.nonneg x, η.le_one x⟩

end QuantitativeSmoothCutoff

end CKN
