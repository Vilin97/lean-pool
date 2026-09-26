/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.Basic
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.Euclidean
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.Profile
public import LeanPool.CoarseGraining.Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Derivative Bounds -/

@[expose] public section

noncomputable section

open scoped Topology

namespace Homogenization

/-!
# Compact-support derivative bounds

This file contains small reusable analytic lemmas for smooth compactly
supported functions on `Vec d`.  They are intentionally independent of the
specific cutoff formulas.
-/

/-- Operator norm bound for scalar continuous linear maps on `Vec d`, using
the coordinate basis and the default product/sup norm on `Vec d`. -/
theorem norm_clm_le_sum_basisVec_apply {d : ℕ} (L : Vec d →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i : Fin d, ‖L (basisVec i)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) ?_
  intro x
  have hx :
      L x = ∑ i : Fin d, x i * L (basisVec i) := by
    calc
      L x = ∑ i : Fin d, x i • L (fun j => if i = j then 1 else 0) := by
        simpa using (LinearMap.pi_apply_eq_sum_univ (f := L.toLinearMap) x)
      _ = ∑ i : Fin d, x i • L (basisVec i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          have hfun : (fun j => if i = j then 1 else 0) = basisVec i := by
            funext j
            simp [basisVec_apply, eq_comm]
          rw [hfun]
      _ = ∑ i : Fin d, x i * L (basisVec i) := by
          simp [smul_eq_mul]
  calc
    ‖L x‖ = ‖∑ i : Fin d, x i * L (basisVec i)‖ := by rw [hx]
    _ ≤ ∑ i : Fin d, ‖x i * L (basisVec i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin d, ‖x i‖ * ‖L (basisVec i)‖ := by
          simp [norm_mul]
    _ ≤ ∑ i : Fin d, ‖x‖ * ‖L (basisVec i)‖ := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i : Fin d, ‖L (basisVec i)‖) * ‖x‖ := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (Finset.mul_sum (s := Finset.univ)
              (f := fun i : Fin d => ‖L (basisVec i)‖) ‖x‖).symm

/-- Directional derivative of a shifted coordinate in a coordinate direction. -/
theorem fderiv_coord_sub_const_apply_basisVec {d : ℕ}
    (i j : Fin d) (c x : Vec d) :
    (fderiv ℝ (fun y : Vec d => y i - c i) x) (basisVec j) =
      if j = i then 1 else 0 := by
  rw [fderiv_sub_const]
  change (fderiv ℝ (⇑(ContinuousLinearMap.proj (R := ℝ) i)) x) (basisVec j) = _
  rw [ContinuousLinearMap.fderiv]
  simp [basisVec_apply, eq_comm]

/-- The operator norm of a shifted coordinate derivative is at most `1` in the
default product/sup norm on `Vec d`. -/
theorem norm_fderiv_coord_sub_const_le_one {d : ℕ}
    (i : Fin d) (c x : Vec d) :
    ‖fderiv ℝ (fun y : Vec d => y i - c i) x‖ ≤ 1 := by
  have hsum := norm_clm_le_sum_basisVec_apply (fderiv ℝ (fun y : Vec d => y i - c i) x)
  calc
    ‖fderiv ℝ (fun y : Vec d => y i - c i) x‖
        ≤ ∑ j : Fin d, ‖(fderiv ℝ (fun y : Vec d => y i - c i) x) (basisVec j)‖ := hsum
    _ = 1 := by
          rw [Finset.sum_eq_single i]
          · simp [fderiv_coord_sub_const_apply_basisVec]
          · intro j _hj hji
            simp [fderiv_coord_sub_const_apply_basisVec, hji]
          · intro hi
            exact False.elim (hi (Finset.mem_univ i))

/-- The derivative of a shifted coordinate is constant in the base point. -/
theorem fderiv_coord_sub_const_eq_proj {d : ℕ}
    (i : Fin d) (c x : Vec d) :
    fderiv ℝ (fun y : Vec d => y i - c i) x = ContinuousLinearMap.proj i := by
  rw [fderiv_sub_const]
  change fderiv ℝ (⇑(ContinuousLinearMap.proj (R := ℝ) i)) x = ContinuousLinearMap.proj i
  rw [ContinuousLinearMap.fderiv]

/-- Directional derivative of a shifted coordinate square in a coordinate
direction. -/
theorem fderiv_coord_sub_const_sq_apply_basisVec {d : ℕ}
    (i j : Fin d) (c x : Vec d) :
    (fderiv ℝ (fun y : Vec d => (y i - c i) ^ 2) x) (basisVec j) =
      2 * (x i - c i) * (if j = i then 1 else 0) := by
  rw [fderiv_fun_pow]
  · simp [fderiv_coord_sub_const_apply_basisVec, pow_one, smul_eq_mul]
  · fun_prop

/-- A shifted coordinate is affine, so its second Fréchet derivative vanishes. -/
theorem iteratedFDeriv_two_coord_sub_const_eq_zero {d : ℕ}
    (i : Fin d) (c : Vec d) :
    iteratedFDeriv ℝ 2 (fun y : Vec d => y i - c i) = 0 := by
  ext x m
  have hx0 : iteratedFDeriv ℝ 2 (fun y : Vec d => y i - c i) x = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_fderiv]
    have hconst :
        fderiv ℝ (fun y : Vec d => y i - c i) = fun _ => ContinuousLinearMap.proj i := by
      funext y
      exact fderiv_coord_sub_const_eq_proj i c y
    rw [hconst, iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by norm_num)
      (ContinuousLinearMap.proj i)]
    simp
  simpa using congrArg (fun F : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Vec d) ℝ => F m) hx0

/-- Uniform second-derivative bound for the square of a shifted coordinate. -/
theorem norm_iteratedFDeriv_two_coord_sub_const_sq_le {d : ℕ}
    (i : Fin d) (c x : Vec d) :
    ‖iteratedFDeriv ℝ 2 (fun y : Vec d => (y i - c i) ^ 2) x‖ ≤ 2 := by
  let g : Vec d → ℝ := fun y => y i - c i
  have hg : ContDiff ℝ (2 : ℕ) g := by
    simpa [g] using ((contDiff_apply ℝ ℝ i).sub contDiff_const)
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (A := ℝ) hg hg x le_rfl
  have hzero : ‖iteratedFDeriv ℝ 2 g x‖ = 0 := by
    rw [iteratedFDeriv_two_coord_sub_const_eq_zero, Pi.zero_apply, norm_zero]
  have hone : ‖iteratedFDeriv ℝ 1 g x‖ ≤ 1 := by
    have hnorm :
        ‖iteratedFDeriv ℝ 1 g x‖ = ‖fderiv ℝ g x‖ := by
      simp [norm_iteratedFDeriv_zero,
        (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := g) (n := 0) (x := x)).symm]
    rw [hnorm]
    simpa [g] using norm_fderiv_coord_sub_const_le_one i c x
  have hval : ‖iteratedFDeriv ℝ 0 g x‖ = ‖g x‖ := by
    simp [g]
  have hsq : (fun y : Vec d => (y i - c i) ^ 2) = fun y : Vec d => g y * g y := by
    funext y
    simp [g, pow_two]
  rw [hsq]
  calc
    ‖iteratedFDeriv ℝ 2 (fun y : Vec d => g y * g y) x‖
        ≤ ∑ k ∈ Finset.range (2 + 1),
            ((2).choose k : ℝ) * ‖iteratedFDeriv ℝ k g x‖ * ‖iteratedFDeriv ℝ (2 - k) g x‖ := hmul
    _ ≤ 2 := by
          have hone_nonneg : 0 ≤ ‖iteratedFDeriv ℝ 1 g x‖ := norm_nonneg _
          have hsum :
              ∑ k ∈ Finset.range (2 + 1),
                  ((2).choose k : ℝ) * ‖iteratedFDeriv ℝ k g x‖ * ‖iteratedFDeriv ℝ (2 - k) g x‖
                =
                ‖g x‖ * ‖iteratedFDeriv ℝ 2 g x‖ +
                  2 * ‖iteratedFDeriv ℝ 1 g x‖ * ‖iteratedFDeriv ℝ 1 g x‖ +
                  ‖iteratedFDeriv ℝ 2 g x‖ * ‖g x‖ := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
            simp [hval]
          rw [hsum, hzero]
          have hmid : 2 * ‖iteratedFDeriv ℝ 1 g x‖ * ‖iteratedFDeriv ℝ 1 g x‖ ≤ 2 := by
            nlinarith
          linarith

/-- Euclidean squared distance has second derivative bounded by `2 d` in the
default product/sup norm on `Vec d`. -/
theorem norm_iteratedFDeriv_two_euclideanSqDist_le {d : ℕ}
    (x₀ x : Vec d) :
    ‖iteratedFDeriv ℝ 2 (fun y : Vec d => euclideanSqDist y x₀) x‖ ≤ 2 * (d : ℝ) := by
  have hfun : (fun y : Vec d => euclideanSqDist y x₀) =
      (fun y : Vec d => ∑ i : Fin d, (y i - x₀ i) ^ 2) := by
    funext y
    simp [euclideanSqDist, vecNormSq, vecDot, pow_two]
  rw [hfun]
  rw [iteratedFDeriv_sum]
  · calc
      ‖(∑ i : Fin d, iteratedFDeriv ℝ 2 (fun y : Vec d => (y i - x₀ i) ^ 2)) x‖ =
          ‖∑ i : Fin d, iteratedFDeriv ℝ 2 (fun y : Vec d => (y i - x₀ i) ^ 2) x‖ := by
            simp
      _ ≤ ∑ i : Fin d, ‖iteratedFDeriv ℝ 2 (fun y : Vec d => (y i - x₀ i) ^ 2) x‖ := by
            simpa using norm_sum_le
              (Finset.univ : Finset (Fin d))
              (fun i : Fin d => iteratedFDeriv ℝ 2 (fun y : Vec d => (y i - x₀ i) ^ 2) x)
      _ ≤ ∑ _i : Fin d, 2 := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            exact norm_iteratedFDeriv_two_coord_sub_const_sq_le i x₀ x
      _ = 2 * (d : ℝ) := by
            simp
            ring
  · intro i _hi
    exact (((contDiff_apply ℝ ℝ i).sub contDiff_const).pow 2)

/-- Coordinate-direction derivative of Euclidean squared distance on `Vec d`. -/
theorem fderiv_euclideanSqDist_apply_basisVec {d : ℕ}
    (x₀ x : Vec d) (j : Fin d) :
    (fderiv ℝ (fun y : Vec d => euclideanSqDist y x₀) x) (basisVec j) =
      2 * (x j - x₀ j) := by
  have hfun : (fun y : Vec d => euclideanSqDist y x₀) =
      (fun y : Vec d => ∑ i : Fin d, (y i - x₀ i) ^ 2) := by
    funext y
    simp [euclideanSqDist, vecNormSq, vecDot, pow_two]
  rw [hfun]
  rw [fderiv_fun_sum]
  · simp [fderiv_coord_sub_const_sq_apply_basisVec]
  · intro i _hi
    fun_prop

/-- Chain-rule bound for composing a quantitative one-dimensional transition
profile with a scalar function on `Vec d`. -/
theorem norm_fderiv_profile_comp_le {d : ℕ}
    (θ : QuantitativeTransitionProfile) {g : Vec d → ℝ} {x : Vec d}
    (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y : Vec d => θ (g y)) x‖ ≤
      θ.derivBound * ‖fderiv ℝ g x‖ := by
  have hθdiff : DifferentiableAt ℝ θ (g x) :=
    θ.smooth.differentiable (by simp) (g x)
  rw [fderiv_fun_comp (x := x) hθdiff hg]
  calc
    ‖(fderiv ℝ θ (g x)).comp (fderiv ℝ g x)‖
        ≤ ‖fderiv ℝ θ (g x)‖ * ‖fderiv ℝ g x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖deriv θ (g x)‖ * ‖fderiv ℝ g x‖ := by
      rw [norm_deriv_eq_norm_fderiv]
    _ ≤ θ.derivBound * ‖fderiv ℝ g x‖ :=
      mul_le_mul_of_nonneg_right (θ.norm_deriv_le _) (norm_nonneg _)

/-- Chain-rule Hessian bound for composing a quantitative one-dimensional
transition profile with a scalar function.  The argument is measured through a
single scale `D` controlling both the first and second derivatives in the form
required by Mathlib's quantitative composition estimate. -/
theorem norm_iteratedFDeriv_two_profile_comp_le {d : ℕ}
    (θ : QuantitativeTransitionProfile) {g : Vec d → ℝ} {x : Vec d} {D : ℝ}
    (hg : ContDiff ℝ (2 : ℕ) g)
    (hD_one : ‖iteratedFDeriv ℝ 1 g x‖ ≤ D)
    (hD_two : ‖iteratedFDeriv ℝ 2 g x‖ ≤ D ^ 2) :
    ‖iteratedFDeriv ℝ 2 (fun y : Vec d => θ (g y)) x‖ ≤
      2 * (max 1 (max θ.derivBound θ.secondDerivBound)) * D ^ 2 := by
  let C : ℝ := max 1 (max θ.derivBound θ.secondDerivBound)
  have hC_nonneg : 0 ≤ C := by
    exact le_trans zero_le_one (le_max_left _ _)
  have hC : ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i θ (g x)‖ ≤ C := by
    intro i hi
    interval_cases i
    · rw [norm_iteratedFDeriv_zero]
      exact (Real.norm_of_nonneg (θ.nonneg _)).trans_le
        ((θ.le_one _).trans (le_max_left _ _))
    · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one]
      exact (θ.norm_deriv_le _).trans
        ((le_max_left θ.derivBound θ.secondDerivBound).trans (le_max_right _ _))
    · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      change ‖iteratedDeriv 2 θ (g x)‖ ≤ C
      rw [show iteratedDeriv 2 θ = deriv (deriv θ) by
        rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
      exact (θ.norm_secondDeriv_le _).trans
        ((le_max_right θ.derivBound θ.secondDerivBound).trans (le_max_right _ _))
  have hD : ∀ i, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i g x‖ ≤ D ^ i := by
    intro i h1 hi
    interval_cases i
    · simpa using hD_one
    · simpa using hD_two
  have hcomp := norm_iteratedFDeriv_comp_le
    (𝕜 := ℝ) (g := θ) (f := g) (n := 2) (N := (2 : ℕ))
    (θ.smooth.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    hg le_rfl x hC hD
  simpa [Function.comp_def, Nat.factorial, C, mul_assoc] using hcomp

/-- A smooth compactly supported scalar function has a global first-derivative
bound. -/
theorem exists_bound_fderiv_of_contDiff_hasCompactSupport {d : ℕ}
    {η : _root_.Homogenization.Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_comp : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ η x‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (hη_comp.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
      (hη.continuous_fderiv (by simp))
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x
  exact le_trans (hC x) (le_max_left _ _)

/-- A smooth compactly supported scalar function has a global second-derivative
bound, expressed through `iteratedFDeriv`. -/
theorem exists_bound_iteratedFDeriv_two_of_contDiff_hasCompactSupport {d : ℕ}
    {η : _root_.Homogenization.Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_comp : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ 2 η x‖ ≤ C := by
  have hcont : Continuous (fun x : _root_.Homogenization.Vec d =>
      ‖iteratedFDeriv ℝ 2 η x‖) :=
    (hη.continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).norm
  have hbounded :
      BddAbove (Set.range fun x : _root_.Homogenization.Vec d =>
        ‖iteratedFDeriv ℝ 2 η x‖) := by
    apply hcont.bddAbove_range_of_hasCompactSupport
    apply HasCompactSupport.comp_left _ norm_zero
    exact hη_comp.iteratedFDeriv (𝕜 := ℝ) 2
  obtain ⟨C, hC⟩ := hbounded
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x
  exact le_trans (hC (Set.mem_range_self x)) (le_max_left _ _)

end Homogenization
