/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.SmoothStep
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Data.Nat.Choose.Sum

/-! Uniform derivative estimates for products of translated smooth transitions. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Cutoff

theorem DerivativeBounds.step_affine_iteratedDeriv (j : ℕ) (a c x : ℝ) :
    iteratedDeriv j (fun y : ℝ => step (a + c * y)) x =
      c ^ j * iteratedDeriv j step (a + c * x) := by
  let g : ℝ → ℝ := fun y => step (y + a)
  have hg : ContDiff ℝ (j : ℕ∞) g := by
    dsimp [g]
    fun_prop
  have hcomp := congrFun (iteratedDeriv_comp_const_mul hg c) x
  have hfun : (fun y : ℝ => step (a + c * y)) = fun y => g (c * y) := by
    funext y
    dsimp [g]
    congr 1
    ring
  rw [hfun]
  calc
    iteratedDeriv j (fun y : ℝ => g (c * y)) x =
        c ^ j * iteratedDeriv j g (c * x) := hcomp
    _ = c ^ j * iteratedDeriv j step (a + c * x) := by
      congr 1
      have hshift := iteratedDeriv_comp_add_const j step a
      simpa [g, add_comm] using congrFun hshift (c * x)

theorem DerivativeBounds.affine_product_iteratedDeriv_bound
    {N : ℕ} {M : ℝ} (hM : 1 ≤ M)
    (hstep : ∀ j : ℕ, j ≤ N → ∀ x : ℝ, |iteratedDeriv j step x| ≤ M)
    {a b c x : ℝ} (hc : |c| ≤ 1) {j : ℕ} (hj : j ≤ N) :
    |iteratedDeriv j (fun y : ℝ => step (a + c * y) * step (b - c * y)) x| ≤
      2 ^ N * M ^ 2 := by
  have hleftSmooth : ContDiff ℝ (j : ℕ∞) (fun y : ℝ => step (a + c * y)) := by
    fun_prop
  have hrightSmooth : ContDiff ℝ (j : ℕ∞) (fun y : ℝ => step (b - c * y)) := by
    fun_prop
  change |iteratedDeriv j
    ((fun y : ℝ => step (a + c * y)) * (fun y : ℝ => step (b - c * y))) x| ≤
      2 ^ N * M ^ 2
  rw [iteratedDeriv_mul hleftSmooth.contDiffAt hrightSmooth.contDiffAt]
  calc
    |∑ i ∈ Finset.range (j + 1),
        j.choose i * iteratedDeriv i (fun y : ℝ => step (a + c * y)) x *
          iteratedDeriv (j - i) (fun y : ℝ => step (b - c * y)) x| ≤
        ∑ i ∈ Finset.range (j + 1),
          |j.choose i * iteratedDeriv i (fun y : ℝ => step (a + c * y)) x *
            iteratedDeriv (j - i) (fun y : ℝ => step (b - c * y)) x| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * M ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simp only [Finset.mem_range] at hi; omega
      have hfi := DerivativeBounds.step_affine_iteratedDeriv i a c x
      have hgi := DerivativeBounds.step_affine_iteratedDeriv (j - i) b (-c) x
      have hfc : |iteratedDeriv i (fun y : ℝ => step (a + c * y)) x| ≤ M := by
        rw [hfi]
        have hpow : |c ^ i| ≤ 1 := by
          rw [abs_pow]
          exact pow_le_one₀ (abs_nonneg c) hc
        calc
          |c ^ i * iteratedDeriv i step (a + c * x)| =
              |c ^ i| * |iteratedDeriv i step (a + c * x)| := abs_mul _ _
          _ ≤ 1 * M := mul_le_mul hpow (hstep i (le_trans hi' hj) _) (abs_nonneg _) (by linarith)
          _ = M := one_mul _
      have hrightFun : (fun y : ℝ => step (b - c * y)) =
          (fun y => step (b + (-c) * y)) := by
        funext y
        congr 1
        ring_nf
      have hgc : |iteratedDeriv (j - i) (fun y : ℝ => step (b - c * y)) x| ≤ M := by
        rw [hrightFun, hgi]
        have hpow : |(-c) ^ (j - i)| ≤ 1 := by
          rw [abs_pow, abs_neg]
          exact pow_le_one₀ (abs_nonneg c) hc
        calc
          |(-c) ^ (j - i) * iteratedDeriv (j - i) step (b + -c * x)| =
              |(-c) ^ (j - i)| *
                |iteratedDeriv (j - i) step (b + -c * x)| := abs_mul _ _
          _ ≤ 1 * M := mul_le_mul hpow
            (hstep (j - i) (by omega) _) (abs_nonneg _) (by linarith)
          _ = M := one_mul _
      have hchoose : 0 ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
      rw [abs_mul, abs_mul, abs_of_nonneg hchoose]
      calc
        (j.choose i : ℝ) *
            |iteratedDeriv i (fun y : ℝ => step (a + c * y)) x| *
            |iteratedDeriv (j - i) (fun y : ℝ => step (b - c * y)) x|
          ≤ (j.choose i : ℝ) * M * M := by
            gcongr
        _ = (j.choose i : ℝ) * M ^ 2 := by ring
    _ = (2 : ℝ) ^ j * M ^ 2 := by
      rw [← Finset.sum_mul]
      norm_cast
      rw [Nat.sum_range_choose]
    _ ≤ 2 ^ N * M ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg M)
      exact_mod_cast (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hj)

/-- Scaling a translated profile by `scale` cancels the corresponding derivative factor. -/
theorem scaled_translate_iteratedDeriv_bound {F : ℝ → ℝ} {N : ℕ} {B scale shift x : ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hbound : ∀ j : ℕ, j ≤ N → ∀ y : ℝ, |iteratedDeriv j F y| ≤ B)
    (hscale : 0 < scale) {j : ℕ} (hj : j ≤ N) :
    scale ^ j * |iteratedDeriv j (fun t : ℝ => F (t / scale - shift)) x| ≤ B := by
  let g : ℝ → ℝ := fun y => F (y - shift)
  have hg : ContDiff ℝ (j : ℕ∞) g := by
    dsimp [g]
    exact (hF.comp (by fun_prop)).of_le (by simp)
  have hfun : (fun t : ℝ => F (t / scale - shift)) =
      fun t => g (scale⁻¹ * t) := by
    funext t
    dsimp [g]
    congr 1
    rw [div_eq_mul_inv]
    ring
  have hcomp := congrFun (iteratedDeriv_comp_const_mul hg scale⁻¹) x
  have hderiv : iteratedDeriv j (fun t : ℝ => F (t / scale - shift)) x =
      (scale⁻¹) ^ j * iteratedDeriv j F (scale⁻¹ * x - shift) := by
    rw [hfun]
    calc
      iteratedDeriv j (fun t : ℝ => g (scale⁻¹ * t)) x =
          (scale⁻¹) ^ j * iteratedDeriv j g (scale⁻¹ * x) := hcomp
      _ = (scale⁻¹) ^ j * iteratedDeriv j F (scale⁻¹ * x - shift) := by
        rw [show iteratedDeriv j g = fun y => iteratedDeriv j F (y - shift) by
          simpa [g] using iteratedDeriv_comp_sub_const j F shift]
  rw [hderiv, abs_mul, abs_pow, abs_inv, abs_of_pos hscale]
  calc
    scale ^ j * (scale⁻¹ ^ j *
        |iteratedDeriv j F (scale⁻¹ * x - shift)|) =
        |iteratedDeriv j F (scale⁻¹ * x - shift)| := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hscale.ne', one_pow, one_mul]
    _ ≤ B := hbound j hj _

theorem affine_product_iteratedDeriv_uniform_bound {N : ℕ} {M : ℝ}
    (hM : 1 ≤ M)
    (hstep : ∀ j : ℕ, j ≤ N → ∀ x : ℝ, |iteratedDeriv j step x| ≤ M)
    {a b x : ℝ} {c : ℝ} (hc : |c| ≤ 1) {j : ℕ} (hj : j ≤ N) :
    |iteratedDeriv j (fun y : ℝ => step (a + c * y) * step (b - c * y)) x| ≤
      2 ^ N * M ^ 2 :=
  DerivativeBounds.affine_product_iteratedDeriv_bound hM hstep hc hj

end AVenhance.Infra.Cutoff
