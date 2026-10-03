/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.Sobolev
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.Derivs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.Defs

/-! Positive-order temperature jets and arbitrary amplitude; no zeroth-order
temperature supremum. Existing Sobolev, product and composition engines are reused. -/

@[expose] public section

noncomputable section

open scoped ContDiff
open Homogenization

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section5.AnalyticBridge

/-- `(n+1)! a^{n+1} ≤ (n+3)! a^{n+3}` for `a ≥ 1`. -/
theorem factorial_mul_pow_succ_le (n : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    (n + 1).factorial * a ^ (n + 1) ≤ ((n + 3).factorial : ℝ) * a ^ (n + 3) := by
  have h1 : ((n + 1).factorial : ℝ) ≤ (n + 3).factorial := by
    exact_mod_cast Nat.factorial_le (by omega)
  have h2 : a ^ (n + 1) ≤ a ^ (n + 3) := pow_le_pow_right₀ ha (by omega)
  have h3 : 0 ≤ a ^ (n + 1) := by positivity
  exact mul_le_mul h1 h2 h3 (by positivity)

/-- Sum of the three Sobolev terms, in abstract-real form. -/
theorem sobolev_sum_le {s₁ s₂ s₃ M : ℝ} (h₁ : s₁ ≤ M) (h₂ : s₂ ≤ M) (h₃ : s₃ ≤ M) :
    s₁ + s₂ + s₃ ≤ 3 * M := by linarith

theorem RelativePositiveSup.basisVec_snoc {n : ℕ} (w : Fin n → Fin 2) (v : Fin 2) :
    (fun j => basisVec ((Fin.snoc (α := fun _ => Fin 2) w v) j)) =
      Fin.snoc (α := fun _ => Vec 2) (fun j => basisVec (w j)) (basisVec v) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

theorem RelativePositiveSup.basisVec_cons {n : ℕ} (w : Fin n → Fin 2) (v : Fin 2) :
    (fun j => basisVec ((Fin.cons (α := fun _ => Fin 2) v w) j)) =
      Fin.cons (α := fun _ => Vec 2) (basisVec v) (fun j => basisVec (w j)) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

/-- The test function `y ↦ Dᵐ f(y)(e_w)` is smooth and periodic. -/
theorem RelativePositiveSup.test_smooth_periodic {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : IsZ2Periodic f) (m : ℕ) (w : Fin m → Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => iteratedFDeriv ℝ m f y (fun j => basisVec (w j))) ∧
      IsZ2Periodic (fun y => iteratedFDeriv ℝ m f y (fun j => basisVec (w j))) :=
  ⟨contDiff_iteratedFDeriv_apply hf m _, isZ2Periodic_iteratedFDeriv_apply hp m _⟩

/-- The `L²_x` bound for the second pure derivative of the test function. -/
theorem RelativePositiveSup.sqrt_l2NormSq_second_le {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f)
    {B a : ℝ}
    (hreg : ∀ (n : ℕ) (i : Fin n → Fin 2), 0 < n →
      Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j)))) ≤
        B * n.factorial * a ^ n)
    (m : ℕ) (w : Fin m → Fin 2) (k : Fin 2) :
    Real.sqrt (l2NormSq (fun y =>
      iteratedFDeriv ℝ 2 (fun z => iteratedFDeriv ℝ m f z (fun j => basisVec (w j))) y
        (fun _ => basisVec k))) ≤ B * ((m + 2).factorial : ℝ) * a ^ (m + 2) := by
  have h := hreg (m + 2) (Fin.cons (α := fun _ => Fin 2) k (Fin.cons (α := fun _ => Fin 2) k w))
      (by omega)
  convert h using 3
  funext y
  rw [iteratedFDeriv_two_iteratedFDeriv_apply hf m _ (basisVec k) y,
      RelativePositiveSup.basisVec_cons, RelativePositiveSup.basisVec_cons]

/-- Pointwise bound on the order-`n` derivatives of `∂_v f`, from the `L²_x` bounds on `f`. -/
theorem abs_iteratedFDeriv_fderiv_le {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : IsZ2Periodic f) {B a : ℝ} (hB : 0 ≤ B) (ha : 1 ≤ a)
    (hreg : ∀ (n : ℕ) (i : Fin n → Fin 2), 0 < n →
      Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j)))) ≤
        B * n.factorial * a ^ n)
    (n : ℕ) (w : Fin n → Fin 2) (v : Fin 2) (x : Vec 2) :
    |iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (basisVec v)) x (fun j => basisVec (w j))| ≤
      3 * sobolevConst * (B * ((n + 3).factorial : ℝ) * a ^ (n + 3)) := by
  set w₁ : Fin (n + 1) → Fin 2 := Fin.snoc (α := fun _ => Fin 2) w v with hw₁
  obtain ⟨hsm, hper⟩ := RelativePositiveSup.test_smooth_periodic hf hp (n + 1) w₁
  have hS := abs_le_sobolevConst_mul hsm hper x
  have hlhs : iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (basisVec v)) x
      (fun j => basisVec (w j)) =
      iteratedFDeriv ℝ (n + 1) f x (fun j => basisVec (w₁ j)) := by
    rw [iteratedFDeriv_fderiv_apply_snoc hf, hw₁, RelativePositiveSup.basisVec_snoc]
  rw [hlhs]
  set M : ℝ := B * ((n + 3).factorial : ℝ) * a ^ (n + 3) with hM
  have hM0 : 0 ≤ M := by positivity
  have s0 : Real.sqrt (l2NormSq (fun y =>
      iteratedFDeriv ℝ (n + 1) f y (fun j => basisVec (w₁ j)))) ≤ M := by
    refine (hreg (n + 1) w₁ (by omega)).trans ?_
    have := factorial_mul_pow_succ_le n ha
    calc B * ((n + 1).factorial : ℝ) * a ^ (n + 1) = B * (((n + 1).factorial : ℝ) * a ^ (n + 1))
        := by
          ring
      _ ≤ B * (((n + 3).factorial : ℝ) * a ^ (n + 3)) := mul_le_mul_of_nonneg_left this hB
      _ = M := by rw [hM]; ring
  have s2 (k : Fin 2) : Real.sqrt (l2NormSq (fun y =>
      iteratedFDeriv ℝ 2 (fun z => iteratedFDeriv ℝ (n + 1) f z (fun j => basisVec (w₁ j))) y
        (fun _ => basisVec k))) ≤ M := RelativePositiveSup.sqrt_l2NormSq_second_le hf hreg (n + 1)
            w₁ k
  have := sobolev_sum_le s0 (s2 0) (s2 1)
  calc _ ≤ sobolevConst * (_ + _ + _) := hS
    _ ≤ sobolevConst * (3 * M) :=
        mul_le_mul_of_nonneg_left this sobolevConst_pos.le
    _ = _ := by ring

end AVenhance.Infra.Section5.RelativeError

end
