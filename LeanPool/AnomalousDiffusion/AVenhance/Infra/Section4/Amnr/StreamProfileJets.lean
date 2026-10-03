/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowGlobalSpatialSmoothness

/-! Every primitive shear derivative with its exact physical amplitude and radius. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Composition with a fixed linear operator has exactly its multilinear
operator cost, without a factorial from the nonlinear chain rule. -/
theorem amnr_iteratedFDeriv_comp_linear_norm_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (L : E →L[ℝ] F) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * ‖L‖ ^ n := by
  rw [L.iteratedFDeriv_comp_right hf x (i := n) (by simp)]
  exact ((iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)).trans_eq
    (by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin])

/-- Every derivative of an actual sinusoidal shear is controlled by its
frequency to that derivative order. -/
theorem amnr_shear_iteratedFDeriv_norm_le {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (i : Fin 2) (n : ℕ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun y : Vec 2 => A * Real.sin (L * y i)) x‖ ≤ A * L ^ n := by
  let P : Vec 2 →L[ℝ] ℝ := L • ContinuousLinearMap.proj i
  have hP : ‖P‖ ≤ L := by
    apply ContinuousLinearMap.opNorm_le_bound _ hL
    intro y
    change ‖L * y i‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hL]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm y i) hL
  have hsin : ‖iteratedFDeriv ℝ n Real.sin (P x)‖ ≤ 1 := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        Real.abs_iteratedDeriv_sin_le_one n (P x)
  have hh := amnr_iteratedFDeriv_comp_linear_norm_le (f := Real.sin) Real.contDiff_sin P n x
  have hc := hh.trans ((mul_le_mul hsin (pow_le_pow_left₀ (norm_nonneg P) hP n)
    (by positivity) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _))
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (Real.sin ∘ P) :=
    (Real.contDiff_sin : ContDiff ℝ (⊤ : ℕ∞) Real.sin).comp P.contDiff
  change ‖iteratedFDeriv ℝ n (fun y => A • (Real.sin ∘ P) y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hsm.contDiffAt.of_le (by simp)),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hA]
  exact mul_le_mul_of_nonneg_left hc hA

/-- Every actual source profile has the physical stream amplitude `a_m ε_m²`
and spatial radius `ε_m`, at every derivative order. -/
theorem amnr_psi_iteratedFDeriv_norm_le {β : ℝ} (I : AVenhance.Ingredients β)
    (m : ℕ) (k : ℤ) (n : ℕ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (AVenhance.psi β I.Λ m k) x‖ ≤
      (AVenhance.a β I.Λ m * AVenhance.epsilon β I.Λ m ^ 2) *
        (2 * Real.pi) ^ n * (AVenhance.epsilon β I.Λ m)⁻¹ ^ n := by
  let A := AVenhance.a β I.Λ m
  let E := AVenhance.epsilon β I.Λ m
  have hA : 0 < A := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hE : 0 < E := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have heq : AVenhance.psi β I.Λ m k = fun y => A * E ^ 2 *
      (if k % 4 = 1 then Real.sin ((2 * Real.pi * E⁻¹) * y 0)
       else if k % 4 = 3 then Real.sin ((2 * Real.pi * E⁻¹) * y 1) else 0) := by
    funext y
    simp only [AVenhance.psi, AVenhance.psi0, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rfl
  rw [heq]
  split_ifs with hk hk
  · exact (amnr_shear_iteratedFDeriv_norm_le (by positivity : 0 ≤ A * E ^ 2)
      (by positivity : 0 ≤ 2 * Real.pi * E⁻¹) 0 n x).trans_eq (by rw [mul_pow]; ring)
  · exact (amnr_shear_iteratedFDeriv_norm_le (by positivity : 0 ≤ A * E ^ 2)
      (by positivity : 0 ≤ 2 * Real.pi * E⁻¹) 1 n x).trans_eq (by rw [mul_pow]; ring)
  · simp only [mul_zero]
    by_cases hn : n = 0
    · subst n
      simp only [norm_iteratedFDeriv_zero, norm_zero]
      positivity
    · rw [iteratedFDeriv_const_of_ne hn]
      simp only [Pi.zero_apply, norm_zero]
      positivity

end AVenhance.Infra.Section4
