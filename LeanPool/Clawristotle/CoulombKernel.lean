/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.SchwartzDecayDefs

/-!
# Coulomb Kernel Definition and Schwartz Helpers

Defines `coulombKernel` (Psi(r) = r^{-3} for r > 0) and proves basic properties:
strict positivity, Schwartz uniform bounds, and `inv_norm_schwartz_integrable`.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- The Coulomb collision kernel: Ψ(r) = r⁻³ for r > 0, extended to 1 for r ≤ 0.
    The value at r ≤ 0 is irrelevant since landauMatrix Ψ 0 = 0 always
    (the projection |z|²I - zz^T vanishes at z = 0). Setting it to 1 ensures
    ∀ r, 0 < Ψ r, which the abstract theorem requires. -/
def coulombKernel (r : ℝ) : ℝ :=
  if r ≤ 0 then 1 else r ^ (-3 : ℝ)

lemma coulombKernel_pos : ∀ r, 0 < coulombKernel r := by
  intro r
  simp only [coulombKernel]
  split
  · exact one_pos
  · exact rpow_pos_of_pos (by linarith) _

/-- Log bound from Schwartz upper bound + stretched-exponential lower bound.
    From Schwartz N=0, k=0: |f x v| ≤ C_upper (uniform in x, v).
    From ExpDecay: f x v ≥ exp(-C_exp * (1+‖v‖)^K_exp).
    Together: |log(f x v)| ≤ max(|log C_upper|, C_exp * (1+‖v‖)^K_exp). -/
lemma schwartz_log_bound
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ x v, 0 < f x v)
    (hSchwartz : UniformSchwartzDecay f)
    (hExpDecay : ∃ (C : ℝ) (K : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      Real.exp (-C * (1 + ‖v‖) ^ K) ≤ f x v) :
    ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log := by
  -- Upper bound on f from Schwartz (N=0, k=0)
  obtain ⟨C_up, hC_up_pos, hbound_up⟩ := hSchwartz.hDecay (k := 0) 0 (by omega)
  -- Lower bound from stretched-exponential decay
  obtain ⟨C_exp, K_exp, hbound_low⟩ := hExpDecay
  -- From Schwartz: ‖iteratedFDeriv ℝ 0 (f x) v‖ * 1 ≤ C_up → |f x v| ≤ C_up
  have hf_le : ∀ x v, f x v ≤ C_up := fun x v => by
    have h := hbound_up x v
    simp only [norm_iteratedFDeriv_zero, norm_eq_abs, pow_zero, mul_one] at h
    exact le_trans (le_abs_self _) h
  -- log(f x v) ≤ log(C_up)
  have hlog_upper : ∀ x v, Real.log (f x v) ≤ Real.log C_up :=
    fun x v => Real.log_le_log (hf_pos x v) (hf_le x v)
  -- log(f x v) ≥ -C_exp * (1 + ‖v‖)^K_exp from exp lower bound
  have hlog_lower : ∀ x v, -C_exp * (1 + ‖v‖) ^ K_exp ≤ Real.log (f x v) := by
    intro x v
    rw [← Real.log_exp (-C_exp * (1 + ‖v‖) ^ K_exp)]
    exact Real.log_le_log (Real.exp_pos _) (hbound_low x v)
  -- |log(f x v)| ≤ (|log C_up| + |C_exp|) * (1 + ‖v‖)^K_exp
  refine ⟨|Real.log C_up| + |C_exp| + 1, K_exp, fun x v => ?_⟩
  rw [abs_le]
  have h1v_ge : (1 : ℝ) ≤ (1 + ‖v‖) ^ K_exp :=
    one_le_pow₀ (by linarith [norm_nonneg v])
  have h1v_nn : (0 : ℝ) ≤ (1 + ‖v‖) ^ K_exp := le_trans zero_le_one h1v_ge
  have hlow := hlog_lower x v
  have hup := hlog_upper x v
  have hlb := le_abs_self (Real.log C_up)
  have key : (|Real.log C_up| + |C_exp| + 1) * (1 + ‖v‖) ^ K_exp ≥
      (|Real.log C_up| + |C_exp| + 1) * 1 :=
    mul_le_mul_of_nonneg_left h1v_ge (by positivity)
  constructor
  · nlinarith [le_abs_self C_exp, abs_nonneg (Real.log C_up),
      mul_le_mul_of_nonneg_right
        (show C_exp ≤ |Real.log C_up| + |C_exp| + 1 by
          linarith [le_abs_self C_exp, abs_nonneg (Real.log C_up)]) h1v_nn]
  · nlinarith [abs_nonneg C_exp]

/-- Schwartz decay implies moment integrability with norm powers. -/
lemma schwartz_norm_pow_integrable
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ 3 (f x))
    (hSchwartz : UniformSchwartzDecay f)
    (x : Torus3) (k : ℕ) :
    Integrable (fun v => ‖v‖ ^ k * |f x v|) := by
  -- Since f > 0, |f| = f
  have habs : (fun v => ‖v‖ ^ k * |f x v|) = (fun v => ‖v‖ ^ k * f x v) :=
    funext fun v => by rw [abs_of_pos (hf_pos x v)]
  rw [habs]
  -- From Schwartz: |f x v| * (1+‖v‖)^(k+4) ≤ C, so f x v ≤ C/(1+‖v‖)^(k+4)
  -- Then ‖v‖^k * f x v ≤ (1+‖v‖)^k * C/(1+‖v‖)^(k+4) = C/(1+‖v‖)^4
  obtain ⟨C, hC_pos, hbound⟩ := hSchwartz.hDecay (k := 0) (k + 4) (by omega)
  apply (inverse_poly_integrable C).mono'
    ((continuous_norm.pow k |>.mul (hf_smooth x).continuous).aestronglyMeasurable)
  filter_upwards [] with v
  have hb := hbound x v
  simp only [norm_iteratedFDeriv_zero, norm_eq_abs] at hb
  -- hb : |f x v| * (1 + ‖v‖) ^ (k + 4) ≤ C
  have hfv_pos := hf_pos x v
  rw [abs_of_pos hfv_pos] at hb
  have h1v : (0 : ℝ) < 1 + ‖v‖ := by linarith [norm_nonneg v]
  -- `Continuous.mul` produces a `Pi` product; unfold it pointwise.
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (le_of_lt hfv_pos)), le_div_iff₀ (pow_pos h1v 4)]
  have h_norm_le : ‖v‖ ≤ 1 + ‖v‖ := le_add_of_nonneg_left zero_le_one
  calc ‖v‖ ^ k * f x v * (1 + ‖v‖) ^ 4
      ≤ (1 + ‖v‖) ^ k * f x v * (1 + ‖v‖) ^ 4 := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h_norm_le _)
            (le_of_lt hfv_pos)
        · exact pow_nonneg (le_of_lt h1v) _
    _ = f x v * (1 + ‖v‖) ^ (k + 4) := by ring_nf
    _ ≤ C := hb

end VML
