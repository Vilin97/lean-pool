/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialSourceRates

/-! Spatial radius bookkeeping for composition with an actual flow map. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- A function whose jets cost `ε⁻ⁱ`, composed with a state map whose positive
jets cost `ε⁻⁽ⁱ⁻¹⁾`, retains the same spatial radius. -/
theorem amnr_iteratedFDeriv_comp_radius_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {g : E → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {ε C D : ℝ} (hε : 0 < ε) (hD : 1 ≤ D) (n : ℕ) (x : E)
    (houter : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i f (g x)‖ ≤ C * ε⁻¹ ^ i)
    (hinner : ∀ i, i < n → ‖iteratedFDeriv ℝ (i + 1) g x‖ ≤ D * ε⁻¹ ^ i) :
    ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤ (n.factorial : ℝ) * C * D ^ n * ε⁻¹ ^ n := by
  let fn := fun y : E => f (ε • y)
  let gn := fun y : E => ε⁻¹ • g (ε • y)
  have hfn : ContDiff ℝ (⊤ : ℕ∞) fn := hf.comp (contDiff_id.const_smul ε)
  have hgn : ContDiff ℝ (⊤ : ℕ∞) gn := (hg.comp (contDiff_id.const_smul ε)).const_smul ε⁻¹
  have hx : ε • (ε⁻¹ • x) = x := by rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  have hv : ε • gn (ε⁻¹ • x) = g x := by
    dsimp [gn]
    rw [hx, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  have ho : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i fn (gn (ε⁻¹ • x))‖ ≤ C := by
    intro i hi
    change ‖iteratedFDeriv ℝ i (fun y => f (ε • y)) (gn (ε⁻¹ • x))‖ ≤ C
    rw [iteratedFDeriv_comp_const_smul ε (hf.of_le (by simp))]
    simp only []
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hε.le i), hv]
    have hc : ε ^ i * (C * ε⁻¹ ^ i) = C := by
      calc
        _ = C * (ε * ε⁻¹) ^ i := by rw [mul_pow]; ring
        _ = C := by rw [mul_inv_cancel₀ hε.ne', one_pow, mul_one]
    exact (mul_le_mul_of_nonneg_left (houter i hi) (pow_nonneg hε.le i)).trans_eq hc
  have hi : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i gn (ε⁻¹ • x)‖ ≤ D ^ i := by
    intro i hi hin
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    change ‖iteratedFDeriv ℝ (j + 1) (fun y => ε⁻¹ • g (ε • y)) (ε⁻¹ • x)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (f := fun y => g (ε • y))
      ((hg.comp (contDiff_id.const_smul ε)).contDiffAt.of_le (by simp)),
      iteratedFDeriv_comp_const_smul ε (hg.of_le (by simp))]
    simp only []
    rw [hx, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hε.le _), abs_of_nonneg (inv_nonneg.mpr hε.le)]
    have hc : ε⁻¹ * (ε ^ (j + 1) * (D * ε⁻¹ ^ j)) = D := by
      rw [pow_succ]
      calc
        _ = D * ((ε * ε⁻¹) ^ j * (ε⁻¹ * ε)) := by rw [mul_pow]; ring
        _ = D := by rw [mul_inv_cancel₀ hε.ne', inv_mul_cancel₀ hε.ne', one_pow, mul_one, mul_one]
    exact ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hinner j (by omega))
      (pow_nonneg hε.le _)) (inv_nonneg.mpr hε.le)).trans_eq hc).trans (le_self_pow₀ hD (by omega))
  have hh := norm_iteratedFDeriv_comp_le (n := n) hfn hgn (by simp) (ε⁻¹ • x) ho hi
  have heq : fn ∘ gn = fun y => (f ∘ g) (ε • y) := by
    funext y
    dsimp [fn, gn]
    rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  rw [heq, iteratedFDeriv_comp_const_smul ε ((hf.comp hg).of_le (by simp))] at hh
  simp only [] at hh
  rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hε.le n)] at hh
  have hi := mul_le_mul_of_nonneg_left hh (pow_nonneg (inv_nonneg.mpr hε.le) n)
  have hc : ε⁻¹ ^ n * (ε ^ n * ‖iteratedFDeriv ℝ n (f ∘ g) x‖) =
      ‖iteratedFDeriv ℝ n (f ∘ g) x‖ := by
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, one_mul]
  rw [hc] at hi
  exact hi.trans_eq (mul_comm _ _)

end AVenhance.Infra.Section4
