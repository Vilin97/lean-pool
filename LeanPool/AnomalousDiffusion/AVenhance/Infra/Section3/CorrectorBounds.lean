/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.CutoffConsequences
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Uniform bounds for the single-mode corrector ingredients. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

namespace AVenhance.Infra.Section3

open AVenhance

theorem CorrectorBounds.indIcc_le_one (a b t : ℝ) : indIcc a b t ≤ 1 := by
  by_cases ht : t ∈ Set.Icc a b <;> simp [indIcc, ht]

/-- Each small-scale time cutoff lies in `[0,1]`. -/
theorem zetaMK_mem_Icc {β : ℝ} (I : Ingredients β) {m : ℕ}
    (k : ℤ) (t : ℝ) : I.zetaMK m k t ∈ Set.Icc 0 1 := by
  let u := (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m
  change I.zeta u ∈ Set.Icc 0 1
  constructor
  · exact I.zeta_nonneg u
  · exact (I.zeta_le_ind u).trans (CorrectorBounds.indIcc_le_one _ _ _)

/-- For positive scales, each translated large-scale time cutoff lies in
`[0,1]`. -/
theorem hatZetaML_mem_Icc {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (l : ℤ) (t : ℝ) : I.hatZetaML m l t ∈ Set.Icc 0 1 := by
  constructor
  · exact Infra.Ingredients.hatZetaML_nonneg I hm l t
  · exact (I.hatZeta_le m hm l t).trans (CorrectorBounds.indIcc_le_one _ _ _)

/-- The Section 3 forcing coefficient is between zero and one. -/
theorem zetaProd_mem_Icc {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (k : ℤ) (t : ℝ) : I.zetaProd m k t ∈ Set.Icc 0 1 := by
  have hh := hatZetaML_mem_Icc I hm (lIdx β I.Λ m k) t
  have hz := zetaMK_mem_Icc I (m := m) k t
  unfold Ingredients.zetaProd
  constructor
  · exact mul_nonneg hh.1 hz.1
  · calc
      I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t ≤ 1 * 1 :=
        mul_le_mul hh.2 hz.2 hz.1 (by norm_num)
      _ = 1 := by norm_num

/-- The memory integral is nonnegative and bounded by the exponential
relaxation scale. -/
theorem corrTime_nonneg_le_inv {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (k : ℤ) (t : ℝ) :
    0 ≤ I.corrTime κ m k t ∧
      I.corrTime κ m k t ≤
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ := by
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  let f : ℝ → ℝ := fun s => I.zetaProd m k s * Real.exp (ρ * (s - t))
  let g : ℝ → ℝ := fun s => I.zetaProd m k s * Real.exp (ρ * s)
  have hfg : f = fun s => Real.exp (-ρ * t) * g s := by
    funext s
    dsimp [f, g]
    rw [show ρ * (s - t) = ρ * s + (-ρ * t) by ring, Real.exp_add]
    ring
  have hGcont : Continuous g := by
    dsimp [g, ρ]
    exact (zetaProd_continuous I k).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hGcompact : HasCompactSupport g := by
    dsimp [g, ρ]
    exact (zetaProd_exp_continuous_compactSupport I κ k).2
  have hGint : Integrable g := hGcont.integrable_of_hasCompactSupport hGcompact
  have hfint : IntegrableOn f (Set.Iic t) := by
    rw [hfg]
    exact hGint.const_mul _ |>.integrableOn
  have hρint : IntegrableOn (fun s : ℝ => Real.exp (ρ * (s - t)))
      (Set.Iic t) := by
    have h := integrableOn_exp_mul_Iic hρ t
    have heq : (fun s : ℝ => Real.exp (ρ * (s - t))) =
        fun s => Real.exp (-ρ * t) * Real.exp (ρ * s) := by
      funext s
      rw [show ρ * (s - t) = ρ * s + (-ρ * t) by ring, Real.exp_add]
      ring
    rw [heq]
    exact h.const_mul _
  have hmono : (∫ s in Set.Iic t, f s) ≤
      ∫ s in Set.Iic t, Real.exp (ρ * (s - t)) := by
    apply setIntegral_mono_on hfint hρint measurableSet_Iic
    intro s hs
    have hz := zetaProd_mem_Icc I hm k s
    calc
      f s = I.zetaProd m k s * Real.exp (ρ * (s - t)) := rfl
      _ ≤ 1 * Real.exp (ρ * (s - t)) :=
        mul_le_mul_of_nonneg_right hz.2 (Real.exp_nonneg _)
      _ = Real.exp (ρ * (s - t)) := by ring
  have hExpInt : (∫ s in Set.Iic t, Real.exp (ρ * (s - t))) = ρ⁻¹ := by
    have hcancel : Real.exp (-ρ * t) * Real.exp (ρ * t) = 1 := by
      rw [← Real.exp_add]
      have hsum : -ρ * t + ρ * t = 0 := by ring
      rw [hsum, Real.exp_zero]
    calc
      (∫ s in Set.Iic t, Real.exp (ρ * (s - t))) =
          Real.exp (-ρ * t) * (∫ s in Set.Iic t, Real.exp (ρ * s)) := by
        rw [show (fun s : ℝ => Real.exp (ρ * (s - t))) =
          fun s => Real.exp (-ρ * t) * Real.exp (ρ * s) by
            funext s
            rw [show ρ * (s - t) = ρ * s + (-ρ * t) by ring, Real.exp_add]
            ring]
        rw [integral_const_mul]
      _ = Real.exp (-ρ * t) * (Real.exp (ρ * t) / ρ) := by
        rw [integral_exp_mul_Iic hρ t]
      _ = ρ⁻¹ := by
        rw [div_eq_mul_inv, ← mul_assoc, hcancel]
        simp
  constructor
  · unfold Ingredients.corrTime
    apply setIntegral_nonneg measurableSet_Iic
    intro s hs
    exact mul_nonneg (zetaProd_mem_Icc I hm k s).1 (Real.exp_nonneg _)
  · unfold Ingredients.corrTime
    calc
      (∫ s in Set.Iic t,
        I.zetaProd m k s * Real.exp (4 * Real.pi ^ 2 * κ /
          epsilon β I.Λ m ^ 2 * (s - t))) ≤
          ∫ s in Set.Iic t, Real.exp (ρ * (s - t)) := by
            simpa [f, ρ] using hmono
      _ = (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ := by
            simpa [ρ] using hExpInt

theorem CorrectorBounds.abs_mul_cos_le (c z : ℝ) :
    |c * Real.cos z| ≤ |c| := by
  rw [abs_mul]
  calc
    |c| * |Real.cos z| ≤ |c| * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one z) (abs_nonneg c)
    _ = |c| := by ring

/-- Every component of the shear is bounded by its amplitude. -/
theorem uShear_component_abs_le {β : ℝ} {Λ m : ℕ} (k : ℤ)
    (x : Vec 2) (j : Fin 2) :
    |uShear β Λ m k x j| ≤ |2 * Real.pi * a β Λ m * epsilon β Λ m| := by
  by_cases h1 : k % 4 = 1
  · fin_cases j
    · simp only [uShear, h1, ↓reduceIte, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero,
        abs_zero, abs_mul,
        Nat.abs_ofNat, Real.abs_pi]
      positivity
    · have hform : uShear β Λ m k x 1 =
        2 * Real.pi * a β Λ m * epsilon β Λ m *
          Real.cos (2 * Real.pi * x 0 / epsilon β Λ m) := by
        simp [uShear, h1]
      change |uShear β Λ m k x (1 : Fin 2)| ≤ _
      rw [hform]
      exact CorrectorBounds.abs_mul_cos_le _ _
  · by_cases h3 : k % 4 = 3
    · fin_cases j
      · have hform : uShear β Λ m k x 0 =
          -(2 * Real.pi * a β Λ m * epsilon β Λ m *
            Real.cos (2 * Real.pi * x 1 / epsilon β Λ m)) := by
          simp [uShear, h3]
        change |uShear β Λ m k x (0 : Fin 2)| ≤ _
        rw [hform, abs_neg]
        exact CorrectorBounds.abs_mul_cos_le _ _
      · simp only [uShear, h3, OfNat.ofNat_ne_one, ↓reduceIte, Fin.isValue, Fin.mk_one,
          Matrix.cons_val_one,
          Matrix.cons_val_fin_one, abs_zero, abs_mul, Nat.abs_ofNat, Real.abs_pi]
        positivity
    · simp only [uShear, h1, ↓reduceIte, h3, Pi.zero_apply, abs_zero, abs_mul, Nat.abs_ofNat,
        Real.abs_pi]
      positivity

/-- The explicit corrector has a global bound when `κ > 0`. -/
theorem chiMK_component_abs_le {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (k : ℤ) (t : ℝ)
    (x : Vec 2) (j : Fin 2) :
    |I.chiMK κ m k t x j| ≤
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ *
        |2 * Real.pi * a β I.Λ m * epsilon β I.Λ m| := by
  have htime := corrTime_nonneg_le_inv I hm κ hκ k t
  have hu := uShear_component_abs_le (β := β) (Λ := I.Λ) (m := m) k x j
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hρ : 0 < 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 := by
    positivity
  have hFabs : |I.corrTime κ m k t| ≤
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ := by
    rw [abs_of_nonneg htime.1]
    exact htime.2
  calc
    |I.chiMK κ m k t x j| =
        |I.corrTime κ m k t| * |uShear β I.Λ m k x j| := by
          simp [Ingredients.chiMK, Pi.smul_apply, smul_eq_mul, abs_mul]
    _ ≤ (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ *
        |uShear β I.Λ m k x j| :=
          mul_le_mul_of_nonneg_right hFabs (abs_nonneg _)
    _ ≤ (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ *
        |2 * Real.pi * a β I.Λ m * epsilon β I.Λ m| :=
          mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hρ.le)

end AVenhance.Infra.Section3
