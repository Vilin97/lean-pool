/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.SpaceAverages
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.CutoffConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.TimeScaleFacts
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.CorrTime

/-! The exact averaged diagonal contribution of a single active shear mode. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

namespace AVenhance.Infra.Section3

open AVenhance

/-- The shear forcing coefficient is nonnegative. -/
theorem zetaProd_nonneg {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (k : ℤ) (t : ℝ) : 0 ≤ I.zetaProd m k t := by
  unfold Ingredients.zetaProd Ingredients.zetaMK scaledCutoff
  exact mul_nonneg (Infra.Ingredients.hatZetaML_nonneg I hm _ t)
    (I.zeta_nonneg _)

/-- The exponential memory of a nonnegative shear forcing is nonnegative. -/
theorem corrTime_nonneg {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ) : 0 ≤ I.corrTime κ m k t := by
  unfold Ingredients.corrTime
  apply setIntegral_nonneg measurableSet_Iic
  intro s _hs
  exact mul_nonneg (zetaProd_nonneg I hm k s) (Real.exp_nonneg _)

/-- Spatially averaging the horizontal active-mode interaction gives the
positive diagonal coefficient in `e.Jm.explicit.mofo`. -/
theorem spaceAvg_cross_one {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ) (hk : k % 4 = 1)
    (hε : epsilon β I.Λ m ≠ 0) :
    spaceAvg (fun x : Vec 2 => I.zetaProd m k t *
      psi β I.Λ m k x *
        spaceGrad (fun y => I.chiMK κ m k t y 1) x 0) =
      2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * I.corrTime κ m k t := by
  have hfun : (fun x : Vec 2 => I.zetaProd m k t *
      psi β I.Λ m k x *
        spaceGrad (fun y => I.chiMK κ m k t y 1) x 0) =
      fun x => (4 * Real.pi ^ 2 * a β I.Λ m ^ 2 *
        epsilon β I.Λ m ^ 2 * I.zetaProd m k t * I.corrTime κ m k t) *
        Real.sin (2 * Real.pi * (epsilon β I.Λ m)⁻¹ * x 0) ^ 2 := by
    funext x
    rw [Infra.Section3.psi_sineCoordinate]
    simp only [ite_eq_left hk]
    rw [chiMK_spaceGrad_one I κ k t x hk hε]
    have hfreq : (2 * Real.pi / epsilon β I.Λ m) * x 0 =
        2 * Real.pi * x 0 / epsilon β I.Λ m := by
      field_simp [hε]
    rw [hfreq]
    ring_nf
  rw [hfun]
  unfold spaceAvg
  rw [integral_const_mul]
  have havg := spaceAvg_sin_square_epsilon I hm 0
  unfold spaceAvg at havg
  rw [havg]
  ring

/-- Spatially averaging the vertical active-mode interaction gives the same
positive diagonal coefficient in the other coordinate. -/
theorem spaceAvg_cross_three {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ) (hk : k % 4 = 3)
    (hε : epsilon β I.Λ m ≠ 0) :
    spaceAvg (fun x : Vec 2 => I.zetaProd m k t *
      psi β I.Λ m k x *
        (-spaceGrad (fun y => I.chiMK κ m k t y 0) x 1)) =
      2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * I.corrTime κ m k t := by
  have hfun : (fun x : Vec 2 => I.zetaProd m k t *
      psi β I.Λ m k x *
        (-spaceGrad (fun y => I.chiMK κ m k t y 0) x 1)) =
    fun x => (4 * Real.pi ^ 2 * a β I.Λ m ^ 2 *
        epsilon β I.Λ m ^ 2 * I.zetaProd m k t * I.corrTime κ m k t) *
        Real.sin (2 * Real.pi * (epsilon β I.Λ m)⁻¹ * x 1) ^ 2 := by
    funext x
    rw [Infra.Section3.psi_sineCoordinate]
    have hnot1 : k % 4 ≠ 1 := by omega
    simp only [ite_eq_right hnot1, ite_eq_left hk]
    rw [chiMK_spaceGrad_three I κ k t x hk hε]
    have hfreq : (2 * Real.pi / epsilon β I.Λ m) * x 1 =
        2 * Real.pi * x 1 / epsilon β I.Λ m := by
      field_simp [hε]
    rw [hfreq]
    ring_nf
  rw [hfun]
  unfold spaceAvg
  rw [integral_const_mul]
  have havg := spaceAvg_sin_square_epsilon I hm 1
  unfold spaceAvg at havg
  rw [havg]
  ring

/-- The mean square of the sole nonzero corrector gradient in a horizontal
active shear. This is the energy term paired with the explicit flux formula. -/
theorem spaceAvg_chiMK_gradient_sq_one {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 1) :
    spaceAvg (fun x : Vec 2 =>
      spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 ^ 2) =
      8 * Real.pi ^ 4 * a β I.Λ m ^ 2 * I.corrTime κ m k t ^ 2 := by
  have hε : epsilon β I.Λ m ≠ 0 := ne_of_gt
    (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  have hfreq (z : ℝ) : 2 * Real.pi * z / epsilon β I.Λ m =
      2 * Real.pi * (epsilon β I.Λ m)⁻¹ * z := by
    field_simp [hε]
  have hfun : (fun x : Vec 2 =>
      spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 ^ 2) =
      fun x => (4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t) ^ 2 *
        Real.sin (2 * Real.pi * (epsilon β I.Λ m)⁻¹ * x 0) ^ 2 := by
    funext x
    rw [chiMK_spaceGrad_one I κ k t x hk hε, hfreq]
    ring
  rw [hfun]
  unfold spaceAvg
  rw [integral_const_mul]
  have havg := spaceAvg_sin_square_epsilon I hm 0
  unfold spaceAvg at havg
  rw [havg]
  ring

/-- The mean square of the sole nonzero corrector gradient in a vertical
active shear. -/
theorem spaceAvg_chiMK_gradient_sq_three {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 3) :
    spaceAvg (fun x : Vec 2 =>
      spaceGrad (fun y => I.chiMK κ m k t y 0) x 1 ^ 2) =
      8 * Real.pi ^ 4 * a β I.Λ m ^ 2 * I.corrTime κ m k t ^ 2 := by
  have hε : epsilon β I.Λ m ≠ 0 := ne_of_gt
    (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  have hfreq (z : ℝ) : 2 * Real.pi * z / epsilon β I.Λ m =
      2 * Real.pi * (epsilon β I.Λ m)⁻¹ * z := by
    field_simp [hε]
  have hfun : (fun x : Vec 2 =>
      spaceGrad (fun y => I.chiMK κ m k t y 0) x 1 ^ 2) =
      fun x => (4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t) ^ 2 *
        Real.sin (2 * Real.pi * (epsilon β I.Λ m)⁻¹ * x 1) ^ 2 := by
    funext x
    rw [chiMK_spaceGrad_three I κ k t x hk hε, hfreq]
    ring
  rw [hfun]
  unfold spaceAvg
  rw [integral_const_mul]
  have havg := spaceAvg_sin_square_epsilon I hm 1
  unfold spaceAvg at havg
  rw [havg]
  ring

end AVenhance.Infra.Section3
