/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ActiveModeFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxEnergyCutoff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! A modewise flux-energy identity from the exact memory ODE. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

namespace AVenhance.Infra.Section3

open AVenhance

theorem FluxEnergy.corrTime_mul_deriv_interval {β : ℝ} (I : Ingredients β) {m : ℕ}
    (κ : ℝ) (k : ℤ) (s t : ℝ) :
    (∫ r in s..t, I.corrTime κ m k r * deriv (I.corrTime κ m k) r) =
      (I.corrTime κ m k t ^ 2 - I.corrTime κ m k s ^ 2) / 2 := by
  let f : ℝ → ℝ := I.corrTime κ m k
  have hfcont : Continuous f := corrTime_continuous I κ k
  let g : ℝ → ℝ := fun r => I.zetaProd m k r -
    (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * f r
  have hgcont : Continuous g := by
    dsimp [g]
    exact (zetaProd_continuous I k).sub
      (continuous_const.mul hfcont)
  have hinter : IntervalIntegrable g volume s t :=
    hgcont.intervalIntegrable (μ := volume) s t
  have hderivEq : deriv f = g := by
    funext r
    exact (corrTime_hasDerivAt I κ k r).deriv
  have hprod := intervalIntegral.integral_deriv_mul_eq_sub
    (u := f) (v := f) (u' := g) (v' := g)
    (fun r _ => corrTime_hasDerivAt I κ k r)
    (fun r _ => corrTime_hasDerivAt I κ k r) hinter hinter
  have hpoint : (fun r => g r * f r + f r * g r) =
      fun r => 2 * (f r * g r) := by
    funext r
    ring
  rw [hpoint, intervalIntegral.integral_const_mul] at hprod
  rw [hderivEq]
  dsimp [f] at hprod ⊢
  calc
    (∫ r in s..t, f r * g r) =
        (2 * ∫ r in s..t, f r * g r) / 2 := by ring
    _ = (I.corrTime κ m k t ^ 2 - I.corrTime κ m k s ^ 2) / 2 := by
      rw [hprod]
      ring

/-- For a horizontal active shear, the instantaneous flux correction minus
the corrector energy is exactly the memory derivative term. -/
theorem activeFluxEnergyBalance_one {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 1) :
    spaceAvg (fun x : Vec 2 => I.zetaProd m k t *
      psi β I.Λ m k x *
        spaceGrad (fun y => I.chiMK κ m k t y 1) x 0) -
      κ * spaceAvg (fun x : Vec 2 =>
        spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 ^ 2) =
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 *
        epsilon β I.Λ m ^ 2 * I.corrTime κ m k t) *
        deriv (I.corrTime κ m k) t := by
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  rw [spaceAvg_cross_one I hm κ k t hk (ne_of_gt hε),
    spaceAvg_chiMK_gradient_sq_one I hm κ k t hk,
    (corrTime_hasDerivAt I κ k t).deriv]
  field_simp [ne_of_gt hε]
  ring

/-- The same instantaneous flux-energy identity holds for a vertical active
shear, with the matching first coordinate. -/
theorem activeFluxEnergyBalance_three {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 3) :
    spaceAvg (fun x : Vec 2 => I.zetaProd m k t *
      psi β I.Λ m k x *
        (-spaceGrad (fun y => I.chiMK κ m k t y 0) x 1)) -
      κ * spaceAvg (fun x : Vec 2 =>
        spaceGrad (fun y => I.chiMK κ m k t y 0) x 1 ^ 2) =
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 *
        epsilon β I.Λ m ^ 2 * I.corrTime κ m k t) *
        deriv (I.corrTime κ m k) t := by
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  rw [spaceAvg_cross_three I hm κ k t hk (ne_of_gt hε),
    spaceAvg_chiMK_gradient_sq_three I hm κ k t hk,
    (corrTime_hasDerivAt I κ k t).deriv]
  field_simp [ne_of_gt hε]
  ring

/-- The horizontal single-mode flux-energy defect has the small scale of the
full source lemma whenever the memory derivative has the corresponding slow
forcing bound. The derivative estimate is kept as an explicit hypothesis here;
the full moving-cutoff aggregate still needs that estimate proved and summed. -/
theorem activeFluxEnergyBalance_one_small {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ τ L : ℝ) (hκ : 0 < κ) (hτ : 0 < τ)
    (k : ℤ) (t : ℝ) (hk : k % 4 = 1)
    (hderiv : |deriv (I.corrTime κ m k) t| ≤
      L * epsilon β I.Λ m ^ 2 / (κ * τ)) :
    |spaceAvg (fun x : Vec 2 => I.zetaProd m k t *
        psi β I.Λ m k x *
          spaceGrad (fun y => I.chiMK κ m k t y 1) x 0) -
      κ * spaceAvg (fun x : Vec 2 =>
        spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 ^ 2)| ≤
      L * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ)) *
        (epsilon β I.Λ m ^ 2 / (κ * τ)) := by
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hmem := corrTime_nonneg_le_inv I hm κ hκ k t
  have hmemEq : (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ =
      epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ) := by
    field_simp [ne_of_gt hκ, ne_of_gt hε]
  have hmemAbs : |I.corrTime κ m k t| ≤
      epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ) := by
    rw [abs_le]
    constructor
    · have hposR : 0 ≤ (epsilon β I.Λ m ^ 2) /
          (4 * Real.pi ^ 2 * κ) := by positivity
      linarith [hmem.1, hposR]
    · simpa [hmemEq] using hmem.2
  rw [activeFluxEnergyBalance_one I hm κ k t hk]
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ 2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2)]
  calc
    (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
        |I.corrTime κ m k t| * |deriv (I.corrTime κ m k) t| ≤
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
        (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) *
        (L * epsilon β I.Λ m ^ 2 / (κ * τ)) := by
      gcongr
    _ = L * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ)) *
        (epsilon β I.Λ m ^ 2 / (κ * τ)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      field_simp [ne_of_gt hκ, ne_of_gt hτ, ne_of_gt hε]
      ring

/-- The vertical active-mode flux-energy defect has the same conditional
small-scale estimate. -/
theorem activeFluxEnergyBalance_three_small {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ τ L : ℝ) (hκ : 0 < κ) (hτ : 0 < τ)
    (k : ℤ) (t : ℝ) (hk : k % 4 = 3)
    (hderiv : |deriv (I.corrTime κ m k) t| ≤
      L * epsilon β I.Λ m ^ 2 / (κ * τ)) :
    |spaceAvg (fun x : Vec 2 => I.zetaProd m k t *
        psi β I.Λ m k x *
          (-spaceGrad (fun y => I.chiMK κ m k t y 0) x 1)) -
      κ * spaceAvg (fun x : Vec 2 =>
        spaceGrad (fun y => I.chiMK κ m k t y 0) x 1 ^ 2)| ≤
      L * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ)) *
        (epsilon β I.Λ m ^ 2 / (κ * τ)) := by
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hmem := corrTime_nonneg_le_inv I hm κ hκ k t
  have hmemEq : (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ =
      epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ) := by
    field_simp [ne_of_gt hκ, ne_of_gt hε]
  have hmemAbs : |I.corrTime κ m k t| ≤
      epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ) := by
    rw [abs_le]
    constructor
    · have hposR : 0 ≤ (epsilon β I.Λ m ^ 2) /
          (4 * Real.pi ^ 2 * κ) := by positivity
      linarith [hmem.1, hposR]
    · simpa [hmemEq] using hmem.2
  rw [activeFluxEnergyBalance_three I hm κ k t hk]
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ 2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2)]
  calc
    (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
        |I.corrTime κ m k t| * |deriv (I.corrTime κ m k) t| ≤
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
        (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) *
        (L * epsilon β I.Λ m ^ 2 / (κ * τ)) := by
      gcongr
    _ = L * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ)) *
        (epsilon β I.Λ m ^ 2 / (κ * τ)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      field_simp [ne_of_gt hκ, ne_of_gt hτ, ne_of_gt hε]
      ring

/-- The horizontal active-mode defect estimate with its derivative hypothesis
discharged from the cutoff bounds. -/
theorem activeFluxEnergyBalance_one_cutoff_error {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ)
    (k : ℤ) (t : ℝ) (hk : k % 4 = 1) :
    |spaceAvg (fun x : Vec 2 => I.zetaProd m k t *
        psi β I.Λ m k x *
          spaceGrad (fun y => I.chiMK κ m k t y 1) x 0) -
      κ * spaceAvg (fun x : Vec 2 =>
        spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 ^ 2)| ≤
      ((I.Czeta + I.Chat) / (4 * Real.pi ^ 2)) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ)) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
  have hderiv := corrTime_forcingError_le I hm κ hκ k t
  have hode := (corrTime_hasDerivAt I (m := m) κ k t).deriv
  rw [← hode] at hderiv
  have hderiv' : |deriv (I.corrTime κ m k) t| ≤
      ((I.Czeta + I.Chat) / (4 * Real.pi ^ 2)) *
        epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) := by
    convert hderiv using 1
    field_simp [ne_of_gt hκ, ne_of_gt (I.tau_pos' m)]
  exact activeFluxEnergyBalance_one_small I hm κ (tau β I.Λ m)
    ((I.Czeta + I.Chat) / (4 * Real.pi ^ 2)) hκ (I.tau_pos' m) k t hk hderiv'

/-- The vertical active-mode defect estimate with its derivative hypothesis
discharged from the cutoff bounds. -/
theorem activeFluxEnergyBalance_three_cutoff_error {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ)
    (k : ℤ) (t : ℝ) (hk : k % 4 = 3) :
    |spaceAvg (fun x : Vec 2 => I.zetaProd m k t *
        psi β I.Λ m k x *
          (-spaceGrad (fun y => I.chiMK κ m k t y 0) x 1)) -
      κ * spaceAvg (fun x : Vec 2 =>
        spaceGrad (fun y => I.chiMK κ m k t y 0) x 1 ^ 2)| ≤
      ((I.Czeta + I.Chat) / (4 * Real.pi ^ 2)) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ)) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
  have hderiv := corrTime_forcingError_le I hm κ hκ k t
  have hode := (corrTime_hasDerivAt I (m := m) κ k t).deriv
  rw [← hode] at hderiv
  have hderiv' : |deriv (I.corrTime κ m k) t| ≤
      ((I.Czeta + I.Chat) / (4 * Real.pi ^ 2)) *
        epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) := by
    convert hderiv using 1
    field_simp [ne_of_gt hκ, ne_of_gt (I.tau_pos' m)]
  exact activeFluxEnergyBalance_three_small I hm κ (tau β I.Λ m)
    ((I.Czeta + I.Chat) / (4 * Real.pi ^ 2)) hκ (I.tau_pos' m) k t hk hderiv'

end AVenhance.Infra.Section3
