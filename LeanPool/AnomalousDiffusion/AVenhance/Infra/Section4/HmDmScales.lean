/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Params
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.DmBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.KappaProduct
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaSpaceTime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.Cutoff
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocitySpatial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.ScalarQuadraticL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HmAdapter

/-! Scalar rate bookkeeping for the `p.Hm` and `p.dm` interfaces.

The geometric factors retain the corrected exponent `4δ` and the cutoff `Jcut`.  The helpers in
    this file keep the temperature amplitude as a
scalar parameter. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section4
open AVenhance

/-- The corrected cutoff is long enough to absorb the fixed negative power
in the `Jcut` remainder scale. -/
theorem hm_dm_jcut_power_budget {β : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) :
    2 + gamma β ≤ delta β * (Jcut β : ℝ) / 2 := by
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos hβ hβ'
  have hδle := Infra.Ingredients.delta_le_one_sixteenth hβ hβ'
  have hN := Infra.Ingredients.Nstar_ge_defining_real hβ hβ'
  have hδN : 500 ≤ delta β * (Nstar β : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hN hδ.le
    have hs : delta β *
        (1 / (delta β) ^ 2 + 500 / delta β) =
          (delta β)⁻¹ + 500 := by
      field_simp
    rw [hs] at h
    have hinv : 0 ≤ (delta β)⁻¹ := inv_nonneg.mpr hδ.le
    linarith
  have hJ : (Nstar β : ℝ) ≤ 2 * (Jcut β : ℝ) + 2 := by
    have hn : Nstar β ≤ 2 * Jcut β + 2 := by
      unfold Jcut
      omega
    exact_mod_cast hn
  have hGamma : gamma β < 4 / 3 := by
    have hg : gamma β = (q β - 1) * β / (q β + 1) := by
      unfold gamma
      ring
    have hq := Infra.Ingredients.one_lt_q hβ hβ'
    rw [hg]
    have hden : 0 < q β + 1 := by linarith
    have hfrac : (q β - 1) / (q β + 1) < 1 := by
      apply (div_lt_iff₀ hden).2
      nlinarith only [hq]
    have hfrac0 : 0 ≤ (q β - 1) / (q β + 1) := by positivity
    calc
      (q β - 1) * β / (q β + 1) = ((q β - 1) / (q β + 1)) * β := by ring
      _ < 1 * β := mul_lt_mul_of_pos_right hfrac (by linarith : 0 < β)
      _ < 1 * (4 / 3) := by nlinarith only [hβ']
      _ = 4 / 3 := by ring
  have hlarge : (2 : ℝ) + gamma β < delta β * (Jcut β : ℝ) / 2 := by
    have hbase : 240 ≤ delta β * (Jcut β : ℝ) := by
      nlinarith only [hδN, hJ, hδle]
    nlinarith only [hbase, hGamma]
  exact hlarge.le

theorem HmDmScales.hmDm_rpow_square {E p : ℝ} (hE : 0 < E) :
    (E ^ p) ^ 2 = E ^ (2 * p) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le]
  congr 1
  ring

/-- The terminal `Jcut` tensor remainder has the scale once its
termwise AMNR envelope, product bound, and time-ratio bound are inserted.
The exponent loss `2+γ` is paid by the exact `Jcut` budget. -/
theorem dm_tail_scale_from_rate_bounds
    {β : ℝ} (I : Ingredients β) (m J : ℕ)
    {E δ γ C₀ Csrc Cprod Theta κm κprev epsm tau tauP A Khalf Afac x : ℝ}
    (hE : 0 < E) (hE1 : E ≤ 1) (_hδ : 0 < δ)
    (_hγ : 0 ≤ γ) (hC₀ : 0 ≤ C₀) (hCsrc : 0 ≤ Csrc)
    (hCprod : 0 ≤ Cprod) (hTheta : 0 ≤ Theta)
    (_hκm : 0 < κm) (hκprev : 0 < κprev) (hepsm : 0 < epsm)
    (htau : 0 < tau) (htauP : 0 < tauP)
    (hKhalf : Khalf = Real.sqrt κprev * Theta)
    (hAfac : Afac = 2) (hx : x = E ^ (δ / 2))
    (hProduct : a β I.Λ m ^ 2 * epsm ^ 4 / κm ≤ Cprod * κprev)
    (hTimeRatio : tau / tauP ≤ (1 / 4) * E ^ δ)
    (hPower : 2 + γ ≤ δ * (J : ℝ) / 2)
    (hA : 0 ≤ A ∧ A ≤ Csrc * Theta * (epsm ^ 2 / κm) *
      (Real.sqrt κprev)⁻¹ * E ^ (-(2 + γ)) * (tauP⁻¹) ^ J) :
      (Nstar β : ℝ) * (8 * A * ((4 * Real.pi ^ 2 * C₀) *
      (a β I.Λ m ^ 2 * epsm ^ 2) * (8 * tau) ^ J)) ≤
      (Nstar β : ℝ) * (8 * (4 * Real.pi ^ 2 * C₀) * Csrc * Cprod) *
        Khalf * (Afac * x) ^ J := by
  rw [hAfac, hx]
  have hsqrt : 0 < Real.sqrt κprev := Real.sqrt_pos.2 hκprev
  have hKhalf0 : 0 ≤ Khalf := by rw [hKhalf]; positivity
  have hsqrtInv : 0 ≤ (Real.sqrt κprev)⁻¹ := inv_nonneg.mpr hsqrt.le
  have hratio0 : 0 ≤ tau / tauP := by positivity
  have hratio8 : 8 * (tau / tauP) ≤ 2 * E ^ δ := by
    calc
      8 * (tau / tauP) ≤ 8 * ((1 / 4) * E ^ δ) :=
        mul_le_mul_of_nonneg_left hTimeRatio (by norm_num)
      _ = 2 * E ^ δ := by ring
  have hratioPow :
      (tauP⁻¹) ^ J * (8 * tau) ^ J ≤ (2 * E ^ δ) ^ J := by
    have hmul : tauP⁻¹ * (8 * tau) = 8 * (tau / tauP) := by
      field_simp [ne_of_gt htauP]
    rw [← mul_pow, hmul]
    exact pow_le_pow_left₀ (by positivity) hratio8 J
  have hprodTime :
      (a β I.Λ m ^ 2 * epsm ^ 4 / κm) *
          ((tauP⁻¹) ^ J * (8 * tau) ^ J) ≤
        (Cprod * κprev) * (2 * E ^ δ) ^ J := by
    exact mul_le_mul hProduct hratioPow (by positivity)
      (mul_nonneg hCprod hκprev.le)
  have hExppow : (E ^ δ) ^ J = E ^ (δ * (J : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le]
  have hEcancel : E ^ (-(2 + γ)) * E ^ (δ * (J : ℝ)) =
      E ^ (δ * (J : ℝ) - (2 + γ)) := by
    rw [← Real.rpow_add hE]
    congr 1
    ring
  have hexp : δ * (J : ℝ) / 2 ≤ δ * (J : ℝ) - (2 + γ) := by
    linarith
  have hEcompare : E ^ (δ * (J : ℝ) - (2 + γ)) ≤
      E ^ (δ * (J : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hE hE1 hexp
  have hxpow : (E ^ (δ / 2)) ^ J = E ^ (δ * (J : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le]
    congr 1
    ring
  have hbase :
      E ^ (-(2 + γ)) * (2 * E ^ δ) ^ J ≤ (2 * E ^ (δ / 2)) ^ J := by
    rw [mul_pow, hExppow]
    calc
      E ^ (-(2 + γ)) * (2 ^ J * E ^ (δ * (J : ℝ))) ≤
          2 ^ J * E ^ (δ * (J : ℝ) - (2 + γ)) := by
        apply le_of_eq
        calc
          _ = 2 ^ J *
              (E ^ (-(2 + γ)) * E ^ (δ * (J : ℝ))) := by ring
          _ = 2 ^ J * E ^ (δ * (J : ℝ) - (2 + γ)) := by rw [hEcancel]
      _ ≤ 2 ^ J * E ^ (δ * (J : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hEcompare (by positivity)
      _ = (2 * E ^ (δ / 2)) ^ J := by
        rw [mul_pow, hxpow]
  have hAterm :
      A * ((a β I.Λ m ^ 2 * epsm ^ 2) * (8 * tau) ^ J) ≤
        Csrc * Cprod * Khalf * (2 * E ^ (δ / 2)) ^ J := by
    calc
      _ ≤ (Csrc * Theta * (epsm ^ 2 / κm) *
          (Real.sqrt κprev)⁻¹ * E ^ (-(2 + γ)) * (tauP⁻¹) ^ J) *
          ((a β I.Λ m ^ 2 * epsm ^ 2) * (8 * tau) ^ J) :=
        mul_le_mul_of_nonneg_right hA.2 (by positivity)
      _ = (Csrc * Theta * (Real.sqrt κprev)⁻¹) *
          ((a β I.Λ m ^ 2 * epsm ^ 4 / κm) *
            ((tauP⁻¹) ^ J * (8 * tau) ^ J)) * E ^ (-(2 + γ)) := by ring
      _ ≤ (Csrc * Theta * (Real.sqrt κprev)⁻¹) *
          ((Cprod * κprev) * (2 * E ^ δ) ^ J) * E ^ (-(2 + γ)) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hprodTime (by positivity)
        · positivity
      _ = Csrc * Cprod * Khalf *
          (E ^ (-(2 + γ)) * (2 * E ^ δ) ^ J) := by
        rw [hKhalf]
        field_simp [ne_of_gt hsqrt]
        rw [Real.sq_sqrt hκprev.le]
        ring
      _ ≤ Csrc * Cprod * Khalf * (2 * E ^ (δ / 2)) ^ J := by
        exact mul_le_mul_of_nonneg_left hbase (by
          exact mul_nonneg (mul_nonneg hCsrc hCprod) hKhalf0)
  have hcoeff : 0 ≤ (Nstar β : ℝ) * (8 * (4 * Real.pi ^ 2 * C₀)) := by
    positivity
  calc
    _ = ((Nstar β : ℝ) * (8 * (4 * Real.pi ^ 2 * C₀))) *
        (A * ((a β I.Λ m ^ 2 * epsm ^ 2) * (8 * tau) ^ J)) := by ring
    _ ≤ ((Nstar β : ℝ) * (8 * (4 * Real.pi ^ 2 * C₀))) *
        (Csrc * Cprod * Khalf * (2 * E ^ (δ / 2)) ^ J) :=
      mul_le_mul_of_nonneg_left hAterm hcoeff
    _ = _ := by ring

theorem HmDmScales.hmDm_abs_apply_le_sqrt_vecNormSq (v : Vec 2) (i : Fin 2) :
    |v i| ≤ Real.sqrt (vecNormSq v) := by
  apply Real.abs_le_sqrt
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

theorem HmDmScales.hmDm_continuous_vecNormSq :
    Continuous (fun v : Vec 2 => vecNormSq v) := by
  unfold vecNormSq vecDot
  fun_prop

end AVenhance.Infra.Section4
