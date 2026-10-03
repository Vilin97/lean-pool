/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionInputs.CosineDeriv
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionInputs.VelGrad
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.NoSelectionInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergySmooth

/-! # `CosineDatumContract` -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSelectionInputs

open AVenhance

theorem cosDatum_periodic (n : ℕ) (c : ℝ) :
    IsZ2Periodic (fun x : Vec 2 => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) := by
  intro m x
  have h : 2 * Real.pi * (n : ℝ) * (x + latticeShift m) 0 =
      2 * Real.pi * (n : ℝ) * x 0 + ((n : ℤ) * m 0 : ℤ) * (2 * Real.pi) := by
    simp [latticeShift]
    ring
  simp only [h, Real.cos_add_int_mul_two_pi]

theorem cosDatum_meanZero (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    MeanZeroOn unitCube (fun x : Vec 2 => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) := by
  unfold MeanZeroOn
  rw [integral_unitCube_coord0 (fun s => c * Real.cos (2 * Real.pi * (n : ℝ) * s)),
    integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.cos x)
      (by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        positivity), integral_cos]
  have : Real.sin (2 * Real.pi * (n : ℝ)) = 0 := by
    rw [show 2 * Real.pi * (n : ℝ) = (n : ℕ) * (2 * Real.pi) by ring]
    have h := Real.sin_periodic.nat_mul n 0
    simpa using h
  simp [this]

theorem cosDatum_l2 (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    l2NormSq (fun x : Vec 2 => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) = c ^ 2 / 2 := by
  have := integral_unitCube_cos_sq n hn c 0
  simp only [add_zero] at this
  exact this

theorem cosDatum_spaceGrad (n : ℕ) (c : ℝ) (x : Vec 2) (i : Fin 2) :
    spaceGrad (fun x : Vec 2 => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) x i =
      (if i = 0 then 1 else 0) *
        (c * (2 * Real.pi * n) * Real.cos (2 * Real.pi * n * x 0 + Real.pi / 2)) := by
  have h := iteratedFDeriv_cosDatum c (2 * Real.pi * n) 1 x (fun _ => basisVec i)
  rw [iteratedFDeriv_one_apply] at h
  simp only [spaceGrad]
  rw [h]
  simp [basisVec_apply, eq_comm]

theorem cosDatum_gradNormSq (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    gradNormSq (spaceGrad (fun x : Vec 2 => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0))) =
      (4 * Real.pi ^ 2 * (n : ℝ) ^ 2) * (c ^ 2 / 2) := by
  have hpt : ∀ x : Vec 2, vecNormSq (spaceGrad (fun x : Vec 2 =>
      c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) x) =
      (c * (2 * Real.pi * n) * Real.cos (2 * Real.pi * n * x 0 + Real.pi / 2)) ^ 2 := by
    intro x
    simp [vecNormSq, vecDot, cosDatum_spaceGrad]
    ring
  unfold gradNormSq
  simp_rw [hpt]
  rw [integral_unitCube_cos_sq n hn (c * (2 * Real.pi * n)) (Real.pi / 2)]
  ring

theorem cosDatum_hessNormSq (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    hessNormSq (fun x : Vec 2 => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) =
      (2 * Real.pi * n) ^ 4 * (c ^ 2 / 2) := by
  have hf := contDiff_cosDatum c (2 * Real.pi * n)
  have hpt : ∀ x : Vec 2, (∑ i : Fin 2, ∑ j : Fin 2,
      (spaceGrad (fun y => spaceGrad (fun x : Vec 2 =>
        c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) y i) x j) ^ 2) =
      (c * (2 * Real.pi * n) ^ 2 *
        Real.cos (2 * Real.pi * n * x 0 + ((2 : ℕ) : ℝ) * (Real.pi / 2))) ^ 2 := by
    intro x
    have hh : ∀ i j : Fin 2, spaceGrad (fun y => spaceGrad (fun x : Vec 2 =>
        c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) y i) x j =
        (if j = 0 then 1 else 0) * ((if i = 0 then 1 else 0) *
          (c * (2 * Real.pi * n) ^ 2 *
            Real.cos (2 * Real.pi * n * x 0 + ((2 : ℕ) : ℝ) * (Real.pi / 2)))) := by
      intro i j
      have := hess2_eq_iterated hf i j x
      change hess2 _ i j x = _
      rw [this, iteratedFDeriv_cosDatum]
      simp [Fin.prod_univ_two, basisVec_apply, eq_comm]
    simp only [hh, Fin.sum_univ_two]
    simp
  unfold hessNormSq
  simp_rw [hpt]
  rw [integral_unitCube_cos_sq n hn (c * (2 * Real.pi * n) ^ 2) (((2 : ℕ) : ℝ) * (Real.pi / 2))]
  ring

theorem cosDatum_analytic (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    IsThetaAnalytic (1 / (2 * Real.pi * (n : ℝ)))
      (fun x : Vec 2 => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) := by
  intro k hk i
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < 2 * Real.pi * (n : ℝ) := by positivity
  have hint : ∫ x in unitCube, (iteratedFDeriv ℝ k
      (fun x : Vec 2 => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) x
        (fun j => basisVec (i j))) ^ 2 ≤
      (c ^ 2 / 2) * ((2 * Real.pi * n) ^ k * (k.factorial : ℝ)) ^ 2 := by
    have hpt : ∀ x : Vec 2, (iteratedFDeriv ℝ k
        (fun x : Vec 2 => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) x
          (fun j => basisVec (i j))) =
        (if ∀ j, i j = 0 then (1 : ℝ) else 0) *
          (c * (2 * Real.pi * n) ^ k * Real.cos (2 * Real.pi * n * x 0 + k * (Real.pi / 2))) := by
      intro x
      rw [iteratedFDeriv_cosDatum, prod_basisVec_zero]
    by_cases hz : ∀ j, i j = 0
    · have hif : (if ∀ j, i j = 0 then (1 : ℝ) else 0) = 1 := by simp [hz]
      simp_rw [hpt, hif, one_mul]
      rw [integral_unitCube_cos_sq n hn (c * (2 * Real.pi * n) ^ k) (k * (Real.pi / 2))]
      have hf1 : (1 : ℝ) ≤ k.factorial := Nat.one_le_cast.2 (Nat.factorial_pos k)
      have hak : 0 ≤ (2 * Real.pi * n) ^ k := by positivity
      have : (c * (2 * Real.pi * n) ^ k) ^ 2 / 2 = (c ^ 2 / 2) * ((2 * Real.pi * n) ^ k) ^ 2 := by
          ring
      rw [this]
      have h2 : ((2 * Real.pi * n) ^ k) ^ 2 ≤ ((2 * Real.pi * n) ^ k * (k.factorial : ℝ)) ^ 2 := by
        rw [mul_pow]
        have : (1 : ℝ) ≤ (k.factorial : ℝ) ^ 2 := one_le_pow₀ hf1
        nlinarith [pow_nonneg hak 2]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    · have hif : (if ∀ j, i j = 0 then (1 : ℝ) else 0) = 0 := by simp [hz]
      simp_rw [hpt, hif, zero_mul]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
      positivity
  have hQ : 0 ≤ (2 * Real.pi * n) ^ k * (k.factorial : ℝ) := by positivity
  have hR : (k.factorial : ℝ) / (1 / (2 * Real.pi * n)) ^ k = (2 * Real.pi * n) ^ k * (k.factorial
      : ℝ) := by
    rw [one_div, inv_pow]
    field_simp
  rw [hR, cosDatum_l2 n hn c]
  calc Real.sqrt _ ≤ Real.sqrt ((c ^ 2 / 2) * ((2 * Real.pi * n) ^ k * (k.factorial : ℝ)) ^ 2) :=
        Real.sqrt_le_sqrt hint
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hQ]

theorem cosineDatum : CosineDatumContract := by
  intro n hn c
  dsimp only
  have hf := contDiff_cosDatum c (2 * Real.pi * n)
  have hper := cosDatum_periodic n c
  refine ⟨hf, hper, cosDatum_meanZero n hn c, cosDatum_l2 n hn c,
    Infra.Section5.RelativeError.isPeriodicH1With_of_contDiff (hf.of_le (by simp)) hper, ?_, ?_,
    cosDatum_analytic n hn c⟩
  · rw [cosDatum_gradNormSq n hn c, cosDatum_l2 n hn c]
  · rw [cosDatum_hessNormSq n hn c, cosDatum_gradNormSq n hn c]
    apply le_of_eq
    have : (2 * Real.pi * n) ^ 4 = (4 * Real.pi ^ 2 * (n : ℝ) ^ 2) *
        (4 * Real.pi ^ 2 * (n : ℝ) ^ 2) := by ring
    rw [this]; ring

end AVenhance.Infra.FullTheorem.NoSelectionInputs
