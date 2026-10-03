/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVAbstractAmplitude
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTAnalyticAssembly

/-! # Iterates TAbstract Upgrade

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Actual conditional T analytic upgrade with abstract positive amplitude,
positive scalar orders, and a separate gradient-only zeroth-order bound.
The PDE increment estimates are proved internally. -/
theorem iterate_T_abstract_upgrade_of_diffusivity_and_flow {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hm : 2 ≤ m) (hκm : 0 < κm)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (hflowp : ∀ t, 0 < t → ∀ l : ℤ, IsZ2Periodic (I.flowGrad hΦ m l t))
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {c Ck K Cflow Cmean Rflow Cθ Rθ C₀ N : ℝ}
    (hN : 0 < N)
    (hc : 0 < c) (hCk : 0 ≤ Ck) (hK : 0 ≤ K) (hCf : 0 ≤ Cflow) (hCm : 0 ≤ Cmean)
    (hRf : 256 ≤ Rflow) (hRθ : 0 < Rθ)
    (hlower : c * (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)) ≤ κprev)
    (hupper : κprev ≤ Ck * (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)))
    (hC₀ : iterateSourceConstant
      (iterateBudgetUniversalConstant K Ck c ((2 : ℝ) ^ (-25 : ℤ)) Cflow Cmean) Rflow Cθ ≤ C₀)
    (hsmall : C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
      max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * Rθ ^ (-2 : ℤ)) ≤ 1 / 4)
    (hKm : ∀ t j k, |I.Kmat κm m t j k| ≤ K * κprev)
    (hmean : ∀ j k, |(timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
      κprev * Cmean * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hzero : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ j k,
      |(I.flowGrad hΦ m l t x - 1) j k| ≤ Cflow * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hpositive : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ p : List (Fin 2), 1 ≤ p.length → ∀ j k,
      |iterateSpatialWord p (fun y => (I.flowGrad hΦ m l t y - 1) j k) x| ≤
        Cflow * (p.length.factorial : ℝ) * (Rflow / epsilon β I.Λ (m - 1)) ^ p.length)
    (hκscale : |κm| ≤ κprev)
    (hbase : iterateCoordinateEnergyProfile θprev κprev N
      (max (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (C₀ / Rθ)) 0) :
    (Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
      (fun t => spaceGrad (T (Nstar β) t))) ≤
      N * (1 + (C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) * max 1 (epsilon β I.Λ (m - 1) ^ (2
          + gamma β) * Rθ ^ (-2 : ℤ))) * (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ))) ∧
    (∀ v w : List (Fin 2), v.length = w.length → 1 ≤ v.length →
      ∀ s, 0 ≤ s → s ≤ 1 →
      Real.sqrt (l2NormSq (iterateSpatialWord v (T (Nstar β) s))) + Real.sqrt κprev *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (T (Nstar β)
            t)))) ≤
      N * (4 : ℝ) ^ Nstar β * ((2 * Nstar β).factorial : ℝ) * (v.length.factorial : ℝ) *
        (4 * max (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (C₀ / Rθ)) ^ v.length) := by
  have hE := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have ha := Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have hκ : 0 < κprev :=
    (mul_pos hc (mul_pos ha (Real.rpow_pos_of_pos hE _))).trans_le hlower
  let L := max (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (C₀ / Rθ)
  let η := C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
    max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * Rθ ^ (-2 : ℤ))
  have hCp : 0 < C₀ := by
    have ht := (iterate_source_constant_bounds
      (iterateBudgetUniversalConstant K Ck c ((2 : ℝ) ^ (-25 : ℤ)) Cflow Cmean) Rflow Cθ).1.trans
          hC₀
    linarith only [ht]
  have hL : 0 ≤ L := le_trans (by positivity) (le_max_left _ _)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hV := iterate_V_abstract_amplitude_of_diffusivity_and_flow (hκscale := hκscale) I hΦ hT hθ
      hm hκm hflow hflowp hA3
    hN hc hCk hK hCf hCm hRf hRθ hlower hupper hC₀
    (hsmall.trans (by norm_num)) hKm hmean hzero hpositive hbase
  constructor
  · apply iterate_T_zero_gradient_relative_of_increment_bounds I hΦ hT hθ.1 hN.le hη (hsmall.trans
      (by norm_num))
    · have hb := iterate_profile_gradient_norm hκ hN.le hL hbase []
      simpa only [iterateSpatialWord, iterateAnalyticWeight, List.length_nil, Nat.mul_zero,
        Nat.add_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one] using hb
    · intro i hi0 hi
      have hb := hV i hi0 hi [] [] rfl 0 (by norm_num) (by norm_num)
      have hh := (le_add_of_nonneg_left (Real.sqrt_nonneg
        (l2NormSq (iterateSpatialWord [] (iterateIncrement T i 0))))).trans hb
      simpa only [iterateSpatialWord, iterateAnalyticWeight, List.length_nil, Nat.zero_add,
        pow_zero, mul_one] using hh
  · exact iterate_T_positive_analytic_of_increment_bounds I hΦ hT hθ.1 hκ hN.le hL hη hsmall hbase
      hV

end AVenhance.Infra.Section4
