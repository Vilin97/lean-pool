/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTAbstractUpgrade
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTSourceScale

/-! # Iterates TSource Upgrade

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Corrected positive-order l.Tm.reg.upgrade under the printed radius and
smallness conditions, with abstract amplitude and a gradient-only zero branch. -/
theorem iterate_T_source_upgrade_of_diffusivity_and_flow {β : ℝ} (I : Ingredients β)
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
    (hradius : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ)
    (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * C₀ ^ 3)⁻¹)
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
      (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0) :
    (Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
      (fun t => spaceGrad (T (Nstar β) t))) ≤
      N * (1 + (C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β)) * (Nstar β : ℝ) * ((2 * Nstar
          β).factorial : ℝ))) ∧
    (∀ v w : List (Fin 2), v.length = w.length → 1 ≤ v.length →
      ∀ s, 0 ≤ s → s ≤ 1 →
      Real.sqrt (l2NormSq (iterateSpatialWord v (T (Nstar β) s))) + Real.sqrt κprev *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (T (Nstar β)
            t)))) ≤
      N * (4 : ℝ) ^ Nstar β * ((2 * Nstar β).factorial : ℝ) * (v.length.factorial : ℝ) *
        ((4 * C₀ ^ 3) * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) ^ v.length) := by
  have hE := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have hC := (iterate_source_constant_bounds
    (iterateBudgetUniversalConstant K Ck c ((2 : ℝ) ^ (-25 : ℤ)) Cflow Cmean) Rflow Cθ).1.trans hC₀
  have hscale := iterate_T_source_scale hE hRθ hC hradius hsmall
  have hquarter : C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
      max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * Rθ ^ (-2 : ℤ)) ≤ 1 / 4 := by
    rw [hscale.1, mul_one]
    exact hscale.2.2
  have hb : iterateCoordinateEnergyProfile θprev κprev N
      (max (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (C₀ / Rθ)) 0 := by
    rw [hscale.2.1]
    exact hbase
  have ht := iterate_T_abstract_upgrade_of_diffusivity_and_flow (hκscale := hκscale) I hΦ hT hθ hm
      hκm hflow hflowp hA3
    hN hc hCk hK hCf hCm hRf hRθ hlower hupper hC₀ hquarter hKm hmean hzero hpositive hb
  refine ⟨?_, ?_⟩
  · simpa only [hscale.1, mul_one] using ht.1
  · intro v w hvw hv s hs hs1
    have hn := ht.2 v w hvw hv s hs hs1
    rw [hscale.2.1] at hn
    have hfreq := iterate_T_frequency_bound hC
      (Real.rpow_pos_of_pos hE (-1 - gamma β / 2)).le
    have hCp : 0 < C₀ := by linarith only [hC]
    have hp := pow_le_pow_left₀
      (by positivity : 0 ≤ 4 * (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2))) hfreq v.length
    exact hn.trans (mul_le_mul_of_nonneg_left hp (by positivity))
end AVenhance.Infra.Section4
