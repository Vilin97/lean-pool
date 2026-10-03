/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusivityComparison
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTSourceUpgrade
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMean
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaAtBounds

/-! # Iterates TA5Upgrade

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual-chain conditional T upgrade with stream-regularity/diffusivity-recursion. Its
    amplitude
is abstract and positive. The theta base excludes the scalar zeroth-order
supremum, and the mean comparison retains both E21c errors. -/
theorem iterate_T_upgrade_conditional_A3_A5_flow_material {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (κ : ℝ) (M : ℕ) {m : ℕ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m (I.kappaAt κ m (M - m)) (I.kappaAt κ (m - 1)
        (M - (m - 1))) θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaAt κ (m - 1) (M - (m - 1))) (fun _ _ =>
        0) θ₀ θprev)
    (hm : 2 ≤ m) (hmM : m ≤ M) (hκtop : 0 < κ)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (hflowp : ∀ t, 0 < t → ∀ l : ℤ, IsZ2Periodic (I.flowGrad hΦ m l t))
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {c Ck K Cflow Cmean Rflow Cθ Rθ C₀ N : ℝ}
    (hN : 0 < N)
    (hc : 0 < c) (hcC : c < Ck)
    (hA5 : ∀ j : ℕ, 1 ≤ j → j < M →
      c * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) ≤ I.kappaAt κ j (M - j) ∧
      I.kappaAt κ j (M - j) ≤ Ck * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β))) (hK : 0 ≤ K)
          (hCf : 0 ≤ Cflow) (hCm : 0 ≤ Cmean)
    (hRf : 256 ≤ Rflow) (hRθ : 0 < Rθ)
    (hC₀ : iterateSourceConstant
      (iterateBudgetUniversalConstant K Ck c ((2 : ℝ) ^ (-25 : ℤ)) Cflow Cmean) Rflow Cθ ≤ C₀)
    (hradius : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ)
    (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * C₀ ^ 3)⁻¹)
    (hKm : ∀ t j k, |I.Kmat (I.kappaAt κ m (M - m)) m t j k| ≤ K * (I.kappaAt κ (m - 1) (M - (m -
        1))))
    (hcondition : epsilon β I.Λ m ^ 2 ≤ (I.kappaAt κ m (M - m)) * tau β I.Λ m / 2)
    (hMeanScale : iterateMeanErrorBound I (I.kappaAt κ m (M - m)) m ≤
      (I.kappaAt κ (m - 1) (M - (m - 1))) * Cmean * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hzero : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ j k,
      |(I.flowGrad hΦ m l t x - 1) j k| ≤ Cflow * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hpositive : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ p : List (Fin 2), 1 ≤ p.length → ∀ j k,
      |iterateSpatialWord p (fun y => (I.flowGrad hΦ m l t y - 1) j k) x| ≤
        Cflow * (p.length.factorial : ℝ) * (Rflow / epsilon β I.Λ (m - 1)) ^ p.length)
    (hbase : iterateCoordinateEnergyProfile θprev (I.kappaAt κ (m - 1) (M - (m - 1))) N
      (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0) :
    (Real.sqrt (I.kappaAt κ (m - 1) (M - (m - 1))) * Real.sqrt (spaceTimeGradNormSq
      (fun t => spaceGrad (T (Nstar β) t))) ≤
      N * (1 + (C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β)) * (Nstar β : ℝ) * ((2 * Nstar
          β).factorial : ℝ))) ∧
    (∀ v w : List (Fin 2), v.length = w.length → 1 ≤ v.length →
      ∀ s, 0 ≤ s → s ≤ 1 →
      Real.sqrt (l2NormSq (iterateSpatialWord v (T (Nstar β) s))) +
        Real.sqrt (I.kappaAt κ (m - 1) (M - (m - 1))) *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (T (Nstar β)
            t)))) ≤
      N * (4 : ℝ) ^ Nstar β * ((2 * Nstar β).factorial : ℝ) * (v.length.factorial : ℝ) *
        ((4 * C₀ ^ 3) * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) ^ v.length) := by
  have hκm := Infra.Section3.kappaAt_pos I hκtop m (M - m)
  have hpoint := hA5 (m - 1) (by omega) (by omega)
  have hmean : ∀ j k, |(timeAvgMat (I.Kmat (I.kappaAt κ m (M - m)) m) -
      I.kappaAt κ (m - 1) (M - (m - 1)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
      I.kappaAt κ (m - 1) (M - (m - 1)) * Cmean *
        epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    intro j k
    have hn := iterate_mean_coefficient_bound I κ (by omega : 1 ≤ m) hmM hκm hcondition
    have he : |(timeAvgMat (I.Kmat (I.kappaAt κ m (M - m)) m) -
        I.kappaAt κ (m - 1) (M - (m - 1)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
        iterateMeanErrorBound I (I.kappaAt κ m (M - m)) m := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ k).trans ((norm_le_pi_norm _ j).trans hn)
    exact he.trans hMeanScale
  exact iterate_T_source_upgrade_of_diffusivity_and_flow
    (hκscale := iterate_kappaAt_abs_le_previous I hκtop (by omega) hmM) I hΦ hT hθ hm hκm
    hflow hflowp hA3 hN hc (hc.trans hcC).le hK hCf hCm hRf hRθ
    hpoint.1 hpoint.2 hC₀ hradius hsmall hKm hmean hzero hpositive hbase

end AVenhance.Infra.Section4
