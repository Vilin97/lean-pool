/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFlowClose
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTDischarge

/-! # Iterates TTheta Upgrade

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- Actual T upgrade with every flow interface discharged, using universal
Cflow=40 and Rflow=2^10. Only the quantitative theta base profile remains. -/
theorem iterate_T_upgrade_of_theta (β Ccut : ℝ) :
    ∃ c Ck : ℝ, 0 < c ∧ c < Ck ∧
    ∀ (I : Ingredients β) (_hz : I.Czeta ≤ Ccut) (_hxi : I.Cxi ≤ Ccut)
      (_hh : I.Chat ≤ Ccut)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (κ : ℝ) (M : ℕ) {m : ℕ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (_hT : I.IsTIterates hΦ m (I.kappaAt κ m (M - m)) (I.kappaAt κ (m - 1)
        (M - (m - 1))) θ₀ θprev T)
    (_hθ : IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaAt κ (m - 1) (M - (m - 1))) (fun _ _ =>
        0) θ₀ θprev)
    (_hm : 2 ≤ m) (_hmM : m ≤ M) (_hPerm : κ ∈ permittedInterval β I.Λ M)
    (Cθ Rθ C₀ N : ℝ)
    (_hN : 0 < N)
    (_hRθ : 0 < Rθ)
    (_hC₀ : iterateReducedSourceConstant β Ccut c Ck 40 (2 ^ 10) Cθ ≤ C₀)
    (_hradius : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ)
    (_hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * C₀ ^ 3)⁻¹)
    (_hbase : iterateCoordinateEnergyProfile θprev (I.kappaAt κ (m - 1) (M - (m - 1))) N
      (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0),
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
  obtain ⟨c, Ck, hc, hcC, hupgrade⟩ := iterate_T_upgrade_of_theta_flow_material β Ccut
  refine ⟨c, Ck, hc, hcC, ?_⟩
  intro I hz hxi hh Φ hΦ κ M m θ₀ θprev T hT hθ hm hmM hPerm
    Cθ Rθ C₀ N hN hRθ hC₀ hradius hsmall hbase
  exact hupgrade I hz hxi hh hΦ κ M hT hθ hm hmM hPerm
    (fun l => iterate_flowGrad_joint_smooth I hΦ m l)
    (fun t _ l => iterate_flowGrad_periodic I hΦ m l t)
    40 (2 ^ 10) Cθ Rθ C₀ N hN (by norm_num) (by norm_num) hRθ hC₀ hradius hsmall
    (fun t x l hn i j => iterate_flowGrad_zero_bound I hΦ (l := l) (t := t) hm hn x i j)
    (fun t x l hn w _ i j => iterate_flowGrad_word_bound I hΦ (l := l) (t := t) hm hn w x i j) hbase

end AVenhance.Infra.Section4
