/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersNonneg
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersProfile

/-! # TUpgrade Consumers Trace

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

theorem iterate_T_upgrade_of_initial_trace (β Ccut : ℝ) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
    ∀ (I : Ingredients β) (_hz : I.Czeta ≤ Ccut) (_hxi : I.Cxi ≤ Ccut)
      (_hh : I.Chat ≤ Ccut)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (κ : ℝ) (M : ℕ) {m : ℕ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (_hT : I.IsTIterates hΦ m (I.kappaAt κ m (M - m)) (I.kappaAt κ (m - 1)
        (M - (m - 1))) θ₀ θprev T)
    (_hθ : IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaAt κ (m - 1) (M - (m - 1))) (fun _ _ =>
        0) θ₀ θprev)
    (_hm : 2 ≤ m) (_hmM : m ≤ M) (_hPerm : κ ∈ permittedInterval β I.Λ M)
    (Rθ N : ℝ)
    (_hN : 0 ≤ N)
    (_hRθ : 0 < Rθ)
    (_hradius : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ)
    (_hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * C₀ ^ 3)⁻¹)
    (_hzero : I.kappaSeq κ M (m - 1) * spaceTimeGradNormSq
      (fun t => spaceGrad (θprev t)) ≤ N ^ 2)
    (_hInitialTrace : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in unitCube, (classicalWordDerivative w θ₀ x) ^ 2) ≤
        N * ((w.length.factorial : ℝ) / Rθ ^ w.length)),
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
  obtain ⟨c, Ck, hc, hcC, hu⟩ := iterate_T_upgrade_of_theta_nonneg β Ccut
  obtain ⟨cp, Cp, hcp, hcpC, hrec⟩ := AVenhance.l_recurse β Ccut
  let Cθ := 4 * max (thetaAnalyticRadiusBase cp) 2
  let C₀ := max (iterateReducedSourceConstant β Ccut c Ck 40 (2 ^ 10) Cθ)
    (8 * max (thetaAnalyticRadiusBase cp) 2)
  have hsource : iterateReducedSourceConstant β Ccut c Ck 40 (2 ^ 10) Cθ ≤ C₀ :=
    le_max_left _ _
  have hC1 : 1 ≤ C₀ := (iterate_source_constant_bounds _ _ _).1.trans
    ((le_max_right _ _).trans hsource)
  refine ⟨C₀, hC1, ?_⟩
  intro I hz hxi hh Φ hΦ κ M m θ₀ θprev T hT hθ hm hmM hPerm
    Rθ N hN hRθ hradius hsmall hzero hTrace
  have hM : 1 ≤ M := by omega
  have hper : κ ∈ permissibleSet β I.Λ :=
    Set.mem_iUnion.mpr ⟨M, Set.mem_iUnion.mpr ⟨hM, hPerm⟩⟩
  have hA5 := hrec I hz hxi hh κ hper M hM hPerm
  obtain ⟨_, _, hreg⟩ := AVenhance.stream_regularity β
  have hbase := theta_iterate_profile_of_initial_trace_nonneg_A3_A5 I Φ hΦ hm hmM (C₀ := C₀)
    hcp hcpC hN hRθ (le_max_right _ _) hradius hzero hTrace
    (fun j hj t n hn => (hreg I Φ hΦ j hj t).2.1 n hn)
    (fun j hj hjM => hA5.1 j hj hjM) hθ
  exact hu I hz hxi hh hΦ κ M hT hθ hm hmM hPerm Cθ Rθ C₀ N hN hRθ
    hsource hradius hsmall hbase

end AVenhance.Infra.Section4
