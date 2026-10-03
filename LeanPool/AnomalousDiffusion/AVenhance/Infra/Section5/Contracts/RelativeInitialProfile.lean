/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.RelativeInitialLayer
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LaterStart

/-! # Relative Initial Profile

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization AVenhance
open AVenhance.Infra.Section4 AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.Contracts

/-- Exact relative initial layer from the named positive-jet, gradient-profile,
and increment contracts. All constants precede the physical family. -/
theorem initialLayer_from_relative_profiles (β C₀ A Cs : ℝ) (hCs : 0 < Cs) :
    ∃ Ci C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ hΦ κ M R _g m θm θprev T =>
        let ν := I.kappaSeq κ M (m - 1)
        let S := Real.sqrt ν * Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (θprev t)))
        TPositiveJetsContract I m T A S →
        ThetaProfileContract I m ν θprev Cs S →
        VIncrementContract I m ν T Cs R S →
        InitialLayerContract I hΦ m (I.kappaSeq κ M m) θm T Ci S) := by
  obtain ⟨Cg, hCg, Lj, hj⟩ := RelativeError.relative_iterate_gradient_jets β Cs hCs
  obtain ⟨Ci, Li, hi⟩ := initialLayer_from_relative_jets β C₀ A Cg (max Cs 1) hCg (le_max_right _ _)
  obtain ⟨K, _, hK⟩ := LeftToShow.left_to_show_scales β C₀
  refine ⟨Ci, max Li Lj, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκp M hM hperm R hR g hg hgp hmean ha
    m hm0 hmM θm θprev T hu hp hT
  dsimp only
  intro hpositive hprofile hV
  have hm : 2 ≤ m := (mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR).1.trans hm0
  obtain ⟨hκm, hκle, -⟩ := hK I hz hx hh κ hκp M hM hperm m hm hmM
  have hν : 0 < I.kappaSeq κ M (m - 1) := hκm.trans_le hκle
  have hradius : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ R := by
    have hstar := mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR
    have he := RelativeError.epsilon_antitone I.one_lt_beta I.beta_lt I.two_pow_seven_le (by omega
        : mTheta0 β I.Λ R - 1 ≤ m - 1)
    have hγ := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
    exact (Real.rpow_le_rpow
      (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le he
      (by linarith : 0 ≤ 1 + gamma β / 2)).trans hstar.2
  have htrace := RelativeError.relative_initial_trace_one_of_positive_jets (funext
      (LeftToShow.tIterates_classicalSol hT).2.2.1) hpositive
  have hjets := hj I ((le_max_right Li Lj).trans hΛ) Φ hΦ κ M m hm g θprev T
    hκm hν hp hT _ R (by positivity) hradius hprofile hV
  exact hi I hz hx hh ((le_max_left Li Lj).trans hΛ) Φ hΦ κ hκp M hM hperm R hR g hg hgp hmean ha
    m hm0 hmM θm θprev T hu hp hT htrace hjets

end AVenhance.Infra.Section5.Contracts
