/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersTraceFrequency
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersFinal
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersV
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersContracts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs

/-! # TJets

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5.Integration

/-- All abstract-amplitude T and V contracts from the sole remaining theta
profile. The profile coefficient may exceed any requested lower bound.
Every coefficient and the scale threshold precedes the ingredients. -/
theorem tJets_of_thetaProfile_contract (β Ccut CsReq : ℝ) :
    ∃ Cs A C₁ : ℝ, CsReq ≤ Cs ∧ 1 ≤ Cs ∧ 1 ≤ A ∧
      OnA7Instances β Ccut C₁ (fun I _Φ _hΦ κ M R _θ₀ m θprev T =>
        ∀ N : ℝ, 0 ≤ N → ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs N →
          TGradientContract β (I.kappaSeq κ M (m - 1)) T A N ∧
          TPositiveJetsContract I m T A N ∧
          FirstOrderGradJetContract I m (I.kappaSeq κ M (m - 1)) T A N ∧
          FirstOrderSliceJetContract I m T (A ^ 2) N ∧
          VIncrementContract I m (I.kappaSeq κ M (m - 1)) T Cs R N) := by
  obtain ⟨ct, Ct, hct, hctC, ht⟩ := iterate_T_upgrade_of_theta_nonneg β Ccut
  obtain ⟨cv, Cv, hcv, hcvC, hv⟩ := iterate_V_upgrade_of_theta β Ccut
  let Cs := max CsReq (max (iterateReducedSourceConstant β Ccut ct Ct 40 (2 ^ 10) 1)
    (iterateReducedSourceConstant β Ccut cv Cv 40 (2 ^ 10) 1))
  have hReqCs : CsReq ≤ Cs := le_max_left _ _
  have hCt : iterateReducedSourceConstant β Ccut ct Ct 40 (2 ^ 10) 1 ≤ Cs :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCv : iterateReducedSourceConstant β Ccut cv Cv 40 (2 ^ 10) 1 ≤ Cs :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hCs : 1 ≤ Cs := (iterate_source_constant_bounds _ _ _).1.trans ((le_max_right _ _).trans hCt)
  let P := (4 : ℝ) ^ Nstar β * ((2 * Nstar β).factorial : ℝ)
  let F := (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ)
  let A := max 1 (max P (max (4 * Cs ^ 3) (1 + F / 4)))
  have hA : 1 ≤ A := le_max_left _ _
  have hPA : P ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hDA : 4 * Cs ^ 3 ≤ A := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hFA : 1 + F / 4 ≤ A := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨C₁, hscale⟩ := iterate_contract_scales β Cs hCs
  refine ⟨Cs, A, C₁, hReqCs, hCs, hA, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm hmM θprev T hθ hT N hN hbase
  obtain ⟨hm2, hradius, hsmall⟩ := hscale I hΛ R hR m hm
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hupgrade := ht I hz hx hh hΦ κ M hT hθ hm2 hmM hperm 1 R Cs N hN hR hCt hradius hsmall hbase
  have hη := (iterate_T_source_scale he hR hCs hradius hsmall).2.2
  have hzero : TGradientContract β (I.kappaSeq κ M (m - 1)) T A N := by
    have hF : 0 ≤ F := by positivity
    have hb := mul_le_mul_of_nonneg_right hη hF
    have hc : 1 + Cs ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) * F ≤ A := by
      apply le_trans _ hFA
      linarith only [hb]
    have hm := mul_le_mul_of_nonneg_left hc hN
    exact hupgrade.1.trans (by simpa only [F, mul_assoc, mul_comm A N] using hm)
  have hjet : TPositiveJetsContract I m T A N := by
    apply iterate_positive_temperature_jets_of_word_bound (κ := I.kappaAt κ (m - 1) (M - (m - 1)))
      (fun t ht => tIterate_space_contDiff I hΦ hT hθ le_rfl ht.1)
      hN (by dsimp [P]; positivity) (by positivity : 0 ≤ 4 * Cs ^ 3)
      (Real.rpow_pos_of_pos he _) hPA hDA
    intro v w hvw hv t ht ht1
    have hb := hupgrade.2 v w hvw hv t ht ht1
    rw [iterate_source_frequency_eq he] at hb
    simpa only [P, mul_assoc] using hb
  have hgrad : FirstOrderGradJetContract I m (I.kappaSeq κ M (m - 1)) T A N := by
    intro i
    have hb := hupgrade.2 [i] [i] rfl (by simp) 0 le_rfl (by norm_num)
    have hd := (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans hb
    simp only [List.length_singleton, Nat.factorial_one, Nat.cast_one, mul_one, pow_one] at hd
    rw [iterate_source_frequency_eq he] at hd
    have hρ : 0 < epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) := Real.rpow_pos_of_pos he _
    have hm := mul_le_mul hPA (div_le_div_of_nonneg_right hDA hρ.le)
      (by positivity : 0 ≤ (4 * Cs ^ 3) / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2))
      (by linarith only [hA] : 0 ≤ A)
    have hout := mul_le_mul_of_nonneg_left hm hN
    exact hd.trans (by simpa only [P, mul_assoc, mul_comm, mul_left_comm] using hout)
  have hslice : FirstOrderSliceJetContract I m T (A ^ 2) N := by
    intro i s hs
    have hb := hjet 1 (fun _ => i) (by norm_num) s hs
    simp only [iteratedFDeriv_one_apply, Nat.factorial_one, Nat.cast_one, mul_one, pow_one] at hb
    rw [Real.rpow_neg he.le]
    convert hb using 1
    all_goals first | rfl | ring
  exact ⟨hzero, hjet, hgrad, hslice,
    hv I hz hx hh hΦ κ M hT hθ hm2 hmM hperm 1 R Cs N hN hR hCv hradius hsmall hbase⟩

/-- The unconditional N-normalised ansatz jet, in the family block. -/
theorem firstOrderSliceJet_contract (β Ccut : ℝ) :
    ∃ AT C₁ : ℝ, OnA7Instances β Ccut C₁
      (fun I _Φ _hΦ _κ _M _R θ₀ m _θprev T =>
        FirstOrderSliceJetContract I m T AT (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨D, A, hD, hA, hb⟩ := iterate_T_analytic_consumer_bounds β Ccut
  obtain ⟨C₁, hscale⟩ := iterate_contract_scales β D hD
  refine ⟨A ^ 2, C₁, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ ha m hm hmM θprev T hθ hT
  obtain ⟨hm2, hradius, hsmall⟩ := hscale I hΛ R hR m hm
  exact (hb I hz hx hh hΦ κ M hT hθ hm2 hmM hperm R hR hradius hsmall ha).2.2

/-- The unconditional N-normalised integrated T gradient. -/
theorem tGradient_contract (β Ccut : ℝ) :
    ∃ A C₁ : ℝ, OnA7Instances β Ccut C₁
      (fun I _Φ _hΦ κ M _R θ₀ _m _θprev T =>
        TGradientContract β (I.kappaSeq κ M (_m - 1)) T A (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨D, A, hD, hA, hb⟩ := iterate_T_analytic_consumer_bounds β Ccut
  obtain ⟨C₁, hscale⟩ := iterate_contract_scales β D hD
  refine ⟨A, C₁, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ ha m hm hmM θprev T hθ hT
  obtain ⟨hm2, hradius, hsmall⟩ := hscale I hΛ R hR m hm
  exact (hb I hz hx hh hΦ κ M hT hθ hm2 hmM hperm R hR hradius hsmall ha).1

end AVenhance.Infra.Section5.Contracts
