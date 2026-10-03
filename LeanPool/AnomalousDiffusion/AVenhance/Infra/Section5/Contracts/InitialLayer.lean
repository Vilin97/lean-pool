/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.RelativeInitialProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.ThetaProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceInstanceContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIInitial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LaterStart
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MStar
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse

/-! # Conditional assembly of the step-down estimate initial-layer contract from the Hm bound -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization Filter Topology

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5
  AVenhance.Infra.Section5.Integration

/-- Assemble the exact step-down estimate initial-layer contract from the matching positive-time
    `HmSupContract`.
The sole additional premise is exposed as a conditional helper; the exact family producer still
requires a proof that the `Hm` bound follows from the step-down estimate data. -/
theorem initialLayer_from_HmSup (β C₀ CHs : ℝ) :
    ∃ Cᵢ C₁ : ℝ,
      OnA8Instances β C₀ C₁ (fun I _Φ hΦ κ M _R θ₀ m θm _θprev T =>
        HmSupContract I hΦ m (I.kappaSeq κ M m) θ₀ T CHs →
          InitialLayerContract I hΦ m (I.kappaSeq κ M m) θm T Cᵢ
            (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨c, C, hc, hcC, hrec⟩ := AVenhance.l_recurse β C₀
  let Cᵢ := CHs + 2 + 8 * (max (max 1 (min c (1 / 2))⁻¹)
    (1 + Infra.Ingredients.supergeoConstant β)) ^ 2 * (Real.sqrt 2 + 1)
  refine ⟨Cᵢ, 0, ?_⟩
  intro I hCzeta hCxi hChat _hC₁ _Φ hΦ κ hpermissible M hM hPerm _R hR θ₀ _hθ₀smooth
    _hθ₀periodic hmean hanalytic m hm0 hmM θm _θprev T hθm hθprev hT hHmSup
  have hm : 2 ≤ m := by
    exact (mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR).1.trans hm0
  have hscale : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ _R := by
    have hstar := mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR
    have hmono : epsilon β I.Λ (m - 1) ≤ epsilon β I.Λ (mTheta0 β I.Λ _R - 1) :=
      AVenhance.Infra.Section5.RelativeError.epsilon_antitone
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (by omega)
    have hexp : 0 ≤ 1 + gamma β / 2 := by
      have hγ := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
      linarith
    exact (Real.rpow_le_rpow
      (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
      hmono hexp).trans hstar.2
  have hA5 := hrec I hCzeta hCxi hChat κ hpermissible M hM hPerm
  have hHm : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t)) ≤
        CHs * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) := by
    intro t ht
    exact hHmSup t ht
  by_cases hNpos : 0 < Real.sqrt (l2NormSq θ₀)
  · have hCHs : 0 ≤ CHs := by
      have hAtOne := hHm 1 ⟨by norm_num, by norm_num⟩
      have he : 0 < epsilon β I.Λ (m - 1) ^ delta β :=
        Real.rpow_pos_of_pos
          (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) _
      have hmul : 0 < epsilon β I.Λ (m - 1) ^ delta β *
          Real.sqrt (l2NormSq θ₀) := mul_pos he hNpos
      by_contra hneg
      have hstrict : CHs * (epsilon β I.Λ (m - 1) ^ delta β *
          Real.sqrt (l2NormSq θ₀)) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hmul
      have hnonneg := Real.sqrt_nonneg
        (l2NormSq (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) 1))
      nlinarith [hAtOne]
    have hκ : 0 < κ :=
      (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
        (Real.rpow_pos_of_pos
          (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) _)).trans_le hPerm.1
    have hpositive := partI_initial_right_limit_of_A5_and_Hm_of_positive_data
      I hΦ hm hmM hκ hPerm hM hCzeta hCxi hChat hpermissible hc hcC hA5
      hNpos hθm hθprev hT hR hscale hmean hanalytic hCHs hHm
    simpa [InitialLayerContract, Cᵢ] using hpositive
  · have hNzero : Real.sqrt (l2NormSq θ₀) = 0 :=
      le_antisymm (le_of_not_gt hNpos) (Real.sqrt_nonneg _)
    have hκ : 0 < κ :=
      (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
        (Real.rpow_pos_of_pos
          (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) _)).trans_le hPerm.1
    have hκm : 0 < I.kappaSeq κ M m :=
      (chiSup_analytic_scale_of_A5 I hm hmM hκ hPerm hM hCzeta hCxi hChat
        hpermissible hc hcC hA5 hR hscale).1
    have hzero := partI_initial_zero_defect_of_A5_and_Hm I hΦ hm hmM hc hA5
      hNzero hκm hθm hθprev hT hHm
    have hsmall : {s : ℝ | s < 1} ∈ 𝓝[>] (0 : ℝ) := by
      have hnear : {s : ℝ | s < 1} ∈ 𝓝 (0 : ℝ) :=
        (isOpen_lt continuous_id continuous_const).mem_nhds (by norm_num)
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear
    filter_upwards [hsmall, self_mem_nhdsWithin] with s hs hspos
    have hsone : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨hspos, le_of_lt hs⟩
    have hdefect := hzero s hsone
    rw [hdefect]
    simp [Cᵢ, hNzero]

end AVenhance.Infra.Section5.Contracts

end
