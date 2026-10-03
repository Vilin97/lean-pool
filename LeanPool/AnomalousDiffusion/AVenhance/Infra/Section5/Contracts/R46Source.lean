/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.Produced
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46IteratesRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Proofs.Construction.StreamRegularity

/-! Conditional producer for the `R46` source-scale contract with an abstract amplitude.

The generic flux estimate uses Section 2 flow-distortion data and the n=0 previous-iterate energy
estimate. The big-bound estimate producer constructs the flow data through the Section 2 chain, so
    only the
`TGradientContract` remains a conditional input. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration

theorem R46Source.epsilon_two_delta_le_delta_r46Source (β : ℝ) (I : Ingredients β)
    (m : ℕ) :
    epsilon β I.Λ m ^ (2 * delta β) ≤ epsilon β I.Λ m ^ delta β := by
  have he : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he1 : epsilon β I.Λ m ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hd : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hpow : epsilon β I.Λ m ^ delta β ≤ 1 :=
    Real.rpow_le_one he.le he1 hd.le
  calc
    epsilon β I.Λ m ^ (2 * delta β) =
        epsilon β I.Λ m ^ delta β * epsilon β I.Λ m ^ delta β := by
      rw [show 2 * delta β = delta β + delta β by ring, Real.rpow_add he]
    _ ≤ epsilon β I.Λ m ^ delta β := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg he.le (delta β))

/-- `R46`'s space-time flux estimate with the amplitude left abstract. The energy premise is exactly
the `n = 0` gradient estimate represented by `TGradientContract`. -/
theorem r46TimeL2_flux_le_of_flowBounds_and_energy
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (Cmat : ℝ)
    (hflow : FlowBoundsData I Φ hΦ Cmat)
    (m : ℕ) (hm : 1 ≤ m) (κm κprev C B : ℝ)
    (T : ℝ → Vec 2 → ℝ)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hF : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ContDiff ℝ (⊤ : ℕ∞) (r46Flux I hΦ m κm T t))
    (hκm : 0 < κm) (hκprev : 0 < κprev) (hκ : κm ≤ κprev)
    (henergy : Real.sqrt κprev *
      Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T t) x)) ≤ C * B) :
    r46TimeL2 (fun t => r46Flux I hΦ m κm T t) ≤
      ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B) := by
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hd : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hroot : 0 < Real.sqrt κprev := Real.sqrt_pos.2 hκprev
  have hCB : 0 ≤ C * B := by
    exact (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans henergy
  have henergy' :
      Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T t) x)) ≤
        (C * B) / Real.sqrt κprev := by
    apply (le_div_iff₀ hroot).2
    calc
      _ = Real.sqrt κprev *
          Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T t) x)) := by ring
      _ ≤ C * B := henergy
  have hgrad :
      r46TimeL2 (fun t x => spaceGrad (T t) x) ≤
        ENNReal.ofReal ((C * B) / Real.sqrt κprev) := by
    rw [r46TimeL2_gradient_eq_spaceTime T hT]
    exact ENNReal.ofReal_le_ofReal henergy'
  have hratio : κm / Real.sqrt κprev ≤ Real.sqrt κm := by
    apply (div_le_iff₀ hroot).2
    calc
      κm = (Real.sqrt κm) ^ 2 := (Real.sq_sqrt hκm.le).symm
      _ = Real.sqrt κm * Real.sqrt κm := by ring
      _ ≤ Real.sqrt κm * Real.sqrt κprev :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hκ) (Real.sqrt_nonneg _)
  have hpow : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤
      epsilon β I.Λ (m - 1) ^ delta β :=
    R46Source.epsilon_two_delta_le_delta_r46Source β I (m - 1)
  have hpow_nonneg : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) :=
    Real.rpow_nonneg he.le _
  have hfactor :
      (κm / Real.sqrt κprev) * epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤
        Real.sqrt κm * epsilon β I.Λ (m - 1) ^ delta β := by
    calc
      _ ≤ Real.sqrt κm * epsilon β I.Λ (m - 1) ^ (2 * delta β) :=
        mul_le_mul_of_nonneg_right hratio hpow_nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)
  have hfactor' :
      (κm * epsilon β I.Λ (m - 1) ^ (2 * delta β)) *
        ((C * B) / Real.sqrt κprev) ≤
      C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B := by
    have hmul := mul_le_mul_of_nonneg_left hfactor hCB
    calc
      _ = (C * B) *
          ((κm / Real.sqrt κprev) * epsilon β I.Λ (m - 1) ^ (2 * delta β)) := by
        field_simp
      _ ≤ (C * B) *
          (Real.sqrt κm * epsilon β I.Λ (m - 1) ^ delta β) := hmul
      _ = _ := by ring
  have hcoeff : 0 ≤ κm * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    positivity
  have hsource := r46TimeL2_flux_le_of_flowBounds I hΦ Cmat hflow m hm κm T hT hF hκm.le
  calc
    _ ≤ ENNReal.ofReal (κm * epsilon β I.Λ (m - 1) ^ (2 * delta β)) *
        r46TimeL2 (fun t x => spaceGrad (T t) x) := hsource
    _ ≤ ENNReal.ofReal (κm * epsilon β I.Λ (m - 1) ^ (2 * delta β)) *
        ENNReal.ofReal ((C * B) / Real.sqrt κprev) := by gcongr
    _ = ENNReal.ofReal
        ((κm * epsilon β I.Λ (m - 1) ^ (2 * delta β)) *
          ((C * B) / Real.sqrt κprev)) := by rw [ENNReal.ofReal_mul hcoeff]
    _ ≤ ENNReal.ofReal
        (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B) :=
      ENNReal.ofReal_le_ofReal hfactor'

end AVenhance.Infra.Section5.Contracts

end
