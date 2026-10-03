/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyExponent
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyCoeff
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAmplitude
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHigherEnergyBudget

/-! # `TinyHMinusSourceContract` producer: scalar bookkeeping

The `L²_{t,x}` energies of the word gradients of the last increment are controlled by
`VIncrementContract` at the index `N*`; this file turns that contract into the explicit bound
`√κ_{m-1} √Q_w ≤ G` and proves the corrector size `|χTilde| ≤ K`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
  AVenhance.Infra.Section4

theorem sc_gamma_le_one {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) : gamma β ≤ 1 := by
  rw [Numeric.gamma_eq_beta_fraction hβ]
  rw [div_le_one (by linarith)]
  nlinarith

theorem sc_length_le_two_of_mem {w : List (Fin 2)} (hw : w ∈ scWords2) : w.length ≤ 2 := by
  simp only [scWords2, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- **The contract `VIncrementContract` at the index `N*`, in explicit form.** -/
theorem sc_Q_le {β : ℝ} (I : Ingredients β) (m : ℕ) {κprev : ℝ} (T : ℕ → ℝ → Vec 2 → ℝ)
    {Cs Rθ B : ℝ} (hCs : 0 ≤ Cs) (hB : 0 ≤ B)
    (hRθ : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ)
    (hV : VIncrementContract I m κprev T Cs Rθ B) {w : List (Fin 2)} (hw : w ∈ scWords2) :
    Real.sqrt κprev * Real.sqrt
        (spaceTimeGradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w)) ≤
      B * (Cs ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β)) ^ ((Nstar β : ℝ) / 2) *
        (((2 * Nstar β + 2).factorial : ℕ) : ℝ) *
        (max 1 Cs * epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) ^ 2 := by
  set x := epsilon β I.Λ (m - 1) with hx
  have hx0 : 0 < x := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hx1 : x ≤ 1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)
  have hγ := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
  have hN1 := sc_one_le_Nstar I.one_lt_beta I.beta_lt
  have hN256 := Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
  have h := hV (Nstar β) hN1 le_rfl w w rfl 0 le_rfl zero_le_one
  have hsq0 := Real.sqrt_nonneg (l2NormSq (iterateSpatialWord w (iterateIncrement T (Nstar β) 0)))
  have h' : Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
      (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T (Nstar β) t)))) ≤
      B * iterateAmplitude (Cs ^ 3 * x ^ (2 * delta β) *
        max 1 (x ^ (2 + gamma β) * Rθ ^ (-2 : ℤ))) (Nstar β) *
      iterateAnalyticWeight w.length (Nstar β)
        (max (Cs * x ^ (-1 - gamma β / 2)) (Cs / Rθ)) := by linarith
  -- the exponent `η`
  have hRpos : 0 < Rθ := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hRθ
  have hmax : max 1 (x ^ (2 + gamma β) * Rθ ^ (-2 : ℤ)) = 1 := by
    apply max_eq_left
    have h1 : x ^ (2 + gamma β) ≤ Rθ ^ 2 := by
      have : (x ^ (1 + gamma β / 2)) ^ 2 = x ^ (2 + gamma β) := by
        rw [sc_rpow_sq hx0]; congr 1; ring
      rw [← this]
      exact pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hRθ 2
    rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact h1
  have hamp : iterateAmplitude (Cs ^ 3 * x ^ (2 * delta β) *
      max 1 (x ^ (2 + gamma β) * Rθ ^ (-2 : ℤ))) (Nstar β) =
      (Cs ^ 3 * x ^ (2 * delta β)) ^ ((Nstar β : ℝ) / 2) := by
    rw [hmax, mul_one]
    unfold iterateAmplitude
    have h1 : ¬ (Nstar β = 0) := by omega
    have h2 : ¬ (Nstar β ≤ 2) := by omega
    simp [h1, h2]
  rw [hamp] at h'
  -- the weight
  have hL' : 1 ≤ max 1 Cs * x ^ (-(1 + gamma β / 2)) := by
    have h1 : 1 ≤ x ^ (-(1 + gamma β / 2)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx0 hx1 (by linarith)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ max 1 Cs * x ^ (-(1 + gamma β / 2)) :=
        mul_le_mul (le_max_left _ _) h1 zero_le_one (by positivity)
  have hLle : max (Cs * x ^ (-1 - gamma β / 2)) (Cs / Rθ) ≤
      max 1 Cs * x ^ (-(1 + gamma β / 2)) := by
    have hneg : x ^ (-1 - gamma β / 2) = x ^ (-(1 + gamma β / 2)) := by
      congr 1; ring
    apply max_le
    · rw [hneg]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx0.le _)
    · calc Cs / Rθ ≤ Cs / x ^ (1 + gamma β / 2) :=
            div_le_div_of_nonneg_left hCs (Real.rpow_pos_of_pos hx0 _) hRθ
        _ = Cs * x ^ (-(1 + gamma β / 2)) := by
            rw [Real.rpow_neg hx0.le, div_eq_mul_inv]
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx0.le _)
  have hL0 : 0 ≤ max (Cs * x ^ (-1 - gamma β / 2)) (Cs / Rθ) :=
    (mul_nonneg hCs (Real.rpow_nonneg hx0.le _)).trans (le_max_left _ _)
  have hlen : w.length ≤ 2 := sc_length_le_two_of_mem hw
  have hweight : iterateAnalyticWeight w.length (Nstar β)
      (max (Cs * x ^ (-1 - gamma β / 2)) (Cs / Rθ)) ≤
      (((2 * Nstar β + 2).factorial : ℕ) : ℝ) * (max 1 Cs * x ^ (-(1 + gamma β / 2))) ^ 2 := by
    unfold iterateAnalyticWeight
    have hf : (((w.length + 2 * Nstar β).factorial : ℕ) : ℝ) ≤
        (((2 * Nstar β + 2).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hp : (max (Cs * x ^ (-1 - gamma β / 2)) (Cs / Rθ)) ^ w.length ≤
        (max 1 Cs * x ^ (-(1 + gamma β / 2))) ^ 2 :=
      (pow_le_pow_left₀ hL0 hLle _).trans (pow_le_pow_right₀ hL' hlen)
    exact mul_le_mul hf hp (by positivity) (Nat.cast_nonneg _)
  have hη0 : 0 ≤ (Cs ^ 3 * x ^ (2 * delta β)) ^ ((Nstar β : ℝ) / 2) :=
    Real.rpow_nonneg (mul_nonneg (pow_nonneg hCs 3) (Real.rpow_nonneg hx0.le _)) _
  calc _ ≤ B * (Cs ^ 3 * x ^ (2 * delta β)) ^ ((Nstar β : ℝ) / 2) *
        iterateAnalyticWeight w.length (Nstar β)
          (max (Cs * x ^ (-1 - gamma β / 2)) (Cs / Rθ)) := h'
    _ ≤ B * (Cs ^ 3 * x ^ (2 * delta β)) ^ ((Nstar β : ℝ) / 2) *
        ((((2 * Nstar β + 2).factorial : ℕ) : ℝ) * (max 1 Cs * x ^ (-(1 + gamma β / 2))) ^ 2) :=
        mul_le_mul_of_nonneg_left hweight (mul_nonneg hB hη0)
    _ = _ := by ring

/-- Summing the seven word energies. -/
theorem sc_sqrt_sum_le {κp G c : ℝ} (hκp : 0 < κp) (hG : 0 ≤ G) (hc : 0 ≤ c)
    {Q : List (Fin 2) → ℝ} (hQ0 : ∀ w, 0 ≤ Q w)
    (hQ : ∀ w ∈ scWords2, Real.sqrt κp * Real.sqrt (Q w) ≤ G) :
    Real.sqrt (c * ∑ w ∈ scWords2, Q w) ≤ Real.sqrt (7 * c) * (G / Real.sqrt κp) := by
  have hs : 0 < Real.sqrt κp := Real.sqrt_pos.2 hκp
  have hQw : ∀ w ∈ scWords2, Q w ≤ (G / Real.sqrt κp) ^ 2 := by
    intro w hw
    have h1 : Real.sqrt (Q w) ≤ G / Real.sqrt κp := by
      rw [le_div_iff₀ hs]; linarith [hQ w hw]
    calc Q w = Real.sqrt (Q w) ^ 2 := (Real.sq_sqrt (hQ0 w)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hsum : ∑ w ∈ scWords2, Q w ≤ 7 * (G / Real.sqrt κp) ^ 2 := by
    calc ∑ w ∈ scWords2, Q w ≤ ∑ _w ∈ scWords2, (G / Real.sqrt κp) ^ 2 :=
          Finset.sum_le_sum hQw
      _ = 7 * (G / Real.sqrt κp) ^ 2 := by rw [Finset.sum_const, sc_card_scWords2]; simp
  calc Real.sqrt (c * ∑ w ∈ scWords2, Q w) ≤ Real.sqrt (c * (7 * (G / Real.sqrt κp) ^ 2)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsum hc)
    _ = Real.sqrt (7 * c) * (G / Real.sqrt κp) := by
        rw [show c * (7 * (G / Real.sqrt κp) ^ 2) = (7 * c) * (G / Real.sqrt κp) ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- The corrector size `|χTilde_{m,k}| ≤ K` from the scale package. -/
theorem sc_chiTilde_le {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm K : ℝ} (hKnn : 0 ≤ K) (hκm : 0 < κm)
    (hK4 : a β I.Λ m * epsilon β I.Λ m ^ 2 / κm ≤ K * epsilon β I.Λ m ^ (-gamma β))
    (k : ℤ) (t : ℝ) (x : Vec 2) (j : Fin 2) : |I.chiTilde hΦ m κm k t x j| ≤ K := by
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hε1 : epsilon β I.Λ m ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
      (by exact_mod_cast I.two_pow_seven_le)
  have ha : 0 ≤ a β I.Λ m := (Real.rpow_pos_of_pos hε _).le
  have hγ := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
  have hγ1 := sc_gamma_le_one I.one_lt_beta I.beta_lt
  have h1 := (Infra.Section3.chiMK_component_abs_le I hm κm hκm k t
    (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j).trans
    (RelativeError.corrector_size_le ha hε hκm)
  calc |I.chiTilde hΦ m κm k t x j| ≤ epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) := h1
    _ ≤ epsilon β I.Λ m * (K * epsilon β I.Λ m ^ (-gamma β)) :=
        mul_le_mul_of_nonneg_left hK4 hε.le
    _ = K * epsilon β I.Λ m ^ (1 - gamma β) := by
        rw [sub_eq_add_neg, Real.rpow_add hε, Real.rpow_one]; ring
    _ ≤ K * 1 := mul_le_mul_of_nonneg_left (Real.rpow_le_one hε.le hε1 (by linarith)) hKnn
    _ = K := mul_one K

end AVenhance.Infra.Section5.Contracts
