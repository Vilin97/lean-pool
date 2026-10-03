/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowMixedEstimate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowAverage

/-! Actual mixed flow-average bounds for the temperature forcing coefficient. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- the left-Jacobian form's cutoff average has two flow factors in each summand. The
additional factor costs one Leibniz factor at every mixed order and changes no
spatial or material exponent. -/
theorem amnr_flowAverageA0Plus_mixed_of_flow_bounds {β : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) {X : ℝ} (hX : 0 ≤ X)
    (hflow : ∀ m, 1 ≤ m → ∀ (l : ℤ) (α : List (Fin 2)) n,
      α.length + 2 * n ≤ AVenhance.Nstar β → ∀ z : AmnrSpace,
      |z.1 - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
        AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m → ∀ i p,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord α n)
        (fun y => I.flowGrad hΦ m l y.1 y.2 i p) z| ≤
        X * (AVenhance.epsilon β I.Λ (m - 1) ^
          (-(1 + AVenhance.gamma β / 2))) ^ α.length *
          (AVenhance.tauP β I.Λ m)⁻¹ ^ n) :
    ∀ m, 1 ≤ m → ∀ j k i p w, IsAmnrMixedWord w →
      amnrBudget w ≤ AVenhance.Nstar β → ∀ z,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
        (amnrFlowAverageA0Plus I hΦ m j k i p) z| ≤
        (3 * (2 : ℝ) ^ AVenhance.Nstar β * I.Chat *
          (2 ^ AVenhance.Nstar β * X * X)) *
          amnrWeight (AVenhance.epsilon β I.Λ (m - 1) ^
            (-(1 + AVenhance.gamma β / 2)))
            (AVenhance.tauP β I.Λ m)⁻¹ w := by
  let N := AVenhance.Nstar β
  intro m hm j k i p w hw hbudget z
  let b := fun y : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) y.1 y.2
  let S := AVenhance.epsilon β I.Λ (m - 1) ^ (-(1 + AVenhance.gamma β / 2))
  let H := (AVenhance.tauP β I.Λ m)⁻¹
  have hS : 0 ≤ S := Real.rpow_nonneg
    (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _
  have hH : 0 ≤ H := inv_nonneg.mpr
    (AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  have hXprod : 0 ≤ (2 : ℝ) ^ N * X * X := by positivity
  have hb : ContDiffOn ℝ N b Set.univ :=
    (amnr_previous_velocity_contDiff I hΦ hm N).contDiffOn
  have hleft (l : ℤ) : ContDiffOn ℝ N
      (fun y : AmnrSpace => I.flowGrad hΦ m l y.1 y.2 j i) Set.univ :=
    ((amnr_flowGrad_joint_contDiff_infty I hΦ m l j i).of_le (by simp)).contDiffOn
  have hright (l : ℤ) : ContDiffOn ℝ N
      (fun y : AmnrSpace => I.flowGrad hΦ m l y.1 y.2 k p) Set.univ :=
    ((amnr_flowGrad_joint_contDiff_infty I hΦ m l k p).of_le (by simp)).contDiffOn
  have hproductBound (l : ℤ) (v : List (Option (Fin 2)))
      (hv : IsAmnrMixedWord v) (hvb : amnrBudget v ≤ N) (y : AmnrSpace)
      (ht : |y.1 - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
        AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m) :
      |amnrWord b v (fun y => I.flowGrad hΦ m l y.1 y.2 j i *
        I.flowGrad hΦ m l y.1 y.2 k p) y| ≤
        (2 : ℝ) ^ N * X * X * amnrWeight S H v := by
    have hflowSub (a b' : Fin 2) (q : List (Option (Fin 2)))
        (hq : q.Sublist v) :
      |amnrWord b q (fun y => I.flowGrad hΦ m l y.1 y.2 a b') y| ≤
        X * amnrWeight S H q := by
      obtain ⟨α, r, rfl⟩ := IsAmnrMixedWord.normalForm (hv.sublist hq)
      have hbq := (amnrBudget_sublist hq).trans hvb
      rw [amnrMixedWord_budget] at hbq
      rw [amnrMixedWord_weight]
      have hh := hflow m hm l α r hbq y ht a b'
      exact hh.trans_eq (by simp [S, H]; ring)
    have hprod := amnrWord_mul_abs_le_at isOpen_univ hb
      (hleft l) (hright l) hS hH hX hX v hvb (mem_univ y)
      (fun q hq => hflowSub j i q hq) (fun q hq => hflowSub k p q hq)
    have hpow : (2 : ℝ) ^ v.length ≤ 2 ^ N :=
      pow_le_pow_right₀ (by norm_num) ((amnrBudget_length_le v).trans hvb)
    have hW := amnrWeight_nonneg hS hH v
    have hcoeff := mul_le_mul_of_nonneg_right hpow (mul_nonneg (mul_nonneg hX hX) hW)
    exact hprod.trans (by simpa [S, H, mul_assoc] using hcoeff)
  have hmain := amnr_cutoff_word_abs_le I hm isOpen_univ hb
    (fun l y => I.flowGrad hΦ m l y.1 y.2 j i *
      I.flowGrad hΦ m l y.1 y.2 k p)
    (fun l => (hleft l).mul (hright l)) hS hXprod
    (fun l v hv hvb y _ ht => hproductBound l v hv hvb y ht)
    w hw hbudget (mem_univ z)
  change |amnrWord b w (fun y => ∑' l : ℤ,
    I.hatXiML m l y.1 * (I.flowGrad hΦ m l y.1 y.2 j i *
      I.flowGrad hΦ m l y.1 y.2 k p)) z| ≤ _
  simpa [N, S, H, mul_assoc] using hmain

end AVenhance.Infra.Section4
