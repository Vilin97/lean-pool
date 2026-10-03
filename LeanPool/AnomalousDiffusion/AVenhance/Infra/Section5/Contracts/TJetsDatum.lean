/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJetsSecondOrder

/-! # Joint datum jets with one uniform coefficient -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5.Integration

/-- All jets needed by the source producers, with the same datum amplitude
and coefficient. The coefficient and threshold precede the ingredients. -/
theorem tJets_datum_contract (β Ccut : ℝ) :
    ∃ A C₁ : ℝ, 1 ≤ A ∧ OnA7Instances β Ccut C₁
      (fun I _Φ _hΦ κ M _R θ₀ m _θprev T =>
        let B := Real.sqrt (l2NormSq θ₀)
        TGradientContract β (I.kappaSeq κ M (m - 1)) T A B ∧
        TPositiveJetsContract I m T A B ∧
        FirstOrderGradJetContract I m (I.kappaSeq κ M (m - 1)) T A B ∧
        SecondOrderGradJetContract I m (I.kappaSeq κ M (m - 1)) T A B) := by
  obtain ⟨D, hD, ht⟩ := iterate_T_upgrade_of_analytic β Ccut
  let P := (4 : ℝ) ^ Nstar β * ((2 * Nstar β).factorial : ℝ)
  let F := (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ)
  let A := max 1 (max (4 * P) (max (4 * D ^ 3) (2 * (1 + F / 4))))
  have hA : 1 ≤ A := le_max_left _ _
  have hPA : 4 * P ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hDA : 4 * D ^ 3 ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hFA : 2 * (1 + F / 4) ≤ A :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have h2PA : 2 * P ≤ A := (by linarith only [hP] : 2 * P ≤ 4 * P).trans hPA
  obtain ⟨C₁, hscale⟩ := iterate_contract_scales β D hD
  refine ⟨A, C₁, hA, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ ha m hm hmM θprev T hθ hT
  obtain ⟨hm2, hradius, hsmall⟩ := hscale I hΛ R hR m hm
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hρ : 0 < epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) := Real.rpow_pos_of_pos he _
  have hu := ht I hz hx hh hΦ κ M hT hθ hm2 hmM hperm R hR hradius hsmall ha
  have hη := (iterate_T_source_scale he hR hD hradius hsmall).2.2
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hF : 0 ≤ F := by dsimp [F]; positivity
    have hb := mul_le_mul_of_nonneg_right hη hF
    have hc : 2 * (1 + D ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) * F) ≤ A := by
      apply le_trans _ hFA
      linarith only [hb]
    exact hu.1.trans (by
      simpa only [F, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (l2NormSq θ₀)))
  · apply iterate_positive_temperature_jets_of_word_bound (κ := I.kappaSeq κ M (m - 1))
      (fun t ht => tIterate_space_contDiff I hΦ hT hθ le_rfl ht.1)
      (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2 * P)
      (by positivity : 0 ≤ 4 * D ^ 3) hρ h2PA hDA
    intro v w hvw hv t ht ht1
    have hb := hu.2 v w hvw hv t ht ht1
    rw [iterate_source_frequency_eq he] at hb
    simpa only [P, Ingredients.kappaSeq, mul_assoc, mul_comm, mul_left_comm] using hb
  · intro i
    have hb := hu.2 [i] [i] rfl (by simp) 0 le_rfl (by norm_num)
    have hd := (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans hb
    simp only [List.length_singleton, Nat.factorial_one, Nat.cast_one, mul_one, pow_one] at hd
    rw [iterate_source_frequency_eq he] at hd
    have hc := mul_le_mul h2PA (div_le_div_of_nonneg_right hDA hρ.le)
      (by positivity : 0 ≤ (4 * D ^ 3) / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2))
      (by linarith only [hA] : 0 ≤ A)
    exact hd.trans (by
      simpa only [P, Ingredients.kappaSeq, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (l2NormSq θ₀)))
  · intro i j
    have hb := hu.2 [i, j] [i, j] rfl (by simp) 0 le_rfl (by norm_num)
    have hd := (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans hb
    simp only [List.length_cons, List.length_nil] at hd
    norm_num only [Nat.factorial] at hd
    rw [iterate_source_frequency_eq he] at hd
    apply secondOrderGradJet_bound_of_constants (P := 2 * P) (D := 4 * D ^ 3)
      (by positivity) (by positivity) (Real.sqrt_nonneg _) hρ
      (by calc 2 * (2 * P) = 4 * P := by ring
               _ ≤ A := hPA) hDA
    simpa only [P, Ingredients.kappaSeq, mul_assoc, mul_comm, mul_left_comm] using hd

end AVenhance.Infra.Section5.Contracts
