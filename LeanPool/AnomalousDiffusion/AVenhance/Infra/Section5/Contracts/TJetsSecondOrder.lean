/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJets

/-! # The integrated second-order T jet (`e.nabm2`, n = 2)

The two-letter word estimate includes the gradient energy. Its factorial is
absorbed in a coefficient chosen before the ingredients; the amplitude stays
abstract in the conditional producer.
-/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5.Integration

theorem secondOrderGradJet_bound_of_constants {P D A B r x : ℝ}
    (hP : 0 ≤ P) (hD : 0 ≤ D) (hB : 0 ≤ B) (hr : 0 < r)
    (hPA : 2 * P ≤ A) (hDA : D ≤ A)
    (hx : x ≤ B * P * 2 * (D / r) ^ 2) :
    x ≤ A * (A / r) ^ 2 * B := by
  have hA : 0 ≤ A := (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hP).trans hPA
  have hpow : (D / r) ^ 2 ≤ (A / r) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hD hr.le) (div_le_div_of_nonneg_right hDA hr.le) 2
  calc x ≤ B * P * 2 * (D / r) ^ 2 := hx
    _ = (2 * P) * (D / r) ^ 2 * B := by ring
    _ ≤ A * (A / r) ^ 2 * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hPA hpow (sq_nonneg _) hA) hB

/-- Exact abstract-amplitude second-order contract from the theta profile,
with its coefficient above the requested lower bound. -/
theorem secondOrderGradJet_of_thetaProfile_contract (β Ccut CsReq : ℝ) :
    ∃ Cs A C₁ : ℝ, CsReq ≤ Cs ∧ 1 ≤ Cs ∧ 1 ≤ A ∧
      OnA7Instances β Ccut C₁ (fun I _Φ _hΦ κ M _R _θ₀ m θprev T =>
        ∀ B : ℝ, 0 ≤ B →
          ThetaProfileContract I m (I.kappaSeq κ M (m - 1)) θprev Cs B →
          SecondOrderGradJetContract I m (I.kappaSeq κ M (m - 1)) T A B) := by
  obtain ⟨c, C, hc, hcC, ht⟩ := iterate_T_upgrade_of_theta_nonneg β Ccut
  let Cs := max CsReq (iterateReducedSourceConstant β Ccut c C 40 (2 ^ 10) 1)
  have hReqCs : CsReq ≤ Cs := le_max_left _ _
  have hSource : iterateReducedSourceConstant β Ccut c C 40 (2 ^ 10) 1 ≤ Cs := le_max_right _ _
  have hCs : 1 ≤ Cs := (iterate_source_constant_bounds _ _ _).1.trans
    ((le_max_right _ _).trans hSource)
  let P := (4 : ℝ) ^ Nstar β * ((2 * Nstar β).factorial : ℝ)
  let A := max 1 (max (2 * P) (4 * Cs ^ 3))
  have hA : 1 ≤ A := le_max_left _ _
  obtain ⟨C₁, hscale⟩ := iterate_contract_scales β Cs hCs
  refine ⟨Cs, A, C₁, hReqCs, hCs, hA, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ _ M _ hperm R hR θ₀ _ _ _ _ m hm hmM θprev T hθ hT B hB hbase
  obtain ⟨hm2, hradius, hsmall⟩ := hscale I hΛ R hR m hm
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hu := ht I hz hx hh hΦ κ M hT hθ hm2 hmM hperm 1 R Cs B hB hR
    hSource hradius hsmall hbase
  intro i j
  have hb := hu.2 [i, j] [i, j] rfl (by simp) 0 le_rfl (by norm_num)
  have hd := (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans hb
  simp only [List.length_cons, List.length_nil] at hd
  norm_num only [Nat.factorial] at hd
  rw [iterate_source_frequency_eq he] at hd
  exact secondOrderGradJet_bound_of_constants (by dsimp [P]; positivity) (by positivity : 0 ≤ 4 *
      Cs ^ 3)
    hB (Real.rpow_pos_of_pos he _)
    ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _)) (by simpa only [P, Ingredients.kappaSeq,
        mul_assoc] using hd)

end AVenhance.Infra.Section5.Contracts
