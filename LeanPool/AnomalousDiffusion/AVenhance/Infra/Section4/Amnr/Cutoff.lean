/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.Seed

/-! Actual large-cutoff support, local finiteness, and mixed derivative bounds. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- The actual support lies in the closed source window. -/
theorem amnr_hatXi_support {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) {t : ℝ} (ht : I.hatXiML m l t ≠ 0) :
    t ∈ Set.Icc ((l - 1 / 2) * AVenhance.tauPP β I.Λ m - AVenhance.tauP β I.Λ m)
      ((l + 1 / 2) * AVenhance.tauPP β I.Λ m + AVenhance.tauP β I.Λ m) := by
  by_contra hnot
  have hh := I.hatXi_le m hm l t
  rw [AVenhance.indIcc_eq_zero_of_not_mem hnot] at hh
  exact ht (le_antisymm hh (Ingredients.hatXiML_mem_Icc I hm l t).1)

/-- Distance form of the source support window. -/
theorem amnr_hatXi_support_radius {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) {t : ℝ} (ht : I.hatXiML m l t ≠ 0) :
    |t - l * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m := by
  have hh := amnr_hatXi_support I hm l ht
  apply abs_le.mpr
  constructor <;> linarith [hh.1, hh.2]

/-- At most three lattice indices occur in a fixed small neighborhood of a
specified time. This is a local support statement, not just pointwise finiteness. -/
theorem amnr_hatXi_local_finite {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    ∃ s : Finset ℤ, s.card ≤ 3 ∧
      ∀ u : ℝ, |u - t| < AVenhance.tauPP β I.Λ m / 8 →
        ∀ l : ℤ, l ∉ s → I.hatXiML m l u = 0 := by
  classical
  let τ := AVenhance.tauPP β I.Λ m
  have hτ : 0 < τ := I.tauPP_pos' m
  have hP : 4 * AVenhance.tauP β I.Λ m ≤ τ :=
    AVenhance.Infra.Cutoff.four_tauP_le_tauPP I.one_lt_beta I.beta_lt I.two_pow_seven_le
  let a : ℤ := ⌊t / τ⌋
  refine ⟨Finset.Icc (a - 1) (a + 1), ?_, ?_⟩
  · simp only [Int.card_Icc]
    omega
  · intro u hu l hl
    by_contra hne
    have hsup := amnr_hatXi_support_radius I hm l hne
    have habs : |t - l * τ| < τ := by
      have htri := abs_add_le (t - u) (u - l * τ)
      have heq : t - l * τ = (t - u) + (u - l * τ) := by ring
      rw [← heq, abs_sub_comm t u] at htri
      change |u - l * τ| ≤ τ / 2 + AVenhance.tauP β I.Λ m at hsup
      linarith
    have hfloor : (a : ℝ) ≤ t / τ := Int.floor_le (t / τ)
    have hceil : t / τ < (a : ℝ) + 1 := Int.lt_floor_add_one (t / τ)
    have hdist := abs_lt.mp habs
    have htlo : (a : ℝ) * τ ≤ t := (le_div_iff₀ hτ).mp hfloor
    have hthi : t < ((a : ℝ) + 1) * τ := (div_lt_iff₀ hτ).mp hceil
    have hli : a - 1 ≤ l ∧ l ≤ a + 1 := by
      constructor
      · have : (a : ℝ) - 1 < (l : ℝ) := by nlinarith [hdist.2]
        have : a - 1 < l := by exact_mod_cast this
        omega
      · have : (l : ℝ) < (a : ℝ) + 2 := by nlinarith [hdist.1]
        have : l < a + 2 := by exact_mod_cast this
        omega
    exact hl (Finset.mem_Icc.mpr hli)

/-- The source derivative bound, expressed without weighted denominators. -/
theorem amnr_hatXi_derivative_abs_le {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) {j : ℕ} (hj : j ≤ AVenhance.Nstar β) (t : ℝ) :
    |iteratedDeriv j (I.hatXiML m l) t| ≤
      I.Chat * (AVenhance.tauP β I.Λ m)⁻¹ ^ j := by
  have hτ : 0 < AVenhance.tauP β I.Λ m :=
    AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hh := I.hatXi_deriv_le m hm l j hj t
  change AVenhance.tauP β I.Λ m ^ j * |iteratedDeriv j (I.hatXiML m l) t| ≤ I.Chat at hh
  rw [inv_pow, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hτ j)).mpr (by simpa only [mul_comm] using hh)

/-- Mixed derivatives of the actual cutoff use only its source time bounds. -/
theorem amnr_hatXi_mixed_abs_le {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) {b : AmnrSpace → Vec 2} {S : ℝ} (hS : 0 ≤ S)
    (w : List (Option (Fin 2))) (hw : IsAmnrMixedWord w)
    (hbudget : amnrBudget w ≤ AVenhance.Nstar β) (z : AmnrSpace) :
    |amnrWord b w (fun y => I.hatXiML m l y.1) z| ≤
      I.Chat * amnrWeight S (AVenhance.tauP β I.Λ m)⁻¹ w := by
  obtain ⟨α, ℓ, rfl⟩ := hw.normalForm
  rw [amnrMixedWord_budget] at hbudget
  have hf : ContDiff ℝ (AVenhance.Nstar β) (I.hatXiML m l) := by
    unfold AVenhance.Ingredients.hatXiML AVenhance.shiftCutoff
    exact ((I.hatXi_smooth m).comp (by fun_prop)).of_le (by simp)
  rw [amnrWord_timeOnly_mixed hf α ℓ (by omega), amnrMixedWord_weight]
  by_cases ha : α = []
  · rw [ite_eq_left ha]
    simpa only [ha, List.length_nil, pow_zero, one_mul] using
      amnr_hatXi_derivative_abs_le I hm l (by omega) z.1
  · rw [ite_eq_right ha]
    simp only [Pi.zero_apply, abs_zero]
    have hC : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
    have hτ : 0 < AVenhance.tauP β I.Λ m :=
      AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    positivity

/-- Every directional word annihilates the zero function. -/
theorem amnrWord_zero (b : AmnrSpace → Vec 2) (w : List (Option (Fin 2))) :
    amnrWord b w (0 : AmnrSpace → ℝ) = 0 := by
  induction w with
  | nil => rfl
  | cons d w ih =>
    simp only [amnrWord, ih]
    funext z
    simp [amnrOp]

/-- Outside the closed source window, every jet of the cutoff-flow product
vanishes by locality, including jets at zero values of the cutoff. -/
theorem amnr_hatXi_product_word_zero {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (f : AmnrSpace → ℝ) (b : AmnrSpace → Vec 2)
    (w : List (Option (Fin 2))) (z : AmnrSpace)
    (hfar : AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m <
      |z.1 - l * AVenhance.tauPP β I.Λ m|) :
    amnrWord b w ((fun y => I.hatXiML m l y.1) * f) z = 0 := by
  let V := {y : AmnrSpace | AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m <
    |y.1 - l * AVenhance.tauPP β I.Λ m|}
  have hV : IsOpen V := isOpen_lt continuous_const (by fun_prop)
  have heq : Set.EqOn ((fun y => I.hatXiML m l y.1) * f) (0 : AmnrSpace → ℝ) V := by
    intro y hy
    have hz : I.hatXiML m l y.1 = 0 := by
      by_contra hne
      exact (not_lt_of_ge (amnr_hatXi_support_radius I hm l hne)) hy
    simp only [Pi.mul_apply, Pi.zero_apply, hz, zero_mul]
  have hh := amnrWord_congr hV (b := b) heq w hfar
  simpa only [amnrWord_zero, Pi.zero_apply] using hh

end AVenhance.Infra.Section4
