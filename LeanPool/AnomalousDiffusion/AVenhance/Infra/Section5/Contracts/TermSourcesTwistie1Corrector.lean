/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BracketFF
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.SpaceErgodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ErgodicParams

/-! # The corrector `χ_{m,k}` as the fast factor of the `twistie1` ergodic estimate

For each component `j`, `g = χ_{m,k}(t,·)_j = -τ_k(t) (u_{m,k})_j` is `ε_m`-periodic (fast periodic
at the integer frequency `ε_m⁻¹`), has zero cell mean (it is a constant times a coordinate cosine of
integer frequency), and is bounded by `ε_m · (a_m ε_m²/κ_m)` (`e.corrm`). -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Ergodic

/-- `∫₀¹ cos(2π N t) dt = 0` for `N ≥ 1`. -/
theorem se_intervalAverage_cos_nat {N : ℕ} (hN : 0 < N) :
    (∫ t in (0 : ℝ)..1, Real.cos (2 * Real.pi * (N : ℝ) * t)) = 0 := by
  have hc : (2 * Real.pi * (N : ℝ)) ≠ 0 := by positivity
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun x => Real.cos x) hc
  simp only [mul_zero, mul_one, integral_cos, Real.sin_zero, sub_zero] at h
  have hs : Real.sin (2 * Real.pi * (N : ℝ)) = 0 := by
    have := Real.sin_nat_mul_pi (2 * N)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  rw [hs] at h
  simpa using h

/-- Every component of `u_{m,k}` is a constant times a coordinate cosine of frequency `N = ε_m⁻¹`.
-/
theorem se_uShear_form {β : ℝ} (I : Ingredients β) (m : ℕ) (k : ℤ) (j : Fin 2) :
    ∃ (c : ℝ) (r : Fin 2), ∀ y : Vec 2, uShear β I.Λ m k y j =
      c * Real.cos (2 * Real.pi * (ergodicFrequency β I.Λ m : ℝ) * y r) := by
  have hN : (ergodicFrequency β I.Λ m : ℝ) = (epsilon β I.Λ m)⁻¹ := ergodicFrequency_cast β _ m
  have hdiv : ∀ z : ℝ, 2 * Real.pi * z / epsilon β I.Λ m =
      2 * Real.pi * (ergodicFrequency β I.Λ m : ℝ) * z := fun z => by
    rw [hN]; ring
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 ∨ (k % 4 ≠ 1 ∧ k % 4 ≠ 3) := by omega
  fin_cases j
  · rcases hk4 with h1 | h3 | ⟨h1, h3⟩
    · exact ⟨0, 0, fun y => by simp [uShear, h1]⟩
    · refine ⟨-(2 * Real.pi * a β I.Λ m * epsilon β I.Λ m), 1, fun y => ?_⟩
      simp [uShear, h3, hdiv]
    · exact ⟨0, 0, fun y => by simp [uShear, h1, h3]⟩
  · rcases hk4 with h1 | h3 | ⟨h1, h3⟩
    · refine ⟨2 * Real.pi * a β I.Λ m * epsilon β I.Λ m, 0, fun y => ?_⟩
      simp [uShear, h1, hdiv]
    · exact ⟨0, 0, fun y => by simp [uShear, h3]⟩
    · exact ⟨0, 0, fun y => by simp [uShear, h1, h3]⟩

/-- Generic form of a corrector component. -/
theorem se_chi_form {β : ℝ} (I : Ingredients β) (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) (j : Fin 2) :
    ∃ (c : ℝ) (r : Fin 2), ∀ y : Vec 2, I.chiMK κ m k t y j =
      c * Real.cos (2 * Real.pi * (ergodicFrequency β I.Λ m : ℝ) * y r) := by
  obtain ⟨c, r, h⟩ := se_uShear_form I m k j
  refine ⟨-(I.corrTime κ m k t) * c, r, fun y => ?_⟩
  simp [Ingredients.chiMK, Pi.smul_apply, smul_eq_mul, h]
  ring

theorem se_chi_continuous {β : ℝ} (I : Ingredients β) (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ)
    (j : Fin 2) : Continuous (fun y => I.chiMK κ m k t y j) := by
  obtain ⟨c, r, h⟩ := se_chi_form I m κ k t j
  have : (fun y => I.chiMK κ m k t y j) = fun y : Vec 2 =>
      c * Real.cos (2 * Real.pi * (ergodicFrequency β I.Λ m : ℝ) * y r) := funext h
  rw [this]
  fun_prop

theorem se_chi_fastPeriodic {β : ℝ} (I : Ingredients β) (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ)
    (j : Fin 2) : IsFastPeriodic (ergodicFrequency β I.Λ m)
      (fun y => I.chiMK κ m k t y j) := by
  obtain ⟨c, r, h⟩ := se_chi_form I m κ k t j
  have hN : (0 : ℝ) < ergodicFrequency β I.Λ m := by
    rw [ergodicFrequency_cast]
    exact inv_pos.2 (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  intro y n
  change I.chiMK κ m k t _ j = I.chiMK κ m k t y j
  rw [h, h]
  congr 1
  have : 2 * Real.pi * (ergodicFrequency β I.Λ m : ℝ) *
      (y + fun i => (n i : ℝ) / (ergodicFrequency β I.Λ m : ℝ)) r =
      2 * Real.pi * (ergodicFrequency β I.Λ m : ℝ) * y r + (n r : ℤ) * (2 * Real.pi) := by
    simp only [Pi.add_apply]
    field_simp
  rw [this, Real.cos_add_int_mul_two_pi]

theorem se_chi_cellAverage {β : ℝ} (I : Ingredients β) (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ)
    (j : Fin 2) : cellAverage (fun y => I.chiMK κ m k t y j) = 0 := by
  obtain ⟨c, r, h⟩ := se_chi_form I m κ k t j
  have hNpos : 0 < ergodicFrequency β I.Λ m :=
    ergodicFrequency_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hfun : (fun y => I.chiMK κ m k t y j) = fun y : Vec 2 =>
      c * Real.cos (2 * Real.pi * (ergodicFrequency β I.Λ m : ℝ) * y r) := funext h
  rw [hfun, ← LeftToShow.spaceAvg_eq_cellAverage]
  unfold AVenhance.spaceAvg
  rw [integral_const_mul]
  have h0 := Infra.Section3.spaceAvg_coordIntegral
    (F := fun s : ℝ => Real.cos (2 * Real.pi * (ergodicFrequency β I.Λ m : ℝ) * s))
    (by fun_prop) r
  unfold AVenhance.spaceAvg at h0
  rw [h0, se_intervalAverage_cos_nat hNpos, mul_zero]

/-- `e.corrm`: `|χ_{m,k,j}| ≤ ε_m · (a_m ε_m²/κ)`. -/
theorem se_chi_abs_le {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (k : ℤ) (t : ℝ) (y : Vec 2) (j : Fin 2) :
    |I.chiMK κ m k t y j| ≤
      epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κ) := by
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have ha : 0 ≤ a β I.Λ m := (Real.rpow_pos_of_pos hε _).le
  exact (Infra.Section3.chiMK_component_abs_le I hm κ hκ k t y j).trans
    (RelativeError.corrector_size_le ha hε hκ)

end AVenhance.Infra.Section5.Contracts
end
