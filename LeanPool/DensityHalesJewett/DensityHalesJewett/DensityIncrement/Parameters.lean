/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.UniformFibers
import Mathlib.Tactic.Linarith

/-!
# Numerical parameters of the density increment

The thresholds `θ`, `η`, and `γ` attached to an alphabet size and a density, together with their
monotonicity and positivity properties.
-/

@[expose] public section

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

namespace Parameters

/-- A positive dimension selected from the density Hales--Jewett assertion when available. -/
noncomputable def m₀ (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 0 < δ ∧ HasDensityHJ k then
    Nat.succ <| Nat.find <| h.2 (δ / 4) (by linarith)
  else 1

lemma m₀_pos (k : ℕ) (δ : ℝ) : 0 < m₀ k δ := by
  classical
  unfold m₀
  split <;> simp

/-- The selected dimension is antitone in the density threshold. -/
lemma m₀_antitone {k : ℕ} (hDHJ : HasDensityHJ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : m₀ k ρ ≤ m₀ k δ := by
  classical
  rw [m₀, dite_eq_left ⟨hδ.trans_le hδρ, hDHJ⟩, m₀, dite_eq_left ⟨hδ, hDHJ⟩]
  apply Nat.succ_le_succ
  apply Nat.find_min'
  intro n hn A hA
  exact Nat.find_spec (hDHJ (δ / 4) (by linarith)) n hn A (le_trans (by gcongr) hA)

/-- The denominator in the parameter definition grows with the selected dimension. -/
lemma power_difference_mono (k : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m ≤
      ((k + 1 : ℕ) : ℝ) ^ n - (k : ℝ) ^ n := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
    rw [pow_succ, pow_succ]
    apply ih.trans
    rw [Nat.cast_add, Nat.cast_one]
    suffices 0 ≤ (k : ℝ) * (((k + 1 : ℕ) : ℝ) ^ n - (k : ℝ) ^ n) by
      rw [Nat.cast_add, Nat.cast_one] at this
      nlinarith [pow_nonneg (by positivity : 0 ≤ (k : ℝ)) n]
    apply mul_nonneg
    · positivity
    · apply sub_nonneg.mpr
      apply pow_le_pow_left₀
      · positivity
      · exact_mod_cast Nat.le_succ k

/-- The denominator defining `θ` is positive for every admissible alphabet and density. -/
lemma θ_denominator_pos {k : ℕ} (hk : 2 ≤ k) (δ : ℝ) :
    0 < ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ := by
  apply sub_pos.mpr
  apply pow_lt_pow_left₀
  · exact_mod_cast Nat.lt_succ_self k
  · positivity
  · exact Nat.ne_of_gt <| m₀_pos k δ

/-- The correlated-fibers threshold attached to an alphabet size and density. -/
noncomputable def θ (k : ℕ) (δ : ℝ) : ℝ :=
  (δ / 4) /
    (((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ)

/-- The threshold is monotone in the density parameter. -/
lemma θ_mono_of_dhj {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : θ k δ ≤ θ k ρ := by
  unfold θ
  refine div_le_div₀ ?_ (by linarith) (θ_denominator_pos hk ρ) ?_
  · exact div_nonneg (hδ.trans_le hδρ).le (by norm_num)
  · exact power_difference_mono k <| m₀_antitone hDHJ hδ hδρ

/-- The threshold is monotone even when the density Hales--Jewett assertion is unavailable. -/
lemma θ_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : θ k δ ≤ θ k ρ := by
  classical
  by_cases hDHJ : HasDensityHJ k
  · exact θ_mono_of_dhj hk hDHJ hδ hδρ
  · unfold θ
    rw [m₀, dite_eq_right (fun h ↦ hDHJ h.2), m₀, dite_eq_right (fun h ↦ hDHJ h.2)]
    apply div_le_div_of_nonneg_right
    · linarith
    · rw [pow_one, pow_one, Nat.cast_add, Nat.cast_one]
      linarith

lemma θ_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < θ k δ := by
  unfold θ
  exact div_pos (by positivity) (θ_denominator_pos hk δ)

/-- The error tolerance attached to an alphabet size and density. -/
noncomputable def η (k : ℕ) (δ : ℝ) : ℝ :=
  min (δ * θ k δ / 48) (min (θ k δ / 4) (δ / 6))

/-- The error tolerance is monotone in the density parameter. -/
lemma η_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : η k δ ≤ η k ρ := by
  unfold η
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · apply div_le_div_of_nonneg_right
    · exact mul_le_mul hδρ (θ_mono hk hδ hδρ) (θ_pos hk hδ).le
        (hδ.trans_le hδρ).le
    · norm_num
  · exact div_le_div_of_nonneg_right (θ_mono hk hδ hδρ) (by norm_num)
  · exact div_le_div_of_nonneg_right hδρ (by norm_num)

lemma η_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < η k δ := by
  unfold η
  apply lt_min
  · positivity [θ_pos hk hδ]
  · apply lt_min
    · positivity [θ_pos hk hδ]
    · positivity

/-- The density increment attached to an alphabet size and density. -/
noncomputable def γ (k : ℕ) (δ : ℝ) : ℝ :=
  min (δ * η k δ ^ 2 / k) (min (η k δ ^ 2 / 2) (3 * η k δ))

/-- The increment is monotone in the density parameter. -/
lemma γ_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : γ k δ ≤ γ k ρ := by
  unfold γ
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · apply div_le_div_of_nonneg_right
    · apply mul_le_mul hδρ
      · exact (sq_le_sq₀ (η_pos hk hδ).le
          (η_pos hk (hδ.trans_le hδρ)).le).mpr (η_mono hk hδ hδρ)
      · positivity
      · exact (hδ.trans_le hδρ).le
    · positivity
  · apply div_le_div_of_nonneg_right
    · exact (sq_le_sq₀ (η_pos hk hδ).le
        (η_pos hk (hδ.trans_le hδρ)).le).mpr (η_mono hk hδ hδρ)
    · norm_num
  · exact mul_le_mul_of_nonneg_left (η_mono hk hδ hδρ) (by norm_num)

lemma γ_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < γ k δ := by
  unfold γ
  positivity [η_pos hk hδ]

lemma η_lt_θ_div_two {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    η k δ < θ k δ / 2 := by
  unfold η
  apply lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
  linarith [θ_pos hk hδ]

lemma η_le_δ_div_six (k : ℕ) (δ : ℝ) : η k δ ≤ δ / 6 := by
  unfold η
  exact (min_le_right _ _).trans (min_le_right _ _)

lemma γ_le_η_sq_div_two (k : ℕ) (δ : ℝ) : γ k δ ≤ η k δ ^ 2 / 2 := by
  unfold γ
  exact (min_le_right _ _).trans (min_le_left _ _)

lemma γ_le_three_mul_η (k : ℕ) (δ : ℝ) : γ k δ ≤ 3 * η k δ := by
  unfold γ
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- The increment parameters can be chosen uniformly above a fixed positive density floor. -/
lemma γ_mono_lowerBound {k : ℕ} (hk : 2 ≤ k) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    0 < γ k δ₀ ∧ ∀ ρ, δ₀ ≤ ρ → γ k δ₀ ≤ γ k ρ := by
  constructor
  · exact γ_pos hk hδ₀
  · intro ρ hδρ
    exact γ_mono hk hδ₀ hδρ

/-- The correlated-fiber threshold is at most one in the admissible parameter range. -/
lemma θ_le_one {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ₁ : δ ≤ 1) :
    θ k δ ≤ 1 := by
  unfold θ
  have hden_pos : 0 < ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ :=
    θ_denominator_pos hk δ
  have h_one_le_diff : 1 ≤ ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ := by
    have h1 : ((k + 1 : ℕ) : ℝ) ^ 1 - (k : ℝ) ^ 1 = (1 : ℝ) := by norm_num
    simpa [h1] using power_difference_mono k (Nat.succ_le_of_lt (m₀_pos k δ))
  apply (div_le_one hden_pos).mpr
  linarith [hδ₁, h_one_le_diff]

/-- The numerical parameters turn the absolute density left outside a large intersection into
the required relative density gain. -/
lemma large_intersection_complement_gain {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) :
    (δ + 6 * η k δ) * (1 - θ k δ / 4) ≤ δ - 3 * η k δ := by
  have hη : η k δ ≤ δ * θ k δ / 48 :=
    min_le_left (δ * θ k δ / 48) (min (θ k δ / 4) (δ / 6))
  nlinarith [hη, θ_pos hk hδ₀, η_pos hk hδ₀,
    mul_nonneg hδ₀.le (θ_pos hk hδ₀).le,
    mul_nonneg (η_pos hk hδ₀).le (θ_pos hk hδ₀).le]

end Parameters

end DensityHalesJewett
