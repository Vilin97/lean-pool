/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.WordBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesRadiusInflation
public import Mathlib.Data.Nat.Choose.Basic

/-! # Profile

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

theorem Profile.coarseCoeff_list_sum_bound {α : Type*} (L : List α) (f : α → ℝ) (C : ℝ)
    (h : ∀ a ∈ L, f a ≤ C) : (L.map f).sum ≤ L.length * C := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have ht := add_le_add (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))
    convert ht using 1; ring

/-- Quadratic flow products preserve the factorial analytic profile, with a
factor two in the radius and a constant polynomial in the small amplitude. -/
theorem coarseCoeffWordBudget_profile {k κ A R : ℝ} (hk : 0 ≤ k) (hA : 0 ≤ A)
    (hR : 0 ≤ R) (w : List (Fin 2)) :
    coarseCoeffWordBudget k κ (fun n => A * (n.factorial : ℝ) * R ^ n) w ≤
      (2 * k * A + 4 * (k + |κ|) * A * (A + 1)) *
        (w.length.factorial : ℝ) * (2 * R) ^ w.length := by
  have hr : 0 ≤ R := hR
  let H := (w.length.factorial : ℝ) * R ^ w.length
  have hh : 0 ≤ H := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr _)
  have hterm (p : List (Fin 2) × List (Fin 2)) (hp : p ∈ iterateSpatialSplits w) :
      (A * (p.1.length.factorial : ℝ) * R ^ p.1.length) *
      (A * (p.2.length.factorial : ℝ) * R ^ p.2.length + if p.2 = [] then 1 else 0) ≤
      A * (A + 1) * H := by
    have hs := iterateSpatialSplits_orders w hp
    have hright : A * (p.2.length.factorial : ℝ) * R ^ p.2.length +
        (if p.2 = [] then 1 else 0) ≤
        (A + 1) * (p.2.length.factorial : ℝ) * R ^ p.2.length := by
      by_cases hp2 : p.2 = []
      · simp [hp2]
      · simp only [hp2, ite_false, add_zero]
        have hn : 0 ≤ (p.2.length.factorial : ℝ) * R ^ p.2.length := by positivity
        nlinarith only [hn]
    have hfac : (p.1.length.factorial : ℝ) * (p.2.length.factorial : ℝ) ≤
        (w.length.factorial : ℝ) := by
      exact_mod_cast hs ▸ Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.factorial_mul_factorial_dvd_factorial_add p.1.length p.2.length)
    calc
      _ ≤ (A * (p.1.length.factorial : ℝ) * R ^ p.1.length) *
          ((A + 1) * (p.2.length.factorial : ℝ) * R ^ p.2.length) :=
        mul_le_mul_of_nonneg_left hright (by positivity)
      _ = A * (A + 1) * ((p.1.length.factorial : ℝ) * (p.2.length.factorial : ℝ)) *
          R ^ w.length := by rw [← hs, pow_add]; ring
      _ ≤ A * (A + 1) * H := by
        have ht := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfac (show 0 ≤ A * (A + 1) by positivity)) (pow_nonneg hr
              w.length)
        convert ht using 1; dsimp [H]; ring
  have hsum := Profile.coarseCoeff_list_sum_bound (iterateSpatialSplits w) _ _ hterm
  rw [iterateSpatialSplits_length] at hsum
  have ht : (1 : ℝ) ≤ 2 ^ w.length := one_le_pow₀ (by norm_num)
  have hlinear : 2 * k * A * H ≤ 2 * k * A * (2 ^ w.length * H) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hh ht) (by positivity)
  unfold coarseCoeffWordBudget
  calc
    _ ≤ 2 * k * A * H + 4 * (k + |κ|) * ((2 : ℝ) ^ w.length * (A * (A + 1) * H)) := by
      have hq := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 4 * (k + |κ|))
      push_cast at hq
      convert add_le_add_left hq (2 * k * A * H) using 1 <;> dsimp [H] <;> ring
    _ ≤ 2 * k * A * (2 ^ w.length * H) +
        4 * (k + |κ|) * (2 ^ w.length * (A * (A + 1) * H)) := add_le_add hlinear le_rfl
    _ = _ := by dsimp [H]; rw [mul_pow]; ring

/-- A common small analytic coefficient profile, including the candidate.
The positive flow profile is first inflated so every factor carries ρ. -/
theorem CoarseCoeffForm.small_profile_of_flow {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hΦ : IsStreamSeq I Φ} {m : ℕ} {κ : ℝ}
    {s : ℝ → Vec 2 → CoarseMatrix} (hs : CoarseCoeffForm I hΦ m κ s)
    (hm : 1 ≤ m) {k Cflow r₀ ρ : ℝ} (hk : 0 ≤ k) (hCf : 0 ≤ Cflow)
    (hr : 0 ≤ r₀) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hflow : ∀ t l, ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t))
    (hK : ∀ t i j, |I.Kmat κ m t i j| ≤ k)
    (hzero : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ i j,
      |(I.flowGrad hΦ m l t x - 1) i j| ≤ Cflow * ρ)
    (hpositive : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ p : List (Fin 2), 1 ≤ p.length → ∀ i j,
      |iterateSpatialWord p (fun y => (I.flowGrad hΦ m l t y - 1) i j) x| ≤
        Cflow * (p.length.factorial : ℝ) * r₀ ^ p.length) :
    ∀ t x p i j, |iterateSpatialWord p (fun y => s t y i j) x| ≤
      (2 * k * (Cflow * ρ) + 4 * (k + |κ|) * (Cflow * ρ) * (Cflow * ρ + 1)) *
        (p.length.factorial : ℝ) * (2 * max 1 (r₀ / ρ)) ^ p.length := by
  intro t x p i j
  let R := max 1 (r₀ / ρ)
  have hR : 1 ≤ R := le_max_left _ _
  have hB : ∀ n, 0 ≤ (Cflow * ρ) * (n.factorial : ℝ) * R ^ n := by
    intro n
    exact mul_nonneg (mul_nonneg (mul_nonneg hCf hρ.le) (Nat.cast_nonneg _))
      (pow_nonneg (le_trans (by norm_num) hR) _)
  have hjets : ∀ l, I.hatXiML m l t ≠ 0 → ∀ v : List (Fin 2), ∀ y a b,
      |iterateSpatialWord v (fun z => (I.flowGrad hΦ m l t z - 1) a b) y| ≤
        (Cflow * ρ) * (v.length.factorial : ℝ) * R ^ v.length := by
    intro l hl v y a b
    have hv : |iterateSpatialWord v (fun z => (I.flowGrad hΦ m l t z - 1) a b) y| ≤
        (Cflow * ρ) * (v.length.factorial : ℝ) * (r₀ / ρ) ^ v.length := by
      by_cases he : v = []
      · subst v
        simpa only [iterateSpatialWord, List.length_nil, Nat.factorial_zero, Nat.cast_one,
          pow_zero, mul_one] using hzero t y l hl a b
      · exact iterate_positive_profile_radius_inflation v.length
          (by have hn := List.length_pos_iff.mpr he; omega) hCf hr hρ hρ1
          (hpositive t y l hl v (by have hn := List.length_pos_iff.mpr he; omega) a b)
    exact hv.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg hr hρ.le) (le_max_right _ _) _) (by positivity))
  exact (hs.word_entry_bound hm t hB (hK t) (hflow t) hjets p x i j).trans
    (coarseCoeffWordBudget_profile hk (mul_nonneg hCf hρ.le)
      (le_trans (by norm_num) hR) p)

end AVenhance.Infra.Section4
