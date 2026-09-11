/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketWeights
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# Weighted Convolution
-/

@[expose] public section

noncomputable section

namespace EulerWeightedConvolution

open Finset EulerPacketWeights

theorem triangular_sum_le_product (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range (N + 1), ∑ l ∈ range n, a (l + 1) * b (n - l)) ≤
      (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
  let e : (Σ _n : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2 + 1, p.1 - p.2)
  have hinj : Set.InjOn e ((range (N + 1)).sigma range) := by
    rintro ⟨n, l⟩ hx ⟨n', l'⟩ hy h
    have hx' := mem_sigma.mp hx
    have hy' := mem_sigma.mp hy
    have hl : l < n := mem_range.mp hx'.2
    have hl' : l' < n' := mem_range.mp hy'.2
    have heq : l + 1 = l' + 1 ∧ n - l = n' - l' := Prod.mk.inj h
    have hll : l = l' := by omega
    have hnn : n = n' := by omega
    subst l'
    subst n'
    rfl
  have himg : Finset.image e ((range (N + 1)).sigma range) ⊆
      (range (N + 1)) ×ˢ (range (N + 1)) := by
    intro p hp
    obtain ⟨⟨n, l⟩, hx, rfl⟩ := mem_image.mp hp
    have hx' := mem_sigma.mp hx
    have hn := mem_range.mp hx'.1
    have hl := mem_range.mp hx'.2
    change n < N + 1 at hn
    change l < n at hl
    simp only [e, mem_product, mem_range]
    omega
  calc
    _ = ∑ p ∈ (range (N + 1)).sigma range, a (p.2 + 1) * b (p.1 - p.2) :=
      sum_sigma' _ _ _
    _ ≤ ∑ p ∈ (range (N + 1)) ×ˢ (range (N + 1)), a p.1 * b p.2 :=
      by
        simpa only [sum_image hinj, e] using
          (sum_le_sum_of_subset_of_nonneg himg
            (fun p _ _ => mul_nonneg (ha p.1) (hb p.2)))
    _ = _ := by rw [sum_product, ← sum_mul_sum]

theorem external_commutator_term (ρ : ℝ) (hρ : 0 < ρ) (j l : ℕ) (hl : 1 ≤ l)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    weight ρ (j + l) * ((j + l).choose l : ℝ) * a * b ≤
      ρ⁻¹ * (weight ρ l * a) * (((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) * b) := by
  have hden : 0 < weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) := by
    have h1 := weight_pos hρ l
    have h2 := weight_pos hρ (j + 1)
    positivity
  have h := (div_le_iff₀ hden).mp (external_commutator_ratio_le ρ hρ j l hl)
  have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h ha) hb
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hp

/-- The full truncated external-commutator convolution has a constant independent of the cutoff. -/
theorem external_commutator_sum (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range (N + 1), ∑ l ∈ range n,
      weight ρ n * (n.choose (l + 1) : ℝ) * a (l + 1) * b (n - l)) ≤
      ρ⁻¹ * (∑ l ∈ range (N + 1), weight ρ l * a l) *
        (∑ j ∈ range (N + 1), (j : ℝ) * weight ρ j * b j) := by
  have hp : ∀ n, 0 ≤ weight ρ n := fun n => (weight_pos hρ n).le
  calc
    _ ≤ ∑ n ∈ range (N + 1), ∑ l ∈ range n,
        ρ⁻¹ * (weight ρ (l + 1) * a (l + 1)) *
          (((n - l : ℕ) : ℝ) * weight ρ (n - l) * b (n - l)) := by
      apply sum_le_sum
      intro n _
      apply sum_le_sum
      intro l hl
      have hln := mem_range.mp hl
      have h := external_commutator_term ρ hρ (n - (l + 1)) (l + 1) (by omega)
        (a (l + 1)) (b (n - l)) (ha _) (hb _)
      have h1 : n - (l + 1) + (l + 1) = n := by omega
      have h2 : n - (l + 1) + 1 = n - l := by omega
      simpa only [h1, h2] using h
    _ = ρ⁻¹ * (∑ n ∈ range (N + 1), ∑ l ∈ range n,
        (weight ρ (l + 1) * a (l + 1)) *
          (((n - l : ℕ) : ℝ) * weight ρ (n - l) * b (n - l))) := by
      simp only [mul_assoc, mul_sum]
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hρ.le)
      exact triangular_sum_le_product N (fun l => weight ρ l * a l)
        (fun j => (j : ℝ) * weight ρ j * b j)
        (fun l => mul_nonneg (hp l) (ha l))
        (fun j => mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (hp j)) (hb j))

theorem shifted_triangular_sum_le_product (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range N, ∑ l ∈ range (n + 1), a l * b (n - l + 1)) ≤
      2 * (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
  have hi (n : ℕ) : (∑ l ∈ range (n + 1), a l * b (n - l + 1)) =
      (∑ l ∈ range n, a (l + 1) * b (n - l)) + a 0 * b (n + 1) := by
    rw [sum_range_succ']
    congr 1
    apply sum_congr rfl
    intro l hl
    have : n - (l + 1) + 1 = n - l := by have := mem_range.mp hl; omega
    rw [this]
  simp_rw [hi]
  rw [sum_add_distrib]
  have hrest : (∑ n ∈ range N, ∑ l ∈ range n, a (l + 1) * b (n - l)) ≤
      (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
    apply le_trans _ (triangular_sum_le_product N a b ha hb)
    apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
    intro n _ _
    exact sum_nonneg (fun l _ => mul_nonneg (ha _) (hb _))
  have ha0 : a 0 ≤ ∑ l ∈ range (N + 1), a l :=
    single_le_sum (fun l _ => ha l) (mem_range.mpr (by omega))
  have hsum : (∑ n ∈ range N, b (n + 1)) ≤ ∑ j ∈ range (N + 1), b j := by
    rw [sum_range_succ']
    linarith [hb 0]
  have hfirst : (∑ n ∈ range N, a 0 * b (n + 1)) ≤
      (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
    rw [← mul_sum]
    exact mul_le_mul ha0 hsum (sum_nonneg (fun n _ => hb _))
      (sum_nonneg (fun n _ => ha _))
  nlinarith

theorem shifted_source_term (ρ : ℝ) (hρ : 0 < ρ) (j l : ℕ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((j + l + 1 : ℕ) : ℝ) * weight ρ (j + l + 1) * ((j + l).choose l : ℝ) * a * b ≤
      (weight ρ l * a) * (((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) * b) := by
  have hden : 0 < weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) := by
    have h1 := weight_pos hρ l
    have h2 := weight_pos hρ (j + 1)
    positivity
  have h := (div_le_iff₀ hden).mp (shifted_source_ratio_le_one ρ hρ.ne' j l)
  have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h ha) hb
  simpa only [one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm] using hp

/-- The pressure-source derivative shift sums with a cutoff-independent constant. -/
theorem shifted_source_sum (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range N, ∑ l ∈ range (n + 1),
      ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1) * (n.choose l : ℝ) * a l * b (n - l + 1)) ≤
      2 * (∑ l ∈ range (N + 1), weight ρ l * a l) *
        (∑ j ∈ range (N + 1), (j : ℝ) * weight ρ j * b j) := by
  have hp : ∀ n, 0 ≤ weight ρ n := fun n => (weight_pos hρ n).le
  calc
    _ ≤ ∑ n ∈ range N, ∑ l ∈ range (n + 1),
        (weight ρ l * a l) * (((n - l + 1 : ℕ) : ℝ) * weight ρ (n - l + 1) * b (n - l + 1)) := by
      apply sum_le_sum
      intro n _
      apply sum_le_sum
      intro l hl
      have hln := mem_range.mp hl
      have h := shifted_source_term ρ hρ (n - l) l (a l) (b (n - l + 1)) (ha _) (hb _)
      have he : n - l + l = n := by omega
      simpa only [he] using h
    _ ≤ _ := shifted_triangular_sum_le_product N (fun l => weight ρ l * a l)
      (fun j => (j : ℝ) * weight ρ j * b j)
      (fun l => mul_nonneg (hp l) (ha l))
      (fun j => mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (hp j)) (hb j))

end EulerWeightedConvolution
