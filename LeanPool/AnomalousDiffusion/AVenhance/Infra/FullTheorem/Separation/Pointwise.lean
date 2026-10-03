/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Pointwise real inequalities for the commutator pairings

Abstract-real lemmas on `Fin 2`-indexed families, used to bound the first- and second-order
commutator densities by the energy densities. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.FullTheorem.Separation

theorem abs_triple_le_young {κ Lu m p q : ℝ} (hκ : 0 < κ) (hm : |m| ≤ Lu) :
    |m * p * q| ≤ κ / 4 * p ^ 2 + Lu ^ 2 / κ * q ^ 2 := by
  have hLu : 0 ≤ Lu := (abs_nonneg m).trans hm
  have h1 : |m * p * q| ≤ Lu * |p| * |q| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hm (abs_nonneg _)) le_rfl (abs_nonneg _)
      (mul_nonneg hLu (abs_nonneg _))
  have h2 : Lu * |p| * |q| ≤ κ / 4 * p ^ 2 + Lu ^ 2 / κ * q ^ 2 := by
    have hsq := sq_nonneg (κ * |p| / 2 - Lu * |q|)
    have e : κ * (κ / 4 * p ^ 2 + Lu ^ 2 / κ * q ^ 2) =
        κ ^ 2 / 4 * |p| ^ 2 + Lu ^ 2 * |q| ^ 2 := by
      rw [← sq_abs p, ← sq_abs q]
      field_simp
    have : κ * (Lu * |p| * |q|) ≤ κ * (κ / 4 * p ^ 2 + Lu ^ 2 / κ * q ^ 2) := by
      rw [e]
      nlinarith [hsq]
    exact le_of_mul_le_mul_left this hκ
  exact h1.trans h2

theorem abs_triple_le_half {Lu m p q : ℝ} (hm : |m| ≤ Lu) :
    |m * p * q| ≤ Lu / 2 * (p ^ 2 + q ^ 2) := by
  have hLu : 0 ≤ Lu := (abs_nonneg m).trans hm
  have h1 : |m * p * q| ≤ Lu * |p| * |q| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hm (abs_nonneg _)) le_rfl (abs_nonneg _)
      (mul_nonneg hLu (abs_nonneg _))
  have h2 : |p| * |q| ≤ (p ^ 2 + q ^ 2) / 2 := by
    nlinarith [sq_nonneg (|p| - |q|), sq_abs p, sq_abs q]
  calc |m * p * q| ≤ Lu * (|p| * |q|) := by linarith [h1, mul_assoc Lu |p| |q|]
    _ ≤ Lu * ((p ^ 2 + q ^ 2) / 2) := mul_le_mul_of_nonneg_left h2 hLu
    _ = Lu / 2 * (p ^ 2 + q ^ 2) := by ring

/-- First-order quadratic form: `|∑ a_i m_{ik} a_k| ≤ 2 Lu ∑ a_i²`. -/
theorem abs_quadForm_le {Lu : ℝ} (m : Fin 2 → Fin 2 → ℝ) (a : Fin 2 → ℝ)
    (hm : ∀ i k, |m i k| ≤ Lu) :
    |∑ i : Fin 2, ∑ k : Fin 2, a i * (m i k * a k)| ≤ 2 * Lu * ∑ i : Fin 2, a i ^ 2 := by
  have h := fun i k => abs_triple_le_half (p := a i) (q := a k) (hm i k)
  have h' := fun i k => abs_le.mp (h i k)
  simp only [Fin.sum_univ_two]
  rw [abs_le]
  have e00 := h' 0 0
  have e01 := h' 0 1
  have e10 := h' 1 0
  have e11 := h' 1 1
  constructor <;> linarith [e00.1, e00.2, e01.1, e01.2, e10.1, e10.2, e11.1, e11.2]

/-- Second-order bound after the single integration by parts. -/
theorem abs_secondForm_le {κ Lu : ℝ} (hκ : 0 < κ) (m : Fin 2 → Fin 2 → ℝ)
    (p : Fin 2 → Fin 2 → Fin 2 → ℝ) (t2 : Fin 2 → Fin 2 → ℝ) (a : Fin 2 → ℝ)
    (hm : ∀ i k, |m i k| ≤ Lu) :
    |∑ j : Fin 2, ∑ i : Fin 2, ∑ k : Fin 2,
        (-(m i k * p j j i * a k) + t2 j i * m j k * t2 i k)| ≤
      κ / 2 * (∑ l : Fin 2, ∑ j : Fin 2, ∑ i : Fin 2, p l j i ^ 2) +
        4 * (Lu ^ 2 / κ) * (∑ k : Fin 2, a k ^ 2) +
        2 * Lu * (∑ j : Fin 2, ∑ i : Fin 2, t2 j i ^ 2) := by
  have hY := fun i k j => abs_le.mp (abs_triple_le_young hκ (p := p j j i) (q := a k) (hm i k))
  have hH := fun j k i => abs_le.mp
    (abs_triple_le_half (p := t2 j i) (q := t2 i k) (hm j k))
  simp only [Fin.sum_univ_two] at hY hH ⊢
  rw [abs_le]
  constructor <;>
  · linarith [hY 0 0 0, hY 0 0 1, hY 0 1 0, hY 0 1 1, hY 1 0 0, hY 1 0 1, hY 1 1 0, hY 1 1 1,
      hH 0 0 0, hH 0 0 1, hH 0 1 0, hH 0 1 1, hH 1 0 0, hH 1 0 1, hH 1 1 0, hH 1 1 1,
      mul_nonneg hκ.le (sq_nonneg (p 0 1 0)), mul_nonneg hκ.le (sq_nonneg (p 1 0 0)),
      mul_nonneg hκ.le (sq_nonneg (p 0 1 1)), mul_nonneg hκ.le (sq_nonneg (p 1 0 1))]

end AVenhance.Infra.FullTheorem.Separation
