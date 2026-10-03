/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import LeanPool.Zeta5Irrational.EnergyBlocks
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # The raw configuration inequality

Combining `atom_energy_nonpos` with the four block estimates gives, for every configuration
`t : Fin (37 n) → ℝ` of pairwise distinct points and every `ε > 0`:

`∑ᵢ ∑ᵢ' log |tᵢ - tᵢ'| ≤ -h log ε + 2K ∑ᵢ (Uρ(tᵢ) + Err ε (tᵢ)) - K² I(ρ)`

(`energy_raw`), where the diagonal terms are `log 0 = 0`.
-/

public section

open MeasureTheory Set Real intervalIntegral Filter Topology Finset

namespace Zeta5Irrational

/-- The total regularisation error at a point. -/
@[expose] noncomputable def Err (ε t : ℝ) : ℝ :=
  ∑ j : Fin 16, cρ (j + 1) * errj ε t (mρ (j + 1)) (rρ (j + 1))

/--
`∑_{j,j' < N} c_j c_j' f (max j j') = ∑_{j < N} (S_{j+1}² - S_j²) f_j` with `S_k = ∑_{i<k} c_i`. -/
lemma sum_sum_max_eq (c f : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ range N, ∑ j' ∈ range N, c j * c j' * f (max j j') =
      ∑ j ∈ range N, ((∑ i ∈ range (j + 1), c i) ^ 2 - (∑ i ∈ range j, c i) ^ 2) * f j := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ] at ih ⊢
    rw [Finset.sum_add_distrib, ih]
    have h1 : ∀ j ∈ range N, c j * c N * f (max j N) = c j * c N * f N := by
      intro j hj
      rw [max_eq_right (Finset.mem_range.mp hj).le]
    have h2 : ∀ j' ∈ range N, c N * c j' * f (max N j') = c N * c j' * f N := by
      intro j' hj'
      rw [max_eq_left (Finset.mem_range.mp hj').le]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, max_self]
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    ring

/-- `I(ρ)` as a double sum over the sixteen intervals. -/
lemma Irho_eq_double_sum :
    Irho =
      ∑ j : Fin 16,
        ∑ j' : Fin 16,
          cρ (j + 1) * cρ (j' + 1) *
            Real.log ((bρ (max (j : ℕ) j' + 1) - aρ (max (j : ℕ) j' + 1)) / 4) := by
  have hS : ∀ k, Sρ k = ∑ i ∈ range k, cρ (i + 1) := fun k => by rw [Sρ, sum_Icc_eq_sum_range']
  unfold Irho
  rw [sum_Icc_eq_sum_range']
  simp only [Nat.add_sub_cancel, hS]
  rw [←
    sum_sum_max_eq (fun i => cρ (i + 1)) (fun j => Real.log ((bρ (j + 1) - aρ (j + 1)) / 4)) 16, ←
    Fin.sum_univ_eq_sum_range
      (fun j =>
        ∑ j' ∈ range 16,
          cρ (j + 1) * cρ (j' + 1) * Real.log ((bρ (max j j' + 1) - aρ (max j j' + 1)) / 4))
      16]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [←
    Fin.sum_univ_eq_sum_range
      (fun j' =>
        cρ ((j : ℕ) + 1) * cρ (j' + 1) *
          Real.log ((bρ (max (j : ℕ) j' + 1) - aρ (max (j : ℕ) j' + 1)) / 4))
      16]

/-- The arcsine–arcsine block dominates `(2π)² I(ρ)`. -/
lemma block_D_sum {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (2 * π) ^ 2 * Irho ≤
      ∑ j : Fin 16, ∑ j' : Fin 16, cρ (j + 1) * cρ (j' + 1) * Plog t ε (Sum.inr j) (Sum.inr j') :=
  by
  rw [Irho_eq_double_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j' _ => ?_
  have hc : 0 ≤ cρ (j + 1) * cρ (j' + 1) :=
    mul_nonneg (cρ_pos _ (by simp only [Finset.mem_Icc]; omega)).le
      (cρ_pos _ (by simp only [Finset.mem_Icc]; omega)).le
  have hP :
    (2 * π) ^ 2 * Real.log ((bρ (max (j : ℕ) j' + 1) - aρ (max (j : ℕ) j' + 1)) / 4) ≤
      Plog t ε (Sum.inr j) (Sum.inr j') := by
    rcases le_total (j : ℕ) j' with hjj | hjj
    · rw [max_eq_right hjj]; exact block_D t hε j j'
    · rw [max_eq_left hjj, Plog, pairInt_log_symm t hε]; exact block_D t hε j' j
  calc
    (2 * π) ^ 2 *
          (cρ (j + 1) * cρ (j' + 1) *
            Real.log ((bρ (max (j : ℕ) j' + 1) - aρ (max (j : ℕ) j' + 1)) / 4)) =
        cρ (j + 1) * cρ (j' + 1) *
          ((2 * π) ^ 2 * Real.log ((bρ (max (j : ℕ) j' + 1) - aρ (max (j : ℕ) j' + 1)) / 4)) :=
      by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hP hc

/-- The circle–circle block. -/
lemma block_AB_sum {h : ℕ} (t : Fin h → ℝ) (hinj : Function.Injective t) {ε : ℝ} (hε : 0 < ε) :
    (2 * π) ^ 2 * ((h : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'|) ≤
      ∑ i, ∑ i', Plog t ε (Sum.inl i) (Sum.inl i') := by
  have hi :
    ∀ i,
      (2 * π) ^ 2 * (Real.log ε + ∑ i', Real.log |t i - t i'|) ≤
        ∑ i', Plog t ε (Sum.inl i) (Sum.inl i') := by
    intro i
    rw [←
      Finset.add_sum_erase (s := Finset.univ) (f := fun i' => Plog t ε (Sum.inl i) (Sum.inl i'))
        (Finset.mem_univ i),
      block_A t hε i, ←
      Finset.sum_erase (s := Finset.univ) (a := i) (f := fun i' => Real.log |t i - t i'|)
        (by simp),
      mul_add, Finset.mul_sum]
    refine add_le_add le_rfl (Finset.sum_le_sum fun i' hi' => ?_)
    exact block_B t hε i i' (fun h => Finset.ne_of_mem_erase hi' (hinj h).symm)
  calc
    (2 * π) ^ 2 * ((h : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'|) =
        ∑ i : Fin h, (2 * π) ^ 2 * (Real.log ε + ∑ i', Real.log |t i - t i'|) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => hi i

/-- The circle–arcsine block. -/
lemma block_C_sum {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin h) :
    ∑ j : Fin 16, cρ (j + 1) * Plog t ε (Sum.inl i) (Sum.inr j) ≤
      (2 * π) ^ 2 * (Uρ (t i) + Err ε (t i)) := by
  have hU : Uρ (t i) = ∑ j : Fin 16, cρ (j + 1) * Uω (aρ (j + 1)) (bρ (j + 1)) (t i) := by
    rw [Uρ, sum_Icc_eq_sum_range',
      Fin.sum_univ_eq_sum_range (fun j => cρ (j + 1) * Uω (aρ (j + 1)) (bρ (j + 1)) (t i)) 16]
  rw [hU, Err, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hc : 0 ≤ cρ (j + 1) := (cρ_pos _ (by simp only [Finset.mem_Icc]; omega)).le
  calc
    cρ (j + 1) * Plog t ε (Sum.inl i) (Sum.inr j) ≤
        cρ (j + 1) *
          ((2 * π) ^ 2 *
            (Uω (aρ (j + 1)) (bρ (j + 1)) (t i) + errj ε (t i) (mρ (j + 1)) (rρ (j + 1)))) :=
      mul_le_mul_of_nonneg_left (block_C t hε i j) hc
    _ = _ := by ring

/-- **The raw configuration inequality.** -/
theorem energy_raw (n : ℕ) (hn : 0 < n) (t : Fin (37 * n) → ℝ) (hinj : Function.Injective t)
    {ε : ℝ} (hε : 0 < ε) :
    ∑ i, ∑ i', Real.log |t i - t i'| ≤
      -(37 * n : ℝ) * Real.log ε + 2 * Kr n * ∑ i, (Uρ (t i) + Err ε (t i)) - Kr n ^ 2 * Irho := by
  have hK : 0 < Kr n := by simp only [Kr]; positivity
  set AB := ∑ i, ∑ i', Plog t ε (Sum.inl i) (Sum.inl i') with hAB
  set C := ∑ i, ∑ j : Fin 16, cρ (j + 1) * Plog t ε (Sum.inl i) (Sum.inr j) with hC
  set D :=
    ∑ j : Fin 16, ∑ j' : Fin 16, cρ (j + 1) * cρ (j' + 1) * Plog t ε (Sum.inr j) (Sum.inr j') with
    hD
  have hE :
    ∑ i,
          (∑ i', 1 / Kr n * (1 / Kr n) * Plog t ε (Sum.inl i) (Sum.inl i') +
            ∑ j : Fin 16, 1 / Kr n * -cρ (j + 1) * Plog t ε (Sum.inl i) (Sum.inr j)) +
        ∑ j : Fin 16,
          (∑ i, -cρ (j + 1) * (1 / Kr n) * Plog t ε (Sum.inr j) (Sum.inl i) +
            ∑ j' : Fin 16, -cρ (j + 1) * -cρ (j' + 1) * Plog t ε (Sum.inr j) (Sum.inr j')) ≤
      0 := by
    have := atom_energy_nonpos n hn t hε
    unfold energy at this
    simpa only [Fintype.sum_sum_type, atomS, Plog] using this
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hE
  have hL1 :
    ∑ i, ∑ i', 1 / Kr n * (1 / Kr n) * Plog t ε (Sum.inl i) (Sum.inl i') = (1 / Kr n) ^ 2 * AB := by
    rw [hAB, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => by ring
  have hL2 :
    ∑ i, ∑ j : Fin 16, 1 / Kr n * -cρ (j + 1) * Plog t ε (Sum.inl i) (Sum.inr j) =
      -(1 / Kr n) * C := by
    rw [hC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hL3 :
    ∑ j : Fin 16, ∑ i, -cρ (j + 1) * (1 / Kr n) * Plog t ε (Sum.inr j) (Sum.inl i) =
      -(1 / Kr n) * C := by
    rw [hC, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Plog]
    rw [pairInt_log_symm t hε]
    ring
  have hL4 :
    ∑ j : Fin 16, ∑ j' : Fin 16, -cρ (j + 1) * -cρ (j' + 1) * Plog t ε (Sum.inr j) (Sum.inr j') =
      D := by
    rw [hD]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
  rw [hL1, hL2, hL3, hL4] at hE
  have hE' : (1 / Kr n) ^ 2 * AB - 2 * (1 / Kr n) * C + D ≤ 0 := by linarith
  have h1 := block_AB_sum t hinj hε
  have h2 : C ≤ (2 * π) ^ 2 * ∑ i, (Uρ (t i) + Err ε (t i)) := by
    rw [hC, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => block_C_sum t hε i
  have h3 := block_D_sum t hε
  rw [← hAB] at h1
  rw [←
    hD] at h3
        -- combine: (1/K)² AB ≤ 2 (1/K) C - D
  have hpi : 0 < (2 * π) ^ 2 := by positivity
  have hK2 : 0 < (1 / Kr n) ^ 2 := by positivity
  have key :
    (1 / Kr n) ^ 2 *
        ((2 * π) ^ 2 * ((37 * n : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'|)) ≤
      2 * (1 / Kr n) * ((2 * π) ^ 2 * ∑ i, (Uρ (t i) + Err ε (t i))) - (2 * π) ^ 2 * Irho := by
    have := mul_le_mul_of_nonneg_left h1 hK2.le
    push_cast at this
    have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * (1 / Kr n))
    linarith
  have key2 :
    (1 / Kr n) ^ 2 * ((37 * n : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'|) ≤
      2 * (1 / Kr n) * ∑ i, (Uρ (t i) + Err ε (t i)) - Irho := by
    have := key
    have e :
      (1 / Kr n) ^ 2 *
          ((2 * π) ^ 2 * ((37 * n : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'|)) =
        (2 * π) ^ 2 *
          ((1 / Kr n) ^ 2 * ((37 * n : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'|)) :=
      by ring
    have e2 :
      2 * (1 / Kr n) * ((2 * π) ^ 2 * ∑ i, (Uρ (t i) + Err ε (t i))) - (2 * π) ^ 2 * Irho =
        (2 * π) ^ 2 * (2 * (1 / Kr n) * ∑ i, (Uρ (t i) + Err ε (t i)) - Irho) :=
      by ring
    rw [e, e2] at this
    exact le_of_mul_le_mul_left this hpi
  have this := mul_le_mul_of_nonneg_left key2 (sq_nonneg (Kr n))
  have e1 :
    Kr n ^ 2 * ((1 / Kr n) ^ 2 * ((37 * n : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'|)) =
      (37 * n : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'| :=
    by field_simp
  have e2 :
    Kr n ^ 2 * (2 * (1 / Kr n) * ∑ i, (Uρ (t i) + Err ε (t i)) - Irho) =
      2 * Kr n * ∑ i, (Uρ (t i) + Err ε (t i)) - Kr n ^ 2 * Irho :=
    by field_simp
  rw [e1, e2] at this
  linarith

end Zeta5Irrational
