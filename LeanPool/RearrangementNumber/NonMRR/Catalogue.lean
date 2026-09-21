/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanPool.RearrangementNumber.NonMRR.FiniteEmbedding
import LeanPool.RearrangementNumber.NonMRR.Construction
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The concrete catalogue of balanced finite blocks

The blocks are Walsh vectors supported on consecutive disjoint intervals. The
geometrically decaying error bound makes their eventual prefix bounds summable.
-/

open Finset Filter
open scoped BigOperators

noncomputable section

namespace NonMRR

/-- The denominators of the prescribed prefix tolerances. -/
def blockDenominator (n : ℕ) : ℕ := 2 ^ (n + 1)

theorem blockDenominator_pos (n : ℕ) : 0 < blockDenominator n := by
  unfold blockDenominator
  positivity

/-- A summable sequence of allowed prefix errors. -/
def blockTolerance (n : ℕ) : ℝ := 1 / (blockDenominator n : ℝ)

/-- The number of exceptional choices allowed at each stage. -/
def blockCapacity (n : ℕ) : ℕ := 8 * blockDenominator n ^ 4

theorem blockCapacity_pos (n : ℕ) : 0 < blockCapacity n := by
  have := blockDenominator_pos n
  unfold blockCapacity
  positivity

theorem blockTolerance_nonneg (n : ℕ) : 0 ≤ blockTolerance n := by
  unfold blockTolerance
  positivity

theorem blockTolerance_summable : Summable blockTolerance := by
  change Summable (fun n => 1 / (blockDenominator n : ℝ))
  simpa only [blockTolerance, blockDenominator, Nat.cast_pow, Nat.cast_ofNat] using
    (summable_one_div_pow_of_le (m := (2 : ℝ)) (f := fun n => n + 1)
      (by norm_num) (fun n => Nat.le_succ n))

/-- A finite balanced family together with its uniform counting estimate. -/
structure FiniteBlock (m q : ℕ) where
  length : ℕ
  length_pos : 0 < length
  value : Fin m → Fin length → ℝ
  balance : ∀ k, ∑ i, value k i = 0
  abs_value : ∀ k i, |value k i| = 1 / (length : ℝ)
  bad_card : ∀ σ : Equiv.Perm (Fin length),
    (univ.filter fun k : Fin m => ∃ j ≤ length,
      1 / (q : ℝ) < |vectorPrefix (value k ∘ σ) j|).card ≤ 4 * q ^ 4

theorem finiteBlock_nonempty (m q : ℕ) (hq : 0 < q) : Nonempty (FiniteBlock m q) := by
  obtain ⟨L, hL, v, hv0, hvabs, hvbad⟩ := finite_counting_estimate m hq
  exact ⟨⟨L, hL, v, hv0, hvabs, hvbad⟩⟩

/-- Choose one of the finite families supplied by the counting lemma. -/
def chosenBlock (g : ℕ → ℕ) (n : ℕ) : FiniteBlock (g n) (blockDenominator n) :=
  Classical.choice (finiteBlock_nonempty (g n) (blockDenominator n) (blockDenominator_pos n))

/-- The left endpoints of consecutive blocks. -/
def blockStart (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => blockStart g n + (chosenBlock g n).length

theorem blockStart_monotone (g : ℕ → ℕ) : Monotone (blockStart g) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Nat.le_add_right _ _

/-- The order-preserving embedding of a finite block into its assigned interval. -/
def blockEmbedding (g : ℕ → ℕ) (n : ℕ) : Fin (chosenBlock g n).length ↪ ℕ where
  toFun i := blockStart g n + i.val
  inj' := by intro i j hij; exact Fin.ext (Nat.add_left_cancel hij)

/-- The finite support assigned to block `n`. -/
def blockInterval (g : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  univ.map (blockEmbedding g n)

theorem blockInterval_pairwise_disjoint (g : ℕ → ℕ) :
    Pairwise (fun n m => Disjoint (blockInterval g n) (blockInterval g m)) := by
  intro n m hnm
  apply disjoint_left.2
  intro x hxn hxm
  obtain ⟨i, -, hi⟩ := mem_map.1 hxn
  obtain ⟨j, -, hj⟩ := mem_map.1 hxm
  have heq : blockStart g n + i.val = blockStart g m + j.val := hi.trans hj.symm
  rcases lt_or_gt_of_ne hnm with h | h
  · have hstart := blockStart_monotone g (show n + 1 ≤ m by omega)
    change blockStart g n + (chosenBlock g n).length ≤ blockStart g m at hstart
    have hi' := i.isLt
    omega
  · have hstart := blockStart_monotone g (show m + 1 ≤ n by omega)
    change blockStart g m + (chosenBlock g m).length ≤ blockStart g n at hstart
    have hj' := j.isLt
    omega

/-- Use the selected finite vector on the assigned interval, and zero for an
unavailable choice. -/
def catalogueVector (g : ℕ → ℕ) (n k : ℕ) : ℕ → ℝ :=
  if hk : k < g n then
    embedVector (blockEmbedding g n) ((chosenBlock g n).value ⟨k, hk⟩)
  else fun _ => 0

theorem catalogueVector_support (g : ℕ → ℕ) (n k : ℕ) (hk : k < g n)
    (i : ℕ) (hi : i ∉ blockInterval g n) : catalogueVector g n k i = 0 := by
  rw [catalogueVector, dif_pos hk]
  apply embedVector_eq_zero
  simpa only [blockInterval, map_eq_image] using hi

theorem catalogueVector_balance (g : ℕ → ℕ) (n k : ℕ) (hk : k < g n) :
    ∑ i ∈ blockInterval g n, catalogueVector g n k i = 0 := by
  simp only [catalogueVector, dif_pos hk, blockInterval, map_eq_image]
  rw [sum_embedVector]
  exact (chosenBlock g n).balance ⟨k, hk⟩

theorem catalogueVector_mass (g : ℕ → ℕ) (n k : ℕ) (hk : k < g n) :
    1 ≤ ∑ i ∈ blockInterval g n, ‖catalogueVector g n k i‖ := by
  simp only [catalogueVector, dif_pos hk, blockInterval, map_eq_image]
  exact (sum_norm_embedVector_eq_one (chosenBlock g n).length_pos
    (blockEmbedding g n) ((chosenBlock g n).value ⟨k, hk⟩)
    ((chosenBlock g n).abs_value ⟨k, hk⟩)).ge

theorem catalogueVector_bad_card (g : ℕ → ℕ) (π : Equiv.Perm ℕ) (n : ℕ) :
    (badValues (catalogueVector g) g π blockTolerance n).card ≤ blockCapacity n := by
  classical
  let s : Finset (Fin (g n)) := univ.filter fun k =>
    (∃ j, 1 / (blockDenominator n : ℝ) <
      ‖rearrangedPartialSum (embedVector (blockEmbedding g n) ((chosenBlock g n).value k))
        (Equiv.refl ℕ) j‖) ∨
    (∃ j, 1 / (blockDenominator n : ℝ) <
      ‖rearrangedPartialSum (embedVector (blockEmbedding g n) ((chosenBlock g n).value k)) π j‖)
  have hs : badValues (catalogueVector g) g π blockTolerance n = s.image Fin.val := by
    ext k
    constructor
    · intro hk
      obtain ⟨hkg, hbad⟩ := mem_filter.1 hk
      have hkn : k < g n := mem_range.1 hkg
      refine mem_image.2 ⟨⟨k, hkn⟩, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
      simpa only [blockTolerance, catalogueVector, dif_pos hkn] using hbad
    · intro hk
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hk
      apply mem_filter.2
      refine ⟨mem_range.2 i.isLt, ?_⟩
      simpa only [blockTolerance, catalogueVector, dif_pos i.isLt] using (mem_filter.1 hi).2
  rw [hs, card_image_of_injective _ Fin.val_injective]
  exact card_bad_embedVector_two_orders_le (blockEmbedding g n)
    (chosenBlock g n).value (chosenBlock g n).bad_card π

/-- The explicit catalogue supplying all concrete data for the rearrangement
construction. Its only choices select the finite Walsh families already proved
to exist. -/
def walshCatalogue : BlockCatalogue blockCapacity blockTolerance where
  interval := blockInterval
  vector := catalogueVector
  disjoint := blockInterval_pairwise_disjoint
  support := catalogueVector_support
  balance := catalogueVector_balance
  mass := catalogueVector_mass
  bad_card := catalogueVector_bad_card

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
