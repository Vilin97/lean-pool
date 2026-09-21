/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integer geometry for the lacunary middle range

This module formalizes the combinatorial core of the lacunary positive-endpoint
argument in arXiv:2609.04101v1. We write the paper's fixed support constant as
`C₀ = 2^c`, where `c : ℕ`, and take the cutoff/block length `B` to be a natural
number. After taking base-two logarithms, the paper's ranges become

* `L B c m = {j : m + 2j ≤ -c - 2B}`;
* `S B c m = {j : -c - 2B < m + 2j ≤ c + 2B}`;
* `Q B τ = [τB, (τ+1)B) ∩ ℤ`;
* `R B c τ = ⋃ m ∈ Q B τ, S B c m`.

All bounds below are explicit. In particular, `S` has between `2B + c` and
`2B + c + 1` elements, `Q` has exactly `B` elements, and `R` has at most
`5B` elements as soon as `2c ≤ 5B`. The paper's sparsification modulo
`10^10` gives pairwise disjoint frozen ranges.
-/

namespace QuadraticCarleson.LacunaryMiddleRange


/-- The paper's very-small atom scales `L_{k,m}`, in additive dyadic coordinates. -/
def L (B c : ℕ) (m : ℤ) : Set ℤ :=
  {j | m + 2 * j ≤ -(c : ℤ) - 2 * (B : ℤ)}

/-- The paper's middle atom scales `S_{k,m}`. The displayed endpoints are the
integer solution set of `-c - 2B < m + 2j ≤ c + 2B`. -/
noncomputable def S (B c : ℕ) (m : ℤ) : Finset ℤ :=
  Finset.Icc ((-(c : ℤ) - 2 * (B : ℤ) - m) / 2 + 1)
    (((c : ℤ) + 2 * (B : ℤ) - m) / 2)

/-- The modulation block `Q_{k,τ} = [τ B_k, (τ+1) B_k) ∩ ℤ`. -/
noncomputable def Q (B : ℕ) (τ : ℤ) : Finset ℤ :=
  Finset.Ico (τ * (B : ℤ)) ((τ + 1) * (B : ℤ))

/-- The frozen atom-scale range `R_{k,τ}`, defined literally as the union of
the middle ranges over one modulation block. -/
noncomputable def R (B c : ℕ) (τ : ℤ) : Finset ℤ :=
  (Q B τ).biUnion (S B c)

@[simp] theorem mem_L {B c : ℕ} {m j : ℤ} :
    j ∈ L B c m ↔ m + 2 * j ≤ -(c : ℤ) - 2 * (B : ℤ) :=
  Iff.rfl

theorem mem_S {B c : ℕ} {m j : ℤ} :
    j ∈ S B c m ↔
      -(c : ℤ) - 2 * (B : ℤ) < m + 2 * j ∧
        m + 2 * j ≤ (c : ℤ) + 2 * (B : ℤ) := by
  simp only [S, Finset.mem_Icc]
  omega

theorem mem_Q {B : ℕ} {τ m : ℤ} :
    m ∈ Q B τ ↔
      τ * (B : ℤ) ≤ m ∧ m < τ * (B : ℤ) + (B : ℤ) := by
  simp only [Q, Finset.mem_Ico, add_mul, one_mul]

/-- The complement of the middle range is exactly the very-small range or the
too-large range occurring in the paper's error term. -/
theorem not_mem_S_iff_mem_L_or_tooLarge {B c : ℕ} {m j : ℤ} :
    j ∉ S B c m ↔
      j ∈ L B c m ∨ (c : ℤ) + 2 * (B : ℤ) < m + 2 * j := by
  rw [mem_S, mem_L]
  omega

/-- An explicit interval description of the union defining `R`. -/
theorem mem_R {B c : ℕ} {τ j : ℤ} (hB : 0 < B) :
    j ∈ R B c τ ↔
      -(τ * (B : ℤ)) - (c : ℤ) - 3 * (B : ℤ) + 2 ≤ 2 * j ∧
        2 * j ≤ (c : ℤ) + 2 * (B : ℤ) - τ * (B : ℤ) := by
  constructor
  · intro hj
    simp only [R, Finset.mem_biUnion] at hj
    rcases hj with ⟨m, hmQ, hmS⟩
    rw [mem_Q] at hmQ
    rw [mem_S] at hmS
    omega
  · intro h
    let a : ℤ := τ * (B : ℤ)
    let low : ℤ := -(c : ℤ) - 2 * (B : ℤ) - 2 * j + 1
    by_cases hx : low ≤ a
    · refine Finset.mem_biUnion.mpr ⟨a, ?_, ?_⟩
      · rw [mem_Q]
        dsimp [a]
        omega
      · rw [mem_S]
        dsimp [low] at hx
        dsimp [a]
        omega
    · refine Finset.mem_biUnion.mpr ⟨low, ?_, ?_⟩
      · rw [mem_Q]
        dsimp [a, low] at *
        omega
      · rw [mem_S]
        dsimp [low]
        omega

theorem S_subset_R {B c : ℕ} {τ m : ℤ} (hm : m ∈ Q B τ) :
    S B c m ⊆ R B c τ := by
  intro j hj
  exact Finset.mem_biUnion.mpr ⟨m, hm, hj⟩

/-- This is the scale dichotomy used for the frozen-range error term. -/
theorem mem_R_sdiff_S_imp_mem_L_or_tooLarge {B c : ℕ} {τ m j : ℤ}
    (hj : j ∈ R B c τ \ S B c m) :
    j ∈ L B c m ∨ (c : ℤ) + 2 * (B : ℤ) < m + 2 * j := by
  exact not_mem_S_iff_mem_L_or_tooLarge.mp (Finset.mem_sdiff.mp hj).2

/-- For positive block length, the `Q B τ` uniquely partition `ℤ`. -/
theorem exists_unique_mem_Q (B : ℕ) (m : ℤ) (hB : 0 < B) :
    ∃! τ : ℤ, m ∈ Q B τ := by
  have hb : 0 < (B : ℤ) := by exact_mod_cast hB
  refine ⟨m / (B : ℤ), ?_, ?_⟩
  · change m ∈ Q B (m / (B : ℤ))
    rw [mem_Q]
    constructor
    · exact Int.ediv_mul_le m (ne_of_gt hb)
    · exact (Int.ediv_le_iff_le_mul hb).mp le_rfl
  · intro τ hτ
    rw [mem_Q] at hτ
    apply le_antisymm
    · by_contra hnot
      have hlt : m / (B : ℤ) < τ := lt_of_not_ge hnot
      have hupper := (Int.ediv_le_iff_le_mul hb).mp
        (show m / (B : ℤ) ≤ m / (B : ℤ) from le_rfl)
      nlinarith
    · by_contra hnot
      have hlt : τ < m / (B : ℤ) := lt_of_not_ge hnot
      have hlower := Int.ediv_mul_le m (ne_of_gt hb)
      nlinarith

theorem card_Q (B : ℕ) (τ : ℤ) : (Q B τ).card = B := by
  rw [Q, Int.card_Ico]
  have : (τ + 1) * (B : ℤ) - τ * (B : ℤ) = B := by ring
  rw [this]
  simp

/-- The explicit upper half of the paper's `2B + O(1)` assertion. -/
theorem card_S_le (B c : ℕ) (m : ℤ) :
    (S B c m).card ≤ 2 * B + c + 1 := by
  rw [S, Int.card_Icc]
  omega

/-- The corresponding lower bound; hence the unspecified `O(1)` is at most
`c + 1` in cardinality. -/
theorem card_S_ge (B c : ℕ) (m : ℤ) :
    2 * B + c ≤ (S B c m).card := by
  rw [S, Int.card_Icc]
  omega

theorem R_eq_Icc (B c : ℕ) (τ : ℤ) (hB : 0 < B) :
    R B c τ = Finset.Icc
      ((-(τ * (B : ℤ)) - (c : ℤ) - 3 * (B : ℤ) + 3) / 2)
      (((c : ℤ) + 2 * (B : ℤ) - τ * (B : ℤ)) / 2) := by
  ext j
  rw [mem_R hB]
  simp only [Finset.mem_Icc]
  omega

/-- A bound retaining the complete dependence on the dyadic support slack `c`. -/
theorem card_R_explicit (B c : ℕ) (τ : ℤ) (hB : 0 < B) :
    (R B c τ).card ≤ (2 * c + 5 * B) / 2 + 1 := by
  rw [R_eq_Icc B c τ hB, Int.card_Icc]
  omega

/-- The paper's stated `5B` bound, with its hidden largeness condition exposed. -/
theorem card_R_le_five_mul (B c : ℕ) (τ : ℤ) (hB : 0 < B)
    (hc : 2 * c ≤ 5 * B) :
    (R B c τ).card ≤ 5 * B := by
  rw [R_eq_Icc B c τ hB, Int.card_Icc]
  omega

/-- Four times the center of the unrounded endpoint interval for `R`. Scaling
by four keeps the first separation estimate integral. -/
def center4 (B : ℕ) (τ : ℤ) : ℤ :=
  -2 * (τ * (B : ℤ)) - (B : ℤ) + 2

theorem mem_R_center4_bound {B c : ℕ} {τ j : ℤ} (hB : 0 < B)
    (hj : j ∈ R B c τ) :
    |4 * j - center4 B τ| ≤ 2 * (c : ℤ) + 5 * (B : ℤ) - 2 := by
  rw [mem_R hB] at hj
  simp only [center4]
  rw [abs_le]
  constructor <;> omega

theorem center4_separated {B : ℕ} {τ τ' : ℤ}
    (hτ : 200 ≤ |τ - τ'|) :
    400 * (B : ℤ) ≤ |center4 B τ - center4 B τ'| := by
  have heq :
      center4 B τ - center4 B τ' = -2 * (τ - τ') * (B : ℤ) := by
    simp only [center4]
    ring
  rw [heq, abs_mul, abs_mul]
  norm_num
  nlinarith [abs_nonneg (τ - τ')]

/-- The actual (rational) center corresponding to `center4`. -/
def center (B : ℕ) (τ : ℤ) : ℚ :=
  (center4 B τ : ℚ) / 4

/-- An index separation of `200` implies the paper's center separation `100B`. -/
theorem center_separated_one_hundred {B : ℕ} {τ τ' : ℤ}
    (hτ : 200 ≤ |τ - τ'|) :
    100 * (B : ℚ) ≤ |center B τ - center B τ'| := by
  have h := center4_separated (B := B) hτ
  have hcast :
      (400 * (B : ℤ) : ℚ) ≤ (|center4 B τ - center4 B τ'| : ℤ) := by
    exact_mod_cast h
  rw [Int.cast_abs] at hcast
  simp only [center]
  rw [div_sub_div_same, abs_div]
  norm_num at hcast ⊢
  linarith

theorem R_disjoint_of_index_separation {B c : ℕ} {τ τ' : ℤ}
    (hB : 0 < B) (hc : 2 * c ≤ 5 * B) (hτ : 200 ≤ |τ - τ'|) :
    Disjoint (R B c τ) (R B c τ') := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  have h1 := mem_R_center4_bound hB hj
  have h2 := mem_R_center4_bound hB hj'
  have hsep := center4_separated (B := B) hτ
  have htri :
      |center4 B τ - center4 B τ'| ≤
        |4 * j - center4 B τ| + |4 * j - center4 B τ'| := by
    have h := abs_sub_le (center4 B τ) (4 * j) (center4 B τ')
    rwa [abs_sub_comm (center4 B τ) (4 * j)] at h
  omega

/-- The residue-class modulus used verbatim in the paper. -/
def sparseModulus : ℤ := 10000000000

theorem abs_sub_ge_sparseModulus {τ τ' : ℤ} (hne : τ ≠ τ')
    (hmod : τ ≡ τ' [ZMOD sparseModulus]) :
    sparseModulus ≤ |τ - τ'| := by
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    intro hzero
    subst q
    simp at hq
    omega
  have hqabs : 1 ≤ |q| := by
    have := abs_pos.mpr hq0
    omega
  have heq : τ - τ' = -(sparseModulus * q) := by omega
  rw [heq, abs_neg, abs_mul]
  norm_num [sparseModulus]
  omega

theorem center_separated_same_sparse_residue {B : ℕ} {τ τ' : ℤ}
    (hne : τ ≠ τ') (hmod : τ ≡ τ' [ZMOD sparseModulus]) :
    100 * (B : ℚ) ≤ |center B τ - center B τ'| := by
  apply center_separated_one_hundred
  have h := abs_sub_ge_sparseModulus hne hmod
  norm_num [sparseModulus] at h ⊢
  omega

/-- Distinct blocks in one residue class modulo `10^10` have disjoint frozen
atom-scale ranges. This is the sparsified disjointness used before Kalton
log-convexity. -/
theorem R_disjoint_same_sparse_residue {B c : ℕ} {τ τ' : ℤ}
    (hB : 0 < B) (hc : 2 * c ≤ 5 * B) (hne : τ ≠ τ')
    (hmod : τ ≡ τ' [ZMOD sparseModulus]) :
    Disjoint (R B c τ) (R B c τ') := by
  apply R_disjoint_of_index_separation hB hc
  have h := abs_sub_ge_sparseModulus hne hmod
  norm_num [sparseModulus] at h ⊢
  omega

end QuadraticCarleson.LacunaryMiddleRange
