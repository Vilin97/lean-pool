/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleRange
public import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryVerySmallRange
public import LeanPool.QuadraticCarleson.QuadraticCarleson.DyadicAtomScales
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Summation consequences for the lacunary middle range

The middle-range part of the paper uses three purely arithmetic facts:

* a modulation block `Q B τ` has exactly `B` integer indices;
* a frozen scale range `R B c τ` has at most `5B` indices under the paper's
  stated largeness condition;
* after restricting `τ` to one residue class modulo `10^10`, the frozen
  ranges are pairwise disjoint, so their nonnegative masses sum with no
  overlap loss.

This file packages the corresponding finite and countable sum estimates.
The last results use the author's exact half-open dyadic atom-scale partition
to turn scale coefficients back into arbitrary atom coefficients. No
operator estimate is assumed. The remaining analytic input in the paper is
the finite-modulation weak estimate on each `Q` block (and support vanishing
for the too-large branch of the error); those are deliberately not encoded
as arithmetic hypotheses here.
-/

@[expose] public section

open Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson.LacunaryMiddleRangeSummation

open QuadraticCarleson.LacunaryMiddleRange


noncomputable
section

/-- A uniformly bounded nonnegative coefficient sums over one modulation
block with the exact factor `B`. -/
theorem sum_Q_le (B : ℕ) (τ : ℤ) (a : ℤ → ENNReal) (M : ENNReal)
    (ha : ∀ m ∈ Q B τ, a m ≤ M) :
    ∑ m ∈ Q B τ, a m ≤ (B : ENNReal) * M := by
  calc
    ∑ m ∈ Q B τ, a m ≤ ∑ _m ∈ Q B τ, M := by
      exact Finset.sum_le_sum fun m hm ↦ ha m hm
    _ = (B : ENNReal) * M := by simp [card_Q]

/-- The analogous finite-sum consequence of the paper's `#R ≤ 5B` bound. -/
theorem sum_R_le_five_mul
    (B c : ℕ) (τ : ℤ) (hB : 0 < B) (hc : 2 * c ≤ 5 * B)
    (a : ℤ → ENNReal) (M : ENNReal)
    (ha : ∀ j ∈ R B c τ, a j ≤ M) :
    ∑ j ∈ R B c τ, a j ≤ (5 * B : ℕ) * M := by
  calc
    ∑ j ∈ R B c τ, a j ≤ ∑ _j ∈ R B c τ, M := by
      exact Finset.sum_le_sum fun j hj ↦ ha j hj
    _ = ((R B c τ).card : ℕ) * M := by simp
    _ ≤ (5 * B : ℕ) * M := by
      gcongr
      exact card_R_le_five_mul B c τ hB hc

/-- Nonnegative mass of one frozen scale block, retained only when its block
index lies in the chosen sparse residue class. -/
def sparseBlockMass
    (B c : ℕ) (ρ : ℤ) (a : ℤ → ENNReal) (τ : ℤ) : ENNReal :=
  if τ ≡ ρ [ZMOD sparseModulus] then ∑ j ∈ R B c τ, a j else 0

/-- In one sparse residue class, a fixed atom scale can occur in at most one
frozen range. -/
theorem eq_of_mem_R_of_same_sparse_residue
    {B c : ℕ} (hB : 0 < B) (hc : 2 * c ≤ 5 * B)
    {ρ τ τ' j : ℤ}
    (hτρ : τ ≡ ρ [ZMOD sparseModulus])
    (hτ'ρ : τ' ≡ ρ [ZMOD sparseModulus])
    (hj : j ∈ R B c τ) (hj' : j ∈ R B c τ') :
    τ = τ' := by
  by_contra hne
  have hmod : τ ≡ τ' [ZMOD sparseModulus] := hτρ.trans hτ'ρ.symm
  have hdis := R_disjoint_same_sparse_residue hB hc hne hmod
  rw [Finset.disjoint_left] at hdis
  exact hdis hj hj'

/-- Fixed-scale form of sparse disjointness, expressed as an unconditional
countable sum. -/
theorem tsum_sparse_membership_le
    (B c : ℕ) (hB : 0 < B) (hc : 2 * c ≤ 5 * B)
    (ρ j : ℤ) (A : ENNReal) :
    ∑' τ : ℤ,
        (if τ ≡ ρ [ZMOD sparseModulus] ∧ j ∈ R B c τ then A else 0) ≤ A := by
  by_cases hex : ∃ τ : ℤ, τ ≡ ρ [ZMOD sparseModulus] ∧ j ∈ R B c τ
  · obtain ⟨τ₀, hτ₀ρ, hj₀⟩ := hex
    rw [tsum_eq_single τ₀]
    · simp [hτ₀ρ, hj₀]
    · intro τ hτne
      have hnot : ¬(τ ≡ ρ [ZMOD sparseModulus] ∧ j ∈ R B c τ) := by
        intro h
        exact hτne (eq_of_mem_R_of_same_sparse_residue hB hc
          h.1 hτ₀ρ h.2 hj₀)
      simp [hnot]
  · have hnot : ∀ τ : ℤ,
        ¬(τ ≡ ρ [ZMOD sparseModulus] ∧ j ∈ R B c τ) := by
      simpa only [not_exists] using hex
    simp [hnot]

/-- Countable sparse packing: the frozen block masses in one residue class
are bounded by the total atom-scale mass. -/
theorem tsum_sparseBlockMass_le
    (B c : ℕ) (hB : 0 < B) (hc : 2 * c ≤ 5 * B)
    (ρ : ℤ) (a : ℤ → ENNReal) :
    ∑' τ : ℤ, sparseBlockMass B c ρ a τ ≤ ∑' j : ℤ, a j := by
  calc
    (∑' τ : ℤ, sparseBlockMass B c ρ a τ) =
        ∑' τ : ℤ, ∑' j : ℤ,
          (if τ ≡ ρ [ZMOD sparseModulus] ∧ j ∈ R B c τ then a j else 0) := by
      apply tsum_congr
      intro τ
      by_cases hτρ : τ ≡ ρ [ZMOD sparseModulus]
      · simp only [sparseBlockMass, hτρ, ite_true]
        rw [sum_eq_tsum_indicator]
        apply tsum_congr
        intro j
        by_cases hj : j ∈ R B c τ <;> simp [hj]
      · simp [sparseBlockMass, hτρ]
    _ = ∑' j : ℤ, ∑' τ : ℤ,
          (if τ ≡ ρ [ZMOD sparseModulus] ∧ j ∈ R B c τ then a j else 0) :=
      ENNReal.tsum_comm
    _ ≤ ∑' j : ℤ, a j := by
      apply ENNReal.tsum_le_tsum
      intro j
      exact tsum_sparse_membership_le B c hB hc ρ j (a j)

/-- Mass in an exact half-open dyadic scale class. -/
def atomScaleMass {ι : Type*}
    (length : ι → ℝ) (w : ι → ENNReal) (j : ℤ) : ENNReal :=
  ∑' I : ι, (QuadraticCarleson.dyadicAtomScaleClass length j).indicator w I

/-- Tonelli plus uniqueness of the half-open dyadic scale gives an exact
partition of arbitrary nonnegative atom mass. -/
theorem tsum_atomScaleMass_eq
    {ι : Type*}
    (length : ι → ℝ) (hlength : ∀ I, 0 < length I)
    (w : ι → ENNReal) :
    ∑' j : ℤ, atomScaleMass length w j = ∑' I : ι, w I := by
  unfold atomScaleMass
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro I
  let j₀ := QuadraticCarleson.dyadicAtomScaleIndex length hlength I
  rw [tsum_eq_single j₀]
  · rw [Set.indicator_of_mem
      (QuadraticCarleson.dyadicAtomScaleIndex_mem length hlength I)]
  · intro j hj
    have hnot : I ∉ QuadraticCarleson.dyadicAtomScaleClass length j := by
      intro hI
      have heq := QuadraticCarleson.dyadicAtomScaleIndex_unique length hlength hI
      exact hj (by simpa only [j₀] using heq)
    rw [Set.indicator_of_notMem hnot]

/-- Sparse middle blocks pack directly into the total mass of an arbitrary
countable atom family, with scales determined by the exact half-open
convention. -/
theorem tsum_sparseBlock_atomScaleMass_le
    {ι : Type*}
    (B c : ℕ) (hB : 0 < B) (hc : 2 * c ≤ 5 * B)
    (ρ : ℤ) (length : ι → ℝ) (hlength : ∀ I, 0 < length I)
    (w : ι → ENNReal) :
    ∑' τ : ℤ, sparseBlockMass B c ρ (atomScaleMass length w) τ ≤
      ∑' I : ι, w I := by
  calc
    ∑' τ : ℤ, sparseBlockMass B c ρ (atomScaleMass length w) τ ≤
        ∑' j : ℤ, atomScaleMass length w j :=
      tsum_sparseBlockMass_le B c hB hc ρ (atomScaleMass length w)
    _ = ∑' I : ι, w I := tsum_atomScaleMass_eq length hlength w

end
end QuadraticCarleson.LacunaryMiddleRangeSummation
