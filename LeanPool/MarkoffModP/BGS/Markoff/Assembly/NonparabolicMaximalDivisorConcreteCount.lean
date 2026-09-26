/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.FixedPointFreeMaximalDivisorTraceCount

/-!
# Fixed-point-free low-order traces on the two rotation tori

The nonparabolic low-order trace set omits the global parabolic set and uses
only eigenvalues whose square is not one. Inversion is therefore
fixed-point-free on both the split and norm-one sources, giving

`2 * |nonparabolic low traces| ≤ (bound - 1) * M`.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.NumberTheory

noncomputable section

/-- Nonparabolic bounded-order traces represented in either the split torus
or the quadratic norm-one torus. -/
def nonparabolicConcreteLowOrderTraceSet
    (p : ℕ) [Fact p.Prime] (bound : ℕ) : Finset (ZMod p) := by
  classical
  exact
    nonTwoTorsionBoundedOrderTraceSet
        (splitTorusTrace : (ZMod p)ˣ → ZMod p) bound ∪
      nonTwoTorsionBoundedOrderTraceSet
        (quadraticNormOneTrace p) bound

/-- Every nonparabolic trace of small rotation order lies in the
fixed-point-free concrete trace set. -/
theorem mem_nonparabolicConcreteLowOrderTraceSet_of_rotationOrder_lt
    {p : ℕ} [Fact p.Prime]
    (hpTwo : p ≠ 2) (t : ZMod p) (bound : ℕ)
    (hnonparabolic : t ^ 2 ≠ 4)
    (hsmall : rotationOrder t < bound) :
    t ∈ nonparabolicConcreteLowOrderTraceSet p bound := by
  classical
  rcases exists_split_or_quadraticNormOneTrace
      p hpTwo t hnonparabolic with
    ⟨w, htrace, hw⟩ | ⟨w, htrace, hw⟩
  · rw [nonparabolicConcreteLowOrderTraceSet, Finset.mem_union]
    apply Or.inl
    rw [nonTwoTorsionBoundedOrderTraceSet, Finset.mem_image]
    refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩,
      htrace⟩
    · rw [← rotationOrder_splitTorusTrace w hw, htrace]
      exact hsmall
    · intro hsq
      apply hw
      simpa using congrArg (fun u : (ZMod p)ˣ ↦ (u : ZMod p)) hsq
  · rw [nonparabolicConcreteLowOrderTraceSet, Finset.mem_union]
    apply Or.inr
    rw [nonTwoTorsionBoundedOrderTraceSet, Finset.mem_image]
    refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩,
      htrace⟩
    · rw [← rotationOrder_quadraticNormOneTrace p w hw, htrace]
      exact hsmall
    · intro hsq
      apply hw
      simpa using congrArg
        (fun u : quadraticNormOneTorus p ↦
          (((u : (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p))) hsq

/-- The exact fixed-point-free maximal-divisor trace count. -/
theorem two_mul_nonparabolicConcreteLowOrderTraceSet_card_le
    {p : ℕ} [Fact p.Prime] (bound : ℕ) :
    2 * (nonparabolicConcreteLowOrderTraceSet p bound).card ≤
      (bound - 1) * maximalDivisorCountSum p bound := by
  classical
  let splitSet :=
    nonTwoTorsionBoundedOrderTraceSet
      (splitTorusTrace : (ZMod p)ˣ → ZMod p) bound
  let nonsplitSet :=
    nonTwoTorsionBoundedOrderTraceSet
      (quadraticNormOneTrace p) bound
  have hsplit :
      2 * splitSet.card ≤
        (bound - 1) *
          (maximalDivisorsBelow
            (Fintype.card (ZMod p)ˣ) bound).card := by
    exact
      two_mul_nonTwoTorsionBoundedOrderTraceSet_card_le_maximalDivisors
        (splitTorusTrace : (ZMod p)ˣ → ZMod p) bound
        (splitTorusTrace_inv (ZMod p))
  have hnonsplit :
      2 * nonsplitSet.card ≤
        (bound - 1) *
          (maximalDivisorsBelow
            (Fintype.card (quadraticNormOneTorus p)) bound).card := by
    exact
      two_mul_nonTwoTorsionBoundedOrderTraceSet_card_le_maximalDivisors
        (quadraticNormOneTrace p) bound
        (quadraticNormOneTrace_inv p)
  have hsplitCard : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, Nat.card_zmod]
  have hnonsplitCard :
      Fintype.card (quadraticNormOneTorus p) = p + 1 := by
    rw [← Nat.card_eq_fintype_card, quadraticNormOneTorus_natCard]
  calc
    2 * (nonparabolicConcreteLowOrderTraceSet p bound).card ≤
        2 * (splitSet.card + nonsplitSet.card) := by
      apply Nat.mul_le_mul_left
      simpa [nonparabolicConcreteLowOrderTraceSet, splitSet, nonsplitSet] using
        (Finset.card_union_le splitSet nonsplitSet)
    _ = 2 * splitSet.card + 2 * nonsplitSet.card := by ring
    _ ≤ (bound - 1) *
          (maximalDivisorsBelow
            (Fintype.card (ZMod p)ˣ) bound).card +
        (bound - 1) *
          (maximalDivisorsBelow
            (Fintype.card (quadraticNormOneTorus p)) bound).card := by
      omega
    _ = (bound - 1) * maximalDivisorCountSum p bound := by
      rw [hsplitCard, hnonsplitCard]
      simp only [maximalDivisorCountSum, Nat.mul_add]

/-- At `bound = d + 1`, the fixed-point-free trace estimate has the exact
coefficient `d`. -/
theorem two_mul_nonparabolicConcreteLowOrderTraceSet_succ_card_le
    {p : ℕ} [Fact p.Prime] (d : ℕ) :
    2 *
        (nonparabolicConcreteLowOrderTraceSet p (d + 1)).card ≤
      d * maximalDivisorCountSum p (d + 1) := by
  simpa using
    (two_mul_nonparabolicConcreteLowOrderTraceSet_card_le
      (p := p) (d + 1))

end

end BGS.Markoff
