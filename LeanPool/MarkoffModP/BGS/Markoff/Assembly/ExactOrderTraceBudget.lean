/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.NonparabolicMaximalDivisorConcreteCount
public import LeanPool.MarkoffModP.BGS.NumberTheory.TruncatedOrderTotient

/-!
# Exact-order root budgets for nonparabolic traces

The old maximal-divisor estimate replaces each exact-order fiber by a common
worst-case size.  Here the cyclic fibers remain disjoint and contribute their
exact root counts `φ(e)`.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.NumberTheory

noncomputable section

theorem pow_two_ne_one_iff_two_lt_orderOf
    {G : Type*} [Group G] [Finite G] (x : G) :
    x ^ 2 ≠ 1 ↔ 2 < orderOf x := by
  constructor
  · intro hpow
    have hpos : 0 < orderOf x :=
      (isOfFinOrder_of_finite x).orderOf_pos
    by_contra hnot
    have hle : orderOf x ≤ 2 := Nat.le_of_not_gt hnot
    have hcases : orderOf x = 1 ∨ orderOf x = 2 := by
      omega
    have hdvd : orderOf x ∣ 2 := by
      rcases hcases with horder | horder <;> simp [horder]
    exact hpow (orderOf_dvd_iff_pow_eq_one.mp hdvd)
  · intro horder hpow
    have hdvd : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one hpow
    have hle : orderOf x ≤ 2 :=
      Nat.le_of_dvd (by norm_num) hdvd
    omega

section CyclicTrace

variable {G T : Type*} [Group G] [Fintype G] [DecidableEq G]
  [DecidableEq T] [IsCyclic G]

omit [IsCyclic G] in
theorem nonTwoTorsionBoundedOrderTraceSet_succ_eq_exactOrderImage
    (trace : G → T) (bound : ℕ) :
    nonTwoTorsionBoundedOrderTraceSet trace (bound + 1) =
      (elementsOfOrderBetweenThreeAnd G bound).image trace := by
  unfold nonTwoTorsionBoundedOrderTraceSet
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    mem_elementsOfOrderBetweenThreeAnd_iff,
    pow_two_ne_one_iff_two_lt_orderOf]
  omega

/-- An inversion-invariant trace map has at most half the exact cyclic root
budget in the non-two-torsion truncated range. -/
theorem two_mul_nonTwoTorsionBoundedOrderTraceSet_succ_card_le_totient
    (trace : G → T) (bound : ℕ)
    (htraceInv : ∀ x, trace x⁻¹ = trace x) :
    2 * (nonTwoTorsionBoundedOrderTraceSet
          trace (bound + 1)).card ≤
      truncatedOrderTotientSum (Fintype.card G) bound := by
  let roots := elementsOfOrderBetweenThreeAnd G bound
  have hsinv : ∀ x ∈ roots, x⁻¹ ∈ roots := by
    intro x hx
    rw [show roots = elementsOfOrderBetweenThreeAnd G bound by rfl,
      mem_elementsOfOrderBetweenThreeAnd_iff]
    have hxData :=
      mem_elementsOfOrderBetweenThreeAnd_iff.mp
        (by simpa [roots] using hx)
    simpa using hxData
  have hnofixed : ∀ x ∈ roots, x⁻¹ ≠ x := by
    intro x hx hinv
    have hxOrder :
        2 < orderOf x :=
      (mem_elementsOfOrderBetweenThreeAnd_iff.mp
        (by simpa [roots] using hx)).1
    have hxPow : x ^ 2 ≠ 1 :=
      (pow_two_ne_one_iff_two_lt_orderOf x).mpr hxOrder
    apply hxPow
    calc
      x ^ 2 = x * x := pow_two x
      _ = x * x⁻¹ := congrArg (fun z ↦ x * z) hinv.symm
      _ = 1 := mul_inv_cancel x
  rw [nonTwoTorsionBoundedOrderTraceSet_succ_eq_exactOrderImage]
  calc
    2 * (roots.image trace).card ≤ roots.card :=
      two_mul_card_image_le_card_of_inv_invariant_of_no_fixed
        roots trace hsinv htraceInv hnofixed
    _ = truncatedOrderTotientSum (Fintype.card G) bound :=
      elementsOfOrderBetweenThreeAnd_card_eq_truncatedOrderTotientSum
        G bound

end CyclicTrace

/-- Exact combined root budget for the split and nonsplit rotation tori. -/
def combinedTruncatedOrderTotientSum (p bound : ℕ) : ℕ :=
  truncatedOrderTotientSum (p - 1) bound +
    truncatedOrderTotientSum (p + 1) bound

/-- The concrete nonparabolic trace set is bounded by the exact combined
root-order budget. -/
theorem two_mul_nonparabolicConcreteLowOrderTraceSet_succ_card_le_totient
    {p : ℕ} [Fact p.Prime] (bound : ℕ) :
    2 * (nonparabolicConcreteLowOrderTraceSet
          p (bound + 1)).card ≤
      combinedTruncatedOrderTotientSum p bound := by
  classical
  let splitSet :=
    nonTwoTorsionBoundedOrderTraceSet
      (splitTorusTrace : (ZMod p)ˣ → ZMod p) (bound + 1)
  let nonsplitSet :=
    nonTwoTorsionBoundedOrderTraceSet
      (quadraticNormOneTrace p) (bound + 1)
  have hsplit :
      2 * splitSet.card ≤
        truncatedOrderTotientSum
          (Fintype.card (ZMod p)ˣ) bound := by
    exact
      two_mul_nonTwoTorsionBoundedOrderTraceSet_succ_card_le_totient
        (splitTorusTrace : (ZMod p)ˣ → ZMod p) bound
        (splitTorusTrace_inv (ZMod p))
  have hnonsplit :
      2 * nonsplitSet.card ≤
        truncatedOrderTotientSum
          (Fintype.card (quadraticNormOneTorus p)) bound := by
    exact
      two_mul_nonTwoTorsionBoundedOrderTraceSet_succ_card_le_totient
        (quadraticNormOneTrace p) bound
        (quadraticNormOneTrace_inv p)
  have hsplitCard : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, Nat.card_zmod]
  have hnonsplitCard :
      Fintype.card (quadraticNormOneTorus p) = p + 1 := by
    rw [← Nat.card_eq_fintype_card, quadraticNormOneTorus_natCard]
  calc
    2 * (nonparabolicConcreteLowOrderTraceSet
          p (bound + 1)).card ≤
        2 * (splitSet.card + nonsplitSet.card) := by
      apply Nat.mul_le_mul_left
      simpa [nonparabolicConcreteLowOrderTraceSet, splitSet, nonsplitSet] using
        (Finset.card_union_le splitSet nonsplitSet)
    _ = 2 * splitSet.card + 2 * nonsplitSet.card := by ring
    _ ≤ truncatedOrderTotientSum
          (Fintype.card (ZMod p)ˣ) bound +
        truncatedOrderTotientSum
          (Fintype.card (quadraticNormOneTorus p)) bound := by
      omega
    _ = combinedTruncatedOrderTotientSum p bound := by
      rw [hsplitCard, hnonsplitCard]
      rfl

end

end BGS.Markoff
