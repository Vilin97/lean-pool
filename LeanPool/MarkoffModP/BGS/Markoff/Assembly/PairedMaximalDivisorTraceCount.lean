/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.PairedMaximalDivisorLowOrderCount

/-!
# Maximal-divisor trace covers after inversion pairing

This module applies the abstract involution estimate to every maximal cyclic
subgroup in the low-order cover.  The resulting inequality is kept
division-free:

`2 * |trace values| ≤ (bound + 1) * |maximal divisors|`.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.NumberTheory

noncomputable section

section CyclicTraceCover

variable {G T : Type*} [Group G] [Fintype G] [DecidableEq G]
  [DecidableEq T] [IsCyclic G]

def maximalDivisorTraceCover (trace : G → T) (bound : ℕ) : Finset T :=
  (maximalDivisorsBelow (Fintype.card G) bound).biUnion fun m =>
    (elementsWithPowOne G m).image trace

theorem boundedOrderTraceSet_subset_maximalDivisorTraceCover
    (trace : G → T) (bound : ℕ) :
    boundedOrderTraceSet trace bound ⊆
      maximalDivisorTraceCover trace bound := by
  intro y hy
  rw [boundedOrderTraceSet, Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxCover :=
    elementsOfOrderLessThan_subset_maximalDivisorCover G bound hx
  rw [Finset.mem_biUnion] at hxCover
  obtain ⟨m, hm, hxm⟩ := hxCover
  rw [maximalDivisorTraceCover, Finset.mem_biUnion]
  exact ⟨m, hm, Finset.mem_image.mpr ⟨x, hxm, rfl⟩⟩

theorem two_mul_maximalDivisorTraceCover_card_le
    (trace : G → T) (bound : ℕ)
    (htraceInv : ∀ x, trace x⁻¹ = trace x) :
    2 * (maximalDivisorTraceCover trace bound).card ≤
      (bound + 1) *
        (maximalDivisorsBelow (Fintype.card G) bound).card := by
  classical
  have hpiece :
      ∀ m ∈ maximalDivisorsBelow (Fintype.card G) bound,
        2 * ((elementsWithPowOne G m).image trace).card ≤ bound + 1 := by
    intro m hm
    have hmData := mem_maximalDivisorsBelow_iff.mp hm
    have hmPos : 0 < m := by
      have hmDvd : m ∣ Fintype.card G :=
        (Nat.mem_divisors.mp hmData.1).1
      exact Nat.pos_of_dvd_of_pos hmDvd Fintype.card_pos
    have hpair :=
      two_mul_card_image_le_card_add_two_of_inv_invariant
        (elementsWithPowOne G m) trace
        (by
          intro x hx
          rw [mem_elementsWithPowOne_iff] at hx ⊢
          simpa using congrArg Inv.inv hx)
        htraceInv
    calc
      2 * ((elementsWithPowOne G m).image trace).card ≤
          (elementsWithPowOne G m).card + 2 := hpair
      _ ≤ m + 2 := Nat.add_le_add_right
        (IsCyclic.card_pow_eq_one_le hmPos) 2
      _ ≤ bound + 1 := by omega
  calc
    2 * (maximalDivisorTraceCover trace bound).card ≤
        2 * ∑ m ∈ maximalDivisorsBelow (Fintype.card G) bound,
          ((elementsWithPowOne G m).image trace).card := by
      apply Nat.mul_le_mul_left
      exact Finset.card_biUnion_le
    _ = ∑ m ∈ maximalDivisorsBelow (Fintype.card G) bound,
          2 * ((elementsWithPowOne G m).image trace).card := by
      simp [Finset.mul_sum]
    _ ≤ ∑ _m ∈ maximalDivisorsBelow (Fintype.card G) bound,
          (bound + 1) := by
      gcongr with m hm
      exact hpiece m hm
    _ = (bound + 1) *
        (maximalDivisorsBelow (Fintype.card G) bound).card := by
      simp [Nat.mul_comm]

theorem two_mul_boundedOrderTraceSet_card_le_maximalDivisors
    (trace : G → T) (bound : ℕ)
    (htraceInv : ∀ x, trace x⁻¹ = trace x) :
    2 * (boundedOrderTraceSet trace bound).card ≤
      (bound + 1) *
        (maximalDivisorsBelow (Fintype.card G) bound).card := by
  exact
    (Nat.mul_le_mul_left 2
      (Finset.card_le_card
        (boundedOrderTraceSet_subset_maximalDivisorTraceCover
          trace bound))).trans
      (two_mul_maximalDivisorTraceCover_card_le trace bound htraceInv)

end CyclicTraceCover

theorem splitTorusTrace_inv (F : Type*) [Field F] (x : Fˣ) :
    splitTorusTrace x⁻¹ = splitTorusTrace x := by
  simp [splitTorusTrace, add_comm]

theorem quadraticNormOneTrace_inv
    (p : ℕ) [Fact p.Prime] (x : quadraticNormOneTorus p) :
    quadraticNormOneTrace p x⁻¹ = quadraticNormOneTrace p x := by
  apply (algebraMap (ZMod p) (quadraticFiniteField p)).injective
  rw [algebraMap_quadraticNormOneTrace,
    algebraMap_quadraticNormOneTrace]
  simp [splitTorusTrace, add_comm]

end

end BGS.Markoff
