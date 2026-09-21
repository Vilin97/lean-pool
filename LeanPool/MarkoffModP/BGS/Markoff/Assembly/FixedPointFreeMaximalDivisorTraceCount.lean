/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.PairedMaximalDivisorTraceCount

/-!
# Fixed-point-free maximal-divisor trace pairing

After restricting to eigenvalues with `x^2 ≠ 1`, inversion has no fixed
points.  Every trace fiber therefore contains a genuine inverse pair, with no
additive exceptional term.  Applying this on each maximal-divisor piece gives

`2 * |non-two-torsion bounded traces| ≤ (bound - 1) * M`.
-/

namespace BGS.Markoff

open BGS.NumberTheory

noncomputable section

section FixedPointFreeInvolutionImage

variable {G T : Type*} [Group G] [Fintype G] [DecidableEq G]
  [DecidableEq T] [IsCyclic G]

/-- An inversion-invariant map has at most half as many values as inputs when
inversion has no fixed point on the source. -/
theorem two_mul_card_image_le_card_of_inv_invariant_of_no_fixed
    (s : Finset G) (f : G → T)
    (hsinv : ∀ x ∈ s, x⁻¹ ∈ s)
    (hfinv : ∀ x, f x⁻¹ = f x)
    (hnofixed : ∀ x ∈ s, x⁻¹ ≠ x) :
    2 * (s.image f).card ≤ s.card := by
  classical
  have hcardFibers :
      s.card =
        ∑ y ∈ s.image f, (s.filter fun x => f x = y).card :=
    Finset.card_eq_sum_card_fiberwise
      (s := s) (t := s.image f) (f := f) (by
        intro x hx
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hfiber :
      ∀ y ∈ s.image f,
        2 ≤ (s.filter fun x => f x = y).card := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    have hxFiber : x ∈ s.filter fun z => f z = y :=
      Finset.mem_filter.mpr ⟨hx, hxy⟩
    have hxInvFiber : x⁻¹ ∈ s.filter fun z => f z = y := by
      refine Finset.mem_filter.mpr ⟨hsinv x hx, ?_⟩
      rw [hfinv, hxy]
    have hpair :
        ({x, x⁻¹} : Finset G) ⊆ s.filter fun z => f z = y := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hxFiber
      · exact hxInvFiber
    have hne : x ≠ x⁻¹ := Ne.symm (hnofixed x hx)
    simpa [hne] using Finset.card_le_card hpair
  calc
    2 * (s.image f).card =
        ∑ _y ∈ s.image f, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ y ∈ s.image f,
        (s.filter fun x => f x = y).card := by
      gcongr with y hy
      exact hfiber y hy
    _ = s.card := hcardFibers.symm

/-- Elements of a roots-of-unity piece that are not fixed by inversion. -/
def nonTwoTorsionElementsWithPowOne (m : ℕ) : Finset G :=
  (elementsWithPowOne G m).filter fun x => x ^ 2 ≠ 1

@[simp]
theorem mem_nonTwoTorsionElementsWithPowOne_iff
    {m : ℕ} {x : G} :
    x ∈ nonTwoTorsionElementsWithPowOne (G := G) m ↔
      x ^ m = 1 ∧ x ^ 2 ≠ 1 := by
  simp [nonTwoTorsionElementsWithPowOne]

/-- Bounded-order trace values represented by non-two-torsion eigenvalues. -/
def nonTwoTorsionBoundedOrderTraceSet
    (trace : G → T) (bound : ℕ) : Finset T :=
  (Finset.univ.filter fun x : G =>
    orderOf x < bound ∧ x ^ 2 ≠ 1).image trace

/-- The maximal-divisor cover built only from non-two-torsion roots. -/
def nonTwoTorsionMaximalDivisorTraceCover
    (trace : G → T) (bound : ℕ) : Finset T :=
  (maximalDivisorsBelow (Fintype.card G) bound).biUnion fun m =>
    (nonTwoTorsionElementsWithPowOne (G := G) m).image trace

/-- Every bounded-order non-two-torsion trace lies in the fixed-point-free
maximal-divisor cover. -/
theorem nonTwoTorsionBoundedOrderTraceSet_subset_maximalDivisorTraceCover
    (trace : G → T) (bound : ℕ) :
    nonTwoTorsionBoundedOrderTraceSet trace bound ⊆
      nonTwoTorsionMaximalDivisorTraceCover trace bound := by
  intro y hy
  rw [nonTwoTorsionBoundedOrderTraceSet, Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxData := Finset.mem_filter.mp hx
  obtain ⟨m, hm, horderDvd⟩ :=
    exists_dvd_maximalDivisorBelow Fintype.card_ne_zero
      orderOf_dvd_card hxData.2.1
  rw [nonTwoTorsionMaximalDivisorTraceCover, Finset.mem_biUnion]
  refine ⟨m, hm, Finset.mem_image.mpr ⟨x, ?_, rfl⟩⟩
  rw [mem_nonTwoTorsionElementsWithPowOne_iff]
  exact ⟨orderOf_dvd_iff_pow_eq_one.mp horderDvd, hxData.2.2⟩

/-- Each maximal-divisor piece is paired without fixed points, so summing the
pieces introduces no additive constant. -/
theorem two_mul_nonTwoTorsionMaximalDivisorTraceCover_card_le
    (trace : G → T) (bound : ℕ)
    (htraceInv : ∀ x, trace x⁻¹ = trace x) :
    2 * (nonTwoTorsionMaximalDivisorTraceCover trace bound).card ≤
      (bound - 1) *
        (maximalDivisorsBelow (Fintype.card G) bound).card := by
  classical
  have hpiece :
      ∀ m ∈ maximalDivisorsBelow (Fintype.card G) bound,
        2 * ((nonTwoTorsionElementsWithPowOne
          (G := G) m).image trace).card ≤ bound - 1 := by
    intro m hm
    have hmData := mem_maximalDivisorsBelow_iff.mp hm
    have hmPos : 0 < m := by
      have hmDvd : m ∣ Fintype.card G :=
        (Nat.mem_divisors.mp hmData.1).1
      exact Nat.pos_of_dvd_of_pos hmDvd Fintype.card_pos
    let s := nonTwoTorsionElementsWithPowOne (G := G) m
    have hsinv : ∀ x ∈ s, x⁻¹ ∈ s := by
      intro x hx
      have hxData :
          x ^ m = 1 ∧ x ^ 2 ≠ 1 := by
        simpa [s] using
          (mem_nonTwoTorsionElementsWithPowOne_iff.mp hx)
      rw [show s = nonTwoTorsionElementsWithPowOne (G := G) m by rfl,
        mem_nonTwoTorsionElementsWithPowOne_iff]
      constructor
      · simpa using congrArg Inv.inv hxData.1
      · intro hinvSq
        apply hxData.2
        have h := congrArg Inv.inv hinvSq
        simpa using h
    have hnofixed : ∀ x ∈ s, x⁻¹ ≠ x := by
      intro x hx hinv
      have hxSq : x ^ 2 ≠ 1 :=
        (mem_nonTwoTorsionElementsWithPowOne_iff.mp
          (by simpa [s] using hx)).2
      apply hxSq
      calc
        x ^ 2 = x * x := pow_two x
        _ = x * x⁻¹ := by rw [hinv]
        _ = 1 := mul_inv_cancel x
    have hpaired :
        2 * (s.image trace).card ≤ s.card :=
      two_mul_card_image_le_card_of_inv_invariant_of_no_fixed
        s trace hsinv htraceInv hnofixed
    calc
      2 * ((nonTwoTorsionElementsWithPowOne
          (G := G) m).image trace).card =
          2 * (s.image trace).card := by rfl
      _ ≤ s.card := hpaired
      _ ≤ (elementsWithPowOne G m).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ m := IsCyclic.card_pow_eq_one_le hmPos
      _ ≤ bound - 1 := Nat.le_sub_one_of_lt hmData.2.1
  calc
    2 * (nonTwoTorsionMaximalDivisorTraceCover trace bound).card ≤
        2 * ∑ m ∈ maximalDivisorsBelow (Fintype.card G) bound,
          ((nonTwoTorsionElementsWithPowOne
            (G := G) m).image trace).card := by
      apply Nat.mul_le_mul_left
      exact Finset.card_biUnion_le
    _ = ∑ m ∈ maximalDivisorsBelow (Fintype.card G) bound,
          2 * ((nonTwoTorsionElementsWithPowOne
            (G := G) m).image trace).card := by
      simp [Finset.mul_sum]
    _ ≤ ∑ _m ∈ maximalDivisorsBelow (Fintype.card G) bound,
          (bound - 1) := by
      gcongr with m hm
      exact hpiece m hm
    _ = (bound - 1) *
        (maximalDivisorsBelow (Fintype.card G) bound).card := by
      simp [Nat.mul_comm]

/-- Fixed-point-free inversion pairing for the bounded-order trace set. -/
theorem two_mul_nonTwoTorsionBoundedOrderTraceSet_card_le_maximalDivisors
    (trace : G → T) (bound : ℕ)
    (htraceInv : ∀ x, trace x⁻¹ = trace x) :
    2 * (nonTwoTorsionBoundedOrderTraceSet trace bound).card ≤
      (bound - 1) *
        (maximalDivisorsBelow (Fintype.card G) bound).card := by
  exact
    (Nat.mul_le_mul_left 2
      (Finset.card_le_card
        (nonTwoTorsionBoundedOrderTraceSet_subset_maximalDivisorTraceCover
          trace bound))).trans
      (two_mul_nonTwoTorsionMaximalDivisorTraceCover_card_le
        trace bound htraceInv)

end FixedPointFreeInvolutionImage

end

end BGS.Markoff
