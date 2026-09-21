/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationThree

/-!
# Atanasov--Ranganathan configuration 5, generic in the core

Configuration 5 of Atanasov--Ranganathan, Proposition 5.1, is the local
picture at a centre of the length-independent row: two boundary arms, a
middle slot to a second centre, two parallel slots onward to a cycle vertex,
and one far slot closing the cycle.  Two nested minima fix the three heights,
and the whole verification reduces to one-edge arithmetic.

This file carries that arithmetic once, in two layers.  The first is the
one-edge ledger: what one slot contributes at each of its ends, stated for a
slot read from either end -- `tailContribution` at the tail,
`headContribution` at the head -- because a row reads the same picture at two
centres in opposite orientations, and every fact here has a mirror.

The second layer states the residual effectivity at each vertex of the local
picture, once per nested-min profile (`outerTarget_*` when the outer minimum
saturates first, `innerTarget_*` when the inner one does) and once for the
cycle vertex, which both profiles share.  The three slots whose orientation
varies between the two centres -- the two boundary arms and the far slot --
are read through a `SlotLedger`, so each statement covers both orientations;
the middle and parallel slots point the same way at both centres and are
spelled out directly.  A row supplies its lookup tables and the five
height equations; nothing else.
-/

namespace AtanasovRanganathan.ConfigurationFive

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec

/-! ## One-edge arithmetic used by configuration 5 -/

def tailContribution (L hu hv : ℕ) : ℤ :=
  if L = 0 then 0
  else SubdivisionArithmetic.step L ((hu : ℤ) - (hv : ℤ)) 0

def headContribution (L hu hv : ℕ) : ℤ :=
  if L = 0 then 0
  else -SubdivisionArithmetic.step L ((hu : ℤ) - (hv : ℤ)) (L - 1)

@[simp] theorem tailContribution_zero_zero (L : ℕ) :
    tailContribution L 0 0 = 0 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · simp [tailContribution, h]
  · simp [tailContribution, h.ne',
      SubdivisionArithmetic.step_zero_of_lt h]

@[simp] theorem headContribution_zero_zero (L : ℕ) :
    headContribution L 0 0 = 0 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · simp [headContribution, h]
  · have hLast : L - 1 < L := by omega
    simp [headContribution, h.ne',
      SubdivisionArithmetic.step_zero_of_lt hLast]

theorem tailContribution_ge_neg_one {L hu hv : ℕ}
    (hLower : hv ≤ hu + L) (hUpper : hu ≤ hv + L) :
    -1 ≤ tailContribution L hu hv := by
  by_cases hL : L = 0
  · have hEq : hu = hv := by omega
    simp [tailContribution, hL]
  · have hPos : 0 < L := by omega
    simp only [tailContribution, if_neg hL]
    exact (SubdivisionArithmetic.endpointSlopeBounds
      ((hu : ℤ) - (hv : ℤ)) (-1) (-1) hPos (by
        omega) (by
        omega)).1

theorem headContribution_ge_neg_one {L hu hv : ℕ}
    (hLower : hv ≤ hu + L) (hUpper : hu ≤ hv + L) :
    -1 ≤ headContribution L hu hv := by
  by_cases hL : L = 0
  · have hEq : hu = hv := by omega
    simp [headContribution, hL]
  · have hPos : 0 < L := by omega
    simp only [headContribution, if_neg hL]
    exact (SubdivisionArithmetic.endpointSlopeBounds
      ((hu : ℤ) - (hv : ℤ)) (-1) (-1) hPos (by
        omega) (by
        omega)).2

theorem tailContribution_nonneg {L hu hv : ℕ} (h : hv ≤ hu)
    (hUpper : hu ≤ hv + L) :
    0 ≤ tailContribution L hu hv := by
  by_cases hL : L = 0
  · have hEq : hu = hv := by omega
    simp [tailContribution, hL]
  · simp only [tailContribution, if_neg hL]
    exact (SubdivisionArithmetic.endpointSlopeBounds
      ((hu : ℤ) - (hv : ℤ)) 0 (-1) (by omega) (by
        omega) (by
        omega)).1

theorem headContribution_nonneg {L hu hv : ℕ} (h : hu ≤ hv)
    (hUpper : hv ≤ hu + L) :
    0 ≤ headContribution L hu hv := by
  by_cases hL : L = 0
  · have hEq : hu = hv := by omega
    simp [headContribution, hL]
  · simp only [headContribution, if_neg hL]
    exact (SubdivisionArithmetic.endpointSlopeBounds
      ((hu : ℤ) - (hv : ℤ)) (-1) 0 (by omega) (by
        omega) (by
        omega)).2

theorem tailContribution_eq_one_of_full {L hu hv : ℕ}
    (hL : 0 < L) (hFull : hu = hv + L) :
    tailContribution L hu hv = 1 := by
  have hRise : (hu : ℤ) - (hv : ℤ) = (L : ℤ) := by
    omega
  simp [tailContribution, hL.ne', hRise,
    ConfigurationCommon.firstStep_full_eq_one hL]

theorem headContribution_eq_one_of_full {L hu hv : ℕ}
    (hL : 0 < L) (hFull : hv = hu + L) :
    headContribution L hu hv = 1 := by
  have hRise : (hu : ℤ) - (hv : ℤ) = -(L : ℤ) := by
    omega
  simp [headContribution, hL.ne', hRise,
    ConfigurationCommon.lastStep_neg_full_eq_neg_one hL]

def positiveChip (L : ℕ) : ℤ := if L = 0 then 0 else 1
def zeroChip (L : ℕ) : ℤ := if L = 0 then 1 else 0

theorem positiveChip_nonneg (L : ℕ) : 0 ≤ positiveChip L := by
  by_cases h : L = 0 <;> simp [positiveChip, h]

theorem zeroChip_nonneg (L : ℕ) : 0 ≤ zeroChip L := by
  by_cases h : L = 0 <;> simp [zeroChip, h]

@[simp] theorem tailContribution_same (L h : ℕ) :
    tailContribution L h h = 0 := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · simp [tailContribution, hL]
  · simp [tailContribution, hL.ne',
      SubdivisionArithmetic.step_zero_of_lt hL]

@[simp] theorem headContribution_same (L h : ℕ) :
    headContribution L h h = 0 := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · simp [headContribution, hL]
  · have hLast : L - 1 < L := by omega
    simp [headContribution, hL.ne',
      SubdivisionArithmetic.step_zero_of_lt hLast]

theorem zeroChip_add_tail_full (L : ℕ) :
    1 ≤ zeroChip L + tailContribution L L 0 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · simp [zeroChip, h]
  · have hOne := tailContribution_eq_one_of_full
        (L := L) (hu := L) (hv := 0) h (by omega)
    simp only [zeroChip, h.ne', ↓reduceIte, zero_add, ge_iff_le]
    omega

theorem zeroChip_add_head_full (L : ℕ) :
    1 ≤ zeroChip L + headContribution L 0 L := by
  rcases Nat.eq_zero_or_pos L with h | h
  · simp [zeroChip, h]
  · have hOne := headContribution_eq_one_of_full
        (L := L) (hu := 0) (hv := L) h (by omega)
    simp only [zeroChip, h.ne', ↓reduceIte, zero_add, ge_iff_le]
    omega

theorem positiveChip_add_head_nonneg {L h : ℕ} (hh : h ≤ L) :
    0 ≤ positiveChip L + headContribution L h 0 := by
  rcases Nat.eq_zero_or_pos L with hZero | hPos
  · have : h = 0 := by omega
    simp [positiveChip, headContribution, hZero]
  · have hHead := headContribution_ge_neg_one (L := L) (hu := h) (hv := 0)
      (by omega) (by omega)
    simp only [positiveChip, hPos.ne', ↓reduceIte, ge_iff_le]
    omega

theorem positiveChip_add_tail_nonneg {L h : ℕ} (hh : h ≤ L) :
    0 ≤ positiveChip L + tailContribution L 0 h := by
  rcases Nat.eq_zero_or_pos L with hZero | hPos
  · simp [positiveChip, tailContribution, hZero]
  · have hTail := tailContribution_ge_neg_one (L := L) (hu := 0) (hv := h)
      (by omega) (by omega)
    simp only [positiveChip, hPos.ne', ↓reduceIte, ge_iff_le]
    omega

abbrev drain := ConfigurationThree.drain

theorem headContribution_eq_neg_drain_of_ge {L hi lo : ℕ}
    (hGe : lo ≤ hi) (hLe : hi ≤ lo + L) :
    headContribution L hi lo = -drain (hi - lo) := by
  rcases Nat.eq_zero_or_pos L with hZero | hPos
  · have : hi = lo := by omega
    simp [headContribution, ConfigurationThree.drain, hZero, this]
  · let k := hi - lo
    have hkCast : (hi : ℤ) - (lo : ℤ) = (k : ℤ) := by
      dsimp [k]
      omega
    have hkLe : k ≤ L := by dsimp [k]; omega
    simp only [headContribution, if_neg hPos.ne', hkCast]
    rw [ConfigurationThree.lastStep_pos_eq_drain hPos hkLe]

theorem tailContribution_eq_neg_drain_of_le {L hi lo : ℕ}
    (hLe : hi ≤ lo) (hBound : lo ≤ hi + L) :
    tailContribution L hi lo = -drain (lo - hi) := by
  rcases Nat.eq_zero_or_pos L with hZero | hPos
  · have : hi = lo := by omega
    simp [tailContribution, ConfigurationThree.drain, hZero, this]
  · let k := lo - hi
    have hkCast : (hi : ℤ) - (lo : ℤ) = -(k : ℤ) := by
      dsimp [k]
      omega
    have hkLe : k ≤ L := by dsimp [k]; omega
    simp only [tailContribution, if_neg hPos.ne', hkCast]
    rw [ConfigurationThree.firstStep_neg_eq_neg_drain hPos hkLe]

/-! ## The orientation ledger

Row 07 reads the same local picture at two centres.  The middle slot and the
two parallel slots point the same way at both, but the two boundary arms and
the far slot are traversed in opposite directions.  A `SlotLedger` names the
two ends of those three slots, so that the whole calculation below is written
once and instantiated twice. -/

/-- The two ends of a slot whose orientation depends on which centre is being
read.  `tail L hu hv` is the contribution at the end carrying height `hu`,
`head L hu hv` the contribution at the end carrying `hv`. -/
structure SlotLedger where
  tail : ℕ → ℕ → ℕ → ℤ
  head : ℕ → ℕ → ℕ → ℤ
  tail_nonneg : ∀ {L hu hv : ℕ}, hv ≤ hu → hu ≤ hv + L → 0 ≤ tail L hu hv
  zeroChip_add_tail_full : ∀ L : ℕ, 1 ≤ zeroChip L + tail L L 0
  positiveChip_add_head_nonneg : ∀ {L h : ℕ}, h ≤ L →
    0 ≤ positiveChip L + head L h 0

/-- The slot read from its tail. -/
def forward : SlotLedger where
  tail := tailContribution
  head := headContribution
  tail_nonneg h hUpper := tailContribution_nonneg h hUpper
  zeroChip_add_tail_full := zeroChip_add_tail_full
  positiveChip_add_head_nonneg h := positiveChip_add_head_nonneg h

/-- The same slot read from its head. -/
def reverse : SlotLedger where
  tail L hu hv := headContribution L hv hu
  head L hu hv := tailContribution L hv hu
  tail_nonneg h hUpper := headContribution_nonneg h hUpper
  zeroChip_add_tail_full := zeroChip_add_head_full
  positiveChip_add_head_nonneg h := positiveChip_add_tail_nonneg h

/-! ## The outer-target reading

`o` is the height at the centre, `i` at the second centre, `e` at the cycle
vertex, and the two nested minima saturate outer-first. -/

/-- Residual effectivity at an outer-target centre.

The two boundary arms get **independent** ledgers: a row whose centre is the
tail of one arm and the head of the other (any core whose local cycle is a
directed one, such as atlas row 09) reads them in opposite orientations.  A row
whose arms point the same way passes the same ledger twice. -/
theorem outerTarget_center_nonneg (SA SB : SlotLedger)
    {la lb c lp lq b a m o i : ℕ}
    (ha : a = min la lb) (hm : m = min lp lq)
    (ho : o = min a (b + m + c)) (hi : i = min o (b + m)) :
    0 ≤ zeroChip la + zeroChip lb -
        (if c = 0 then if a ≤ b + m then 1 else 0 else 1) +
      (SA.tail la o 0 + SB.tail lb o 0 + tailContribution c o i) := by
  have hiO : i ≤ o := by omega
  have hoIC : o ≤ i + c := by omega
  have hArm0 : 0 ≤ SA.tail la o 0 := SA.tail_nonneg (by omega) (by omega)
  have hArm1 : 0 ≤ SB.tail lb o 0 := SB.tail_nonneg (by omega) (by omega)
  have hMiddleSupply : 0 ≤ tailContribution c o i :=
    tailContribution_nonneg hiO hoIC
  have hZeroLa : (0 : ℤ) ≤ zeroChip la := zeroChip_nonneg la
  have hZeroLb : (0 : ℤ) ≤ zeroChip lb := zeroChip_nonneg lb
  have hArmFull (hFull : o = a) :
      1 ≤ zeroChip la + zeroChip lb + SA.tail la o 0 + SB.tail lb o 0 := by
    rcases min_choice la lb with hLa | hLb
    · have hOne : 1 ≤ zeroChip la + SA.tail la o 0 := by
        rw [show o = la by omega]
        exact SA.zeroChip_add_tail_full la
      omega
    · have hOne : 1 ≤ zeroChip lb + SB.tail lb o 0 := by
        rw [show o = lb by omega]
        exact SB.zeroChip_add_tail_full lb
      omega
  by_cases hc : c = 0
  · have hMiddleZero : tailContribution c o i = 0 := by
      rw [show o = i by omega]
      exact tailContribution_same c i
    by_cases hSide : a ≤ b + m
    · have hSupply := hArmFull (by omega)
      rw [if_pos hc, if_pos hSide, hMiddleZero]
      omega
    · rw [if_pos hc, if_neg hSide, hMiddleZero]
      omega
  · have hOuterSupply : o = la ∨ o = lb ∨ o = i + c := by
      rcases min_choice a (b + m + c) with hOa | hOr
      · rcases min_choice la lb with hLa | hLb
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    rw [if_neg hc]
    rcases hOuterSupply with hFull | hFull | hFull
    · have hOne : 1 ≤ zeroChip la + SA.tail la o 0 := by
        rw [hFull]
        exact SA.zeroChip_add_tail_full la
      omega
    · have hOne : 1 ≤ zeroChip lb + SB.tail lb o 0 := by
        rw [hFull]
        exact SB.zeroChip_add_tail_full lb
      omega
    · have hOne := tailContribution_eq_one_of_full (L := c) (hu := o) (hv := i)
        (by omega) hFull
      omega

/-- Residual effectivity at the second centre of an outer-target reading. -/
theorem outerTarget_inner_nonneg
    {c lp lq b a m o i e : ℕ}
    (hm : m = min lp lq) (ho : o = min a (b + m + c))
    (hi : i = min o (b + m)) (he : e = min i b) :
    0 ≤ zeroChip m - (if c = 0 then if a ≤ b + m then 0 else 1 else 0) +
      (headContribution c o i + tailContribution lp i e +
        tailContribution lq i e) := by
  have hiO : i ≤ o := by omega
  have hoIC : o ≤ i + c := by omega
  have heI : e ≤ i := by omega
  have hiEM : i ≤ e + m := by omega
  have hMiddleCost : -1 ≤ headContribution c o i :=
    headContribution_ge_neg_one (by omega) hoIC
  have hParallel0 : 0 ≤ tailContribution lp i e :=
    tailContribution_nonneg heI (by omega)
  have hParallel1 : 0 ≤ tailContribution lq i e :=
    tailContribution_nonneg heI (by omega)
  have hZeroM : (0 : ℤ) ≤ zeroChip m := zeroChip_nonneg m
  have hParallelFull (hFull : i = e + m) :
      1 ≤ zeroChip m + tailContribution lp i e + tailContribution lq i e := by
    by_cases hm0 : m = 0
    · have hz : zeroChip m = 1 := by simp [zeroChip, hm0]
      omega
    · rcases min_choice lp lq with hMp | hMq
      · have hOne := tailContribution_eq_one_of_full (L := lp) (hu := i)
          (hv := e) (by omega) (by omega)
        omega
      · have hOne := tailContribution_eq_one_of_full (L := lq) (hu := i)
          (hv := e) (by omega) (by omega)
        omega
  by_cases hc : c = 0
  · have hMiddleZero : headContribution c o i = 0 := by
      rw [show o = i by omega]
      exact headContribution_same c i
    by_cases hSide : a ≤ b + m
    · rw [if_pos hc, if_pos hSide, hMiddleZero]
      omega
    · have hSupply := hParallelFull (by omega)
      rw [if_pos hc, if_neg hSide, hMiddleZero]
      omega
  · rw [if_neg hc]
    by_cases hio : i = o
    · have hMiddleZero : headContribution c o i = 0 := by
        rw [hio]
        exact headContribution_same c o
      rw [hMiddleZero]
      omega
    · have hSupply := hParallelFull (by omega)
      omega

/-! ## The inner-target reading

The same ledger with the two nested minima saturating inner-first. -/

/-- Residual effectivity at the outer centre of an inner-target reading.

As with `outerTarget_center_nonneg`, the two boundary arms carry independent
ledgers. -/
theorem innerTarget_center_nonneg (SA SB : SlotLedger)
    {la lb c lp lq b a m o i : ℕ}
    (ha : a = min la lb) (hm : m = min lp lq)
    (hi : i = min (a + c) (b + m)) (ho : o = min a i) :
    0 ≤ zeroChip la + zeroChip lb -
        (if c = 0 then if a ≤ b + m then 1 else 0 else 0) +
      (SA.tail la o 0 + SB.tail lb o 0 + tailContribution c o i) := by
  have hoI : o ≤ i := by omega
  have hiOC : i ≤ o + c := by omega
  have hArm0 : 0 ≤ SA.tail la o 0 := SA.tail_nonneg (by omega) (by omega)
  have hArm1 : 0 ≤ SB.tail lb o 0 := SB.tail_nonneg (by omega) (by omega)
  have hMiddleCost : -1 ≤ tailContribution c o i :=
    tailContribution_ge_neg_one hiOC (by omega)
  have hZeroLa : (0 : ℤ) ≤ zeroChip la := zeroChip_nonneg la
  have hZeroLb : (0 : ℤ) ≤ zeroChip lb := zeroChip_nonneg lb
  have hArmFull (hFull : o = a) :
      1 ≤ zeroChip la + zeroChip lb + SA.tail la o 0 + SB.tail lb o 0 := by
    rcases min_choice la lb with hLa | hLb
    · have hOne : 1 ≤ zeroChip la + SA.tail la o 0 := by
        rw [show o = la by omega]
        exact SA.zeroChip_add_tail_full la
      omega
    · have hOne : 1 ≤ zeroChip lb + SB.tail lb o 0 := by
        rw [show o = lb by omega]
        exact SB.zeroChip_add_tail_full lb
      omega
  by_cases hoi : o = i
  · have hMiddleZero : tailContribution c o i = 0 := by
      rw [hoi]
      exact tailContribution_same c i
    by_cases hc : c = 0
    · by_cases hSide : a ≤ b + m
      · have hSupply := hArmFull (by omega)
        rw [if_pos hc, if_pos hSide, hMiddleZero]
        omega
      · rw [if_pos hc, if_neg hSide, hMiddleZero]
        omega
    · rw [if_neg hc, hMiddleZero]
      omega
  · have hSupply := hArmFull (by omega)
    rw [if_neg (show ¬ c = 0 by omega)]
    omega

/-- Residual effectivity at the inner centre of an inner-target reading. -/
theorem innerTarget_inner_nonneg
    {c lp lq b a m o i e : ℕ}
    (hm : m = min lp lq) (hi : i = min (a + c) (b + m))
    (ho : o = min a i) (he : e = min b i) :
    0 ≤ zeroChip m - (if c = 0 then if a ≤ b + m then 0 else 1 else 1) +
      (headContribution c o i + tailContribution lp i e +
        tailContribution lq i e) := by
  have hoI : o ≤ i := by omega
  have hiOC : i ≤ o + c := by omega
  have heI : e ≤ i := by omega
  have hiEM : i ≤ e + m := by omega
  have hMiddleSupply : 0 ≤ headContribution c o i :=
    headContribution_nonneg hoI hiOC
  have hParallel0 : 0 ≤ tailContribution lp i e :=
    tailContribution_nonneg heI (by omega)
  have hParallel1 : 0 ≤ tailContribution lq i e :=
    tailContribution_nonneg heI (by omega)
  have hZeroM : (0 : ℤ) ≤ zeroChip m := zeroChip_nonneg m
  have hParallelFull (hFull : i = e + m) :
      1 ≤ zeroChip m + tailContribution lp i e + tailContribution lq i e := by
    by_cases hm0 : m = 0
    · have hz : zeroChip m = 1 := by simp [zeroChip, hm0]
      omega
    · rcases min_choice lp lq with hMp | hMq
      · have hOne := tailContribution_eq_one_of_full (L := lp) (hu := i)
          (hv := e) (by omega) (by omega)
        omega
      · have hOne := tailContribution_eq_one_of_full (L := lq) (hu := i)
          (hv := e) (by omega) (by omega)
        omega
  by_cases hc : c = 0
  · have hMiddleZero : headContribution c o i = 0 := by
      rw [show o = i by omega]
      exact headContribution_same c i
    by_cases hSide : a ≤ b + m
    · rw [if_pos hc, if_pos hSide, hMiddleZero]
      omega
    · have hSupply := hParallelFull (by omega)
      rw [if_pos hc, if_neg hSide, hMiddleZero]
      omega
  · have hInnerSupply : i = o + c ∨ i = e + m := by
      rcases min_choice (a + c) (b + m) with hIa | hIb
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [if_neg hc]
    rcases hInnerSupply with hFull | hFull
    · have hOne := headContribution_eq_one_of_full (L := c) (hu := o) (hv := i)
        (by omega) hFull
      omega
    · have hSupply := hParallelFull hFull
      omega

/-! ## The cycle vertex

Shared by both readings: only the far slot's orientation varies. -/

/-- Residual effectivity at the cycle vertex. -/
theorem cycle_nonneg (S : SlotLedger) {lp lq b m i e : ℕ}
    (hm : m = min lp lq) (heI : e ≤ i) (heB : e ≤ b)
    (hEB : e = i ∨ e = b) (hiEM : i ≤ e + m) :
    0 ≤ positiveChip m + zeroChip b +
      (headContribution lp i e + headContribution lq i e +
        S.tail b e 0) := by
  have hZeroB : (0 : ℤ) ≤ zeroChip b := zeroChip_nonneg b
  have hPositiveM : (0 : ℤ) ≤ positiveChip m := positiveChip_nonneg m
  have hFarSupply : 0 ≤ S.tail b e 0 := S.tail_nonneg (by omega) (by omega)
  by_cases hie : i = e
  · have hp0 : headContribution lp i e = 0 := by
      rw [hie]
      exact headContribution_same lp e
    have hp1 : headContribution lq i e = 0 := by
      rw [hie]
      exact headContribution_same lq e
    omega
  · have hmPos : 0 < m := by omega
    have hFar : 1 ≤ zeroChip b + S.tail b e 0 := by
      rw [show e = b by omega]
      exact S.zeroChip_add_tail_full b
    have hp0 := headContribution_eq_neg_drain_of_ge (L := lp) (hi := i)
      (lo := e) heI (by omega)
    have hp1 := headContribution_eq_neg_drain_of_ge (L := lq) (hi := i)
      (lo := e) heI (by omega)
    have hDrain : drain (i - e) = 1 :=
      ConfigurationThree.drain_eq_one (by omega)
    have hPosM : positiveChip m = 1 := by simp [positiveChip, hmPos.ne']
    rw [hPosM, hp0, hp1, hDrain]
    omega

end AtanasovRanganathan.ConfigurationFive
