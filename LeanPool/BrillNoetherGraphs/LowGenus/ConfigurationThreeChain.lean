/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationFive

/-!
# The chip-free three-chain, generic in the core

This file states one local picture and proves its residual-effectivity
statements once, generically in the core.

**The picture.**  A chip-free path `v₁ — v₂ — v₃` of three core vertices, with
two chip leaves `c₁, c₂` hanging off `v₁`, one chip leaf `c₃` off `v₂`, and one
chip leaf `c₄` off `v₃`.  The six displayed slots are all the slots incident to
`v₁, v₂, v₃`, and `c₁, c₂, c₃, c₄` carry the whole degree-four divisor.

**This is not one of Atanasov--Ranganathan's eleven configurations.**  It is
the natural extension of their configuration 3 -- their "Third" local picture,
a chip-free *edge* with two chip leaves at each end -- from a chip-free path of
length one to one of length two.  Proposition 5.1 of
Atanasov--Ranganathan does not list it, and they never need it: on the row-03
family (Figure 8, scope 3) they avoid it by placing two of the four chips at
*interior* points of edges, at length-dependent positions
(`a = |B5-A5|` along `B3-A3`, and `z = min(b, c)` along `41-43`).  A divisor
supported on core vertices cannot follow that route, and on row 03 no
core-supported degree-four divisor is covered by configurations 2, 3 and 5
alone; the chip-free set is always a path of three or four vertices.  Hence
this file.

**The two profiles.**  A chip must be delivered to each of `v₁` and `v₂` (on
row 03 the third chain vertex is the middle vertex of the mirrored picture, so
`v₃` is never a centre).  Write `m = min |c₁v₁| |c₂v₁|` for the shorter of the
two leaves at `v₁`, and put the two lower chips `c₃, c₄` at height `0`, the
ambient level -- `v₃`, `c₁`, `c₂` and everything off the picture -- at height
`base`.

*End centre* (`v₁`), `endCenter_*`:
```
base = min |v₃c₄| |v₂c₃|
mid  = min |v₂v₃| (min (|v₂c₃| - base) m)
top  = min |v₁v₂| (m - mid)
height v₃ = base,  height v₂ = base + mid,  height v₁ = base + mid + top
```

*Middle centre* (`v₂`), `midCenter_*`:
```
base = min |v₃c₄| |v₂c₃|
low  = min m (min |v₂v₃| (|v₂c₃| - base))
high = min |v₁v₂| (min (|v₂v₃| - low) (|v₂c₃| - base - low))
height v₃ = base,  height v₁ = base + low,  height v₂ = base + low + high
```

Both are nested minima of slot lengths, so every height collapses along with
any slot it spans: the same script therefore works verbatim on every nonloopy
forest face, exactly as in `ConfigurationFive`.

**The shift.**  When `|v₂v₃|` collapses, `v₂` and `v₃` become one class, and
the single incoming chip may sit at either end of that class depending on
whether `base` is attained at `|v₃c₄|` or at `|v₂c₃|`.  The row's chip
bookkeeping therefore carries one extra conditional transfer, `v₃ ⟶ v₂` guarded
by `|v₂v₃| = 0 ∧ |v₃c₄| < |v₂c₃|`; it appears below as the parameter `shift`.
With it in place each profile needs a *two*-branch target owner, not three.

Everything here is stated against an orientation-agnostic `ChainLedger`, so a
row instantiates each statement in whichever direction its core happens to
orient the two slots whose direction varies (`v₁c₁` and `v₂v₃` on row 03).
The one-edge arithmetic itself is `ConfigurationFive`'s and is reused
unchanged.
-/

namespace AtanasovRanganathan.ConfigurationThreeChain

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open ConfigurationFive

/-! ## The orientation ledger

`tail L hu hv` is the contribution at the end carrying height `hu`, `head`
the contribution at the end carrying `hv`.  A row picks `forward` when the
picture's first end is the core tail of the slot and `reverse` when it is the
core head. -/

structure ChainLedger where
  tail : ℕ → ℕ → ℕ → ℤ
  head : ℕ → ℕ → ℕ → ℤ
  tail_same : ∀ L h : ℕ, tail L h h = 0
  head_same : ∀ L h : ℕ, head L h h = 0
  tail_nonneg : ∀ {L hu hv : ℕ}, hv ≤ hu → hu ≤ hv + L → 0 ≤ tail L hu hv
  head_nonneg : ∀ {L hu hv : ℕ}, hu ≤ hv → hv ≤ hu + L → 0 ≤ head L hu hv
  tail_ge_neg_one : ∀ {L hu hv : ℕ}, hv ≤ hu + L → hu ≤ hv + L →
    -1 ≤ tail L hu hv
  head_ge_neg_one : ∀ {L hu hv : ℕ}, hv ≤ hu + L → hu ≤ hv + L →
    -1 ≤ head L hu hv
  tail_eq_one_of_full : ∀ {L hu hv : ℕ}, 0 < L → hu = hv + L →
    tail L hu hv = 1

namespace ChainLedger

variable (S : ChainLedger)

/-- A full slot delivers a chip at its lower end, and a collapsed slot has
already delivered the chip by contraction. -/
theorem zeroChip_add_tail_full (L hv : ℕ) :
    1 ≤ zeroChip L + S.tail L (hv + L) hv := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    simp [zeroChip, S.tail_same]
  · rw [S.tail_eq_one_of_full hL rfl]
    simp [zeroChip, hL.ne']

/-- A chip leaf gives away at most the one chip it carries. -/
theorem positiveChip_add_head_nonneg {L hu hv : ℕ}
    (h1 : hv ≤ hu) (h2 : hu ≤ hv + L) :
    0 ≤ positiveChip L + S.head L hu hv := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · have hEq : hu = hv := by omega
    subst hEq
    simp [positiveChip, hL, S.head_same]
  · have hGe := S.head_ge_neg_one (L := L) (hu := hu) (hv := hv)
      (by omega) (by omega)
    have hPos : positiveChip L = 1 := by simp [positiveChip, hL.ne']
    omega

end ChainLedger

/-- The slot read from its core tail. -/
def forward : ChainLedger where
  tail := tailContribution
  head := headContribution
  tail_same := tailContribution_same
  head_same := headContribution_same
  tail_nonneg h1 h2 := tailContribution_nonneg h1 h2
  head_nonneg h1 h2 := headContribution_nonneg h1 h2
  tail_ge_neg_one h1 h2 := tailContribution_ge_neg_one h1 h2
  head_ge_neg_one h1 h2 := headContribution_ge_neg_one h1 h2
  tail_eq_one_of_full h1 h2 := tailContribution_eq_one_of_full h1 h2

/-- The same slot read from its core head. -/
def reverse : ChainLedger where
  tail L hu hv := headContribution L hv hu
  head L hu hv := tailContribution L hv hu
  tail_same L h := headContribution_same L h
  head_same L h := tailContribution_same L h
  tail_nonneg h1 h2 := headContribution_nonneg h1 h2
  head_nonneg h1 h2 := tailContribution_nonneg h1 h2
  tail_ge_neg_one h1 h2 := headContribution_ge_neg_one h2 h1
  head_ge_neg_one h1 h2 := tailContribution_ge_neg_one h2 h1
  tail_eq_one_of_full h1 h2 := headContribution_eq_one_of_full h1 h2

/-- A nested minimum of three naturals is one of them.  Splitting the nested
minima by hand keeps the linear-arithmetic goals below small. -/
theorem min_three_le (a b c : ℕ) :
    min a (min b c) ≤ a ∧ min a (min b c) ≤ b ∧ min a (min b c) ≤ c :=
  ⟨Nat.min_le_left _ _,
    le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _),
    le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)⟩

/-- A nested minimum of three naturals is one of them. -/
theorem min_three_cases (a b c : ℕ) :
    min a (min b c) = a ∨ min a (min b c) = b ∨ min a (min b c) = c := by
  rcases min_choice a (min b c) with h | h
  · exact Or.inl h
  · rcases min_choice b c with h' | h'
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))

/-! ## The arithmetic of the nested minima

Everything the four residual statements need about a profile is one bundle of
inequalities and "which argument is attained" disjunctions, proved once.  Each
consumer then `clear`s the two *nested* minimum equations and works with plain
naturals, so no `omega` below re-derives a three-way minimum.  The two single
minima `m = min la lb` and `b = min u s` are left in place on purpose: `omega`
handles one `min` cheaply, and several branches want to split on it directly.

This is the shape `ConfigurationChippedTriangle.bounds`,
`ConfigurationReservoirChain.bounds` and `ConfigurationReservoirPair.bounds`
already use; this file was the one picture in the family still expanding its
minima at every call, and it was the most expensive module on the library's
critical path because of it (measured `7.7 s`, of which the profiler
attributed `9.8 s` of CPU to `omega` across twenty-one calls; `4.2 s` after).

Both bundles are `private`: they are an internal convenience, and every
exported statement in this file is unchanged. -/

/-- The three nested minima of the end-centre profile. -/
private theorem endBounds {la lb c s t u m b mid top i o : ℕ}
    (hm : m = min la lb) (hb : b = min u s)
    (hmid : mid = min t (min (s - b) m)) (htop : top = min c (m - mid))
    (hi : i = b + mid) (ho : o = i + top) :
    (b ≤ u ∧ b ≤ s) ∧ (b = u ∨ b = s)
      ∧ (m ≤ la ∧ m ≤ lb) ∧ (m = la ∨ m = lb)
      ∧ (mid ≤ t ∧ mid ≤ s - b ∧ mid ≤ m)
      ∧ (mid = t ∨ mid = s - b ∨ mid = m)
      ∧ (top ≤ c ∧ top ≤ m - mid) ∧ (top = c ∨ top = m - mid)
      ∧ (b ≤ i ∧ i ≤ o ∧ i ≤ b + t ∧ i ≤ s ∧ o ≤ b + m ∧ o ≤ i + c) := by
  subst hm hb hmid htop hi ho
  omega

/-- The three nested minima of the middle-centre profile. -/
private theorem midBounds {la lb c s t u m b low high i o : ℕ}
    (hm : m = min la lb) (hb : b = min u s)
    (hlow : low = min m (min t (s - b)))
    (hhigh : high = min c (min (t - low) (s - b - low)))
    (ho : o = b + low) (hi : i = o + high) :
    (b ≤ u ∧ b ≤ s) ∧ (b = u ∨ b = s)
      ∧ (m ≤ la ∧ m ≤ lb) ∧ (m = la ∨ m = lb)
      ∧ (low ≤ m ∧ low ≤ t ∧ low ≤ s - b)
      ∧ (low = m ∨ low = t ∨ low = s - b)
      ∧ (high ≤ c ∧ high ≤ t - low ∧ high ≤ s - b - low)
      ∧ (high = c ∨ high = t - low ∨ high = s - b - low)
      ∧ (b ≤ o ∧ o ≤ i ∧ i ≤ b + t ∧ i ≤ s ∧ o ≤ b + m ∧ i ≤ o + c) := by
  subst hm hb hlow hhigh ho hi
  omega

/-! ## The chip leaves

All four chip leaves obey the same one-line bound, whichever way the slot is
oriented and whatever the ambient height at the far end. -/

/-- Residual effectivity at a chip leaf of the picture. -/
theorem leaf_nonneg (S : ChainLedger) {L hu hv : ℕ}
    (h1 : hv ≤ hu) (h2 : hu ≤ hv + L) :
    0 ≤ positiveChip L + S.head L hu hv :=
  S.positiveChip_add_head_nonneg h1 h2

/-- The same bound for a leaf whose slot always points away from the chain. -/
theorem leaf_head_nonneg {L hu hv : ℕ}
    (h1 : hv ≤ hu) (h2 : hu ≤ hv + L) :
    0 ≤ positiveChip L + headContribution L hu hv :=
  forward.positiveChip_add_head_nonneg h1 h2

/-! ## The far chain vertex

`v₃` is shared by both profiles: it always sits at `base`, gives away at most
one chip along the middle slot `v₂v₃`, and is refilled by its own leaf `c₄`
whenever it does. -/

/-- Residual effectivity at the far chain vertex `v₃`. -/
theorem third_nonneg (Sm : ChainLedger) {s t u b i : ℕ} (shift : ℤ)
    (hb : b = min u s) (hbi : b ≤ i) (hit : i ≤ b + t)
    (hfull : i = b ∨ b = u)
    (hshift : shift = if t = 0 ∧ u < s then 1 else 0) :
    0 ≤ zeroChip u - shift +
      (Sm.head t i b + tailContribution u b 0) := by
  have hbu : b ≤ u := by omega
  have hLeaf : 0 ≤ tailContribution u b 0 :=
    tailContribution_nonneg (by omega) (by omega)
  have hMid : -1 ≤ Sm.head t i b :=
    Sm.head_ge_neg_one (by omega) (by omega)
  have hZero : (0 : ℤ) ≤ zeroChip u := zeroChip_nonneg u
  have hArmFull : b = u →
      1 ≤ zeroChip u + tailContribution u b 0 := by
    intro hEq
    have := ConfigurationFive.zeroChip_add_tail_full u
    rw [hEq]
    omega
  by_cases hs : t = 0 ∧ u < s
  · have hshift1 : shift = 1 := by rw [hshift, if_pos hs]
    have hib : i = b := by omega
    have hMidZero : Sm.head t i b = 0 := by
      rw [hib]
      exact Sm.head_same t b
    have hbu' : b = u := by omega
    have := hArmFull hbu'
    omega
  · have hshift0 : shift = 0 := by rw [hshift, if_neg hs]
    rcases hfull with hEq | hEq
    · have hMidZero : Sm.head t i b = 0 := by
        rw [hEq]
        exact Sm.head_same t b
      omega
    · have := hArmFull hEq
      omega

/-! ## The end-centre profile

`o` is the height at `v₁`, `i` at `v₂`, and the three nested minima saturate
outward from `v₃`. -/

/-- Residual effectivity at `v₁`, the centre of the end-centre profile. -/
theorem endCenter_first_nonneg (Sa : ChainLedger)
    {la lb c s t u m b mid top i o : ℕ} (k : ℤ)
    (hm : m = min la lb) (hb : b = min u s)
    (hmid : mid = min t (min (s - b) m)) (htop : top = min c (m - mid))
    (hi : i = b + mid) (ho : o = i + top)
    (hk : k ≤ 1) (hkOwner : 1 ≤ k → c ≠ 0 ∨ mid = m) :
    0 ≤ zeroChip la + zeroChip lb - k +
      (Sa.tail la o b + tailContribution lb o b +
        tailContribution c o i) := by
  obtain ⟨-, -, ⟨hmla, hmlb⟩, hmAtt, ⟨-, -, hmidM⟩, -, ⟨htopC, htopM⟩, htopAtt,
      -⟩ := endBounds hm hb hmid htop hi ho
  clear hmid htop
  have hArm0 : 0 ≤ Sa.tail la o b := Sa.tail_nonneg (by omega) (by omega)
  have hArm1 : 0 ≤ tailContribution lb o b :=
    tailContribution_nonneg (by omega) (by omega)
  have hMid : 0 ≤ tailContribution c o i :=
    tailContribution_nonneg (by omega) (by omega)
  have hZ0 : (0 : ℤ) ≤ zeroChip la := zeroChip_nonneg la
  have hZ1 : (0 : ℤ) ≤ zeroChip lb := zeroChip_nonneg lb
  by_cases hk0 : (1 : ℤ) ≤ k
  · have hFull : o = b + m ∨ (0 < c ∧ o = i + c) := by
      rcases hkOwner hk0 with hc | hmm
      · rcases Nat.eq_zero_or_pos c with hc0 | hcPos
        · exact absurd hc0 hc
        · rcases le_total c (m - mid) with _ | _
          · exact Or.inr ⟨hcPos, by omega⟩
          · exact Or.inl (by omega)
      · exact Or.inl (by omega)
    rcases hFull with hFull | ⟨hcPos, hFull⟩
    · rcases hmAtt with hla | hlb
      · have hOne : 1 ≤ zeroChip la + Sa.tail la o b := by
          rw [show o = b + la by omega]
          exact Sa.zeroChip_add_tail_full la b
        omega
      · have hOne : 1 ≤ zeroChip lb + tailContribution lb o b := by
          rw [show o = b + lb by omega]
          exact forward.zeroChip_add_tail_full lb b
        omega
    · have hOne : tailContribution c o i = 1 :=
        tailContribution_eq_one_of_full hcPos hFull
      omega
  · omega

/-- Residual effectivity at `v₂` in the end-centre profile. -/
theorem endCenter_second_nonneg (Sm : ChainLedger)
    {la lb c s t u m b mid top i o : ℕ} (k shift : ℤ)
    (hm : m = min la lb) (hb : b = min u s)
    (hmid : mid = min t (min (s - b) m)) (htop : top = min c (m - mid))
    (hi : i = b + mid) (ho : o = i + top)
    (hshift : shift = if t = 0 ∧ u < s then 1 else 0)
    (hk : k ≤ 1) (hkOwner : 1 ≤ k → c = 0 ∧ mid < m) :
    0 ≤ zeroChip s + shift - k +
      (headContribution c o i + tailContribution s i 0 +
        Sm.tail t i b) := by
  obtain ⟨-, -, -, -, ⟨hmidT, hmidS, hmidM⟩, hmidAtt, ⟨htopC, htopM⟩, -, -⟩ :=
    endBounds hm hb hmid htop hi ho
  clear hmid htop
  have hLeaf : 0 ≤ tailContribution s i 0 :=
    tailContribution_nonneg (by omega) (by omega)
  have hMidTwo : 0 ≤ Sm.tail t i b := Sm.tail_nonneg (by omega) (by omega)
  have hZs : (0 : ℤ) ≤ zeroChip s := zeroChip_nonneg s
  have hShift0 : 0 ≤ shift := by
    rw [hshift]; split_ifs <;> norm_num
  have hGain : mid < m →
      1 ≤ zeroChip s + shift + tailContribution s i 0 + Sm.tail t i b := by
    intro hlt
    have hLeafFull : i = s →
        1 ≤ zeroChip s + tailContribution s i 0 := by
      intro hEq
      have := ConfigurationFive.zeroChip_add_tail_full s
      rw [hEq]
      omega
    by_cases ht : t = 0
    · by_cases hus : u < s
      · have : shift = 1 := by rw [hshift, if_pos ⟨ht, hus⟩]
        omega
      · have := hLeafFull (by omega)
        omega
    · have hcase : i = s ∨ i = b + t := by
        rcases hmidAtt with h | h | h <;> omega
      rcases hcase with hEq | hEq
      · have := hLeafFull hEq
        omega
      · have hOne : Sm.tail t i b = 1 :=
          Sm.tail_eq_one_of_full (Nat.pos_of_ne_zero ht) hEq
        omega
  by_cases hk0 : (1 : ℤ) ≤ k
  · obtain ⟨hc, hlt⟩ := hkOwner hk0
    have hEq : o = i := by omega
    have hZero : headContribution c o i = 0 := by
      rw [hEq]; exact headContribution_same c i
    have := hGain hlt
    omega
  · by_cases hoi : o = i
    · have hZero : headContribution c o i = 0 := by
        rw [hoi]; exact headContribution_same c i
      omega
    · have := hGain (by omega)
      have hGe : -1 ≤ headContribution c o i :=
        headContribution_ge_neg_one (by omega) (by omega)
      omega

/-! ## The middle-centre profile

The same picture read at `v₂`: `v₁` now drains towards `v₂`, and the nested
minima saturate in the opposite order. -/

/-- Residual effectivity at `v₁` in the middle-centre profile. -/
theorem midCenter_first_nonneg (Sa : ChainLedger)
    {la lb c s t u m b low high i o : ℕ} (k : ℤ)
    (hm : m = min la lb) (hb : b = min u s)
    (hlow : low = min m (min t (s - b)))
    (hhigh : high = min c (min (t - low) (s - b - low)))
    (ho : o = b + low) (hi : i = o + high)
    (hk : k ≤ 1) (hkOwner : 1 ≤ k → c = 0 ∧ low = m) :
    0 ≤ zeroChip la + zeroChip lb - k +
      (Sa.tail la o b + tailContribution lb o b +
        tailContribution c o i) := by
  obtain ⟨-, -, ⟨hmla, hmlb⟩, hmAtt, ⟨hlowM, hlowT, hlowS⟩, hlowAtt,
      ⟨hhighC, hhighT, hhighS⟩, -, -⟩ := midBounds hm hb hlow hhigh ho hi
  clear hlow hhigh
  have hArm0 : 0 ≤ Sa.tail la o b := Sa.tail_nonneg (by omega) (by omega)
  have hArm1 : 0 ≤ tailContribution lb o b :=
    tailContribution_nonneg (by omega) (by omega)
  have hZ0 : (0 : ℤ) ≤ zeroChip la := zeroChip_nonneg la
  have hZ1 : (0 : ℤ) ≤ zeroChip lb := zeroChip_nonneg lb
  have hArmsFull : low = m →
      1 ≤ zeroChip la + zeroChip lb + Sa.tail la o b +
        tailContribution lb o b := by
    intro hEq
    rcases hmAtt with hla | hlb
    · have hOne : 1 ≤ zeroChip la + Sa.tail la o b := by
        rw [show o = b + la by omega]
        exact Sa.zeroChip_add_tail_full la b
      omega
    · have hOne : 1 ≤ zeroChip lb + tailContribution lb o b := by
        rw [show o = b + lb by omega]
        exact forward.zeroChip_add_tail_full lb b
      omega
  by_cases hk0 : (1 : ℤ) ≤ k
  · obtain ⟨hc, hlm⟩ := hkOwner hk0
    have hEq : o = i := by omega
    have hZero : tailContribution c o i = 0 := by
      rw [hEq]; exact tailContribution_same c i
    have hA := hArmsFull hlm
    omega
  · by_cases hio : o = i
    · have hZero : tailContribution c o i = 0 := by
        rw [hio]; exact tailContribution_same c i
      omega
    · have hlm : low = m := by
        rcases hlowAtt with h | h | h <;> omega
      have hA := hArmsFull hlm
      have hGe : -1 ≤ tailContribution c o i :=
        tailContribution_ge_neg_one (by omega) (by omega)
      omega

/-- Residual effectivity at `v₂`, the centre of the middle-centre profile. -/
theorem midCenter_second_nonneg (Sm : ChainLedger)
    {la lb c s t u m b low high i o : ℕ} (k shift : ℤ)
    (hm : m = min la lb) (hb : b = min u s)
    (hlow : low = min m (min t (s - b)))
    (hhigh : high = min c (min (t - low) (s - b - low)))
    (ho : o = b + low) (hi : i = o + high)
    (hshift : shift = if t = 0 ∧ u < s then 1 else 0)
    (hk : k ≤ 1) (hkOwner : 1 ≤ k → c ≠ 0 ∨ low ≠ m) :
    0 ≤ zeroChip s + shift - k +
      (headContribution c o i + tailContribution s i 0 +
        Sm.tail t i b) := by
  obtain ⟨⟨-, hbs⟩, -, -, -, hlowLe, hlowCases, hhighLe, hhighCases, -⟩ :=
    midBounds hm hb hlow hhigh ho hi
  clear hlow hhigh
  have hMidOne : 0 ≤ headContribution c o i :=
    headContribution_nonneg (by omega) (by omega)
  have hLeaf : 0 ≤ tailContribution s i 0 :=
    tailContribution_nonneg (by omega) (by omega)
  have hMidTwo : 0 ≤ Sm.tail t i b := Sm.tail_nonneg (by omega) (by omega)
  have hZs : (0 : ℤ) ≤ zeroChip s := zeroChip_nonneg s
  have hShift0 : 0 ≤ shift := by
    rw [hshift]; split_ifs <;> norm_num
  by_cases hk0 : (1 : ℤ) ≤ k
  · have hOwn := hkOwner hk0
    have hLeafFull : i = s →
        1 ≤ zeroChip s + tailContribution s i 0 := by
      intro hEq
      have := ConfigurationFive.zeroChip_add_tail_full s
      rw [hEq]
      omega
    by_cases ht : t = 0
    · by_cases hus : u < s
      · have : shift = 1 := by rw [hshift, if_pos ⟨ht, hus⟩]
        omega
      · have := hLeafFull (by omega)
        omega
    · have hcase : i = s ∨ i = b + t ∨ (0 < c ∧ i = o + c) := by
        rcases hhighCases with hH | hH | hH
        · rcases Nat.eq_zero_or_pos c with hc0 | hcPos
          · have hlm : low ≠ m := by
              rcases hOwn with hc | hlm
              · exact absurd hc0 hc
              · exact hlm
            rcases hlowCases with h | h | h
            · exact absurd h hlm
            · exact Or.inr (Or.inl (by omega))
            · exact Or.inl (by omega)
          · exact Or.inr (Or.inr ⟨hcPos, by omega⟩)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inl (by omega)
      rcases hcase with hEq | hEq | ⟨hcPos, hEq⟩
      · have := hLeafFull hEq
        omega
      · have hOne : Sm.tail t i b = 1 :=
          Sm.tail_eq_one_of_full (Nat.pos_of_ne_zero ht) hEq
        omega
      · have hOne : headContribution c o i = 1 :=
          headContribution_eq_one_of_full hcPos hEq
        omega
  · omega

end AtanasovRanganathan.ConfigurationThreeChain
