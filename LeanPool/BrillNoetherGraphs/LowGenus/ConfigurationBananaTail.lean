/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationThreeChain

/-!
# Atanasov--Ranganathan's sixth configuration, generic in the core

This is the *sixth* local picture of Atanasov--Ranganathan, Proposition 5.1
(`fig:configurations-for-genus-5`, the scope commented `%Sixth`):

```
   a       b            a, b, d, f carry the four chips
    \     /             c, e are chip free
      \ /
       c
       |                c -- d  is the middle slot
       d
      / \                d == e is a banana (two parallel slots)
      \ /
       e
       |                e -- f  is the tail slot
       f
```

Note on the file name: the AR numbering is not available here, because
`ConfigurationThreeChain.lean` in this directory is the chip-free *three*-chain,
which is not one of AR's eleven pictures at all.  This file is named after
the geometry instead -- the centre sits at the far end of a banana whose near
end carries a chip -- and the docstrings say which AR picture is meant.

**Relation to `ConfigurationFive`.**  Configuration 5 is drawn on the same
underlying graph, with the chips moved: there `e` carries a chip and `d` is
chip free, so the banana runs from a chip-free vertex *into* a chip.  Here it
runs from the chip at `d` *out* to the chip-free `e`, which is what makes the
picture genuinely different: `d` must give away one chip along each of the two
parallel slots, so it has to be refilled along `c -- d`, and `c` in turn along
its two arms.

**Only the `e`-centre profile is proved here.**  On row 14 the other chip-free
vertex `c` of the picture happens to be a configuration-2 tripod as well (all
three of its slots end on chips), so it is covered by `ConfigurationTwo` and
the `c`-centre profile is never needed.  Should a later row need it, it goes
next to `center_nonneg` below.

**The profile.**  Write `m = min |ca| |cb|` and `pq = min |de₁| |de₂|`, and
put the chips `a`, `b`, `f` and everything off the picture at height `0`:
```
E = min |ef| (m + |cd| + pq)      -- height at the centre e
D = min E (m + |cd|)              -- height at the chip d
C = min D m                       -- height at the chip-free c
```
Three nested minima of slot lengths, so every height collapses along with any
slot it spans and the same script works on every nonloopy forest face.

**The shift.**  When `|cd|` collapses, `c` and `d` are one class, and `d`'s two
outgoing banana chips have to be paid for by `c`'s two arms.  The row's chip
bookkeeping therefore carries one conditional transfer `c ⟶ d`, guarded by
`|cd| = 0 ∧ D < E`; it appears below as the parameter `shift`.  With it the
target owner has only two branches: the centre `e`, except when a banana slot
collapses and the tail slot is too long to reach, where the chip sits on `d`.

The one-edge arithmetic is `ConfigurationFive`'s, reused unchanged, and the
orientation ledger extends `ConfigurationThreeChain.ChainLedger` by the one fact the
proofs below need that it does not carry.
-/

@[expose] public section

namespace AtanasovRanganathan.ConfigurationBananaTail

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open ConfigurationFive
open ConfigurationThreeChain

/-! ## The orientation ledger -/

/-- A `ChainLedger` that also knows when the far end of a full slot receives
the chip.  `tail L hu hv` is the contribution at the end carrying height `hu`,
`head L hu hv` the contribution at the end carrying `hv`. -/
structure BananaLedger extends ChainLedger where
  head_eq_one_of_full : ∀ {L hu hv : ℕ}, 0 < L → hv = hu + L →
    toChainLedger.head L hu hv = 1

/-- The slot read from its core tail. -/
def fwd : BananaLedger where
  toChainLedger := ConfigurationThreeChain.forward
  head_eq_one_of_full h1 h2 := headContribution_eq_one_of_full h1 h2

/-- The same slot read from its core head. -/
def rev : BananaLedger where
  toChainLedger := ConfigurationThreeChain.reverse
  head_eq_one_of_full h1 h2 := tailContribution_eq_one_of_full h1 h2

/-! ## The chip leaves

`a`, `b` and `f` each give away at most the single chip they carry. -/

/-- Residual effectivity at a chip leaf of the picture. -/
theorem leaf_nonneg (S : BananaLedger) {L hu hv : ℕ}
    (h1 : hv ≤ hu) (h2 : hu ≤ hv + L) :
    0 ≤ positiveChip L + S.head L hu hv :=
  S.toChainLedger.positiveChip_add_head_nonneg h1 h2

/-! ## The chip-free arm vertex `c` -/

/-- Residual effectivity at the chip-free vertex `c`, which feeds the chip at
`d` along the middle slot and is refilled by its two arms. -/
theorem armCenter_nonneg (Sa Sb Sw : BananaLedger)
    {la lb w p q u m pq C D E : ℕ} (shift : ℤ)
    (hm : m = min la lb) (hpq : pq = min p q)
    (hE : E = min u (m + w + pq)) (hD : D = min E (m + w)) (hC : C = min D m)
    (hshift : shift = if w = 0 ∧ D < E then 1 else 0) :
    0 ≤ zeroChip la + zeroChip lb - shift +
      (Sa.tail la C 0 + Sb.tail lb C 0 + Sw.tail w C D) := by
  have hCD : C ≤ D := by omega
  have hDw : D ≤ C + w := by omega
  have hArm0 : 0 ≤ Sa.tail la C 0 :=
    Sa.toChainLedger.tail_nonneg (by omega) (by omega)
  have hArm1 : 0 ≤ Sb.tail lb C 0 :=
    Sb.toChainLedger.tail_nonneg (by omega) (by omega)
  have hZ0 : (0 : ℤ) ≤ zeroChip la := zeroChip_nonneg la
  have hZ1 : (0 : ℤ) ≤ zeroChip lb := zeroChip_nonneg lb
  have hArmsFull : C = m →
      1 ≤ zeroChip la + zeroChip lb + Sa.tail la C 0 + Sb.tail lb C 0 := by
    intro hEq
    rcases min_choice la lb with hla | hlb
    · have hOne : 1 ≤ zeroChip la + Sa.tail la C 0 := by
        have := Sa.toChainLedger.zeroChip_add_tail_full la 0
        rw [show C = 0 + la by omega]
        omega
      omega
    · have hOne : 1 ≤ zeroChip lb + Sb.tail lb C 0 := by
        have := Sb.toChainLedger.zeroChip_add_tail_full lb 0
        rw [show C = 0 + lb by omega]
        omega
      omega
  by_cases hw : w = 0 ∧ D < E
  · have hshift1 : shift = 1 := by rw [hshift, ite_eq_left hw]
    have hCDeq : C = D := by omega
    have hMidZero : Sw.tail w C D = 0 := by
      rw [hCDeq]
      exact Sw.toChainLedger.tail_same w D
    have := hArmsFull (by omega)
    omega
  · have hshift0 : shift = 0 := by rw [hshift, ite_eq_right hw]
    by_cases hCDeq : C = D
    · have hMidZero : Sw.tail w C D = 0 := by
        rw [hCDeq]
        exact Sw.toChainLedger.tail_same w D
      omega
    · have hMid : -1 ≤ Sw.tail w C D :=
        Sw.toChainLedger.tail_ge_neg_one (by omega) (by omega)
      have := hArmsFull (by omega)
      omega

/-! ## The chip at the near end of the banana -/

/-- Residual effectivity at the chip `d`.  It gives away one chip along each
of the two parallel slots and is refilled either along the middle slot or, if
that slot has collapsed, by the shift. -/
theorem bananaChip_nonneg (Sw Sp Sq : BananaLedger)
    {la lb w p q u m pq C D E : ℕ} (shift k : ℤ)
    (hm : m = min la lb) (hpq : pq = min p q)
    (hE : E = min u (m + w + pq)) (hD : D = min E (m + w)) (hC : C = min D m)
    (hshift : shift = if w = 0 ∧ D < E then 1 else 0)
    (hk : k ≤ 1) (hkOwner : 1 ≤ k → pq = 0) :
    0 ≤ 1 + shift - k +
      (Sw.head w C D + Sp.tail p D E + Sq.tail q D E) := by
  have hCD : C ≤ D := by omega
  have hDw : D ≤ C + w := by omega
  have hDE : D ≤ E := by omega
  have hEp : E ≤ D + p := by omega
  have hEq : E ≤ D + q := by omega
  have hMid : 0 ≤ Sw.head w C D :=
    Sw.toChainLedger.head_nonneg (by omega) (by omega)
  have hPar0 : -1 ≤ Sp.tail p D E :=
    Sp.toChainLedger.tail_ge_neg_one (by omega) (by omega)
  have hPar1 : -1 ≤ Sq.tail q D E :=
    Sq.toChainLedger.tail_ge_neg_one (by omega) (by omega)
  have hShift0 : 0 ≤ shift := by rw [hshift]; split_ifs <;> norm_num
  by_cases hDEeq : D = E
  · have hp : Sp.tail p D E = 0 := by
      rw [hDEeq]; exact Sp.toChainLedger.tail_same p E
    have hq : Sq.tail q D E = 0 := by
      rw [hDEeq]; exact Sq.toChainLedger.tail_same q E
    omega
  · have hkZero : k ≤ 0 := by
      by_contra hcon
      have hpq0 := hkOwner (by omega)
      omega
    by_cases hw : w = 0
    · have hshift1 : shift = 1 := by
        rw [hshift, ite_eq_left ⟨hw, by omega⟩]
      have hCDeq : C = D := by omega
      have hMidZero : Sw.head w C D = 0 := by
        rw [hCDeq]; exact Sw.toChainLedger.head_same w D
      omega
    · have hFull : Sw.head w C D = 1 :=
        Sw.head_eq_one_of_full (Nat.pos_of_ne_zero hw) (by omega)
      omega

/-! ## The centre -/

/-- Residual effectivity at the centre `e`, the chip-free far end of the
banana. -/
theorem center_nonneg (Sp Sq Su : BananaLedger)
    {la lb w p q u m pq C D E : ℕ} (k : ℤ)
    (hm : m = min la lb) (hpq : pq = min p q)
    (hE : E = min u (m + w + pq)) (hD : D = min E (m + w)) (_hC : C = min D m)
    (hk : k ≤ 1) (hkOwner : 1 ≤ k → ¬(pq = 0 ∧ m + w < u)) :
    0 ≤ zeroChip u - k +
      (Sp.head p D E + Sq.head q D E + Su.tail u E 0) := by
  have hDE : D ≤ E := by omega
  have hEp : E ≤ D + p := by omega
  have hEqq : E ≤ D + q := by omega
  have hEu : E ≤ u := by omega
  have hPar0 : 0 ≤ Sp.head p D E :=
    Sp.toChainLedger.head_nonneg (by omega) (by omega)
  have hPar1 : 0 ≤ Sq.head q D E :=
    Sq.toChainLedger.head_nonneg (by omega) (by omega)
  have hTail : 0 ≤ Su.tail u E 0 :=
    Su.toChainLedger.tail_nonneg (by omega) (by omega)
  have hZu : (0 : ℤ) ≤ zeroChip u := zeroChip_nonneg u
  by_cases hk0 : (1 : ℤ) ≤ k
  · have hOwn := hkOwner hk0
    by_cases hEuEq : E = u
    · have hOne : 1 ≤ zeroChip u + Su.tail u E 0 := by
        have := Su.toChainLedger.zeroChip_add_tail_full u 0
        rw [show E = 0 + u by omega]
        omega
      omega
    · have hSplit : E = m + w + pq ∧ m + w + pq < u := by omega
      have hpqPos : 0 < pq := by
        by_contra hcon
        exact hOwn ⟨by omega, by omega⟩
      have hDeq : D = m + w := by omega
      rcases min_choice p q with hp | hq
      · have hOne : Sp.head p D E = 1 :=
          Sp.head_eq_one_of_full (by omega) (by omega)
        omega
      · have hOne : Sq.head q D E = 1 :=
          Sq.head_eq_one_of_full (by omega) (by omega)
        omega
  · omega

end AtanasovRanganathan.ConfigurationBananaTail
