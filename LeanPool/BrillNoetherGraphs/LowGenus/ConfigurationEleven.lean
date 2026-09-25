/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedThree

/-!
# Atanasov--Ranganathan's eleventh configuration, generic in the core

This is the *eleventh* local picture of Atanasov--Ranganathan, Proposition 5.1
(`fig:configurations-for-genus-5`, the scope commented `%Eleventh`): a triangle
of chip-free vertices closed off by a banana, with one chip arm at each corner
and a fourth chip sitting **on** the near banana vertex.

```
        A1                B1                C1
        | alpha           | beta            | gamma
        A ---- S ---- B ---- u ---- Q ==m₁,m₂== P ---- w ---- C
        |                                                     |
        +------------------- t ------------------------------+
```

Chip-free: the apex `A`, the two banana-side vertices `B` and `C`, and the far
banana vertex `P`.  Chips: the three arm ends `A1`, `B1`, `C1`, and `Q`.  The
slots are `A-B` (`S`), `A-C` (`t`), `B-Q` (`u`), `C-P` (`w`), the banana
`P = Q` (`m₁, m₂`), and the three arms `alpha`, `beta`, `gamma`.

The solid subgraph of both scopes of the ninth family (atlas row `10`) is this
picture, in the special position where the apex arm equals the `C` arm. In the
formal script, **the chip on the banana is lifted with the chip-free banana
vertex**: if `Q` stayed at the ambient level
while `P` rose, `Q` would pay one chip along *each* of the two parallel slots
and has only one.  That is the same mechanism as
`ConfigurationBananaTail` (AR's *sixth* picture), and the profiles below mirror
its `E / D / C` nested minima term for term.

## The hypothesis, and its orientation

Everything below assumes

```
 alpha = gamma ≤ beta
```

--- the apex arm equals the `C` arm, and both are at most the `B` arm.  Every
row-10 chamber supplies exactly this: the chamber's first inequality places the
interior chip so that `alpha = gamma = min(a,b,c)`, and its second inequality is
`gamma ≤ beta`.  Only `gamma` appears below, standing for both arms.

The hypothesis is orientation-specific. Row 10 uses only the
`alpha = gamma` orientation, so that is the version stated here.

## The three profiles

Everything off the picture, and the three arm chips, sit at height `0`.  Write

```
 pq = min m₁ m₂            mB = min beta (gamma + S)       G = gamma + w
 E  = min G (mB + u + pq)  D  = min E (mB + u)             C = min D mB
```

for the target-`P` heights --- these are literally `ConfigurationBananaTail`'s
`E / D / C` under the substitution `m ↦ mB`, `|cd| ↦ u`, `|ef| ↦ G`, the far
route being two slots here (`C1 ⟶ C ⟶ P`) because `C` is chip free and carries
its own arm.  Then

```
 targets A and C:  h A = h B = h C = h P = h Q = gamma        (one script, two targets)
 target  B:        h A = h C = h P = h Q = gamma,
                   h B = min mB (gamma + u)
 target  P:        h A = h C = gamma,  h B = C,  h Q = D,  h P = E
```

Every height is a nested minimum of slot lengths, so it collapses along with any
slot it spans and the same script works on every nonloopy forest face, exactly
as in `ConfigurationFive`.

## The shift

When `u` collapses, `B` and `Q` are one class and `Q`'s two outgoing banana
chips have to be paid for out of `B`'s resources.  The row's chip bookkeeping
therefore carries one conditional transfer `B ⟶ Q`, guarded by `u = 0 ∧ D < E`;
it appears below as the parameter `shift`, exactly as in
`ConfigurationBananaTail`.  The other collapses are handled by the row's owner
choice rather than by a transfer: when `S = 0` the apex `A` lies in `B`'s class
and already carries the delivered chip, and when `w = 0` the vertex `C` lies in
`P`'s class and does.

Everything is stated against `ConfigurationMarkedThree.PairLedger`, so a row
instantiates each statement in whichever direction its core happens to orient
the slot, and so that an arm may be the *half* of a marked slot --- which is how
row 10 supplies `alpha = gamma` in the first place.  The one-edge arithmetic is
`ConfigurationFive`'s, reused unchanged.
-/

@[expose] public section

namespace AtanasovRanganathan.ConfigurationEleven

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open ConfigurationFive
open ConfigurationMarkedThree

/-! ## Two ledger facts the profiles below use

`PairLedger` states the full-ramp fact only at base height zero; both the `A-B`
slot and the `C-P` slot are climbed from the ambient height `gamma`, so the
general form is needed. -/

/-- A full slot delivers a chip at its upper end, from any base height; a
collapsed slot has already delivered it by contraction. -/
theorem zeroChip_add_tail_full' (S : PairLedger) (L hv : ℕ) :
    1 ≤ zeroChip L + S.tail L (hv + L) hv := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    simp [zeroChip, S.tail_same]
  · rw [S.tail_eq_one_of_full hL rfl]
    simp [zeroChip, hL.ne']

/-- A chip leaf gives away at most the single chip it carries. -/
theorem positiveChip_add_tail_nonneg (S : PairLedger) {L h : ℕ} (hh : h ≤ L) :
    0 ≤ positiveChip L + S.tail L 0 h := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · have : h = 0 := by omega
    subst hL
    simp [positiveChip, this, S.tail_same]
  · have hGe := S.tail_ge_neg_one (L := L) (hu := 0) (hv := h) (by omega) (by omega)
    have : positiveChip L = 1 := by simp [positiveChip, hL.ne']
    omega

/-! ## The apex `A` and the far vertex `C`

Both carry a *full* arm of length `gamma` -- that is the whole content of the
hypothesis `alpha = gamma` -- one slot to a neighbour that may sit higher (`B`
across `S` at `A`; `P` across `w` at `C`), and one slot to a neighbour that is
always at the same height (the `A-C` slot `t`, whose two ends carry `gamma` in
every profile). -/

/-- **Both flat neighbours: the chip is delivered.**  Used at `A` and `C` for
the flat profile, and at the vertex that owns the delivered chip when the slot
to the possibly-higher neighbour collapses. -/
theorem armFull_ge_one (SA Sx Sy : PairLedger) {gamma lx ly hx : ℕ}
    (hx0 : hx = gamma) :
    1 ≤ zeroChip gamma +
      (SA.tail gamma gamma 0 + Sx.tail lx gamma hx + Sy.tail ly gamma gamma) := by
  rw [hx0]
  have hA := zeroChip_add_tail_full' SA gamma 0
  have hX : Sx.tail lx gamma gamma = 0 := Sx.tail_same lx gamma
  have hY : Sy.tail ly gamma gamma = 0 := Sy.tail_same ly gamma
  simp only [Nat.zero_add] at hA
  omega

/-- **One higher neighbour: still effective.**  The full arm pays for the single
chip the higher neighbour draws. -/
theorem armFull_nonneg (SA Sx Sy : PairLedger) {gamma lx ly hx : ℕ}
    (hlo : gamma ≤ hx) (hhi : hx ≤ gamma + lx) :
    0 ≤ zeroChip gamma +
      (SA.tail gamma gamma 0 + Sx.tail lx gamma hx + Sy.tail ly gamma gamma) := by
  have hA := zeroChip_add_tail_full' SA gamma 0
  have hX : -1 ≤ Sx.tail lx gamma hx :=
    Sx.tail_ge_neg_one (by omega) (by omega)
  have hY : Sy.tail ly gamma gamma = 0 := Sy.tail_same ly gamma
  simp only [Nat.zero_add] at hA
  omega

/-- **The apex under the target-`P` profile.**  It gives up one chip to `B`'s
class when the `A-B` slot collapses -- that is the transfer which funds
`zeroChip S` in `armCenter_nonneg` below. -/
theorem apex_nonneg (SA Sx Sy : PairLedger) {gamma lx ly hx : ℕ}
    (hlo : gamma ≤ hx) (hhi : hx ≤ gamma + lx) (hzero : lx = 0 → hx = gamma) :
    0 ≤ zeroChip gamma - zeroChip lx +
      (SA.tail gamma gamma 0 + Sx.tail lx gamma hx + Sy.tail ly gamma gamma) := by
  have hA := zeroChip_add_tail_full' SA gamma 0
  have hY : Sy.tail ly gamma gamma = 0 := Sy.tail_same ly gamma
  simp only [Nat.zero_add] at hA
  rcases Nat.eq_zero_or_pos lx with hx0 | hxPos
  · have hEq := hzero hx0
    have hX : Sx.tail lx gamma hx = 0 := by
      rw [hEq]; exact Sx.tail_same lx gamma
    have hZ : zeroChip lx = 1 := by simp [zeroChip, hx0]
    omega
  · have hX : -1 ≤ Sx.tail lx gamma hx :=
      Sx.tail_ge_neg_one (by omega) (by omega)
    have hZ : zeroChip lx = 0 := by simp [zeroChip, hxPos.ne']
    omega

/-! ## The vertex `B` under the target-`B` profile

`B` alone rises, to `min beta (min (gamma + S) (gamma + u))`: it may not outrun
its own chip `B1`, may not draw more than the one chip `A`'s full arm delivers,
and may not draw more than the single chip sitting at `Q`.  Whichever of the
three caps is attained is a *full* slot at `B`, so `B` gains a chip. -/

/-- Residual effectivity at `B` under the target-`B` profile. -/
theorem targetB_nonneg (SB Ss Su : PairLedger) {beta gamma S u bt : ℕ}
    (hgb : gamma ≤ beta) (hbt : bt = min beta (min (gamma + S) (gamma + u))) :
    0 ≤ zeroChip beta +
      (SB.tail beta bt 0 + Ss.tail S bt gamma + Su.tail u bt gamma) := by
  have hB : 0 ≤ SB.tail beta bt 0 := SB.tail_nonneg (by omega) (by omega)
  have hS : 0 ≤ Ss.tail S bt gamma := Ss.tail_nonneg (by omega) (by omega)
  have hU : 0 ≤ Su.tail u bt gamma := Su.tail_nonneg (by omega) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip beta := zeroChip_nonneg beta
  omega

/-- **The target `B` is reached**, whenever neither of the two slots at `B` has
collapsed.  When `S = 0` the apex lies in `B`'s class and owns the chip
(`armFull_ge_one`); when `u = 0` the chip at `Q` does. -/
theorem targetB_ge_one (SB Ss Su : PairLedger) {beta gamma S u bt : ℕ}
    (hgb : gamma ≤ beta) (hbt : bt = min beta (min (gamma + S) (gamma + u)))
    (hS0 : 0 < S) (hu0 : 0 < u) :
    1 ≤ zeroChip beta +
      (SB.tail beta bt 0 + Ss.tail S bt gamma + Su.tail u bt gamma) := by
  have hB : 0 ≤ SB.tail beta bt 0 := SB.tail_nonneg (by omega) (by omega)
  have hS : 0 ≤ Ss.tail S bt gamma := Ss.tail_nonneg (by omega) (by omega)
  have hU : 0 ≤ Su.tail u bt gamma := Su.tail_nonneg (by omega) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip beta := zeroChip_nonneg beta
  have hcases : bt = beta ∨ bt = gamma + S ∨ bt = gamma + u := by omega
  rcases hcases with hFull | hFull | hFull
  · have hOne : 1 ≤ zeroChip beta + SB.tail beta bt 0 := by
      rw [hFull]
      have := zeroChip_add_tail_full' SB beta 0
      simpa using this
    omega
  · have hOne : Ss.tail S bt gamma = 1 := Ss.tail_eq_one_of_full hS0 (by omega)
    omega
  · have hOne : Su.tail u bt gamma = 1 := Su.tail_eq_one_of_full hu0 (by omega)
    omega

/-! ## The target-`P` profile

Three nested minima, `ConfigurationBananaTail`'s verbatim:

```
 E = min G (mB + u + pq)   -- the far banana vertex P
 D = min E (mB + u)        -- the chip Q
 C = min D mB              -- the chip-free B
```

with `mB = min beta (gamma + S)` -- `B`'s two resources, its own arm or the
apex's full arm followed by the full `A-B` slot -- and `G = gamma + w`, the far
route `C1 ⟶ C ⟶ P`, which is two slots here because `C` is chip free. -/

section TargetP

variable {beta gamma S t u w m1 m2 pq mB G E D C : ℕ}

/-- The comparisons every statement of this section runs on. -/
theorem chain_bounds (hgb : gamma ≤ beta)
    (hm : mB = min beta (gamma + S)) (hpq : pq = min m1 m2) (hG : G = gamma + w)
    (hE : E = min G (mB + u + pq)) (hD : D = min E (mB + u)) (hC : C = min D mB) :
    gamma ≤ C ∧ C ≤ D ∧ D ≤ E ∧ E ≤ G ∧ C ≤ beta ∧ C ≤ gamma + S ∧
      D ≤ C + u ∧ E ≤ D + m1 ∧ E ≤ D + m2 := by
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega⟩

/-- **Residual effectivity at `B`.**  If `B` sits strictly below `Q` it pays one
chip along the `B-Q` slot, and then its height is attained at one of its two
resources, which therefore delivers one.  The `shift` is the transfer to `Q`'s
class when the `B-Q` slot has collapsed. -/
theorem armCenter_nonneg (SB Ss Su : PairLedger) (shift : ℤ)
    (hgb : gamma ≤ beta)
    (hm : mB = min beta (gamma + S)) (hpq : pq = min m1 m2) (hG : G = gamma + w)
    (hE : E = min G (mB + u + pq)) (hD : D = min E (mB + u)) (hC : C = min D mB)
    (hshift : shift = if u = 0 ∧ D < E then 1 else 0) :
    0 ≤ zeroChip beta + zeroChip S - shift +
      (SB.tail beta C 0 + Ss.tail S C gamma + Su.tail u C D) := by
  have hB : 0 ≤ SB.tail beta C 0 := SB.tail_nonneg (by omega) (by omega)
  have hSs : 0 ≤ Ss.tail S C gamma := Ss.tail_nonneg (by omega) (by omega)
  have hZb : (0 : ℤ) ≤ zeroChip beta := zeroChip_nonneg beta
  have hZs : (0 : ℤ) ≤ zeroChip S := zeroChip_nonneg S
  have hArmsFull : C = mB →
      1 ≤ zeroChip beta + zeroChip S + (SB.tail beta C 0 + Ss.tail S C gamma) := by
    intro hEq
    rcases Nat.le_total beta (gamma + S) with hle | hle
    · have hOne : 1 ≤ zeroChip beta + SB.tail beta C 0 := by
        rw [show C = 0 + beta by omega]
        exact zeroChip_add_tail_full' SB beta 0
      omega
    · have hOne : 1 ≤ zeroChip S + Ss.tail S C gamma := by
        rw [show C = gamma + S by omega]
        exact zeroChip_add_tail_full' Ss S gamma
      omega
  by_cases hu : u = 0 ∧ D < E
  · have hshift1 : shift = 1 := by rw [hshift, if_pos hu]
    have hCD : C = D := by omega
    have hMid : Su.tail u C D = 0 := by
      rw [hCD]; exact Su.tail_same u D
    have := hArmsFull (by omega)
    omega
  · have hshift0 : shift = 0 := by rw [hshift, if_neg hu]
    by_cases hCD : C = D
    · have hMid : Su.tail u C D = 0 := by
        rw [hCD]; exact Su.tail_same u D
      omega
    · have hMid : -1 ≤ Su.tail u C D :=
        Su.tail_ge_neg_one (by omega) (by omega)
      have := hArmsFull (by omega)
      omega

/-- **Residual effectivity at the chip `Q`.**  It gives one chip away along each
banana slot whenever `P` rises above it, and is refilled along the `B-Q` slot
or, when that slot has collapsed, by the shift. -/
theorem bananaChip_nonneg (Su Sp Sq : PairLedger) (shift : ℤ)
    (_hgb : gamma ≤ beta)
    (hm : mB = min beta (gamma + S)) (hpq : pq = min m1 m2) (_hG : G = gamma + w)
    (hE : E = min G (mB + u + pq)) (hD : D = min E (mB + u)) (hC : C = min D mB)
    (hshift : shift = if u = 0 ∧ D < E then 1 else 0) :
    0 ≤ 1 + shift + (Su.tail u D C + Sp.tail m1 D E + Sq.tail m2 D E) := by
  have hMid : 0 ≤ Su.tail u D C := Su.tail_nonneg (by omega) (by omega)
  have hP1 : -1 ≤ Sp.tail m1 D E := Sp.tail_ge_neg_one (by omega) (by omega)
  have hP2 : -1 ≤ Sq.tail m2 D E := Sq.tail_ge_neg_one (by omega) (by omega)
  have hZ : 0 ≤ shift := by rw [hshift]; split_ifs <;> norm_num
  by_cases hDE : D = E
  · have h1 : Sp.tail m1 D E = 0 := by rw [hDE]; exact Sp.tail_same m1 E
    have h2 : Sq.tail m2 D E = 0 := by rw [hDE]; exact Sq.tail_same m2 E
    omega
  · by_cases hu : u = 0
    · have hshift1 : shift = 1 := by rw [hshift, if_pos ⟨hu, by omega⟩]
      have hCD : C = D := by omega
      have hZero : Su.tail u D C = 0 := by
        rw [hCD]; exact Su.tail_same u D
      omega
    · have hFull : Su.tail u D C = 1 :=
        Su.tail_eq_one_of_full (Nat.pos_of_ne_zero hu) (by omega)
      omega

/-- `Q` owns the delivered chip when a banana slot has collapsed: then `P` and
`Q` are one class and no rise crosses the banana at all. -/
theorem bananaChip_ge_one (Su Sp Sq : PairLedger) (shift : ℤ)
    (_hgb : gamma ≤ beta)
    (hm : mB = min beta (gamma + S)) (hpq : pq = min m1 m2) (_hG : G = gamma + w)
    (hE : E = min G (mB + u + pq)) (hD : D = min E (mB + u)) (hC : C = min D mB)
    (hshift : shift = if u = 0 ∧ D < E then 1 else 0) (hpq0 : pq = 0) :
    1 ≤ 1 + shift + (Su.tail u D C + Sp.tail m1 D E + Sq.tail m2 D E) := by
  have hDE : D = E := by omega
  have hMid : 0 ≤ Su.tail u D C := Su.tail_nonneg (by omega) (by omega)
  have h1 : Sp.tail m1 D E = 0 := by rw [hDE]; exact Sp.tail_same m1 E
  have h2 : Sq.tail m2 D E = 0 := by rw [hDE]; exact Sq.tail_same m2 E
  have hZ : 0 ≤ shift := by rw [hshift]; split_ifs <;> norm_num
  omega

/-- **Residual effectivity at the centre `P`.**  Every neighbour sits at or
below it. -/
theorem center_nonneg (Sp Sq Sw : PairLedger)
    (hgb : gamma ≤ beta)
    (hm : mB = min beta (gamma + S)) (hpq : pq = min m1 m2) (hG : G = gamma + w)
    (hE : E = min G (mB + u + pq)) (hD : D = min E (mB + u)) (_hC : C = min D mB) :
    0 ≤ Sp.tail m1 E D + Sq.tail m2 E D + Sw.tail w E gamma := by
  have h1 : 0 ≤ Sp.tail m1 E D := Sp.tail_nonneg (by omega) (by omega)
  have h2 : 0 ≤ Sq.tail m2 E D := Sq.tail_nonneg (by omega) (by omega)
  have h3 : 0 ≤ Sw.tail w E gamma := Sw.tail_nonneg (by omega) (by omega)
  omega

/-- **The centre `P` is reached.**  `P` gains only across a full slot, and it has
exactly two routes: the `C-P` slot, capped by `C`'s own residual at `gamma + w`,
or the shorter banana slot, which needs `Q` pushed up to `mB + u` first.  When
`w = 0` the vertex `C` lies in `P`'s class and owns the chip instead, and when
the banana collapses the chip at `Q` does. -/
theorem center_ge_one (Sp Sq Sw : PairLedger)
    (hgb : gamma ≤ beta)
    (hm : mB = min beta (gamma + S)) (hpq : pq = min m1 m2) (hG : G = gamma + w)
    (hE : E = min G (mB + u + pq)) (hD : D = min E (mB + u)) (_hC : C = min D mB)
    (hw : 0 < w) (hown : ¬ (pq = 0 ∧ mB + u < G)) :
    1 ≤ Sp.tail m1 E D + Sq.tail m2 E D + Sw.tail w E gamma := by
  have h1 : 0 ≤ Sp.tail m1 E D := Sp.tail_nonneg (by omega) (by omega)
  have h2 : 0 ≤ Sq.tail m2 E D := Sq.tail_nonneg (by omega) (by omega)
  have h3 : 0 ≤ Sw.tail w E gamma := Sw.tail_nonneg (by omega) (by omega)
  by_cases hEG : E = G
  · have hOne : Sw.tail w E gamma = 1 := Sw.tail_eq_one_of_full hw (by omega)
    omega
  · have hpqPos : 0 < pq := by
      by_contra hcon
      exact hown ⟨by omega, by omega⟩
    have hDeq : D = mB + u := by omega
    rcases Nat.le_total m1 m2 with hle | hle
    · have hOne : Sp.tail m1 E D = 1 := Sp.tail_eq_one_of_full (by omega) (by omega)
      omega
    · have hOne : Sq.tail m2 E D = 1 := Sq.tail_eq_one_of_full (by omega) (by omega)
      omega

end TargetP

end AtanasovRanganathan.ConfigurationEleven
