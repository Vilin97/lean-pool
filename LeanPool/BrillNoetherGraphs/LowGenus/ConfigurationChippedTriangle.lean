/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedThree

/-!
# The chipped triangle

This is the solid subgraph of Atanasov--Ranganathan's *second* scope for their
seventh genus-five family (atlas row `08`).  It is **not** one of the eleven
pictures of their Proposition 5.1: the closest, the *Eighth*, is a triangle with
three chip arms too, but its triangle is chip **free** and it carries the extra
hypothesis that one arm has length `min` of the other two, which row 08's second
chamber does not supply.  The module is therefore named for its geometry,
following the `ConfigurationThreeChain` / `ConfigurationBananaTail` /
`ConfigurationBananaDoubleChip` precedent.

```
        A            B           A, B, C each carry a chip
        |            |           c carries a chip as well
        u ==== q ====v           u, v are chip free
         \          /            |c u| = p, |u v| = q, |c v| = r
          p        r             |u A| = al, |v B| = be, |c C| = ga
            \    /
              c
              |
              C
```

Four chips in all: one on `c`, one at the end of each of the three arms.  The
target is `u`; the picture is read a second time at `v` by swapping `u ↔ v`,
`al ↔ be`, `p ↔ r`.  The profile is four nested minima,

```
 hc = min ga (min al be)                        -- the chipped vertex
 h0 = min be (hc + r)                           -- the partner, before clamping
 ht = min al (min (hc + p) (h0 + q))            -- the target
 hv = min h0 ht                                 -- the partner
```

The three ways `u` gets its chip are the three arguments of `ht`: its own arm
goes full, or the triangle slot from `c` goes full and `c` refills along `ga`,
or the triangle slot from `v` goes full.

The final clamp `hv = min h0 ht` ensures that the partner does not rise above
the target; this is used in the slot-ledger inequalities below.

**One chip moves inside a contracted class.**  When the triangle slot `c - v`
collapses (`r = 0`) *and* `c` sits strictly above the partner's arm
(`hc < be`), the partner has to pay one unit across `q` that neither its own arm
nor the collapsed slot can supply; `c` and `v` are then the same contracted
class, so `c` lends it the chip it is sitting on.  That transfer is `lend`, and
it is the only allocation the picture needs.
-/

@[expose] public section

namespace AtanasovRanganathan.ConfigurationChippedTriangle

open Utilities

open Certificate
open Certificate.ExplicitPotential
open ConfigurationFive
open ConfigurationMarkedThree

/-! ## The four nested minima -/

/-- The height at the chipped triangle vertex `c`. -/
def chipHeight (al be ga : ℕ) : ℕ := min ga (min al be)

/-- The partner's height before the final clamp. -/
def sideHeight (al be ga r : ℕ) : ℕ := min be (chipHeight al be ga + r)

/-- The height at the target `u`. -/
def targetHeight (al be ga p q r : ℕ) : ℕ :=
  min al (min (chipHeight al be ga + p) (sideHeight al be ga r + q))

/-- The height at the partner `v`, clamped so that `v` is never deeper than the
target -- without this clamp the picture breaks (see the module docstring). -/
def partnerHeight (al be ga p q r : ℕ) : ℕ :=
  min (sideHeight al be ga r) (targetHeight al be ga p q r)

/-- The chip `c` lends its partner when the slot between them has collapsed and
`c` is strictly shallower than the partner's own arm. -/
def lend (r hc be : ℕ) : ℤ := if r = 0 ∧ hc < be then 1 else 0

theorem lend_nonneg (r hc be : ℕ) : 0 ≤ lend r hc be := by
  unfold lend; split_ifs <;> norm_num

theorem lend_eq_one {r hc be : ℕ} (hr : r = 0) (hlt : hc < be) :
    lend r hc be = 1 := by
  unfold lend; rw [if_pos ⟨hr, hlt⟩]

theorem lend_cases (r hc be : ℕ) : lend r hc be = 0 ∨ lend r hc be = 1 := by
  unfold lend; split_ifs <;> simp

theorem eq_of_lend_eq_one {r hc be : ℕ} (h : lend r hc be = 1) :
    r = 0 ∧ hc < be := by
  by_cases hcond : r = 0 ∧ hc < be
  · exact hcond
  · rw [lend, if_neg hcond] at h
    exact absurd h (by norm_num)

/-! ## The arithmetic of the four minima

Everything the three residual statements need about the profile is this one
bundle of inequalities and "which argument is attained" disjunctions; each
consumer then works with plain naturals and `omega`. -/

theorem bounds {al be ga p q r hc h0 ht hv : ℕ}
    (hhc : hc = chipHeight al be ga) (hh0 : h0 = sideHeight al be ga r)
    (hht : ht = targetHeight al be ga p q r)
    (hhv : hv = partnerHeight al be ga p q r) :
    (hc ≤ ga ∧ hc ≤ al ∧ hc ≤ be) ∧ (hc = ga ∨ hc = al ∨ hc = be)
      ∧ (h0 ≤ be ∧ h0 ≤ hc + r ∧ hc ≤ h0) ∧ (h0 = be ∨ h0 = hc + r)
      ∧ (ht ≤ al ∧ ht ≤ hc + p ∧ ht ≤ h0 + q ∧ hc ≤ ht)
      ∧ (ht = al ∨ ht = hc + p ∨ ht = h0 + q)
      ∧ (hv ≤ h0 ∧ hv ≤ ht ∧ hc ≤ hv ∧ ht ≤ hv + q ∧ hv ≤ hc + r ∧ hv ≤ be)
      ∧ (hv = h0 ∨ hv = ht) := by
  subst hhc hh0 hht hhv
  simp only [partnerHeight, targetHeight, sideHeight, chipHeight]
  omega

/-! ## Who owns the delivered chip -/

/-- The target delivers its own chip: its arm goes full, or one of the two
triangle slots at it goes full. -/
def Delivers (al p q hc h0 ht : ℕ) : Prop :=
  ht = al ∨ (0 < p ∧ ht = hc + p) ∨ (0 < q ∧ ht = h0 + q)

instance (al p q hc h0 ht : ℕ) : Decidable (Delivers al p q hc h0 ht) := by
  unfold Delivers; infer_instance

/-- The partner can be charged instead.  Both disjuncts force `hv = ht`, so the
partner never pays across `q` in this situation. -/
def PartnerOwns (be p q r hc h0 ht : ℕ) : Prop :=
  (q = 0 ∧ ht = h0) ∨ (p = 0 ∧ r = 0 ∧ hc < be)

/-- When the target does not deliver, one of the two triangle slots at it has
collapsed -- which is what puts the fallback owner in the target's class. -/
theorem cases_of_not_delivers {al be ga p q r hc h0 ht hv : ℕ}
    (hhc : hc = chipHeight al be ga) (hh0 : h0 = sideHeight al be ga r)
    (hht : ht = targetHeight al be ga p q r)
    (hhv : hv = partnerHeight al be ga p q r)
    (h : ¬ Delivers al p q hc h0 ht) :
    (p = 0 ∧ ht = hc) ∨ (q = 0 ∧ ht = h0) := by
  obtain ⟨-, -, -, -, ⟨-, hthc, -, hcht⟩, htAtt, -, -⟩ := bounds hhc hh0 hht hhv
  unfold Delivers at h
  omega

theorem partnerOwns_of_not_delivers {al be ga p q r hc h0 ht hv : ℕ}
    (hhc : hc = chipHeight al be ga) (hh0 : h0 = sideHeight al be ga r)
    (hht : ht = targetHeight al be ga p q r)
    (hhv : hv = partnerHeight al be ga p q r)
    (h : ¬ Delivers al p q hc h0 ht) (h2 : ¬ (p = 0 ∧ lend r hc be = 0)) :
    PartnerOwns be p q r hc h0 ht := by
  rcases cases_of_not_delivers hhc hh0 hht hhv h with ⟨hp, -⟩ | ⟨hq, hEq⟩
  · have hne : lend r hc be ≠ 0 := fun hz => h2 ⟨hp, hz⟩
    rcases lend_cases r hc be with hz | ho
    · exact absurd hz hne
    · obtain ⟨hr, hlt⟩ := eq_of_lend_eq_one ho
      exact Or.inr ⟨hp, hr, hlt⟩
  · exact Or.inl ⟨hq, hEq⟩

/-- The fallback owner is in the target's contracted class: either the slot to
the partner has collapsed, or both slots at the chipped vertex have. -/
theorem class_of_not_delivers {al be ga p q r hc h0 ht hv : ℕ}
    (hhc : hc = chipHeight al be ga) (hh0 : h0 = sideHeight al be ga r)
    (hht : ht = targetHeight al be ga p q r)
    (hhv : hv = partnerHeight al be ga p q r)
    (h : ¬ Delivers al p q hc h0 ht) (h2 : ¬ (p = 0 ∧ lend r hc be = 0)) :
    q = 0 ∨ (p = 0 ∧ r = 0) := by
  rcases partnerOwns_of_not_delivers hhc hh0 hht hhv h h2 with ⟨hq, -⟩ | ⟨hp, hr, -⟩
  · exact Or.inl hq
  · exact Or.inr ⟨hp, hr⟩

/-! ## The three residual statements

Each arm and each triangle slot may be a whole slot read from either end or the
half of a marked slot, so all six are read through a `PairLedger`, exactly as in
`ConfigurationMarkedThree`.  `S.tail L x y` is the contribution at the end
carrying height `x`. -/

/-- **The target.**  `k` is one exactly when the delivered chip is charged
here. -/
theorem triangleTarget_nonneg (SA SP SQ : PairLedger)
    {al be ga p q r hc h0 ht hv : ℕ} {k : ℤ}
    (hhc : hc = chipHeight al be ga) (hh0 : h0 = sideHeight al be ga r)
    (hht : ht = targetHeight al be ga p q r)
    (hhv : hv = partnerHeight al be ga p q r)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hk : k = 1 → Delivers al p q hc h0 ht) :
    0 ≤ zeroChip al - k +
      (SA.tail al ht 0 + SP.tail p ht hc + SQ.tail q ht hv) := by
  obtain ⟨-, -, ⟨-, -, -⟩, -, ⟨htal, hthc, hth0, hcht⟩, -,
    ⟨hvh0, hvht, hchv, hthv, -, -⟩, hvAtt⟩ := bounds hhc hh0 hht hhv
  have hA : 0 ≤ SA.tail al ht 0 := SA.tail_nonneg (Nat.zero_le _) (by omega)
  have hP : 0 ≤ SP.tail p ht hc := SP.tail_nonneg (by omega) (by omega)
  have hQ : 0 ≤ SQ.tail q ht hv := SQ.tail_nonneg (by omega) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip al := zeroChip_nonneg al
  rcases eq_or_lt_of_le hk1 with hkOne | hkLt
  · rcases hk hkOne with hFull | ⟨hp, hFull⟩ | ⟨hq, hFull⟩
    · have hOne : 1 ≤ zeroChip al + SA.tail al ht 0 := by
        rw [hFull]; exact SA.zeroChip_add_tail_full al
      omega
    · have hOne : SP.tail p ht hc = 1 := SP.tail_eq_one_of_full hp (by omega)
      omega
    · have hOne : SQ.tail q ht hv = 1 := SQ.tail_eq_one_of_full hq (by omega)
      omega
  · omega

/-- **The partner.**  It pays across `q` only when its own arm or the slot to
the chipped vertex is full, or when `c` lends it the chip it sits on. -/
theorem trianglePartner_nonneg (SB SR SQ : PairLedger)
    {al be ga p q r hc h0 ht hv : ℕ} {k : ℤ}
    (hhc : hc = chipHeight al be ga) (hh0 : h0 = sideHeight al be ga r)
    (hht : ht = targetHeight al be ga p q r)
    (hhv : hv = partnerHeight al be ga p q r)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hk : k = 1 → PartnerOwns be p q r hc h0 ht) :
    0 ≤ zeroChip be + lend r hc be - k +
      (SB.tail be hv 0 + SR.tail r hv hc + SQ.tail q hv ht) := by
  obtain ⟨⟨-, -, hcbe⟩, -, ⟨h0be, h0hc, hch0⟩, h0Att, ⟨-, hthc, hth0, hcht⟩, -,
    ⟨hvh0, hvht, hchv, hthv, hvhcr, hvbe⟩, hvAtt⟩ := bounds hhc hh0 hht hhv
  have hB : 0 ≤ SB.tail be hv 0 := SB.tail_nonneg (Nat.zero_le _) (by omega)
  have hR : 0 ≤ SR.tail r hv hc := SR.tail_nonneg (by omega) (by omega)
  have hQ : -1 ≤ SQ.tail q hv ht := SQ.tail_ge_neg_one (by omega) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip be := zeroChip_nonneg be
  have hL : (0 : ℤ) ≤ lend r hc be := lend_nonneg r hc be
  -- one unit of supply, available whenever the partner sits at `h0`
  have key : hv = h0 →
      1 ≤ zeroChip be + lend r hc be + (SB.tail be hv 0 + SR.tail r hv hc) := by
    intro hEq
    by_cases hbe : be ≤ hc + r
    · have hvbe' : hv = be := by omega
      have hfull : 1 ≤ zeroChip be + SB.tail be hv 0 := by
        rw [hvbe']; exact SB.zeroChip_add_tail_full be
      omega
    · by_cases hr : 0 < r
      · have hone : SR.tail r hv hc = 1 := SR.tail_eq_one_of_full hr (by omega)
        omega
      · have hlend : lend r hc be = 1 := lend_eq_one (by omega) (by omega)
        omega
  by_cases hEq : hv = ht
  · have hQ0 : SQ.tail q hv ht = 0 := by rw [hEq]; exact SQ.tail_same q ht
    rcases eq_or_lt_of_le hk1 with hkOne | hkLt
    · rcases hk hkOne with ⟨hq0, hEq0⟩ | ⟨hp0, hr0, hlt⟩
      · have := key (by omega)
        omega
      · have hlend : lend r hc be = 1 := lend_eq_one hr0 hlt
        omega
    · omega
  · have hlt : hv < ht := by omega
    have hkZero : k = 0 := by
      rcases eq_or_lt_of_le hk1 with hkOne | hkLt
      · exfalso
        rcases hk hkOne with ⟨hq0, hEq0⟩ | ⟨hp0, hr0, -⟩
        · omega
        · omega
      · omega
    have := key (by omega)
    omega

/-- **The chipped vertex.**  It always has the slack of the chip it carries, so
it can absorb both triangle slots running full away from it -- and when they
both do, its own arm is full as well. -/
theorem triangleChipped_nonneg (SG SP SR : PairLedger)
    {al be ga p q r hc h0 ht hv : ℕ} {k : ℤ}
    (hhc : hc = chipHeight al be ga) (hh0 : h0 = sideHeight al be ga r)
    (hht : ht = targetHeight al be ga p q r)
    (hhv : hv = partnerHeight al be ga p q r)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hk : k = 1 → p = 0 ∧ lend r hc be = 0) :
    0 ≤ 1 + zeroChip ga - lend r hc be - k +
      (SG.tail ga hc 0 + SP.tail p hc ht + SR.tail r hc hv) := by
  obtain ⟨⟨hcga, hcal, hcbe⟩, hcAtt, -, -, ⟨htal, hthc, -, hcht⟩, -,
    ⟨-, hvht, hchv, -, hvhcr, hvbe⟩, -⟩ := bounds hhc hh0 hht hhv
  have hG : 0 ≤ SG.tail ga hc 0 := SG.tail_nonneg (Nat.zero_le _) (by omega)
  have hP : -1 ≤ SP.tail p hc ht := SP.tail_ge_neg_one (by omega) (by omega)
  have hR : -1 ≤ SR.tail r hc hv := SR.tail_ge_neg_one (by omega) (by omega)
  have hZ : (0 : ℤ) ≤ zeroChip ga := zeroChip_nonneg ga
  have hArm : hc = ga → 1 ≤ zeroChip ga + SG.tail ga hc 0 := by
    intro h; rw [h]; exact SG.zeroChip_add_tail_full ga
  have hPzero : hc = ht → SP.tail p hc ht = 0 := by
    intro h; rw [h]; exact SP.tail_same p ht
  have hRzero : hc = hv → SR.tail r hc hv = 0 := by
    intro h; rw [h]; exact SR.tail_same r hv
  rcases lend_cases r hc be with hLend | hLend
  · rw [hLend]
    rcases eq_or_lt_of_le hk1 with hkOne | hkLt
    · have hp0 := (hk hkOne).1
      have hPh : hc = ht := by omega
      have hRv : hc = hv := by omega
      rw [hPzero hPh, hRzero hRv]
      omega
    · by_cases hPh : hc = ht
      · rw [hPzero hPh]; omega
      · by_cases hRv : hc = hv
        · rw [hRzero hRv]; omega
        · have hga : hc = ga := by omega
          have := hArm hga
          omega
  · obtain ⟨hr0, hlt⟩ := eq_of_lend_eq_one hLend
    rw [hLend]
    have hRv : hc = hv := by omega
    rw [hRzero hRv]
    have hkZero : k = 0 := by
      rcases eq_or_lt_of_le hk1 with hkOne | hkLt
      · have := (hk hkOne).2
        omega
      · omega
    by_cases hPh : hc = ht
    · rw [hPzero hPh]; omega
    · have hga : hc = ga := by omega
      have := hArm hga
      omega

end AtanasovRanganathan.ConfigurationChippedTriangle
