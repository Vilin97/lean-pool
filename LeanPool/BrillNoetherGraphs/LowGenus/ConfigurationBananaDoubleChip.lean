/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.ConfigurationMarkedThree

/-!
# A banana pair with a double chip at the short end

This is the solid subgraph of Atanasov--Ranganathan's *third* scope for their
seventh genus-five family (atlas row `08`).  It is **not** one of the eleven
pictures of their Proposition 5.1: the closest, the *Fourth*, puts its single
chip on a banana vertex rather than at the end of a leg.  The module is
therefore named for its geometry, following the `ConfigurationThreeChain` /
`ConfigurationBananaTail` precedent.

```
      A                B          A carries one chip, B carries TWO
      |                |          u, v are chip free, joined by a banana
      u ===== v                   |u A| = p,  |v B| = q,  q ≤ p
```

The pair is **lopsided** -- the arms have different lengths -- and the target is
the *far* vertex `u`, the one whose arm is the long one.  With
`par = min m1 m2` the profile is the two nested minima

```
 hv = min (2 * q) p
 hu = min p (hv + par)
```

and **only the double chip makes it possible**: with a single chip at `B` the
far vertex of a lopsided banana pair is unreachable by any script of this shape,
because the arm `v B` can then carry at most one unit of slope while the two
banana slots charge `v` twice.

Three ways `u` gets its chip, which are the three arguments of the two minima:

* `hu = p` -- the arm `u A` is full and delivers;
* `hu = hv + par` with `par > 0` -- the shorter banana slot is full and delivers,
  and `v` pays the two banana chips out of the two it drew along `q`;
* `par = 0` -- the banana has collapsed, `u` and `v` are the same contracted
  class, and the chip is charged to `v` (or, when `q = 0` as well, to `B`
  itself).  That is the `k` parameter below.

The near vertex is where the double chip is spent: `far_partner_nonneg` is the
statement that `v` still balances, and its proof is the only place in the whole
programme where a canonical ramp runs at **slope two** -- `headContribution q 0
(2 * q) = 2`.  The four one-edge facts that needs are proved first.
-/

@[expose] public section

namespace AtanasovRanganathan.ConfigurationBananaDoubleChip

open Utilities

open Certificate
open Certificate.ExplicitPotential
open ConfigurationFive
open ConfigurationMarkedThree

/-! ## One-edge arithmetic at slope two

`ConfigurationFive`'s ledger bounds every endpoint slope by one in absolute
value, which is right for a divisor with one chip per arm end.  The double chip
allows -- and needs -- slope two on its own arm. -/

/-- An arm read from its head delivers a chip as soon as its rise reaches the
arm's length. -/
theorem headContribution_ge_one_of_ge {L h : ℕ} (hL : 0 < L) (hle : L ≤ h) :
    1 ≤ headContribution L 0 h := by
  simp only [headContribution, ite_eq_right hL.ne', Nat.cast_zero]
  have hstep := SubdivisionArithmetic.step_le_upper_of_le_mul
    (L := L) (i := L - 1) ((0 : ℤ) - (h : ℤ)) (-1) hL (by omega)
    (by omega)
  omega

/-- **Slope two.**  An arm whose rise is twice its length delivers two chips at
its head.  This is what the double chip buys. -/
theorem headContribution_ge_two_of_ge {L h : ℕ} (hL : 0 < L) (hle : 2 * L ≤ h) :
    2 ≤ headContribution L 0 h := by
  simp only [headContribution, ite_eq_right hL.ne', Nat.cast_zero]
  have hstep := SubdivisionArithmetic.step_le_upper_of_le_mul
    (L := L) (i := L - 1) ((0 : ℤ) - (h : ℤ)) (-2) hL (by omega)
    (by omega)
  omega

/-- The matching cost: an arm of rise at most twice its length takes at most two
chips from its tail. -/
theorem tailContribution_ge_neg_two {L h : ℕ} (hh : h ≤ 2 * L) :
    -2 ≤ tailContribution L 0 h := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · have : h = 0 := by omega
    simp [tailContribution, hL]
  · simp only [tailContribution, ite_eq_right hL.ne']
    exact SubdivisionArithmetic.lower_le_step_of_mul_le (L := L) (i := 0)
      ((0 : ℤ) - (h : ℤ)) (-2) hL (by omega)

/-- The double chip pays for its own arm. -/
theorem doubleChip_add_tail_nonneg {L h : ℕ} (hh : h ≤ 2 * L) :
    0 ≤ 2 * positiveChip L + tailContribution L 0 h := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · have : h = 0 := by omega
    simp [positiveChip, tailContribution, hL]
  · have hp : positiveChip L = 1 := by simp [positiveChip, hL.ne']
    have := tailContribution_ge_neg_two (L := L) (h := h) hh
    omega

/-! ## The profile -/

/-- The height at the near vertex: two chips' worth of its own arm, clamped by
the far arm. -/
def nearHeight (p q : ℕ) : ℕ := min (2 * q) p

/-- The height at the far vertex, the target. -/
def farHeight (p q par : ℕ) : ℕ := min p (nearHeight p q + par)

theorem nearHeight_le_far {p q par : ℕ} :
    nearHeight p q ≤ farHeight p q par := by
  unfold nearHeight farHeight nearHeight
  omega

theorem nearHeight_ge_short {p q : ℕ} (hqp : q ≤ p) : q ≤ nearHeight p q := by
  unfold nearHeight
  omega

/-! ## The two residual statements

Both are stated at the orientation row `08` reads them in: the far arm from its
tail, the near arm from its head.  The mirror orientation is not needed, because
the fourth sign pattern of row 08 is the `sigma` image of the third and is
obtained by transport rather than by a second proof. -/

/-- **The far vertex, the target.**  `k` is one exactly when the delivered chip
is charged here; the hypothesis says that is legitimate. -/
theorem far_center_nonneg {p q par m1 m2 hv hu : ℕ} {k : ℤ}
    (hpar : par = min m1 m2) (hnear : hv = nearHeight p q)
    (hfar : hu = farHeight p q par)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hk : k = 1 → 0 < par ∨ hu = p) :
    0 ≤ zeroChip p - k +
      (tailContribution p hu 0 + tailContribution m1 hu hv
        + tailContribution m2 hu hv) := by
  have hnear' : hv = min (2 * q) p := hnear
  have hfar' : hu = min p (hv + par) := by rw [hfar, farHeight, hnear]
  have harm : 0 ≤ tailContribution p hu 0 :=
    tailContribution_nonneg (Nat.zero_le _) (by omega)
  have hb1 : 0 ≤ tailContribution m1 hu hv :=
    tailContribution_nonneg (by omega) (by omega)
  have hb2 : 0 ≤ tailContribution m2 hu hv :=
    tailContribution_nonneg (by omega) (by omega)
  have hz : (0 : ℤ) ≤ zeroChip p := zeroChip_nonneg p
  rcases eq_or_lt_of_le hk1 with hkOne | hkLt
  · have hfull : hu = p ∨ (0 < par ∧ hu = hv + par) := by
      rcases hk hkOne with hp | hp
      · rcases Nat.le_total p (hv + par) with h1 | h1
        · exact Or.inl (by omega)
        · exact Or.inr ⟨hp, by omega⟩
      · exact Or.inl hp
    rcases hfull with hp | ⟨hpar0, hp⟩
    · have hOne : 1 ≤ zeroChip p + tailContribution p hu 0 := by
        rw [hp]
        exact zeroChip_add_tail_full p
      omega
    · rcases Nat.le_total m1 m2 with h1 | h1
      · have hOne := tailContribution_eq_one_of_full (L := m1) (hu := hu)
          (hv := hv) (by omega) (by omega)
        omega
      · have hOne := tailContribution_eq_one_of_full (L := m2) (hu := hu)
          (hv := hv) (by omega) (by omega)
        omega
  · omega

/-- **The near vertex, under the double chip.**  It balances because its own arm
runs at slope two exactly when the banana charges it twice. -/
theorem far_partner_nonneg {p q par m1 m2 hv hu : ℕ} {k : ℤ}
    (hpar : par = min m1 m2) (hnear : hv = nearHeight p q)
    (hfar : hu = farHeight p q par) (hqp : q ≤ p)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hk : k = 1 → par = 0 ∧ 0 < q) :
    0 ≤ 2 * zeroChip q - k +
      (headContribution q 0 hv + headContribution m1 hu hv
        + headContribution m2 hu hv) := by
  have hnear' : hv = min (2 * q) p := hnear
  have hfar' : hu = min p (hv + par) := by rw [hfar, farHeight, hnear]
  have hb1 : -1 ≤ headContribution m1 hu hv :=
    headContribution_ge_neg_one (by omega) (by omega)
  have hb2 : -1 ≤ headContribution m2 hu hv :=
    headContribution_ge_neg_one (by omega) (by omega)
  have hz : (0 : ℤ) ≤ 2 * zeroChip q := by
    have := zeroChip_nonneg q
    omega
  by_cases hq : 0 < q
  · have hone : 1 ≤ headContribution q 0 hv :=
      headContribution_ge_one_of_ge hq (by omega)
    have hzq : zeroChip q = 0 := by
      have hne : q ≠ 0 := by omega
      simp [zeroChip, hne]
    by_cases hEq : hu = hv
    · have h1 : headContribution m1 hu hv = 0 := by
        rw [hEq]; exact headContribution_same m1 hv
      have h2 : headContribution m2 hu hv = 0 := by
        rw [hEq]; exact headContribution_same m2 hv
      omega
    · have hlt : hv < hu := by omega
      have hk0' : k = 0 := by
        rcases eq_or_lt_of_le hk1 with hkOne | hkLt
        · exact absurd (hk hkOne).1 (by omega)
        · omega
      have hdouble : 2 * q ≤ hv := by omega
      have htwo : 2 ≤ headContribution q 0 hv :=
        headContribution_ge_two_of_ge hq hdouble
      omega
  · have hq0 : q = 0 := by omega
    have hzq : zeroChip q = 1 := by simp [zeroChip, hq0]
    have hv0 : hv = 0 := by omega
    have harm : headContribution q 0 hv = 0 := by
      rw [hq0, hv0]
      exact headContribution_zero_zero 0
    have hk0' : k = 0 := by
      rcases eq_or_lt_of_le hk1 with hkOne | hkLt
      · exact absurd (hk hkOne).2 (by omega)
      · omega
    omega

end AtanasovRanganathan.ConfigurationBananaDoubleChip
