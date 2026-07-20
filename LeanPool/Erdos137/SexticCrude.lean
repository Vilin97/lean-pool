/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import LeanPool.Erdos137.BlockFramework

/-!
# Erdős Problem #137: the sextic (`g = 6`) crude block route — sharp threshold `n > k^3`

This module instantiates the generic crude (non-smooth) block route `master_ineq_crude_g`
(`BlockFramework`, PART E) at the block length `g = 6`. The crude master inequality reads
`n ^ (6 - 2) ≤ k ^ (2 * 6)`, i.e. `n ^ 4 ≤ k ^ 12`, equivalently `n ≤ k ^ 3`. So under the sextic
block radical hypothesis `BlockRadLB6`, for `k ≥ 6` and `n > k^3` the product `F k n` is **not
powerful** (`not_powerful_of_large_g6`); for each fixed `k ≥ 6`, `F k n` is powerful for only
finitely many `n` (`g6_crude_finiteness`).

## Why `g = 6`

The crude exponent is `2g/(g-2) = 2 + 4/(g-2)`, an integer exactly when `(g-2) ∣ 4`, i.e. precisely
for `g ∈ {3, 4, 6}` — giving `k^6` (`JointFiniteness`), `k^4` (`QuarticCrude`), and `k^3` here. So
`g = 6` is the **last (largest) block length with an integer crude exponent**, and `k^3` is the
**sharpest clean integer-exponent crude threshold this route reaches**: beyond `g = 6` the crude
exponent stays non-integer and only decreases toward `k^2` as `g → ∞` (e.g. `g = 10 → k^{2.5}`).
Like all crude thresholds this is **fully explicit** — no `o(1)`, no unformalized Mertens input —
but it costs a correspondingly higher-degree block radical input: `BlockRadLB6` is the
`(F k n)^{5/6} ≤ ∏ rad` bound over sextic blocks, with the `g`-dependent abc/Langevin constant (the
known radical-method ceiling: a sharper exponent for a worse constant). `k^3` is comfortably below
the `k^5` unconditional squarefree ceiling, so it too is a valid high-`n` input for the
squarefree-counting reduction.

## What is proved (no `sorry`, only Mathlib's three axioms)

* `not_powerful_of_large_g6` : `BlockRadLB6 → 6 ≤ k → k^3 < n → ¬ Powerful (F k n)` — the headline.
* `g6_crude_finiteness` : `BlockRadLB6 → 6 ≤ k → {n | 1 ≤ n ∧ Powerful (F k n)}.Finite`.

The ONLY hypothesis is `BlockRadLB6` (the `g = 6` instance of `BlockRadLBg`); it is a premise, not
an `axiom`, so it does not appear in any axiom footprint.
-/

namespace Erdos137

open scoped BigOperators
open Finset

noncomputable section

/-- **(H, g = 6) Sextic block radical lower bound (abc-extremal form).** Langevin/abc applied to
each squarefree sextic block `g(m) = m(m+1)⋯(m+5)`, assembled over the `⌊k/6⌋` blocks:
`(F k n)^{5/6} ≤ ∏ rad over sextic blocks`. The `g = 6` instance of `BlockRadLBg`; the exponent
`5/6 = (6-1)/6` and the guard `6 ≤ k` matches `g ≤ k`. -/
def BlockRadLB6 : Prop :=
  ∀ k n : ℕ, 6 ≤ k → 1 ≤ n →
    (F k n : ℝ) ^ ((5 : ℝ) / 6) ≤
      ((∏ j ∈ Finset.range (k / 6), rad (F 6 (n + 6 * j)) : ℕ) : ℝ)

/-- `BlockRadLB6` is exactly the `g = 6` instance of the generic `BlockRadLBg` (the exponents
`5/6` and `(6-1)/6` agree, and the guard `6 ≤ k` matches `g ≤ k`). -/
lemma blockRadLB6_iff : BlockRadLB6 ↔ BlockRadLBg 6 := by
  unfold BlockRadLB6 BlockRadLBg
  constructor
  · intro h k n hk hn
    have := h k n hk hn
    rwa [show (((6 : ℕ) : ℝ) - 1) / ((6 : ℕ) : ℝ) = (5 : ℝ) / 6 by norm_num]
  · intro h k n hk hn
    have := h k n hk hn
    rwa [show (((6 : ℕ) : ℝ) - 1) / ((6 : ℕ) : ℝ) = (5 : ℝ) / 6 by norm_num] at this

/-! ## The `g = 6` block objects as literal instances of the generic framework -/

/-- The sextic block product `B6 k n`: the `g = 6` instance of the generic `Bg`. -/
def B6 (k n : ℕ) : ℕ := Bg 6 k n

/-- `overlap6 p` is the number of sextic blocks `p` divides: the `g = 6` instance of `overlapg`. -/
def overlap6 (k n p : ℕ) : ℕ := overlapg 6 k n p

/-- The over-count `W6 k n`: the `g = 6` instance of the generic `Wg`. -/
def W6 (k n : ℕ) : ℕ := Wg 6 k n

/-- **`B6 k n` divides `F k n`** (the `g = 6` instance of `Bg_dvd_F`). -/
lemma B6_dvd_F (k n : ℕ) : B6 k n ∣ F k n := Bg_dvd_F (by norm_num) k n

/-- **Overlap bound (g = 6): `W6 k n ≤ k^k`.** The `g = 6` instance of `Wg_le_pow`. -/
theorem W6_le_pow {k n : ℕ} (hn : 1 ≤ n) : W6 k n ≤ k ^ k :=
  Wg_le_pow (by norm_num) hn

/-! ## The sharp sextic crude headline (threshold `k^3`) -/

/-- **Sextic crude headline.** Under `BlockRadLB6`, for `k ≥ 6` and `n > k^3`, `F k n` is not
powerful. From the crude master inequality `n^4 ≤ k^12` (= `master_ineq_crude_g 6`): `k^3 < n`
forces `k^12 = (k^3)^4 < n^4`, contradiction. -/
theorem not_powerful_of_large_g6 (hBlock : BlockRadLB6) {k n : ℕ}
    (hk : 6 ≤ k) (hn : k ^ 3 < n) : ¬ Powerful (F k n) := by
  intro hPow
  have hn1 : 1 ≤ n := by have : 1 ≤ k ^ 3 := Nat.one_le_pow _ _ (by omega); omega
  have hmaster : n ^ 4 ≤ k ^ 12 := by
    have := master_ineq_crude_g 6 (blockRadLB6_iff.mp hBlock) (by norm_num) hk hn1 hPow
    simpa using this   -- (6-2)=4, 2*6=12
  have hlt : k ^ 12 < n ^ 4 := by
    have h2 : (k ^ 3) ^ 4 < n ^ 4 := Nat.pow_lt_pow_left hn (by norm_num)
    have : (k ^ 3) ^ 4 = k ^ 12 := by ring
    omega
  omega

/-- **Per-`k` finiteness (sextic crude).** For `k ≥ 6` under `BlockRadLB6`,
`{n ≥ 1 : F k n powerful}` is finite (all satisfy `n ≤ k^3`). -/
theorem g6_crude_finiteness (hBlock : BlockRadLB6) {k : ℕ} (hk : 6 ≤ k) :
    {n : ℕ | 1 ≤ n ∧ Powerful (F k n)}.Finite := by
  apply Set.Finite.subset (Set.finite_Iic (k ^ 3))
  intro n hn; simp only [Set.mem_setOf_eq] at hn; simp only [Set.mem_Iic]
  by_contra hcon; push Not at hcon
  exact not_powerful_of_large_g6 hBlock hk hcon hn.2

end  -- noncomputable section

end Erdos137
