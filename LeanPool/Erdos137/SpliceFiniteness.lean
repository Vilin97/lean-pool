/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import LeanPool.Erdos137.Finiteness
import LeanPool.Erdos137.Base
import LeanPool.Erdos137.BlockFramework
import LeanPool.Erdos137.JointFiniteness
import LeanPool.Erdos137.SmoothRefinement
import LeanPool.Erdos137.TaoPoint

/-!
# Erdős Problem #137: the honest `g = 5` per-`k` bound and the abstract splice machine

`Erdos137/JointFiniteness.lean` formalizes the radical-decomposition argument for triples (`g = 3`);
`Erdos137/SmoothRefinement.lean` adds the smooth-part saving. This file develops the corresponding
quintic (`g = 5`) block machinery and separates two logically distinct outputs.

Since the unification into `Erdos137.BlockFramework`, the `g = 5` block objects (`B5`, `overlap5`,
`W5`, `Msplice`) are the **literal `g = 5` instances** of the generic framework, and the public
combinatorial lemmas (`B5_eq`, `B5_dvd_F`, `rad_5blocks_le`, `W5_dvd_factorial`, `W5_le_pow`,
`master_ineq5`, `not_powerful_g5`, `powerful_bound_g5`, `g5_finiteness`) are thin wrappers of their
generic counterparts. The abstract splice machine (`abstract_splice_no_counterexamples` and friends)
is unchanged.

## What is formalized

* **`g5_finiteness` / `powerful_bound_g5` — per-`k` finiteness from one block input.** From the
  single tail-absorbed hypothesis `BlockRadLB5`, for every fixed `k ≥ 5` the set of `n ≥ 1` with
  `F k n` powerful is finite; precisely, every such `n` satisfies
  `n ≤ Msplice k = (k^{2k})^5 · P k^{10}`. The proof is the formalized master inequality
  `n^{3k} · L k^5 ≤ (k^{2k})^5 · P k^{10}` (`master_ineq5`), using the quintic block radical input,
  the overlap bound `W5 ≤ k^k`, and the smooth-part refinement.
  The guard `5 ≤ k` is essential: for `k < 5` there are no quintic blocks (`⌊k/5⌋ = 0`). This is a
  per-`k` finiteness statement, NOT joint finiteness in `(n, k)`.

* **`abstract_splice_no_counterexamples` — an honest range-splice template.** Parametric in two
  predicates `Mid High : ℕ → ℕ → Prop`. Given (i) `CoversAll Mid High` — every `(k, n)` with
  `k ≥ 3`, `1 ≤ n` lies in `n ≤ k`, `Mid k n`, or `High k n`; (ii) `PrimeInBlockOnRange Mid` — a
  prime `p > k` that is a term of the block on the middle range; (iii) a high-range proof
  `High k n → ¬ Powerful (F k n)`; it proves `¬ Powerful (F k n)` for all such `(k, n)`. The small
  range `n ≤ k` is discharged unconditionally by Bertrand via `upper_half_prime_not_powerful`.

The intended Pandey-free no-gap splice is an ASYMPTOTIC pen-and-paper reading of
`abstract_splice_no_counterexamples`: take `Mid` = the Baker–Harman–Pintz range
`k < n ≤ k^{40/21−o(1)}` (where BHP supplies a prime `p > k` in `[n, n+k-1]`) and `High` = the
Mertens-sharpened quintic range `n > k^{5/3+o(1)}`. Since `5/3 < 40/21`, these ranges overlap for
all sufficiently large `k`, after the usual finite exceptional range (and `k = 3, 4`, handled by
the triple route) is absorbed. Lean does NOT formalize Baker–Harman–Pintz, Mertens, or this
asymptotic coverage; they enter only as the external premises of the abstract splice theorem, and a
faithful instantiation would carry a finite-exception clause.

## What is proved vs. hypothesized

* **Proved (Mathlib's three axioms only):** the `g = 5` block product identities, the radical
  product decomposition, `W5_le_pow` (`W5 ∣ k!`, Legendre), `master_ineq5`, `not_powerful_g5`,
  `powerful_bound_g5`, `g5_finiteness` (all `g = 5` instances of the generic framework), the
  unconditional small-`n` lemma `upper_half_prime_not_powerful` (Bertrand),
  `prime_range_not_powerful`, and `abstract_splice_no_counterexamples`.
* **Hypotheses (analytic inputs, NOT formalized):** `BlockRadLB5` packages the abc/Langevin quintic
  block estimate, its constants, the epsilon loss, and the omitted tail into one explicit normalized
  hypothesis. `PrimeInBlockOnRange`, `CoversAll`, and the high-range proof are premises of the
  abstract splice (encoding BHP + Mertens + the exact exponents on the intended instantiation). All
  enter as premises, so they do NOT appear in the axiom footprint of any theorem. Unconditional
  Erdős #137 and
  abc remain open.
-/

namespace Erdos137

open scoped BigOperators
open Finset

noncomputable section

/-! ## PART A — the `g = 5` block objects as literal instances of the generic framework -/

/-- The block product `B5 k n = ∏_{j<⌊k/5⌋} F 5 (n+5j) = F (5⌊k/5⌋) n`: the `g = 5` instance of
the generic `Bg`. -/
def B5 (k n : ℕ) : ℕ := Bg 5 k n

/-- `overlap5 p` is the number of quintic blocks `p` divides: the `g = 5` instance of `overlapg`. -/
def overlap5 (k n p : ℕ) : ℕ := overlapg 5 k n p

/-- The over-count `W5 k n`: the `g = 5` instance of the generic `Wg`. -/
def W5 (k n : ℕ) : ℕ := Wg 5 k n

/-- `B5 k n = F (5 * (k/5)) n`. The `g = 5` instance of `Bg_eq`. -/
lemma B5_eq (k n : ℕ) : B5 k n = F (5 * (k / 5)) n := Bg_eq (by norm_num) k n

/-- **`B5 k n` divides `F k n`** (the `g = 5` instance of `Bg_dvd_F`). -/
lemma B5_dvd_F (k n : ℕ) : B5 k n ∣ F k n := Bg_dvd_F (by norm_num) k n

/-- `B5 k n ≠ 0` for `n ≥ 1`. The `g = 5` instance of `Bg_ne_zero`. -/
lemma B5_ne_zero {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : B5 k n ≠ 0 := Bg_ne_zero (by norm_num) hn k

/-- For `n ≥ 1` each quintic block `F 5 (n + 5j)` is nonzero. The `g = 5` instance of
`block_ne_zero`. -/
lemma block5_ne_zero {n : ℕ} (hn : 1 ≤ n) (j : ℕ) : F 5 (n + 5 * j) ≠ 0 :=
  block_ne_zero hn 5 j

/-- **Radical-of-product decomposition (g = 5), exact form.**
`∏_j rad (F 5 (n+5j)) = rad (B5 k n) * W5 k n`. The `g = 5` instance of `rad_blocksg_decomp`. -/
theorem rad_blocks5_decomp {k n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / 5), rad (F 5 (n + 5 * j))) = rad (B5 k n) * W5 k n :=
  rad_blocksg_decomp (by norm_num) hn

/-- `rad (B5 k n) ∣ rad (F k n)`. The `g = 5` instance of `rad_Bg_dvd_rad_F`. -/
lemma rad_B5_dvd_rad_F {k n : ℕ} (hn : 1 ≤ n) : rad (B5 k n) ∣ rad (F k n) :=
  rad_Bg_dvd_rad_F (by norm_num) hn

/-- **Decomposition inequality (the usable form, g = 5):**
`∏_j rad (F 5 (n+5j)) ≤ rad (F k n) * W5 k n`. The `g = 5` instance of `rad_blocksg_le`. -/
theorem rad_5blocks_le {k n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / 5), rad (F 5 (n + 5 * j))) ≤ rad (F k n) * W5 k n :=
  rad_blocksg_le (by norm_num) hn

/-- **Overlap bound (combinatorial core, g = 5).** `overlap5 k n p ≤ ⌊k/p⌋ + 1` for `n ≥ 1`.
The `g = 5` instance of `overlapg_le`. -/
lemma overlap5_le {k n p : ℕ} (hn : 1 ≤ n) : overlap5 k n p ≤ k / p + 1 :=
  overlapg_le (by norm_num) hn

/-- **Overlap product divides `k!` (g = 5).** `W5 k n ∣ k!`. The `g = 5` instance of
`Wg_dvd_factorial`. -/
theorem W5_dvd_factorial {k n : ℕ} (hn : 1 ≤ n) : W5 k n ∣ Nat.factorial k :=
  Wg_dvd_factorial (by norm_num) hn

/-- **Overlap bound (g = 5): `W5 k n ≤ k^k`.** The `g = 5` instance of `Wg_le_pow`. -/
theorem W5_le_pow {k n : ℕ} (hn : 1 ≤ n) : W5 k n ≤ k ^ k :=
  Wg_le_pow (by norm_num) hn

/-! ### The genuine abc input (g = 5) and the master inequality -/

/-- Tail-absorbed quintic block radical input. This is a NORMALIZED asymptotic
hypothesis, NOT the literal blockwise abc/Langevin statement: it packages the
abc/Langevin constant, the epsilon loss, and the omitted `k mod 5` tail into one
explicit hypothesis. The guard `5 ≤ k` is ESSENTIAL: for `k < 5` there are no
quintic blocks (`⌊k/5⌋ = 0`), the RHS is the empty product `1`, and the bound
`(F k n)^{4/5} ≤ 1` would be false — i.e. the hypothesis would be inconsistent. -/
def BlockRadLB5 : Prop :=
  ∀ k n : ℕ, 5 ≤ k → 1 ≤ n →
    (F k n : ℝ) ^ ((4 : ℝ) / 5) ≤
      ((∏ j ∈ Finset.range (k / 5), rad (F 5 (n + 5 * j)) : ℕ) : ℝ)

/-- `BlockRadLB5` is exactly the `g = 5` instance of the generic `BlockRadLBg` (the exponents
`4/5` and `(5-1)/5` agree, and the guard `5 ≤ k` matches `g ≤ k`). -/
lemma blockRadLB5_iff : BlockRadLB5 ↔ BlockRadLBg 5 := by
  unfold BlockRadLB5 BlockRadLBg
  constructor
  · intro h k n hk hn
    have := h k n hk hn
    rwa [show (((5 : ℕ) : ℝ) - 1) / ((5 : ℕ) : ℝ) = (4 : ℝ) / 5 by norm_num]
  · intro h k n hk hn
    have := h k n hk hn
    rwa [show (((5 : ℕ) : ℝ) - 1) / ((5 : ℕ) : ℝ) = (4 : ℝ) / 5 by norm_num] at this

/-- **Smooth-refined master inequality (g = 5).** Under `BlockRadLB5`, for `k ≥ 5` and a powerful
`F k n` with `n ≥ 1`:  `n^{3k} · L k ^ 5 ≤ (k^{2k})^5 · P k ^ 10`. The `g = 5` instance of
`master_ineq_g` (`(5 - 2) * k = 3 * k`, `2 * 5 = 10`). -/
theorem master_ineq5 (hBlock5 : BlockRadLB5) {k n : ℕ}
    (hk : 5 ≤ k) (hn : 1 ≤ n) (hPow : Powerful (F k n)) :
    (n : ℝ) ^ (3 * k) * (L k : ℝ) ^ 5 ≤ ((k : ℝ) ^ (2 * k)) ^ 5 * (P k : ℝ) ^ 10 := by
  have hg := master_ineq_g 5 (blockRadLB5_iff.mp hBlock5) (by norm_num) hk hn hPow
  simpa using hg

/-- **Headline (g = 5 threshold).** Under `BlockRadLB5` (the genuine abc input, the only hypothesis
here), for `k ≥ 5`, if `n` exceeds the threshold `(k^{2k})^5 · P^{10} < n^{3k} · L^5`, then `F k n`
is **not powerful**. The `g = 5` ingredient `4/5 > 2/3` makes this `n > k^{5/3 + o(1)}`. -/
theorem not_powerful_g5 (hBlock5 : BlockRadLB5) {k n : ℕ}
    (hk : 5 ≤ k) (hn : 1 ≤ n)
    (hthr : ((k ^ (2 * k)) ^ 5 * P k ^ 10 : ℕ) < n ^ (3 * k) * L k ^ 5) :
    ¬ Powerful (F k n) := by
  intro hPow
  have hmaster := master_ineq5 hBlock5 hk hn hPow
  have hcast : (((k ^ (2 * k)) ^ 5 * P k ^ 10 : ℕ) : ℝ) < ((n ^ (3 * k) * L k ^ 5 : ℕ) : ℝ) := by
    exact_mod_cast hthr
  push_cast at hcast hmaster
  linarith [hcast, hmaster]

/-! ## PART B — the small-`n` (Bertrand) input -/

/-- **Small-`n` lemma (unconditional, via Bertrand).** For `2 ≤ k`, `1 ≤ n`, and `n ≤ k`, the
product `F k n` is **not powerful**.

Write `N = n + k - 1` (the top of the block, the largest factor). Applying Mathlib's Bertrand
postulate (`Nat.exists_prime_lt_and_le_two_mul`) at `m = N / 2` (which is `≥ 1` since `N ≥ 2`)
yields a prime `p` with `N / 2 < p ≤ 2 ⌊N/2⌋ ≤ N`. Hence:

* **Upper / single-occurrence:** `2p > 2 ⌊N/2⌋ ≥ N - 1`, so `2p > N - 1`, giving `2p > N` (as
  `2p ≥ N/2·2 + 2 > N`). Thus the only multiple of `p` in `[1, N]` that is itself a block factor is
  `p` (any other multiple is `≥ 2p > N`), and `p^2 ≥ (N/2+1)^2 > N` too.
* **Lower / membership:** `p > N / 2 = (n + k - 1) / 2 ≥ (n + n - 1) / 2 ≥ n - 1` (using `n ≤ k`),
  so `p ≥ n`; and `p ≤ N = n + k - 1`. Hence `p = n + i₀` for some `i₀ < k`: `p` is a **term**.

Then `v_p(F k n) = ∑_{i<k} v_p(n+i) = v_p(p) = 1` (every other factor `< 2p` is not a multiple of
`p`), so `p ∣ F` but `p^2 ∤ F`, contradicting powerfulness. The single occurrence comes from
`2p > N`, not from `p > k`. -/
theorem upper_half_prime_not_powerful {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) (hnk : n ≤ k) :
    ¬ Powerful (F k n) := by
  intro hPow
  have hFne : F k n ≠ 0 := F_ne_zero hn
  -- N = n + k - 1, the largest factor of the block.
  set N : ℕ := n + k - 1 with hN
  have hN2 : 2 ≤ N := by omega
  have hm1 : N / 2 ≠ 0 := by omega
  -- Bertrand at m = N/2:  a prime p with N/2 < p ≤ 2·(N/2).
  obtain ⟨p, hp, hpgt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) hm1
  -- 2·(N/2) ≤ N, so p ≤ N.
  have h2half_le : 2 * (N / 2) ≤ N := by omega
  have hpN : p ≤ N := le_trans hple h2half_le
  -- 2p > N:  p ≥ N/2 + 1 ⇒ 2p ≥ 2(N/2) + 2 ≥ N + 1 > N.
  have h2half_ge : N ≤ 2 * (N / 2) + 1 := by omega
  have h2p : N < 2 * p := by omega
  -- p ≥ n:  p > N/2 = (n+k-1)/2 and n ≤ k give N/2 ≥ n - 1, so p ≥ n.
  have hhalf_ge : n - 1 ≤ N / 2 := by
    rw [hN]
    have : 2 * (n - 1) ≤ n + k - 1 := by omega
    omega
  have hpn : n ≤ p := by omega
  -- p is a term:  n ≤ p ≤ n + k - 1, so p = n + i₀ with i₀ < k.
  have hi0lt : p - n < k := by omega
  have hterm : n + (p - n) = p := by omega
  set i₀ : ℕ := p - n with hi0
  -- v_p(F k n) = ∑_{i<k} v_p(n+i).
  have hfac : (F k n).factorization p = ∑ i ∈ Finset.range k, (n + i).factorization p := by
    unfold F
    rw [Nat.factorization_prod (by intro i _; omega)]
    rw [Finset.sum_apply']
  -- Every summand with i ≠ i₀ vanishes:  p ∤ (n+i), since 0 < n+i ≤ N < 2p forces n+i = p.
  have hsingle : (∑ i ∈ Finset.range k, (n + i).factorization p)
      = (n + i₀).factorization p := by
    rw [Finset.sum_eq_single i₀]
    · intro i hi hii₀
      have hik : i < k := Finset.mem_range.mp hi
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpi
      -- p ∣ n+i, 0 < n+i ≤ N < 2p ⇒ n+i = p ⇒ i = i₀.
      have hni_pos : 0 < n + i := by omega
      have hni_le : n + i ≤ N := by omega
      have hni_lt : n + i < 2 * p := by omega
      -- p ∣ n+i with n+i < 2p and n+i > 0 ⇒ n+i = p.
      obtain ⟨c, hc⟩ := hpi
      have hc1 : c = 1 := by
        rcases Nat.lt_or_ge c 2 with hclt2 | hcge2
        · -- c ∈ {0, 1};  c = 0 gives n+i = 0, contradicting n+i > 0.
          interval_cases c
          · omega
          · rfl
        · -- c ≥ 2 ⇒ n+i = p*c ≥ 2p, contradiction with n+i < 2p.
          exfalso
          have h2pc : 2 * p ≤ p * c :=
            calc 2 * p = p * 2 := by ring
              _ ≤ p * c := Nat.mul_le_mul_left p hcge2
          omega
      rw [hc1, mul_one] at hc
      -- n+i = p = n+i₀ ⇒ i = i₀.
      have : n + i = n + i₀ := by rw [hc, ← hterm]
      omega
    · intro hcon; exact absurd (Finset.mem_range.mpr hi0lt) hcon
  -- v_p(n+i₀) = v_p(p) = 1.
  have hvterm : (n + i₀).factorization p = 1 := by
    rw [hterm, Nat.Prime.factorization_self hp]
  have hvF : (F k n).factorization p = 1 := by rw [hfac, hsingle, hvterm]
  -- p ∣ F (via the i₀-th term), so powerfulness gives p² ∣ F, i.e. v_p(F) ≥ 2.  Contradiction.
  have hpF : p ∣ F k n := by
    have hmem : i₀ ∈ Finset.range k := Finset.mem_range.mpr hi0lt
    have hdvd : (n + i₀) ∣ F k n := by unfold F; exact Finset.dvd_prod_of_mem _ hmem
    rwa [hterm] at hdvd
  have hp2F : p ^ 2 ∣ F k n := hPow p hp hpF
  have hge2 : 2 ≤ (F k n).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hFne).mp hp2F
  omega

/-! ## PART C — the honest `g = 5` finiteness and the abstract splice machine -/

/-- The explicit `g = 5` finiteness bound `M k = (k^{2k})^5 · P k^{10}`. The `g = 5` instance of the
generic `Mg`. -/
def Msplice (k : ℕ) : ℕ := Mg 5 k

/-- Explicit bound form of the `g = 5` deduction: a powerful `F k n` (with `k ≥ 5`,
`n ≥ 1`) forces `n ≤ Msplice k`. The `g = 5` instance of the generic `powerful_bound_g`. -/
theorem powerful_bound_g5 (hBlock5 : BlockRadLB5) {k n : ℕ}
    (hk : 5 ≤ k) (hn : 1 ≤ n) (hPow : Powerful (F k n)) :
    n ≤ Msplice k :=
  powerful_bound_g 5 (blockRadLB5_iff.mp hBlock5) (by norm_num) hk hn hPow

/-- **Honest `g = 5` finiteness (from `BlockRadLB5` ALONE).** For `k ≥ 5`, under the single analytic
hypothesis `BlockRadLB5`, the set of `n ≥ 1` with `F k n` powerful is **finite**: every such `n`
satisfies the explicit bound `n ≤ Msplice k = (k^{2k})^5 · P k^{10}`. The `g = 5` instance of the
generic `g_finiteness`; involves no BHP, no Bertrand, and no Mertens — just `BlockRadLB5`. -/
theorem g5_finiteness (hBlock5 : BlockRadLB5) {k : ℕ} (hk : 5 ≤ k) :
    {n : ℕ | 1 ≤ n ∧ Powerful (F k n)}.Finite :=
  g_finiteness 5 (blockRadLB5_iff.mp hBlock5) (by norm_num) hk

/-- **Ranged prime-in-block input.** `PrimeInBlockOnRange Range` says: on the range `Range k n`
(with `k ≥ 3`, `1 ≤ n`), the block `[n, n+k-1]` contains a prime `p > k` that is a term `n + i` of
the block. This replaces the old too-strong global `BHP`: it only asks for a prime on whatever range
`Range` it is instantiated at (e.g. the genuine Baker–Harman–Pintz range `n ≤ k^{40/21}`), never in
"every" block. It enters as a hypothesis; Baker–Harman–Pintz is NOT formalized. -/
def PrimeInBlockOnRange (Range : ℕ → ℕ → Prop) : Prop :=
  ∀ k n : ℕ, 3 ≤ k → 1 ≤ n → Range k n →
    ∃ p, p.Prime ∧ k < p ∧ ∃ i < k, n + i = p

/-- **Ranged prime deduction.** Given a ranged prime input `PrimeInBlockOnRange Range`, for `k ≥ 3`,
`1 ≤ n`, and `hR : Range k n`, the product `F k n` is not powerful: the prime `p > k` supplied on
the range is a term of the block, and `prime_in_block_not_powerful` (TaoPoint) rules out
powerfulness. -/
theorem prime_range_not_powerful {Range : ℕ → ℕ → Prop}
    (hPrime : PrimeInBlockOnRange Range) {k n : ℕ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) (hR : Range k n) : ¬ Powerful (F k n) := by
  obtain ⟨p, hp, hpk, hmem⟩ := hPrime k n hk hn hR
  exact prime_in_block_not_powerful hp hpk hn hmem

/-- **Coverage of the three ranges.** `CoversAll Mid High` says every `(k, n)` with `k ≥ 3`, `1 ≤ n`
falls into the small range `n ≤ k`, the middle range `Mid k n`, or the high range `High k n`. On the
intended instantiation, `Mid` = BHP range, `High` = Mertens-sharpened `g = 5` range, and coverage is
the inequality `5/3 < 40/21` (kept external). -/
def CoversAll (Mid High : ℕ → ℕ → Prop) : Prop :=
  ∀ k n : ℕ, 3 ≤ k → 1 ≤ n → n ≤ k ∨ Mid k n ∨ High k n

/-- **The abstract splice machine — the honest no-gap architecture.** Parametric in two range
predicates `Mid High`. Given:

* `hCover : CoversAll Mid High` — every `(k, n)` is small (`n ≤ k`), middle (`Mid`), or high
  (`High`);
* `hMid : PrimeInBlockOnRange Mid` — a prime `p > k` term of the block on the middle range;
* `hHigh : ∀ k n, 3 ≤ k → 1 ≤ n → High k n → ¬ Powerful (F k n)` — non-powerfulness on the high
  range;

then `¬ Powerful (F k n)` for **every** `(k, n)` with `k ≥ 3`, `1 ≤ n`. The small range is
discharged unconditionally by `upper_half_prime_not_powerful` (Bertrand); the middle range by
`prime_range_not_powerful`; the high range by the supplied `hHigh`. Baker–Harman–Pintz, Mertens, and
the exact exponents live entirely inside the three premises — Lean never assumes them, so it never
assumes "a prime in every block". For `k ≥ 5`, instantiating `Mid` = BHP range and `High` =
Mertens-sharpened `g = 5` range, with `hHigh` supplied by `not_powerful_g5`, gives the clean
Pandey-free no-gap splice, whose analytic inputs remain external. -/
theorem abstract_splice_no_counterexamples {Mid High : ℕ → ℕ → Prop}
    (hCover : CoversAll Mid High)
    (hMid : PrimeInBlockOnRange Mid)
    (hHigh : ∀ k n, 3 ≤ k → 1 ≤ n → High k n → ¬ Powerful (F k n))
    {k n : ℕ} (hk : 3 ≤ k) (hn : 1 ≤ n) : ¬ Powerful (F k n) := by
  rcases hCover k n hk hn with hsmall | hmid | hhigh
  · exact upper_half_prime_not_powerful (by omega) hn hsmall
  · exact prime_range_not_powerful hMid hk hn hmid
  · exact hHigh k n hk hn hhigh

end  -- noncomputable section

end Erdos137
