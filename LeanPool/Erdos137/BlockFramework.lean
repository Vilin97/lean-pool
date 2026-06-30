/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import LeanPool.Erdos137.Finiteness
import LeanPool.Erdos137.Base

/-!
# Erdős Problem #137: the parametric `g`-block framework (unifying `g = 3` and `g = 5`)

`Erdos137/JointFiniteness.lean` develops the **triple** (`g = 3`) radical-decomposition route and
`Erdos137/SpliceFiniteness.lean` the **quintic** (`g = 5`) route. Both are the *same* argument run
with a different block length `g`. This file factors that duplication into ONE parametric
`g`-block framework: every `3`/`5` in the two existing chains is replaced by a symbolic `g`, and
the master inequality, per-`k` bound, and finiteness wrapper are proved once, for all `g ≥ 3`.

## The unified master inequality

The headline is `master_ineq_g`: under the normalized block radical hypothesis `BlockRadLBg g`,
for `k ≥ g ≥ 3` and a powerful `F k n` (`n ≥ 1`),

  `n ^ ((g - 2) * k) · L k ^ g  ≤  (k ^ (2k)) ^ g · P k ^ (2g)`.

This specializes EXACTLY to both recorded thresholds:

* `g = 3` ⟹ `n ^ k · L^3 ≤ (k^{2k})^3 · P^6` — the JointFiniteness/SmoothRefinement threshold
  (`master_ineq`, since `(3 - 2) * k = k`);
* `g = 5` ⟹ `n ^ {3k} · L^5 ≤ (k^{2k})^5 · P^{10}` — the SpliceFiniteness threshold
  (`master_ineq5`, since `(5 - 2) * k = 3k`).

There are TWO exponent readings of `master_ineq_g`, and they must not be conflated. With only the
proved lower bound `L k ≥ 1`, the master inequality gives the **coarse** threshold
`n > k^{2g/(g-2) + o(1)}`; as `g → ∞` this exponent tends to `2`, i.e. toward `k^{2 + ε}` — NOT
`k^{1 + ε}`. The `k^{1 + ε}` reading appears only after the unformalized Mertens lower bound
`log L k = k log k − O(k)` (so `L k = k^{k − o(k)}`), which sharpens the threshold to
`n > k^{g/(g-2) + o(1)}`; that exponent tends to `1`. So fixed large `g` reaches the pen-and-paper
`k^{1 + ε}` floor only in the Mertens-sharpened reading, never from the coarse formal bound alone.
The formal `.Finite` wrapper deliberately uses the coarse explicit bound `n ≤ Mg g k`; the sharp
exponent stays an external asymptotic reading of the master inequality. This is also NOT an
unconditional improvement: for each FIXED `g` the abc/Langevin constant packaged in `BlockRadLBg g`
depends on `g` (the implied constant degrades with the block length) — the known ceiling of the
radical method, trading a sharper exponent for a worse constant, and the constant is exactly what
abc would supply. So this is not a uniform growing-`g` theorem.

## The two guards

* `3 ≤ g` is needed for the exponent `(g - 2) ≥ 1` (so `n ≤ n^{(g-2)k}`) and for the smooth/squaring
  arithmetic `2(g-1)/g - 1 = (g-2)/g ≥ 0`.
* `g ≤ k` is a CONSISTENCY guard built into `BlockRadLBg`. For `g > k` there are no `g`-blocks
  (`⌊k/g⌋ = 0`), the block-radical product is the empty product `1`, and the hypothesis
  `(F k n)^{(g-1)/g} ≤ 1` would be inconsistent (it would force `F k n ≤ 1`).

## What is proved vs. hypothesized

* **Proved (Mathlib's three axioms only):** the generic block product identity `blocksg_prod_eq`,
  the radical-of-product decomposition `rad_blocksg_decomp`, the overlap bound `Wg_le_pow`
  (`Wg ∣ k!`, Legendre), the smooth-refined master inequality `master_ineq_g`, the explicit per-`k`
  bound `powerful_bound_g`, and the finiteness wrapper `g_finiteness`.
* **Hypothesis (analytic input, NOT formalized):** `BlockRadLBg g` is the normalized tail-absorbed
  block radical lower bound — it packages the abc/Langevin constant, the epsilon loss, and the
  omitted `k mod g` tail into one explicit Prop. abc itself is NOT formalized; it enters only as a
  premise, so it does not appear in any axiom footprint.

The shared low-level helpers (`rad_dvd_self`, `factorization_rad`, `rad_dvd_rad_of_dvd`,
`Ioc_dvd_count`, `Ioc_dvd_le`, `div_le_factorization_factorial`, `pow_le_F`, `le_F`, the smooth
refinement `smooth_refinement`, `P`, `L`, …) are imported and reused verbatim from `Erdos137.Base`,
not re-proved.

This framework sits ABOVE the concrete `g = 3, 5` modules: `JointFiniteness` defines
`B`/`overlap`/`W` literally as `Bg 3`/`overlapg 3`/`Wg 3` and `SpliceFiniteness` defines
`B5`/`overlap5`/`W5` as the `g = 5` instances, with their public lemmas re-derived as thin
wrappers of the generic theorems below.

## Two routes: SMOOTH vs. CRUDE

There are now TWO parametric routes off the same block chain, and they must not be conflated:

* **SMOOTH** (`master_ineq_g`, PART C): `n ^ ((g-2) k) · L ^ g ≤ (k^{2k})^g · P ^ {2g}`. This
  refines the bare powerful inequality `rad ^ 2 ≤ F` by the smooth gain `L`, so it carries a
  *sharper exponent* — threshold `k ^ {2g/(g-2) + o(1)}` (coarse `L ≥ 1` reading) or
  `k ^ {g/(g-2) + o(1)}`
  (Mertens reading). But the sharpening is only realized through the *unformalized* Mertens lower
  bound on `L`; the formal `.Finite` wrapper falls back on the coarse explicit `Mg`.
* **CRUDE** (`master_ineq_crude_g`, PART E): `n ^ (g - 2) ≤ k ^ (2 * g)`, a clean INTEGER inequality
  carrying NO `L`/`P` factor — it uses only `rad ^ 2 ≤ F`. The exponent is weaker but the threshold
  is the *exact, fully explicit* `k ^ {2g/(g-2)}` with no `o(1)` and no Mertens input:
  `g = 3 → k^6`, `g = 4 → k^4` (since `n^2 ≤ k^8 ↔ n ≤ k^4`), `g = 6 → k^3`.

So: the crude route gives a fully explicit constant at a worse exponent; the smooth route gives a
sharper exponent only via the unformalized Mertens reading. The crude `g = 3` instance recovers the
recorded `not_powerful_of_large` threshold `n > k^6` exactly.
-/

namespace Erdos137

open scoped BigOperators
open Finset

noncomputable section

/-! ## PART A — the generic `g`-block combinatorics (literal `3`/`5` → `g`) -/

/-- The block product `Bg g k n = ∏_{j<⌊k/g⌋} F g (n+g·j) = F (g⌊k/g⌋) n`: the part of `F k n`
covered by the `g`-blocks (dropping the `k % g` tail). Generic form of `B`/`B5`. -/
def Bg (g k n : ℕ) : ℕ := ∏ j ∈ Finset.range (k / g), F g (n + g * j)

/-- `overlapg g p = ∑_j [p ∈ (F g (n+g·j)).primeFactors]` is the number of `g`-blocks `p` divides.
Generic form of `overlap`/`overlap5`. -/
def overlapg (g k n p : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k / g), if p ∈ (F g (n + g * j)).primeFactors then 1 else 0

/-- The over-count `Wg g k n := ∏_{p ∈ (Bg g k n).primeFactors} p ^ (overlapg p − 1)`.
Generic form of `W`/`W5`. -/
def Wg (g k n : ℕ) : ℕ :=
  ∏ p ∈ (Bg g k n).primeFactors, p ^ (overlapg g k n p - 1)

/-- The product over the `⌊k/g⌋` blocks, `∏_{j<⌊k/g⌋} F g (n + g·j)`, equals `F (g · ⌊k/g⌋) n`.
Generic form of `triples_prod_eq`/`blocks5_prod_eq`. The `(hg : 1 ≤ g)` guard makes the stride
positive in the telescoping; it is not actually needed here (the induction is on `k / g`), but is
recorded to match the parametric setting. -/
lemma blocksg_prod_eq (_hg : 1 ≤ g) (k n : ℕ) :
    (∏ j ∈ Finset.range (k / g), F g (n + g * j)) = F (g * (k / g)) n := by
  induction (k / g) with
  | zero => simp [F]
  | succ t ih =>
    rw [Finset.prod_range_succ, ih]
    have hg' : g * (t + 1) = g * t + g := by ring
    rw [hg', F_add]

/-- `Bg g k n = F (g * (k/g)) n`. -/
lemma Bg_eq (hg : 1 ≤ g) (k n : ℕ) : Bg g k n = F (g * (k / g)) n := blocksg_prod_eq hg k n

/-- The product of the `g`-blocks divides `F k n`. Generic form of `triples_prod_dvd`. -/
lemma blocksg_prod_dvd (hg : 1 ≤ g) (k n : ℕ) :
    (∏ j ∈ Finset.range (k / g), F g (n + g * j)) ∣ F k n := by
  rw [blocksg_prod_eq hg]
  have hk : k = g * (k / g) + (k % g) := (Nat.div_add_mod k g).symm
  conv_rhs => rw [hk]
  exact F_dvd_F_add _ _ _

/-- **`Bg g k n` divides `F k n`** (generic form of `B_dvd_F`/`B5_dvd_F`). -/
lemma Bg_dvd_F (hg : 1 ≤ g) (k n : ℕ) : Bg g k n ∣ F k n := blocksg_prod_dvd hg k n

/-- `Bg g k n ≠ 0` for `n ≥ 1`. -/
lemma Bg_ne_zero (hg : 1 ≤ g) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : Bg g k n ≠ 0 := by
  rw [Bg_eq hg]; exact F_ne_zero hn

/-- For `n ≥ 1` each block `F g (n + g·j)` is nonzero. -/
lemma block_ne_zero {n : ℕ} (hn : 1 ≤ n) (g j : ℕ) : F g (n + g * j) ≠ 0 :=
  F_ne_zero (by omega)

/-- The `p`-adic valuation of the product of the block radicals equals `overlapg g k n p`. -/
lemma factorization_blocksg_rad (g k n p : ℕ) (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / g), rad (F g (n + g * j))).factorization p = overlapg g k n p := by
  have hrad_ne : ∀ j ∈ Finset.range (k / g), rad (F g (n + g * j)) ≠ 0 := by
    intro j _; exact Nat.one_le_iff_ne_zero.mp (rad_pos _)
  rw [Nat.factorization_prod_apply hrad_ne]
  unfold overlapg
  apply Finset.sum_congr rfl
  intro j _
  rw [factorization_rad (block_ne_zero hn g j)]

/-- The `p`-valuation of `rad (Bg g k n)` is `1` if `p ∈ (Bg g k n).primeFactors`, else `0`. -/
lemma factorization_rad_Bg (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) (p : ℕ) :
    (rad (Bg g k n)).factorization p = if p ∈ (Bg g k n).primeFactors then 1 else 0 :=
  factorization_rad (Bg_ne_zero hg hn k) p

/-- A prime in the support of `Bg g k n` divides some block, hence `overlapg ≥ 1`. -/
lemma overlapg_pos_of_mem_primeFactors {g k n p : ℕ} (hn : 1 ≤ n)
    (hp : p ∈ (Bg g k n).primeFactors) : 1 ≤ overlapg g k n p := by
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpdvd : p ∣ Bg g k n := Nat.dvd_of_mem_primeFactors hp
  have : ∃ j ∈ Finset.range (k / g), p ∣ F g (n + g * j) := by
    rw [Bg] at hpdvd
    exact (Nat.Prime.prime hpprime).exists_mem_finset_dvd hpdvd
  obtain ⟨j, hj, hjdvd⟩ := this
  unfold overlapg
  have hmem : p ∈ (F g (n + g * j)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpprime, hjdvd, block_ne_zero hn g j⟩
  have hle := Finset.single_le_sum
    (f := fun i => if p ∈ (F g (n + g * i)).primeFactors then (1:ℕ) else 0)
    (by intro i _; positivity) hj
  simpa [hmem] using hle

/-- If `overlapg g k n p ≥ 1` then `p ∈ (Bg g k n).primeFactors`. -/
lemma mem_primeFactors_of_overlapg_pos {g k n p : ℕ} (hn : 1 ≤ n) (h : 1 ≤ overlapg g k n p) :
    p ∈ (Bg g k n).primeFactors := by
  unfold overlapg at h
  obtain ⟨j, hj, hjne⟩ : ∃ j ∈ Finset.range (k / g),
      (if p ∈ (F g (n + g * j)).primeFactors then (1:ℕ) else 0) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : ∑ j ∈ Finset.range (k / g),
        (if p ∈ (F g (n + g * j)).primeFactors then (1:ℕ) else 0) = 0 :=
      Finset.sum_eq_zero (fun j hj => hcon j hj)
    omega
  -- The block range is nonempty (`j ∈ range (k/g)`), so `k/g ≥ 1`, forcing `g ≥ 1`.
  have hg1 : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with hg0 | hg0
    · exfalso; subst hg0; simp at hj
    · exact hg0
  have hmem : p ∈ (F g (n + g * j)).primeFactors := by
    by_contra hc; simp [hc] at hjne
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hmem).1
  have hpdvd_block : p ∣ F g (n + g * j) := Nat.dvd_of_mem_primeFactors hmem
  have hpdvdB : p ∣ Bg g k n := by
    rw [Bg]; exact dvd_trans hpdvd_block (Finset.dvd_prod_of_mem _ hj)
  exact Nat.mem_primeFactors.mpr ⟨hpprime, hpdvdB, Bg_ne_zero hg1 hn k⟩

/-- For a prime power `q ^ e` with `q` prime, its `p`-valuation is `e` if `q = p`, else `0`. -/
private lemma factorization_prime_pow_applyg {q : ℕ} (hq : q.Prime) (e p : ℕ) :
    (q ^ e).factorization p = if q = p then e else 0 := by
  rw [Nat.Prime.factorization_pow hq]
  rw [Finsupp.single_apply]

/-- The `p`-valuation of the over-count `Wg g k n`. -/
lemma factorization_Wg {g k n : ℕ} (_hn : 1 ≤ n) (p : ℕ) :
    (Wg g k n).factorization p =
      if p ∈ (Bg g k n).primeFactors then overlapg g k n p - 1 else 0 := by
  unfold Wg
  rw [Nat.factorization_prod_apply (by
    intro q hq
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero)]
  by_cases hp : p ∈ (Bg g k n).primeFactors
  · simp only [hp, if_true]
    rw [Finset.sum_eq_single p]
    · have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
      rw [factorization_prime_pow_applyg hpprime]
      simp
    · intro q hq hqp
      have hqprime : q.Prime := (Nat.mem_primeFactors.mp hq).1
      rw [factorization_prime_pow_applyg hqprime]
      simp [hqp]
    · intro h; exact absurd hp h
  · simp only [hp, if_false]
    apply Finset.sum_eq_zero
    intro q hq
    have hqprime : q.Prime := (Nat.mem_primeFactors.mp hq).1
    rw [factorization_prime_pow_applyg hqprime]
    have : q ≠ p := by rintro rfl; exact hp hq
    simp [this]

/-- **Radical-of-product decomposition (generic `g`), exact form.**
`∏_j rad (F g (n+g·j)) = rad (Bg g k n) * Wg g k n`. Generic form of
`rad_triples_decomp`/`rad_blocks5_decomp`. -/
theorem rad_blocksg_decomp (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / g), rad (F g (n + g * j))) = rad (Bg g k n) * Wg g k n := by
  have hR_ne : (∏ j ∈ Finset.range (k / g), rad (F g (n + g * j))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Nat.one_le_iff_ne_zero.mp (rad_pos _)
  have hradB_ne : rad (Bg g k n) ≠ 0 := Nat.one_le_iff_ne_zero.mp (rad_pos _)
  have hW_ne : Wg g k n ≠ 0 := by
    unfold Wg; exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  apply Nat.eq_of_factorization_eq hR_ne (mul_ne_zero hradB_ne hW_ne)
  intro p
  rw [factorization_blocksg_rad g k n p hn]
  rw [Nat.factorization_mul hradB_ne hW_ne]
  simp only [Finsupp.add_apply]
  rw [factorization_rad_Bg hg hn p, factorization_Wg hn p]
  by_cases hp : p ∈ (Bg g k n).primeFactors
  · simp only [hp, if_true]
    have h1 : 1 ≤ overlapg g k n p := overlapg_pos_of_mem_primeFactors hn hp
    omega
  · simp only [hp, if_false, add_zero]
    by_contra hcon
    have : 1 ≤ overlapg g k n p := by omega
    exact hp (mem_primeFactors_of_overlapg_pos hn this)

/-- `rad (Bg g k n) ∣ rad (F k n)`. -/
lemma rad_Bg_dvd_rad_F (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) : rad (Bg g k n) ∣ rad (F k n) :=
  rad_dvd_rad_of_dvd (F_ne_zero hn) (Bg_dvd_F hg k n)

/-- **Decomposition inequality (the usable form, generic `g`):**
`∏_j rad (F g (n+g·j)) ≤ rad (F k n) * Wg g k n`
(generic form of `rad_triples_le`/`rad_5blocks_le`). -/
theorem rad_blocksg_le (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / g), rad (F g (n + g * j))) ≤ rad (F k n) * Wg g k n := by
  rw [rad_blocksg_decomp hg hn]
  apply Nat.mul_le_mul_right
  exact Nat.le_of_dvd (rad_pos _) (rad_Bg_dvd_rad_F hg hn)

/-! ### The overlap bound `Wg g k n ≤ k^k` -/

/-- The "first hit" map used to inject the counted `g`-blocks into the multiples of `p` in the
spanning interval. `firstHit g n p j` is `n + g·j + r₀`, where `r₀ < g` is the least block offset
with `p ∣ (n + g·j + r₀)` (defaulting to `g - 1` if none — that branch is never taken for counted
blocks). Replaces the hardcoded `if … then … else …` chains of `overlap_le`/`overlap5_le` by a
uniform construction that works for any block length `g`. -/
def firstHit (g n p j : ℕ) : ℕ :=
  n + g * j + (((Finset.range g).filter (fun r => p ∣ (n + g * j + r))).min.getD (g - 1))

/-- `firstHit g n p j` lies in the block `[n + g·j, n + g·j + (g-1)]`. -/
lemma firstHit_mem_Icc (g n p j : ℕ) :
    firstHit g n p j ∈ Finset.Icc (n + g * j) (n + g * j + (g - 1)) := by
  simp only [firstHit, Finset.mem_Icc]
  refine ⟨by omega, ?_⟩
  rcases ((Finset.range g).filter (fun r => p ∣ (n + g * j + r))).min.eq_none_or_eq_some
    with hnone | ⟨r0, hr0⟩
  · simp [hnone]
  · have hr0mem : r0 ∈ (Finset.range g).filter (fun r => p ∣ (n + g * j + r)) :=
      Finset.mem_of_min hr0
    rw [Finset.mem_filter, Finset.mem_range] at hr0mem
    simp only [hr0, Option.getD]; omega

/-- **Overlap bound (combinatorial core, generic `g`).** `overlapg g k n p ≤ ⌊k/p⌋ + 1` for
`n ≥ 1`. The `⌊k/g⌋` blocks span `≤ k` consecutive integers, and a prime `p` divides at most
`⌊k/p⌋ + 1` of any `≤ k` consecutive integers. Generic form of `overlap_le`/`overlap5_le`. -/
lemma overlapg_le (hg : 1 ≤ g) {k n p : ℕ} (hn : 1 ≤ n) : overlapg g k n p ≤ k / p + 1 := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · subst hp0; unfold overlapg
    have hz : (∑ j ∈ Finset.range (k / g),
        (if (0 : ℕ) ∈ (F g (n + g * j)).primeFactors then (1 : ℕ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hnotmem : (0 : ℕ) ∉ (F g (n + g * j)).primeFactors := by
        intro h; exact absurd (Nat.prime_of_mem_primeFactors h) Nat.not_prime_zero
      rw [if_neg hnotmem]
    rw [hz]; omega
  · set t := k / g with ht
    set m := g * t with hm
    have hmk : m ≤ k := by rw [hm, ht]; exact Nat.mul_div_le k g
    -- Each counted block `j` contributes a divisible integer in `(n-1, n-1+m]`: `firstHit g n p j`.
    have hkey : overlapg g k n p ≤ #{x ∈ Finset.Ioc (n - 1) (n - 1 + m) | p ∣ x} := by
      unfold overlapg
      have hsum : (∑ j ∈ Finset.range t,
          (if p ∈ (F g (n + g * j)).primeFactors then (1 : ℕ) else 0))
          = #{j ∈ Finset.range t | p ∈ (F g (n + g * j)).primeFactors} := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
          mul_one]
      rw [show k / g = t from rfl, hsum]
      apply Finset.card_le_card_of_injOn (firstHit g n p)
      · intro j hj
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
        obtain ⟨hjt, hmem⟩ := hj
        have hpp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
        have hpdvd : p ∣ F g (n + g * j) := Nat.dvd_of_mem_primeFactors hmem
        -- `p` divides some factor `n + g·j + r` with `r < g`.
        have hexists : ∃ r ∈ Finset.range g, p ∣ (n + g * j + r) := by
          have hprod : p ∣ ∏ i ∈ Finset.range g, (n + g * j + i) := by
            have hF : F g (n + g * j) = ∏ i ∈ Finset.range g, ((n + g * j) + i) := by
              unfold F; rfl
            rwa [hF] at hpdvd
          obtain ⟨i, hi, hidvd⟩ := (Nat.Prime.prime hpp).exists_mem_finset_dvd hprod
          exact ⟨i, hi, hidvd⟩
        set S : Finset ℕ := (Finset.range g).filter (fun r => p ∣ (n + g * j + r)) with hS
        have hSne : S.Nonempty := by
          obtain ⟨r, hr, hrd⟩ := hexists
          exact ⟨r, by rw [hS, Finset.mem_filter]; exact ⟨hr, hrd⟩⟩
        obtain ⟨r0, hr0min⟩ := Finset.min_of_nonempty hSne
        have hr0mem : r0 ∈ S := Finset.mem_of_min hr0min
        rw [hS, Finset.mem_filter, Finset.mem_range] at hr0mem
        obtain ⟨hr0lt, hr0dvd⟩ := hr0mem
        have hval : firstHit g n p j = n + g * j + r0 := by
          simp only [firstHit, ← hS, hr0min, Option.getD]
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc, hval]
        refine ⟨⟨?_, ?_⟩, hr0dvd⟩
        · omega
        · have hr0m : g * j + r0 < m := by
            rw [hm]
            calc g * j + r0 < g * j + g := by omega
              _ = g * (j + 1) := by ring
              _ ≤ g * t := Nat.mul_le_mul_left g hjt
          omega
      · intro j hj j' hj' heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj hj'
        have h1 := firstHit_mem_Icc g n p j
        have h2 := firstHit_mem_Icc g n p j'
        simp only [Finset.mem_Icc] at h1 h2
        rw [heq] at h1
        -- From `h1`, `h2`:  g·j ≤ g·j' + (g-1) < g·(j'+1)  and  g·j' ≤ g·j + (g-1) < g·(j+1).
        have hjj' : g * j < g * (j' + 1) := by
          have : g * j ≤ g * j' + (g - 1) := by omega
          calc g * j ≤ g * j' + (g - 1) := this
            _ < g * j' + g := by omega
            _ = g * (j' + 1) := by ring
        have hj'j : g * j' < g * (j + 1) := by
          have : g * j' ≤ g * j + (g - 1) := by omega
          calc g * j' ≤ g * j + (g - 1) := this
            _ < g * j + g := by omega
            _ = g * (j + 1) := by ring
        have hlt1 : j < j' + 1 := Nat.lt_of_mul_lt_mul_left hjj'
        have hlt2 : j' < j + 1 := Nat.lt_of_mul_lt_mul_left hj'j
        omega
    refine le_trans hkey ?_
    refine le_trans (Ioc_dvd_le (n - 1) m p hp) ?_
    have : m / p ≤ k / p := Nat.div_le_div_right hmk
    omega

/-- **Overlap product divides `k!` (generic `g`).** `Wg g k n ∣ k!`. Generic form of
`W_dvd_factorial`/`W5_dvd_factorial`. -/
theorem Wg_dvd_factorial (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) : Wg g k n ∣ Nat.factorial k := by
  have hWne : Wg g k n ≠ 0 := by
    unfold Wg; exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← Nat.factorization_le_iff_dvd hWne (Nat.factorial_ne_zero k)]
  intro p
  rw [factorization_Wg hn p]
  by_cases hp : p ∈ (Bg g k n).primeFactors
  · simp only [hp, if_true]
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have h1 : overlapg g k n p ≤ k / p + 1 := overlapg_le hg hn
    have h2 : k / p ≤ (Nat.factorial k).factorization p := div_le_factorization_factorial hpp
    omega
  · simp only [hp, if_false]; exact Nat.zero_le _

/-- **Overlap bound (generic `g`): `Wg g k n ≤ k^k`.** Since `Wg ∣ k!` (Legendre) and `k! ≤ k^k`.
Generic form of `W_le_pow`/`W5_le_pow`. -/
theorem Wg_le_pow (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) : Wg g k n ≤ k ^ k := by
  calc Wg g k n ≤ Nat.factorial k := Nat.le_of_dvd (Nat.factorial_pos k) (Wg_dvd_factorial hg hn)
    _ ≤ k ^ k := Nat.factorial_le_pow k

/-! ## PART B — the generic block radical hypothesis -/

/-- Tail-absorbed `g`-block radical input. NORMALIZED hypothesis (not the literal blockwise
abc/Langevin statement): packages the abc constant, epsilon loss, and omitted tail. The guard
`g ≤ k` is essential — for `g > k` there are no `g`-blocks (`⌊k/g⌋ = 0`), the RHS is the empty
product `1`, and `(F k n)^{(g-1)/g} ≤ 1` would be inconsistent. -/
def BlockRadLBg (g : ℕ) : Prop :=
  ∀ k n : ℕ, g ≤ k → 1 ≤ n →
    (F k n : ℝ) ^ (((g : ℝ) - 1) / (g : ℝ)) ≤
      ((∏ j ∈ Finset.range (k / g), rad (F g (n + g * j)) : ℕ) : ℝ)

/-! ## PART C — the unified master inequality and finiteness -/

/-- **Smooth-refined master inequality (generic `g`).** Under `BlockRadLBg g`, for `k ≥ g ≥ 3` and a
powerful `F k n` with `n ≥ 1`:

  `n ^ ((g - 2) * k) · L k ^ g  ≤  (k ^ (2k)) ^ g · P k ^ (2g)`.

This is `master_ineq5`'s proof with the symbolic exponent `g` in place of `5`, the block exponent
`(g-1)/g` in place of `4/5`, and the intermediate `(g-2)/g` in place of `3/5`. Specializes to
`master_ineq` (`g = 3`) and `master_ineq5` (`g = 5`). -/
theorem master_ineq_g (g : ℕ) (hBlock : BlockRadLBg g) (hg : 3 ≤ g) {k n : ℕ}
    (hk : g ≤ k) (hn : 1 ≤ n) (hPow : Powerful (F k n)) :
    (n : ℝ) ^ ((g - 2) * k) * (L k : ℝ) ^ g ≤ ((k : ℝ) ^ (2 * k)) ^ g * (P k : ℝ) ^ (2 * g) := by
  have hg1 : 1 ≤ g := by omega
  have hkpos : 0 < k := by omega
  -- Real facts about `g`.
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hgRpos : (0 : ℝ) < (g : ℝ) := by linarith
  have hgR1 : (0 : ℝ) ≤ (g : ℝ) - 1 := by linarith
  have hgR2 : (0 : ℝ) ≤ (g : ℝ) - 2 := by linarith
  set Φ : ℝ := (F k n : ℝ) with hΦ
  have hFne : F k n ≠ 0 := F_ne_zero hn
  have hΦpos : 0 < Φ := by rw [hΦ]; exact_mod_cast Nat.pos_of_ne_zero hFne
  have hLpos : (0 : ℝ) < (L k : ℝ) := by exact_mod_cast L_pos k
  -- Block chain: Φ^{(g-1)/g} ≤ ∏rad ≤ rad·Wg ≤ rad·k^k.
  have hblk := hBlock k n hk hn
  set Prd : ℝ := ((∏ j ∈ Finset.range (k / g), rad (F g (n + g * j)) : ℕ) : ℝ) with hPrd
  have hdecomp : Prd ≤ (rad (F k n) : ℝ) * (Wg g k n : ℝ) := by
    rw [hPrd]; exact_mod_cast rad_blocksg_le hg1 hn
  have hradpos : (0 : ℝ) ≤ (rad (F k n) : ℝ) := by positivity
  have hW : (Wg g k n : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Wg_le_pow hg1 hn
  have hchain : Φ ^ (((g : ℝ) - 1) / (g : ℝ)) ≤ (rad (F k n) : ℝ) * (k : ℝ) ^ k :=
    le_trans (le_trans hblk hdecomp) (mul_le_mul_of_nonneg_left hW hradpos)
  -- Square: Φ^{2(g-1)/g} ≤ rad^2 · k^{2k}.
  have hbase_nonneg : (0 : ℝ) ≤ Φ ^ (((g : ℝ) - 1) / (g : ℝ)) := Real.rpow_nonneg (le_of_lt hΦpos) _
  have hsq : (Φ ^ (((g : ℝ) - 1) / (g : ℝ))) ^ 2 ≤ ((rad (F k n) : ℝ) * (k : ℝ) ^ k) ^ 2 :=
    pow_le_pow_left₀ hbase_nonneg hchain 2
  have hLsq : (Φ ^ (((g : ℝ) - 1) / (g : ℝ))) ^ 2 = Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) := by
    rw [← Real.rpow_natCast (Φ ^ (((g : ℝ) - 1) / (g : ℝ))) 2, ← Real.rpow_mul (le_of_lt hΦpos)]
    congr 1; ring
  have hRsq : ((rad (F k n) : ℝ) * (k : ℝ) ^ k) ^ 2
      = (rad (F k n) : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := by
    rw [mul_pow, ← pow_mul]; ring_nf
  rw [hLsq, hRsq] at hsq
  -- smooth_refinement (cast): rad^2 · L ≤ Φ · P^2.
  have hsmooth : (rad (F k n) : ℝ) ^ 2 * (L k : ℝ) ≤ Φ * (P k : ℝ) ^ 2 := by
    rw [hΦ]; exact_mod_cast smooth_refinement hn hPow
  -- Combine: Φ^{2(g-1)/g} · L ≤ Φ · P^2 · k^{2k}.
  have hk2kpos : (0 : ℝ) < (k : ℝ) ^ (2 * k) := by positivity
  have hstep : Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) * (L k : ℝ)
      ≤ Φ * (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := by
    calc Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) * (L k : ℝ)
        ≤ ((rad (F k n) : ℝ) ^ 2 * (k : ℝ) ^ (2 * k)) * (L k : ℝ) :=
          mul_le_mul_of_nonneg_right hsq (le_of_lt hLpos)
      _ = ((rad (F k n) : ℝ) ^ 2 * (L k : ℝ)) * (k : ℝ) ^ (2 * k) := by ring
      _ ≤ (Φ * (P k : ℝ) ^ 2) * (k : ℝ) ^ (2 * k) :=
          mul_le_mul_of_nonneg_right hsmooth (le_of_lt hk2kpos)
      _ = Φ * (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := by ring
  -- Divide by Φ:  Φ^{(g-2)/g} · L ≤ P^2 · k^{2k}.   (2(g-1)/g = (g-2)/g + 1.)
  have hexp_id : 2 * ((g : ℝ) - 1) / (g : ℝ) = ((g : ℝ) - 2) / (g : ℝ) + 1 := by
    field_simp; ring
  have hΦsplit : Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) = Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * Φ := by
    rw [hexp_id, Real.rpow_add hΦpos, Real.rpow_one]
  rw [hΦsplit] at hstep
  have hdiv : Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ) ≤ (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := by
    have h : Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ) * Φ
        ≤ (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) * Φ := by
      calc Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ) * Φ
          = Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * Φ * (L k : ℝ) := by ring
        _ ≤ Φ * (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := hstep
        _ = (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) * Φ := by ring
    exact le_of_mul_le_mul_right h hΦpos
  -- Use Φ ≥ n^k:  (n^k)^{(g-2)/g}·L ≤ Φ^{(g-2)/g}·L ≤ P^2·k^{2k}.
  have hFlow : (n : ℝ) ^ k ≤ Φ := by rw [hΦ]; exact_mod_cast pow_le_F (k := k) (n := n)
  have hnk_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
  have hexp_nonneg : (0 : ℝ) ≤ ((g : ℝ) - 2) / (g : ℝ) := by positivity
  have hnpow : ((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) ≤ Φ ^ (((g : ℝ) - 2) / (g : ℝ)) :=
    Real.rpow_le_rpow hnk_nonneg hFlow hexp_nonneg
  have hkey : ((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ)
      ≤ (P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) :=
    le_trans (mul_le_mul_of_nonneg_right hnpow (le_of_lt hLpos)) hdiv
  -- Raise to the `g` power (clears the `/g`):
  --   n^{(g-2)k} · L^g ≤ (P^2 · k^{2k})^g = (k^{2k})^g · P^{2g}.
  have hLHS_nonneg : (0 : ℝ) ≤ ((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ) := by
    positivity
  have hpowg : (((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ)) ^ g
      ≤ ((P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k)) ^ g :=
    pow_le_pow_left₀ hLHS_nonneg hkey g
  -- Simplify the left side: ((n^k)^{(g-2)/g})^g · L^g = n^{(g-2)k} · L^g.
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega : n ≠ 0)
  have hLHS : (((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ)) ^ g
      = (n : ℝ) ^ ((g - 2) * k) * (L k : ℝ) ^ g := by
    rw [mul_pow]
    congr 1
    -- ((n^k)^{(g-2)/g})^g = (n^k)^{(g-2)} = n^{(g-2)k}.
    have hexp : (((g : ℝ) - 2) / (g : ℝ)) * (g : ℝ) = ((g : ℝ) - 2) := by
      field_simp
    rw [← Real.rpow_natCast (((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ))) g,
      ← Real.rpow_mul hnk_nonneg, hexp]
    -- (n^k)^{(g-2)} = n^{(g-2)*k}, both as rpow.
    rw [← Real.rpow_natCast (n : ℝ) k, ← Real.rpow_mul (le_of_lt hnpos),
      ← Real.rpow_natCast (n : ℝ) ((g - 2) * k)]
    congr 1
    -- (↑k) * (↑g - 2) = ↑((g-2)*k)
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ g)]
    push_cast
    ring
  have hRHS : ((P k : ℝ) ^ 2 * (k : ℝ) ^ (2 * k)) ^ g
      = ((k : ℝ) ^ (2 * k)) ^ g * (P k : ℝ) ^ (2 * g) := by
    rw [mul_pow, ← pow_mul, mul_comm 2 g]; ring
  rw [hLHS, hRHS] at hpowg
  exact hpowg

/-- The explicit generic `g`-block finiteness bound `Mg g k = (k^{2k})^g · P k^{2g}`. Generic form
of `Msplice`. -/
def Mg (g k : ℕ) : ℕ := (k ^ (2 * k)) ^ g * P k ^ (2 * g)

/-- **Exact generic threshold.** Under `BlockRadLBg g`, if the exact master threshold is violated —
`Mg g k < n^{(g-2)k} · L k ^ g` — then `F k n` is not powerful. This is the generic form of
`not_powerful_g5`; it carries the sharp exponent (the `L k ^ g` factor) before any coarse `L ≥ 1`
collapse, and `powerful_bound_g`/`g_finiteness` are its corollaries. -/
theorem not_powerful_g (g : ℕ) (hBlock : BlockRadLBg g) (hg : 3 ≤ g) {k n : ℕ}
    (hk : g ≤ k) (hn : 1 ≤ n)
    (hthr : (Mg g k : ℕ) < n ^ ((g - 2) * k) * L k ^ g) :
    ¬ Powerful (F k n) := by
  intro hPow
  have hmaster := master_ineq_g g hBlock hg hk hn hPow
  have hcast : ((Mg g k : ℕ) : ℝ) < ((n ^ ((g - 2) * k) * L k ^ g : ℕ) : ℝ) := by
    exact_mod_cast hthr
  rw [Mg] at hcast
  push_cast at hcast hmaster
  linarith [hcast, hmaster]

/-- **Explicit per-`k` bound (generic `g`).** A powerful `F k n` (with `k ≥ g ≥ 3`, `n ≥ 1`) forces
`n ≤ Mg g k`. Generic form of `powerful_bound_g5`; the corollary of `not_powerful_g` after the
coarse `L ≥ 1` collapse and `n ≤ n^{(g-2)k}`. -/
theorem powerful_bound_g (g : ℕ) (hBlock : BlockRadLBg g) (hg : 3 ≤ g) {k n : ℕ}
    (hk : g ≤ k) (hn : 1 ≤ n) (hPow : Powerful (F k n)) : n ≤ Mg g k := by
  by_contra hnot
  have hcon : Mg g k < n := by omega
  have hexp_pos : (g - 2) * k ≠ 0 := by
    have h1 : 1 ≤ g - 2 := by omega
    have h2 : 1 ≤ k := by omega
    exact Nat.mul_ne_zero (by omega) (by omega)
  have hthr : (Mg g k : ℕ) < n ^ ((g - 2) * k) * L k ^ g := by
    calc Mg g k
        < n := hcon
      _ ≤ n ^ ((g - 2) * k) := Nat.le_self_pow hexp_pos n
      _ ≤ n ^ ((g - 2) * k) * L k ^ g :=
          Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (pow_ne_zero _ (L_ne_zero k)))
  exact not_powerful_g g hBlock hg hk hn hthr hPow

/-- **Generic `g`-block per-fixed-`k` finiteness (from `BlockRadLBg g` ALONE).** For `k ≥ g ≥ 3`,
under the single analytic hypothesis `BlockRadLBg g`, the set of `n ≥ 1` with `F k n` powerful is
**finite**: every such `n` satisfies `n ≤ Mg g k`. Generic form of `g5_finiteness`. -/
theorem g_finiteness (g : ℕ) (hBlock : BlockRadLBg g) (hg : 3 ≤ g) {k : ℕ} (hk : g ≤ k) :
    {n : ℕ | 1 ≤ n ∧ Powerful (F k n)}.Finite := by
  apply Set.Finite.subset (Set.finite_Iic (Mg g k))
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iic]
  exact powerful_bound_g g hBlock hg hk hn.1 hn.2

/-! ## PART E — the crude (non-smooth) route

The crude route drops the smooth gain `L`/`P` entirely and uses only the bare powerful inequality
`rad (F k n) ^ 2 ≤ F k n` (`powerful_rad_sq_le`). It yields a *weaker exponent* than the smooth
route (`master_ineq_g`), but with a **fully explicit constant** and a clean INTEGER master
inequality `n ^ (g - 2) ≤ k ^ (2 * g)` — the exact threshold `k ^ (2 * g / (g - 2))` with no
`o(1)` and no unformalized Mertens input:

* `g = 3` ⟹ `n ^ 1 ≤ k ^ 6`  (threshold `k ^ 6`, matching `not_powerful_of_large`);
* `g = 4` ⟹ `n ^ 2 ≤ k ^ 8`  ↔ `n ≤ k ^ 4` (threshold `k ^ 4`);
* `g = 6` ⟹ `n ^ 4 ≤ k ^ {12}` ↔ `n ≤ k ^ 3` (threshold `k ^ 3`).

Contrast the SMOOTH `master_ineq_g` (`n ^ ((g-2) k) · L ^ g ≤ …`): that route carries the sharper
exponent `k ^ {2g/(g-2) + o(1)}` (coarse reading) / `k ^ {g/(g-2) + o(1)}` (Mertens reading), but
the sharpening is only available through the *unformalized* Mertens lower bound on `L`. The crude
route below trades that sharper exponent for a fully explicit, formalized integer constant. -/

/-- **Crude master inequality (generic `g`, non-smooth).** Under `BlockRadLBg g`, for `k ≥ g ≥ 3`
and a powerful `F k n` with `n ≥ 1`, the clean INTEGER inequality

  `n ^ (g - 2) ≤ k ^ (2 * g)`.

This is `not_powerful_of_large`'s real chain (`Φ^{(g-1)/g} ≤ rad · k^k`, square using the crude
`rad ^ 2 ≤ Φ`, divide by `Φ`, use `n^k ≤ Φ`) run with the symbolic exponents `(g-1)/g`, `(g-2)/g`,
then raised to the `g`-th power and the common `k`-th power dropped via `Nat.pow_le_pow_iff_left`.
Specializes to the `g = 3` threshold `n ≤ k^6` and the `g = 4` threshold `n^2 ≤ k^8` (`n ≤ k^4`). -/
theorem master_ineq_crude_g (g : ℕ) (hBlock : BlockRadLBg g) (hg : 3 ≤ g) {k n : ℕ}
    (hk : g ≤ k) (hn : 1 ≤ n) (hPow : Powerful (F k n)) : n ^ (g - 2) ≤ k ^ (2 * g) := by
  have hg1 : 1 ≤ g := by omega
  have hkpos : 0 < k := by omega
  have hkne : k ≠ 0 := by omega
  -- Real facts about `g`.
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hgRpos : (0 : ℝ) < (g : ℝ) := by linarith
  set Φ : ℝ := (F k n : ℝ) with hΦ
  have hFne : F k n ≠ 0 := F_ne_zero hn
  have hΦpos : 0 < Φ := by rw [hΦ]; exact_mod_cast Nat.pos_of_ne_zero hFne
  -- Block chain: Φ^{(g-1)/g} ≤ ∏rad ≤ rad·Wg ≤ rad·k^k.
  have hblk := hBlock k n hk hn
  set Prd : ℝ := ((∏ j ∈ Finset.range (k / g), rad (F g (n + g * j)) : ℕ) : ℝ) with hPrd
  have hdecomp : Prd ≤ (rad (F k n) : ℝ) * (Wg g k n : ℝ) := by
    rw [hPrd]; exact_mod_cast rad_blocksg_le hg1 hn
  have hradsq : (rad (F k n) : ℝ) ^ 2 ≤ Φ := by
    rw [hΦ]; exact_mod_cast powerful_rad_sq_le hFne hPow
  have hradpos : (0 : ℝ) ≤ (rad (F k n) : ℝ) := by positivity
  have hW : (Wg g k n : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Wg_le_pow hg1 hn
  have hFlow : (n : ℝ) ^ k ≤ Φ := by rw [hΦ]; exact_mod_cast pow_le_F (k := k) (n := n)
  -- Chain: Φ^{(g-1)/g} ≤ ∏rad ≤ rad·W ≤ rad·k^k; square it.
  have hchain : Φ ^ (((g : ℝ) - 1) / (g : ℝ)) ≤ (rad (F k n) : ℝ) * (k : ℝ) ^ k :=
    le_trans (le_trans hblk hdecomp) (mul_le_mul_of_nonneg_left hW hradpos)
  have hbase_nonneg : (0 : ℝ) ≤ Φ ^ (((g : ℝ) - 1) / (g : ℝ)) := Real.rpow_nonneg (le_of_lt hΦpos) _
  have hsq : (Φ ^ (((g : ℝ) - 1) / (g : ℝ))) ^ 2 ≤ ((rad (F k n) : ℝ) * (k : ℝ) ^ k) ^ 2 :=
    pow_le_pow_left₀ hbase_nonneg hchain 2
  have hLsq : (Φ ^ (((g : ℝ) - 1) / (g : ℝ))) ^ 2 = Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) := by
    rw [← Real.rpow_natCast (Φ ^ (((g : ℝ) - 1) / (g : ℝ))) 2, ← Real.rpow_mul (le_of_lt hΦpos)]
    congr 1; ring
  have hRsq : ((rad (F k n) : ℝ) * (k : ℝ) ^ k) ^ 2
      = (rad (F k n) : ℝ) ^ 2 * (k : ℝ) ^ (2 * k) := by
    rw [mul_pow, ← pow_mul]; ring_nf
  rw [hLsq, hRsq] at hsq
  -- Use the crude rad² ≤ Φ:  Φ^{2(g-1)/g} ≤ Φ · k^{2k}.
  have hk2kpos : (0 : ℝ) < (k : ℝ) ^ (2 * k) := by positivity
  have hsq2 : Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) ≤ Φ * (k : ℝ) ^ (2 * k) :=
    le_trans hsq (mul_le_mul_of_nonneg_right hradsq (le_of_lt hk2kpos))
  -- Divide by Φ:  Φ^{(g-2)/g} ≤ k^{2k}.   (2(g-1)/g = (g-2)/g + 1.)
  have hexp_id : 2 * ((g : ℝ) - 1) / (g : ℝ) = ((g : ℝ) - 2) / (g : ℝ) + 1 := by
    field_simp; ring
  have hΦsplit : Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) = Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * Φ := by
    rw [hexp_id, Real.rpow_add hΦpos, Real.rpow_one]
  rw [hΦsplit] at hsq2
  have hdiv : Φ ^ (((g : ℝ) - 2) / (g : ℝ)) ≤ (k : ℝ) ^ (2 * k) := by
    have h : Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * Φ ≤ (k : ℝ) ^ (2 * k) * Φ := by
      rw [mul_comm ((k : ℝ) ^ (2 * k)) Φ]; exact hsq2
    exact le_of_mul_le_mul_right h hΦpos
  -- Use Φ ≥ n^k:  (n^k)^{(g-2)/g} ≤ Φ^{(g-2)/g} ≤ k^{2k}.
  have hnk_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
  have hexp_nonneg : (0 : ℝ) ≤ ((g : ℝ) - 2) / (g : ℝ) := by
    apply div_nonneg (by linarith) (by linarith)
  have hnpow : ((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) ≤ Φ ^ (((g : ℝ) - 2) / (g : ℝ)) :=
    Real.rpow_le_rpow hnk_nonneg hFlow hexp_nonneg
  have hkey : ((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) ≤ (k : ℝ) ^ (2 * k) :=
    le_trans hnpow hdiv
  -- Raise to the `g` power (clears the `/g`):  n^{(g-2)k} ≤ (k^{2k})^g = k^{2gk}.
  have hLHS_nonneg : (0 : ℝ) ≤ ((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) :=
    Real.rpow_nonneg hnk_nonneg _
  have hpowg : (((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ))) ^ g ≤ ((k : ℝ) ^ (2 * k)) ^ g :=
    pow_le_pow_left₀ hLHS_nonneg hkey g
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega : n ≠ 0)
  -- Simplify LHS:  ((n^k)^{(g-2)/g})^g = (n^k)^{(g-2)} = n^{(g-2)k}.
  have hLHS : (((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ))) ^ g
      = (n : ℝ) ^ ((g - 2) * k) := by
    have hexp : (((g : ℝ) - 2) / (g : ℝ)) * (g : ℝ) = ((g : ℝ) - 2) := by
      field_simp
    rw [← Real.rpow_natCast (((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ))) g,
      ← Real.rpow_mul hnk_nonneg, hexp]
    rw [← Real.rpow_natCast (n : ℝ) k, ← Real.rpow_mul (le_of_lt hnpos),
      ← Real.rpow_natCast (n : ℝ) ((g - 2) * k)]
    congr 1
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ g)]
    push_cast
    ring
  -- Simplify RHS:  (k^{2k})^g = k^{2gk}.
  have hRHS : ((k : ℝ) ^ (2 * k)) ^ g = (k : ℝ) ^ (2 * g * k) := by
    rw [← pow_mul]; congr 1; ring
  rw [hLHS, hRHS] at hpowg
  -- Cast the real inequality `n^{(g-2)k} ≤ k^{2gk}` down to ℕ.
  have hnat : n ^ ((g - 2) * k) ≤ k ^ (2 * g * k) := by
    have hcast : ((n ^ ((g - 2) * k) : ℕ) : ℝ) ≤ ((k ^ (2 * g * k) : ℕ) : ℝ) := by
      push_cast; exact hpowg
    exact_mod_cast hcast
  -- Rewrite both as `(·)^k` and drop the common `k`-th power.
  have hL2 : n ^ ((g - 2) * k) = (n ^ (g - 2)) ^ k := by rw [← pow_mul]
  have hR2 : k ^ (2 * g * k) = (k ^ (2 * g)) ^ k := by rw [← pow_mul]
  rw [hL2, hR2] at hnat
  exact (Nat.pow_le_pow_iff_left hkne).mp hnat

/-- The right-hand side of the crude master inequality: `Mcrude g k = k ^ (2 * g)`, so the exact
threshold is `Mcrude g k < n ^ (g - 2)`. For example `g = 3` gives `k^6 < n`, while `g = 4` gives
`k^8 < n^2`, equivalently `k^4 < n`. (Note `Mcrude g k` is the bound on `n^{g-2}`, not on `n` itself
unless `g = 3`.) -/
def Mcrude (g k : ℕ) : ℕ := k ^ (2 * g)

/-- **Crude per-`k` non-powerfulness (generic `g`).** Under `BlockRadLBg g`, for `k ≥ g ≥ 3`, if the
crude threshold is violated — `k ^ (2 * g) < n ^ (g - 2)` — then `F k n` is not powerful. Corollary
of `master_ineq_crude_g`. -/
theorem not_powerful_crude_g (g : ℕ) (hBlock : BlockRadLBg g) (hg : 3 ≤ g) {k n : ℕ}
    (hk : g ≤ k) (hn : 1 ≤ n) (hthr : k ^ (2 * g) < n ^ (g - 2)) : ¬ Powerful (F k n) := by
  intro hPow
  have := master_ineq_crude_g g hBlock hg hk hn hPow
  omega

/-- **Explicit crude per-`k` bound (generic `g`).** A powerful `F k n` (with `k ≥ g ≥ 3`, `n ≥ 1`)
forces `n ≤ k ^ (2 * g)`. From `n ^ (g - 2) ≤ k ^ (2 * g)` via `g - 2 ≥ 1` and `n ≤ n ^ (g - 2)`. -/
theorem powerful_bound_crude_g (g : ℕ) (hBlock : BlockRadLBg g) (hg : 3 ≤ g) {k n : ℕ}
    (hk : g ≤ k) (hn : 1 ≤ n) (hPow : Powerful (F k n)) : n ≤ k ^ (2 * g) := by
  have hmaster := master_ineq_crude_g g hBlock hg hk hn hPow
  have hge : n ≤ n ^ (g - 2) := Nat.le_self_pow (by omega) n
  omega

/-- **Crude per-fixed-`k` finiteness (generic `g`).** For `k ≥ g ≥ 3`, under `BlockRadLBg g` ALONE,
the set of `n ≥ 1` with `F k n` powerful is **finite**: every such `n` satisfies `n ≤ k ^ (2 * g)`.
The crude analogue of `g_finiteness`, with a fully explicit threshold. -/
theorem crude_g_finiteness (g : ℕ) (hBlock : BlockRadLBg g) (hg : 3 ≤ g) {k : ℕ} (hk : g ≤ k) :
    {n : ℕ | 1 ≤ n ∧ Powerful (F k n)}.Finite := by
  apply Set.Finite.subset (Set.finite_Iic (k ^ (2 * g)))
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iic]
  exact powerful_bound_crude_g g hBlock hg hk hn.1 hn.2

end  -- noncomputable section

end Erdos137
