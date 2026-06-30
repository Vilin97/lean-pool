/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import LeanPool.Erdos137.BlockFramework

/-!
# Erdős Problem #137: a refined deterministic overlap bound

This file isolates a **deterministic** sharpening of the universal overlap bound `Wg g k n ≤ k^k`
of `BlockFramework`. It contains **no analytic number theory** — no abc/Langevin constant, no
Mertens estimate, no growing-`g` input. Everything below is a finite valuation computation checked
on the standard Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`).

## The refinement

Recall `Wg g k n = ∏_{p ∈ (Bg g k n).primeFactors} p ^ (overlapg g k n p - 1)`, where
`overlapg g k n p` counts the `⌊k/g⌋` blocks `F g (n + g·j)` that `p` divides. `BlockFramework`
bounds the exponent two ways:

* `overlapg_le`: `overlapg g k n p ≤ ⌊k/p⌋ + 1` (interval-count: `p` hits `≤ ⌊k/p⌋ + 1` of any `k`
  consecutive integers), giving `Wg ∣ k!` and `Wg ≤ k^k`.
* (new, easy) `overlapg_le_numBlocks`: `overlapg g k n p ≤ ⌊k/g⌋` (there are only `⌊k/g⌋` blocks),
  reflecting that a prime hits at most `~k/g` blocks.

Combining the two — the exponent `overlapg - 1` is `≤ min(⌊k/p⌋, ⌊k/g⌋)` — gives the **refined
capacity**
```
WgRefinedCap g k = ∏_{p ≤ k} p ^ min(⌊k/p⌋, ⌊k/g⌋),
```
and `Wg g k n ∣ WgRefinedCap g k` (`Wg_dvd_refinedCap`), hence `Wg g k n ≤ WgRefinedCap g k`
(`Wg_le_refinedCap`). This improves the exact overlap factor from `k^k` toward a finite product
whose heuristic logarithm is `k log(k/g) + O(k)` (each prime contributes `≤ ⌊k/g⌋` instead of the
generic `⌊k/p⌋`, capping the small primes that dominate the `k^k` bound).

## Modest scope — what is and is NOT claimed

This is a **contained deterministic improvement of the overlap factor**, NOT a new exponent claim.
In particular:

* For **fixed** `g` it coincides *in scale* with the existing `k^k`/`Mg`/`Mcrude` bounds: the
  refined master inequalities below carry `WgRefinedCap g k` exactly where the old ones carried
  `k^k`, and for fixed `g` no asymptotic improvement to the per-`k` threshold follows.
* **No uniform-in-`g` abc conclusion is claimed.** The heuristic `k log(k/g)` (vs. `k log k` for
  `k^k`) is the *only* place the refinement could matter, and it would matter only for a
  *growing*-`g` strategy. Realizing that requires a uniform-in-`g` Langevin/abc constant
  `A_g ≪ g² log g` (discriminant scale) which is an **open pen-and-paper problem**, NOT formalized
  here. The heuristic logarithm and the `A_g` target are remarks only.

So `WgRefinedCap` is a strictly sharper *deterministic* cap on the overcount; whether it ever beats
`k^k` usefully is gated entirely on the unformalized uniform-`A_g` input.

## Note on the `k + 1`

`WgRefinedCap` ranges over `Nat.primesBelow (k + 1)`, i.e. primes `p ≤ k`, rather than `p < k`.
Including the single boundary prime `p = k` is a deliberate, harmless choice: it makes the
divisibility `Wg ∣ WgRefinedCap` hold directly (the prime `p = k`, if it divides a block, satisfies
`overlapg - 1 ≤ ⌊k/k⌋ = 1`), without a separate large-prime lemma. It does not change the heuristic
logarithm `k log(k/g) + O(k)`.

## Main results (Mathlib's three axioms only)

* `overlapg_le_numBlocks` : `overlapg g k n p ≤ ⌊k/g⌋`.
* `Wg_dvd_refinedCap` : `Wg g k n ∣ WgRefinedCap g k` (the key valuation comparison).
* `Wg_le_refinedCap` : the size form `Wg g k n ≤ WgRefinedCap g k`.
* `rad_blocksg_le_refined` : the refined decomposition inequality `∏ rad ≤ rad(F k n)·WgRefinedCap`.
* `master_ineq_crude_g_refinedOverlap`, `master_ineq_g_refinedOverlap` : the crude and smooth master
  inequalities of `BlockFramework`, restated with `WgRefinedCap g k` in place of `k^k`.
-/

namespace Erdos137

open scoped BigOperators
open Finset

noncomputable section

/-! ## The number-of-blocks bound -/

/-- **Number-of-blocks overlap bound.** `overlapg g k n p ≤ ⌊k/g⌋`: the overlap is a sum of `0/1`
indicators over the `⌊k/g⌋` blocks, so it is at most the number of blocks. This is the easy
companion to `overlapg_le` (`overlapg ≤ ⌊k/p⌋ + 1`); their `min` powers the refined cap. -/
lemma overlapg_le_numBlocks (g k n p : ℕ) : overlapg g k n p ≤ k / g := by
  unfold overlapg
  calc ∑ j ∈ Finset.range (k / g), (if p ∈ (F g (n + g * j)).primeFactors then 1 else 0)
      ≤ ∑ j ∈ Finset.range (k / g), 1 :=
        Finset.sum_le_sum (fun j _ => by split <;> simp)
    _ = k / g := by simp [Finset.sum_const, Finset.card_range]

/-! ## The refined capacity -/

/-- The **refined overlap capacity** `WgRefinedCap g k = ∏_{p ≤ k} p ^ min(⌊k/p⌋, ⌊k/g⌋)`.

The product ranges over `Nat.primesBelow (k + 1)`, i.e. the primes `p ≤ k`; the exponent at `p` is
`min(⌊k/p⌋, ⌊k/g⌋)`, capping the generic Legendre exponent `⌊k/p⌋` by the number of blocks `⌊k/g⌋`.
Using `k + 1` rather than `k` (so the boundary prime `p = k` is included) is a deliberate, harmless
choice that makes `Wg g k n ∣ WgRefinedCap g k` hold without a separate large-prime lemma; the
heuristic logarithm `k log(k/g) + O(k)` is unchanged by the single extra prime. -/
def WgRefinedCap (g k : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow (k + 1), p ^ min (k / p) (k / g)

/-- `1 ≤ WgRefinedCap g k` (empty/prime-power factors are all `≥ 1`).
Mirrors `smoothCapacity_pos`. -/
lemma wgRefinedCap_pos (g k : ℕ) : 1 ≤ WgRefinedCap g k :=
  Finset.one_le_prod' fun _p hp => Nat.one_le_pow _ _ (Nat.prime_of_mem_primesBelow hp).pos

lemma wgRefinedCap_ne_zero (g k : ℕ) : WgRefinedCap g k ≠ 0 :=
  Nat.one_le_iff_ne_zero.mp (wgRefinedCap_pos g k)

/-- **Factorization of the refined capacity.** For prime `p ≤ k`, `v_p(WgRefinedCap g k) =
min(⌊k/p⌋, ⌊k/g⌋)`; for `p ∉ primesBelow (k+1)`, it is `0`.
Mirrors `smoothCapacity_factorization`. -/
lemma wgRefinedCap_factorization (g k p : ℕ) :
    (WgRefinedCap g k).factorization p
      = if p ∈ Nat.primesBelow (k + 1) then min (k / p) (k / g) else 0 := by
  unfold WgRefinedCap
  rw [Nat.factorization_prod (fun q hq => by
    have := (Nat.prime_of_mem_primesBelow hq).pos; positivity)]
  rw [Finset.sum_apply']
  by_cases hp : p ∈ Nat.primesBelow (k + 1)
  · rw [if_pos hp]
    have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    rw [Finset.sum_eq_single p
          (fun q hq hqp => by
            have hqp' : q.Prime := Nat.prime_of_mem_primesBelow hq
            rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, if_neg hqp])
          (fun h => absurd hp h)]
    rw [Nat.Prime.factorization_pow hpp, Finsupp.single_apply, if_pos rfl]
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro q hq
    have hqp' : q.Prime := Nat.prime_of_mem_primesBelow hq
    have hne : q ≠ p := by rintro rfl; exact hp hq
    rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, if_neg hne]

/-! ## The key divisibility -/

/-- **The overcount divides the refined capacity.** `Wg g k n ∣ WgRefinedCap g k`. Pointwise on
factorizations: at a prime `p ≤ k`, `v_p(Wg) = overlapg - 1 ≤ min(⌊k/p⌋, ⌊k/g⌋) = v_p(cap)` by
`overlapg_le` (`≤ ⌊k/p⌋ + 1`) and `overlapg_le_numBlocks` (`≤ ⌊k/g⌋`); at any other prime, `Wg`'s
support (its prime factors) and the count `overlapg ≤ ⌊k/p⌋ + 1` (which is `1` when `p > k`) force
`v_p(Wg) = 0`. This refines `Wg_dvd_factorial` (`Wg ∣ k!`) by also capping each exponent at
`⌊k/g⌋`. -/
theorem Wg_dvd_refinedCap (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) :
    Wg g k n ∣ WgRefinedCap g k := by
  have hWne : Wg g k n ≠ 0 := by
    unfold Wg; exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← Nat.factorization_le_iff_dvd hWne (wgRefinedCap_ne_zero g k)]
  intro p
  rw [factorization_Wg hn p, wgRefinedCap_factorization g k p]
  by_cases hp : p ∈ Nat.primesBelow (k + 1)
  · -- `p ≤ k` prime: overlapg - 1 ≤ min(⌊k/p⌋, ⌊k/g⌋).
    rw [if_pos hp]
    by_cases hpB : p ∈ (Bg g k n).primeFactors
    · simp only [hpB, if_true]
      have h1 : overlapg g k n p ≤ k / p + 1 := overlapg_le hg hn
      have h2 : overlapg g k n p ≤ k / g := overlapg_le_numBlocks g k n p
      -- `overlapg - 1 ≤ min(⌊k/p⌋, ⌊k/g⌋)`. (Use explicit `Nat` lemmas: `omega`'s `Nat.div`
      -- preprocessing mishandles the two division atoms here.)
      exact Nat.le_min.mpr
        ⟨Nat.sub_le_iff_le_add.mpr h1, le_trans (Nat.sub_le _ 1) h2⟩
    · simp only [hpB, if_false]; exact Nat.zero_le _
  · -- `p ∉ primesBelow (k+1)`: either not prime, or `p > k`; either way `v_p(Wg) = 0`.
    rw [if_neg hp]
    by_cases hpB : p ∈ (Bg g k n).primeFactors
    · simp only [hpB, if_true]
      have hpp : p.Prime := (Nat.mem_primeFactors.mp hpB).1
      -- `p ∉ primesBelow (k+1)` and `p` prime ⟹ `k + 1 ≤ p`, i.e. `p > k`, so `⌊k/p⌋ = 0`.
      have hkp : k + 1 ≤ p := by
        by_contra hlt
        push Not at hlt
        exact hp (Nat.mem_primesBelow.mpr ⟨hlt, hpp⟩)
      have hdiv0 : k / p = 0 := Nat.div_eq_of_lt (by omega)
      set o : ℕ := overlapg g k n p with ho
      have h1 : o ≤ k / p + 1 := overlapg_le hg hn
      rw [hdiv0] at h1
      omega
    · simp only [hpB, if_false]; exact Nat.zero_le _

/-- **Size form of the refined overlap bound.** `Wg g k n ≤ WgRefinedCap g k`, immediate from the
divisibility `Wg_dvd_refinedCap` via `Nat.le_of_dvd`. The deterministic improvement of
`Wg ≤ k^k`. -/
theorem Wg_le_refinedCap (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) :
    Wg g k n ≤ WgRefinedCap g k :=
  Nat.le_of_dvd (wgRefinedCap_pos g k) (Wg_dvd_refinedCap hg hn)

/-! ## The refined decomposition inequality -/

/-- **Refined decomposition inequality.** `∏_j rad (F g (n+g·j)) ≤ rad (F k n) · WgRefinedCap g k`.
The refined analogue of `rad_blocksg_le`: from the exact decomposition `∏ rad = rad(Bg)·Wg`
(`rad_blocksg_decomp`), `rad(Bg) ∣ rad(F k n)` (`rad_Bg_dvd_rad_F`), and `Wg ≤ WgRefinedCap`
(`Wg_le_refinedCap`). -/
theorem rad_blocksg_le_refined (hg : 1 ≤ g) {k n : ℕ} (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (k / g), rad (F g (n + g * j))) ≤ rad (F k n) * WgRefinedCap g k := by
  rw [rad_blocksg_decomp hg hn]
  calc rad (Bg g k n) * Wg g k n
      ≤ rad (F k n) * Wg g k n :=
        Nat.mul_le_mul_right _ (Nat.le_of_dvd (rad_pos _) (rad_Bg_dvd_rad_F hg hn))
    _ ≤ rad (F k n) * WgRefinedCap g k :=
        Nat.mul_le_mul_left _ (Wg_le_refinedCap hg hn)

/-! ## The refined master inequalities

These restate `master_ineq_crude_g` and `master_ineq_g` of `BlockFramework` with `WgRefinedCap g k`
in place of the universal `k^k` factor. The proofs are the originals verbatim, substituting
`rad_blocksg_le_refined` for `rad_blocksg_le` and `(WgRefinedCap g k : ℝ)` for `(k : ℝ)^k`. -/

/-- **Crude master inequality with the refined cap.** Under `BlockRadLBg g`, for `k ≥ g ≥ 3` and a
powerful `F k n` with `n ≥ 1`:

  `n ^ ((g - 2) * k) ≤ WgRefinedCap g k ^ (2 * g)`.

The refined analogue of `master_ineq_crude_g` (whose RHS is `k ^ (2 * g * k) = (k^{2k})^g`). The
chain `Φ^{(g-1)/g} ≤ ∏rad ≤ rad·WgRefinedCap` is squared with the crude `rad² ≤ Φ`, divided by `Φ`,
combined with `n^k ≤ Φ`, and raised to the `g`-th power. The result is the exact refined-cap
inequality `n ^ ((g - 2) * k) ≤ WgRefinedCap g k ^ (2 * g)` — note the `k` stays in the exponent
here, since (unlike the old crude RHS `(k^{2g})^k`) the refined cap is not a perfect `k`-th power
to divide out. -/
theorem master_ineq_crude_g_refinedOverlap (g : ℕ) (hBlock : BlockRadLBg g) (hg : 3 ≤ g) {k n : ℕ}
    (hk : g ≤ k) (hn : 1 ≤ n) (hPow : Powerful (F k n)) :
    n ^ ((g - 2) * k) ≤ WgRefinedCap g k ^ (2 * g) := by
  have hg1 : 1 ≤ g := by omega
  have hkpos : 0 < k := by omega
  have hkne : k ≠ 0 := by omega
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hgRpos : (0 : ℝ) < (g : ℝ) := by linarith
  set Φ : ℝ := (F k n : ℝ) with hΦ
  have hFne : F k n ≠ 0 := F_ne_zero hn
  have hΦpos : 0 < Φ := by rw [hΦ]; exact_mod_cast Nat.pos_of_ne_zero hFne
  set C : ℝ := (WgRefinedCap g k : ℝ) with hC
  have hCpos : (0 : ℝ) < C := by rw [hC]; exact_mod_cast wgRefinedCap_pos g k
  -- Block chain: Φ^{(g-1)/g} ≤ ∏rad ≤ rad·WgRefinedCap.
  have hblk := hBlock k n hk hn
  set Prd : ℝ := ((∏ j ∈ Finset.range (k / g), rad (F g (n + g * j)) : ℕ) : ℝ) with hPrd
  have hdecomp : Prd ≤ (rad (F k n) : ℝ) * C := by
    rw [hPrd, hC]; exact_mod_cast rad_blocksg_le_refined hg1 hn
  have hradsq : (rad (F k n) : ℝ) ^ 2 ≤ Φ := by
    rw [hΦ]; exact_mod_cast powerful_rad_sq_le hFne hPow
  have hradpos : (0 : ℝ) ≤ (rad (F k n) : ℝ) := by positivity
  have hFlow : (n : ℝ) ^ k ≤ Φ := by rw [hΦ]; exact_mod_cast pow_le_F (k := k) (n := n)
  have hchain : Φ ^ (((g : ℝ) - 1) / (g : ℝ)) ≤ (rad (F k n) : ℝ) * C :=
    le_trans hblk hdecomp
  have hbase_nonneg : (0 : ℝ) ≤ Φ ^ (((g : ℝ) - 1) / (g : ℝ)) := Real.rpow_nonneg (le_of_lt hΦpos) _
  have hsq : (Φ ^ (((g : ℝ) - 1) / (g : ℝ))) ^ 2 ≤ ((rad (F k n) : ℝ) * C) ^ 2 :=
    pow_le_pow_left₀ hbase_nonneg hchain 2
  have hLsq : (Φ ^ (((g : ℝ) - 1) / (g : ℝ))) ^ 2 = Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) := by
    rw [← Real.rpow_natCast (Φ ^ (((g : ℝ) - 1) / (g : ℝ))) 2, ← Real.rpow_mul (le_of_lt hΦpos)]
    congr 1; ring
  have hRsq : ((rad (F k n) : ℝ) * C) ^ 2 = (rad (F k n) : ℝ) ^ 2 * C ^ 2 := by
    rw [mul_pow]
  rw [hLsq, hRsq] at hsq
  -- Use the crude rad² ≤ Φ:  Φ^{2(g-1)/g} ≤ Φ · C².
  have hC2pos : (0 : ℝ) < C ^ 2 := by positivity
  have hsq2 : Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) ≤ Φ * C ^ 2 :=
    le_trans hsq (mul_le_mul_of_nonneg_right hradsq (le_of_lt hC2pos))
  -- Divide by Φ:  Φ^{(g-2)/g} ≤ C².
  have hexp_id : 2 * ((g : ℝ) - 1) / (g : ℝ) = ((g : ℝ) - 2) / (g : ℝ) + 1 := by
    field_simp; ring
  have hΦsplit : Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) = Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * Φ := by
    rw [hexp_id, Real.rpow_add hΦpos, Real.rpow_one]
  rw [hΦsplit] at hsq2
  have hdiv : Φ ^ (((g : ℝ) - 2) / (g : ℝ)) ≤ C ^ 2 := by
    have h : Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * Φ ≤ C ^ 2 * Φ := by
      rw [mul_comm (C ^ 2) Φ]; exact hsq2
    exact le_of_mul_le_mul_right h hΦpos
  -- Use Φ ≥ n^k:  (n^k)^{(g-2)/g} ≤ Φ^{(g-2)/g} ≤ C².
  have hnk_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
  have hexp_nonneg : (0 : ℝ) ≤ ((g : ℝ) - 2) / (g : ℝ) := by
    apply div_nonneg (by linarith) (by linarith)
  have hnpow : ((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) ≤ Φ ^ (((g : ℝ) - 2) / (g : ℝ)) :=
    Real.rpow_le_rpow hnk_nonneg hFlow hexp_nonneg
  have hkey : ((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) ≤ C ^ 2 := le_trans hnpow hdiv
  -- Raise to the `g` power:  n^{(g-2)k} ≤ (C²)^g = C^{2g}.
  have hLHS_nonneg : (0 : ℝ) ≤ ((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) :=
    Real.rpow_nonneg hnk_nonneg _
  have hpowg : (((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ))) ^ g ≤ (C ^ 2) ^ g :=
    pow_le_pow_left₀ hLHS_nonneg hkey g
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega : n ≠ 0)
  -- Simplify LHS:  ((n^k)^{(g-2)/g})^g = n^{(g-2)k}.
  have hLHS : (((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ))) ^ g = (n : ℝ) ^ ((g - 2) * k) := by
    have hexp : (((g : ℝ) - 2) / (g : ℝ)) * (g : ℝ) = ((g : ℝ) - 2) := by field_simp
    rw [← Real.rpow_natCast (((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ))) g,
      ← Real.rpow_mul hnk_nonneg, hexp]
    rw [← Real.rpow_natCast (n : ℝ) k, ← Real.rpow_mul (le_of_lt hnpos),
      ← Real.rpow_natCast (n : ℝ) ((g - 2) * k)]
    congr 1
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ g)]
    push_cast
    ring
  -- Simplify RHS:  (C²)^g = C^{2g}.
  have hRHS : (C ^ 2) ^ g = C ^ (2 * g) := by rw [← pow_mul]
  rw [hLHS, hRHS] at hpowg
  -- Cast the real inequality `n^{(g-2)k} ≤ (WgRefinedCap g k)^{2g}` down to ℕ.
  have hcast : ((n ^ ((g - 2) * k) : ℕ) : ℝ) ≤ ((WgRefinedCap g k ^ (2 * g) : ℕ) : ℝ) := by
    rw [hC] at hpowg
    push_cast
    exact hpowg
  exact_mod_cast hcast

/-- **Smooth-refined master inequality with the refined cap.** Under `BlockRadLBg g`, for
`k ≥ g ≥ 3` and a powerful `F k n` with `n ≥ 1`:

  `n ^ ((g - 2) * k) · L k ^ g  ≤  (WgRefinedCap g k) ^ (2 * g) · P k ^ (2 * g)`.

The refined analogue of `master_ineq_g` (whose first RHS factor is `(k^{2k})^g`). The proof is the
original, with `rad_blocksg_le_refined`/`Wg_le_refinedCap` and `(WgRefinedCap g k : ℝ)` in place of
the `k^k` factor throughout the rpow chain. -/
theorem master_ineq_g_refinedOverlap (g : ℕ) (hBlock : BlockRadLBg g) (hg : 3 ≤ g) {k n : ℕ}
    (hk : g ≤ k) (hn : 1 ≤ n) (hPow : Powerful (F k n)) :
    (n : ℝ) ^ ((g - 2) * k) * (L k : ℝ) ^ g
      ≤ (WgRefinedCap g k : ℝ) ^ (2 * g) * (P k : ℝ) ^ (2 * g) := by
  have hg1 : 1 ≤ g := by omega
  have hkpos : 0 < k := by omega
  have hgR : (3 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hgRpos : (0 : ℝ) < (g : ℝ) := by linarith
  set Φ : ℝ := (F k n : ℝ) with hΦ
  have hFne : F k n ≠ 0 := F_ne_zero hn
  have hΦpos : 0 < Φ := by rw [hΦ]; exact_mod_cast Nat.pos_of_ne_zero hFne
  have hLpos : (0 : ℝ) < (L k : ℝ) := by exact_mod_cast L_pos k
  set C : ℝ := (WgRefinedCap g k : ℝ) with hC
  have hCpos : (0 : ℝ) < C := by rw [hC]; exact_mod_cast wgRefinedCap_pos g k
  -- Block chain: Φ^{(g-1)/g} ≤ ∏rad ≤ rad·WgRefinedCap.
  have hblk := hBlock k n hk hn
  set Prd : ℝ := ((∏ j ∈ Finset.range (k / g), rad (F g (n + g * j)) : ℕ) : ℝ) with hPrd
  have hdecomp : Prd ≤ (rad (F k n) : ℝ) * C := by
    rw [hPrd, hC]; exact_mod_cast rad_blocksg_le_refined hg1 hn
  have hradpos : (0 : ℝ) ≤ (rad (F k n) : ℝ) := by positivity
  have hchain : Φ ^ (((g : ℝ) - 1) / (g : ℝ)) ≤ (rad (F k n) : ℝ) * C :=
    le_trans hblk hdecomp
  -- Square: Φ^{2(g-1)/g} ≤ rad² · C².
  have hbase_nonneg : (0 : ℝ) ≤ Φ ^ (((g : ℝ) - 1) / (g : ℝ)) := Real.rpow_nonneg (le_of_lt hΦpos) _
  have hsq : (Φ ^ (((g : ℝ) - 1) / (g : ℝ))) ^ 2 ≤ ((rad (F k n) : ℝ) * C) ^ 2 :=
    pow_le_pow_left₀ hbase_nonneg hchain 2
  have hLsq : (Φ ^ (((g : ℝ) - 1) / (g : ℝ))) ^ 2 = Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) := by
    rw [← Real.rpow_natCast (Φ ^ (((g : ℝ) - 1) / (g : ℝ))) 2, ← Real.rpow_mul (le_of_lt hΦpos)]
    congr 1; ring
  have hRsq : ((rad (F k n) : ℝ) * C) ^ 2 = (rad (F k n) : ℝ) ^ 2 * C ^ 2 := by rw [mul_pow]
  rw [hLsq, hRsq] at hsq
  -- smooth_refinement (cast): rad² · L ≤ Φ · P².
  have hsmooth : (rad (F k n) : ℝ) ^ 2 * (L k : ℝ) ≤ Φ * (P k : ℝ) ^ 2 := by
    rw [hΦ]; exact_mod_cast smooth_refinement hn hPow
  -- Combine: Φ^{2(g-1)/g} · L ≤ Φ · P² · C².
  have hC2pos : (0 : ℝ) < C ^ 2 := by positivity
  have hstep : Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) * (L k : ℝ) ≤ Φ * (P k : ℝ) ^ 2 * C ^ 2 := by
    calc Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) * (L k : ℝ)
        ≤ ((rad (F k n) : ℝ) ^ 2 * C ^ 2) * (L k : ℝ) :=
          mul_le_mul_of_nonneg_right hsq (le_of_lt hLpos)
      _ = ((rad (F k n) : ℝ) ^ 2 * (L k : ℝ)) * C ^ 2 := by ring
      _ ≤ (Φ * (P k : ℝ) ^ 2) * C ^ 2 := mul_le_mul_of_nonneg_right hsmooth (le_of_lt hC2pos)
      _ = Φ * (P k : ℝ) ^ 2 * C ^ 2 := by ring
  -- Divide by Φ:  Φ^{(g-2)/g} · L ≤ P² · C².
  have hexp_id : 2 * ((g : ℝ) - 1) / (g : ℝ) = ((g : ℝ) - 2) / (g : ℝ) + 1 := by
    field_simp; ring
  have hΦsplit : Φ ^ (2 * ((g : ℝ) - 1) / (g : ℝ)) = Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * Φ := by
    rw [hexp_id, Real.rpow_add hΦpos, Real.rpow_one]
  rw [hΦsplit] at hstep
  have hdiv : Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ) ≤ (P k : ℝ) ^ 2 * C ^ 2 := by
    have h : Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ) * Φ ≤ (P k : ℝ) ^ 2 * C ^ 2 * Φ := by
      calc Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ) * Φ
          = Φ ^ (((g : ℝ) - 2) / (g : ℝ)) * Φ * (L k : ℝ) := by ring
        _ ≤ Φ * (P k : ℝ) ^ 2 * C ^ 2 := hstep
        _ = (P k : ℝ) ^ 2 * C ^ 2 * Φ := by ring
    exact le_of_mul_le_mul_right h hΦpos
  -- Use Φ ≥ n^k.
  have hFlow : (n : ℝ) ^ k ≤ Φ := by rw [hΦ]; exact_mod_cast pow_le_F (k := k) (n := n)
  have hnk_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
  have hexp_nonneg : (0 : ℝ) ≤ ((g : ℝ) - 2) / (g : ℝ) := by
    apply div_nonneg (by linarith) (by linarith)
  have hnpow : ((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) ≤ Φ ^ (((g : ℝ) - 2) / (g : ℝ)) :=
    Real.rpow_le_rpow hnk_nonneg hFlow hexp_nonneg
  have hkey : ((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ) ≤ (P k : ℝ) ^ 2 * C ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_right hnpow (le_of_lt hLpos)) hdiv
  -- Raise to the `g` power.
  have hLHS_nonneg : (0 : ℝ) ≤ ((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ) := by
    positivity
  have hpowg : (((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ)) ^ g
      ≤ ((P k : ℝ) ^ 2 * C ^ 2) ^ g :=
    pow_le_pow_left₀ hLHS_nonneg hkey g
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega : n ≠ 0)
  -- Simplify LHS.
  have hLHS : (((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ)) * (L k : ℝ)) ^ g
      = (n : ℝ) ^ ((g - 2) * k) * (L k : ℝ) ^ g := by
    rw [mul_pow]
    congr 1
    have hexp : (((g : ℝ) - 2) / (g : ℝ)) * (g : ℝ) = ((g : ℝ) - 2) := by field_simp
    rw [← Real.rpow_natCast (((n : ℝ) ^ k) ^ (((g : ℝ) - 2) / (g : ℝ))) g,
      ← Real.rpow_mul hnk_nonneg, hexp]
    rw [← Real.rpow_natCast (n : ℝ) k, ← Real.rpow_mul (le_of_lt hnpos),
      ← Real.rpow_natCast (n : ℝ) ((g - 2) * k)]
    congr 1
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ g)]
    push_cast
    ring
  -- Simplify RHS:  (P² · C²)^g = C^{2g} · P^{2g}.
  have hRHS : ((P k : ℝ) ^ 2 * C ^ 2) ^ g = C ^ (2 * g) * (P k : ℝ) ^ (2 * g) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 g, mul_comm]
  rw [hLHS, hRHS] at hpowg
  rw [hC] at hpowg
  exact hpowg

end  -- noncomputable section

end Erdos137
