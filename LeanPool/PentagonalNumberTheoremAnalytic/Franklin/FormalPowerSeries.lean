/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Zify
public import LeanPool.PentagonalNumberTheoremAnalytic.Franklin.Defs
public import LeanPool.PentagonalNumberTheoremAnalytic.Franklin.Helpers
public import LeanPool.PentagonalNumberTheoremAnalytic.Franklin.Lemmas

/-! # Pentagonal Number Theorem — Formal Power Series Statements
This file contains the formal power series identities from the source document
"Pentagonal Number Theorem" by Jonathan Conrad, Paula Muermann, Maryna Viazovska (May 11, 2026).
These results connect the combinatorial content (proved in `Lemmas.lean`)
to the algebraic identities involving generating functions.
-/

@[expose] public section

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace PentagonalNumberTheorem.Franklin

/-- The unrestricted partition count `p(n)`: the number of ways to write
`n` as a sum of positive integers (with repetition allowed, order ignored). -/
noncomputable def pCount (n : ℕ) : ℕ := Fintype.card n.Partition

/-- The generating function for `pCount`: a formal power series in `ℤ⟦X⟧`
whose coefficients are the partition counts. -/
noncomputable def pGenFun : ℤ⟦X⟧ := Nat.Partition.genFun fun _ _ => (1 : ℤ)

/--
**Lemma 3 (combinatorial side).** The `n`-th coefficient of the partition
generating function is `p(n)`.
-/
theorem coeff_pGenFun_eq_p_count (n : ℕ) :
    (coeff n) pGenFun = (pCount n : ℤ) := by
  simp [pGenFun, pCount, Finsupp.prod_fun_one]

/--
**Lemma 3 (product side).** The generating function equals the formal product
`∏_{k≥1} (1 + X^k + X^{2k} + ...)` (the geometric series expansion of each
`(1 - X^k)^{-1}`). The product is taken in the X-adic topology on `ℤ⟦X⟧`,
where it converges (each `[X^n]` only sees finitely many factors).
-/
theorem pGenFun_eq_prod :
    pGenFun
      = ∏' i, ((1 : ℤ⟦X⟧) + ∑' j, (1 : ℤ) • X^((i+1)*(j+1))) :=
  Nat.Partition.genFun_eq_tprod (fun _ _ => (1 : ℤ))

/--
The coefficient of `X^n` in `∏_{k ∈ T} (-X^k)` is `(-1)^|T|` if `∑_{k ∈ T} k = n`,
and `0` otherwise: the product collapses to `(-1)^|T| · X^{T.sum id}`.
-/
theorem coeff_prod_neg_X_pow (n : ℕ) (T : Finset ℕ) :
    (coeff n) (∏ k ∈ T, (-(X ^ k) : ℤ⟦X⟧)) = if T.sum id = n then (-1 : ℤ) ^ T.card else 0 := by
  rw [prod_neg, show (∏ x ∈ T, (X : ℤ⟦X⟧) ^ x) = X ^ T.sum id from prod_pow_eq_pow_sum T id X,
    ← map_one (C (R := ℤ)), ← map_neg, ← map_pow, coeff_C_mul_X_pow]
  simp [eq_comm]

/--
**Lemma 5a (combinatorial expansion).** The coefficient of `X^n` in the
truncated product `∏_{k=1}^{n}(1 - X^k)` equals `∑_{S ∈ distinctPartitions n} (-1)^|S|`.

**Proof sketch.** Rewrite each factor as `1 + (-X^k)` and use the classical
expansion of a product of `1 + a_k` over subsets (`Finset.prod_one_add`):
`∏_{k ∈ {1,…,n}} (1 + (-X^k)) = ∑_{T ⊆ {1,…,n}} ∏_{k ∈ T} (-X^k)`
`                            = ∑_{T ⊆ {1,…,n}} (-1)^|T| · X^{T.sum id}`.
Since `coeff n` is linear, `coeff_prod_neg_X_pow` turns the coefficient into a sum of
`if T.sum id = n then (-1)^|T| else 0` over the powerset, and that is by definition the
sum over `distinctPartitions n` (`Finset.sum_filter`).
-/
theorem coeff_prod_eq_signed_partition_sum (n : ℕ) :
    (coeff n) (∏ k ∈ Finset.Icc 1 n, (1 - X^k : ℤ⟦X⟧)) =
      ∑ S ∈ distinctPartitions n, (-1 : ℤ)^S.card := by
  have h : ∀ k : ℕ, (1 - X ^ k : ℤ⟦X⟧) = 1 + -X ^ k := fun _ => by ring
  simp only [h, prod_one_add, map_sum, coeff_prod_neg_X_pow]
  exact (sum_filter _ _).symm

/--
**Lemma 5b (parity split).** The signed partition sum equals `p_e(n) - p_o(n)`.

The sum splits over the partition
`distinctPartitions n = distinctPartitionsEven n ⊔ distinctPartitionsOdd n`.
On `distinctPartitionsEven`, `(-1)^|S| = 1`; on `distinctPartitionsOdd`, `(-1)^|S| = -1`.
The two pieces give `|distinctPartitionsEven|` and `-|distinctPartitionsOdd|`,
i.e. `p_e(n)` and `-p_o(n)`.
-/
theorem signed_partition_sum_eq_pe_sub_po (n : ℕ) :
    ∑ S ∈ distinctPartitions n, (-1 : ℤ)^S.card = (pe n : ℤ) - po n := by
  have h_sign : ∀ S ∈ distinctPartitions n,
      (-1 : ℤ) ^ S.card = if S.card % 2 = 0 then (1 : ℤ) else -1 := fun S _ => by
    rcases Nat.even_or_odd S.card with h | h
    · rw [h.neg_one_pow, ite_eq_left (Nat.even_iff.1 h)]
    · rw [h.neg_one_pow, ite_eq_right (by rw [Nat.odd_iff] at h; omega)]
  have hodd : {S ∈ distinctPartitions n | ¬S.card % 2 = 0} = distinctPartitionsOdd n :=
    filter_congr fun S _ => by omega
  rw [sum_congr rfl h_sign, sum_ite, hodd, sum_const, sum_const]
  simp [pe, po, distinctPartitionsEven, sub_eq_add_neg]

/--
**Lemma 5 (Source).** For each `n`, the coefficient of `X^n` in the
truncated product `∏_{k=1}^{n}(1 - X^k)` in `ℤ⟦X⟧` equals `p_e(n) - p_o(n)`.

(The truncation matches the infinite product `∏_{k≥1}(1 - X^k)` on this
coefficient because factors with `k > n` are `≡ 1 mod X^{n+1}`.)
-/
theorem coeff_prod_eq_pe_sub_po (n : ℕ) :
    (coeff n) (∏ k ∈ Finset.Icc 1 n, (1 - X^k : ℤ⟦X⟧)) = (pe n : ℤ) - po n := by
  rw [coeff_prod_eq_signed_partition_sum, signed_partition_sum_eq_pe_sub_po]

/--
**PNT (Euler), zero case.** `[X^0] ∏_{k=1}^{0}(1 - X^k) = 1`.
(The product is empty, so this is just `coeff 0 1 = 1`; we state it via
`coeff_prod_eq_pe_sub_po` for uniformity with the other cases.)
-/
theorem coeff_prod_pentagonal_zero :
    (coeff 0) (∏ k ∈ Finset.Icc 1 0, (1 - X^k : ℤ⟦X⟧)) = 1 := by
  rw [coeff_prod_eq_pe_sub_po]; exact pe_minus_po_zero

/--
**PNT (Euler), non-pentagonal case.** For `n ≥ 1` with `2n` not of the
form `3k² - k` nor `3k² + k` for any `k ≥ 1`,
`[X^n] ∏_{k=1}^{n}(1 - X^k) = 0`.
-/
theorem coeff_prod_pentagonal_nonpent (n : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 - k)
    (h2 : ∀ k, 1 ≤ k → 2 * n ≠ 3 * k ^ 2 + k) :
    (coeff n) (∏ k ∈ Finset.Icc 1 n, (1 - X^k : ℤ⟦X⟧)) = 0 := by
  rw [coeff_prod_eq_pe_sub_po]; exact pe_minus_po_nonpent n hn h1 h2

/--
**PNT (Euler), pentagonal `(3k²-k)/2` case.** If `2n = 3k² - k` for some
`k ≥ 1` (equivalently, `n = (3k²-k)/2`), then
`[X^n] ∏_{k'=1}^{n}(1 - X^{k'}) = (-1)^k`.
-/
theorem coeff_prod_pentagonal_minus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 - k) :
    (coeff n) (∏ k' ∈ Finset.Icc 1 n, (1 - X^k' : ℤ⟦X⟧)) = (-1)^k := by
  rw [coeff_prod_eq_pe_sub_po]; exact pe_minus_po_pent_minus n k hk hn

/--
**PNT (Euler), pentagonal `(3k²+k)/2` case.** If `2n = 3k² + k` for some
`k ≥ 1` (equivalently, `n = (3k²+k)/2`), then
`[X^n] ∏_{k'=1}^{n}(1 - X^{k'}) = (-1)^k`.
-/
theorem coeff_prod_pentagonal_plus (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * n = 3 * k ^ 2 + k) :
    (coeff n) (∏ k' ∈ Finset.Icc 1 n, (1 - X^k' : ℤ⟦X⟧)) = (-1)^k := by
  rw [coeff_prod_eq_pe_sub_po]; exact pe_minus_po_pent_plus n k hk hn

/-- `k * (3 * k - 1)` is always even, so over `ℤ` the generalized pentagonal equation
`n = k(3k-1)/2` is equivalent to its subtraction-free form `2n = k(3k-1)`. -/
lemma natCast_eq_gen_pent_div_two_iff (n : ℕ) (k : ℤ) :
    (n : ℤ) = k * (3 * k - 1) / 2 ↔ 2 * (n : ℤ) = k * (3 * k - 1) := by
  obtain ⟨m, hm⟩ := Int.even_mul_pred_self k
  have : (2 : ℤ) ∣ k * (3 * k - 1) := ⟨3 * m + k, by linear_combination 3 * hm⟩
  omega

/-- **Franklin/Euler in unified integer-index form.** If `2n = k(3k-1)` for some `k : ℤ`,
then `p_e(n) - p_o(n) = (-1)^|k|`. This subsumes the three pentagonal cases:
`k = 0` forces `n = 0`, `k = j > 0` gives `2n = 3j² - j`, and `k = -j < 0` gives
`2n = 3j² + j`. -/
theorem pe_minus_po_of_gen_pent (n : ℕ) (k : ℤ) (hk : 2 * (n : ℤ) = k * (3 * k - 1)) :
    (pe n : ℤ) - po n = (-1 : ℤ) ^ k.natAbs := by
  rcases lt_trichotomy k 0 with h | rfl | h
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = -(j : ℤ) := ⟨k.natAbs, by omega⟩
    rw [show (-(j : ℤ)).natAbs = j by omega]
    refine pe_minus_po_pent_plus n j (by omega) ?_
    exact_mod_cast (by linear_combination hk : (2 * n : ℤ) = 3 * (j : ℤ) ^ 2 + (j : ℤ))
  · rw [show n = 0 by omega]
    simpa using pe_minus_po_zero
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j : ℤ) := ⟨k.natAbs, by omega⟩
    rw [show ((j : ℤ)).natAbs = j by omega]
    refine pe_minus_po_pent_minus n j (by omega) ?_
    have hz : 2 * n + j = 3 * j ^ 2 :=
      mod_cast (by linear_combination hk : (2 * n : ℤ) + (j : ℤ) = 3 * (j : ℤ) ^ 2)
    omega

/-- Converse bookkeeping: both `ℕ`-indexed pentagonal families `2n = 3j² ∓ j` (with `j ≥ 1`)
produce an integer index `k` with `2n = k(3k-1)`, namely `k = j` and `k = -j`. -/
lemma exists_gen_pent_of_pent (n j : ℕ) (hj : 1 ≤ j)
    (h : 2 * n = 3 * j ^ 2 - j ∨ 2 * n = 3 * j ^ 2 + j) :
    ∃ k : ℤ, 2 * (n : ℤ) = k * (3 * k - 1) := by
  have hjle : j ≤ 3 * j ^ 2 := by have := Nat.le_self_pow two_ne_zero j; omega
  rcases h with h | h
  · exact ⟨j, by zify [hjle] at h; linear_combination h⟩
  · exact ⟨-j, by zify at h; linear_combination h⟩

/--
**PNT (Euler), Maryna's unified form.** For every `n`, either `n` is a
generalized pentagonal number `k(3k-1)/2` for some `k ∈ ℤ` — in which case
`p_e(n) - p_o(n) = (-1)^|k|` — or it is not, in which case the difference
vanishes.

This repackages the four cases (`pe_minus_po_zero`, `pe_minus_po_pent_minus`,
`pe_minus_po_pent_plus`, `pe_minus_po_nonpent`) under a single integer index:
`k = 0` gives `n = 0`, `k ≥ 1` gives the `(3k²-k)/2` family, and `k ≤ -1`
(with `m = |k|`) gives the `(3m²+m)/2` family. All the arithmetic lives in
`natCast_eq_gen_pent_div_two_iff`, `pe_minus_po_of_gen_pent` and
`exists_gen_pent_of_pent`; what is left here is pure case bookkeeping.
-/
theorem euler_pentagonal_number_theorem_packaged (n : ℕ) :
  (∃ k : ℤ, (n = (k * (3 * k - 1)) / 2) ∧
  ((pe n : ℤ) - (po n : ℤ) = (-1 : ℤ) ^ (Int.natAbs k) )) ∨
  ((¬ ∃ k : ℤ, n = (k * (3 * k - 1)) / 2 ) ∧
    ((pe n : ℤ) - (po n : ℤ) = 0 )) := by
  have hpent : ∀ j, 1 ≤ j → 2 * n = 3 * j ^ 2 - j ∨ 2 * n = 3 * j ^ 2 + j →
      ∃ k : ℤ, (n : ℤ) = k * (3 * k - 1) / 2 := fun j hj h =>
    (exists_gen_pent_of_pent n j hj h).imp fun k => (natCast_eq_gen_pent_div_two_iff n k).2
  by_cases hP : ∃ k : ℤ, (n : ℤ) = k * (3 * k - 1) / 2
  · obtain ⟨k, hk⟩ := hP
    exact .inl ⟨k, hk, pe_minus_po_of_gen_pent n k ((natCast_eq_gen_pent_div_two_iff n k).1 hk)⟩
  · refine .inr ⟨hP, pe_minus_po_nonpent n ?_ (fun j hj h => hP (hpent j hj (.inl h)))
      (fun j hj h => hP (hpent j hj (.inr h)))⟩
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd ⟨0, by norm_num⟩ hP
    · exact h

end PentagonalNumberTheorem.Franklin
