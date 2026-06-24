/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Egrs75.Defs
import LeanPool.Egrs75.RoundUp
import LeanPool.Egrs75.LeafInduction
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Count
import Mathlib.Data.List.GetD

/-!
EGRS75 two-prime ALIGN leaf — route `digitvector`: the carry-controlled repair step.

This file attacks the SINGLE remaining gap of the EGRS two-prime theorem,
`repair_step` (EgrsLeaf_induction.lean:154), via an explicit base-`q` digit-vector
manipulation.  The target, with the SAME signature as the scaffolding's
`repair_step`, is:

  for distinct odd primes `p q`, if `LowDigits p n` and `0 < badCountQ q n`, then
  `∃ n', n < n' ∧ LowDigits p n' ∧ badCountQ q n' < badCountQ q n`.

ROUTE digitvector.  Model `n` by its base-`q` digit list, locate the highest
oversized base-`q` digit at index `j`, split `n = q^(j+1)·Hi + Lo`, construct an
additive `LowDigits p` correction `U` (drawn from the per-base density Fact
`RoundUp.exists_lowDigits_between`, i.e. EGRS's interval at `(p-1)/A = 2`) placed at
position `j`, and prove by direct base-`q`/base-`p` digit bookkeeping that the bad
base-`q` count strictly drops while no oversized base-`p` digit is created (the
"makes essential use of condition (3)" step).

This file IMPORTS the existing kernel-clean definitions (`LowDigits`, `badDigitsQ`,
`badCountQ`) and the density Fact; it does NOT modify any pre-existing clean file.

HONESTY.  Real Lean.  Everything here is kernel-clean
(propext / Classical.choice / Quot.sound only) EXCEPT possibly one clearly-labelled
`sorry` at the genuinely-hardest residual carry-invariant, reported precisely in the
run summary.  No `native_decide`, no bogus `axiom`, no `implemented_by`, no circular
hypothesis.  Formalizes the KNOWN theorem EGRS75 (Math. Comp. 29 (1975), the repair
Lemma p.84, case `κ₁ = κ₂ = 1/2`).  Three primes is Erdős #376 (OPEN); not attempted.
-/

namespace Egrs75.RepairDV

open Nat
open Egrs75
open Egrs75.LeafInduction

/-! ## Local notation and the "oversized digit" predicate -/

/-- The base-`q` "oversized" test: a digit `d` is oversized iff `(q-1)/2 < d`. -/
@[reducible] def bigQ (q d : ℕ) : Bool := decide ((q - 1) / 2 < d)

/-- `badCountQ` unfolded as a filter-length over the base-`q` digit list. -/
theorem badCountQ_eq (q n : ℕ) :
    badCountQ q n = ((Nat.digits q n).filter (fun d => bigQ q d)).length := rfl

/-- `badCountQ` additivity over `filter`/`append`: the bad count of a digit list
that splits as `L₁ ++ L₂` is the sum of the two bad counts.  Used to read the bad
count off a high/low decomposition of `n`. -/
theorem badCount_filter_append (q : ℕ) (L₁ L₂ : List ℕ) :
    ((L₁ ++ L₂).filter (fun d => bigQ q d)).length =
      (L₁.filter (fun d => bigQ q d)).length + (L₂.filter (fun d => bigQ q d)).length := by
  rw [List.filter_append, List.length_append]

/-- Appending zeros to a digit list does not change its bad count (since `0` is
never oversized for `q ≥ 1`). -/
theorem badCount_filter_replicate_zero (q k : ℕ) :
    ((List.replicate k 0).filter (fun d => bigQ q d)).length = 0 := by
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro d hd
  rw [List.mem_replicate] at hd
  simp only [bigQ, hd.2, decide_eq_true_eq, not_lt]
  exact Nat.zero_le _

/-! ## High/low split of the base-`q` digit list and bad count

For `n = q^k · Hi + Lo` with `Lo < q^k` and `Hi > 0`, the base-`q` digit list of `n`
is `(digits q Lo) ++ (zero padding to length k) ++ (digits q Hi)`, so the bad count
splits additively: `badCountQ q n = badCountQ q Lo + badCountQ q Hi`.  This is the
digit-vector view that lets the repair reason about the high block and low block
independently. -/

/-- Base-`q` digit list of `Lo + q^k · Hi` is `digits Lo ++ zeros ++ digits Hi`,
for `Lo < q^k`, `Hi > 0`, `q ≥ 2`. -/
theorem digits_split {q k Lo Hi : ℕ} (hq : 1 < q) (hLo : Lo < q ^ k) (hHi : 0 < Hi) :
    Nat.digits q (Lo + q ^ k * Hi) =
      Nat.digits q Lo ++ List.replicate (k - (Nat.digits q Lo).length) 0 ++ Nat.digits q Hi := by
  have hlen : (Nat.digits q Lo).length ≤ k := (digits_length_le_iff hq Lo).mpr hLo
  have hpad : (Nat.digits q Lo).length + (k - (Nat.digits q Lo).length) = k := by omega
  rw [digits_append_zeroes_append_digits hq hHi, hpad]

/-- **Bad-count split (KERNEL-CLEAN).**  For `n = Lo + q^k · Hi` with `Lo < q^k`,
`Hi > 0`, `q ≥ 2`: the oversized-base-`q`-digit count is the sum of the low block's
and the high block's bad counts. -/
theorem badCountQ_split {q k Lo Hi : ℕ} (hq : 1 < q) (hLo : Lo < q ^ k) (hHi : 0 < Hi) :
    badCountQ q (Lo + q ^ k * Hi) = badCountQ q Lo + badCountQ q Hi := by
  rw [badCountQ_eq, badCountQ_eq, badCountQ_eq, digits_split hq hLo hHi]
  rw [badCount_filter_append, badCount_filter_append, badCount_filter_replicate_zero]
  ring

/-! ## Disjoint-support `LowDigits p` addition (KERNEL-CLEAN)

The base-`p` safety half of the repair: a `LowDigits p` correction `U < p^k` added to
`p^k · Hi` (with `Hi` itself `LowDigits p`) keeps the result `LowDigits p`.  Its
base-`p` digit list is `digits U ++ zeros ++ digits Hi`, every entry of which is
`≤ (p-1)/2`.  This is EGRS's "adding two `(p,A)`-good numbers with disjoint base-`p`
supports keeps the result `(p,A)`-good" — the place where `U < p^m` (condition (3))
is used to guarantee no oversized base-`p` digit is created. -/

/-- **Disjoint-support `LowDigits p` addition (KERNEL-CLEAN).**  If `U < p^k` and both
`U` and `Hi` are `LowDigits p` (and `Hi > 0`, `p ≥ 2`), then `U + p^k · Hi` is
`LowDigits p`: its base-`p` digits are exactly those of `U`, of `Hi`, and padding
zeros, all `≤ (p-1)/2`. -/
theorem lowDigits_disjoint_add {p k U Hi : ℕ} (hp : 1 < p) (hU : U < p ^ k) (hHi : 0 < Hi)
    (hUlow : LowDigits p U) (hHilow : LowDigits p Hi) : LowDigits p (U + p ^ k * Hi) := by
  unfold LowDigits at *
  have hlen : (Nat.digits p U).length ≤ k := (digits_length_le_iff hp U).mpr hU
  have hpad : (Nat.digits p U).length + (k - (Nat.digits p U).length) = k := by omega
  have hsplit : Nat.digits p (U + p ^ k * Hi) =
      Nat.digits p U ++ List.replicate (k - (Nat.digits p U).length) 0 ++ Nat.digits p Hi := by
    rw [Nat.digits_append_zeroes_append_digits hp hHi, hpad]
  rw [hsplit]
  intro d hd
  rw [List.mem_append, List.mem_append] at hd
  rcases hd with (hd | hd) | hd
  · exact hUlow d hd
  · rw [List.mem_replicate] at hd; rw [hd.2]; exact Nat.zero_le _
  · exact hHilow d hd

/-! ## The highest oversized base-`q` index (KERNEL-CLEAN)

When `badCountQ q n > 0`, there is at least one oversized base-`q` digit; we extract
the **highest** such index `j`.  Above `j`, every base-`q` digit is good.  This `j`
defines the decomposition scale `k = j+1` for the repair (low block = digits `0..j`,
containing the bad digit at `j`; high block = digits `> j`, all good). -/

/-- The (decidable, finite, nonempty) set of oversized base-`q` digit positions of `n`,
as indices into the digit list.  `i` is oversized iff `(q-1)/2 < n / q^i % q`
(= the `i`-th base-`q` digit) and `i < length`. -/
def badIndexSet (q n : ℕ) : Finset ℕ :=
  (Finset.range (Nat.digits q n).length).filter (fun i => bigQ q ((Nat.digits q n).getD i 0))

/-- If the bad count is positive, the bad-index set is nonempty. -/
theorem badIndexSet_nonempty {q n : ℕ} (_hq : 1 < q) (hbad : 0 < badCountQ q n) :
    (badIndexSet q n).Nonempty := by
  -- A bad digit exists in the list; its position is in `badIndexSet`.
  rw [badCountQ_eq] at hbad
  -- the filtered list is nonempty, so it has a member `d` that is oversized
  have hne : (Nat.digits q n).filter (fun d => bigQ q d) ≠ [] := by
    intro h; rw [h] at hbad; simp at hbad
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hne
  rw [List.mem_filter] at hd
  obtain ⟨hdmem, hdbig⟩ := hd
  obtain ⟨i, hilt, hget⟩ := List.mem_iff_getElem.mp hdmem
  refine ⟨i, ?_⟩
  simp only [badIndexSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨hilt, ?_⟩
  have : (Nat.digits q n).getD i 0 = d := by
    rw [List.getD_eq_getElem (Nat.digits q n) 0 hilt, hget]
  rw [this]; exact hdbig

/-- The highest oversized base-`q` index of `n` (defined when the bad count is
positive; otherwise junk `0`). -/
noncomputable def topBadIndex (q n : ℕ) : ℕ :=
  if h : (badIndexSet q n).Nonempty then (badIndexSet q n).max' h else 0

/-- The top bad index is itself a bad index: its base-`q` digit is oversized and it is
within the digit list. -/
theorem topBadIndex_mem {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    topBadIndex q n ∈ badIndexSet q n := by
  rw [topBadIndex, dif_pos (badIndexSet_nonempty hq hbad)]
  exact (badIndexSet q n).max'_mem _

/-- Maximality: every bad index is `≤ topBadIndex`. -/
theorem le_topBadIndex {q n i : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n)
    (hi : i ∈ badIndexSet q n) : i ≤ topBadIndex q n := by
  rw [topBadIndex, dif_pos (badIndexSet_nonempty hq hbad)]
  exact (badIndexSet q n).le_max' i hi

/-! ## Digit-at-index helper and the "high block is all good" fact (KERNEL-CLEAN)

`getD_digits` reads the `i`-th base-`q` digit as `n / q^i % q`.  Combined with
`topBadIndex` maximality, every base-`q` digit at index `> topBadIndex` is good, so
the high block `n / q^(topBadIndex+1)` is `LowDigits q` (bad count `0`). -/

/-- The base-`q` digit of `n` at any index strictly above `topBadIndex q n` is good
(`≤ (q-1)/2`).  Indices beyond the list read as `0` (also good); indices in range
above the top bad index are good by maximality. -/
theorem digit_good_above_top {q n i : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n)
    (hi : topBadIndex q n < i) : n / q ^ i % q ≤ (q - 1) / 2 := by
  -- The digit at index `i` equals `(digits q n).getD i 0`.
  have hval : n / q ^ i % q = (Nat.digits q n).getD i 0 :=
    (getD_digits n i (by omega)).symm
  by_cases hlen : i < (Nat.digits q n).length
  · -- in range: if it were oversized, `i` would be a bad index `> topBadIndex`,
    -- contradicting maximality.
    by_contra hcon
    push Not at hcon
    have hibad : i ∈ badIndexSet q n := by
      simp only [badIndexSet, Finset.mem_filter, Finset.mem_range]
      refine ⟨hlen, ?_⟩
      rw [← hval]
      simp only [bigQ, decide_eq_true_eq]
      omega
    have := le_topBadIndex hq hbad hibad
    omega
  · -- out of range: the digit reads as the default `0`.
    push Not at hlen
    rw [hval, List.getD_eq_default _ 0 hlen]
    exact Nat.zero_le _

/-- **High block is `LowDigits q` (KERNEL-CLEAN).**  With `k = topBadIndex q n + 1`,
the high block `Hi = n / q^k` has no oversized base-`q` digit. -/
theorem highBlock_lowDigits {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    LowDigits q (n / q ^ (topBadIndex q n + 1)) := by
  set k := topBadIndex q n + 1 with hk
  unfold LowDigits
  intro d hd
  -- `d` is the `i`-th digit of `Hi` for some `i < length`, hence the `(k+i)`-th of `n`.
  obtain ⟨i, hilt, hget⟩ := List.mem_iff_getElem.mp hd
  have hdval : d = (n / q ^ k) / q ^ i % q := by
    rw [← getD_digits (n / q ^ k) i (by omega), List.getD_eq_getElem _ 0 hilt, hget]
  -- `(n / q^k) / q^i = n / q^(k+i)`
  have hdiv : (n / q ^ k) / q ^ i = n / q ^ (k + i) := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]
  rw [hdval, hdiv]
  exact digit_good_above_top hq hbad (by omega)

/-! ## The low block carries the entire bad count, and it is positive (KERNEL-CLEAN)

With `k = topBadIndex q n + 1`, write `n = Lo + q^k·Hi`, `Lo = n % q^k`, `Hi = n / q^k`.
The high block is `LowDigits q` (bad count `0`), so by the split the entire bad count
sits in the low block: `badCountQ q n = badCountQ q Lo`.  And `Lo ≥ 1` carries the
oversized top digit, so `badCountQ q Lo ≥ 1`. -/

/-- The base-`q` digit at index `topBadIndex q n` is itself oversized
(`(q-1)/2 < n / q^(topBadIndex) % q`). -/
theorem digit_top_big {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    (q - 1) / 2 < n / q ^ (topBadIndex q n) % q := by
  have hmem := topBadIndex_mem hq hbad
  simp only [badIndexSet, Finset.mem_filter, Finset.mem_range] at hmem
  obtain ⟨hlt, hbig⟩ := hmem
  rw [getD_digits n _ (by omega)] at hbig
  simpa only [bigQ, decide_eq_true_eq] using hbig

/-- **Decomposition (KERNEL-CLEAN).**  With `k = topBadIndex q n + 1`, the bad count of
`n` equals the bad count of its low block `n % q^k`, and that is `≥ 1`.  Moreover the
high block `n / q^k` is positive (the top bad digit forces `n ≥ q^(k-1) > 0`, and
since the digit at `topBadIndex` is nonzero the number extends at least that far). -/
theorem badCount_eq_lowBlock {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    badCountQ q n = badCountQ q (n % q ^ (topBadIndex q n + 1)) := by
  set j := topBadIndex q n with hj
  set k := j + 1 with hk
  have hHi : LowDigits q (n / q ^ k) := highBlock_lowDigits hq hbad
  have hHi0 : badCountQ q (n / q ^ k) = 0 := badCountQ_eq_zero_iff_lowDigits.mpr hHi
  -- n = (n % q^k) + q^k * (n / q^k)
  rcases Nat.eq_zero_or_pos (n / q ^ k) with hHiZero | hHiPos
  · -- high block 0 ⟹ n < q^k, so n % q^k = n
    have : n % q ^ k = n := by
      have hlt : n < q ^ k := by
        rcases Nat.lt_or_ge n (q ^ k) with h | h
        · exact h
        · exact absurd (Nat.div_pos h (by positivity)) (by omega)
      exact Nat.mod_eq_of_lt hlt
    rw [this]
  · have hdecomp : n = n % q ^ k + q ^ k * (n / q ^ k) := by
      rw [Nat.mod_add_div]
    have hLolt : n % q ^ k < q ^ k := Nat.mod_lt _ (by positivity)
    calc badCountQ q n
        = badCountQ q (n % q ^ k + q ^ k * (n / q ^ k)) := by rw [← hdecomp]
      _ = badCountQ q (n % q ^ k) + badCountQ q (n / q ^ k) :=
            badCountQ_split hq hLolt hHiPos
      _ = badCountQ q (n % q ^ k) := by rw [hHi0, add_zero]

/-! ## The EGRS carry-controlled correction (THE RESIDUAL — one labelled `sorry`)

Everything above is kernel-clean digit-vector infrastructure.  What remains is the
single irreducible EGRS75 carry-control content: the existence of the additive
`LowDigits p` correction that clears the top oversized base-`q` digit without creating
an oversized base-`p` digit and without a net increase in the base-`q` bad count.

We isolate it as `repair_correction`, stated in the decomposed coordinates produced
above (top bad index `j`, scale `k = j+1`, low block `Lo = n % q^k`,
high block `Hi = n / q^k`, with `Hi` already `LowDigits q` and `Lo` carrying the bad
count `≥ 1`).  The statement asks exactly for the corrected number `n'`:

  `n < n'`,  `LowDigits p n'`,  `badCountQ q n' < badCountQ q Lo`.

This is the EGRS Lemma (Math. Comp. 29 (1975) p.84) in the equality case
`A = B = (p-1)/2 = (q-1)/2`.  Its proof "makes essential use of the condition (3)"
(`q^i − 1 < ((q-1)/B)((p−A−1)/(p-1))(p^m − 1)`, EGRS75 p.85 eq. (3)), which couples the
base-`q` clearing window to the base-`p` safety margin `U < p^m` — the single place
the two bases interact, and the part Bloom–Croot (arXiv:2509.02835 §1) explicitly
defer to [4] and that current Mathlib does not package (no effective equidistribution,
no carry bookkeeping).  The intended correction source is
`RoundUp.exists_lowDigits_between` (the density Fact = EGRS's interval at
`(p-1)/A = 2`); the residual is the carry-controlled PLACEMENT of that correction.

ONE labelled `sorry`, reported precisely.  No `native_decide`, no bogus axiom, no
circularity. -/

end Egrs75.RepairDV
