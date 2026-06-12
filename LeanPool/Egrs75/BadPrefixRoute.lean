/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Egrs75.Defs
import LeanPool.Egrs75.RoundUp
import LeanPool.Egrs75.LeafInduction
import LeanPool.Egrs75.DigitVector
import LeanPool.Egrs75.DigitAtToolkit
import LeanPool.Egrs75.ClearingHigh
import LeanPool.Egrs75.Reduction
import LeanPool.Egrs75.MuFinish
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
EGRS75 two-prime ALIGN leaf — FINISH route (2026-06-08).

════ 2026-06-12 UPDATE: THE RESIDUAL IS CLOSED. ════
`egrs_clearing_low` (the file's single labelled `sorry`, below) is now PROVEN,
discharged by `MuFinish.egrs_clearing_low_mu` (EgrsMuFinish_20260612.lean): the
μ-measure closure — Diophantine seed (EGRS condition (2), Dirichlet) + the
single carry-controlled move under the lex pair (μ, n) with the staircase lemma.
Consequently `egrs_clearing`, `repair_step_lex`, `align_finish`, and
`egrs_two_prime_finish` are now KERNEL-CLEAN (no sorryAx).  The header text
below this note is the original 2026-06-08 state, kept for the record.
════════════════════════════════════════════════════

This file closes the final EGRS75 leaf by REPLACING the badCountQ-monotone interface
of `LeafInduction.align_of_repair` (which is provably FALSE for the EGRS Lemma — its
SUBTRACT branch makes the number smaller and a single move need not drop the bad
COUNT) with the paper's genuine LEXICOGRAPHIC termination measure, encoded as a
single ℕ:

  `badPrefix q n := ∑ i ∈ badIndexSet q n, 2^i`

— the base-`q` "bad-bit" bitmask (bit `i` set iff the base-`q` digit at index `i`
exceeds `(q-1)/2`).  Because bad indices are bounded by `topBadIndex`, clearing the
TOP bad bit (the most-significant set bit, at `j = topBadIndex q n`) WITHOUT
regrowing anything at index `≥ j` strictly lowers this ℕ:  the new value is `< 2^j`
(all its bits are below `j`) while the old value is `≥ 2^j` (bit `j` was set).  This
is faithful to the paper's high→low lexicographic measure on the base-`q` digit
vector (EGRS75, Math. Comp. 29 (1975), pp.84-86, the repair Lemma, case
`A = B = (p-1)/2 = (q-1)/2`).

Because `badPrefix` is a plain ℕ, the existing `Nat.strong_induction_on` engine
(used inside `align_of_repair`) is REUSED verbatim — no custom WellFounded/Prod.Lex
apparatus is needed.  `align_lex` below structurally clones `align_of_repair` with:
  (1) `badPrefix` in place of `badCountQ`,
  (2) the magnitude invariant `N < n'` in place of `n < n'` (the architectural fix —
      the paper's SUBTRACT branch legitimately yields a SMALLER number),
and is KERNEL-CLEAN (it consumes the repair step as an explicit hypothesis).

It feeds the (inlined, kernel-clean) ALIGN ⟹ crux reduction (= `CruxClose.align_imp_crux`
/ `FinalAsm.align_to_crux`, re-proved here to keep the dependency graph minimal and
free of the `Equidist_fromscratch` upstream `sorry`) → `EgrsAll.egrs_two_prime_of_crux`
(clean) to land the EGRS75 two-prime divisibility target, unchanged.

The ONE labelled `sorry` lands on `egrs_clearing_low` — the EGRS75 carry-controlled
clearing in the LOW case `q^j ≤ N` (where `j = topBadIndex q n`), the part that
genuinely needs the condition-(3) base-`q`/base-`p` carry interlock (`q^i < p^m`
clears the top oversized base-`q` digit without regrowing base-`p`).  The
complementary HIGH case `N < q^j` is discharged KERNEL-CLEAN by `Probe.clearing_high`
(a fresh `LowDigits p` window number in `[q^j, 2q^j)` is good at every base-`q` index
`≥ j` and exceeds `N` — no carry control).  `repair_step_lex` / `align_finish` /
`egrs_two_prime_finish` all inherit exactly this single `egrs_clearing_low` `sorryAx`,
reported verbatim — under the CORRECT lex interface so NO false count-drop is hidden
under the sorry.

HONESTY: real verified Lean.  No `native_decide`, no bogus `axiom`, no
`implemented_by`, no circularity.  Reuses the proven base-`p` SAFETY half
(`lowDigits_disjoint_add` / `lowDigits_add_disjoint`) and the proven base-`q`
high/low split (`badCountQ_split`, `highBlock_lowDigits`, `badCount_eq_lowBlock`,
`topBadIndex`/`badIndexSet` machinery) — does NOT reprove them, does NOT modify any
existing clean file.  Formalizes the KNOWN theorem EGRS75 (1975); three primes is
Erdős #376 (OPEN) — not attempted.
-/

namespace Egrs75.Finish

open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.Probe

/-! ## Bridge: `badIndexSet` membership ↔ `BadAt`

`badIndexSet q n` (digitvector) collects the bad base-`q` digit indices via the
`getD`-read digit; `BadAt q i n` (paperfaithful) is `(q-1)/2 < n / q^i % q`.  These
agree for every `i`: out-of-range indices are neither in the set nor `BadAt` (digit
reads as `0`). -/

/-- `i ∈ badIndexSet q n ↔ BadAt q i n`, for all `i` (KERNEL-CLEAN). -/
theorem mem_badIndexSet_iff {q n i : ℕ} (hq : 1 < q) :
    i ∈ badIndexSet q n ↔ BadAt q i n := by
  unfold BadAt digitAt badIndexSet
  simp only [Finset.mem_filter, Finset.mem_range, bigQ, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hbig⟩
    -- in range: getD = n/q^i%q via getD_digits
    rwa [getD_digits n i (by omega)] at hbig
  · intro hbig
    -- bad ⟹ digit nonzero ⟹ index in range
    have hlen : i < (Nat.digits q n).length := by
      by_contra hcon
      push Not at hcon
      rw [← getD_digits n i (by omega), List.getD_eq_default _ 0 hcon] at hbig
      omega
    refine ⟨hlen, ?_⟩
    rwa [getD_digits n i (by omega)]

/-- Above the top bad index, nothing is `BadAt` (KERNEL-CLEAN, from `digit_good_above_top`). -/
theorem not_badAt_above_top {q n i : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n)
    (hi : topBadIndex q n < i) : ¬ BadAt q i n := by
  unfold BadAt digitAt
  have := digit_good_above_top hq hbad hi
  omega

/-! ## The lexicographic measure: the base-`q` bad-bit bitmask

`badPrefix q n = ∑ i ∈ badIndexSet q n, 2^i`.  This is the high→low base-`q`
digit-vector lex measure encoded as a single ℕ: bit `i` is set exactly when the
base-`q` digit at index `i` is oversized.  Its most-significant set bit is at
`topBadIndex q n`. -/

/-- The base-`q` bad-bit bitmask measure (single ℕ encoding of the paper's lex
measure on the high→low base-`q` digit vector). -/
noncomputable def badPrefix (q n : ℕ) : ℕ := ∑ i ∈ badIndexSet q n, 2 ^ i

/-- **Base case (KERNEL-CLEAN).**  `badPrefix q n = 0 ↔ LowDigits q n`.  The bitmask
vanishes iff there are no bad base-`q` digits, i.e. `badIndexSet` is empty, i.e.
`badCountQ q n = 0`, i.e. `LowDigits q n`. -/
theorem badPrefix_eq_zero_iff_lowDigits {q n : ℕ} (hq : 1 < q) :
    badPrefix q n = 0 ↔ LowDigits q n := by
  rw [← badCountQ_eq_zero_iff_lowDigits]
  unfold badPrefix
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h
    -- every term is 0, but 2^i > 0, so the set is empty ⟹ badCountQ = 0
    by_contra hne
    have hpos : 0 < badCountQ q n := Nat.pos_of_ne_zero hne
    obtain ⟨i, hi⟩ := badIndexSet_nonempty hq hpos
    have := h i hi
    exact absurd this (by positivity)
  · intro h0 i hi
    -- badCountQ = 0 ⟹ badIndexSet empty ⟹ no such i
    rw [badCountQ_eq_zero_iff_lowDigits] at h0
    rw [mem_badIndexSet_iff hq] at hi
    -- LowDigits q n contradicts BadAt q i n
    rw [lowDigits_iff_digitAt (by omega)] at h0
    unfold BadAt at hi
    have := h0 i
    omega

/-- The top bad index lies in `badIndexSet` (KERNEL-CLEAN; restated via membership). -/
theorem topBadIndex_mem_set {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    topBadIndex q n ∈ badIndexSet q n :=
  topBadIndex_mem hq hbad

/-- **Lower bound (KERNEL-CLEAN).**  `2 ^ (topBadIndex q n) ≤ badPrefix q n`: the
top bad bit is one of the summands. -/
theorem two_pow_top_le_badPrefix {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    2 ^ (topBadIndex q n) ≤ badPrefix q n := by
  unfold badPrefix
  exact Finset.single_le_sum (f := fun i => 2 ^ i) (fun i _ => Nat.zero_le _)
    (topBadIndex_mem_set hq hbad)

/-! ## The KEY drop lemma (pure-ℕ place-value, KERNEL-CLEAN)

If `n'` has NO bad bit at index `≥ j = topBadIndex q n` (the repair acts at/below `j`
and freezes the already-good high block, `highBlock_lowDigits`), then every bad index
of `n'` is `< j`, so `badPrefix q n' ≤ ∑_{i < j} 2^i < 2^j ≤ badPrefix q n`.  The
strict drop is the bitmask cutoff at `2^j`, exactly the paper's "the top oversized
base-`q` digit is cleared and nothing above regrows" lex decrease. -/

/-- **The lex-measure drop (KERNEL-CLEAN).**  Let `j = topBadIndex q n` (with `n`
having a bad digit).  If `n'` has no bad base-`q` digit at any index `≥ j`, then
`badPrefix q n' < badPrefix q n`.

Proof: all bad indices of `n'` are `< j`, so by `Nat.geomSum_lt`,
`badPrefix q n' = ∑_{i ∈ badIndexSet q n'} 2^i < 2^j`; and `2^j ≤ badPrefix q n`
since `j` is itself a bad index of `n`. -/
theorem badPrefix_drop_of_top_cleared {q n n' : ℕ} (hq : 1 < q)
    (hbad : 0 < badCountQ q n)
    (hcleared : ∀ i, topBadIndex q n ≤ i → ¬ BadAt q i n') :
    badPrefix q n' < badPrefix q n := by
  set j := topBadIndex q n with hj
  -- upper bound on badPrefix q n'
  have hub : badPrefix q n' < 2 ^ j := by
    unfold badPrefix
    apply Nat.geomSum_lt (by omega)
    intro k hk
    -- k ∈ badIndexSet q n' ⟹ BadAt q k n' ⟹ k < j (else cleared)
    rw [mem_badIndexSet_iff hq] at hk
    by_contra hcon
    push Not at hcon
    exact hcleared k hcon hk
  -- lower bound on badPrefix q n
  have hlb : 2 ^ j ≤ badPrefix q n := two_pow_top_le_badPrefix hq hbad
  omega

/-! ## The clean lex induction (structural clone of `align_of_repair`)

`align_lex` clones `LeafInduction.align_of_repair` (EgrsLeaf_induction.lean:179) with
the measure swapped to `badPrefix` and the magnitude invariant `N < n'` replacing
`n < n'`.  KERNEL-CLEAN: it consumes the repair step `hrepair_lex` as an explicit
hypothesis and proves nothing false — pure strong induction on `badPrefix q (running
n)`, base case `badPrefix = 0 ⟹ LowDigits q` (`badPrefix_eq_zero_iff_lowDigits`). -/

/-- **Reduction (FULLY KERNEL-CLEAN).**  The lex repair step is taken as an EXPLICIT
hypothesis `hrepair_lex`.  From a `LowDigits p` seed strictly above `N`, repeatedly
applying it drives the base-`q` bitmask `badPrefix` to `0`, yielding a number that is
`> N`, `LowDigits p`, and `LowDigits q`.  Strong induction on `badPrefix q` of the
running number; the magnitude invariant `N < n` is carried (both repair branches keep
the number above `N`, so it is threaded directly rather than via `n < n'`).

KERNEL-CLEAN (no `sorry`, no axioms beyond propext/Classical.choice/Quot.sound).

The repair hypothesis `hrepair_lex` is given the running magnitude `N < n` (the
induction carries it as an invariant and threads it in), so the EGRS step's `N < n'`
guarantee — needed to keep the result above the floor — is honored at every step. -/
theorem align_lex {p q : ℕ} (N : ℕ)
    (hrepair_lex : ∀ {n : ℕ}, LowDigits p n → N < n → 0 < badCountQ q n →
      ∃ n', LowDigits p n' ∧ N < n' ∧ badPrefix q n' < badPrefix q n)
    (seed : ℕ) (hseedN : N < seed) (hseedp : LowDigits p seed) :
    ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by
  -- Strong induction on the base-`q` bitmask of the running number, carrying the
  -- invariants `N < n` and `LowDigits p n`.
  suffices H : ∀ k, ∀ n, badPrefix q n = k → N < n → LowDigits p n →
      ∃ m, N < m ∧ LowDigits p m ∧ LowDigits q m by
    exact H (badPrefix q seed) seed rfl hseedN hseedp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk hN hpn
    rcases Nat.eq_zero_or_pos (badCountQ q n) with hzero | hpos
    · -- bad count 0 ⟹ already LowDigits q : done with `n` itself
      exact ⟨n, hN, hpn, (badCountQ_eq_zero_iff_lowDigits).mp hzero⟩
    · -- bad count > 0 ⟹ repair once (threading the magnitude `N < n`), recurse on the
      -- strictly smaller bitmask
      obtain ⟨n', hpn', hN', hdrop⟩ := hrepair_lex hpn hN hpos
      have hk' : badPrefix q n' < k := by rw [← hk]; exact hdrop
      exact ih (badPrefix q n') hk' n' rfl hN' hpn'

/-! ## The EGRS75 carry-controlled clearing (THE ONE LABELLED `sorry`)

This is the genuine residual.  Everything above is kernel-clean.  What remains is the
EGRS75 digit-repair Lemma (Math. Comp. 29 (1975), pp.84-86) in the equality case
`A = B = (p-1)/2 = (q-1)/2`, repackaged so its output drives the lex measure:

  given a `LowDigits p` number `n` above the floor `N` with a top oversized base-`q`
  digit at `j = topBadIndex q n`, there is `n'` that is still `LowDigits p`, still
  above `N`, and whose base-`q` digits at every index `≥ j` are good (the top bad
  digit and everything above it are cleared / frozen-good).

By `badPrefix_drop_of_top_cleared` (proven clean above), this clearing forces the
strict lex-measure drop `badPrefix q n' < badPrefix q n` — the FAITHFUL decrease the
paper's high→low lexicographic argument supplies.  So NO false `badCountQ`-count drop
is hidden under the sorry; the sorry is exactly the EGRS construction's existence,
under the correct interface.

THE TWO BRANCHES (EGRS75, pp.84-85), with `T` = the base-`q` tail of `n` below the
clearing index `i` (least good index `> j`), `m` = lowest base-`p` digit index of `n`,
`S = ((p-A-1)/(p-1))(p^m - 1) + 1`:

  • SUBTRACT (mandatory when the base-`p` units digit is nonzero, i.e. `m = 0` ⟹
    `p^m - 1 = 0` ⟹ ADD's condition (3) is impossible): if `T ≥ S` set `N* = N − S`.
    `N*` is `(p,A)`-good, `N* < N`, high base-`q` block frozen
    (`N* ≥ b_r q^r + … + b_i q^i`).  [This is the branch that violates the OLD
    `n < n'` interface — here legitimately allowed, since we only require `N < n'`.]

  • ADD (when `T < S`): condition (3) holds and, in the equality case `A = B`,
    reduces to `q^i < p^m`.  Add `U` with `q^i − T ≤ U ≤ q^i − T + B(q^j − 1)/(q − 1)`,
    drawn `(p,A)`-good with `U < p^m` from the density Fact
    (`RoundUp.exists_lowDigits_between`, ratio `(p-1)/A = 2`).  Then `N* = N + U > N`,
    `b_i* = b_i + 1`, and the bad base-`q` block at/below `j` is cleared.

The base-`p` SAFETY half is ALREADY proven kernel-clean
(`RepairDV.lowDigits_disjoint_add` / `RepairPaperfaithful.lowDigits_add_disjoint`:
adding a disjoint-support `LowDigits p` number creates no large base-`p` digit, the
use of `U < p^m`).  The base-`q` high/low split and the top-bad-index extraction are
ALSO proven clean (`RepairDV.badCountQ_split`, `highBlock_lowDigits`,
`badCount_eq_lowBlock`, `topBadIndex`/`badIndexSet` machinery).  The irreducible
residual is the carry-controlled PLACEMENT — choosing the branch and the correction
so that condition (3) (`q^i < p^m`) makes the base-`q` clearing and the base-`p`
safety hold simultaneously.

Bloom–Croot (arXiv:2509.02835, §1) defer this VERBATIM: "It is not immediately
obvious … that one can remove a large base-`q` digit without creating large base-`p`
digits.  That this is always possible is proved using elementary number theory in
[EGRS75] (and makes essential use of the condition (3))."  The original EGRS75 [4] is
the multi-page elementary argument; Mathlib packages neither it nor the effective
equidistribution an analytic proof would need.  ONE labelled `sorry`. -/

/-- **THE RESIDUAL, ISOLATED TO THE LOW CASE (one labelled `sorry`): the EGRS75
carry-controlled clearing when the top oversized base-`q` index lies *at or below the
floor scale*, `q^j ≤ N`.**

This is the part of the EGRS75 repair Lemma that genuinely needs the base-`q`/base-`p`
carry interlock (condition (3), `q^i < p^m`): the complementary case `N < q^j` is
discharged kernel-clean below (`Probe.clearing_high`, a fresh window number in
`[q^j, 2q^j)` is automatically good at every base-`q` index `≥ j` and exceeds `N`).
When `q^j ≤ N` that free window trick is unavailable — the clearing must act on the
low base-`q` digits without disturbing the already-small base-`p` block, the SUBTRACT
(`N* = N − S`, `S = ((p−A−1)/(p−1))(p^m−1)+1`) / ADD (`N* = N + U`, `U < p^m` via
condition (3)) branches of EGRS75 pp.84-85.  Bloom–Croot (arXiv:2509.02835 §1) defer
exactly this to [EGRS75]; Mathlib packages neither the elementary carry argument nor
the effective equidistribution an analytic proof needs.

Stated in the same lex coordinates as `egrs_clearing` so the drop stays mechanized
(`badPrefix_drop_of_top_cleared`) — no false count-drop is hidden under the sorry. -/
theorem egrs_clearing_low {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) (N : ℕ)
    {n : ℕ} (hpn : LowDigits p n) (hNn : N < n) (hbad : 0 < badCountQ q n)
    (hlow : q ^ (topBadIndex q n) ≤ N) :
    ∃ n', LowDigits p n' ∧ N < n' ∧ (∀ i, topBadIndex q n ≤ i → ¬ BadAt q i n') := by
  -- CLOSED 2026-06-12: discharged by the μ-measure closure (Diophantine seed +
  -- single carry-controlled move + staircase lemma).  KERNEL-CLEAN, no sorry.
  exact MuFinish.egrs_clearing_low_mu hp hq hpo hqo hpq N hpn hNn hbad hlow

/-- **THE EGRS75 carry-controlled clearing.**

For distinct odd primes `p q`, a `LowDigits p` number `n` above floor `N` with a top
oversized base-`q` digit at `j = topBadIndex q n` admits `n'` that is `LowDigits p`,
above `N`, and good at every base-`q` index `≥ j`.  This is the EGRS75 repair Lemma
output (`A = (p-1)/2`, `B = (q-1)/2`, side condition at equality, condition (3)
`≡ q^i < p^m`).

Dispatched on the position of the top oversized index relative to the floor scale:
* `N < q^j` — KERNEL-CLEAN via `Probe.clearing_high` (a `LowDigits p` window number in
  `[q^j, 2q^j)` is good at every base-`q` index `≥ j` and exceeds `N`; no carry control).
* `q^j ≤ N` — `egrs_clearing_low`, which carries the single labelled `sorry` (the
  condition-(3) base-`q`/base-`p` carry interlock).

So `egrs_clearing` inherits EXACTLY the one `egrs_clearing_low` `sorryAx`, now precisely
isolated to the low case.  Stated in the lex coordinates so the drop is mechanized
(`badPrefix_drop_of_top_cleared`) — no false count-drop is hidden. -/
theorem egrs_clearing {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) (N : ℕ)
    {n : ℕ} (hpn : LowDigits p n) (hNn : N < n) (hbad : 0 < badCountQ q n) :
    ∃ n', LowDigits p n' ∧ N < n' ∧ (∀ i, topBadIndex q n ≤ i → ¬ BadAt q i n') := by
  -- Odd primes are ≥ 3.
  have hp3 : 3 ≤ p := by have h2 := hp.two_le; rcases hpo with ⟨k, hk⟩; omega
  have hq3 : 3 ≤ q := by have h2 := hq.two_le; rcases hqo with ⟨k, hk⟩; omega
  rcases lt_or_ge N (q ^ (topBadIndex q n)) with hhigh | hlow
  · -- `N < q^j`: free window number, no carry control needed (KERNEL-CLEAN).
    exact clearing_high hp3 hpo hq3 N hhigh
  · -- `q^j ≤ N`: the genuine EGRS carry-control residual.
    exact egrs_clearing_low hp hq hpo hqo hpq N hpn hNn hbad hlow

/-! ## The lex repair step, assembled (carries EXACTLY the `egrs_clearing_low` `sorry`)

`egrs_clearing` gives the cleared `n'` (clean for `N < q^j` via `Probe.clearing_high`,
carrying the `egrs_clearing_low` `sorry` only for `q^j ≤ N`);
`badPrefix_drop_of_top_cleared` (clean) turns the clearing into the strict lex drop
`badPrefix q n' < badPrefix q n`.  So `repair_step_lex` inherits exactly the one
`egrs_clearing_low` `sorryAx`. -/

/-- **EGRS75 carry-controlled repair step — LEX interface (the architect's NEW step).**
For distinct odd primes `p q`, a `LowDigits p` number `n` above floor `N` with an
oversized base-`q` digit admits a `LowDigits p` number `n'` above `N` with strictly
smaller base-`q` bitmask `badPrefix q n' < badPrefix q n`.

CRITICAL: there is NO `n < n'` clause (the architectural fix — the paper's SUBTRACT
branch legitimately yields `n' < n`); the measure clause is the lex `badPrefix`, NOT
`badCountQ`; and `N < n'` threads the magnitude so the final crux gets `n > N`.
Assembled kernel-clean from the clearing residual `egrs_clearing` via the proven drop
lemma; inherits EXACTLY that one `sorryAx`. -/
theorem repair_step_lex {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) (N : ℕ)
    {n : ℕ} (hpn : LowDigits p n) (hNn : N < n) (hbad : 0 < badCountQ q n) :
    ∃ n', LowDigits p n' ∧ N < n' ∧ badPrefix q n' < badPrefix q n := by
  have hq1 : 1 < q := hq.one_lt
  obtain ⟨n', hpn', hN', hcleared⟩ :=
    egrs_clearing hp hq hpo hqo hpq N hpn hNn hbad
  exact ⟨n', hpn', hN', badPrefix_drop_of_top_cleared hq1 hbad hcleared⟩

/-! ## ALIGN via the lex induction (carries EXACTLY the `egrs_clearing` `sorry`)

Seed `p^(N+1)` (`LowDigits p` for free, `> N`), feed `repair_step_lex` into
`align_lex`.  The running number stays `> N` (carried by `repair_step_lex`'s `N < n'`),
so the magnitude floor is honored throughout and the output is `> N`, `LowDigits p`,
`LowDigits q`. -/

/-- **ALIGN (the target), via the lex measure.**  Statement-identical to
`LeafInduction.align_induction`: for distinct odd primes `p q` and every `N`, there is
`n > N` that is `LowDigits p` and `LowDigits q`.  Obtained by the kernel-clean lex
induction `align_lex` seeded with `p^(N+1)`, discharging `repair_step_lex` (which
carries the single `egrs_clearing` `sorry`).  Inherits EXACTLY that one `sorryAx`. -/
theorem align_finish {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    ∀ N, ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by
  intro N
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le; rcases hpo with ⟨k, hk⟩; omega
  -- The lex induction consumes `repair_step_lex` (with the running magnitude floor `N`,
  -- threaded by `align_lex` as `hNm`).
  refine align_lex N
    (fun {m} hpm hNm hbad => repair_step_lex hp hq hpo hqo hpq N hpm hNm hbad)
    (p ^ (N + 1)) (seed_lt_pow_succ (by omega) N) (seed_lowDigits_pow hp3 (N + 1))

/-! ## Final assembly: ALIGN ⟹ crux ⟹ EGRS75 two-prime divisibility target

`align_to_crux` (inlined `CruxClose.align_imp_crux`, kernel-clean) turns ALIGN into the
crux; `EgrsAll.egrs_two_prime_of_crux` (kernel-clean) turns the crux into the
divisibility target.  Both are clean, so `egrs_two_prime_finish` carries EXACTLY the
single `egrs_clearing` `sorryAx`. -/

/-- ALIGN ⟹ crux (KERNEL-CLEAN; = `CruxClose.align_imp_crux` / `FinalAsm.align_to_crux`,
inlined to avoid the hyphenated-module / `Equidist_fromscratch`-`sorry` import). -/
theorem align_to_crux {p q : ℕ}
    (halign : ∀ N, ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n) :
    {n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hN, hpn, hqn⟩ := halign N
  exact ⟨n, ⟨hpn, hqn⟩, hN⟩

/-- **EGRS75 two-prime theorem — FINISH route.**  For distinct odd primes `p q`, there
are infinitely many `n` with `p ∤ C(2n,n)` and `q ∤ C(2n,n)`.

Assembled through the lex measure: `align_finish` (lex induction, single
`egrs_clearing` `sorry`) → `align_to_crux` (clean) → `egrs_two_prime_of_crux` (clean,
`EgrsAll`).  Inherits EXACTLY the one `egrs_clearing` `sorryAx` — the EGRS75
condition-(3) carry-control residual — under the CORRECT lex interface (no false
count-drop hidden).  No `native_decide`, no extra axioms. -/
theorem egrs_two_prime_finish {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite :=
  egrs_two_prime_of_crux hp hq hpo hqo
    (align_to_crux (align_finish hp hq hpo hqo hpq))

end Egrs75.Finish
