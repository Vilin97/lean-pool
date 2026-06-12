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
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Intervals

/-!
EGRS75 LOW-case clearing — PRIMITIVE P4: condition-(3) window producer (2026-06-08).

This file builds the EGRS75 "condition (3)" producer for the ADD branch of the
LOW-case repair (`Finish.egrs_clearing_low`, EgrsFinish_core.lean:301).  NEW file; does
NOT modify any existing clean file and reuses the proven base-`q` digit machinery.

THE MATH (EGRS75, Math. Comp. 29 (1975), pp.84-85, the Lemma; equality case
`A = (p-1)/2`, `B = (q-1)/2`).  Write `n` in base `q`; let `j = topBadIndex q n` be the
largest index whose base-`q` digit exceeds `B` (the top oversized digit), and let `i` be
the LEAST index `> j` whose base-`q` digit is `< B` (strictly good).  By maximality of `j`
and minimality of `i`, every digit at an index `k` with `j < k < i` equals exactly `B`.
Let `T = n % q^i` (the paper's "tail" of `N` = digits below `i`) and
`S = ((p-A-1)/(p-1))(p^m - 1) + 1`, which in the equality case is `S = (p^m + 1)/2`,
`m = lowest nonzero base-`p` digit index.

The paper's ADD branch fires when `T < S`.  The tail then satisfies the lower bound
`T ≥ B·(q^i - 1)/(q - 1) + 1`.  Combining `B·(q^i-1)/(q-1) + 1 ≤ T < S = (p^m+1)/2` and
`B = (q-1)/2` (so `B·(q^i-1)/(q-1) = (q^i-1)/2`) yields condition (3) in equality form:

      q^i < p^m.

This is the carry-interlock the ADD branch (P2) consumes: it guarantees the EGRS density
`Fact` (`RoundUp.exists_lowDigits_between`) draws `U ∈ [q^i - T, p^m)` `LowDigits p`,
`< p^m`, so adding it clears the top oversized base-`q` digit WITHOUT creating a large
base-`p` digit (base-`p` SAFETY half `RepairDV.lowDigits_disjoint_add`, kernel-clean).

The paper clause is literally "from `T < S` AND `T ≥ B(q^i-1)/(q-1)+1` derive (3)".  This
file delivers, KERNEL-CLEAN:
  • the place-value GOLDEN identity `q^i = (q-1)·G i + 1`, `G i = ∑_{k<i} q^k`,
  • the EXISTENCE+minimality of the least strictly-good index `i > j` (`Nat.find`),
  • the middle-digits-are-`B` structural fact (`digit_good_above_top` + minimality),
  • the ALGEBRAIC INTERLOCK `cond3_of_tail_small` turning `B·G i + 1 ≤ T < S` into
    `q^i < p^m`, and
  • `cond3_window`, the assembled producer: from `T < S` it extracts `i`, proves it is a
    valid clearing index (strictly good, `> j`) and `q^i < p^m`, consuming the tail lower
    bound `tail_ge` as the one structural input (see its docstring).

HONESTY: real verified Lean.  No `native_decide`, no bogus `axiom`, no circularity.
Reuses (does not reprove) the imported base-`q` digit machinery.  Formalizes the KNOWN
theorem EGRS75 (1975).  Three primes is Erdős #376 (OPEN) — not attempted.
-/

namespace Egrs75.P4

open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful

/-! ## The base-`q` geometric sum and the GOLDEN place-value identity -/

/-- The base-`q` geometric sum `G q i = 1 + q + … + q^(i-1)`. -/
def geomQ (q i : ℕ) : ℕ := ∑ k ∈ Finset.range i, q ^ k

/-- **GOLDEN identity (KERNEL-CLEAN).**  `(q-1)·G q i + 1 = q^i` for `q ≥ 1`.
Division- and subtraction-free form of `G q i = (q^i - 1)/(q - 1)`, from `geom_sum_mul_add`
at `x = q-1` (`(q-1)+1 = q`). -/
theorem geomQ_golden {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    (q - 1) * geomQ q i + 1 = q ^ i := by
  unfold geomQ
  have hx : (q - 1) + 1 = q := by omega
  have h := geom_sum_mul_add (q - 1) i
  rw [hx] at h
  rw [mul_comm]; exact h

/-- `(q-1)·G q i = q^i - 1` (KERNEL-CLEAN corollary). -/
theorem geomQ_mul {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    (q - 1) * geomQ q i = q ^ i - 1 := by
  have := geomQ_golden hq i; omega

/-- `G q (i+1) = G q i + q^i` (KERNEL-CLEAN). -/
theorem geomQ_succ (q i : ℕ) : geomQ q (i + 1) = geomQ q i + q ^ i := by
  unfold geomQ; rw [Finset.sum_range_succ]

/-- `1 ≤ G q i` for `i ≥ 1` (the `k=0` term is `1`; KERNEL-CLEAN). -/
theorem one_le_geomQ {q i : ℕ} (hi : 1 ≤ i) : 1 ≤ geomQ q i := by
  unfold geomQ
  have h0 : (0 : ℕ) ∈ Finset.range i := Finset.mem_range.mpr (by omega)
  calc (1 : ℕ) = q ^ 0 := by rw [pow_zero]
    _ ≤ ∑ k ∈ Finset.range i, q ^ k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0

/-! ## The ALGEBRAIC INTERLOCK (KERNEL-CLEAN): `B·G i + 1 ≤ T < S ⟹ q^i < p^m`

This is the load-bearing condition-(3) derivation.  With `B = (q-1)/2`, `q` odd, the tail
lower bound `B·G i + 1 ≤ T` and the ADD condition `T < S = (p^m+1)/2` combine via the
golden identity `(q-1)·G i = q^i - 1` to force `q^i < p^m`.  Pure ℕ arithmetic. -/

/-- **CONDITION (3), algebraic form (KERNEL-CLEAN).**  For odd `p, q ≥ 3`, given the EGRS
tail squeeze in the equality case `A = (p-1)/2`, `B = (q-1)/2`:

  * `hlo : (q-1)/2 * geomQ q i + 1 ≤ T`   (paper: `T ≥ B(q^i-1)/(q-1) + 1`), and
  * `hTS : T < (p^m + 1)/2`               (paper: `T < S`, equality case `S = (p^m+1)/2`),

condition (3) reduces to `q^i < p^m`.

Proof.  `p, q` odd ⟹ `2·((q-1)/2) = q-1` and `2·((p^m+1)/2) = p^m+1`.  From `hTS`,
`2T < p^m + 1`, so `2T ≤ p^m`.  From `hlo`, `2·((q-1)/2·G i + 1) ≤ 2T`, i.e.
`(q-1)·G i + 2 ≤ 2T ≤ p^m`.  The golden identity `(q-1)·G i = q^i - 1` then gives
`(q^i - 1) + 2 ≤ p^m`, i.e. `q^i + 1 ≤ p^m`, hence `q^i < p^m`. -/
theorem cond3_of_tail_small {p q : ℕ} (hq : 3 ≤ q)
    (hpo : Odd p) (hqo : Odd q) (m i T : ℕ)
    (hlo : (q - 1) / 2 * geomQ q i + 1 ≤ T)
    (hTS : T < (p ^ m + 1) / 2) :
    q ^ i < p ^ m := by
  -- `q` odd ⟹ `q - 1` even ⟹ `2·((q-1)/2) = q - 1`.
  have hqhalf : 2 * ((q - 1) / 2) = q - 1 := by
    obtain ⟨a, ha⟩ := hqo; subst ha
    have : 2 * a + 1 - 1 = 2 * a := by omega
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  -- `p^m` odd ⟹ `p^m + 1` even ⟹ `2·((p^m+1)/2) = p^m + 1`.
  have hpodd : Odd (p ^ m) := hpo.pow
  have hph : 2 * ((p ^ m + 1) / 2) = p ^ m + 1 := by
    obtain ⟨a, ha⟩ := hpodd; rw [ha]
    have : 2 * a + 1 + 1 = 2 * (a + 1) := by omega
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  -- golden: `(q-1)·G i = q^i - 1`, and `1 ≤ q^i`.
  have hgolden : (q - 1) * geomQ q i = q ^ i - 1 := geomQ_mul (by omega) i
  have hqipos : 1 ≤ q ^ i := Nat.one_le_pow _ _ (by omega)
  -- `2T < p^m + 1` ⟹ `2T ≤ p^m`.
  have h2T : 2 * T < p ^ m + 1 := by
    calc 2 * T < 2 * ((p ^ m + 1) / 2) := by omega
      _ = p ^ m + 1 := hph
  -- `2·((q-1)/2·G i + 1) ≤ 2T`.
  have h2lo : (q - 1) * geomQ q i + 2 ≤ 2 * T := by
    have : 2 * ((q - 1) / 2 * geomQ q i + 1) ≤ 2 * T := by omega
    calc (q - 1) * geomQ q i + 2
        = 2 * ((q - 1) / 2) * geomQ q i + 2 := by rw [hqhalf]
      _ = 2 * ((q - 1) / 2 * geomQ q i + 1) := by ring
      _ ≤ 2 * T := this
  -- chain: `(q^i - 1) + 2 ≤ 2T ≤ p^m` ⟹ `q^i + 1 ≤ p^m`.
  rw [hgolden] at h2lo
  omega

/-! ## The least strictly-good base-`q` index above the top bad index (KERNEL-CLEAN)

`leastGoodAbove q n` is the least index `i > j = topBadIndex q n` whose base-`q` digit is
`< B = (q-1)/2` (STRICTLY good).  It exists because base-`q` digits eventually vanish (out
of range they read `0 < B` for `q ≥ 3`).  We expose it via `Nat.find`, supplying the
existence proof. -/

/-- The strictly-good base-`q` digit predicate at index `i`: `n / q^i % q < (q-1)/2`. -/
def StrictGoodAt (q i n : ℕ) : Prop := n / q ^ i % q < (q - 1) / 2

instance (q i n : ℕ) : Decidable (StrictGoodAt q i n) := by
  unfold StrictGoodAt; infer_instance

/-- There is a strictly-good index above `j = topBadIndex q n` (KERNEL-CLEAN): for any
`i ≥ length` the digit reads `0`, and `0 < (q-1)/2` since `q ≥ 3`. -/
theorem exists_strictGood_above {q n : ℕ} (hq : 3 ≤ q) (_hbad : 0 < badCountQ q n) :
    ∃ i, topBadIndex q n < i ∧ StrictGoodAt q i n := by
  set j := topBadIndex q n with hj
  set L := (Nat.digits q n).length with hL
  refine ⟨max (j + 1) L, by omega, ?_⟩
  unfold StrictGoodAt
  set i := max (j + 1) L with hi
  have hge : L ≤ i := by omega
  -- n / q^i = 0 since q^i ≥ q^L > n
  have hqL : n < q ^ L := Nat.lt_base_pow_length_digits (by omega)
  have hqi : n < q ^ i := lt_of_lt_of_le hqL (Nat.pow_le_pow_right (by omega) hge)
  have hd0 : n / q ^ i = 0 := Nat.div_eq_of_lt hqi
  rw [hd0]; simp only [Nat.zero_mod]
  omega

/-- `leastGoodAbove q n`: the least strictly-good base-`q` index `> topBadIndex q n`,
defined for `q ≥ 3` and a positive bad count.  Carries the existence witness. -/
noncomputable def leastGoodAbove {q n : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n) : ℕ :=
  Nat.find (exists_strictGood_above hq hbad)

/-- `leastGoodAbove` lies strictly above the top bad index (KERNEL-CLEAN). -/
theorem topBad_lt_leastGoodAbove {q n : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n) :
    topBadIndex q n < leastGoodAbove hq hbad :=
  (Nat.find_spec (exists_strictGood_above hq hbad)).1

/-- `leastGoodAbove` is strictly good (KERNEL-CLEAN). -/
theorem strictGoodAt_leastGoodAbove {q n : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n) :
    StrictGoodAt q (leastGoodAbove hq hbad) n :=
  (Nat.find_spec (exists_strictGood_above hq hbad)).2

/-- **Minimality (KERNEL-CLEAN).**  No index strictly between `j` and `leastGoodAbove` is
strictly good: any `k` with `j < k < leastGoodAbove` has `(q-1)/2 < n / q^k % q` — wait,
this is `¬ StrictGoodAt`, i.e. the digit is `≥ B`.  Combined with `digit_good_above_top`
(`≤ B`) this pins the middle digits to exactly `B`. -/
theorem not_strictGood_of_lt_leastGoodAbove {q n k : ℕ} (hq : 3 ≤ q)
    (hbad : 0 < badCountQ q n) (hjk : topBadIndex q n < k)
    (hk : k < leastGoodAbove hq hbad) : ¬ StrictGoodAt q k n := by
  intro hcon
  -- `k` is strictly good and `> j`, so it is a witness for the `Nat.find` predicate,
  -- contradicting minimality of `leastGoodAbove`.
  exact Nat.find_min (exists_strictGood_above hq hbad) hk ⟨hjk, hcon⟩

/-- **Middle digits are exactly `B` (KERNEL-CLEAN).**  For `j < k < i = leastGoodAbove`,
the base-`q` digit of `n` at index `k` equals `(q-1)/2`.  (`digit_good_above_top` gives
`≤ B`; non-strict-goodness gives `≥ B`.) -/
theorem middle_digit_eq {q n k : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n)
    (hjk : topBadIndex q n < k) (hk : k < leastGoodAbove hq hbad) :
    n / q ^ k % q = (q - 1) / 2 := by
  have hle : n / q ^ k % q ≤ (q - 1) / 2 := digit_good_above_top (by omega) hbad hjk
  have hge : ¬ (n / q ^ k % q < (q - 1) / 2) :=
    not_strictGood_of_lt_leastGoodAbove hq hbad hjk hk
  omega

/-! ## The TAIL LOWER BOUND (the genuine base-`q` digit bookkeeping, KERNEL-CLEAN)

`T = n % q^i ≥ B·G i + 1`.  The digits of `n` at indices `j .. i-1` are `b_j ≥ B+1`
(the top oversized digit) and `B, …, B` (the middle digits, `middle_digit_eq`).  Dropping
the digits below `j`, the tail is `≥ b_j·q^j + B(q^{j+1} + … + q^{i-1})`, which (using
`b_j ≥ B+1` and the golden identity) is `≥ B·G i + 1`.

We prove it by a clean upward induction on the cutoff `t` from `j+1` to `i`, telescoping
the partial lower bound `LB t := b_j·q^j + B·(q^{j+1} + … + q^{t-1})` via the base-`q`
mod-recursion `n % q^{t+1} = n % q^t + q^t·(n/q^t % q)`. -/

/-- Base-`q` mod-recursion (KERNEL-CLEAN): `n % q^{t+1} = n % q^t + q^t·(n / q^t % q)`. -/
theorem mod_pow_succ (n q t : ℕ) :
    n % q ^ (t + 1) = n % q ^ t + q ^ t * (n / q ^ t % q) := by
  conv_lhs => rw [pow_succ]
  rw [Nat.mod_mul]

/-- The partial tail lower bound `LB q n j t = b_j·q^j + B·(q^{j+1} + … + q^{t-1})`,
expressed as `(n/q^j%q)·q^j + B·∑_{j < s < t} q^s`.  (Only used internally.) -/
private def tailLB (q n j t : ℕ) : ℕ :=
  (n / q ^ j % q) * q ^ j + ((q - 1) / 2) * ∑ s ∈ Finset.Ico (j + 1) t, q ^ s

/-- **Inductive tail bound (KERNEL-CLEAN).**  For `j = topBadIndex q n`, `i = leastGoodAbove`,
and any `t` with `j < t ≤ i`: `tailLB q n j t ≤ n % q^t`.  The middle digits being exactly
`B` (`middle_digit_eq`) feed the inductive step. -/
theorem tailLB_le_mod {q n : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n)
    {t : ℕ} (htlo : topBadIndex q n < t) (hthi : t ≤ leastGoodAbove hq hbad) :
    tailLB q n (topBadIndex q n) t ≤ n % q ^ t := by
  set j := topBadIndex q n with hj
  -- induct on `t` from `j+1`.  Reformulate as: ∀ d, j+1+d ≤ i → tailLB (j+1+d) ≤ mod.
  obtain ⟨d, rfl⟩ : ∃ d, t = j + 1 + d := ⟨t - (j + 1), by omega⟩
  clear htlo
  induction d with
  | zero =>
    -- base: t = j+1.  tailLB = b_j·q^j (empty Ico sum); n % q^{j+1} ≥ q^j·b_j.
    simp only [tailLB, Nat.add_zero]
    have hIco : Finset.Ico (j + 1) (j + 1) = (∅ : Finset ℕ) := by simp
    rw [hIco, Finset.sum_empty, Nat.mul_zero, Nat.add_zero]
    rw [mod_pow_succ n q j, Nat.mul_comm (q ^ j) (n / q ^ j % q)]
    exact Nat.le_add_left _ _
  | succ d ih =>
    -- step: t = j+1+(d+1).  Need j+1+d < i to apply middle_digit_eq at index j+1+d.
    have hstep_hi : j + 1 + d ≤ leastGoodAbove hq hbad := by omega
    have hstep_lt : j + 1 + d < leastGoodAbove hq hbad := by omega
    have ih' := ih (by omega)
    -- middle digit at index (j+1+d) is exactly B:
    have hmid : n / q ^ (j + 1 + d) % q = (q - 1) / 2 :=
      middle_digit_eq hq hbad (by omega) hstep_lt
    -- tailLB at t+1 = tailLB at t + B·q^(j+1+d)
    have htail_succ : tailLB q n j (j + 1 + (d + 1))
        = tailLB q n j (j + 1 + d) + ((q - 1) / 2) * q ^ (j + 1 + d) := by
      simp only [tailLB]
      rw [show j + 1 + (d + 1) = (j + 1 + d) + 1 by omega,
          Finset.sum_Ico_succ_top (by omega : j + 1 ≤ j + 1 + d) (fun s => q ^ s)]
      ring
    -- mod at t+1 = mod at t + q^(j+1+d)·B
    have hmod_succ : n % q ^ (j + 1 + (d + 1))
        = n % q ^ (j + 1 + d) + q ^ (j + 1 + d) * ((q - 1) / 2) := by
      rw [show j + 1 + (d + 1) = (j + 1 + d) + 1 by omega, mod_pow_succ n q (j + 1 + d), hmid]
    rw [htail_succ, hmod_succ]
    have hcomm : ((q - 1) / 2) * q ^ (j + 1 + d) = q ^ (j + 1 + d) * ((q - 1) / 2) := by
      rw [Nat.mul_comm]
    omega

/-- **THE TAIL LOWER BOUND (KERNEL-CLEAN).**  `(q-1)/2 · G q i + 1 ≤ n % q^i`, where
`i = leastGoodAbove`.  Assembles `tailLB_le_mod` (at `t = i`) with `b_j ≥ B+1` and the
golden identity: `tailLB q n j i = b_j q^j + B(q^{j+1}+…+q^{i-1}) ≥ B·G i + 1`. -/
theorem tail_ge {q n : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n) :
    (q - 1) / 2 * geomQ q (leastGoodAbove hq hbad) + 1 ≤ n % q ^ (leastGoodAbove hq hbad) := by
  -- Abbreviations as plain `let`-free locals (avoid `set` aliasing of `q^j`).
  obtain ⟨j, hjdef⟩ : ∃ j, j = topBadIndex q n := ⟨_, rfl⟩
  obtain ⟨i, hidef⟩ : ∃ i, i = leastGoodAbove hq hbad := ⟨_, rfl⟩
  rw [← hidef]
  have hji : j < i := by rw [hjdef, hidef]; exact topBad_lt_leastGoodAbove hq hbad
  -- top digit b_j ≥ B+1 (oversized)
  have hbj : (q - 1) / 2 < n / q ^ j % q := by rw [hjdef]; exact digit_top_big (by omega) hbad
  -- tailLB i ≤ n % q^i
  have hlb : tailLB q n j i ≤ n % q ^ i := by
    rw [hjdef]; exact tailLB_le_mod hq hbad (t := i) (by rw [← hjdef]; omega) (by rw [hidef])
  -- value of tailLB: with SumMid = ∑_{j+1 ≤ s < i} q^s,
  --   tailLB q n j i = (n/q^j%q)·q^j + B·SumMid.
  set SumMid := ∑ s ∈ Finset.Ico (j + 1) i, q ^ s with hSM
  have htailval : tailLB q n j i = (n / q ^ j % q) * q ^ j + ((q - 1) / 2) * SumMid := by
    simp only [tailLB, ← hSM]
  -- geom split: geomQ q i = geomQ q j + q^j + SumMid.
  have hGsplit : geomQ q i = geomQ q j + q ^ j + SumMid := by
    have h1 : geomQ q i = geomQ q (j + 1) + SumMid := by
      unfold geomQ; rw [hSM, ← Finset.sum_range_add_sum_Ico _ (by omega : j + 1 ≤ i)]
    rw [h1, geomQ_succ q j]
  -- abbreviate the load-bearing products and bound them.
  set B := (q - 1) / 2 with hB
  set Gj := geomQ q j with hGjdef
  set P := q ^ j with hP
  set bj := n / q ^ j % q with hbjdef
  -- 2·(B·Gj) ≤ P - 1 (golden + 2B ≤ q-1), and P ≥ 1, so B·Gj + 1 ≤ P.
  have h2B : 2 * B ≤ q - 1 := by rw [hB]; omega
  have hgolden : (q - 1) * Gj = P - 1 := by rw [hGjdef, hP]; exact geomQ_mul (by omega) j
  have hPpos : 1 ≤ P := by rw [hP]; exact Nat.one_le_pow _ _ (by omega)
  have h2BGj : 2 * (B * Gj) ≤ P - 1 := by
    calc 2 * (B * Gj) = (2 * B) * Gj := by ring
      _ ≤ (q - 1) * Gj := Nat.mul_le_mul_right _ h2B
      _ = P - 1 := hgolden
  have hBGj : B * Gj + 1 ≤ P := by omega
  -- b_j ≥ B+1 ⟹ b_j·P ≥ (B+1)·P = B·P + P.
  have hbjge : B + 1 ≤ bj := by omega
  have hbjP : B * P + P ≤ bj * P := by
    calc B * P + P = (B + 1) * P := by ring
      _ ≤ bj * P := Nat.mul_le_mul_right _ hbjge
  -- assemble: goal  B·(geomQ q i) + 1 ≤ n % q^i.
  rw [hGsplit]
  -- B·(Gj + P + SumMid) + 1 ≤ n % q^i.  Use htailval, hlb, and the products.
  have hgoalexp : B * (Gj + P + SumMid) + 1 = (B * Gj + 1) + (B * P) + (B * SumMid) := by ring
  rw [hgoalexp]
  -- tailLB = bj·P + B·SumMid ≤ n%q^i.  And (B·Gj+1)+B·P ≤ P + B·P ≤ bj·P.
  have htv : tailLB q n j i = bj * P + B * SumMid := by rw [htailval]
  rw [htv] at hlb
  omega

/-! ## THE ASSEMBLED CONDITION-(3) WINDOW PRODUCER (KERNEL-CLEAN)

`cond3_window` is the EGRS75 "window-nonempty / condition-(3)" producer for the ADD branch
of the LOW case.  Given a `LowDigits q`-failing number `n` (`0 < badCountQ q n`) whose paper
tail `T = n % q^i` (at the least strictly-good index `i = leastGoodAbove > j = topBadIndex`)
is below `S = (p^m + 1)/2` (the ADD trigger `T < S` in the equality case
`A = (p-1)/2`, `B = (q-1)/2`), it produces the clearing index `i` together with:

  * `topBadIndex q n < i`  (above the top oversized digit),
  * `n / q^i % q < (q-1)/2` (the digit at `i` is STRICTLY good, so `b_i* = b_i + 1 ≤ B`
    stays good after the ADD), and
  * `q^i < p^m`             (condition (3) — the carry interlock the ADD draw needs).

It chains `tail_ge` (the tail LOWER bound `B·G i + 1 ≤ T`, KERNEL-CLEAN) with
`cond3_of_tail_small` (the algebraic interlock, KERNEL-CLEAN).  This is the exact triple
P2 consumes to draw `U ∈ [q^i - T, p^m)` from `RoundUp.exists_lowDigits_between`. -/

/-- **CONDITION-(3) WINDOW PRODUCER (KERNEL-CLEAN).**  For odd primes `p, q ≥ 3`, a number
`n` with a bad base-`q` digit, and the ADD trigger `n % q^i < (p^m + 1)/2` at the least
strictly-good index `i = leastGoodAbove`, the clearing index `i` is above the top bad index,
strictly good, and satisfies condition (3) `q^i < p^m`.

This is the producer the ADD branch consumes: `i` is a valid place to add (digit strictly
good, above the top bad digit), and `q^i < p^m` guarantees the EGRS density `Fact`
(`RoundUp.exists_lowDigits_between` at `x = q^i - T`) yields a correction `< p^m` that is
base-`p` safe (via `RepairDV.lowDigits_disjoint_add`). -/
theorem cond3_window {p q : ℕ} (_hp : 3 ≤ p) (hq : 3 ≤ q) (hpo : Odd p) (hqo : Odd q)
    (n m : ℕ) (hbad : 0 < badCountQ q n)
    (hTS : n % q ^ (leastGoodAbove hq hbad) < (p ^ m + 1) / 2) :
    ∃ i, topBadIndex q n < i ∧ n / q ^ i % q < (q - 1) / 2 ∧ q ^ i < p ^ m := by
  refine ⟨leastGoodAbove hq hbad, topBad_lt_leastGoodAbove hq hbad,
    strictGoodAt_leastGoodAbove hq hbad, ?_⟩
  -- condition (3): from the tail lower bound `B·G i + 1 ≤ T` and `T < S`.
  exact cond3_of_tail_small hq hpo hqo m _ _ (tail_ge hq hbad) hTS

end Egrs75.P4
