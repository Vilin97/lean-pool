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
import LeanPool.Egrs75.AddBranch
import LeanPool.Egrs75.SubtractBranch
import LeanPool.Egrs75.ConditionThreeWindow
import LeanPool.Egrs75.MoveDigits
import LeanPool.Egrs75.SeedWindow
import LeanPool.Egrs75.Reduction
import Mathlib.Data.Nat.Digits.Lemmas

/-!
EGRS75 two-prime — the μ-MEASURE CLOSURE (2026-06-12).

NEW file.  Imports the kernel-clean P-machinery + `EgrsMoveDigits_20260612`
(local digit toolkit) + `EgrsSeedWindow_20260612` (the Diophantine seed) +
`EgrsAll` (the clean `egrs_two_prime_of_crux`).  Modifies nothing upstream.

════════════════════════════════════════════════════════════════════════════
THE CLOSURE ARGUMENT (EGRS75, Math. Comp. 29 (1975), pp.84-85, equality case
`A = (p-1)/2`, `B = (q-1)/2`), with two fixes over the 2026-06-08 wave:

(1) THE MEASURE.  μ(n) = i·q + (B − b_i), where j = topBadIndex q n,
    i = leastGoodAbove(j) (least strictly-good index above j; digits strictly
    between are exactly B), b_i = digit of n at i.  μ strictly drops on every
    single ADD move and never rises on a SUBTRACT (which strictly drops n), so
    lex (μ, n) ∈ ℕ² is a faithful termination measure — the outer strong
    induction does ALL the iterating and no inner iteration is hidden anywhere.

(2) THE FLOOR.  The magnitude invariant is NOT `N < n` alone (the paper's
    SUBTRACT branch lowers n) but `N < (n / q^i)·q^i` — the digits at/above the
    working index alone already exceed N.  Both branches preserve it: SUBTRACT
    freezes the block at/above i (it only strips the tail `S ≤ T = n % q^i`);
    ADD increments it.  The Diophantine seed `p^α` (condition (2), file
    `EgrsSeedWindow_20260612`) establishes it at start: its base-`q` digits are
    B at e+3, 0 at e+2 (a strictly-good barrier), staircase below, so its
    working index is ≤ e+2 and the preserved block is ≥ B·q^(e+3) > N.

THE MOVE (single, no iteration), branch on T = n % q^i vs S = (p^m+1)/2 with
m = lowest nonzero base-p digit index:
  • T < S (ADD):  condition (3) gives q^i < p^m; draw a LowDigits-p correction
    U ∈ [q^i−T, 2(q^i−T)) (density Fact); the single carry sends digit i to
    b_i+1, freezes everything above, and replaces the tail by R = T+U−q^i with
    2R+3 ≤ q^i — STRICTLY below the all-B ceiling.  The STAIRCASE lemma then
    locates a strictly-good barrier k < i with exactly-B digits in (k,i), so the
    new working index is ≤ k < i:  μ STRICTLY DROPS.  n grows; the block at i
    increments — floor preserved.
  • S ≤ T (SUBTRACT):  n' = n − S is LowDigits p (borrow eats the trailing
    base-p zeros), digits at/above i are FROZEN (S ≤ T), so μ is unchanged (or
    drops) while n strictly drops — the lex pair falls.  Floor frozen.

STATUS: **ZERO sorry.**  Every theorem in this file is kernel-clean
(`#print axioms` = propext / Classical.choice / Quot.sound; no native_decide,
no extra axiom).  This completes the Lean 4 formalization of the KNOWN
Erdős–Graham–Ruzsa–Straus 1975 two-prime theorem (Theorem 1, equality case):
infinitely many n with p ∤ C(2n,n) and q ∤ C(2n,n) for distinct odd primes p,q.
NOT an open-problem solve: the r ≥ 3 generalization is Erdős #376 (OPEN) and is
not attempted.  Recon: ~/Knowledge/Construct/recon/erdos_376.md.
-/

namespace Egrs75.MuFinish

open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.P4

/-! ## The μ-measure (total ℕ-valued) -/

/-- **The μ-measure.**  `μ(n) = i·q + (B − b_i)` with `i = leastGoodAbove(topBad n)`,
`B = (q-1)/2`, `b_i = n / q^i % q`.  Total: junk `0` when `n` has no bad base-`q`
digit.  `B − b_i < q`, so this is the faithful mixed-radix linearisation of the
lex pair `(i, B − b_i)`. -/
noncomputable def muVal (q : ℕ) (hq3 : 3 ≤ q) (n : ℕ) : ℕ :=
  if hbad : 0 < badCountQ q n then
    leastGoodAbove hq3 hbad * q + ((q - 1) / 2 - n / q ^ (leastGoodAbove hq3 hbad) % q)
  else 0

/-! ## The μ-drop arithmetic core (KERNEL-CLEAN) -/

/-- **μ strictly drops.**  `μ(n') < μ(n)` whenever `n'` is fully good, or its
working index dropped, or the index held and the digit there strictly climbed. -/
theorem muVal_lt_of {q : ℕ} (hq3 : 3 ≤ q) {n n' : ℕ} (hbad : 0 < badCountQ q n)
    (h : badCountQ q n' = 0 ∨
         ∃ hbad' : 0 < badCountQ q n',
           leastGoodAbove hq3 hbad' < leastGoodAbove hq3 hbad ∨
           (leastGoodAbove hq3 hbad' = leastGoodAbove hq3 hbad ∧
            n / q ^ (leastGoodAbove hq3 hbad) % q
              < n' / q ^ (leastGoodAbove hq3 hbad') % q)) :
    muVal q hq3 n' < muVal q hq3 n := by
  have hmn : muVal q hq3 n
      = leastGoodAbove hq3 hbad * q
        + ((q - 1) / 2 - n / q ^ (leastGoodAbove hq3 hbad) % q) := by
    simp only [muVal, dif_pos hbad]
  have hbB : n / q ^ (leastGoodAbove hq3 hbad) % q < (q - 1) / 2 :=
    strictGoodAt_leastGoodAbove hq3 hbad
  have hi1 : 1 ≤ leastGoodAbove hq3 hbad := by
    have := topBad_lt_leastGoodAbove hq3 hbad; omega
  rcases h with hzero | ⟨hbad', hcase⟩
  · have hmn' : muVal q hq3 n' = 0 := by
      simp only [muVal, dif_neg (by omega : ¬ 0 < badCountQ q n')]
    have hpos : 0 < leastGoodAbove hq3 hbad * q :=
      Nat.mul_pos (by omega) (by omega)
    rw [hmn, hmn']; omega
  · have hmn' : muVal q hq3 n'
        = leastGoodAbove hq3 hbad' * q
          + ((q - 1) / 2 - n' / q ^ (leastGoodAbove hq3 hbad') % q) := by
      simp only [muVal, dif_pos hbad']
    have hb'B : n' / q ^ (leastGoodAbove hq3 hbad') % q < (q - 1) / 2 :=
      strictGoodAt_leastGoodAbove hq3 hbad'
    rw [hmn, hmn']
    rcases hcase with hlt | ⟨heq, hbb⟩
    · have key : leastGoodAbove hq3 hbad' * q + q ≤ leastGoodAbove hq3 hbad * q := by
        have hle : leastGoodAbove hq3 hbad' + 1 ≤ leastGoodAbove hq3 hbad := by omega
        calc leastGoodAbove hq3 hbad' * q + q
            = (leastGoodAbove hq3 hbad' + 1) * q := by ring
          _ ≤ leastGoodAbove hq3 hbad * q := by gcongr
      omega
    · rw [heq] at hbb hb'B ⊢; omega

/-! ## THE SINGLE MOVE — fully proven (no sorry)

One EGRS75 condition-(3) carry-controlled move: ADD when `T < S`, SUBTRACT when
`S ≤ T`.  Output: still `LowDigits p`, the floor block at the working index is
preserved-or-grown, and the lex pair `(μ, n)` strictly falls. -/

/-- **THE EGRS75 SINGLE MOVE (KERNEL-CLEAN, no sorry).** -/
theorem egrs_move {p q : ℕ} (hp : p.Prime) (_hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (_hpq : p ≠ q) (hq3 : 3 ≤ q) (N : ℕ)
    {n : ℕ} (hpn : LowDigits p n) (hbad : 0 < badCountQ q n)
    (hfloor : N < n / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad)) :
    ∃ n', LowDigits p n' ∧
      N < n' / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad) ∧
      (muVal q hq3 n' < muVal q hq3 n ∨
        (muVal q hq3 n' = muVal q hq3 n ∧ n' < n)) := by
  have hq1 : 1 < q := by omega
  have hp3 : 3 ≤ p := by have h2 := hp.two_le; rcases hpo with ⟨c, hc⟩; omega
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp [badCountQ, badDigitsQ] at hbad
  set i := leastGoodAbove hq3 hbad with hidef
  set m := ClearingP3.lowPDigitIndex p n with hmdef
  set T := n % q ^ i with hTdef
  set S := (p ^ m + 1) / 2 with hSdef
  have hji : topBadIndex q n < i := topBad_lt_leastGoodAbove hq3 hbad
  have hi1 : 1 ≤ i := by omega
  have hbi : n / q ^ i % q < (q - 1) / 2 := strictGoodAt_leastGoodAbove hq3 hbad
  have hqipos : 0 < q ^ i := pow_pos (by omega) i
  have hTlt : T < q ^ i := by rw [hTdef]; exact Nat.mod_lt _ hqipos
  have htail : (q - 1) / 2 * geomQ q i + 1 ≤ T := by
    rw [hTdef, hidef]; exact tail_ge hq3 hbad
  have hB2 : 2 * ((q - 1) / 2) = q - 1 := by obtain ⟨c, hc⟩ := hqo; omega
  have hgold : (q - 1) * geomQ q i = q ^ i - 1 := geomQ_mul (by omega) i
  have hqi1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ (by omega)
  have hT2 : q ^ i + 1 ≤ 2 * T := by
    have h2 : 2 * ((q - 1) / 2 * geomQ q i) = (q - 1) * geomQ q i := by
      calc 2 * ((q - 1) / 2 * geomQ q i)
          = 2 * ((q - 1) / 2) * geomQ q i := by ring
        _ = (q - 1) * geomQ q i := by rw [hB2]
    omega
  have hmun : muVal q hq3 n = i * q + ((q - 1) / 2 - n / q ^ i % q) := by
    simp only [muVal, dif_pos hbad, ← hidef]
  have hq_le_iq : q ≤ i * q := by
    calc q = 1 * q := (one_mul q).symm
      _ ≤ i * q := Nat.mul_le_mul_right _ hi1
  rcases Nat.lt_or_ge T S with hTS | hST
  · -- ════════════ ADD branch (T < S; condition (3) fires) ════════════
    have hTS' : T < (p ^ m + 1) / 2 := by omega
    have hcond3 : q ^ i < p ^ m :=
      cond3_of_tail_small hq3 hpo hqo m i T htail hTS'
    have hx1 : 1 ≤ q ^ i - T := by omega
    obtain ⟨U, hUlo, hUhi, hUlow⟩ :=
      RoundUp.exists_lowDigits_between hp3 hpo (q ^ i - T) hx1
    have hUp : U < p ^ m := by omega
    have hmod : n % p ^ m = 0 := by
      rw [hmdef]; exact ClearingP3.mod_pow_lowPDigitIndex (by omega) hn0
    have hpn' : LowDigits p (n + U) :=
      ClearingP2.add_U_lowDigits_p (by omega) hpn hUlow hUp hmod (by omega)
    have hclo : q ^ i ≤ n % q ^ i + U := by omega
    have hchi : n % q ^ i + U < 2 * q ^ i := by omega
    have hdiv_i : (n + U) / q ^ i = n / q ^ i + 1 :=
      MoveDigits.add_div_pow_eq hq1 n U i hclo hchi
    have hfl' : N < (n + U) / q ^ i * q ^ i := by
      rw [hdiv_i]
      have hmono : n / q ^ i * q ^ i ≤ (n / q ^ i + 1) * q ^ i :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    refine ⟨n + U, hpn', hfl', ?_⟩
    rcases Nat.eq_zero_or_pos (badCountQ q (n + U)) with hz | hbad'
    · -- terminal: fully good, μ' = 0 < μ
      left
      have hmu0 : muVal q hq3 (n + U) = 0 := by
        simp only [muVal, dif_neg (by omega : ¬ 0 < badCountQ q (n + U))]
      omega
    · -- the staircase: the working index drops strictly
      left
      have hRst : 2 * (n % q ^ i + U - q ^ i) + 3 ≤ q ^ i := by omega
      obtain ⟨k, hki, hkstrict, hkbet⟩ :=
        MoveDigits.staircase hq3 hqo i (n % q ^ i + U - q ^ i) hRst
      have hlow : ∀ t, t < i →
          (n + U) / q ^ t % q = (n % q ^ i + U - q ^ i) / q ^ t % q :=
        fun t ht => MoveDigits.add_low_digit hq1 n U i t ht hclo
      have hbiq : n / q ^ i % q < q - 1 := by omega
      have hdig_i : (n + U) / q ^ i % q = n / q ^ i % q + 1 :=
        MoveDigits.add_digit_i hq1 n U i hclo hchi hbiq
      have hhigh : ∀ idx, i < idx → (n + U) / q ^ idx % q = n / q ^ idx % q :=
        fun idx hidx => MoveDigits.add_high_frozen hq1 n U i idx hclo hchi hbiq hidx
      have hgoodk : ∀ idx, k ≤ idx → (n + U) / q ^ idx % q ≤ (q - 1) / 2 := by
        intro idx hidx
        rcases Nat.lt_trichotomy idx i with hlt | heqi | hgt
        · rcases Nat.eq_or_lt_of_le hidx with heqk | hgtk
          · rw [hlow idx hlt, ← heqk]
            exact le_of_lt hkstrict
          · rw [hlow idx hlt, hkbet idx hgtk hlt]
        · subst heqi
          rw [hdig_i]; omega
        · rw [hhigh idx hgt]
          exact digit_good_above_top hq1 hbad (by omega)
      have htb' : topBadIndex q (n + U) < k :=
        MoveDigits.topBad_lt_of_good_from hq1 hbad' hgoodk
      have hsgk : StrictGoodAt q k (n + U) := by
        unfold StrictGoodAt
        rw [hlow k hki]; exact hkstrict
      have hi'le : leastGoodAbove hq3 hbad' ≤ k := Nat.find_min' _ ⟨htb', hsgk⟩
      exact muVal_lt_of hq3 hbad (Or.inr ⟨hbad', Or.inl (by omega)⟩)
  · -- ════════════ SUBTRACT branch (S ≤ T; tail strip, block frozen) ════════════
    have hppos : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
    have hSpos : 1 ≤ S := by omega
    have hTn : T ≤ n := by rw [hTdef]; exact Nat.mod_le _ _
    have hlt_n : n - S < n := by omega
    have hST' : S ≤ n % q ^ i := by omega
    have hpn' : LowDigits p (n - S) := by
      rw [hSdef, hmdef]
      exact ClearingP3.sub_preserves_lowDigits hp hpo hpn hn0
    have hfrozen : ∀ idx, i ≤ idx → (n - S) / q ^ idx % q = n / q ^ idx % q :=
      fun idx hidx => ClearingP3.sub_high_digits_frozen (by omega) hST' hidx
    have hdivfr : (n - S) / q ^ i = n / q ^ i :=
      ClearingP3.sub_div_pow_eq (by omega) hST'
    have hfl' : N < (n - S) / q ^ i * q ^ i := by rw [hdivfr]; exact hfloor
    refine ⟨n - S, hpn', hfl', ?_⟩
    rcases Nat.eq_zero_or_pos (badCountQ q (n - S)) with hz | hbad'
    · left
      have hmu0 : muVal q hq3 (n - S) = 0 := by
        simp only [muVal, dif_neg (by omega : ¬ 0 < badCountQ q (n - S))]
      omega
    · have hgoodi : ∀ idx, i ≤ idx → (n - S) / q ^ idx % q ≤ (q - 1) / 2 := by
        intro idx hidx
        rw [hfrozen idx hidx]
        rcases Nat.eq_or_lt_of_le hidx with heqi | hgti
        · rw [← heqi]; exact le_of_lt hbi
        · exact digit_good_above_top hq1 hbad (by omega)
      have htb' : topBadIndex q (n - S) < i :=
        MoveDigits.topBad_lt_of_good_from hq1 hbad' hgoodi
      have hsgi : StrictGoodAt q i (n - S) := by
        unfold StrictGoodAt
        rwa [hfrozen i (le_refl i)]
      have hi'le : leastGoodAbove hq3 hbad' ≤ i := Nat.find_min' _ ⟨htb', hsgi⟩
      rcases Nat.eq_or_lt_of_le hi'le with heq' | hlt'
      · -- index and digit frozen: μ unchanged, n strictly drops
        right
        refine ⟨?_, hlt_n⟩
        have h1 : muVal q hq3 (n - S)
            = leastGoodAbove hq3 hbad' * q
              + ((q - 1) / 2 - (n - S) / q ^ (leastGoodAbove hq3 hbad') % q) := by
          simp only [muVal, dif_pos hbad']
        rw [h1, hmun, heq']
        rw [hfrozen i (le_refl i)]
      · -- index dropped: μ strictly drops
        left
        exact muVal_lt_of hq3 hbad (Or.inr ⟨hbad', Or.inl (by omega)⟩)

/-! ## The clean lex-(μ, n) strong induction -/

/-- **ALIGN via the lex pair `(μ, n)` (KERNEL-CLEAN).**  Repeatedly applying the
single move from a seed whose floor block exceeds `N` yields a number that is
`> N`, `LowDigits p`, and `LowDigits q`.  Outer strong induction on `μ`, inner
on `n`; the floor invariant `N < (n/q^i)·q^i` is threaded (it implies `N < n`). -/
theorem align_mu {p q : ℕ} (hq3 : 3 ≤ q) (N : ℕ)
    (hmove : ∀ {n : ℕ}, LowDigits p n → ∀ (hbad : 0 < badCountQ q n),
        N < n / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad) →
        ∃ n', LowDigits p n' ∧
          N < n' / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad) ∧
          (muVal q hq3 n' < muVal q hq3 n ∨
            (muVal q hq3 n' = muVal q hq3 n ∧ n' < n)))
    (seed : ℕ) (hsN : N < seed) (hsp : LowDigits p seed)
    (hsfl : ∀ (hbad : 0 < badCountQ q seed),
        N < seed / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad)) :
    ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by
  suffices H : ∀ k n, muVal q hq3 n = k → LowDigits p n → N < n →
      (∀ (hbad : 0 < badCountQ q n),
        N < n / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad)) →
      ∃ m, N < m ∧ LowDigits p m ∧ LowDigits q m by
    exact H _ seed rfl hsp hsN hsfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro hk hpn hNn hfl
      rcases Nat.eq_zero_or_pos (badCountQ q n) with hz | hbad
      · exact ⟨n, hNn, hpn, badCountQ_eq_zero_iff_lowDigits.mp hz⟩
      obtain ⟨n', hpn', hfl', hdrop⟩ := hmove hpn hbad (hfl hbad)
      have hNn' : N < n' := lt_of_lt_of_le hfl' (Nat.div_mul_le_self _ _)
      have hfl'' : ∀ (hbad' : 0 < badCountQ q n'),
          N < n' / q ^ (leastGoodAbove hq3 hbad') * q ^ (leastGoodAbove hq3 hbad') := by
        intro hbad'
        have hmle : muVal q hq3 n' ≤ muVal q hq3 n := by
          rcases hdrop with h | ⟨h, _⟩
          · exact le_of_lt h
          · exact le_of_eq h
        have hile : leastGoodAbove hq3 hbad' ≤ leastGoodAbove hq3 hbad := by
          by_contra hcon
          push Not at hcon
          have h1 : muVal q hq3 n' = leastGoodAbove hq3 hbad' * q
              + ((q - 1) / 2 - n' / q ^ (leastGoodAbove hq3 hbad') % q) := by
            simp only [muVal, dif_pos hbad']
          have h2 : muVal q hq3 n = leastGoodAbove hq3 hbad * q
              + ((q - 1) / 2 - n / q ^ (leastGoodAbove hq3 hbad) % q) := by
            simp only [muVal, dif_pos hbad]
          have h3 : (leastGoodAbove hq3 hbad + 1) * q ≤ leastGoodAbove hq3 hbad' * q :=
            Nat.mul_le_mul_right _ (by omega)
          have h4 : (leastGoodAbove hq3 hbad + 1) * q
              = leastGoodAbove hq3 hbad * q + q := by ring
          have h5 : (q - 1) / 2 - n / q ^ (leastGoodAbove hq3 hbad) % q < q := by omega
          omega
        exact lt_of_lt_of_le hfl'
          (MoveDigits.div_mul_pow_mono (by omega) n' hile)
      rcases hdrop with hlt | ⟨heq, hltn⟩
      · exact ihk (muVal q hq3 n') (by omega) n' rfl hpn' hNn' hfl''
      · exact ihn n' hltn (by omega) hpn' hNn' hfl''

/-! ## The seeded finish: Diophantine seed + μ-induction + single move -/

/-- align ⟹ crux (KERNEL-CLEAN). -/
theorem align_to_crux {p q : ℕ}
    (halign : ∀ N, ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n) :
    {n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hN, hpn, hqn⟩ := halign N
  exact ⟨n, ⟨hpn, hqn⟩, hN⟩

/-- **ALIGN, fully proven (KERNEL-CLEAN, no sorry).**  For distinct odd primes
`p q`, every `N` admits `n > N` that is `LowDigits p` and `LowDigits q`.  Seeded
by the Diophantine window `seed_window` (EGRS condition (2)); driven by
`align_mu` consuming the fully-proven `egrs_move`. -/
theorem align_finish_mu {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    ∀ N, ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by
  intro N
  have hp3 : 3 ≤ p := by have h2 := hp.two_le; rcases hpo with ⟨c, hc⟩; omega
  have hq3 : 3 ≤ q := by have h2 := hq.two_le; rcases hqo with ⟨c, hc⟩; omega
  have hq1 : 1 < q := by omega
  have hBq1 : 1 ≤ (q - 1) / 2 := by omega
  -- the Diophantine seed
  obtain ⟨α, e, hα1, hF, hlo, hhi⟩ := SeedWindow.seed_window hp hq hq3 hpq N
  have hsp : LowDigits p (p ^ α) := seed_lowDigits_pow hp3 α
  -- seed magnitude
  have hBmul : q ^ (e + 3) ≤ (q - 1) / 2 * q ^ (e + 3) := by
    have h := Nat.mul_le_mul_right (q ^ (e + 3)) hBq1
    omega
  have hsN : N < p ^ α := by omega
  -- seed digit structure
  have hpow13 : q ^ (e + 1) ≤ q ^ (e + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow12 : q ^ (e + 1) ≤ q ^ (e + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hupper : p ^ α < ((q - 1) / 2 + 1) * q ^ (e + 3) := by
    have hexp : ((q - 1) / 2 + 1) * q ^ (e + 3)
        = (q - 1) / 2 * q ^ (e + 3) + q ^ (e + 3) := by ring
    omega
  have hdiv3 : p ^ α / q ^ (e + 3) = (q - 1) / 2 :=
    Nat.div_eq_of_lt_le (le_of_lt hlo) hupper
  have hsplit23 : q ^ (e + 3) = q ^ (e + 2) * q := pow_succ q (e + 2)
  have hdiv2 : p ^ α / q ^ (e + 2) = (q - 1) / 2 * q := by
    apply Nat.div_eq_of_lt_le
    · have hexp2 : (q - 1) / 2 * q * q ^ (e + 2) = (q - 1) / 2 * q ^ (e + 3) := by
        rw [hsplit23]; ring
      omega
    · have hexp3 : ((q - 1) / 2 * q + 1) * q ^ (e + 2)
          = (q - 1) / 2 * q ^ (e + 3) + q ^ (e + 2) := by
        rw [hsplit23]; ring
      omega
  have hsmall : p ^ α < q ^ (e + 4) := by
    have h1 : ((q - 1) / 2 + 1) * q ^ (e + 3) ≤ q * q ^ (e + 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : q ^ (e + 4) = q ^ (e + 3) * q := pow_succ q (e + 3)
    have h3 : q * q ^ (e + 3) = q ^ (e + 3) * q := Nat.mul_comm _ _
    omega
  have hgood2 : ∀ idx, e + 2 ≤ idx → p ^ α / q ^ idx % q ≤ (q - 1) / 2 := by
    intro idx hidx
    rcases Nat.lt_or_ge idx (e + 3) with h2 | h3
    · -- idx = e + 2
      have heq2 : idx = e + 2 := by omega
      subst heq2
      rw [hdiv2, Nat.mul_mod_left]
      omega
    · rcases Nat.lt_or_ge idx (e + 4) with h4 | h5
      · -- idx = e + 3
        have heq3 : idx = e + 3 := by omega
        subst heq3
        rw [hdiv3, Nat.mod_eq_of_lt (by omega : (q - 1) / 2 < q)]
      · -- idx ≥ e + 4: digit 0
        have hz : p ^ α / q ^ idx = 0 := by
          apply Nat.div_eq_of_lt
          calc p ^ α < q ^ (e + 4) := hsmall
            _ ≤ q ^ idx := Nat.pow_le_pow_right (by omega) h5
        rw [hz]
        simp only [Nat.zero_mod]
        omega
  rcases Nat.eq_zero_or_pos (badCountQ q (p ^ α)) with hz | hbads
  · -- the seed is already fully good
    exact ⟨p ^ α, hsN, hsp, badCountQ_eq_zero_iff_lowDigits.mp hz⟩
  · -- run the μ-machine from the seed
    have htb : topBadIndex q (p ^ α) < e + 2 :=
      MoveDigits.topBad_lt_of_good_from hq1 hbads hgood2
    have hsg : StrictGoodAt q (e + 2) (p ^ α) := by
      unfold StrictGoodAt
      rw [hdiv2, Nat.mul_mod_left]
      omega
    have hple : leastGoodAbove hq3 hbads ≤ e + 2 := Nat.find_min' _ ⟨htb, hsg⟩
    have hsfl : ∀ (hbad : 0 < badCountQ q (p ^ α)),
        N < p ^ α / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad) := by
      intro hbad
      have hBe : (q - 1) / 2 * q ^ (e + 3) = (q - 1) / 2 * q * q ^ (e + 2) := by
        rw [hsplit23]; ring
      calc N < q ^ (e + 3) := hF
        _ ≤ (q - 1) / 2 * q ^ (e + 3) := hBmul
        _ = (q - 1) / 2 * q * q ^ (e + 2) := hBe
        _ = p ^ α / q ^ (e + 2) * q ^ (e + 2) := by rw [hdiv2]
        _ ≤ p ^ α / q ^ (leastGoodAbove hq3 hbad) * q ^ (leastGoodAbove hq3 hbad) :=
            MoveDigits.div_mul_pow_mono (by omega) _ hple
    exact align_mu hq3 N
      (fun {m'} hpm hbad' hfl' => egrs_move hp hq hpo hqo hpq hq3 N hpm hbad' hfl')
      (p ^ α) hsN hsp hsfl

/-! ## Final assembly: the EGRS75 two-prime theorem, ZERO sorry -/

/-- **EGRS75 two-prime theorem — CLOSED (KERNEL-CLEAN, no sorry).**  For
distinct odd primes `p q`, there are infinitely many `n` with `p ∤ C(2n,n)` and
`q ∤ C(2n,n)`.  (Erdős–Graham–Ruzsa–Straus, Math. Comp. 29 (1975), Theorem 1,
equality case — a KNOWN theorem; this is its machine-checked proof.) -/
theorem egrs_two_prime_mu {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite :=
  egrs_two_prime_of_crux hp hq hpo hqo
    (align_to_crux (align_finish_mu hp hq hpo hqo hpq))

/-- The crux itself, closed: `A_p ∩ A_q` is infinite. -/
theorem egrs_crux_mu {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite :=
  align_to_crux (align_finish_mu hp hq hpo hqo hpq)

/-- **The 2026-06-08 residual, discharged.**  Statement byte-identical to
`Finish.egrs_clearing_low` (EgrsFinish_core.lean:301): from the μ-closure, a
fully `(q,B)`-good number above any floor exists, which clears every index. -/
theorem egrs_clearing_low_mu {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) (N : ℕ)
    {n : ℕ} (_hpn : LowDigits p n) (_hNn : N < n) (_hbad : 0 < badCountQ q n)
    (_hlow : q ^ (topBadIndex q n) ≤ N) :
    ∃ n', LowDigits p n' ∧ N < n' ∧ (∀ i, topBadIndex q n ≤ i → ¬ BadAt q i n') := by
  obtain ⟨n', hN', hpn', hqn'⟩ := align_finish_mu hp hq hpo hqo hpq N
  refine ⟨n', hpn', hN', fun idx _ => ?_⟩
  have hq3 : 3 ≤ q := by have h2 := hq.two_le; rcases hqo with ⟨c, hc⟩; omega
  have hd := (lowDigits_iff_digitAt (by omega : 2 ≤ q)).mp hqn' idx
  unfold BadAt
  omega

end Egrs75.MuFinish
