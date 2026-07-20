/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.IntervalCases
import LeanPool.Erdos403.Basic
import LeanPool.Erdos403.FactBase

/-!
# Erdős #403 — the sharp bound `m ≤ 7` (Phases B–D)

Using the factorial number system (`FactBase`), `factSum S = 2^m` is impossible once `2^m` and
`2^m − 1` both carry a factorial digit `≥ 2` (`not_factSum_of_digits`).

* **Phase B (done):** `m` even `≥ 4` is killed cleanly — `2^m ≡ 16 (mod 24)` forces the
  `3!`-digit of *both* `2^m` and `2^m − 1` to be `2` (and `3! = 6` has no factorial degeneracy, so
  the `0!` carry cannot fix it).
* **Phase C (done):** `m` ≥ 8 is killed by a *fixed* modulus `12!` — every such `2^m` (and
  `2^m − 1`) carries a factorial digit `≥ 2` at some index `≤ 11`, a finite check over the
  period-`1620` cycle of `2^m mod 12!`, discharged by a kernel-pure `decide`.
* **Phase D (done):** `erdos_403_sharp` and `erdos_403_finite` are assembled below (`decide` the
  small `m`). Both are `sorry`-free and depend only on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Erdos403

open scoped Nat

/-- `2^(2t+4) ≡ 16 (mod 24)` — the period-2 cycle `…,16,8,16,8,…` of `2^m mod 24` (`m ≥ 3`),
on the even branch. -/
theorem two_pow_mod_24_even : ∀ t, 2 ^ (2 * t + 4) % 24 = 16 := by
  intro t
  induction t with
  | zero => decide
  | succ k ih =>
    have he : 2 * (k + 1) + 4 = (2 * k + 4) + 2 := by ring
    rw [he, pow_add, Nat.mul_mod, ih]
    decide

/-- `2^m ≡ 16 (mod 24)` for even `m ≥ 4`. -/
theorem two_pow_mod_24_of_even {m : ℕ} (he : Even m) (hm : 4 ≤ m) : 2 ^ m % 24 = 16 := by
  obtain ⟨r, rfl⟩ := he
  have hrw : r + r = 2 * (r - 2) + 4 := by omega
  rw [hrw]; exact two_pow_mod_24_even (r - 2)

/-- For even `m ≥ 4`, the `3!`-digit of `2^m` is `2`. -/
theorem factDigit_three_two_pow_even {m : ℕ} (he : Even m) (hm : 4 ≤ m) :
    factDigit 3 (2 ^ m) = 2 := by
  have h := two_pow_mod_24_of_even he hm
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ m = 24 * q + 16 := ⟨2 ^ m / 24, by omega⟩
  change (2 ^ m / 6) % 4 = 2
  rw [hq]; omega

/-- For even `m ≥ 4`, the `3!`-digit of `2^m − 1` is also `2` (so the `0!` carry can't rescue
it). -/
theorem factDigit_three_two_pow_sub_one_even {m : ℕ} (he : Even m) (hm : 4 ≤ m) :
    factDigit 3 (2 ^ m - 1) = 2 := by
  have h := two_pow_mod_24_of_even he hm
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ m = 24 * q + 16 := ⟨2 ^ m / 24, by omega⟩
  change ((2 ^ m - 1) / 6) % 4 = 2
  rw [hq]; omega

/-- **Phase B result.** No sum of distinct factorials equals `2^m` for even `m ≥ 4`. -/
theorem factSum_ne_of_even {m : ℕ} (he : Even m) (hm : 4 ≤ m) (S : Finset ℕ) :
    factSum S ≠ 2 ^ m := by
  refine not_factSum_of_digits (2 ^ m) ⟨3, by omega, ?_⟩ ⟨3, by omega, ?_⟩ S
  · rw [factDigit_three_two_pow_even he hm]
  · rw [factDigit_three_two_pow_sub_one_even he hm]

/-- **Phase C-7a (leading-digit kill).** If `2·M! < 2^m < (M+1)!` — i.e. `2^m` reaches *twice* its
leading factorial `M!` without spilling into the next — then the top factorial digit of *both*
`2^m` and `2^m − 1` is `≥ 2` (`2^m − 1` shares the same leading index and still clears `2·M!`,
strictly, since `2^m` is a power of two). So `not_factSum_of_digits` fires. This bankable sub-case
kills every odd `m ≥ 9` whose `2^m` lands in the upper half `[2·M!, (M+1)!)`; the residual nut is
the lower half `[M!, 2·M!)`. -/
theorem factSum_ne_of_leading_two {m M : ℕ} (hM : 2 ^ m < (M + 1)!) (h2 : 2 * M ! < 2 ^ m)
    (S : Finset ℕ) : factSum S ≠ 2 ^ m := by
  -- `2·M! < 2^m < (M+1)! = (M+1)·M!` forces `M ≥ 2`, so `M` is a valid positive digit index.
  have hM1 : 1 ≤ M := by
    by_contra h
    simp_all
  refine not_factSum_of_digits (2 ^ m) ⟨M, hM1, ?_⟩ ⟨M, hM1, ?_⟩ S
  · exact two_le_factDigit_top hM (by omega)
  · exact two_le_factDigit_top (by omega) (by omega)

/-! ## Phase C — odd `m ≥ 9` killed by a FIXED modulus (`12!`)

Direct computation (verified three ways) shows the factorial-base expansion of `2^m` **and** of
`2^m - 1` carries a digit `≥ 2` at some index `≤ 11` for *every* `m ≥ 8`. Equivalently, a single
fixed modulus `12!` closes Erdős #403. The earlier belief that "no fixed modulus works" was a
heuristic extrapolation — the smallest offending index climbs `5 → 7 → 8 → 11` and was *assumed*
to grow without bound; in fact it caps at `11`.

Mechanism: `factDigit i n` depends only on `n mod (i+1)!`, hence for `i ≤ 11` only on `n mod 12!`;
and `2^m mod 12!` is periodic in `m` with period `1620` (`ord_{467775}(2) = 1620`, where
`12! = 1024 · 467775`). So the claim reduces to a finite check over one period, discharged by a
kernel-pure `decide` over a residue fold (no `native_decide`). -/

/-- `factDigit i n` depends only on `n` modulo `(i+1)!`. -/
theorem factDigit_mod (i n : ℕ) : factDigit i n = factDigit i (n % (i + 1)!) := by
  unfold factDigit
  set q := n / (i + 1)! with hq
  set r := n % (i + 1)! with hr
  have hn : n = (i + 1)! * q + r := by rw [hq, hr, Nat.div_add_mod]
  have hsplit : n / i ! = (i + 1) * q + r / i ! := by
    conv_lhs => rw [hn, Nat.factorial_succ]
    rw [show (i + 1) * i ! * q = i ! * ((i + 1) * q) by ring, Nat.mul_add_div (Nat.factorial_pos i)]
  rw [hsplit, add_comm, Nat.add_mul_mod_self_left]

/-- For `i ≤ 11`, `factDigit i n` depends only on `n` modulo `12!`. -/
theorem factDigit_mod_twelve {i : ℕ} (hi : i ≤ 11) (n : ℕ) :
    factDigit i n = factDigit i (n % (12)!) := by
  have hdvd : ((i + 1)! : ℕ) ∣ (12)! := Nat.factorial_dvd_factorial (by omega)
  rw [factDigit_mod i n, factDigit_mod i (n % (12)!), Nat.mod_mod_of_dvd n hdvd]

/-- If `2^d ≡ 1 (mod n)` and `d ∣ e`, then `2^e ≡ 1 (mod n)`. Two design points keep this
**evaluation-free**, dodging the `exponentiation.threshold` warning that an inlined literal
version trips: (1) the multiplier `k` from `d ∣ e` stays a *variable*, so the closing
`one_pow k` is symbolic — no concrete `1 ^ 540` is handed to the power evaluator; (2) the
conclusion is stated as `2^e`, so a caller's expected `2^1620` binds `e := 1620` by plain
unification rather than a defeq check `2^(d*k) =?= 2^1620` that would force `2^1620` to evaluate. -/
private theorem two_pow_modEq_one_of_dvd {d n e : ℕ} (h : (2 : ℕ) ^ d ≡ 1 [MOD n]) (hde : d ∣ e) :
    (2 : ℕ) ^ e ≡ 1 [MOD n] := by
  obtain ⟨k, rfl⟩ := hde
  calc (2 : ℕ) ^ (d * k) = ((2 : ℕ) ^ d) ^ k := by rw [pow_mul]
    _ ≡ 1 ^ k [MOD n] := h.pow k
    _ = 1 := one_pow k

/-- `2^1620 ≡ 1 (mod 467775)`, proved **kernel-pure via CRT** (no `native_decide`).
`467775 = 3^5 · 5^2 · 7 · 11 = 243 · 25 · 7 · 11` (pairwise coprime); `ord(2)` modulo each
prime power is `162, 20, 3, 10`, each dividing `1620`. The four small `decide`s are kernel
computations; the combine is `Nat.modEq_and_modEq_iff_modEq_mul`. -/
private theorem two_pow_1620_odd : (2 : ℕ) ^ 1620 % 467775 = 1 := by
  have h243 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 243] :=
    two_pow_modEq_one_of_dvd (by decide : (2 : ℕ) ^ 162 ≡ 1 [MOD 243]) (by norm_num)
  have h25 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 25] :=
    two_pow_modEq_one_of_dvd (by decide : (2 : ℕ) ^ 20 ≡ 1 [MOD 25]) (by norm_num)
  have h7 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 7] :=
    two_pow_modEq_one_of_dvd (by decide : (2 : ℕ) ^ 3 ≡ 1 [MOD 7]) (by norm_num)
  have h11 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 11] :=
    two_pow_modEq_one_of_dvd (by decide : (2 : ℕ) ^ 10 ≡ 1 [MOD 11]) (by norm_num)
  have c1 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 243 * 25] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨h243, h25⟩
  have c2 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 243 * 25 * 7] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨c1, h7⟩
  have c3 : (2 : ℕ) ^ 1620 ≡ 1 [MOD 243 * 25 * 7 * 11] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨c2, h11⟩
  rw [show (243 * 25 * 7 * 11 : ℕ) = 467775 by norm_num] at c3
  -- `c3 : 2^1620 % 467775 = 1 % 467775`; `1 % 467775` is defeq `1`.
  exact c3

/-- `2^(10+k) mod 12! = 1024 · (2^k mod 467775)` (since `12! = 1024 · 467775`). -/
private theorem two_pow_split (k : ℕ) : (2 : ℕ) ^ (10 + k) % (12)! = 1024 * (2 ^ k % 467775) := by
  have h12 : ((12)! : ℕ) = 1024 * 467775 := by decide
  rw [h12, pow_add, show (2 : ℕ) ^ 10 = 1024 by norm_num, Nat.mul_mod_mul_left]

/-- `2^m mod 12!` has period `1620` (on the `+10`-shifted exponent). -/
private theorem two_pow_period (k : ℕ) :
    (2 : ℕ) ^ (10 + (k + 1620)) % (12)! = (2 : ℕ) ^ (10 + k) % (12)! := by
  have hinner : (2 : ℕ) ^ (k + 1620) % 467775 = 2 ^ k % 467775 := by
    rw [pow_add, Nat.mul_mod, two_pow_1620_odd, mul_one]
    omega
  rw [two_pow_split (k + 1620), two_pow_split k, hinner]

/-- Drop full periods: `2^(10 + (1620·j + k)) ≡ 2^(10+k)  (mod 12!)`. -/
private theorem two_pow_drop (j k : ℕ) :
    (2 : ℕ) ^ (10 + (1620 * j + k)) % (12)! = (2 : ℕ) ^ (10 + k) % (12)! := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [show 1620 * (n + 1) + k = (1620 * n + k) + 1620 by ring,
        two_pow_period (1620 * n + k), ih]

/-- Reduce any `m ≥ 10` to the base window `[10, 1630)` modulo `12!`. -/
private theorem two_pow_reduce {m : ℕ} (hm : 10 ≤ m) :
    (2 : ℕ) ^ m % (12)! = (2 : ℕ) ^ (10 + (m - 10) % 1620) % (12)! := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 10 + k := ⟨m - 10, by omega⟩
  conv_lhs => rw [show k = 1620 * (k / 1620) + k % 1620 from (Nat.div_add_mod k 1620).symm]
  rw [two_pow_drop]
  simp_all

-- Base window (one full period): every `m ∈ [10, 1630)` has an offending factorial digit of
-- `2^m` (resp. `2^m - 1`) at an index in `[1, 11]`. Proved **kernel-pure** (no `native_decide`):
-- a flat `decide` over the 1620 residues `2^m mod 12!`, kept below `12!` via `r ↦ 2r mod 12!`.

/-- `offendingB r`: does `r` carry a factorial-base digit `≥ 2` at some index `1..11`? -/
private def offendingB (r : ℕ) : Bool := (List.range 11).any (fun j => 2 ≤ factDigit (j + 1) r)

/-- The residue-advance map `r ↦ (2r) mod 12!`. -/
private def adv (r : ℕ) : ℕ := (2 * r) % 479001600

/-- Flat fold: `offendingB` holds on the next `fuel` residues starting from `r`. -/
private def checkAll : ℕ → ℕ → Bool
  | 0,        _ => true
  | fuel + 1, r => offendingB r && checkAll fuel (adv r)

/-- Sub-companion: `offendingB` on `r - 1`, encoded as `(r + 12! - 1) mod 12!`. -/
private def checkAllSub : ℕ → ℕ → Bool
  | 0,        _ => true
  | fuel + 1, r => offendingB ((r + 479001599) % 479001600) && checkAllSub fuel (adv r)

/-- Balanced (divide-and-conquer) checker: `seg d r` examines the block of `2^d` consecutive
residues starting at `r`, returning whether they are all `offendingB` together with the residue
reached after `2^d` advances. Recursion is on the depth `d`, so the kernel evaluates `seg d r`
with reduction depth `O(d)` rather than `O(2^d)` — the linear `checkAll fuel r` blows the default
`maxRecDepth` at `fuel = 1620`, whereas `seg 11` (covering `2048 ≥ 1620` residues) stays shallow. -/
private def seg : ℕ → ℕ → Bool × ℕ
  | 0,     r => (offendingB r, adv r)
  | d + 1, r =>
    let p := seg d r
    let q := seg d p.2
    (p.1 && q.1, q.2)

/-- Sub-companion of `seg`, evaluating `offendingB` on the `(· - 1)`-encoded residue at each
leaf. -/
private def segSub : ℕ → ℕ → Bool × ℕ
  | 0,     r => (offendingB ((r + 479001599) % 479001600), adv r)
  | d + 1, r =>
    let p := segSub d r
    let q := segSub d p.2
    (p.1 && q.1, q.2)

/-- `offendingB r = true` with `n ≡ r (mod 12!)` yields the digit witness for `n`
(using that `factDigit i` for `i ≤ 11` only sees `n mod 12!`). -/
private theorem offendingB_to_exists {n r : ℕ} (hr : n % 479001600 = r)
    (h : offendingB r = true) : ∃ i ∈ Finset.Icc 1 11, 2 ≤ factDigit i n := by
  unfold offendingB at h
  rw [List.any_eq_true] at h
  obtain ⟨j, hjm, hj⟩ := h
  rw [List.mem_range] at hjm
  rw [decide_eq_true_eq] at hj
  refine ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [factDigit_mod_twelve (by omega : j + 1 ≤ 11),
      (by decide : Nat.factorial 12 = 479001600), hr]
  exact hj

/-- The `k`-th advance of `2^10 mod 12!` is `2^(10+k) mod 12!`. -/
private theorem res_pow (k : ℕ) : adv^[k] 1024 = 2 ^ (10 + k) % 479001600 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, adv,
        show (2 : ℕ) ^ (10 + (n + 1)) = 2 * 2 ^ (10 + n) from by ring,
        Nat.mul_mod 2 (2 ^ (10 + n)) 479001600]

private theorem checkAll_true {fuel r : ℕ} (h : checkAll fuel r = true) :
    ∀ k, k < fuel → offendingB (adv^[k] r) = true := by
  induction fuel generalizing r with
  | zero => intro k hk; omega
  | succ n ih =>
    rw [checkAll, Bool.and_eq_true] at h
    intro k hk
    cases k with
    | zero => simpa using h.1
    | succ k => rw [Function.iterate_succ_apply]; exact ih h.2 k (by omega)

private theorem checkAllSub_true {fuel r : ℕ} (h : checkAllSub fuel r = true) :
    ∀ k, k < fuel → offendingB ((adv^[k] r + 479001599) % 479001600) = true := by
  induction fuel generalizing r with
  | zero => intro k hk; omega
  | succ n ih =>
    rw [checkAllSub, Bool.and_eq_true] at h
    intro k hk
    cases k with
    | zero => simpa using h.1
    | succ k => rw [Function.iterate_succ_apply]; exact ih h.2 k (by omega)

/-- `(n - 1) mod 12! = (n mod 12! + (12!-1)) mod 12!` for `n ≥ 1`. -/
private theorem sub_res {n : ℕ} (hn : 1 ≤ n) :
    (n - 1) % 479001600 = (n % 479001600 + 479001599) % 479001600 := by
  conv_lhs => rw [← Nat.add_mod_right (n - 1) 479001600]
  rw [show n - 1 + 479001600 = n + 479001599 from by omega, Nat.add_mod,
      Nat.mod_eq_of_lt (by norm_num : (479001599 : ℕ) < 479001600)]

/-- The residue reached after a `seg`-block of depth `d` is `adv` iterated `2^d` times. -/
private theorem seg_snd (d : ℕ) (r : ℕ) : (seg d r).2 = adv^[2 ^ d] r := by
  induction d generalizing r with
  | zero => simp [seg]
  | succ n ih =>
    rw [seg]
    simp only []
    rw [ih, ih, pow_succ, Nat.mul_two, Function.iterate_add_apply]

/-- A `true` depth-`d` `seg`-block certifies `offendingB` on each of its `2^d` residues. -/
private theorem seg_true {d r : ℕ} (h : (seg d r).1 = true) :
    ∀ k, k < 2 ^ d → offendingB (adv^[k] r) = true := by
  induction d generalizing r with
  | zero =>
    intro k hk
    interval_cases k
    simpa [seg] using h
  | succ n ih =>
    rw [seg] at h
    simp only [Bool.and_eq_true] at h
    intro k hk
    rw [pow_succ, Nat.mul_two] at hk
    rcases Nat.lt_or_ge k (2 ^ n) with hlt | hge
    · exact ih h.1 k hlt
    · obtain ⟨j, rfl⟩ : ∃ j, k = 2 ^ n + j := ⟨k - 2 ^ n, by omega⟩
      rw [add_comm, Function.iterate_add_apply, ← seg_snd n r]
      exact ih h.2 j (by omega)

/-- The residue reached after a `segSub`-block of depth `d` is `adv` iterated `2^d` times
(the `.2` field tracks the same forward advance as `seg`). -/
private theorem segSub_snd (d : ℕ) (r : ℕ) : (segSub d r).2 = adv^[2 ^ d] r := by
  induction d generalizing r with
  | zero => simp [segSub]
  | succ n ih =>
    rw [segSub]
    simp only []
    rw [ih, ih, pow_succ, Nat.mul_two, Function.iterate_add_apply]

/-- A `true` depth-`d` `segSub`-block certifies `offendingB` on the `(· - 1)`-encoded residues. -/
private theorem segSub_true {d r : ℕ} (h : (segSub d r).1 = true) :
    ∀ k, k < 2 ^ d → offendingB ((adv^[k] r + 479001599) % 479001600) = true := by
  induction d generalizing r with
  | zero =>
    intro k hk
    interval_cases k
    simpa [segSub] using h
  | succ n ih =>
    rw [segSub] at h
    simp only [Bool.and_eq_true] at h
    intro k hk
    rw [pow_succ, Nat.mul_two] at hk
    rcases Nat.lt_or_ge k (2 ^ n) with hlt | hge
    · exact ih h.1 k hlt
    · obtain ⟨j, rfl⟩ : ∃ j, k = 2 ^ n + j := ⟨k - 2 ^ n, by omega⟩
      have hsplit : adv^[2 ^ n + j] r = adv^[j] (segSub n r).2 := by
        rw [segSub_snd n r, Nat.add_comm, Function.iterate_add_apply]
      simp_all

private theorem base_offending :
    ∀ m ∈ Finset.Ico 10 1630, ∃ i ∈ Finset.Icc 1 11, 2 ≤ factDigit i (2 ^ m) := by
  have key : (seg 11 1024).1 = true := by decide
  have key' : ∀ k, k < 1620 → offendingB (adv^[k] 1024) = true := fun k hk =>
    seg_true key k (by omega)
  intro m hm
  rw [Finset.mem_Ico] at hm
  obtain ⟨k, rfl⟩ : ∃ k, m = 10 + k := ⟨m - 10, by omega⟩
  have ho := key' k (by omega)
  rw [res_pow] at ho
  exact offendingB_to_exists rfl ho

private theorem base_offending_sub :
    ∀ m ∈ Finset.Ico 10 1630, ∃ i ∈ Finset.Icc 1 11, 2 ≤ factDigit i (2 ^ m - 1) := by
  have key : (segSub 11 1024).1 = true := by decide
  have key' : ∀ k, k < 1620 →
      offendingB ((adv^[k] 1024 + 479001599) % 479001600) = true := fun k hk =>
    segSub_true key k (by omega)
  intro m hm
  rw [Finset.mem_Ico] at hm
  obtain ⟨k, rfl⟩ : ∃ k, m = 10 + k := ⟨m - 10, by omega⟩
  have ho := key' k (by omega)
  rw [res_pow, ← sub_res Nat.one_le_two_pow] at ho
  exact offendingB_to_exists rfl ho

/-- **Fixed-modulus kill (heart of Phase C).** For every `m ≥ 8`, `2^m` carries a factorial-base
digit `≥ 2` at some positive index — so `2^m` is not a sum of distinct factorials. -/
theorem two_pow_offending {m : ℕ} (hm : 8 ≤ m) : ∃ i, 1 ≤ i ∧ 2 ≤ factDigit i (2 ^ m) := by
  rcases Nat.lt_or_ge m 10 with h9 | h10
  · interval_cases m
    · exact ⟨2, by norm_num, by decide⟩
    · exact ⟨5, by norm_num, by decide⟩
  · obtain ⟨i, hi_mem, hi_d⟩ :=
      base_offending (10 + (m - 10) % 1620)
        (Finset.mem_Ico.mpr ⟨by omega,
          by have := Nat.mod_lt (m - 10) (show 0 < 1620 by norm_num); omega⟩)
    rw [Finset.mem_Icc] at hi_mem
    refine ⟨i, hi_mem.1, ?_⟩
    rwa [factDigit_mod_twelve hi_mem.2 (2 ^ m), two_pow_reduce h10,
        ← factDigit_mod_twelve hi_mem.2 (2 ^ (10 + (m - 10) % 1620))]

/-- The `2^m - 1` companion of `two_pow_offending`. -/
theorem two_pow_sub_one_offending {m : ℕ} (hm : 8 ≤ m) :
    ∃ i, 1 ≤ i ∧ 2 ≤ factDigit i (2 ^ m - 1) := by
  rcases Nat.lt_or_ge m 10 with h9 | h10
  · interval_cases m
    · exact ⟨3, by norm_num, by decide⟩
    · exact ⟨5, by norm_num, by decide⟩
  · obtain ⟨i, hi_mem, hi_d⟩ :=
      base_offending_sub (10 + (m - 10) % 1620)
        (Finset.mem_Ico.mpr ⟨by omega,
          by have := Nat.mod_lt (m - 10) (show 0 < 1620 by norm_num); omega⟩)
    rw [Finset.mem_Icc] at hi_mem
    refine ⟨i, hi_mem.1, ?_⟩
    have key : (2 ^ m - 1) % (12)! = (2 ^ (10 + (m - 10) % 1620) - 1) % (12)! := by
      have hbase := two_pow_reduce h10
      have hNval : ((12)! : ℕ) = 479001600 := by decide
      have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have hr1 : 1 ≤ 2 ^ (10 + (m - 10) % 1620) := Nat.one_le_two_pow
      rw [hNval] at hbase ⊢
      omega
    rwa [factDigit_mod_twelve hi_mem.2 (2 ^ m - 1), key,
        ← factDigit_mod_twelve hi_mem.2 (2 ^ (10 + (m - 10) % 1620) - 1)]

/-- **Phase C complete.** No sum of distinct factorials equals `2^m` for `m ≥ 8`. -/
theorem factSum_ne_of_ge_eight {m : ℕ} (hm : 8 ≤ m) (S : Finset ℕ) : factSum S ≠ 2 ^ m :=
  not_factSum_of_digits (2 ^ m) (two_pow_offending hm) (two_pow_sub_one_offending hm) S

/-! ## The headline theorems (FNS route, fully sorry-free)

The fixed-modulus kill makes the entire 2-adic carry machinery (`cascade_*`, `tied_*`) unnecessary:
`factSum_ne_of_ge_eight` gives `m ≤ 7` directly, and finiteness follows from the size sandwich
`M! ≤ 2^m ≤ 2^7`. -/

/-- **Erdős #403 (sharp form)** — the largest power of two that is a sum of distinct factorials is
`2⁷ = 2! + 3! + 5! = 128`. Every solution has `m ≤ 7`. -/
theorem erdos_403_sharp {S : Finset ℕ} {m : ℕ} (h : factSum S = 2 ^ m) : m ≤ 7 := by
  by_contra hc
  exact factSum_ne_of_ge_eight (by omega) S h

/-- **Erdős #403 (finiteness)** — exactly what the problem asks: only finitely many sums of
distinct factorials are powers of two. By `erdos_403_sharp`, every solution has `m ≤ 7`, so
`M! ≤ 2^m ≤ 128` forces `max' S ≤ 5`; hence every solution lives in `(range 6).powerset`. -/
theorem erdos_403_finite :
    {S : Finset ℕ | ∃ m : ℕ, factSum S = 2 ^ m}.Finite := by
  apply Set.Finite.subset ((Finset.range 6).powerset : Finset (Finset ℕ)).finite_toSet
  intro S hS
  obtain ⟨m, hm⟩ := hS
  have hne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | h
    · rw [factSum, Finset.sum_empty] at hm
      exact absurd hm.symm (pow_ne_zero m two_ne_zero)
    · exact h
  have hm7 : m ≤ 7 := erdos_403_sharp hm
  have hfac : (S.max' hne)! ≤ 2 ^ m := by rw [← hm]; exact factorial_max_le_factSum hne
  have hMle : S.max' hne ≤ 5 := by
    by_contra hc
    have h6 : (6 : ℕ)! ≤ (S.max' hne)! := Nat.factorial_le (by omega)
    have h2 : (2 : ℕ) ^ m ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hm7
    rw [show (6 : ℕ)! = 720 by decide] at h6
    omega
  refine Finset.mem_coe.mpr (Finset.mem_powerset.mpr (fun a ha => ?_))
  exact Finset.mem_range.mpr (by have := S.le_max' a ha; omega)

end Erdos403
