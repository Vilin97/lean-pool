/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Egrs75.CentralBinomialDigits
import Mathlib.Data.Set.Finite.Basic

/-!
EGRS75 two-prime infinitude — strategy + defs scaffold.

Erdős–Graham–Ruzsa–Straus 1975, "On the prime factors of binomial coefficients"
(Math. Comput. 29 (1975) 83–92).

TARGET (`egrs_two_prime`): for distinct odd primes `p q`,
  `{n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite`.

This file performs the BRIDGE REDUCTION only. It assembles the single-base
Kummer→digit characterisation we already hold KERNEL-CLEAN in
  ConstructProofs/Erdos376Bridge.lean      (`coprime_centralBinom_prime_iff`)
  ConstructProofs/ConcreteMath/KummerBridge.lean
into the predicate `LowDigits p n` ("every base-`p` digit of `n` is `≤ (p-1)/2`"),
proves `¬ p ∣ Nat.centralBinom n ↔ LowDigits p n` (kernel-clean), and reduces the
target to the CRUX `egrs_crux`:
  `{n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite`.

The crux is the genuine theorem (counting-exponent density argument:
θ_p + θ_q > 1 for all distinct odd p,q) and is left as the single labelled
`sorry`. Three primes is Erdős #376 (OPEN) — do NOT attempt here.

Recon / context: MATH CONTEXT block in the run prompt; #376 recon at
  ~/Knowledge/Construct/recon/erdos_376.md
DO NOT reprove Kummer — reuse the imports below.
-/

namespace Egrs75

open Nat

/-! ## The digit predicate -/

/-- `LowDigits p n`: every base-`p` digit of `n` is `≤ (p-1)/2`.
This is the Kummer no-carry condition for doubling `n` in base `p`
(`p ∤ C(2n,n)`). For an **odd** prime `p`, `d ≤ (p-1)/2 ↔ 2*d < p`, so it is
the same predicate as #376's `LowDoubleDigits p n := ∀ d ∈ digits p n, 2*d < p`
(see `lowDigits_iff_lowDoubleDigits` below). -/
def LowDigits (p n : ℕ) : Prop := ∀ d ∈ Nat.digits p n, d ≤ (p - 1) / 2

/-- For an **odd** prime `p`, the per-digit bound `2*d < p` (the #376 form, i.e.
"doubling produces no carry") is equivalent to `d ≤ (p-1)/2` (the `LowDigits`
form). The hypotheses are stated per-digit so the lemma threads through the
`∀ d ∈ digits p n` quantifier. -/
lemma digit_le_half_iff_two_mul_lt {p d : ℕ} (hp2 : 2 ≤ p) (hpodd : Odd p) :
    d ≤ (p - 1) / 2 ↔ 2 * d < p := by
  obtain ⟨k, hk⟩ := hpodd
  -- p = 2k+1, so (p-1)/2 = k and the claim is `d ≤ k ↔ 2*d < 2k+1 ↔ 2*d ≤ 2k`.
  subst hk
  have hhalf : (2 * k + 1 - 1) / 2 = k := by
    have : 2 * k + 1 - 1 = 2 * k := by omega
    rw [this]; exact Nat.mul_div_cancel_left k (by decide)
  rw [hhalf]; omega

/-- `LowDigits` and #376's `LowDoubleDigits` coincide for odd primes. -/
theorem lowDigits_iff_lowDoubleDigits {p n : ℕ} (hp2 : 2 ≤ p) (hpodd : Odd p) :
    LowDigits p n ↔ Egrs75.Erdos376.LowDoubleDigits p n := by
  unfold LowDigits Egrs75.Erdos376.LowDoubleDigits
  constructor
  · intro h d hd; exact (digit_le_half_iff_two_mul_lt hp2 hpodd).mp (h d hd)
  · intro h d hd; exact (digit_le_half_iff_two_mul_lt hp2 hpodd).mpr (h d hd)

/-! ## The single-base bridge (KERNEL-CLEAN — assembled from #376)

`coprime_centralBinom_prime_iff` (Erdos376Bridge) gives, for any prime `p`:
  `Coprime (centralBinom n) p ↔ LowDoubleDigits p n`.
We turn `Coprime _ p` into `¬ p ∣ _` and `LowDoubleDigits` into `LowDigits`
(odd prime), yielding the single-base fact we already hold. -/

/-- **EGRS single-base bridge.** For an **odd prime** `p`,
`p ∤ C(2n,n)` exactly when every base-`p` digit of `n` is `≤ (p-1)/2`.
Kernel-clean: assembled from `coprime_centralBinom_prime_iff` + odd-prime digit
arithmetic. This is the per-prime Kummer fact the two-prime target stands on. -/
theorem not_dvd_centralBinom_iff_lowDigits {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (n : ℕ) : ¬ p ∣ Nat.centralBinom n ↔ LowDigits p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hcop := Egrs75.Erdos376.coprime_centralBinom_prime_iff (p := p) n
  -- `Coprime (centralBinom n) p ↔ ¬ p ∣ centralBinom n`
  have hnotdvd : Nat.Coprime (Nat.centralBinom n) p ↔ ¬ p ∣ Nat.centralBinom n := by
    rw [Nat.coprime_comm]; exact hp.coprime_iff_not_dvd
  rw [← hnotdvd, hcop, ← lowDigits_iff_lowDoubleDigits hp2 hpodd]

end Egrs75
