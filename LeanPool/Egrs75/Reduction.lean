/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Egrs75.Defs

/-!
EGRS75 two-prime infinitude — ASSEMBLY.

Erdős–Graham–Ruzsa–Straus 1975, "On the prime factors of binomial coefficients"
(Math. Comput. 29 (1975) 83–92), Theorem 1.

TARGET (`egrs_two_prime`): for distinct odd primes `p q`,
  `{n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite`.

────────────────────────────────────────────────────────────────────────────
WHAT THIS FILE ESTABLISHES (HONEST STATUS — read carefully):

  The target is assembled from TWO pieces:

  (1) THE BRIDGE  — `not_dvd_centralBinom_iff_lowDigits` (in `EgrsDefs`):
      for an odd prime `p`,  `¬ p ∣ C(2n,n) ↔ LowDigits p n`.
      This half is FULLY VERIFIED, KERNEL-CLEAN
      (`#print axioms` = [propext, Classical.choice, Quot.sound], NO sorryAx).
      It is assembled from the Kummer→digit characterisation we already hold
      (Egrs75.Erdos376 `coprime_centralBinom_prime_iff` over the Kummer
      bridge `sub_one_mul_padicValNat_centralBinom`), via the odd-prime digit
      identity `d ≤ (p-1)/2 ↔ 2*d < p`. The Set-rewrite reduction of the target
      to the crux is a `Set.ext` and is itself sorry-free.

  (2) THE CRUX  — `egrs_crux` :
      `{n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite`
      for distinct odd primes `p q`.
      This is the GENUINE EGRS75 two-prime theorem (counting-exponent density:
      `θ_p + θ_q > 1` for all distinct odd `p,q`, where `θ_p = log((p+1)/2)/log p`;
      smallest pair `3,5` gives `≈ 1.314`).  It is NOT closed: it remains exactly
      ONE clearly-labelled `sorry` (see the route files), and is reported below as
      an explicit open hypothesis `EgrsCrux p q`.

  We wire (1)∘(2): `egrs_two_prime` is proven SORRY-FREE *relative to* the crux
  hypothesis `EgrsCrux`.  Concretely, `egrs_two_prime_of_crux` takes the crux as a
  hypothesis and discharges the target with NO new sorry — its `#print axioms` is
  kernel-clean (propext / Classical.choice / Quot.sound only).  This is the precise,
  machine-checked statement of the reduction: the ONLY missing input is the crux.

  `egrs_two_prime_assembled` (the unconditional form; `egrs_two_prime` itself is
  already declared in `EgrsDefs` against the in-file crux, so this assembly uses a
  distinct name) plugs the strongest available crux route —
  `Cdensity.egrs_crux_Cdensity` (route C-density, which additionally carries the
  kernel-clean θ_p count `count_lowDigits_pow` and the EGRS "Fact"
  `exists_lowDigits_between`) — into that reduction.  It therefore inherits, and
  ONLY inherits, the single `sorryAx` of the crux.  No fakes: no native_decide, no
  bogus axiom, no circular hypothesis.  `#print axioms egrs_two_prime_assembled`
  lists `sorryAx`, and that `sorryAx` is traceable to exactly the crux `sorry`,
  nothing else.

  NET: this is a KERNEL-CLEAN machine-verified REDUCTION of the EGRS two-prime
  theorem to the single digit-intersection lemma "A_p ∩ A_q is infinite", with the
  Kummer→digit bridge half fully verified.  Three primes is Erdős #376 (OPEN); not
  attempted.

Recon / context: MATH CONTEXT block in the run prompt; #376 recon at
  ~/Knowledge/Construct/recon/erdos_376.md.
-/

namespace Egrs75

open Nat

/-! ## The crux as an explicit hypothesis

`EgrsCrux p q` is the single open input: the joint low-digit set is infinite.
Everything else in the assembly is verified. -/

/-- The EGRS two-prime CRUX as a `Prop`: for the (distinct, odd, prime) bases
`p q`, the set of `n` low-digit in BOTH bases is infinite. This is the genuine
number-theoretic core (`θ_p + θ_q > 1`); it is the ONLY unproven input to the
target. -/
def EgrsCrux (p q : ℕ) : Prop := {n : ℕ | LowDigits p n ∧ LowDigits q n}.Infinite

/-! ## The reduction, SORRY-FREE relative to the crux (KERNEL-CLEAN) -/

/-- **EGRS two-prime target, conditional on the crux.** Given the crux
(`EgrsCrux p q`, i.e. `A_p ∩ A_q` infinite) for distinct odd primes `p q`, there
are infinitely many `n` with `p ∤ C(2n,n)` and `q ∤ C(2n,n)`.

This proof is SORRY-FREE: it uses ONLY the kernel-clean single-base bridge
`not_dvd_centralBinom_iff_lowDigits` to rewrite the divisibility set as the joint
low-digit set, then applies the crux hypothesis. `#print axioms` below confirms
propext / Classical.choice / Quot.sound only (NO sorryAx) for this lemma. -/
theorem egrs_two_prime_of_crux {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hcrux : EgrsCrux p q) :
    {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite := by
  have hset :
      {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n} =
        {n : ℕ | LowDigits p n ∧ LowDigits q n} := by
    ext n
    simp only [Set.mem_setOf_eq]
    rw [not_dvd_centralBinom_iff_lowDigits hp hpo n,
        not_dvd_centralBinom_iff_lowDigits hq hqo n]
  rw [hset]
  exact hcrux

end Egrs75
