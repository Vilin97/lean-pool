/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Egrs75.MuFinish
import Mathlib.Tactic.NormNum.Prime

/-!
EGRS75 two-prime closure — NO-VACUITY SMOKE PROBE (2026-06-12).

Instantiates the closed theorem `MuFinish.egrs_two_prime_mu` at the three
smallest odd-prime pairs.  Purpose: machine-check that the hypotheses are
satisfiable (no hidden vacuity) and that the closure is usable downstream.
All three MUST be kernel-clean.
-/

namespace Egrs75.SmokeProbe

open Egrs75.MuFinish

/-- Infinitely many `n` with `3 ∤ C(2n,n)` and `5 ∤ C(2n,n)`. -/
theorem egrs_3_5 : {n : ℕ | ¬ 3 ∣ Nat.centralBinom n ∧ ¬ 5 ∣ Nat.centralBinom n}.Infinite :=
  egrs_two_prime_mu (by norm_num) (by norm_num) ⟨1, rfl⟩ ⟨2, rfl⟩ (by norm_num)

/-- Infinitely many `n` with `3 ∤ C(2n,n)` and `7 ∤ C(2n,n)`. -/
theorem egrs_3_7 : {n : ℕ | ¬ 3 ∣ Nat.centralBinom n ∧ ¬ 7 ∣ Nat.centralBinom n}.Infinite :=
  egrs_two_prime_mu (by norm_num) (by norm_num) ⟨1, rfl⟩ ⟨3, rfl⟩ (by norm_num)

/-- Infinitely many `n` with `5 ∤ C(2n,n)` and `7 ∤ C(2n,n)`. -/
theorem egrs_5_7 : {n : ℕ | ¬ 5 ∣ Nat.centralBinom n ∧ ¬ 7 ∣ Nat.centralBinom n}.Infinite :=
  egrs_two_prime_mu (by norm_num) (by norm_num) ⟨2, rfl⟩ ⟨3, rfl⟩ (by norm_num)

/-- **Comparator challenge form (2026-06-12).**  Byte-identical to the statement
in `comparator/egrs75/Challenge.lean` (the leanprover/comparator workspace shipped
with this development): Mathlib-vocabulary only, no project definitions.  If this
compiles clean, the comparator `Solution` bridge does too. -/
theorem egrs_two_prime_challenge_form {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite :=
  egrs_two_prime_mu hp hq hpo hqo hpq

end Egrs75.SmokeProbe
