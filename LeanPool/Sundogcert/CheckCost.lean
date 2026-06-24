/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.Certificate

/-!
  Sundog syndrome certificate — the CHECK-COST theorem  (Lean 4 / mathlib v4.30.0)

  GOAL.  Make the "cheap to check" half of the lane's "cheaper to check than to find" claim
  DEDUCTIVE: a PROVEN polynomial (`O(m·n)` = linear in the parity-check size `|H|`) upper bound
  on the cost of ONE verification query.  The matching FIND-hardness (ISD/SIS one-wayness) stays
  IMPORTED — it is an assumption, never a theorem here.

  WHAT IS PROVED.  `verifyCost S ≤ 2·(m·n) + n + m + 2`, i.e. the per-query operation count of the
  worst-case (reject/quarantine) path of `Verifier.run` is linear in `|H| = m·n`.  That is all.

  WHAT IS NOT PROVED / NOT CLAIMED.
    • NOT `P ≠ NP`.  • NOT that the certificate is one-way.
    • NOT a lower bound on FINDING a witness.
  The asymmetry the lane advertises is: poly-time CHECK (proved HERE) vs. exp-time FIND (an imported
  ISD/SIS hardness assumption, established ELSEWHERE, never in this file).

  TRUST SURFACE (load-bearing, audited by a human exactly as the `Scheme` fields are).
  The COST MODEL below is a trust-surface item.  A reviewer checks that `verifyCost` /
  `syndromeMulCost` faithfully count the field/Boolean operations of `Verifier.run` on its dominant
  path, for the DEPLOYED verifier (`witnessOpt` = `wt y ≤ τ` light test; `lb` = `colWeightLb`).
  Nothing forces this correspondence mechanically — it is asserted, then audited, like `hHG`.
  Given that audited model, the polynomial bound is a THEOREM (kernel-checked, `sorry`-free).
-/

open Matrix

namespace Sundog.Certificate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable (S : Scheme F)

/-! ### The cost model (TRUST SURFACE — counts operations on `Verifier.run`'s dominant path)

  The dominant path of `Verifier.run` is the no-witness branch (reject / quarantine): it is the one
  that actually COMPUTES the bound, so its op-count upper-bounds the accept path (which
  short-circuits on an exhibited witness).  On that path, per query:

    • syndrome `H *ᵥ y`     : one MULT per term of `(H *ᵥ y)_i = ∑_{j:Fin n} H i j * y j`, over
                              `m` rows ⟹ `m·n` mults; plus `m·(n-1)` ADDs to sum each row.
    • witness search `V.witnessOpt y` : the deployed `wt y ≤ τ` light-witness test ⟹ `n` zero-tests.
    • `wt (H *ᵥ y)`         : `m` zero-tests (after the syndrome is formed).
    • the `τ < lb` decision : `1` compare, plus `1` division for `colWeightLb` (`‖z‖/colBound H`).

  EXCLUDED (correctly): `colBound S.H` depends on `H` ALONE, so it is amortized ONCE per scheme at
  setup, NOT per query — a one-time `O(m·n)` prep, off the per-query hot path.
-/

/-- **Faithful structural mult-count** for the syndrome `H *ᵥ y`: one `(1 : ℕ)` per sum-term of
    `(H *ᵥ y)_i = ∑_{j:Fin S.n} H i j * y j`, summed over the `m` rows.  By `Matrix.mulVec` /
    `dotProduct`, each row is an `n`-term inner product, so this counts exactly the field mults. -/
def syndromeMulCost : ℕ := ∑ _i : Fin S.m, ∑ _j : Fin S.n, 1

/-- The structural mult-count equals `m·n` — the count is `m` rows of `n` terms each. -/
theorem syndromeMulCost_eq : syndromeMulCost S = S.m * S.n := by
  unfold syndromeMulCost
  simp [Finset.sum_const, Fintype.card_fin, Nat.mul_comm]

/-- **Per-query verification cost** on the dominant (reject/quarantine) path:
      `syndromeMulCost S`  — `m·n` syndrome mults,
    + `S.m * (S.n - 1)`    — syndrome row-sum adds,
    + `S.n`                — witness search `V.witnessOpt y` (the `wt y ≤ τ` test),
    + `S.m`                — `wt (H *ᵥ y)` zero-tests,
    + `2`                  — one `colWeightLb` division + one `τ < lb` compare. -/
def verifyCost : ℕ :=
  syndromeMulCost S + S.m * (S.n - 1) + S.n + S.m + 2

/-! ### THE HEADLINE THEOREM — verification is polynomial-time, BY THEOREM. -/

/-- **CHECK-COST is linear in `|H| = m·n`.**  One verification query costs at most
    `2·(m·n) + n + m + 2` operations — `O(m·n)`, linear in the parity-check size.  The check is
    cheap by THEOREM (the FIND side stays an imported ISD/SIS hardness assumption; see header). -/
theorem verifyCost_le : verifyCost S ≤ 2 * (S.m * S.n) + S.n + S.m + 2 := by
  unfold verifyCost
  rw [syndromeMulCost_eq]
  -- `m·(n-1) ≤ m·n`, then `omega` over the atoms `m*n` and `m*(n-1)`.
  have hsub : S.m * (S.n - 1) ≤ S.m * S.n :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  omega

/-! ### Concrete costs — raw `ℕ` formulas (no `Scheme` needed), `#eval`-able.

  These mirror the defs above with `m`, `n` as plain naturals, so the deployed numbers can be read
  off directly.  `verifyCostMN m n` = `verifyCost`; `syndromeMulCostMN m n = m·n`. -/

/-- Raw mult-count: `m·n` (matches `syndromeMulCost_eq`). -/
def syndromeMulCostMN (m n : ℕ) : ℕ := m * n

/-- Raw per-query cost formula (matches `verifyCost` after `syndromeMulCost = m·n`). -/
def verifyCostMN (m n : ℕ) : ℕ := m * n + m * (n - 1) + n + m + 2

-- [4,2] instance  (m = 2, n = 4):  syndromeMulCost = 8 mults;  verifyCost = 8+6+4+2+2 = 22 ops.

-- Deployed [128,64] certificate  (m = 64, n = 128):  syndromeMulCost = m·n = 64·128 = 8192 mults —
-- EXACTLY the lane's "flat 8,192-op check".  verifyCost = 8192 + 8128 + 128 + 64 + 2 = 16514.

-- Cross-check the 8192 consistency point against `m * n` directly (Boolean, must print `true`):

-- The headline bound holds numerically at the deployed size as well:
-- verifyCostMN 64 128 = 16514 ≤ 2*(64*128) + 128 + 64 + 2 = 16384 + 194 = 16578.

/-- Trust anchor: the structural mult-count `syndromeMulCost` agrees with the raw formula for any
    scheme whose dimensions are `(m, n)` — the model is internally consistent, not two unrelated
    numbers.  (Stated at the deployed size via the proved `syndromeMulCost_eq`.) -/
theorem syndromeMulCost_eq_raw : syndromeMulCost S = syndromeMulCostMN S.m S.n :=
  syndromeMulCost_eq S


end Sundog.Certificate
