/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Nicholas Bulka
-/
import LeanPool.LiCriterion.comparator.ChallengeDeps
import LeanPool.LiCriterion.Lc.LiCriterion.Fidelity

/-!
Solution.lean — the UNTRUSTED comparator solution module: the statement of `Challenge.lean`,
byte-identical, PROVED by delegating to the LiCriterion library.

  li_criterion
    → LiCriterion.li_criterion_rh_iff
      (Lc/LiCriterion/XiOrderBridge.lean)

  li_coefficients_eq_zero_sum
    → LiCriterion.summable_li_symmetrized ∧ LiCriterion.taylorCoeff_eq_li_symmetrized
      (Lc/LiCriterion/Fidelity.lean)

The challenge definitions in `ChallengeDeps.lean` (`riemannXi`, `taylorCoeff`, and the helpers
`phi`, `logDeriv`) are character-for-character the library's (`LiCriterion.riemannXi`,
`LiCriterion.taylorCoeff`, `LiCriterion.phi`, `LiCriterion.logDeriv`), so the delegation
typechecks by definitional unfolding in the kernel even though the challenge copies live in the
`LiChallenge` namespace.

Nothing in this file is part of the trusted base: the comparator re-checks that the theorems below
have exactly the statements of their `Challenge` namesakes and use only the permitted axioms.

STATUS: unconditional.  The two order inputs of `LiCriterion.li_criterion_rh_iff`
(`xi_hasFiniteOrder`, `xi_order_le_one`) are proved in `Lc/LiCriterion/XiGrowth.lean`, and
both compared theorems report `[propext, Classical.choice, Quot.sound]`.
-/

open LiChallenge

/-- **Li's criterion for the Riemann Hypothesis**, proved in
`LiCriterion.li_criterion_rh_iff`. -/
theorem li_criterion :
    RiemannHypothesis ↔ (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re) :=
  LiCriterion.li_criterion_rh_iff

/-- **Fidelity**: summability from `LiCriterion.summable_li_symmetrized`, the identity from
`LiCriterion.taylorCoeff_eq_li_symmetrized`. -/
theorem li_coefficients_eq_zero_sum (n : ℕ) :
    Summable (fun ρ : NontrivialZero =>
        (analyticOrderNatAt riemannXi ρ.val : ℂ) *
          ((1 - (1 - 1 / ρ.val) ^ (-((n : ℤ) + 1)))
            + (1 - (1 - 1 / ρ.val) ^ ((n : ℤ) + 1)))) ∧
    taylorCoeff riemannXi n
      = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero,
          (analyticOrderNatAt riemannXi ρ.val : ℂ) *
            ((1 - (1 - 1 / ρ.val) ^ (-((n : ℤ) + 1)))
              + (1 - (1 - 1 / ρ.val) ^ ((n : ℤ) + 1))) :=
  ⟨LiCriterion.summable_li_symmetrized n, LiCriterion.taylorCoeff_eq_li_symmetrized n⟩
