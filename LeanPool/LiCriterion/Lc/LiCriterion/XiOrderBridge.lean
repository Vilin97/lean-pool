/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
module


public import LeanPool.LiCriterion.Lc.LiCriterion.RHBridge
public import LeanPool.LiCriterion.Lc.LiCriterion.XiGrowth

/-!
# The ξ order bridge — the last analytic input to the unconditional Li criterion

`LiCriterion.biconditional_rh_li_of_hadamard_order_one` (in `Lc/LiCriterion/RHBridge.lean`)
already reduces the full Li ↔ RH equivalence to exactly two facts about the completed
`riemannXi`:

* it is an entire function of finite order, and
* its order is at most `1`.

Everything else on the analytic side is *proved*, not assumed: the general genus-1 Hadamard
factorization theorem (`Hadamard.hadamard_factorization_general`), its full specialization to
`riemannXi` (`LiCriterion.xi_hadamard_factorization_with_multiplicity`), and the genus-1
`1/‖ρ‖²` summability are all discharged inside that bridge. So the two lemmas below are the
*only* remaining analytic inputs standing between this development and an unconditional Li
criterion.

Both are now **proved**, in `Lc/LiCriterion/XiGrowth.lean`, so `li_criterion_rh_iff` below is
unconditional and depends on the standard axioms alone (`propext`, `Classical.choice`,
`Quot.sound`).

## How the two bridge lemmas are proved

Not through `ξ = ½ s (s-1) π^{-s/2} Γ(s/2) ζ(s)`: that route owes a polynomial bound for `ζ` in
the critical strip, which is not in Mathlib.  Instead, `XiGrowth.lean` uses the Mellin
representation that Mathlib already builds `completedRiemannZeta₀` from,

  `completedRiemannZeta₀ s = (mellin f_modif (s/2)) / 2`,

with `f_modif` the modified theta kernel of `HurwitzZeta.hurwitzEvenFEPair 0`.  The kernel decays
exponentially at `∞`, and its functional equation transports that decay to `0`; bounding the
Mellin integral against the two exponentials gives `‖ξ(s)‖ ≤ exp (O (‖s‖ log ‖s‖))` for every `s`,
with no case split on the strip and no appeal to Stirling.  See the module docstring there.
-/

@[expose] public section

namespace LiCriterion

open Complex

/-- **BRIDGE 1.** `riemannXi` is an entire function of finite order.

Classical fact: ξ has order exactly `1`; only `≤` is needed, and only that is proved. -/
theorem xi_hasFiniteOrder : Hadamard.hasFiniteOrder riemannXi :=
  XiGrowth.riemannXi_hasFiniteOrder

/-- **BRIDGE 2.** The order of `riemannXi` is at most `1`.

Proved in `XiGrowth.lean` from the Mellin representation of `completedRiemannZeta₀` and the
exponential decay of the theta kernel. -/
theorem xi_order_le_one : Hadamard.order riemannXi ≤ 1 :=
  XiGrowth.riemannXi_order_le_one

/-- **Li's criterion for the Riemann zeta function (unconditional).**

The Riemann Hypothesis (Mathlib's `RiemannHypothesis`) holds if and only if every Li–Keiper
coefficient of `riemannXi` — the `n`-th Taylor coefficient at `0` of the logarithmic derivative
of `s ↦ riemannXi (1/(1-s))` — has nonnegative real part.

This is `biconditional_rh_li_of_hadamard_order_one` with its two order inputs discharged. -/
theorem li_criterion_rh_iff :
    RiemannHypothesis ↔ (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re) :=
  biconditional_rh_li_of_hadamard_order_one xi_hasFiniteOrder xi_order_le_one

end LiCriterion
