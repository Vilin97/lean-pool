/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/
import Mathlib.Basic.Real.Basic

/-!
# The abstract damped ladder

This file defines the rung weights `w_m` and the structure `Ladder`: a family `N : ℕ → ℕ → ℝ` of
nonnegative reals that is bounded by a total mass `M` at rung `0`, starts empty above every rung
`m ≥ 1`, and obeys a damped one-step recursion. It contains no Pauli operators; it is the
interface between the Pauli model and the quantitative bounds.

The quantitative core of the LPD truncation analysis is not quantum. The high-weight norm is the
normalized Pauli 2-norm of a restricted coefficient vector
(`apd:eq:def_high_weight_norm`):

  `N_{≥m}^{(g)} := ‖O^{(g)}_{≥ w_m + 1}‖_{2,normalized} = sqrt(∑_{w > w_m}
  ‖O^{(g)}_{=w}‖_{2,normalized}²)`,

and the damped local norm flow lemma (`apd:thm:local_flow_k_local`) says only

  `N_{≥m}^{(g)} ≤ N_{≥m}^{(g-1)} + sin(dt) · N_{≥m-1}^{(g-1)}`.

Everything downstream — the binomial cumulation, the multi-jump majorant, the entry and part
factors, and the threshold `t₀` — follows from that inequality alone. The recursion is therefore
packaged as a structure on an abstract family `N : ℕ → ℕ → ℝ`, and its consequences are proved
with no Pauli infrastructure at all.

This separates the quantitative recursion from the Pauli model, so that each can be checked
independently. The files under `Ladder/` and `Constants/` are elementary real analysis and
combinatorics. `Lean4LPD/Pauli/Flow.lean` proves that the Pauli model satisfies the fields
(`PauliString.pauliLadder`), and `Lean4LPD/Pauli/Truncate.lean` does the same with truncations
interleaved (`PauliString.pauliLadderTrunc`). Measuring the high-weight part by one 2-norm is
what makes the fields provable: the rung-`0` bound is unitary invariance of that norm, and the
step inequality is its triangle inequality applied to the part that stays above the rung and the
inflow from the rung below.

## Main definitions

* `rungWeight`: the rung weight `w_m = k_o + (m-1)(k_h-1)`.
* `Ladder`: the damped ladder with damping factor `a` and total mass `M`.
-/

namespace Lean4LPD

/-- The rung weight `w_m := k_o + (m-1)(k_h - 1)`: the largest Pauli weight reachable by
`m-1` anticommuting `k_h`-local rotations starting from a `k_o`-local observable. The paper
defines it alongside `apd:eq:def_high_weight_norm`.

This is only used for the *interpretation* of the ladder; the abstract results never evaluate
it. In particular nothing relies on `rungWeight ko kh 0`, which `ℕ` truncated subtraction makes
`ko` rather than the intended `ko - (kh - 1)`. Rung `0` is instead treated as a distinguished
reservoir; see `Ladder.reservoir`.

That choice matters for correctness, not only for tidiness. The Pauli model wants
`w_0 = w_1 - (k_h-1) = k_o - (k_h-1)`, and truncated subtraction gives `k_o`, which would make
`N 0` too *small* — the direction that breaks `step` at `m = 1`, since `N 0 g` sits on its
right-hand side. With rung `0` distinguished, the model (`PauliString.ladderN`) sets
`N 0 g := ‖O^{(g)}‖_{2,normalized} = ‖O‖_{2,normalized}`, satisfies `reservoir` with equality,
makes `step` at `m = 1`
weaker than the true flow bound and hence implied by it, and reads only real rungs at `m ≥ 2`. -/
def rungWeight (ko kh m : ℕ) : ℕ := ko + (m - 1) * (kh - 1)

@[simp] lemma rungWeight_one (ko kh : ℕ) : rungWeight ko kh 1 = ko := by
  simp [rungWeight]

/-- A **damped ladder** with damping factor `a` and total mass `M`.

`N m g` is the mass strictly above rung `m` after `g` steps. Rung `0` is the *reservoir*: it
holds everything, bounded by the total mass `M`. Reading rung `0` this way, rather than
computing `rungWeight ko kh 0`, is what makes the recursion at `m = 1` be its own base case,
and sidesteps `ℕ` truncated subtraction.

The fields are exactly the hypotheses the Pauli model supplies:

* `reservoir` — unitary invariance of the 2-norm, `N_{≥0}^{(l)} ≤ ‖O^{(l)}‖ = ‖O‖`, for every
  `l` (with truncations interleaved the last equality becomes `≤`). It holds because the
  high-weight functional is a single 2-norm (`apd:eq:def_high_weight_norm`), and it is the base
  case of `apd:cor:norm_cumulation_jump`.
* `init` — the input observable is `k_o`-local, so no mass sits above rung `m ≥ 1` at `g = 0`.
* `step` — the damped local norm flow lemma `apd:thm:local_flow_k_local`. Truncation only
  decreases every `N m`, so the recursion holds along the whole LPD trajectory with truncations
  interleaved. -/
structure Ladder (a M : ℝ) where
  /-- Mass strictly above rung `m` after `g` steps. -/
  N : ℕ → ℕ → ℝ
  nonneg : ∀ m g, 0 ≤ N m g
  reservoir : ∀ g, N 0 g ≤ M
  init : ∀ m, 1 ≤ m → N m 0 = 0
  step : ∀ m g, 1 ≤ m → N m (g + 1) ≤ N m g + a * N (m - 1) g

end Lean4LPD
