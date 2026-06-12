/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import LeanPool.Sensitivity.Defs
import LeanPool.Sensitivity.Basic
import LeanPool.Sensitivity.Multilinear
import LeanPool.Sensitivity.Subcube
import LeanPool.Sensitivity.Parity
import LeanPool.Sensitivity.HuangBridge
import LeanPool.Sensitivity.Main
import LeanPool.Sensitivity.Consequences

/-!
# Sensitivity Conjecture: sqrt(deg) <= sensitivity

Source: arxiv:1907.00847, doi:10.4007/annals.2019.190.3.6
Authors: Samuel Schlesinger
Status: verified
Main declarations: `LeanPoolSensitivity.sensitivity_ge_sqrt_degree`
Tags: combinatorics, boolean-functions, computational-complexity
MSC: 06E30, 68Q17
-/

/-!
## Mathematical overview

For a Boolean function `f : (Fin n → Bool) → Bool`, the *sensitivity* `s(f)`
is the maximum, over all inputs `x`, of the number of coordinates `i` at
which flipping bit `i` changes the value of `f`. The *multilinear degree*
`deg(f)` is the maximum cardinality of a set `S ⊆ Fin n` whose Möbius
coefficient in the multilinear polynomial representing `f` is nonzero.

This project formalises the quantitative form of the Nisan–Szegedy/Huang
sensitivity conjecture: for every Boolean function `f` with `deg(f) ≥ 1`,
`√(deg(f)) ≤ s(f)`. Squaring this inequality recovers the corollary
`deg(f) ≤ s(f)²`. The argument restricts `f` to a subcube of dimension
`deg(f)` on which the top Möbius coefficient is preserved, derives a
parity-sign imbalance there, and feeds the result into the Huang hypercube
lemma `Sensitivity.huang_degree_theorem` from `Mathlib`'s
`Archive.Sensitivity`.

The exported modules follow the proof structure: core definitions
(`LeanPool.Sensitivity.Defs`, `LeanPool.Sensitivity.Basic`), the multilinear
representation (`LeanPool.Sensitivity.Multilinear`), restrictions to subcubes
(`LeanPool.Sensitivity.Subcube`), the parity imbalance lemma
(`LeanPool.Sensitivity.Parity`), the bridge to Mathlib's Huang theorem
(`LeanPool.Sensitivity.HuangBridge`), the main bound
`LeanPoolSensitivity.sensitivity_ge_sqrt_degree`
(`LeanPool.Sensitivity.Main`), and the corollary
`LeanPoolSensitivity.degree_le_sensitivity_sq`
(`LeanPool.Sensitivity.Consequences`).

## Provenance

Imported from <https://github.com/SamuelSchlesinger/sensitivity-conjecture>.
Upstream contains no `sorry`s. Ported from Lean v4.28.0 to Lean Pool's
v4.30.0-rc2. The upstream `Sensitivity` namespace has been renamed to
`LeanPoolSensitivity` to avoid polluting Mathlib's `Sensitivity` namespace,
which is used by `Archive.Sensitivity` for the underlying Huang lemma.
-/
