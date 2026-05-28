/-
Copyright (c) 2026 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/

import LeanPool.Duality.Common
import LeanPool.Duality.ExtendedFields
import LeanPool.Duality.FarkasBartl
import LeanPool.Duality.FarkasBasic
import LeanPool.Duality.FarkasSpecial
import LeanPool.Duality.LinearProgramming
import LeanPool.Duality.LinearProgrammingB

/-!
# Duality theory in linear optimization and its extensions

Source: arxiv:2409.08119
Authors: Martin Dvorak
Status: verified
Main declarations: `extendedFarkas`, `StandardLP.strongDuality`
Tags: linear-programming, optimization, farkas-lemma
MSC: 90C05, 90C46
-/

/-!
## Mathematical overview

Farkas established that a system of linear inequalities has a solution if and only if we cannot
obtain a contradiction by taking a linear combination of the inequalities. Several Farkas-like
theorems are stated and formally proved in Lean 4. Furthermore, we consider a linearly ordered
field extended with two special elements denoted by `⊥` and `⊤`, where `⊥` is below every
element and `⊤` is above every element. We define `⊥ + a = ⊥ = a + ⊥` for all `a` and we
define `⊤ + b = ⊤ = b + ⊤` for all `b ≠ ⊥`. Instead of multiplication, we define scalar
action `c • ⊥ = ⊥` for every `c ≥ 0` but we define `d • ⊤ = ⊤` only for `d > 0` because
`0 • ⊤ = 0`. We extend certain Farkas-like theorems to a setting where coefficients are from
an extended linearly ordered field.

Main corollaries:
- `equalityFarkas`: Farkas for equalities,
- `inequalityFarkas`: Farkas for inequalities,
- `StandardLP.strongDuality`: strong duality for standard LP.

Main results:
- `finFarkasBartl` / `fintypeFarkasBartl`: Farkas–Bartl theorem,
- `extendedFarkas`: extended Farkas theorem,
- `ValidELP.strongDuality`: strong duality for extended LP.

## Provenance

Imported from <https://github.com/madvorak/duality> (originally Lean v4.18.0) and ported to
Lean Pool's v4.30.0-rc2 / Mathlib v4.30.0-rc2 toolchain. Technical report:
<https://arxiv.org/abs/2409.08119>.
-/
