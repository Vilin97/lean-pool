/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/

import LeanPool.Feige.MainTheorem

/-!
# Feige's sharp unit-slack inequality

Source: arxiv:2607.23980
Authors: Zhengqing Zhou
Status: verified
Main declarations: `Feige.sharp_unit_slack_feige_complete`
Tags: probability, concentration-inequalities, convex-geometry, sharp-constants
MSC: 60E15, 52A20
-/

/-!
## Mathematical overview

For every positive fixed dimension `n`, this development proves that independent,
integrable, nonnegative random variables with coordinatewise means at most one satisfy

`P[∑ i, X i < E[∑ i, X i] + 1] ≥ (n / (n + 1)) ^ n`,

and that the constant is optimal. The proof formalizes the Vlassis--Thomas exact
distribution-free calibration theorem, the required Grünbaum centroid-halfspace
inequality and its sharp simplex case, and the normalized-exponential bridge assembling
them into the probability bound.

The public theorem is the `δ = 1` specialization of Theorem 1.1 in the source paper.
The imported snapshot is otherwise assumption-free beyond Lean and Mathlib's standard
logical foundations; the formalization is restricted to positive finite dimensions and
small-universe probability spaces.

## Provenance

Imported from <https://github.com/pengzhang91/Feige> at commit
`98ab466e74280ae9d40622c19dc7f24f01b60864`; ported from Lean v4.31.0 to Lean Pool's
v4.34.0-rc1. Source files retain their upstream OpenAI copyright headers where present;
the remaining files fall under the repository-wide Zhengqing Zhou and contributors
notice.
-/
