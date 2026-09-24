/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

module

public import LeanPool.BlockSpectralSensitivity.Main

/-!
# Block sensitivity can exceed spectral sensitivity squared

Source: arxiv:2608.00851, url:https://github.com/Timeroot/BS_Lam/tree/7bd39a8d41ee7910d3296d0477ad18f8fff9d870
Authors: Alex Meiburg
Status: verified
Main declarations: `BSLambda.Final.exists_bs_gt_lam_rpow`
Tags: boolean-functions, complexity, probabilistic-method
MSC: 68Q17, 05D40, 05C50
-/

/-!
## Scope and provenance

Adapted from Alex Meiburg's `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`, under Apache-2.0.
Upstream's `formalization.yaml` records AI-written proofs produced using Claude Code and
Harmonic ATP from the author's manuscript `bs_lambda.txt`. The import preserves the complete
mathematical dependency closure, with updated module exports, API repairs, and proof optimization.

The seed has `bs(f) ≥ 14011` and `lambda(f)^2 ≤ 7149 + 2 sqrt(150108)`.
The explicit certified separation is `lambda(f)^2.12 < bs(f)`; the exact logarithmic exponent
is retained without a claimed decimal evaluation. `exists_ratio_blowup` states the
multiplicative inequality for every iterate, with `ratio_gt` giving a factor above `1.768`.
The paper's numerical searches and separate thirty-variable example are outside this import.
-/
