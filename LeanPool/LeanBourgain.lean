/-
Copyright (c) 2026 Command Master. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Command Master
-/

import LeanPool.LeanBourgain.Additive
import LeanPool.LeanBourgain.Incidence
import LeanPool.LeanBourgain.Util

/-!
# Lean Bourgain explicit constants

Source: url:https://github.com/Command-Master/lean-bourgain
Authors: Command Master
Status: verified
Main declarations: `LeanPool.LeanBourgain.pos_ST_prime_field_eps`, `LeanPool.LeanBourgain.ST_C_pos`
Tags: additive-combinatorics, sum-product, extractors
MSC: 11B30, 11T23, 68P30
-/

/-!
## Mathematical overview

The upstream Lean 4 project formalises Bourgain's two-source extractor (Bou05)
and the prime-field Szemerédi-Trotter theorem (BKT04), culminating in
`bourgain_extractor_final`: for every prime `p ≠ 2` and positive integer `m`,
the function `f(x, y) = (xy + x² y² mod p) mod m` is a two-source extractor with
explicit min-entropy and error parameters expressed in terms of the
sum-product and incidence schedules `SG_eps`, `ST_prime_field_eps`, the
numeric constants `SG_C₅, …, ST_C`, and the doubling-dependent `full_C` factor.

The Lean Pool vendoring captures the foundational analytical layer of the
proof:

* `LeanPool.LeanBourgain.Util` — generic floor/min/sum-card lemmas used
  throughout the proof.
* `LeanPool.LeanBourgain.Additive.Constants` — the doubling-dependent constant
  `full_C β` driving the sum-product iterations.
* `LeanPool.LeanBourgain.Incidence.Constants` — the explicit constants
  `SG_C₅, SG_C₄, …, ST_C` and epsilon schedules `SG_eps_i`,
  `ST_prime_field_eps_i`, together with the structural inequalities
  (`lemma1`–`lemma16`, `ntlSGeps`, `ntlSGeps'`, `full_C_neq_zero`,
  `pos_ST_prime_field_eps`, `one_le_SG_C₃`, `one_le_ST_C₃`, `ST_C_pos`) that
  govern how these constants compare and combine in the proof of the main
  estimate.

## Provenance

Imported from <https://github.com/Command-Master/lean-bourgain>; the upstream
Lean v4.7.0 proof depends on the LeanAPAP library for its discrete Fourier
analysis (Lp-norms, DFT, convolution, BSG). Since Lean Pool's dependency set is
restricted to Mathlib, only the LeanAPAP-free fragment is vendored here: the
constants, epsilon schedules, and structural inequalities that parameterise
the analytic core of the proof. Ported from Lean v4.7.0 to Lean Pool's
v4.30.0-rc2.
-/
