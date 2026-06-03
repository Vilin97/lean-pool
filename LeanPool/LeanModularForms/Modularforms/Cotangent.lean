/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# Cotangent series expansion

All of the lemmas formerly defined here — `Complex.cot_eq_exp_ratio`,
`Complex.cot_pi_eq_exp_ratio`, `pi_mul_cot_pi_q_exp`, the `sinTerm`/`cotTerm` series,
`tendsto_logDeriv_euler_*`, `cot_series_rep`/`cot_series_rep'`, and the lemmas building
up to them — have been upstreamed into
`Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent`.  This file is now a
re-export so the historical import path continues to work.

The two downstream consumers in this project (`Modularforms/summable_lems.lean`) already
import the upstream module directly and resolve `cot_series_rep'` and
`pi_mul_cot_pi_q_exp` against Mathlib's versions.
-/
