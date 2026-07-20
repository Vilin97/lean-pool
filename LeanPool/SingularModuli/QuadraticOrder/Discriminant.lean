/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/

import LeanPool.SingularModuli.QuadraticOrder.Norm

/-!
# The discriminant identity `(τ − tauConj)² = d`

**Thesis.** §3.2, the discriminant of the order: for an honest discriminant
`d` (i.e. `d ≡ 0, 1 (mod 4)`), `(τ − tauConj)² = d`.

**This file proves:**

* `tau_sub_tauConj`               — `τ − tauConj = 2τ − d`
* `tau_sub_tauConj_sq`            — the general identity, valid for *all* `d`
* `tau_sub_tauConj_sq_of_valid_disc` — specialises to `(τ − tauConj)² = d` when
  `d ≡ 0 ∨ 1 (mod 4)` (the case used in the thesis)

**Divergence from thesis.** The thesis only ever needs `(τ − tauConj)² = d` because
it assumes `d` is a discriminant. Because `QuadraticOrder d` is defined for all
`d` here (see `Basic.lean`), the honest general identity carries the Euclidean
remainder term: `(τ − tauConj)² = (d² − 4⌊(d²−d)/4⌋) • 1`, which collapses to `d`
exactly under the congruence hypothesis. The general form
`tau_sub_tauConj_sq` is a Lean-only artifact with no thesis counterpart.
-/

namespace QuadraticOrder

variable {d : ℤ}

/-! ### Discriminant: `(τ - tauConj)²` -/

/-- The difference of the two roots: `τ - tauConj = 2 • τ - d • 1`. -/
lemma tau_sub_tauConj : tau - tauConj = 2 • tau - d • (1 : QuadraticOrder d) := by
  unfold tauConj
  abel

/-- General discriminant identity: `(τ - tauConj)² = (d² - 4·⌊(d²-d)/4⌋) • 1`. The
right-hand-side equals `d • 1` when `d ≡ 0` or `d ≡ 1 (mod 4)` (the values
for which `poly d` has integer coefficients matching the discriminant of the
quadratic field). For general `d`, the difference is the Euclidean remainder
`(d² - d) mod 4`. -/
lemma tau_sub_tauConj_sq :
    (tau - tauConj) ^ 2
      = (d ^ 2 - 4 * ((d ^ 2 - d) / 4) : ℤ) • (1 : QuadraticOrder d) := by
  have h := tau_minimal_poly (d := d)
  rw [tau_sub_tauConj]
  -- (2 • τ - d • 1)^2 = 4 • τ² - 4d • τ + d² • 1
  -- substitute τ² = d • τ - q • 1, giving d² • 1 - 4q • 1 = (d² - 4q) • 1
  linear_combination (4 : QuadraticOrder d) * h

/-- Under the valid-discriminant hypothesis `d ≡ 0 ∨ d ≡ 1 (mod 4)`, the
discriminant equals `d` exactly: `(τ - tauConj)² = d • 1`. This is the case used
throughout the thesis (the only `d` for which `QuadraticOrder d` coincides
with the quadratic order of discriminant `d`). -/
lemma tau_sub_tauConj_sq_of_valid_disc
    (hd : d % 4 = 0 ∨ d % 4 = 1) :
    (tau - tauConj) ^ 2 = d • (1 : QuadraticOrder d) := by
  rw [tau_sub_tauConj_sq]
  congr 1
  -- reduce to: d^2 - 4 * ((d^2 - d) / 4) = d
  -- equivalently: 4 ∣ (d^2 - d), so 4 * ((d^2-d)/4) = d^2 - d
  have h4dvd := dvd_four_of_valid_disc hd
  have hcancel : (4 : ℤ) * ((d ^ 2 - d) / 4) = d ^ 2 - d :=
    Int.mul_ediv_cancel' h4dvd
  linarith

end QuadraticOrder
