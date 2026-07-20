/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/

import LeanPool.SingularModuli.QuadraticOrder.Basic

/-!
# The norm form on `O_d`

**Thesis.** §3.2, the norm form `N(a + bτ) = a² + d·a·b + ((d² − d)/4)·b²`
and its multiplicativity (this is the norm used throughout the ideal-counting
of §3.1–§3.3).

**This file proves:**

* `normForm`            — the integer norm form `N(a, b)`
* `normForm_mul`        — multiplicativity `N(αβ) = N(α)·N(β)`
* `tauConj`             — the Galois conjugate `tauConj = d − τ` (other root of `poly d`)
* `tau_add_tauConj` / `tau_mul_tauConj` — the Vieta relations
* `normForm_eq_mul_conj`— `(a + bτ)(a + btauConj) = N(a, b)`

**Divergence from thesis.** The thesis states `N(a + bτ)` directly as a
quadratic form. Here it is *derived* and shown multiplicative through the
Galois conjugate `tauConj` and the Vieta relations `τ + tauConj = d`, `τ·tauConj = (d²−d)/4`,
which exhibit `N` as an honest multiplicative norm `α ↦ α·alphaConj`. The end formula
agrees with the thesis; the route via `tauConj` is a Lean-idiomatic
reformulation.
-/

namespace QuadraticOrder

variable {d : ℤ}

/-! ### Norm form -/

/-- The norm form on `QuadraticOrder d`: the norm of `a + b·τ` is
`a² + d·a·b + ((d²-d)/4)·b²`.

Derivation: N(a + bτ) = (a + bτ)(a + b(d - τ)), using the fact that
`τ` and `d - τ` are the two roots of `X² - dX + (d²-d)/4`.
Expanding: a² + ab(d - τ) + abτ + b²τ(d - τ) = a² + abd + b²·τ(d-τ).
Since τ² - dτ + (d²-d)/4 = 0, we have τ(d - τ) = (d²-d)/4, giving the formula. -/
noncomputable def normForm (d a b : ℤ) : ℤ :=
  a ^ 2 + d * a * b + ((d ^ 2 - d) / 4) * b ^ 2

/-- The norm form is multiplicative: N(αβ) = N(α)·N(β).

This follows from the ring-identity that holds for any integers a, b, c, e, d,
and any integer q substituted for (d²-d)/4. -/
theorem normForm_mul (a b c e : ℤ) :
    normForm d (a * c - ((d ^ 2 - d) / 4) * (b * e)) (a * e + b * c + d * b * e) =
    normForm d a b * normForm d c e := by
  simp only [normForm]
  set q := (d ^ 2 - d) / 4
  ring

/-! ### Conjugate and norm involution

The element `tauConj := d • 1 - tau` is the "Galois conjugate" of `tau`: it is
the other root of `poly d`. Together with `tau`, it satisfies the standard
Vieta relations, and exhibits `normForm` as a multiplicative norm via the
factorisation `(a + b·τ)(a + b·tauConj) = N(a, b)`. -/

/-- The Galois conjugate of `tau`: the other root of `poly d`. -/
noncomputable def tauConj : QuadraticOrder d := d • (1 : QuadraticOrder d) - tau

/-- Vieta: the sum of the roots of `poly d` equals `d`. -/
lemma tau_add_tauConj : tau + tauConj = d • (1 : QuadraticOrder d) := by
  unfold tauConj
  ring

/-- Vieta: the product of the roots of `poly d` equals `(d^2 - d) / 4`. -/
lemma tau_mul_tauConj :
    tau * tauConj = ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) := by
  unfold tauConj
  have h := tau_minimal_poly (d := d)
  -- `tau * (d • 1 - tau) = d • tau - tau^2`, and `tau^2 = d • tau - q • 1`.
  linear_combination -h

/-- The conjugate `tauConj` is also a root of the defining polynomial `poly d`. -/
lemma tauConj_minimal_poly :
    tauConj ^ 2 - d • tauConj + ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) = 0 := by
  unfold tauConj
  have h := tau_minimal_poly (d := d)
  linear_combination h

/-- The Galois conjugate `tauConj` is also a root of `poly d`. -/
@[simp] lemma poly_aeval_tauConj :
    Polynomial.aeval (tauConj (d := d)) (poly d) = 0 := by
  have h := tauConj_minimal_poly (d := d)
  simp only [poly, map_sub, map_add, map_mul, map_pow,
             Polynomial.aeval_X, Polynomial.aeval_C,
             Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact h

/-- The norm involution: `(a + b·τ)(a + b·tauConj) = N(a, b)`. This exhibits the
conjugate as the involution under which `normForm` is the multiplicative norm. -/
lemma normForm_eq_mul_conj (a b : ℤ) :
    (a • (1 : QuadraticOrder d) + b • tau)
      * (a • (1 : QuadraticOrder d) + b • tauConj)
    = (normForm d a b) • (1 : QuadraticOrder d) := by
  have hsum : tau + tauConj = d • (1 : QuadraticOrder d) := tau_add_tauConj
  have hprod : tau * tauConj = ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) :=
    tau_mul_tauConj
  simp only [normForm, zsmul_eq_mul] at hsum hprod ⊢
  push_cast
  linear_combination
    ((b : QuadraticOrder d) * (a : QuadraticOrder d)) * hsum
      + ((b : QuadraticOrder d) ^ 2) * hprod

end QuadraticOrder
