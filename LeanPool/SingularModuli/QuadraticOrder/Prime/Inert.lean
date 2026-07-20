/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/

import LeanPool.SingularModuli.QuadraticOrder.Prime.QuotientIso

/-!
# Prime classification, part 3: the inert case

**Thesis.** §3.2, Proposition 3.2.1 — the *inert* branch: a rational prime `p`
remains prime in `O_d` exactly when the Legendre symbol `(d/p) = -1`.

**This file proves:**

* `span_p_isMaximal_iff_irreducible_polyMod` — `(p)` maximal ↔ `polyMod d p`
  irreducible (the ideal ↔ polynomial transport)
* `prime_inert_iff` — `(p)` maximal ↔ `(d/p) = -1`

**Divergence from thesis.** Maximality of `(p)` is obtained by transporting
`IsField` across `quadraticOrderModPEquivPolyModQuot` (see `QuotientIso.lean`)
rather than via the thesis's direct index computation in `ℤ/pᵏ[x]/g(x)`.
-/

open Polynomial

namespace QuadraticOrder

/-- The ideal `(p)` in `QuadraticOrder d` is maximal iff `polyMod d p` is
irreducible in `(ZMod p)[X]`. This is the ideal-theoretic inert
characterisation: `(p)` is maximal — equivalently, `(p)` does not factor in
`QuadraticOrder d` — exactly when its mod-`p` polynomial form is irreducible
over `ZMod p`.

Combined with `polyMod_splits_iff_legendreSym_ne_neg_one` (and the field
structure on `(ZMod p)[X] / (irreducible)`), this connects the Legendre
symbol `(d/p) = -1` characterisation to the ring-theoretic notion that
`(p)` remains prime in `QuadraticOrder d`. -/
theorem span_p_isMaximal_iff_irreducible_polyMod
    (d : ℤ) (p : ℕ) [Fact p.Prime] :
    (Ideal.span {(p : QuadraticOrder d)}).IsMaximal ↔ Irreducible (polyMod d p) := by
  constructor
  · intro hMax
    -- Transport maximality through the ring equiv to get maximality of
    -- `Ideal.span {polyMod d p}` in `(ZMod p)[X]`.
    have hField :
        IsField (QuadraticOrder d ⧸ Ideal.span {(p : QuadraticOrder d)}) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hMax
    have hField' :
        IsField ((ZMod p)[X] ⧸ Ideal.span {polyMod d p}) :=
      (quadraticOrderModPEquivPolyModQuot d p).symm.toMulEquiv.isField hField
    have hMax' : (Ideal.span {polyMod d p}).IsMaximal :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hField'
    -- IsMaximal → IsPrime → Prime → Irreducible (using `polyMod` is nonzero).
    have hne : (polyMod d p) ≠ 0 := (polyMod_monic d p).ne_zero
    have hPrime : Prime (polyMod d p) :=
      (Ideal.span_singleton_prime hne).mp hMax'.isPrime
    exact hPrime.irreducible
  · intro hIrred
    -- `(ZMod p)[X]` is a PID, so irreducible generates a maximal ideal.
    have hMax' : (Ideal.span {polyMod d p}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hIrred
    have hField' :
        IsField ((ZMod p)[X] ⧸ Ideal.span {polyMod d p}) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hMax'
    -- Transport `IsField` back through the ring equiv.
    have hField :
        IsField (QuadraticOrder d ⧸ Ideal.span {(p : QuadraticOrder d)}) :=
      (quadraticOrderModPEquivPolyModQuot d p).toMulEquiv.isField hField'
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hField

variable {d : ℤ} {p : ℕ}

/-- **Issue #7's inert iff at the ideal level**: the ideal `(p)` is maximal
in `QuadraticOrder d` (i.e. `p` is "inert") iff the Legendre symbol
`(d/p) = -1`. Direct composition of `span_p_isMaximal_iff_irreducible_polyMod`
with `polyMod_irreducible_iff_legendreSym_eq_neg_one`. -/
theorem prime_inert_iff
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1) :
    (Ideal.span {(p : QuadraticOrder d)}).IsMaximal ↔ legendreSym p d = -1 := by
  rw [span_p_isMaximal_iff_irreducible_polyMod,
      polyMod_irreducible_iff_legendreSym_eq_neg_one hp2 hd]

end QuadraticOrder
