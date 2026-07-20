/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/

import LeanPool.SingularModuli.QuadraticOrder.Prime.PolyMod

/-!
# Prime classification, part 2: the quotient ring isomorphism

**Thesis.** §3.2, the proof of Proposition 3.2.1 reasons about the quotient
`O/(p)` directly (in the thesis, via the presentation `ℤ/pᵏ[x]/g(x)` and
explicit index computations).

**This file proves the structural bridge:**

* `quadraticOrderModPEquivPolyModQuot` — `O/(p) ≅ 𝔽ₚ[X]/(polyMod d p)`
* `quadraticOrderModPEquivXSqQuot`   — in the ramified case (`p ∣ d`),
  `O/(p) ≅ 𝔽ₚ[X]/(X²)` (the dual numbers)

**Divergence from thesis.** This ring isomorphism is the central
reorganisation of the argument. The thesis manipulates `O/(p)` through the
concrete polynomial-quotient presentation and computes ideal indices by hand.
Here we instead transport *every* ideal-theoretic property of `(p) ⊆ O`
(maximality → inert, radicality → split, non-radicality → ramified) across this
single iso to the corresponding property of `(polyMod d p) ⊆ 𝔽ₚ[X]`, where the
field/PID structure of `𝔽ₚ[X]` does the work. The downstream files
(`Inert`, `Split`, `Ramified`) are thin wrappers over this transport. This is a
Lean-idiomatic route; the mathematical content matches Prop 3.2.1.
-/

open Polynomial

namespace QuadraticOrder

/-- The structural bridge: `QuadraticOrder d / (p)` is ring-equivalent to
`(ZMod p)[X] / (polyMod d p)`. This is the key isomorphism connecting
ideal-theoretic properties of `(p)` in `QuadraticOrder d` to polynomial-level
properties of `polyMod d p` in `(ZMod p)[X]`. It is the foundation on which
the inert/split/ramified ideal-theoretic characterisations are built. -/
noncomputable def quadraticOrderModPEquivPolyModQuot
    (d : ℤ) (p : ℕ) [Fact p.Prime] :
    (QuadraticOrder d ⧸ Ideal.span {(p : QuadraticOrder d)}) ≃+*
      ((ZMod p)[X] ⧸ Ideal.span {polyMod d p}) := by
  -- Step 1: rewrite `(p) ⊆ QuadraticOrder d` as the image under
  -- `algebraMap ℤ (QuadraticOrder d) = AdjoinRoot.of (poly d)` of `(p) ⊆ ℤ`.
  have h_span_eq : Ideal.span {(p : QuadraticOrder d)} =
      Ideal.map (AdjoinRoot.of (poly d)) (Ideal.span {(p : ℤ)}) := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  -- Step 2: the polynomial in the target ideal — after transport through
  -- `Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod p)` — coincides with
  -- `polyMod d p`. Uses `Polynomial.map_map` and
  -- `Int.quotientSpanNatEquivZMod_comp_Quotient_mk`.
  have h_poly_eq :
      (poly d).map ((Int.quotientSpanNatEquivZMod p : _ →+* _).comp
        (Ideal.Quotient.mk (Ideal.span {(p : ℤ)}))) = polyMod d p := by
    rw [Int.quotientSpanNatEquivZMod_comp_Quotient_mk]
    rfl
  have h_map_eq :
      (Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod p) : _ →+* _)
        ((poly d).map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)}))) =
        polyMod d p := by
    change (Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod p))
        ((poly d).map (Ideal.Quotient.mk _)) = polyMod d p
    rw [Polynomial.mapEquiv_apply, Polynomial.map_map, h_poly_eq]
  have h_map_span :
      Ideal.map (Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod p) : _ →+* _)
          (Ideal.span {(poly d).map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)}))}) =
        Ideal.span {polyMod d p} := by
    rw [Ideal.map_span, Set.image_singleton, h_map_eq]
  -- Step 3: compose `Ideal.quotEquivOfEq` with `AdjoinRoot.quotEquivQuotMap`
  -- and `Ideal.quotientEquiv` (the latter transports the polynomial quotient
  -- along the ring equiv `ℤ/(p) ≃+* ZMod p`).
  exact
    (Ideal.quotEquivOfEq h_span_eq).trans <|
      (AdjoinRoot.quotEquivQuotMap (poly d) (Ideal.span {(p : ℤ)})).toRingEquiv.trans <|
        Ideal.quotientEquiv _ (Ideal.span {polyMod d p})
          (Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod p)) h_map_span.symm

/-- **Ramified-case quotient isomorphism**: when `p ∣ d` (with the
discriminant hypothesis `d ≡ 0 ∨ 1 (mod 4)` and `p ≠ 2`), the quotient
`QuadraticOrder d / (p)` is isomorphic to `(ZMod p)[X] / (X²)`. This makes
the dual-numbers / non-reduced structure of the ramified branch explicit:
the image of `X` in this quotient is nilpotent of order 2, witnessing that
`(p)` is not a radical ideal in `QuadraticOrder d`. -/
noncomputable def quadraticOrderModPEquivXSqQuot
    (d : ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1)
    (hpd : (p : ℤ) ∣ d) :
    (QuadraticOrder d ⧸ Ideal.span {(p : QuadraticOrder d)}) ≃+*
      ((ZMod p)[X] ⧸ Ideal.span {(X ^ 2 : (ZMod p)[X])}) :=
  (quadraticOrderModPEquivPolyModQuot d p).trans <|
    Ideal.quotEquivOfEq <| by rw [polyMod_eq_X_sq_of_p_dvd_d hp2 hd hpd]

end QuadraticOrder
