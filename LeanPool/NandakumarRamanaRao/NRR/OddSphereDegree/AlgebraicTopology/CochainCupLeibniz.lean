/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.AlexanderWhitneyChainMap

/-!
# Cochain cup Leibniz identity and its descent consequences

This file records the cochain-level Leibniz / coboundary formula for the singular
cup product over `ZMod 2` and derives the immediate consequences needed to descend
the cup product to singular cohomology.

The headline identity itself,

```text
δ(φ ⌣ ψ) = δφ ⌣ ψ + φ ⌣ δψ (over `ZMod 2`)
```

is `aw_cochain_leibniz_zmod2` from `AlexanderWhitneyChainMap.lean`; here it is
restated as `cochainCupZMod2_differential`, and the following descent facts are
proved:

* `cochainCupZMod2_respects_cocycles` — the cup of two cocycles is a cocycle, so
 the cup product is defined on cocycle representatives;
* `cochainCupZMod2_coboundary_left` / `cochainCupZMod2_coboundary_right` — if one
 factor is a cocycle, the coboundary of the cup is the cup of that factor with
 the coboundary of the other (the cup of a cocycle with a coboundary is itself a
 coboundary, up to the degree relabelling cast);
* `cochainCupZMod2_coboundary_left'` / `cochainCupZMod2_coboundary_right'` — the
 same facts in the "is a coboundary" direction (`δη ⌣ ψ = cast (δ(η ⌣ ψ))`),
 exhibiting the cup with a coboundary explicitly as the coboundary of a cochain;
* `cochainCupZMod2_respects_coboundaries` — changing a cocycle factor by a
 coboundary changes the cup product by a coboundary, i.e. the cup product
 respects the cohomology equivalence relation at the cochain level.

Together these are exactly the inputs needed to define the cohomology-level cup
product `H^p(X; ZMod 2) × H^q(X; ZMod 2) → H^{p+q}(X; ZMod 2)`: the
cup descends to a well-defined bilinear pairing on cohomology classes.

## Degree bookkeeping

The `δφ ⌣ ψ` term naturally lives in degree `(p+1)+q` and the `φ ⌣ δψ` term in
degree `p+(q+1)`; both are transported to the common degree `(p+q)+1` via the
cochain degree cast `cochainCast` (with `p+(q+1) = (p+q)+1` definitional and
`(p+1)+q = (p+q)+1` propositional via `aw_degree_left_succ`).
-/

open CategoryTheory
open SphereOddDegree.AlexanderWhitney

namespace SphereOddDegree

/-! ## 0. Cast lemmas for the cochain degree cast -/

/-- The degree cast of the zero cochain is zero. -/
@[simp] theorem cochainCast_zero {R : Type} [CommRing R] {Z : TopCat.{0}} {m m' : ℕ}
    (h : m = m') :
    cochainCast (R := R) (Z := Z) h (0 : singularCochainGroup R Z m) = 0 := by
  unfold cochainCast; simp

/-- The degree cast is additive. -/
theorem cochainCast_add {R : Type} [CommRing R] {Z : TopCat.{0}} {m m' : ℕ} (h : m = m')
    (φ ψ : singularCochainGroup R Z m) :
    cochainCast h (φ + ψ) = cochainCast h φ + cochainCast h ψ := by
  unfold cochainCast; rw [Preadditive.comp_add]

/-- The degree cast along `h` followed by the cast along `h.symm` is the identity. -/
@[simp] theorem cochainCast_cast {R : Type} [CommRing R] {Z : TopCat.{0}} {m m' : ℕ}
    (h : m = m') (φ : singularCochainGroup R Z m) :
    cochainCast h.symm (cochainCast h φ) = φ := by
  unfold cochainCast
  rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-! ## 1. The Leibniz / coboundary identity (restated) -/

/-- **Cochain cup Leibniz identity over `ZMod 2`** (restatement of
`aw_cochain_leibniz_zmod2`). The cochain coboundary is a derivation for the cup
product:

```text
δ(φ ⌣ ψ) = δφ ⌣ ψ + φ ⌣ δψ.
```

The two right-hand terms, of degrees `(p+1)+q` and `p+(q+1)`, are transported to
the common degree `(p+q)+1` via the cochain degree cast. -/
theorem cochainCupZMod2_differential {X : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q φ ψ)
      = cochainCast (aw_degree_left_succ p q)
          (cochainCup (p + 1) q (cochainCoboundary (ZMod 2) X p φ) ψ)
        + cochainCast (aw_degree_right_succ p q)
            (cochainCup p (q + 1) φ (cochainCoboundary (ZMod 2) X q ψ)) :=
  aw_cochain_leibniz_zmod2 p q φ ψ

/-! ## 2. Cup of cocycles is a cocycle -/

/-- **The cup of two cocycles is a cocycle.** If `δφ = 0` and `δψ = 0` then
`δ(φ ⌣ ψ) = 0`. This is what makes the cup product defined on cocycle
representatives. -/
theorem cochainCupZMod2_respects_cocycles {X : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q φ ψ) = 0 := by
  rw [cochainCupZMod2_differential, hφ, hψ, cochainCup_zero_left, cochainCup_zero_right,
    cochainCast_zero, cochainCast_zero, add_zero]

/-! ## 3. Cup with a coboundary is a coboundary -/

/-- **Coboundary of a cup, left factor a cocycle.** If `δa = 0` then
`δ(a ⌣ ψ) = cast (a ⌣ δψ)`. Equivalently, the cup of the cocycle `a` with the
coboundary `δψ` is itself a coboundary. -/
theorem cochainCupZMod2_coboundary_right {X : TopCat.{0}} (p q : ℕ)
    (a : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q)
    (ha : cochainCoboundary (ZMod 2) X p a = 0) :
    cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q a ψ)
      = cochainCast (aw_degree_right_succ p q)
          (cochainCup p (q + 1) a (cochainCoboundary (ZMod 2) X q ψ)) := by
  rw [cochainCupZMod2_differential, ha, cochainCup_zero_left, cochainCast_zero, zero_add]

/-- **Coboundary of a cup, right factor a cocycle.** If `δψ = 0` then
`δ(η ⌣ ψ) = cast (δη ⌣ ψ)`. Equivalently, the cup of the coboundary `δη` with the
cocycle `ψ` is itself a coboundary. -/
theorem cochainCupZMod2_coboundary_left {X : TopCat.{0}} (p q : ℕ)
    (η : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q)
    (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q η ψ)
      = cochainCast (aw_degree_left_succ p q)
          (cochainCup (p + 1) q (cochainCoboundary (ZMod 2) X p η) ψ) := by
  rw [cochainCupZMod2_differential, hψ, cochainCup_zero_right, cochainCast_zero, add_zero]

/-- **`δη ⌣ ψ` is a coboundary (explicit form).** When `ψ` is a cocycle,
`δη ⌣ ψ` equals the degree-relabelled coboundary `cast (δ(η ⌣ ψ))`, exhibiting it
explicitly as a coboundary. -/
theorem cochainCupZMod2_coboundary_left' {X : TopCat.{0}} (p q : ℕ)
    (η : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q)
    (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    cochainCup (p + 1) q (cochainCoboundary (ZMod 2) X p η) ψ
      = cochainCast (aw_degree_left_succ p q).symm
          (cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q η ψ)) := by
  rw [cochainCupZMod2_coboundary_left p q η ψ hψ, cochainCast_cast]

/-- **`a ⌣ δη` is a coboundary (explicit form).** When `a` is a cocycle,
`a ⌣ δη` equals the degree-relabelled coboundary `cast (δ(a ⌣ η))`, exhibiting it
explicitly as a coboundary. -/
theorem cochainCupZMod2_coboundary_right' {X : TopCat.{0}} (p q : ℕ)
    (a : singularCochainGroup (ZMod 2) X p) (η : singularCochainGroup (ZMod 2) X q)
    (ha : cochainCoboundary (ZMod 2) X p a = 0) :
    cochainCup p (q + 1) a (cochainCoboundary (ZMod 2) X q η)
      = cochainCast (aw_degree_right_succ p q).symm
          (cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q a η)) := by
  rw [cochainCupZMod2_coboundary_right p q a η ha, cochainCast_cast]

/-! ## 4. The cup respects cohomology equivalence -/

/-- **The cup product respects coboundaries in the left factor.** If `ψ` is a
cocycle, then changing the left factor by a coboundary `δη` changes the cup
product by the coboundary `cast (δ(η ⌣ ψ))`:

```text
(φ + δη) ⌣ ψ = φ ⌣ ψ + cast (δ(η ⌣ ψ)).
```

Thus cohomologous left factors yield cohomologous cups: the cup product descends
to cohomology classes in the left variable. -/
theorem cochainCupZMod2_respects_coboundaries {X : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X (p + 1))
    (η : singularCochainGroup (ZMod 2) X p)
    (ψ : singularCochainGroup (ZMod 2) X q)
    (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    cochainCup (p + 1) q (φ + cochainCoboundary (ZMod 2) X p η) ψ
      = cochainCup (p + 1) q φ ψ
        + cochainCast (aw_degree_left_succ p q).symm
            (cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q η ψ)) := by
  rw [cochainCup_add_left, cochainCupZMod2_coboundary_left' p q η ψ hψ]

/-- **The cup product respects coboundaries in the right factor.** If `φ` is a
cocycle, then changing the right factor by a coboundary `δη` changes the cup
product by the coboundary `cast (δ(φ ⌣ η))`:

```text
φ ⌣ (ψ + δη) = φ ⌣ ψ + cast (δ(φ ⌣ η)).
```

Thus cohomologous right factors yield cohomologous cups: the cup product descends
to cohomology classes in the right variable. -/
theorem cochainCupZMod2_respects_coboundaries_right {X : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (ψ : singularCochainGroup (ZMod 2) X (q + 1))
    (η : singularCochainGroup (ZMod 2) X q)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    cochainCup p (q + 1) φ (ψ + cochainCoboundary (ZMod 2) X q η)
      = cochainCup p (q + 1) φ ψ
        + cochainCast (aw_degree_right_succ p q).symm
            (cochainCoboundary (ZMod 2) X (p + q) (cochainCup p q φ η)) := by
  rw [cochainCup_add_right, cochainCupZMod2_coboundary_right' p q φ η hφ]

end SphereOddDegree
