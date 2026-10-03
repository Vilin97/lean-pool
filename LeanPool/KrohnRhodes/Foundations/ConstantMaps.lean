/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/

module
public import LeanPool.KrohnRhodes.Foundations.GreenRelations
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Submonoid.Membership

/-!
# Constant maps and aperiodicity

Convention: `Function.End Q` multiplies by composition, `(f * g) x = f (g x)`.

* `constEnd q` — the constant map `_ ↦ q`, and the predicate `IsConstEnd`;
* `constEnd_mul` — constant maps are left zeros: `constEnd p * t = constEnd p`;
* `eq_constEnd_of_R_constEnd` — anything `R`-related to a constant map is that constant map;
* `isAperiodicElem_of_id_or_const` — in a submonoid of `Function.End Q` whose elements are
  all the identity or constant maps, every element is aperiodic. This is what makes the reset
  monoids used in the decomposition genuine aperiodic factors.
-/

public section

namespace LeanPool.KrohnRhodes

universe u

/-! ## Reset / rank-drop transformations: the constant maps

A constant map `constEnd q : Q → Q`, `_ ↦ q`, has one-point image.
It is nonsurjective when `Q` has more than one point. Constant maps are the aperiodic
building blocks of the reset monoids used in the decomposition.

`Function.End Q` has multiplication `(f * g) x = f (g x)` and unit
`1 = id`.  Under this convention:

* `constEnd p * t = constEnd p` — a constant map **absorbs on the left**;
* `t * constEnd q = constEnd (t q)` — composing a constant on the *right*
  yields the constant `constEnd (t q)`;

so the constant maps form a **two-sided ideal** of `Function.End Q`, and
among themselves `constEnd p * constEnd q = constEnd p`, i.e. they form a
**left-zero semigroup**.  Left-zero semigroups are aperiodic, and any
transformation monoid all of whose non-identity elements are constants is
therefore aperiodic. -/

variable {Q : Type u}

/-- The constant transformation `_ ↦ q` of `Q`, as an element of the full
transformation monoid `Function.End Q`. -/
@[expose]
def constEnd (q : Q) : Function.End Q := fun _ => q

/-- A transformation of `Q` *is constant* if it equals `constEnd q` for
some `q` — equivalently, its image has exactly one point. -/
@[expose]
def IsConstEnd (t : Function.End Q) : Prop := ∃ q : Q, t = constEnd q

theorem isConstEnd_constEnd (q : Q) : IsConstEnd (constEnd q) := ⟨q, rfl⟩

/-- **A constant map absorbs on the left:** `constEnd p * t = constEnd p`
for every transformation `t`.  (`(constEnd p * t) x = constEnd p (t x) = p`.) -/
@[simp] theorem constEnd_mul (p : Q) (t : Function.End Q) :
    constEnd p * t = constEnd p := rfl

/-! ### Aperiodicity of constant transformation monoids

The constant maps are aperiodic.  The key observation is purely
multiplicative: **anything `R`-related (inside `Function.End Q`) to a
constant map equals that constant map** — because `constEnd p * s`
is *always* `constEnd p` (left absorption: `(constEnd p * s) x =
constEnd p (s x) = p`), so `constEnd p * s = b` forces `b = constEnd p`.
Hence any two `H`-related constants are equal.

(Note the convention: `Function.End Q` has `(f * g) x = f (g x)`, so a
constant map absorbs *on the left* of a product — it is a *left zero* of
the monoid — and it is `Green.R` that collapses constants, not `Green.L`.) -/

/-- **Anything right-related to a constant map is that constant map.**  If
`Green.R (constEnd p) b` holds in `Function.End Q`, then `b = constEnd p`.
(`Green.R` provides `s` with `constEnd p * s = b`, and `constEnd p * s`
collapses to `constEnd p` by left absorption.) -/
theorem eq_constEnd_of_R_constEnd {p : Q} {b : Function.End Q}
    (h : Green.R (constEnd p) b) : b = constEnd p := by
  obtain ⟨s, _t, hs, _ht⟩ := h
  rw [← hs, constEnd_mul]

/-! ### Reset-monoid aperiodicity: monoids of constants-plus-identity

A transformation monoid `S ≤ Function.End Q` *all of whose non-identity
elements are constant maps* is aperiodic.  This is the structure of the reset
monoids used in the decomposition (the identity together with constant maps).

We phrase the aperiodicity hypothesis on a `Submonoid (Function.End Q)`. -/

/-- **A constants-plus-identity transformation monoid is aperiodic.**  Let
`S` be a submonoid of `Function.End Q` such that every element of `S` is
*either the identity or a constant map* (`hS`).  Then every element of `S`
is aperiodic: any two `H`-related elements `a, b ∈ S` are equal.

Proof by cases on `a`:
* if `a` is constant, `H a b` gives `Green.R a b`, so
  `eq_constEnd_of_R_constEnd` forces `b = a`;
* if `a = 1`, `H 1 b` gives `Green.R 1 b`, providing `t` with
  `(1 : Function.End Q) * t = b` *and* `b * t' = 1`.  If `b` is also `1`
  we are done; if `b` is a constant `constEnd q`, then `b * t' = constEnd q`
  by left absorption, so `constEnd q = 1`, i.e. `Q` is subsingleton, and
  then `Function.End Q` is subsingleton so `a = b` regardless.

The conclusion is stated with `H` unfolded into explicit `L`- and `R`-witnesses. -/
theorem isAperiodicElem_of_id_or_const
    (S : Submonoid (Function.End Q))
    (hS : ∀ t ∈ S, t = 1 ∨ IsConstEnd t) :
    ∀ a b : S,
      ((∃ s t : S, s * a = b ∧ t * b = a) ∧
       (∃ s t : S, a * s = b ∧ b * t = a)) → a = b := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨_hLpair, hRpair⟩
  obtain ⟨⟨sR, _⟩, ⟨tR, _⟩, hsaR, htbR⟩ := hRpair
  apply Subtype.ext
  change a = b
  -- The underlying R-relation in `Function.End Q`.
  have hR : Green.R a b :=
    ⟨sR, tR, congrArg Subtype.val hsaR, congrArg Subtype.val htbR⟩
  rcases hS a ha with haId | haC
  · -- `a = 1`.  Use `R 1 b`: `b * tR = 1` (with `tR ∈ Function.End Q`).
    rcases hS b hb with hbId | hbC
    · rw [haId, hbId]
    · -- `b = constEnd q`; then `b * tR = constEnd q` but also `= 1`.
      obtain ⟨q, hbq⟩ := hbC
      obtain ⟨_s, t, _hs, ht⟩ := hR
      -- `ht : b * t = a = 1`; with `b = constEnd q`, `constEnd q * t = constEnd q`.
      rw [hbq, constEnd_mul, haId] at ht
      -- `constEnd q = 1` ⟹ `Q` subsingleton.
      have : Subsingleton Q := by
        refine ⟨fun x y => ?_⟩
        -- `congrFun ht x : constEnd q x = (1 : Function.End Q) x`, i.e. `q = x`.
        have hx : q = x := congrFun ht x
        have hy : q = y := congrFun ht y
        rw [← hx, ← hy]
      -- `Q` subsingleton ⟹ all transformations of `Q` are equal.
      funext x
      exact Subsingleton.elim _ _
  · -- `a` is a constant: `R a b` forces `b = a`.
    obtain ⟨p, hap⟩ := haC
    rw [hap]
    rw [hap] at hR
    exact (eq_constEnd_of_R_constEnd hR).symm

end LeanPool.KrohnRhodes
