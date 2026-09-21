/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Ideal.Basic

/-!
# Seminormal Rings

A commutative ring is **seminormal** if for every pair `(b, c)` with `b³ = c²`, there
exists `a` with `a² = b` and `a³ = c`.

This is a weaker condition than normality (integrally closed in its total ring of
fractions). The seminormalization of a ring `R` is the largest subextension of `R` in
its integral closure that is subintegral over `R`.

## Main definitions

* `IsSeminormalRing R` : A commutative ring `R` is seminormal.

## References

* Swan, *On seminormality*, J. Algebra 67 (1980), pp. 210–229
* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 39
-/

/-- A commutative ring `R` is **seminormal** if whenever `b, c ∈ R` satisfy `b³ = c²`,
there exists `a ∈ R` with `a² = b` and `a³ = c`.

Equivalently, the natural map from `R` to its seminormalization is an isomorphism.
This notion characterizes when `H¹(Spa(A, A⁺), O⁺)` is killed by a topologically
nilpotent unit for adic affinoid algebras over nonarchimedean fields
(Scottish Book Problem 39). -/
class IsSeminormalRing (R : Type*) [CommRing R] : Prop where
  /-- For any `b, c` with `b³ = c²`, there exists `a` with `a² = b` and `a³ = c`. -/
  seminormal : ∀ (b c : R), b ^ 3 = c ^ 2 → ∃ a : R, a ^ 2 = b ∧ a ^ 3 = c
