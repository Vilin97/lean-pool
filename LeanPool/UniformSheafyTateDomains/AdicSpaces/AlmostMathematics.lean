/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Almost Mathematics

The theory of "almost modules" over a ring `V` with an idempotent ideal `m`
(Gabber--Ramero, *Almost Ring Theory*, LNM 1800).

An element `x` of a `V`-module `M` is **almost zero** if `a • x = 0` for all `a ∈ m`.
A `V`-linear map is **almost injective/surjective** if its kernel/cokernel is almost zero.

## Main definitions

* `AlmostSetup V` : A ring `V` with a distinguished idempotent ideal `m` (`m * m = m`).
* `AlmostMath.IsAlmostZero V x` : Element `x` is annihilated by every element of `m`.
* `Module.IsAlmostZero V M` : Module `M` is annihilated by `m`.
* `LinearMap.IsAlmostInjective f` : Kernel of `f` is almost zero.
* `LinearMap.IsAlmostSurjective f` : Cokernel of `f` is almost zero.
* `Module.IsAlmostFinitelyGenerated V M` : `M` is almost finitely generated.

## References

* Gabber--Ramero, *Almost Ring Theory*, Springer LNM 1800
* Scholze, *Perfectoid Spaces*, section 4 (almost mathematics in perfectoid context)
-/

@[expose] public section

universe u v

/-- A **basic almost setup** is a commutative ring `V` equipped with an idempotent
ideal `m` (satisfying `m * m = m`). In the perfectoid context, `V = O_K` and
`m` is the maximal ideal of a perfectoid field `K`. -/
class AlmostSetup (V : Type u) [CommRing V] where
  /-- The distinguished idempotent ideal. -/
  m : Ideal V
  /-- The ideal is idempotent: `m * m = m`. -/
  idempotent : m * m = m

namespace AlmostMath

variable {V : Type u} [CommRing V] [AlmostSetup V]
variable {M : Type v} [AddCommGroup M] [Module V M]

/-- An element `x` of a `V`-module is **almost zero** if `a • x = 0` for all `a ∈ m`. -/
def IsAlmostZero (x : M) : Prop :=
  ∀ a : V, a ∈ AlmostSetup.m (V := V) → a • x = 0

theorem IsAlmostZero.zero : IsAlmostZero (V := V) (0 : M) :=
  fun _ _ => smul_zero _

theorem IsAlmostZero.add {x y : M} (hx : IsAlmostZero (V := V) x)
    (hy : IsAlmostZero (V := V) y) : IsAlmostZero (V := V) (x + y) :=
  fun a ha => by rw [smul_add, hx a ha, hy a ha, add_zero]

theorem IsAlmostZero.neg {x : M} (hx : IsAlmostZero (V := V) x) :
    IsAlmostZero (V := V) (-x) :=
  fun a ha => by rw [smul_neg, hx a ha, neg_zero]

theorem IsAlmostZero.smul {x : M} (hx : IsAlmostZero (V := V) x) (r : V) :
    IsAlmostZero (V := V) (r • x) :=
  fun a ha => by rw [smul_comm, hx a ha, smul_zero]

end AlmostMath

/-- A `V`-module `M` is **almost zero** if `m ≤ annihilator(M)`, i.e., every element
of `m` annihilates every element of `M`. -/
class Module.IsAlmostZero (V : Type u) (M : Type v) [CommRing V] [AlmostSetup V]
    [AddCommGroup M] [Module V M] : Prop where
  /-- The ideal `m` annihilates the module. -/
  almost_zero : AlmostSetup.m (V := V) ≤ Module.annihilator V M

namespace AlmostMath

variable {V : Type u} [CommRing V] [AlmostSetup V]
variable {M N : Type v} [AddCommGroup M] [Module V M] [AddCommGroup N] [Module V N]

/-- A `V`-linear map is **almost injective** if its kernel is almost zero. -/
def LinearMap.IsAlmostInjective (f : M →ₗ[V] N) : Prop :=
  Module.IsAlmostZero V (LinearMap.ker f)

/-- A `V`-linear map is **almost surjective** if its cokernel is almost zero. -/
def LinearMap.IsAlmostSurjective (f : M →ₗ[V] N) : Prop :=
  Module.IsAlmostZero V (N ⧸ LinearMap.range f)

/-- A `V`-linear map is **almost bijective** if it is both almost injective and
almost surjective. -/
def LinearMap.IsAlmostBijective (f : M →ₗ[V] N) : Prop :=
  LinearMap.IsAlmostInjective f ∧ LinearMap.IsAlmostSurjective f

/-- A `V`-module is **almost finitely generated** if for every `a ∈ m`, the element
`a` acts through a finitely generated submodule. -/
def Module.IsAlmostFinitelyGenerated (V : Type u) (M : Type v)
    [CommRing V] [AlmostSetup V] [AddCommGroup M] [Module V M] : Prop :=
  ∀ a : V, a ∈ AlmostSetup.m (V := V) →
    ∃ (S : Finset M), ∀ x : M, a • x ∈ Submodule.span V (S : Set M)

end AlmostMath
