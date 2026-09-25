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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Bounded
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings

/-!
# The Integral Structure Presheaf O⁺

The integral structure presheaf `O⁺` on the adic spectrum `Spa(A, A⁺)` assigns to each
rational subset `R(T/s)` the subring of power-bounded elements of the presheaf value
`O_X(R(T/s))`.

We also define the sheaf cohomology groups `H^i(Spa(A, A⁺), O⁺)` as opaque types
(placeholders for the full derived functor construction) and the predicate
`AnnihilatedByTopNilpotentUnit` used in Scottish Book Problems 27 and 39.

## Main definitions

* `integralPresheafValue D` : The set `O⁺(R(T/s)) = {f ∈ O_X(R(T/s)) | f is power-bounded}`.
* `integralCohomology A i` : The sheaf cohomology group `H^i(Spa(A, A⁺), O⁺)` (placeholder).
* `AnnihilatedByTopNilpotentUnit A M` : `M` is killed by a topologically nilpotent unit.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §8.1
* [K. Kedlaya, *The Nonarchimedean Scottish Book*], Problems 27, 39
-/

@[expose] public section

open ValuationSpectrum TopologicalRing

universe u

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The integral structure presheaf value `O⁺(R(T/s))`, defined as the set of
power-bounded elements `A°(R(T/s))` in the presheaf value `O_X(R(T/s))`.

This is the set of sections of the integral structure sheaf on the rational
subset `R(T/s)` (§8.1 of Wedhorn). The integral structure sheaf `O⁺` is the
subsheaf of `O_X` whose sections are power-bounded elements. -/
def integralPresheafValue (D : RationalLocData A) : Set (presheafValue D) :=
  powerBoundedSubring (presheafValue D)

/-- Membership in `O⁺(R(T/s))` is equivalent to being power-bounded. -/
theorem mem_integralPresheafValue {D : RationalLocData A} {f : presheafValue D} :
    f ∈ integralPresheafValue D ↔ IsPowerBounded f :=
  Iff.rfl

end ValuationSpectrum

/-! ### Sheaf cohomology of O⁺ (placeholder)

The sheaf cohomology `H^i(Spa(A, A⁺), O⁺)` is the `i`-th right derived functor of
the global sections functor applied to the integral structure sheaf `O⁺`.

The full construction requires:
1. `O⁺` as a sheaf of abelian groups on `Spa(A, A⁺)`.
2. Enough injectives in the category of sheaves of abelian groups.
3. The derived functor cohomology machinery.

We define the type and its algebraic structures as opaque placeholders (`sorry`).
The intent is that once the full sheaf cohomology is available in Mathlib for
topological spaces, these can be replaced by the correct definitions. -/

/-- The sheaf cohomology group `H^i(Spa(A, A⁺), O⁺)` of the integral structure sheaf.

For a Huber pair `(A, A⁺)`, the integral structure sheaf `O⁺` on `X = Spa(A, A⁺)`
assigns to each rational subset `R(T/s)` the power-bounded elements of the completed
localization `O_X(R(T/s))` (see `integralPresheafValue`). The sheaf cohomology
`H^i(X, O⁺)` is defined via derived functors of the global sections functor.

This is a placeholder definition. -/
noncomputable def ScottishBook.integralCohomology
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] (i : ℕ) : Type u := sorry

/-- `H^i(Spa(A, A⁺), O⁺)` carries an abelian group structure (placeholder). -/
noncomputable instance ScottishBook.integralCohomology.addCommGroup
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] (i : ℕ) :
    AddCommGroup (ScottishBook.integralCohomology A i) := sorry

/-- `H^i(Spa(A, A⁺), O⁺)` carries an `A`-module structure via the canonical map
`A → Γ(X, O_X) → Γ(X, O⁺)` (placeholder). -/
noncomputable instance ScottishBook.integralCohomology.module
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] (i : ℕ) :
    Module A (ScottishBook.integralCohomology A i) := sorry

/-! ### Annihilation by topologically nilpotent units -/

namespace ScottishBook

/-- An abelian group `M` with an `A`-module structure is *annihilated by a topologically
nilpotent unit* of `A` if there exists a unit `u ∈ Aˣ` that is topologically nilpotent
and satisfies `u • m = 0` for all `m : M`.

This is the key condition appearing in Scottish Book Problems 27 and 39: whether
the cohomology groups `H^i(Spa(A, A⁺), O⁺)` are killed by such a unit, which
means the integral structure sheaf is "almost acyclic." -/
def AnnihilatedByTopNilpotentUnit
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTateRing A]
    (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∃ u : Aˣ, IsTopologicallyNilpotent (u : A) ∧ ∀ m : M, (u : A) • m = 0

/-- The cohomology groups `H^1, ..., H^j` of `O⁺` are all annihilated by topologically
nilpotent units. -/
def AllIntegralCohomologyAnnihilated
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsTateRing A] (j : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ j →
    AnnihilatedByTopNilpotentUnit A (integralCohomology A i)

end ScottishBook
