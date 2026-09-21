/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.IntegralStructureSheaf
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SeminormalRing

/-!
# Nonarchimedean Scottish Book — Problem 39

**Proposer:** Kiran Kedlaya
**Date:** 15 March 2021

## Problem Statement

Let (A, A+) be an adic affinoid algebra over a nonarchimedean field, and let n be a
positive integer. For i = 1, ..., j, suppose H^i(Spa(A, A+), O+) is killed by a
topologically nilpotent unit. Can this condition ring-theoretically describe A?

## Notes

For j = 1, the condition that H^1(Spa(A, A+), O+) is killed by a topologically
nilpotent unit is equivalent to A being seminormal (in the sense of Swan).

## Status

Open.

## Definitions needed

- **O+ cohomology**: The sheaf cohomology groups H^i(Spa(A, A+), O+) of the integral
  structure sheaf O+ on the adic spectrum (see `integralCohomology` in
  `IntegralStructureSheaf.lean`).
- **Seminormal ring**: A ring R such that whenever b, c in R satisfy b^3 = c^2, there
  exists a in R with a^2 = b and a^3 = c (see `IsSeminormalRing` in
  `SeminormalRing.lean`).

## Mathematical Background

An *adic affinoid algebra* over a nonarchimedean field `K` is a Tate Huber pair
`(A, A⁺)` together with a `K`-algebra structure on `A` that is compatible with
the topology (i.e., the structure map `K → A` is continuous and adic). The field `K`
is a complete non-trivially valued field with nonarchimedean (ultrametric) valuation.

The integral structure sheaf `O⁺` on `X = Spa(A, A⁺)` assigns to each rational subset
`R(T/s)` the power-bounded elements `A°(R(T/s))` of the completed localization.

Problem 39 asks whether the condition "H^i(X, O⁺) is killed by a topologically nilpotent
unit for i = 1, ..., j" characterizes a ring-theoretic property of `A`. The key special
case is `j = 1`, where this condition is conjectured to be equivalent to `A` being
seminormal.

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 39
* Swan, *On seminormality*, J. Algebra 67 (1980), pp. 210–229
* Wedhorn, *Adic Spaces*, §8.1 (integral structure sheaf)
-/

open ValuationSpectrum

universe u

namespace ScottishBook

/-! ### Nonarchimedean field

A nonarchimedean field is formalized as a field `K` equipped with a Tate ring structure
(which provides a topologically nilpotent unit and hence a nonarchimedean topology).
The `IsTateRing K` condition combined with `Field K` captures the essential property:
`K` is a complete non-trivially valued nonarchimedean field. -/

/-! ### Problem 39, part (a): j = 1 case -/

/-- **Nonarchimedean Scottish Book, Problem 39, part (a)** (Kedlaya, 15 Mar 2021).

*Let `K` be a nonarchimedean field (formalized as a field with `IsTateRing` structure),
and let `(A, A⁺)` be an adic affinoid `K`-algebra (a Tate Huber pair with a continuous
`K`-algebra structure). Then `H¹(Spa(A, A⁺), O⁺)` is annihilated by a topologically
nilpotent unit if and only if `A` is seminormal.*

The forward direction (seminormal implies almost vanishing of `H¹`) and the backward
direction (almost vanishing implies seminormal) are both part of this open conjecture.

This is an **open problem** -- the `sorry` is intentional. -/
theorem problem39a
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [IsTateRing K]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsTateRing A] [Algebra K A] :
    AllIntegralCohomologyAnnihilated A 1 ↔ IsSeminormalRing A := by
  sorry

/-! ### Problem 39, general case -/

/-- **Nonarchimedean Scottish Book, Problem 39** (Kedlaya, 15 Mar 2021).

*Let `K` be a nonarchimedean field and `(A, A⁺)` an adic affinoid `K`-algebra.
For a positive integer `j`, suppose `H^i(Spa(A, A⁺), O⁺)` is killed by a topologically
nilpotent unit for all `i = 1, ..., j`. Can this condition ring-theoretically
describe `A`?*

For `j = 1`, this is conjectured to be equivalent to `A` being seminormal (see
`problem39a`). For larger `j`, the ring-theoretic characterization is unknown.

The predicate `P` in the existential represents the unknown ring-theoretic property
that would characterize the cohomological condition.

This is an **open problem** -- the `sorry` is intentional. -/
theorem problem39
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [IsTateRing K]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsTateRing A] [Algebra K A]
    (j : ℕ) (hj : 0 < j) :
    ∃ (P : Prop),
      (AllIntegralCohomologyAnnihilated A j ↔ P) := by
  sorry

end ScottishBook
