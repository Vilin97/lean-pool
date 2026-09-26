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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicSpectrum
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Bounded

/-!
# Affinoid Rings

We define **rings of integral elements** and **affinoid rings** for topological rings,
following Definition 7.14 and Remark 7.15 of [Wedhorn, *Adic Spaces*].

## Main definitions

* `ValuationSpectrum.IsRingOfIntegralElements B` : The subring `B` is a ring of integral elements
  (Definition 7.14(1) of Wedhorn).
* `ValuationSpectrum.IsAffinoidRing A` : The pair `(A, A⁺)` is an affinoid ring
  (Definition 7.14 of Wedhorn).

## Main results

* `IsRingOfIntegralElements.le_powerBoundedSubring` : Any ring of integral elements
  is contained in `A°` (Remark 7.15(1) of Wedhorn).
* `topologicallyNilpotent_mem_of_isOpen_integrallyClosed` : An open, integrally
  closed subring contains all topologically nilpotent elements (Remark 7.15(2)).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 7.14, Remark 7.15
-/

@[expose] public section

open Filter Topology

namespace ValuationSpectrum

section IntegralElements

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- A ring of integral elements (Definition 7.14(1)): open, integrally closed, and in `A°`.

A `class` (not a bare `structure`) so it can be required as `[IsRingOfIntegralElements (A⁺)]`
on `Spa`-level theorems — the faithful affinoid-ring interface (expert-review 2026-06-18,
reviewer Q1). The bare `PlusSubring` carrier stays low-level; this records the three
Definition-7.14 axioms (open, integrally closed, `⊆ A°`) that make `(A, A⁺)` an affinoid ring. -/
class IsRingOfIntegralElements (B : Subring A) : Prop where
  /-- `B` is open in `A`. -/
  isOpen : IsOpen (B : Set A)
  /-- `B` is integrally closed in `A`. -/
  isIntegrallyClosed : ∀ a : A, IsIntegral (↥B) a → a ∈ B
  /-- `B ⊆ A°`. -/
  subset_powerBounded : (B : Set A) ⊆ TopologicalRing.powerBoundedSubring A

/-! ### Remark 7.15 -/

/-- Any ring of integral elements is contained in `A°` (Remark 7.15(1)). -/
theorem IsRingOfIntegralElements.le_powerBoundedSubring {B : Subring A}
    (hB : IsRingOfIntegralElements B) :
    (B : Set A) ⊆ TopologicalRing.powerBoundedSubring A :=
  hB.subset_powerBounded

/-- An open, integrally closed subring contains all topologically nilpotent elements
(Remark 7.15(2)). -/
theorem topologicallyNilpotent_mem_of_isOpen_integrallyClosed
    (B : Subring A) (hB_open : IsOpen (B : Set A))
    (hB_ic : ∀ a : A, IsIntegral (↥B) a → a ∈ B)
    {a : A} (ha : IsTopologicallyNilpotent a) : a ∈ B := by
  obtain ⟨n, hn_mem, hn_pos⟩ := (ha.eventually (hB_open.mem_nhds B.zero_mem) |>.and
    (Filter.eventually_gt_atTop 0)).exists
  exact hB_ic a (TopologicalRing.isIntegral_of_pow_mem B hn_pos hn_mem)

/-- A ring of integral elements contains all topologically nilpotent elements. -/
theorem IsRingOfIntegralElements.topologicallyNilpotentElements_subset {B : Subring A}
    (hB : IsRingOfIntegralElements B) :
    TopologicalRing.topologicallyNilpotentElements A ⊆ (B : Set A) :=
  fun _ ↦ topologicallyNilpotent_mem_of_isOpen_integrallyClosed B hB.isOpen hB.isIntegrallyClosed

variable [PlusSubring A]

/-- `(A, A⁺)` is an affinoid ring if `A⁺` is a ring of integral elements (Definition 7.14). -/
def IsAffinoidRing (A : Type*) [CommRing A] [TopologicalSpace A] [PlusSubring A] : Prop :=
  IsRingOfIntegralElements (A⁺)

end IntegralElements

end ValuationSpectrum
