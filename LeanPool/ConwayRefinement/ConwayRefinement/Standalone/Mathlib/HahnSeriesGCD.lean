/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Greatest common divisors and factorisation in `K((ℝ^{≤0}))`

`nonpos K` is the Hahn-series ring `K((ℝ^{≤0}))`. In characteristic zero it is a GCD domain and
pre-Schreier. Consequently every irreducible series is prime, and any two irreducible
factorisations are the same up to order and units. LM24, Corollary 6.4.2 proves that these two
ring properties are equivalent to every irreducible series with infinite support being prime;
the theorems below establish the properties themselves.

## References

* S. L'Innocente, V. Mantova, *A factorisation theory for generalised power series and omnific
  integers*, Adv. Math. 442 (2024) 109513, <https://doi.org/10.1016/j.aim.2024.109513>, cited
  as [LM24].
-/

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Hahn

universe u

variable (K : Type u) [Field K]

/-- `K((ℝ^{≤0}))`: Hahn series with real exponents `≤ 0` [LM24, §1.2]. -/
def nonpos : Subring (HahnSeries ℝ K) where
  carrier := {x | x.support ⊆ Set.Iic 0}
  zero_mem' := by simp
  one_mem' := fun _ hg ↦ (HahnSeries.support_single_subset hg).le
  add_mem' := fun hx hy ↦
    (HahnSeries.support_add_subset _ _).trans (Set.union_subset hx hy)
  neg_mem' := fun hx ↦ (HahnSeries.support_neg_subset _).trans hx
  mul_mem' := fun hx hy ↦ HahnSeries.support_mul_subset.trans fun _ ⟨i, hi, j, hj, h⟩ ↦
    h ▸ show i + j ≤ 0 from add_nonpos (hx hi) (hy hj)

/-- Every pair of series in `K((ℝ^{≤0}))` has a greatest common divisor. -/
abbrev SeriesHasGCDs : Prop :=
  CharZero K →
    ∀ a b : nonpos K, ∃ d : nonpos K, ∀ e : nonpos K, e ∣ a ∧ e ∣ b ↔ e ∣ d

/-- Every series in `K((ℝ^{≤0}))` is primal, in the sense of LM24, §2.5. -/
abbrev SeriesIsPrimal : Prop :=
  CharZero K → ∀ a : nonpos K, IsPrimal a

/-- Every irreducible series in `K((ℝ^{≤0}))` is prime. -/
abbrev SeriesIrreduciblesArePrime : Prop :=
  CharZero K → ∀ a : nonpos K, Irreducible a → Prime a

/-- Two products of irreducibles that agree up to a unit have the same factors up to order and
association. -/
abbrev SeriesFactorizationsAreUnique : Prop :=
  CharZero K →
    ∀ f g : Multiset (nonpos K), (∀ x ∈ f, Irreducible x) → (∀ x ∈ g, Irreducible x) →
      Associated f.prod g.prod → Multiset.Rel Associated f g

end ConwayRefinement.Standalone.Hahn

/-!
## Formal proof

Proof module: `HahnSeriesGCDProof`.

* `SeriesHasGCDs` → `SeriesHasGCDs.proof`
* `SeriesIsPrimal` → `SeriesIsPrimal.proof`
* `SeriesIrreduciblesArePrime` → `SeriesIrreduciblesArePrime.proof`
* `SeriesFactorizationsAreUnique` → `SeriesFactorizationsAreUnique.proof`
-/
