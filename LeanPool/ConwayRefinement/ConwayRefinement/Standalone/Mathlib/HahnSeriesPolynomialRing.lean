/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.HahnSeries.Cardinal

/-!
# The Hahn-series ring is a polynomial ring

Let `K_fin` be the subring of `K((ℝ^{≤0}))` consisting of the series with finite support. In
characteristic zero there is a set of indeterminates `ι` for which

`K_fin[X_i : i ∈ ι] ≅ K((ℝ^{≤0}))`.

Both rings are defined below in ordinary Mathlib language; the statement does not mention the
principal graded ring or a chosen generating system.
-/

open Cardinal

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.HahnPolynomial

universe u

variable (K : Type u) [Field K]

/-- The Hahn-series ring `K((ℝ^{≤0}))`. -/
def Series : Subring (HahnSeries ℝ K) where
  carrier := {x | x.support ⊆ Set.Iic 0}
  zero_mem' := by simp
  one_mem' := fun _ hg ↦ (HahnSeries.support_single_subset hg).le
  add_mem' := fun hx hy ↦
    (HahnSeries.support_add_subset _ _).trans (Set.union_subset hx hy)
  neg_mem' := fun hx ↦ (HahnSeries.support_neg_subset _).trans hx
  mul_mem' := fun hx hy ↦ HahnSeries.support_mul_subset.trans fun _ ⟨i, hi, j, hj, h⟩ ↦
    h ▸ show i + j ≤ 0 from add_nonpos (hx hi) (hy hj)

/-- The elements of `K((ℝ^{≤0}))` are exactly the Hahn series supported in `(-∞, 0]`. -/
theorem mem_series_iff (x : HahnSeries ℝ K) :
    x ∈ Series K ↔ x.support ⊆ Set.Iic 0 := (Iff.rfl)

/-- The subring `K_fin` of nonpositive Hahn series with finite support. -/
def FiniteSupport : Subring (Series K) :=
  let _ : Fact (aleph0 ≤ aleph0) := ⟨le_rfl⟩
  (HahnSeries.cardSuppLTSubring ℝ K aleph0).comap (Series K).subtype

/-- Membership in `K_fin` is exactly finiteness of the Hahn-series support. -/
theorem mem_finiteSupport_iff (x : Series K) :
    x ∈ FiniteSupport K ↔ x.1.support.Finite := by
  letI : Fact (aleph0 ≤ aleph0) := ⟨le_rfl⟩
  rw [FiniteSupport, Subring.mem_comap, HahnSeries.mem_cardSuppLTSubring,
    HahnSeries.cardSupp]
  exact Cardinal.lt_aleph0_iff_set_finite

/-- **Polynomial presentation of the full series ring.** For some set `ι`, the polynomial algebra
over the finite-support series is isomorphic to the full nonpositive Hahn-series ring. -/
abbrev IsPolynomialRing : Prop :=
  CharZero K → ∃ ι : Type (max u 1),
    Nonempty (MvPolynomial ι (FiniteSupport K) ≃ₐ[FiniteSupport K] Series K)

end ConwayRefinement.Standalone.HahnPolynomial

/-!
## Formal proof

Proof module: `HahnSeriesPolynomialRingProof`.

* `IsPolynomialRing` → `IsPolynomialRing.proof`
-/
