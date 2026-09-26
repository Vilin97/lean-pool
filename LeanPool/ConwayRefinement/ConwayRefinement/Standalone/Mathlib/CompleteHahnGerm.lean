/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Hahn germs over a Cauchy-complete exponent group

Let `K((G^{≤ 0}))` be the ring of Hahn series supported in the nonpositive cone of `G`, and
identify two series when they agree on some interval immediately below zero. If `G` is Cauchy
complete for an order-compatible uniformity, dense, has no endpoints, and has no smallest nonzero
Archimedean magnitude, then this germ ring is a polynomial algebra over `K`. Consequently it has
four-factor refinement.
-/

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.CompleteHahnGerm

universe u v

variable (G : Type u) (K : Type v)
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [NoMinOrder G] [Field K]

/-- The Hahn-series `K`-algebra `K((G^{≤ 0}))`. -/
def NonpositiveSeries : Subalgebra K (HahnSeries G K) where
  carrier := {x | x.support ⊆ Set.Iic 0}
  algebraMap_mem' k := by
    intro g hg
    rw [HahnSeries.algebraMap_apply] at hg
    have hg0 : g = 0 := HahnSeries.support_single_subset hg
    simp [hg0]
  add_mem' := fun hx hy ↦
    (HahnSeries.support_add_subset _ _).trans (Set.union_subset hx hy)
  mul_mem' := fun hx hy ↦ HahnSeries.support_mul_subset.trans fun _ ⟨i, hi, j, hj, h⟩ ↦
    h ▸ show i + j ≤ 0 from add_nonpos (hx hi) (hy hj)

/-- The ideal of series whose support is bounded away from zero. -/
def BoundedAwayIdeal : Ideal (NonpositiveSeries G K) where
  carrier := {x | ∃ r < (0 : G), (x : HahnSeries G K).support ⊆ Set.Iic r}
  zero_mem' := by
    obtain ⟨r, hr⟩ := exists_lt (0 : G)
    exact ⟨r, hr, by simp⟩
  add_mem' := by
    rintro x y ⟨r, hr, hxr⟩ ⟨s, hs, hys⟩
    refine ⟨max r s, max_lt hr hs, ?_⟩
    intro q hq
    rcases HahnSeries.support_add_subset (x : HahnSeries G K) y hq with hqx | hqy
    · exact (hxr hqx).trans (le_max_left r s)
    · exact (hys hqy).trans (le_max_right r s)
  smul_mem' := by
    rintro x y ⟨r, hr, hyr⟩
    refine ⟨r, hr, HahnSeries.support_mul_subset.trans ?_⟩
    rintro _ ⟨i, hi, j, hj, rfl⟩
    simpa only [Set.mem_Iic, zero_add] using add_le_add (x.2 hi) (hyr hj)

/-- The germ ring `K((G^{≤ 0}))` modulo series supported away from zero. -/
abbrev Germ := NonpositiveSeries G K ⧸ BoundedAwayIdeal G K

/-- The germ ring is isomorphic to a polynomial algebra over `K`. -/
abbrev IsPolynomialRing : Prop :=
  ∀ [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G]
    [Nontrivial G] [CompleteSpace G] [DenselyOrdered G] [NoMaxOrder G]
    [NoMaxOrder (FiniteArchimedeanClass G)] [CharZero K],
      ∃ ι : Type (max (u + 1) v), Nonempty (MvPolynomial ι K ≃ₐ[K] Germ G K)

/-- Every equation of four germs admits a four-factor refinement. -/
abbrev HasRefinement : Prop :=
  ∀ [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G]
    [Nontrivial G] [CompleteSpace G] [DenselyOrdered G] [NoMaxOrder G]
    [NoMaxOrder (FiniteArchimedeanClass G)] [CharZero K],
      ∀ a b c d : Germ G K, a * b = c * d →
        ∃ e f g h : Germ G K,
          a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h

end ConwayRefinement.Standalone.CompleteHahnGerm

/-!
## Formal proof

Proof module: `CompleteHahnGermProof`.

* `IsPolynomialRing` → `IsPolynomialRing.proof`
* `HasRefinement` → `HasRefinement.proof`
-/
