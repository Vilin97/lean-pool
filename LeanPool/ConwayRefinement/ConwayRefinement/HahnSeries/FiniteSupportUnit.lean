/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupport

/-!
# Units of the nonpositive Hahn-series ring

Half of LM24, Fact 2.5.2: the units of the finite-support nonpositive Hahn-series ring are
exactly the nonzero constant series.

Finiteness of the support is not used. The order of a nonzero series is the least exponent of its
support, so it is at most zero here, and it is additive on products over a domain. A product equal
to one therefore forces both orders to vanish, which leaves the whole support at zero.
-/

open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
variable [Field K]

/-- A factor of a product equal to one, among series supported in the nonpositive exponents, has
order zero. -/
private theorem order_eq_zero_of_mul_eq_one {x y : K⟦G⟧}
    (hx : x.support ⊆ Set.Iic 0) (hy : y.support ⊆ Set.Iic 0) (hxy : x * y = 1) :
    x.order = 0 := by
  have hx0 : x ≠ 0 := left_ne_zero_of_mul_eq_one hxy
  have hy0 : y ≠ 0 := right_ne_zero_of_mul_eq_one hxy
  have hmem : ∀ {z : K⟦G⟧}, z ≠ 0 → z.support ⊆ Set.Iic 0 → z.order ≤ 0 := by
    intro z hz hsub
    exact hsub ((HahnSeries.mem_support _ _).mpr
      fun hc ↦ hz (HahnSeries.coeff_order_eq_zero.mp hc))
  have hsum := HahnSeries.order_mul hx0 hy0
  rw [hxy, HahnSeries.order_one] at hsum
  refine le_antisymm (hmem hx0 hx) ?_
  by_contra hlt
  rw [not_le] at hlt
  refine absurd ?_ (lt_irrefl (0 : G))
  calc (0 : G) = x.order + y.order := hsum
    _ < 0 + 0 := add_lt_add_of_lt_of_le hlt (hmem hy0 hy)
    _ = 0 := add_zero 0

/-- A nonpositive series of order zero is a constant. -/
private theorem eq_C_coeff_of_order_eq_zero {x : K⟦G⟧} (hx : x.support ⊆ Set.Iic 0)
    (horder : x.order = 0) : x = HahnSeries.C (x.coeff 0) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hg]
    by_contra hne
    exact hg (le_antisymm (hx hne) (horder ▸ HahnSeries.order_le_of_coeff_ne_zero hne))

/-- LM24, Fact 2.5.2: the units of the finite-support nonpositive Hahn-series ring are exactly
the nonzero constant series. -/
theorem isUnit_finiteSupport_iff_exists_scalar
    (p : (finiteSupportSubring : Subring (Nonpositive G K))) :
    IsUnit p ↔
      ∃ k : K, k ≠ 0 ∧ p = finiteSupportScalarHom (G := G) k := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, (u : (finiteSupportSubring : Subring (Nonpositive G K))) * q = 1 :=
      ⟨↑u⁻¹, u.mul_inv⟩
    have hmul : (((u : (finiteSupportSubring : Subring (Nonpositive G K))) :
          Nonpositive G K) : K⟦G⟧) * ((q : Nonpositive G K) : K⟦G⟧) = 1 := by
      have hcast := congrArg (fun r : (finiteSupportSubring : Subring (Nonpositive G K)) ↦
        ((r : Nonpositive G K) : K⟦G⟧)) hq
      simpa using hcast
    have hsub : ∀ r : (finiteSupportSubring : Subring (Nonpositive G K)),
        ((r : Nonpositive G K) : K⟦G⟧).support ⊆ Set.Iic 0 :=
      fun r ↦ (HahnSeries.mem_nonpositiveSubring (Γ := G) (R := K)).mp (r : Nonpositive G K).2
    have horder := order_eq_zero_of_mul_eq_one (hsub _) (hsub q) hmul
    refine ⟨(((u : (finiteSupportSubring : Subring (Nonpositive G K))) :
      Nonpositive G K) : K⟦G⟧).coeff 0, ?_, ?_⟩
    · rw [← horder]
      intro hc
      have h0 : (((u : (finiteSupportSubring : Subring (Nonpositive G K))) :
          Nonpositive G K) : K⟦G⟧) = 0 := HahnSeries.coeff_order_eq_zero.mp hc
      rw [h0, zero_mul] at hmul
      exact one_ne_zero hmul.symm
    · apply Subtype.ext
      apply Subtype.ext
      rw [coe_finiteSupportScalarHom]
      exact eq_C_coeff_of_order_eq_zero (hsub _) horder
  · rintro ⟨k, hk, rfl⟩
    exact (Ne.isUnit hk).map (finiteSupportScalarHom (G := G))

end HahnSeries.Nonpositive
