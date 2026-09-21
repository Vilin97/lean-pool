/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Nat.Cast.Order.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.MapWeight

/-!
# The top weighted-homogeneous component

For weights in a linearly ordered monoid with a bottom element, a nonzero multivariate polynomial
is the finite sum of its weighted-homogeneous components over the weights occurring in its
support, its component at the weighted total degree is nonzero, and removing that component
either leaves zero or strictly lowers the weighted total degree. Weights in `ℕ` read in the
monoid through `Nat.cast` have the cast weights, homogeneous components and weighted total
degree.
-/

universe u v w

public noncomputable section

namespace MvPolynomial

variable {σ : Type u} {R : Type v} {M : Type w}
variable [AddCommMonoid M] [LinearOrder M] [OrderBot M] (w : σ → M)

section CommSemiring

variable [CommSemiring R]

/-- The weighted-homogeneous component of a nonzero polynomial at its weighted total degree is
nonzero. -/
theorem weightedHomogeneousComponent_weightedTotalDegree_ne_zero {F : MvPolynomial σ R}
    (hF : F ≠ 0) :
    weightedHomogeneousComponent w (weightedTotalDegree w F) F ≠ 0 := by
  classical
  obtain ⟨d, hd, hsup⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF)
    fun s ↦ Finsupp.weight w s
  intro h0
  have := coeff_weightedHomogeneousComponent (w := w) (n := weightedTotalDegree w F) (φ := F) d
  rw [h0, AddMonoidAlgebra.coeff_zero, weightedTotalDegree, hsup, ite_eq_left rfl] at this
  exact mem_support_iff.mp hd this.symm

omit [OrderBot M] in
/-- Every polynomial is the finite sum of its weighted-homogeneous components over the weights
occurring in its support. -/
theorem eq_sum_weightedHomogeneousComponent (F : MvPolynomial σ R) :
    F = ∑ m ∈ F.support.image (fun s ↦ Finsupp.weight w s),
      weightedHomogeneousComponent w m F := by
  classical
  refine MvPolynomial.ext _ _ fun d ↦ ?_
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  by_cases hd : d ∈ F.support
  · rw [Finset.sum_eq_single (Finsupp.weight w d)]
    · rw [ite_eq_left rfl]
    · intro m _ hm
      rw [ite_eq_right (Ne.symm hm)]
    · intro hnot
      exact absurd (Finset.mem_image_of_mem _ hd) hnot
  · rw [notMem_support_iff.mp hd]
    exact (Finset.sum_eq_zero fun m _ ↦ ite_self 0).symm

end CommSemiring

section CommRing

variable [CommRing R]

/-- Removing the top weighted-homogeneous component of a polynomial leaves zero or a polynomial
of strictly smaller weighted total degree. -/
theorem weightedTotalDegree_sub_weightedHomogeneousComponent_lt (F : MvPolynomial σ R) :
    F - weightedHomogeneousComponent w (weightedTotalDegree w F) F = 0 ∨
      weightedTotalDegree w (F - weightedHomogeneousComponent w (weightedTotalDegree w F) F) <
        weightedTotalDegree w F := by
  classical
  set d := weightedTotalDegree w F with hd
  set G := weightedHomogeneousComponent w d F with hG
  by_cases hFG : F - G = 0
  · exact Or.inl hFG
  refine Or.inr (lt_of_le_of_ne (Finset.sup_le fun s hs ↦ ?_) fun heq ↦ ?_)
  · have hs' : AddMonoidAlgebra.coeff (F - G) s ≠ 0 := mem_support_iff.mp hs
    have hsub : AddMonoidAlgebra.coeff (F - G) s =
        if Finsupp.weight w s = d then 0 else AddMonoidAlgebra.coeff F s := by
      rw [coeff_sub, hG, coeff_weightedHomogeneousComponent]
      split_ifs <;> simp
    have hne : Finsupp.weight w s ≠ d := by
      intro heq
      rw [hsub, ite_eq_left heq] at hs'
      exact hs' rfl
    have hFne : AddMonoidAlgebra.coeff F s ≠ 0 := by
      rw [hsub, ite_eq_right hne] at hs'
      exact hs'
    exact le_weightedTotalDegree _ (mem_support_iff.mpr hFne)
  · obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup (F - G).support (support_nonempty.mpr hFG)
      fun s ↦ Finsupp.weight w s
    have hs' : AddMonoidAlgebra.coeff (F - G) s ≠ 0 := mem_support_iff.mp hs
    have hweight : Finsupp.weight w s = d := by
      rw [← heq, weightedTotalDegree, hsup]
    rw [coeff_sub, hG, coeff_weightedHomogeneousComponent, ite_eq_left hweight, sub_self] at hs'
    exact hs' rfl

end CommRing

end MvPolynomial

/-! ### Weights in `ℕ` read in `M` through `Nat.cast` -/

namespace MvPolynomial

variable {σ : Type u} {R : Type v} {M : Type w}

section Cast

variable [AddCommMonoidWithOne M]

/-- For weights in `ℕ` read in `M` through `Nat.cast`, the weight of a monomial is the cast of its
weight in `ℕ`. -/
theorem weight_natCast_comp (w : σ → ℕ) (e : σ →₀ ℕ) :
    Finsupp.weight (fun i ↦ (w i : M)) e = ((Finsupp.weight w e : ℕ) : M) := by
  simpa only [Nat.coe_castAddMonoidHom] using
    Finsupp.weight_comp_addMonoidHom (Nat.castAddMonoidHom M) w e

variable [CommSemiring R]

/-- A nonzero polynomial homogeneous for cast natural weights has a cast natural degree. -/
theorem IsWeightedHomogeneous.exists_degree_eq_natCast {w : σ → ℕ}
    {F : MvPolynomial σ R} {d : M}
    (hF : IsWeightedHomogeneous (fun i ↦ (w i : M)) F d) (hF0 : F ≠ 0) :
    ∃ n : ℕ, d = (n : M) := by
  obtain ⟨e, he⟩ := exists_coeff_ne_zero hF0
  refine ⟨Finsupp.weight w e, ?_⟩
  rw [← hF he, weight_natCast_comp]

variable [CharZero M]

/-- Homogeneity of degree `d` for weights read through `Nat.cast` is homogeneity of degree `d` for
the weights in `ℕ`. -/
theorem isWeightedHomogeneous_natCast_comp_iff (w : σ → ℕ) {F : MvPolynomial σ R} {d : ℕ} :
    IsWeightedHomogeneous (fun i ↦ (w i : M)) F (d : M) ↔ IsWeightedHomogeneous w F d := by
  simp only [IsWeightedHomogeneous, weight_natCast_comp, Nat.cast_inj]

/-- The homogeneous component of degree `d` for weights read through `Nat.cast` is the one for the
weights in `ℕ`. -/
theorem weightedHomogeneousComponent_natCast_comp (w : σ → ℕ) (d : ℕ) (F : MvPolynomial σ R) :
    weightedHomogeneousComponent (fun i ↦ (w i : M)) (d : M) F =
      weightedHomogeneousComponent w d F := by
  classical
  ext e
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent, weight_natCast_comp,
    Nat.cast_inj]
  by_cases h : Finsupp.weight w e = d <;> simp [h]

variable [LinearOrder M] [OrderBot M] [AddLeftMono M] [ZeroLEOneClass M]

omit [CharZero M] in
/-- The weighted total degree for weights read through `Nat.cast` is the cast of the weighted
total degree for the weights in `ℕ`, when `⊥ = 0` in `M`. -/
theorem weightedTotalDegree_natCast_comp (hbot : (⊥ : M) = 0) (w : σ → ℕ)
    (F : MvPolynomial σ R) :
    weightedTotalDegree (fun i ↦ (w i : M)) F = ((weightedTotalDegree w F : ℕ) : M) := by
  change F.support.sup (fun s ↦ Finsupp.weight (fun i ↦ (w i : M)) s) =
    ((F.support.sup fun s ↦ Finsupp.weight w s : ℕ) : M)
  rw [Finset.apply_sup_eq_sup_comp_of_linearOrder (Nat.cast : ℕ → M) Nat.mono_cast
      (by rw [Nat.bot_eq_zero, Nat.cast_zero, hbot])]
  exact Finset.sup_congr rfl fun s _ ↦ weight_natCast_comp w s

end Cast

end MvPolynomial
