/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeSum
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.WeightedTotalDegree
public import Mathlib.Algebra.MvPolynomial.Eval

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# The degree of a polynomial in elements with independent initial forms

Let `ν` be a multiplicative degree on a commutative ring `R` with values in `M`, let `L → R` be a
ring of scalars whose nonzero elements have degree zero, and let `x i ∈ R` be elements of degrees
`w i ∈ M`. Suppose the initial forms of the `x i` are algebraically independent over the initial
forms of `L`: an injective ring homomorphism `Φ : L[X] → gr_ν R` sends `C c` to `in(c)` and `X i`
to `in(x i)`. Then for every nonzero polynomial `F`, the degree of `F(x)` is the weighted total
degree of `F` for the weights `w`, and the initial form of `F(x)` is `Φ` of the top
weighted-homogeneous component of `F`: the monomials of top weight have independent initial
forms, so their sum has exactly that degree, and the remaining terms have smaller degree.
Consequently evaluation at `x` is injective.

The weights take values in the value monoid `M` itself; weights in `ℕ`, read in `M` through
`Nat.cast`, are the case treated by the cast lemmas of
`ConwayRefinement.Algebra.MvPolynomial.WeightedTotalDegree`.
-/

universe u v w x

public noncomputable section

open MvPolynomial

namespace MaxAddDegree

variable {R : Type u} {M : Type v} {L : Type w} {σ : Type x}

variable [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]

section Multiplicative

variable (ν : MaxAddDegree R M) [ν.IsMultiplicative]

/-- The initial form of a power is the power of the initial form. -/
theorem initialForm_pow (y : R) (n : ℕ) : ν.initialForm (y ^ n) = ν.initialForm y ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ν.initialForm_one]
  | succ n ih => rw [pow_succ, pow_succ, ν.initialForm_mul, ih]

/-- The initial form of a finite product is the product of the initial forms. -/
theorem initialForm_finset_prod {ι : Type*} (s : Finset ι) (f : ι → R) :
    ν.initialForm (∏ i ∈ s, f i) = ∏ i ∈ s, ν.initialForm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, ν.initialForm_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, ν.initialForm_mul, ih]

end Multiplicative

variable [CommRing L] [Nontrivial L] [Algebra L R]

/-- Elements `x i` of degrees `w i` whose initial forms are algebraically independent over the
initial forms of the degree-zero scalars `L`, witnessed by an injective ring homomorphism
`Φ : L[X] → gr_ν R` with `Φ (C c) = in(c)` and `Φ (X i) = in(x i)`. -/
structure IsInitialFormCoordinates (ν : MaxAddDegree R M) (w : σ → M) (x : σ → R)
    (Φ : MvPolynomial σ L →+* ν.AssociatedGraded) : Prop where
  degree_algebraMap : ∀ c : L, c ≠ 0 → ν (algebraMap L R c) = 0
  degree_x : ∀ i, ν (x i) = (w i : WithBot M)
  injective : Function.Injective Φ
  map_C : ∀ c : L, Φ (C c) = ν.initialForm (algebraMap L R c)
  map_X : ∀ i, Φ (X i) = ν.initialForm (x i)

namespace IsInitialFormCoordinates

variable {ν : MaxAddDegree R M} {w : σ → M} {x : σ → R}
  {Φ : MvPolynomial σ L →+* ν.AssociatedGraded}
variable [ν.IsMultiplicative] (H : IsInitialFormCoordinates ν w x Φ)
include H

omit [ν.IsMultiplicative] in
theorem degree_one : ν 1 = 0 := by
  simpa using H.degree_algebraMap 1 one_ne_zero

theorem degree_pow {y : R} {m : M} (hy : ν y = m) (n : ℕ) :
    ν (y ^ n) = ((n • m : M) : WithBot M) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, WithBot.coe_zero]; exact H.degree_one
  | succ n ih => rw [pow_succ, ν.map_mul, ih, hy, succ_nsmul, WithBot.coe_add]

theorem degree_finset_prod {ι : Type*} (s : Finset ι) (f : ι → R) (m : ι → M)
    (h : ∀ i ∈ s, ν (f i) = m i) :
    ν (∏ i ∈ s, f i) = ((∑ i ∈ s, m i : M) : WithBot M) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using H.degree_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ν.map_mul, h a (Finset.mem_insert_self a s),
      ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi), WithBot.coe_add]

/-- The degree of the value of a monomial with nonzero coefficient is its weight. -/
theorem degree_aeval_monomial (e : σ →₀ ℕ) {c : L} (hc : c ≠ 0) :
    ν (aeval x (monomial e c)) = (Finsupp.weight w e : WithBot M) := by
  classical
  rw [aeval_monomial, ν.map_mul, H.degree_algebraMap c hc, zero_add, Finsupp.prod,
    H.degree_finset_prod e.support (fun i ↦ x i ^ e i) (fun i ↦ e i • w i)
      fun i _ ↦ H.degree_pow (H.degree_x i) (e i),
    Finsupp.weight_apply, Finsupp.sum]

omit [Nontrivial L] in
/-- On a monomial, the initial form of the value is `Φ` of the monomial. -/
theorem initialForm_aeval_monomial (e : σ →₀ ℕ) (c : L) :
    ν.initialForm (aeval x (monomial e c)) = Φ (monomial e c) := by
  classical
  rw [aeval_monomial, ν.initialForm_mul, Finsupp.prod, ν.initialForm_finset_prod, monomial_eq,
    _root_.map_mul, H.map_C, Finsupp.prod, _root_.map_prod]
  congr 1
  exact Finset.prod_congr rfl fun i _ ↦ by rw [ν.initialForm_pow, _root_.map_pow, H.map_X]

/-- For a weighted-homogeneous polynomial `G` of weight `d`, the class of `G(x)` at level `d` is
`Φ G`: every monomial of `G` has degree exactly `d`, where the class map is additive. -/
theorem homogeneousMk_aeval_of_isWeightedHomogeneous {G : MvPolynomial σ L} {d : M}
    (hG : IsWeightedHomogeneous w G d) (hle : aeval x G ∈ ν.filtrationLE d) :
    ν.homogeneousMk d ⟨aeval x G, hle⟩ = Φ G := by
  classical
  have hdeg : ∀ e ∈ G.support,
      ν (aeval x (monomial e (coeff e G))) = (d : WithBot M) := fun e he ↦ by
    rw [H.degree_aeval_monomial e (mem_support_iff.mp he), hG (mem_support_iff.mp he)]
  have hmem : ∀ e ∈ G.support, aeval x (monomial e (coeff e G)) ∈ ν.filtrationLE d :=
    fun e he ↦ (ν.mem_filtrationLE_iff _ _).mpr (hdeg e he).le
  have hsplit : (⟨aeval x G, hle⟩ : ν.filtrationLE d) =
      ⟨∑ e ∈ G.support, aeval x (monomial e (coeff e G)), (ν.filtrationLE _).sum_mem hmem⟩ := by
    apply Subtype.ext
    change aeval x G = _
    conv_lhs => rw [as_sum G]
    rw [_root_.map_sum]
  rw [hsplit, ν.homogeneousMk_finsetSum _ _ hmem]
  conv_rhs => rw [as_sum G]
  rw [_root_.map_sum, ← Finset.sum_attach G.support fun e ↦ Φ (monomial e (coeff e G))]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [ν.homogeneousMk_eq_initialForm_of_degree_eq _ (hdeg e.1 e.2)]
  exact H.initialForm_aeval_monomial e.1 (coeff e.1 G)

variable [OrderBot M]

/-- A polynomial of weighted total degree at most `d` evaluates to an element of degree at most
`d`. -/
theorem degree_aeval_le_of_weightedTotalDegree_le {F : MvPolynomial σ L} {d : M}
    (hF : weightedTotalDegree w F ≤ d) :
    ν (aeval x F) ≤ (d : WithBot M) := by
  classical
  conv_lhs => rw [as_sum F]
  rw [_root_.map_sum]
  refine ν.map_sum_le_of_forall_le _ _ _ fun e he ↦ ?_
  rw [H.degree_aeval_monomial e (mem_support_iff.mp he)]
  exact WithBot.coe_le_coe.mpr ((le_weightedTotalDegree w he).trans hF)

/-- A polynomial value has degree at most the weighted total degree of the polynomial. -/
theorem degree_aeval_le (F : MvPolynomial σ L) :
    ν (aeval x F) ≤ ((weightedTotalDegree w F : M) : WithBot M) :=
  H.degree_aeval_le_of_weightedTotalDegree_le le_rfl

/-- A nonzero weighted-homogeneous polynomial of weight `d` evaluates to an element of degree
exactly `d`. -/
theorem degree_aeval_eq_of_isWeightedHomogeneous {G : MvPolynomial σ L} {d : M}
    (hG : IsWeightedHomogeneous w G d) (hne : G ≠ 0) :
    ν (aeval x G) = (d : WithBot M) := by
  have hle : ν (aeval x G) ≤ (d : WithBot M) :=
    H.degree_aeval_le_of_weightedTotalDegree_le
      (Finset.sup_le fun e he ↦ (hG (mem_support_iff.mp he)).le)
  have hmem := (ν.mem_filtrationLE_iff _ _).mpr hle
  refine le_antisymm hle (not_lt.mp fun hlt ↦ H.injective.ne hne ?_)
  rw [_root_.map_zero, ← H.homogeneousMk_aeval_of_isWeightedHomogeneous hG hmem]
  exact ν.homogeneousMk_eq_zero_of_degree_lt hmem hlt

/-- The initial form of the value of a weighted-homogeneous polynomial `G` is `Φ G`. -/
theorem initialForm_aeval_of_isWeightedHomogeneous {G : MvPolynomial σ L} {d : M}
    (hG : IsWeightedHomogeneous w G d) :
    ν.initialForm (aeval x G) = Φ G := by
  by_cases hzero : G = 0
  · subst hzero
    rw [_root_.map_zero, _root_.map_zero, ν.initialForm_zero]
  have hdeg := H.degree_aeval_eq_of_isWeightedHomogeneous hG hzero
  have hmem := (ν.mem_filtrationLE_iff _ _).mpr hdeg.le
  rw [← ν.homogeneousMk_eq_initialForm_of_degree_eq hmem hdeg]
  exact H.homogeneousMk_aeval_of_isWeightedHomogeneous hG hmem

/-- The degree of the value of a nonzero polynomial is its weighted total degree, and the initial
form of the value is `Φ` of the top weighted-homogeneous component. -/
theorem degree_aeval_eq_and_initialForm {F : MvPolynomial σ L} (hF : F ≠ 0) :
    ν (aeval x F) = ((weightedTotalDegree w F : M) : WithBot M) ∧
      ν.initialForm (aeval x F) =
        Φ (weightedHomogeneousComponent w (weightedTotalDegree w F) F) := by
  classical
  set d := weightedTotalDegree w F with hd
  set G := weightedHomogeneousComponent w d F with hG
  have hGne : G ≠ 0 := weightedHomogeneousComponent_weightedTotalDegree_ne_zero w hF
  have hGhom : IsWeightedHomogeneous w G d :=
    weightedHomogeneousComponent_isWeightedHomogeneous d F
  have hGdeg := H.degree_aeval_eq_of_isWeightedHomogeneous hGhom hGne
  have hrest : ν (aeval x (F - G)) < (d : WithBot M) := by
    rcases weightedTotalDegree_sub_weightedHomogeneousComponent_lt w F with h0 | hlt
    · rw [h0, _root_.map_zero, ν.map_zero]
      exact WithBot.bot_lt_coe _
    · exact lt_of_le_of_lt (H.degree_aeval_le (F - G)) (WithBot.coe_lt_coe.mpr hlt)
  have hsplit : aeval x F = aeval x G + aeval x (F - G) := by
    rw [← _root_.map_add, add_sub_cancel]
  have hdegF : ν (aeval x F) = (d : WithBot M) := by
    rw [hsplit, ν.degree_add_eq_of_lt (by rw [hGdeg]; exact hrest), hGdeg]
  refine ⟨hdegF, ?_⟩
  have hmemF := (ν.mem_filtrationLE_iff _ _).mpr hdegF.le
  have hmemG := (ν.mem_filtrationLE_iff _ _).mpr hGdeg.le
  have hmemR := (ν.mem_filtrationLE_iff _ _).mpr hrest.le
  rw [← ν.homogeneousMk_eq_initialForm_of_degree_eq hmemF hdegF]
  have hsum : (⟨aeval x F, hmemF⟩ : ν.filtrationLE d) =
      ⟨aeval x G, hmemG⟩ + ⟨aeval x (F - G), hmemR⟩ := Subtype.ext hsplit
  rw [hsum, _root_.map_add, H.homogeneousMk_aeval_of_isWeightedHomogeneous hGhom hmemG,
    ν.homogeneousMk_eq_zero_of_degree_lt hmemR hrest, add_zero]

/-- The degree of the value of a nonzero polynomial is its weighted total degree. -/
theorem degree_aeval_eq {F : MvPolynomial σ L} (hF : F ≠ 0) :
    ν (aeval x F) = ((weightedTotalDegree w F : M) : WithBot M) :=
  (H.degree_aeval_eq_and_initialForm hF).1

/-- Evaluation at `x` is injective: the `x i` are algebraically independent over `L`. -/
theorem aeval_injective : Function.Injective (aeval (R := L) x) := by
  refine (injective_iff_map_eq_zero _).mpr fun F hF ↦ ?_
  by_contra hne
  have h := H.degree_aeval_eq hne
  rw [hF, ν.map_zero] at h
  exact WithBot.bot_ne_coe h

end IsInitialFormCoordinates

end MaxAddDegree
