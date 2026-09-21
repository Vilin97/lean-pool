/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.TruncationPolynomial

/-!
# The coefficient of `X_{B₀}^e` in the polynomial of a translated truncation

Fix a variable `B₀` of degree `deg B₀ < α` and assume evaluation injective below `α`. A series `u`
with `v_J(u) < ω^{β+1}`, `β < α`, is *free of `X_{B₀}`* (`FreeOfVariable`) if neither `pol(u)` nor
`pol(u^{|γ})`, for all `γ < 0` sufficiently close to `0`, involves `X_{B₀}`. Constants are free of
`X_{B₀}`; so are the lifts `b_B` of the variables `B ≠ B₀` of degree at most `deg B₀`, since a
polynomial of degree below `deg B₀` cannot involve `X_{B₀}`; and sums, scalar multiples, products
and powers of series free of `X_{B₀}` are free of `X_{B₀}` (degrees permitting), by the
convolution formula read in polynomials [Ber00, Lem. 7.5], because in every term each factor is
either free of `X_{B₀}` or untruncated.

For `u` free of `X_{B₀}` and the lift `b_{B₀}`, the polynomial of `(b_{B₀}^e u)^{|γ}`, expanded in
powers of `X_{B₀}`, has no coefficient above `e`, and its coefficient of `X_{B₀}^e` is
`pol(u^{|γ})`: by induction on `e` through the convolution formula with the factors `b_{B₀}` and
`b_{B₀}^{e-1} u`, the only term reaching `X_{B₀}^e` is the boundary term
`X_{B₀} · pol((b_{B₀}^{e-1} u)^{|γ})`, every translated truncation of `b_{B₀}` at a cutoff `ζ < 0`
being free of `X_{B₀}`. For `u = 1` the coefficient of `X_{B₀}^{e-1}` is `e · pol(b_{B₀}^{|γ})`, by
the same induction. These are the two leading-coefficient identities used in the limit step.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci MvPolynomial OrdinalGraded

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] {ι : Type w} [DecidableEq ι] {wt : ι → NatOrdinal}
  {x : ι → PrincipalSubring K}

namespace Lifts

variable (σ : Lifts wt x) (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)
  {α : NatOrdinal} (hinj : ∀ β < α, InjectiveAt K wt x β) (B₀ : ι)

/-! ### Series free of `X_{B₀}` -/

variable (α) in
/-- A series `u` with `v_J(u) < ω^{β+1}`, `β < α`, is free of `X_{B₀}` if `pol u` and the
polynomials `pol(u^{|γ})` of its translated truncations, for all `γ < 0` sufficiently close to `0`,
do not involve `X_{B₀}`. -/
structure FreeOfVariable (u : Series K) (β : NatOrdinal) : Prop where
  /-- `u ∈ J_{ω^(β+1)}`. -/
  lt : ordinalValue u < ω^ (β + 1)
  /-- `β < α`. -/
  beta_lt : β < α
  /-- `pol u` does not involve `X_{B₀}`. -/
  pol_mem : σ.pol hx α u ∈ supported K {B₀}ᶜ
  /-- The polynomials of the translated truncations, for all `γ < 0` sufficiently close to `0`, do
  not involve `X_{B₀}`. -/
  exists_forall : ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 →
    σ.pol hx α (translatedTruncation (u : K⟦ℝ⟧) γ) ∈ supported K {B₀}ᶜ

include hinj

omit [DecidableEq ι] in
/-- Constants are free of `X_{B₀}` (in degree `0`, when `0 < α`). -/
theorem freeOfVariable_C (hα : 0 < α) (k : K) :
    σ.FreeOfVariable hx α B₀ ((HahnSeries.Nonpositive.C : K →+* Series K) k) 0 where
  lt := ordinalValue_C_lt_wpow_one k
  beta_lt := hα
  pol_mem := by
    have h1 : (HahnSeries.Nonpositive.C : K →+* Series K) k =
        aeval σ.lift (C k : MvPolynomial ι K) := by
      rw [aeval_C, HahnSeries.Nonpositive.algebraMap_apply]
    have hC : DegreeLT wt (C k : MvPolynomial ι K) α := degreeLT_iff.mpr fun d hd ↦ by
      classical
      rw [support_C] at hd
      split_ifs at hd with hk
      · exact absurd hd (Finset.notMem_empty d)
      · rw [Finset.mem_singleton] at hd
        rw [hd, map_zero]
        exact hα
    rw [h1, σ.pol_aeval hx hinj hC]
    exact Subalgebra.algebraMap_mem _ k
  exists_forall := ⟨1, one_pos, fun γ _ hγ ↦ by
    rw [σ.pol_translatedTruncation_C hx hinj k hγ]
    exact Subalgebra.zero_mem _⟩

omit [DecidableEq ι] in
/-- `1` is free of `X_{B₀}`. -/
theorem freeOfVariable_one (hα : 0 < α) : σ.FreeOfVariable hx α B₀ 1 0 := by
  have := σ.freeOfVariable_C hx hinj B₀ hα 1
  rwa [map_one] at this

omit [DecidableEq ι] in
/-- The lift of a variable `i ≠ B₀` of degree at most `wt B₀ < α` is free of `X_{B₀}`. -/
theorem freeOfVariable_lift (hg : wt B₀ < α) {i : ι} (hi : i ≠ B₀) (hwt : wt i ≤ wt B₀) :
    σ.FreeOfVariable hx α B₀ (σ.lift i) (wt i) where
  lt := Berarducci.Represents.ordinalValue_lt (σ.represents i)
  beta_lt := hwt.trans_lt hg
  pol_mem := by
    have h1 : σ.lift i = aeval σ.lift (X i : MvPolynomial ι K) := (aeval_X _ i).symm
    have hX : DegreeLT wt (X i : MvPolynomial ι K) α := degreeLT_iff.mpr fun d hd ↦ by
      rw [support_X, Finset.mem_singleton] at hd
      rw [hd, Finsupp.weight_single, one_smul]
      exact hwt.trans_lt hg
    rw [h1, σ.pol_aeval hx hinj hX, X_mem_supported]
    exact hi
  exists_forall := by
    obtain ⟨ε, hε, h⟩ :=
      exists_forall_ordinalValue_translatedTruncation_lt
        (Berarducci.Represents.ordinalValue_lt (σ.represents i))
    refine ⟨ε, hε, fun γ hγε hγ0 ↦ ?_⟩
    have hlt := σ.pol_degreeLT_of_lt hx hinj (hwt.trans_lt hg).le (h γ hγε hγ0)
    exact mem_supported_of_forall_weight_lt B₀ wt fun d hd ↦
      (degreeLT_iff.mp hlt d hd).trans_le hwt

omit [DecidableEq ι] in
variable {σ hx B₀} in
/-- The product of two series free of `X_{B₀}` is free of `X_{B₀}`, when the sum of their degrees
stays below `α`. -/
theorem FreeOfVariable.mul {u u' : Series K} {β β' : NatOrdinal} (hu : σ.FreeOfVariable hx α B₀ u β)
    (hu' : σ.FreeOfVariable hx α B₀ u' β') (h : β + β' < α) :
    σ.FreeOfVariable hx α B₀ (u * u') (β + β') where
  lt := ordinalValue_mul_lt_wpow_add_one hu.lt hu'.lt
  beta_lt := h
  pol_mem := by
    have hβα : β + 1 ≤ α := Order.add_one_le_of_lt hu.beta_lt
    have hβ'α : β' + 1 ≤ α := Order.add_one_le_of_lt hu'.beta_lt
    have hmul := σ.pol_mul hx hinj (hu.lt.trans_le (NatOrdinal.wpow_le_wpow.mpr hβα))
      (hu'.lt.trans_le (NatOrdinal.wpow_le_wpow.mpr hβ'α))
      (((σ.pol_degreeLE hx hinj hu.beta_lt hu.lt).mul
        (σ.pol_degreeLE hx hinj hu'.beta_lt hu'.lt)).degreeLT h)
    rw [hmul.2]
    exact Subalgebra.mul_mem _ hu.pol_mem hu'.pol_mem
  exists_forall := by
    obtain ⟨ε₁, hε₁, h₁⟩ := hu.exists_forall
    obtain ⟨ε₂, hε₂, h₂⟩ := hu'.exists_forall
    obtain ⟨ε₃, hε₃, h₃⟩ := σ.exists_forall_pol_translatedTruncation_mul hx hinj hu.lt hu'.lt
      hu.beta_lt hu'.beta_lt h.le
    refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), fun γ hγε hγ0 ↦ ?_⟩
    have hγ₁ : -ε₁ < γ := by have := min_le_left ε₁ (min ε₂ ε₃); linarith
    have hγ₂ : -ε₂ < γ := by
      have := (min_le_right ε₁ (min ε₂ ε₃)).trans (min_le_left ε₂ ε₃); linarith
    have hγ₃ : -ε₃ < γ := by
      have := (min_le_right ε₁ (min ε₂ ε₃)).trans (min_le_right ε₂ ε₃); linarith
    rw [h₃ γ hγ₃ hγ0 _ subset_rfl fun β hβ ↦ mem_Icc_of_mem_convolutionIndex hβ]
    refine Subalgebra.sum_mem _ fun β hβ ↦ Subalgebra.mul_mem _ ?_ ?_
    · obtain ⟨hγβ, hβ0⟩ := mem_Icc_of_mem_convolutionIndex hβ
      rcases eq_or_lt_of_le hβ0 with rfl | hβneg
      · rw [translatedTruncation_zero]; exact hu.pol_mem
      · exact h₁ β (by linarith) hβneg
    · obtain ⟨hγβ, hβ0⟩ := mem_Icc_of_mem_convolutionIndex hβ
      rcases eq_or_lt_of_le (sub_nonpos.mpr hγβ) with h0 | hneg
      · rw [h0, translatedTruncation_zero]; exact hu'.pol_mem
      · exact h₂ (γ - β) (by linarith) hneg

omit [DecidableEq ι] in
variable {σ hx B₀} in
/-- Powers of a series free of `X_{B₀}` are free of `X_{B₀}`, degrees permitting. -/
theorem FreeOfVariable.pow {u : Series K} {β : NatOrdinal} (hu : σ.FreeOfVariable hx α B₀ u β)
    (n : ℕ)
    (h : n • β < α) : σ.FreeOfVariable hx α B₀ (u ^ n) (n • β) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    exact σ.freeOfVariable_one hx hinj B₀ (zero_smul ℕ β ▸ h)
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    have hn : n • β < α := NatOrdinal.le_add_right.trans_lt (succ_nsmul β n ▸ h)
    exact (ih hn).mul hinj hu (succ_nsmul β n ▸ h)

omit [DecidableEq ι] in
/-- Finite products of series free of `X_{B₀}` are free of `X_{B₀}`, degrees permitting. -/
theorem freeOfVariable_prod {ι' : Type*} (hα : 0 < α) (s : Finset ι') (f : ι' → Series K)
    (g : ι' → NatOrdinal) (h : ∀ i ∈ s, σ.FreeOfVariable hx α B₀ (f i) (g i))
    (hsum : ∑ i ∈ s, g i < α) :
    σ.FreeOfVariable hx α B₀ (∏ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using σ.freeOfVariable_one hx hinj B₀ hα
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at hsum
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hs : ∑ i ∈ s, g i < α := NatOrdinal.le_add_left.trans_lt hsum
    exact (h a (Finset.mem_insert_self a s)).mul hinj
      (ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi)) hs) hsum

omit [DecidableEq ι] in
/-- The evaluation at the lifts of a monomial not involving `X_{B₀}`, in variables of degree at
most `wt B₀`, of degree below `α`, is free of `X_{B₀}`. -/
theorem freeOfVariable_aeval_monomial (hg : wt B₀ < α) (d : ι →₀ ℕ) (hd : d B₀ = 0)
    (hwt : ∀ i ∈ d.support, wt i ≤ wt B₀) (hdegree : Finsupp.weight wt d < α) :
    σ.FreeOfVariable hx α B₀ (∏ i ∈ d.support, σ.lift i ^ d i) (Finsupp.weight wt d) := by
  have hα : 0 < α := (bot_le : (0 : NatOrdinal) ≤ wt B₀).trans_lt hg
  rw [Finsupp.weight_apply, Finsupp.sum]
  rw [Finsupp.weight_apply, Finsupp.sum] at hdegree
  refine σ.freeOfVariable_prod hx hinj B₀ hα d.support (fun i ↦ σ.lift i ^ d i)
    (fun i ↦ d i • wt i) ?_ hdegree
  intro i hi
  have hi0 : i ≠ B₀ := fun h ↦ (Finsupp.mem_support_iff.mp hi) (h ▸ hd)
  have hlt : d i • wt i < α := (Finset.single_le_sum (f := fun i ↦ d i • wt i)
    (fun _ _ ↦ bot_le) hi).trans_lt hdegree
  exact (σ.freeOfVariable_lift hx hinj B₀ hg hi0 (hwt i hi)).pow hinj (d i) hlt

omit [DecidableEq ι] in
/-- `0` is free of `X_{B₀}` in every degree below `α`. -/
theorem freeOfVariable_zero {β : NatOrdinal} (hβ : β < α) : σ.FreeOfVariable hx α B₀ 0 β where
  lt := by rw [ordinalValue_zero]; exact NatOrdinal.wpow_pos _
  beta_lt := hβ
  pol_mem := by rw [σ.pol_zero hx hinj]; exact Subalgebra.zero_mem _
  exists_forall := ⟨1, one_pos, fun γ _ _ ↦ by
    rw [Subring.coe_zero, translatedTruncation_zero_input, σ.pol_zero hx hinj]
    exact Subalgebra.zero_mem _⟩

omit [DecidableEq ι] in
variable {σ hx B₀} in
/-- The sum of two series free of `X_{B₀}` of the same degree is free of `X_{B₀}`. -/
theorem FreeOfVariable.add {u u' : Series K} {β : NatOrdinal} (hu : σ.FreeOfVariable hx α B₀ u β)
    (hu' : σ.FreeOfVariable hx α B₀ u' β) : σ.FreeOfVariable hx α B₀ (u + u') β where
  lt := (ordinalValue_add_le_max u u').trans_lt (max_lt hu.lt hu'.lt)
  beta_lt := hu.beta_lt
  pol_mem := by
    have hβα : β + 1 ≤ α := Order.add_one_le_of_lt hu.beta_lt
    rw [σ.pol_add hx hinj (hu.lt.trans_le (NatOrdinal.wpow_le_wpow.mpr hβα))
      (hu'.lt.trans_le (NatOrdinal.wpow_le_wpow.mpr hβα))]
    exact Subalgebra.add_mem _ hu.pol_mem hu'.pol_mem
  exists_forall := by
    obtain ⟨ε₁, hε₁, h₁⟩ := hu.exists_forall
    obtain ⟨ε₂, hε₂, h₂⟩ := hu'.exists_forall
    obtain ⟨ε₃, hε₃, h₃⟩ := exists_forall_ordinalValue_translatedTruncation_lt hu.lt
    obtain ⟨ε₄, hε₄, h₄⟩ := exists_forall_ordinalValue_translatedTruncation_lt hu'.lt
    refine ⟨min (min ε₁ ε₂) (min ε₃ ε₄), lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄),
      fun γ hγε hγ0 ↦ ?_⟩
    have hγ₁ : -ε₁ < γ := by
      have := (min_le_left (min ε₁ ε₂) (min ε₃ ε₄)).trans (min_le_left ε₁ ε₂); linarith
    have hγ₂ : -ε₂ < γ := by
      have := (min_le_left (min ε₁ ε₂) (min ε₃ ε₄)).trans (min_le_right ε₁ ε₂); linarith
    have hγ₃ : -ε₃ < γ := by
      have := (min_le_right (min ε₁ ε₂) (min ε₃ ε₄)).trans (min_le_left ε₃ ε₄); linarith
    have hγ₄ : -ε₄ < γ := by
      have := (min_le_right (min ε₁ ε₂) (min ε₃ ε₄)).trans (min_le_right ε₃ ε₄); linarith
    rw [Subring.coe_add, translatedTruncation_add,
      σ.pol_add hx hinj ((h₃ γ hγ₃ hγ0).trans_le (NatOrdinal.wpow_le_wpow.mpr hu.beta_lt.le))
        ((h₄ γ hγ₄ hγ0).trans_le (NatOrdinal.wpow_le_wpow.mpr hu.beta_lt.le))]
    exact Subalgebra.add_mem _ (h₁ γ hγ₁ hγ0) (h₂ γ hγ₂ hγ0)

omit [DecidableEq ι] in
variable {σ hx B₀} in
/-- Scalar multiples of a series free of `X_{B₀}` are free of `X_{B₀}`. -/
theorem FreeOfVariable.C_mul (k : K) {u : Series K} {β : NatOrdinal}
    (hu : σ.FreeOfVariable hx α B₀ u β) :
    σ.FreeOfVariable hx α B₀ ((HahnSeries.Nonpositive.C : K →+* Series K) k * u) β := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [map_zero, zero_mul]; exact σ.freeOfVariable_zero hx hinj B₀ hu.beta_lt
  have hβα : β + 1 ≤ α := Order.add_one_le_of_lt hu.beta_lt
  refine ⟨by rw [ordinalValue_C_mul hk]; exact hu.lt, hu.beta_lt, ?_, ?_⟩
  · rw [σ.pol_C_mul hx hinj k (hu.lt.trans_le (NatOrdinal.wpow_le_wpow.mpr hβα))]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ k) hu.pol_mem
  · obtain ⟨ε₁, hε₁, h₁⟩ := hu.exists_forall
    obtain ⟨ε₂, hε₂, h₂⟩ := exists_forall_ordinalValue_translatedTruncation_lt hu.lt
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun γ hγε hγ0 ↦ ?_⟩
    have hγ₁ : -ε₁ < γ := by have := min_le_left ε₁ ε₂; linarith
    have hγ₂ : -ε₂ < γ := by have := min_le_right ε₁ ε₂; linarith
    rw [Subring.coe_mul, HahnSeries.Nonpositive.coe_C, translatedTruncation_C_mul,
      σ.pol_C_mul hx hinj k ((h₂ γ hγ₂ hγ0).trans_le
        (NatOrdinal.wpow_le_wpow.mpr hu.beta_lt.le))]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ k) (h₁ γ hγ₁ hγ0)

omit [DecidableEq ι] in
/-- Finite sums of series free of `X_{B₀}`, all of one degree, are free of `X_{B₀}`. -/
theorem freeOfVariable_sum {ι' : Type*} {β : NatOrdinal} (hβ : β < α) (s : Finset ι')
    (f : ι' → Series K) (h : ∀ i ∈ s, σ.FreeOfVariable hx α B₀ (f i) β) :
    σ.FreeOfVariable hx α B₀ (∑ i ∈ s, f i) β := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact σ.freeOfVariable_zero hx hinj B₀ hβ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add hinj
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

omit [DecidableEq ι] in
/-- The evaluation at the lifts of a polynomial not involving `X_{B₀}`, homogeneous of degree
`β < α`, in variables of degree at most `wt B₀`, is free of `X_{B₀}`. -/
theorem freeOfVariable_aeval (hg : wt B₀ < α) {F : MvPolynomial ι K} {β : NatOrdinal}
    (hF : IsWeightedHomogeneous wt F β) (hβ : β < α) (hmem : F ∈ supported K {B₀}ᶜ)
    (hvars : ∀ i ∈ F.vars, wt i ≤ wt B₀) : σ.FreeOfVariable hx α B₀ (aeval σ.lift F) β := by
  classical
  conv => rw [F.as_sum]
  rw [map_sum]
  refine σ.freeOfVariable_sum hx hinj B₀ hβ _ _ fun d hd ↦ ?_
  have hdw : Finsupp.weight wt d = β := hF (mem_support_iff.mp hd)
  have hmono : (monomial d (coeff d F) : MvPolynomial ι K) = C (coeff d F) * monomial d 1 := by
    rw [C_mul_monomial, mul_one]
  rw [hmono, map_mul, aeval_C, HahnSeries.Nonpositive.algebraMap_apply, aeval_monomial, map_one,
    one_mul, Finsupp.prod]
  refine FreeOfVariable.C_mul hinj _ ?_
  have hd0 : d B₀ = 0 := by
    by_contra h0
    have hv : B₀ ∈ F.vars :=
      (mem_vars_iff_mem_support B₀).mpr ⟨d, hd, Finsupp.mem_support_iff.mpr h0⟩
    exact (mem_supported.mp hmem) hv rfl
  have hwt' : ∀ i ∈ d.support, wt i ≤ wt B₀ := fun i hi ↦
    hvars i ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)
  rw [← hdw]
  exact σ.freeOfVariable_aeval_monomial hx hinj B₀ hg d hd0 hwt' (hdw ▸ hβ)

/-! ### The coefficient of `X_{B₀}^e` -/

omit [DecidableEq ι] in
/-- The polynomial of `b_{B₀}^e` is `X_{B₀}^e` when `e • wt B₀ < α`. -/
theorem pol_lift_pow (e : ℕ) (he : e • wt B₀ < α) :
    σ.pol hx α (σ.lift B₀ ^ e) = X B₀ ^ e := by
  have h1 : σ.lift B₀ ^ e = aeval σ.lift (X B₀ ^ e : MvPolynomial ι K) := by
    rw [map_pow, aeval_X]
  have hX : DegreeLT wt (X B₀ ^ e : MvPolynomial ι K) α := degreeLT_iff.mpr fun d hd ↦ by
    classical
    rw [X_pow_eq_monomial, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hd
    rw [hd, Finsupp.weight_single]
    exact he
  rw [h1, σ.pol_aeval hx hinj hX]

omit [DecidableEq ι] in
/-- The polynomials of the translated truncations `b_{B₀}^{|γ}`, for all `γ < 0` sufficiently close
to `0`, do not involve `X_{B₀}`. -/
@[blueprint "lem:proper-truncation-omits-variable"
  (phase := "Translated truncations")
  (title := "Omission of a maximal-weight variable from proper truncation representatives")
  (statement := /--
    Let $K$ be a field, let $(x_i)_{i\in I}$ be a minimal homogeneous
    generating system of $\widehat{\mathrm P}$ with
    $x_i\in\mathrm P_{w_i}$, and choose representatives
    $b_i\in K((\mathbb R^{\le0}))$. Fix $\alpha<\omega_1$, and suppose that
    evaluation at $(x_i)$ is injective on weighted-homogeneous polynomials of
    every degree below $\alpha$. For $v_J(u)<\omega^\alpha$, denote by $P_u$
    the unique polynomial whose monomials have weight below $\alpha$ and for
    which $P_u(b_i)\equiv u\pmod J$.

    If $B_0\in I$ and $w_{B_0}<\alpha$, then there is $\varepsilon>0$ such
    that
    \[
      X_{B_0}\notin\operatorname{vars}(P_{b_{B_0}^{|\gamma}})
      \qquad(-\varepsilon<\gamma<0).
    \]
  -/)
  (proof := /--
  Since $b_{B_0}$ represents $x_{B_0}\in\mathrm P_{w_{B_0}}$, its ordinal
  value is below $\omega^{w_{B_0}+1}$. By
  \ref{lem:truncation-drop}, for every $\gamma<0$ sufficiently close to $0$,
  \[
    v_J(b_{B_0}^{|\gamma})<\omega^{w_{B_0}}.
  \]
  Apply \ref{prop:polynomial-representative-exists} at $w_{B_0}$. Its
  polynomial has every monomial of weight below $w_{B_0}$, and uniqueness from
  \ref{prop:polynomial-evaluation-ordinal-value} identifies it with the
  representative $P_{b_{B_0}^{|\gamma}}$ chosen below $\alpha$. A monomial
  involving $X_{B_0}$ has weight at least $w_{B_0}$, so no such monomial can
  occur.
  -/)]
theorem exists_forall_pol_translatedTruncation_lift_mem (hg : wt B₀ < α) :
    ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 →
      σ.pol hx α (translatedTruncation (σ.lift B₀ : K⟦ℝ⟧) γ) ∈ supported K {B₀}ᶜ := by
  obtain ⟨ε, hε, h⟩ :=
    exists_forall_ordinalValue_translatedTruncation_lt
      (Berarducci.Represents.ordinalValue_lt (σ.represents B₀))
  refine ⟨ε, hε, fun γ hγε hγ0 ↦ ?_⟩
  exact mem_supported_of_forall_weight_lt B₀ wt
    (degreeLT_iff.mp (σ.pol_degreeLT_of_lt hx hinj hg.le (h γ hγε hγ0)))

omit [DecidableEq ι] hinj in
/-- The sum over a finite set containing `0` and `γ ≠ 0`, split at these two points. -/
theorem sum_eq_add_add_sum_erase {S : Finset ℝ} {γ : ℝ} (h0 : (0 : ℝ) ∈ S) (hγ : γ ∈ S)
    (hne : γ ≠ 0) (f : ℝ → MvPolynomial ι K) :
    ∑ β ∈ S, f β = f 0 + f γ + ∑ β ∈ (S.erase 0).erase γ, f β := by
  rw [add_assoc, Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne, hγ⟩),
    Finset.add_sum_erase _ _ h0]

/-- **The coefficient of `X_{B₀}^e`.** For `u` free of `X_{B₀}`, of degree `β` with
`e • wt B₀ ⊕ β ≤ α`, and all `γ < 0` sufficiently close to `0`: the polynomial of
`(b_{B₀}^e · u)^{|γ}` has no coefficient of `X_{B₀}^k` for `k > e`, and its coefficient of
`X_{B₀}^e` is `pol(u^{|γ})`. -/
@[blueprint "lem:leading-coefficient-of-truncated-product"
  (phase := "Translated truncations")
  (title := "Leading coefficient after translated truncation")
  (statement := /--
    Let $(x_i)_{i\in I}$ be a minimal homogeneous generating system of
    $\widehat{\mathrm P}$, with $x_i\in\mathrm P_{w_i}$, and choose series
    $b_i$ representing the $x_i$. Assume that evaluation at $(x_i)$ is
    injective in every weighted degree below $\alpha<\omega_1$, and write
    $P_a$ for the resulting polynomial representative of a series $a$ of
    ordinal value below $\omega^\alpha$.

    Fix $B_0\in I$ with $w_{B_0}<\alpha$. Let $\beta<\alpha$ and let
    $u\in K((\mathbb R^{\le0}))$ satisfy $v_J(u)<\omega^{\beta+1}$. Suppose
    that $P_u$ does not involve $X_{B_0}$ and that the same holds for
    $P_{u^{|\gamma}}$ for every $\gamma<0$ sufficiently close to $0$.

    If $(e\odot w_{B_0})\oplus\beta\le\alpha$, then, for every
    $\gamma<0$ sufficiently close to $0$, the polynomial
    $P_{(b_{B_0}^eu)^{|\gamma}}$ has degree at most $e$ in $X_{B_0}$ and
    \[
      [X_{B_0}^e]\,P_{(b_{B_0}^eu)^{|\gamma}}=P_{u^{|\gamma}}.
    \]
  -/)
  (proof := /--
  Induct on $e$. The case $e=0$ is the hypothesis on $u$. For the successor
  step, apply \ref{lem:polynomial-convolution-formula} to
  $b_{B_0}(b_{B_0}^eu)$. The summand at cutoff $0$ is
  $X_{B_0}P_{(b_{B_0}^eu)^{|\gamma}}$, whose coefficients are controlled by
  the induction hypothesis.

  In every other summand the first factor is a proper translated truncation
  of $b_{B_0}$, so its polynomial omits $X_{B_0}$ by
  \ref{lem:proper-truncation-omits-variable}. At cutoff $\gamma$, the second
  translated truncation is $b_{B_0}^eu$, whose unique polynomial
  representative with monomial weights below $\alpha$ is $P_uX_{B_0}^e$;
  at the interior cutoffs the induction hypothesis bounds its
  $X_{B_0}$-degree by $e$. Thus only the cutoff-$0$ summand can contribute in
  degree $e+1$, and its coefficient there is $P_{u^{|\gamma}}$.
  -/)]
theorem exists_forall_xCoeff_pol_translatedTruncation_pow_mul (hg : wt B₀ < α) {u : Series K}
    {β : NatOrdinal} (hu : σ.FreeOfVariable hx α B₀ u β) (e : ℕ) (he : e • wt B₀ + β ≤ α) :
    ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 →
      (∀ k, e < k →
        xCoeff B₀ k (σ.pol hx α (translatedTruncation ((σ.lift B₀ ^ e * u : Series K) : K⟦ℝ⟧) γ))
          = 0) ∧
      xCoeff B₀ e (σ.pol hx α (translatedTruncation ((σ.lift B₀ ^ e * u : Series K) : K⟦ℝ⟧) γ)) =
        σ.pol hx α (translatedTruncation (u : K⟦ℝ⟧) γ) := by
  have hg0 : wt B₀ ≠ 0 := hx.ne_zero B₀
  induction e with
  | zero =>
    obtain ⟨ε, hε, h⟩ := hu.exists_forall
    refine ⟨ε, hε, fun γ hγε hγ0 ↦ ?_⟩
    rw [pow_zero, one_mul]
    refine ⟨fun k hk ↦ ?_, ?_⟩
    · rw [xCoeff_of_mem_supported B₀ (h γ hγε hγ0), if_neg (Nat.pos_iff_ne_zero.mp hk)]
    · rw [xCoeff_of_mem_supported B₀ (h γ hγε hγ0), if_pos rfl]
  | succ e ih =>
    -- degrees
    have hstep : e • wt B₀ + β < (e + 1) • wt B₀ + β := by
      rw [succ_nsmul, add_right_comm]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hg0)
    have he' : e • wt B₀ + β < α := hstep.trans_le he
    obtain ⟨ε₁, hε₁, h₁⟩ := ih he'.le
    -- the factor `b_{B₀}^e · u`
    have hw : ordinalValue (σ.lift B₀ ^ e * u) < ω^ (e • wt B₀ + β + 1) :=
      ordinalValue_mul_lt_wpow_add_one
        (Berarducci.Represents.ordinalValue_lt ((σ.represents B₀).pow e)) hu.lt
    have hsum : wt B₀ + (e • wt B₀ + β) ≤ α := by
      rw [← add_assoc, add_comm (wt B₀), ← succ_nsmul]
      exact he
    obtain ⟨ε₂, hε₂, h₂⟩ := σ.exists_forall_pol_translatedTruncation_mul hx hinj
      (Berarducci.Represents.ordinalValue_lt (σ.represents B₀)) hw hg he' hsum
    obtain ⟨ε₃, hε₃, h₃⟩ := σ.exists_forall_pol_translatedTruncation_lift_mem hx hinj B₀ hg
    refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), fun γ hγε hγ0 ↦ ?_⟩
    have hγ₁ : -ε₁ < γ := by have := min_le_left ε₁ (min ε₂ ε₃); linarith
    have hγ₂ : -ε₂ < γ := by
      have := (min_le_right ε₁ (min ε₂ ε₃)).trans (min_le_left ε₂ ε₃); linarith
    have hγ₃ : -ε₃ < γ := by
      have := (min_le_right ε₁ (min ε₂ ε₃)).trans (min_le_right ε₂ ε₃); linarith
    -- the convolution sum over `S = {0, γ} ∪ index`
    set S : Finset ℝ := insert 0 (insert γ
      (convolutionIndex (σ.lift B₀ : K⟦ℝ⟧) ((σ.lift B₀ ^ e * u : Series K) : K⟦ℝ⟧) γ)) with hS
    have hSsub : convolutionIndex (σ.lift B₀ : K⟦ℝ⟧) ((σ.lift B₀ ^ e * u : Series K) : K⟦ℝ⟧) γ ⊆
        S := (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    have hSIcc : (S : Set ℝ) ⊆ Set.Icc γ 0 := by
      intro β hβ
      rw [hS, Finset.coe_insert, Finset.coe_insert] at hβ
      rcases hβ with rfl | rfl | hβ
      · exact ⟨hγ0.le, le_rfl⟩
      · exact ⟨le_rfl, hγ0.le⟩
      · exact mem_Icc_of_mem_convolutionIndex hβ
    have h0S : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
    have hγS : γ ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hexp : σ.lift B₀ ^ (e + 1) * u = σ.lift B₀ * (σ.lift B₀ ^ e * u) := by ring
    set f : ℝ → MvPolynomial ι K := fun β ↦
      σ.pol hx α (translatedTruncation (σ.lift B₀ : K⟦ℝ⟧) β) *
        σ.pol hx α (translatedTruncation ((σ.lift B₀ ^ e * u : Series K) : K⟦ℝ⟧) (γ - β))
      with hf
    have hconv : σ.pol hx α (translatedTruncation ((σ.lift B₀ ^ (e + 1) * u : Series K) : K⟦ℝ⟧) γ)
        = f 0 + f γ + ∑ β ∈ (S.erase 0).erase γ, f β := by
      rw [hexp, h₂ γ hγ₂ hγ0 S hSsub hSIcc, ← sum_eq_add_add_sum_erase h0S hγS hγ0.ne]
    -- the three kinds of terms
    have hf0 : f 0 = X B₀ * σ.pol hx α
        (translatedTruncation ((σ.lift B₀ ^ e * u : Series K) : K⟦ℝ⟧) γ) := by
      rw [hf]
      simp only
      rw [translatedTruncation_zero, sub_zero]
      congr 1
      have := σ.pol_lift_pow hx hinj B₀ 1 (by rw [one_smul]; exact hg)
      rwa [pow_one, pow_one] at this
    have hfγ : f γ = σ.pol hx α (translatedTruncation (σ.lift B₀ : K⟦ℝ⟧) γ) *
        (σ.pol hx α u * X B₀ ^ e) := by
      rw [hf]
      simp only
      rw [sub_self, translatedTruncation_zero]
      congr 1
      have hβα : β + 1 ≤ α := Order.add_one_le_of_lt hu.beta_lt
      have hmul := σ.pol_mul hx hinj
        ((Berarducci.Represents.ordinalValue_lt ((σ.represents B₀).pow e)).trans_le
          (NatOrdinal.wpow_le_wpow.mpr
            (Order.add_one_le_of_lt (NatOrdinal.le_add_right.trans_lt he'))))
        (hu.lt.trans_le (NatOrdinal.wpow_le_wpow.mpr hβα))
        (by
          rw [σ.pol_lift_pow hx hinj B₀ e (NatOrdinal.le_add_right.trans_lt he')]
          exact (((isWeightedHomogeneous_X K wt B₀).pow e).degreeLE.mul
            (σ.pol_degreeLE hx hinj hu.beta_lt hu.lt)).degreeLT he')
      rw [hmul.2, σ.pol_lift_pow hx hinj B₀ e (NatOrdinal.le_add_right.trans_lt he'), mul_comm]
    have hfβ : ∀ β ∈ (S.erase 0).erase γ, ∀ k, e < k → xCoeff B₀ k (f β) = 0 := by
      intro β hβ k hk
      have hβne : β ≠ γ := (Finset.mem_erase.mp hβ).1
      have hβ0 : β ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hβ).2).1
      obtain ⟨hγβ, hβle⟩ := hSIcc (Finset.mem_erase.mp (Finset.mem_erase.mp hβ).2).2
      have hβneg : β < 0 := lt_of_le_of_ne hβle hβ0
      have hγβneg : γ - β < 0 := by
        rcases lt_or_eq_of_le hγβ with h | h
        · linarith
        · exact absurd h.symm hβne
      rw [hf]
      simp only
      rw [xCoeff_mul_of_mem_supported B₀ (h₃ β (by linarith) hβneg),
        (h₁ (γ - β) (by linarith) hγβneg).1 k hk, mul_zero]
    refine ⟨fun k hk ↦ ?_, ?_⟩
    · -- no coefficient above `e + 1`
      rw [hconv, map_add, map_add, hf0, hfγ, map_sum,
        Finset.sum_eq_zero fun β hβ ↦ hfβ β hβ k (by omega)]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [xCoeff_succ_X_mul, (h₁ γ hγ₁ hγ0).1 k' (by omega), ← mul_assoc,
        xCoeff_mul_X_pow B₀ (Subalgebra.mul_mem _ (h₃ γ hγ₃ hγ0) hu.pol_mem), if_neg (by omega),
        add_zero, add_zero]
    · -- the coefficient of `X_{B₀}^(e+1)`
      rw [hconv, map_add, map_add, hf0, hfγ, map_sum,
        Finset.sum_eq_zero fun β hβ ↦ hfβ β hβ (e + 1) (Nat.lt_succ_self e),
        xCoeff_succ_X_mul, (h₁ γ hγ₁ hγ0).2, ← mul_assoc,
        xCoeff_mul_X_pow B₀ (Subalgebra.mul_mem _ (h₃ γ hγ₃ hγ0) hu.pol_mem),
        if_neg (Nat.succ_ne_self e), add_zero, add_zero]

/-- **The coefficient of `X_{B₀}^e` for the pure power `b_{B₀}^{e+1}`.** For `(e + 1) • wt B₀ ≤ α`
and all `γ < 0` sufficiently close to `0`, the coefficient of `X_{B₀}^e` in the polynomial of
`(b_{B₀}^{e+1})^{|γ}` is `(e + 1) · pol(b_{B₀}^{|γ})`. -/
theorem exists_forall_xCoeff_pol_translatedTruncation_pow (hg : wt B₀ < α) (e : ℕ)
    (he : (e + 1) • wt B₀ ≤ α) :
    ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 →
      xCoeff B₀ e (σ.pol hx α (translatedTruncation ((σ.lift B₀ ^ (e + 1) : Series K) : K⟦ℝ⟧) γ))
        = (e + 1 : ℕ) • σ.pol hx α (translatedTruncation (σ.lift B₀ : K⟦ℝ⟧) γ) := by
  have hg0 : wt B₀ ≠ 0 := hx.ne_zero B₀
  have hα : 0 < α := (bot_le : (0 : NatOrdinal) ≤ wt B₀).trans_lt hg
  induction e with
  | zero =>
    obtain ⟨ε, hε, h⟩ := σ.exists_forall_pol_translatedTruncation_lift_mem hx hinj B₀ hg
    refine ⟨ε, hε, fun γ hγε hγ0 ↦ ?_⟩
    rw [zero_add, pow_one, xCoeff_of_mem_supported B₀ (h γ hγε hγ0), if_pos rfl, one_smul]
  | succ e ih =>
    have hstep : (e + 1) • wt B₀ < (e + 1 + 1) • wt B₀ := by
      rw [succ_nsmul (wt B₀) (e + 1)]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hg0)
    have he' : (e + 1) • wt B₀ < α := hstep.trans_le he
    obtain ⟨ε₁, hε₁, h₁⟩ := ih he'.le
    -- the coefficient of `X_{B₀}^{e+1}` for `b_{B₀}^{e+1} · 1`
    obtain ⟨ε₀, hε₀, h₀⟩ := σ.exists_forall_xCoeff_pol_translatedTruncation_pow_mul hx hinj B₀ hg
      (σ.freeOfVariable_one hx hinj B₀ hα) (e + 1) (by rw [add_zero]; exact he'.le)
    have hw : ordinalValue (σ.lift B₀ ^ (e + 1)) < ω^ ((e + 1) • wt B₀ + 1) :=
      (Berarducci.Represents.ordinalValue_lt ((σ.represents B₀).pow (e + 1)))
    have hsum : wt B₀ + (e + 1) • wt B₀ ≤ α := by
      rw [add_comm, ← succ_nsmul]
      exact he
    obtain ⟨ε₂, hε₂, h₂⟩ := σ.exists_forall_pol_translatedTruncation_mul hx hinj
      (Berarducci.Represents.ordinalValue_lt (σ.represents B₀)) hw hg he' hsum
    obtain ⟨ε₃, hε₃, h₃⟩ := σ.exists_forall_pol_translatedTruncation_lift_mem hx hinj B₀ hg
    refine ⟨min (min ε₀ ε₁) (min ε₂ ε₃), lt_min (lt_min hε₀ hε₁) (lt_min hε₂ hε₃),
      fun γ hγε hγ0 ↦ ?_⟩
    have hγ₀ : -ε₀ < γ := by
      have := (min_le_left (min ε₀ ε₁) (min ε₂ ε₃)).trans (min_le_left ε₀ ε₁); linarith
    have hγ₁ : -ε₁ < γ := by
      have := (min_le_left (min ε₀ ε₁) (min ε₂ ε₃)).trans (min_le_right ε₀ ε₁); linarith
    have hγ₂ : -ε₂ < γ := by
      have := (min_le_right (min ε₀ ε₁) (min ε₂ ε₃)).trans (min_le_left ε₂ ε₃); linarith
    have hγ₃ : -ε₃ < γ := by
      have := (min_le_right (min ε₀ ε₁) (min ε₂ ε₃)).trans (min_le_right ε₂ ε₃); linarith
    set S : Finset ℝ := insert 0 (insert γ
      (convolutionIndex (σ.lift B₀ : K⟦ℝ⟧) ((σ.lift B₀ ^ (e + 1) : Series K) : K⟦ℝ⟧) γ)) with hS
    have hSsub : convolutionIndex (σ.lift B₀ : K⟦ℝ⟧) ((σ.lift B₀ ^ (e + 1) : Series K) : K⟦ℝ⟧) γ ⊆
        S := (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    have hSIcc : (S : Set ℝ) ⊆ Set.Icc γ 0 := by
      intro β hβ
      rw [hS, Finset.coe_insert, Finset.coe_insert] at hβ
      rcases hβ with rfl | rfl | hβ
      · exact ⟨hγ0.le, le_rfl⟩
      · exact ⟨le_rfl, hγ0.le⟩
      · exact mem_Icc_of_mem_convolutionIndex hβ
    have h0S : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
    have hγS : γ ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hexp : σ.lift B₀ ^ (e + 1 + 1) = σ.lift B₀ * σ.lift B₀ ^ (e + 1) := by ring
    set f : ℝ → MvPolynomial ι K := fun β ↦
      σ.pol hx α (translatedTruncation (σ.lift B₀ : K⟦ℝ⟧) β) *
        σ.pol hx α (translatedTruncation ((σ.lift B₀ ^ (e + 1) : Series K) : K⟦ℝ⟧) (γ - β))
      with hf
    have hconv : σ.pol hx α (translatedTruncation ((σ.lift B₀ ^ (e + 1 + 1) : Series K) : K⟦ℝ⟧) γ)
        = f 0 + f γ + ∑ β ∈ (S.erase 0).erase γ, f β := by
      rw [hexp, h₂ γ hγ₂ hγ0 S hSsub hSIcc, ← sum_eq_add_add_sum_erase h0S hγS hγ0.ne]
    have hf0 : f 0 = X B₀ * σ.pol hx α
        (translatedTruncation ((σ.lift B₀ ^ (e + 1) : Series K) : K⟦ℝ⟧) γ) := by
      rw [hf]
      simp only
      rw [translatedTruncation_zero, sub_zero]
      congr 1
      have := σ.pol_lift_pow hx hinj B₀ 1 (by rw [one_smul]; exact hg)
      rwa [pow_one, pow_one] at this
    have hfγ : f γ = σ.pol hx α (translatedTruncation (σ.lift B₀ : K⟦ℝ⟧) γ) * X B₀ ^ (e + 1) := by
      rw [hf]
      simp only
      rw [sub_self, translatedTruncation_zero, σ.pol_lift_pow hx hinj B₀ (e + 1) he']
    -- the interior terms have no coefficient of `X_{B₀}^(e+1)`: the coefficient of `X_{B₀}^{e+1}`
    -- in the polynomial of a translated truncation of the pure power is the polynomial of a
    -- translated truncation of `1`, which is `0`
    have hfβ : ∀ β ∈ (S.erase 0).erase γ, xCoeff B₀ (e + 1) (f β) = 0 := by
      intro β hβ
      have hβne : β ≠ γ := (Finset.mem_erase.mp hβ).1
      have hβ0 : β ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hβ).2).1
      obtain ⟨hγβ, hβle⟩ := hSIcc (Finset.mem_erase.mp (Finset.mem_erase.mp hβ).2).2
      have hβneg : β < 0 := lt_of_le_of_ne hβle hβ0
      have hγβneg : γ - β < 0 := by
        rcases lt_or_eq_of_le hγβ with h | h
        · linarith
        · exact absurd h.symm hβne
      have h0' := (h₀ (γ - β) (by linarith) hγβneg).2
      rw [mul_one] at h0'
      have hC := σ.pol_translatedTruncation_C hx hinj (1 : K) hγβneg
      rw [map_one] at hC
      rw [hf]
      simp only
      rw [xCoeff_mul_of_mem_supported B₀ (h₃ β (by linarith) hβneg), h0', hC, mul_zero]
    rw [hconv, map_add, map_add, hf0, hfγ, map_sum, Finset.sum_eq_zero hfβ, add_zero,
      xCoeff_succ_X_mul, h₁ γ hγ₁ hγ0, xCoeff_mul_X_pow B₀ (h₃ γ hγ₃ hγ0), if_pos rfl]
    exact (succ_nsmul _ (e + 1)).symm

end Lifts

end Berarducci
