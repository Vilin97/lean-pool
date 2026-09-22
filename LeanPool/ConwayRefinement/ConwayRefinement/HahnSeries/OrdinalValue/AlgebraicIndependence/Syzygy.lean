/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.RemainderBound
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.PrincipalRepresentatives
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.ComponentsSpan
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.HomogeneousSpan

/-!
# High-degree components of truncated partial derivatives

Let `F ∈ K[X]` be homogeneous of degree `α` in variables of degree below `α`. Suppose that the
translated truncations of `F(b_𝓑)` have ordinal value below `ω^{α₁}` for all `γ < 0` sufficiently
close to `0`. Let `α''` be at least `α₁` and exceed the degree of every term of the expansion of a
monomial of `F` by the convolution formula in which at least two factors are translated truncations
at cutoffs `ζ < 0` (`TermDegree wt d k ρ` with `2 ≤ k`). For an index `B′` and a degree `τ` with
`α'' ≤ τ ⊕ deg B′`, the differentiated form of the Leibniz rule with remainder
(`exists_forall_pol_translatedTruncation_aeval_pderiv`) gives, for all `γ < 0` sufficiently close
to `0`,

`pol((∂F/∂X_{B′})(b_𝓑)^{|γ}) = ∂/∂X_{B′}[pol(G^{|γ})] − ∑_B (∂ pol(b_B^{|γ})/∂X_{B′}) ∂F/∂X_B
  − ∂R_γ/∂X_{B′} + R′_γ`,

with `R_γ`, `R′_γ` the remainders for `F` and for `∂F/∂X_{B′}`. The components of degree at least
`τ` of the first term and of the two remainder terms vanish: a monomial `m′` of any of them has
`X_{B′} m′` of degree below `α''`, hence `m′` of degree below `τ`. In the sum only the `B` with
`deg B > deg B′` contribute, `pol(b_B^{|γ})` having degree below `deg B`. Hence the components of
degree at least `τ` of `pol((∂F/∂X_{B′})(b_𝓑)^{|γ})` lie in the ideal `(∂F/∂X_B : deg B > deg B′)`.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial OrdinalGraded

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] {ι : Type w} {wt : ι → NatOrdinal}

/-! ### Partial derivatives -/

/-- A monomial `d'` of `∂_i p` has `d' · X_i` a monomial of `p`. -/
theorem add_single_mem_support_of_mem_support_pderiv {i : ι} {p : MvPolynomial ι K} {d' : ι →₀ ℕ}
    (hd' : d' ∈ (pderiv i p).support) : d' + Finsupp.single i 1 ∈ p.support := by
  obtain ⟨d, hd, hdi, rfl⟩ := exists_mem_support_of_mem_support_pderiv hd'
  rwa [tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hdi))]

/-- A polynomial all of whose monomials have degree below `g ≤ wt v` has no monomial containing
`X_v`: its partial derivative with respect to `X_v` vanishes. -/
theorem pderiv_eq_zero_of_degreeLT_le {P : MvPolynomial ι K} {g : NatOrdinal}
    (hP : DegreeLT wt P g) {v : ι} (hg : g ≤ wt v) : pderiv v P = 0 := by
  by_contra h
  obtain ⟨d', hd'⟩ := support_nonempty.mpr h
  obtain ⟨d, hd, hw⟩ := exists_add_eq_weight_of_mem_support_pderiv wt hd'
  have h1 := degreeLT_iff.mp hP d hd
  rw [← hw] at h1
  exact absurd (hg.trans (le_add_of_nonneg_left zero_le)) (not_le.mpr h1)

/-! ### Components of a product with a homogeneous factor -/

open scoped Classical in
/-- The component of degree `γ` of `P · Q`, `Q` homogeneous of degree `c`, is the component of
degree `γ ⊖ c` of `P` times `Q`, and `0` if `c \not\preccurlyeq γ` in the algebraic order. -/
theorem weightedHomogeneousComponent_mul_of_isWeightedHomogeneous {P Q : MvPolynomial ι K}
    {c : NatOrdinal} (hQ : IsWeightedHomogeneous wt Q c) (γ : NatOrdinal) :
    weightedHomogeneousComponent wt γ (P * Q) =
      if h : ∃ β, β + c = γ then weightedHomogeneousComponent wt (Classical.choose h) P * Q
      else 0 := by
  classical
  let := weightedGradedAlgebra K wt
  have hdec : ∀ (R : MvPolynomial ι K) (e : NatOrdinal),
      (DirectSum.decompose (weightedHomogeneousSubmodule K wt) R e : MvPolynomial ι K) =
        weightedHomogeneousComponent wt e R := fun R e ↦ by
    rw [← decompose'_apply]
    rfl
  have := coe_decompose_mul_of_left_mem (𝒜 := weightedHomogeneousSubmodule K wt)
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hQ) P γ
  rw [mul_comm, ← hdec, this]
  split_ifs with h
  · rw [hdec, mul_comm]
  · rfl

variable {x : ι → PrincipalSubring K}

namespace Lifts

variable (σ : Lifts wt x) (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)
  {α : NatOrdinal} (hinj : ∀ β < α, InjectiveAt K wt x β) (hσ : σ.IsPrincipal)
include hinj hσ

/-- **The polynomial of a truncated partial derivative, above a degree `τ`.** Let `F` be homogeneous
of degree `α` in variables of degree `< α`, whose evaluation `F(b_𝓑)` has translated truncations of
ordinal value below `ω^{α₁}` for all `γ < 0` sufficiently close to `0`, with `α₁ ≤ α''` and
`α₁ ≤ α`; let every term of the expansion of a monomial of `F` with at least two translated
truncations have degree below `α''`. For an index `v'` and a degree `τ` with
`α'' ≤ τ ⊕ wt v'`: for all `γ < 0` sufficiently close to `0`, the components of degree at least `τ`
of `pol((∂F/∂X_{v'})(b_𝓑)^{|γ})` lie in the ideal of the `∂F/∂X_j` over the variables `j` of `F`
with `wt v' < wt j`. The index `v'` need not occur in `F`. -/
@[blueprint "lem:differentiated-relation"
  (phase := "Translated truncations")
  (title := "High-degree Jacobian ideal membership")
  (statement := /--
    Let $K$ be a field, let $(x_i)_{i\in I}$ be a minimal homogeneous
    generating system of $\widehat{\mathrm P}$ with
    $x_i\in\mathrm P_{w_i}$, and choose principal series $b_i$ of degree
    $w_i$ representing the $x_i$. Assume that evaluation at $(x_i)$ is
    injective in every weighted degree below $\alpha<\omega_1$. For a series
    $a$ of ordinal value below $\omega^\alpha$, write $P_a$ for its resulting
    polynomial representative.

    Let $F\in K[X_i:i\in I]$ be weighted-homogeneous of degree $\alpha$, and
    suppose $w_i<\alpha$ for every variable $X_i$ occurring in $F$. Choose
    ordinals $\alpha_1,\alpha''$ such that
    $\alpha_1\le\alpha''$ and $\alpha_1\le\alpha$. Suppose that, for some
    $\varepsilon_1>0$,
    \[
      v_J((F(b_i))^{|\gamma})<\omega^{\alpha_1}
      \qquad(-\varepsilon_1<\gamma<0).
    \]
    Assume also that every term obtained from a monomial of $F$ by replacing
    the weights of at least two variable factors, counted with multiplicity,
    by strictly smaller ordinals has weight below $\alpha''$.

    Fix $i'\in I$ and an ordinal $\tau$ with
    $\alpha''\le\tau\oplus w_{i'}$. Then, for every $\gamma<0$ sufficiently
    close to $0$,
    \[
      \bigl(P_{((\partial_{i'}F)(b_i))^{|\gamma}}\bigr)_{\ge\tau}
      \in
      \bigl(\partial_jF:
        j\in\operatorname{vars}(F),\ w_{i'}<w_j\bigr).
    \]
    Here the subscript $\ge\tau$ denotes the sum of the monomials of weighted
    degree at least $\tau$.
  -/)
  (proof := /--
  Apply \ref{lem:differentiated-leibniz-remainder}. In each of the first three
  terms, adjoining one factor of weight $w_{i'}$ to a monomial gives weight
  below $\alpha''$. The hypothesis
  $\alpha''\le\tau\oplus w_{i'}$ therefore makes every such monomial have
  weight below $\tau$. For the derivative of
  $P_{(F(b_i))^{|\gamma}}$, the defining degree bound for the representative
  makes its monomial weights less than $\alpha_1\le\alpha''$; for the two
  remainder terms this is exactly the assumed bound on terms with at least
  two translated factors. Their components of degree at least $\tau$
  consequently vanish.

  It remains to consider
  \[
    \sum_{j\in\operatorname{vars}(F)}
      (\partial_{i'}P_{b_j^{|\gamma}})\,\partial_jF.
  \]
  By \ref{lem:principal-truncations-lower-value}, the first factor has
  weighted degree below $w_j$. It is therefore zero when $w_j\le w_{i'}$.
  The remaining summands are multiples of the displayed generators.
  Each $\partial_jF$ is weighted-homogeneous when $w_j\preccurlyeq\alpha$
  in the algebraic order, and otherwise vanishes by
  \ref{lem:partial-derivative-vanishes}. Hence taking the components of
  degree at least $\tau$ preserves membership in their ideal.
  -/)]
theorem exists_forall_componentsGE_pol_translatedTruncation_aeval_pderiv_mem
    {F : MvPolynomial ι K} (hF : IsWeightedHomogeneous wt F α)
    (hvars : ∀ i ∈ F.vars, wt i < α) {α₁ α'' : NatOrdinal} (hα₁ : α₁ ≤ α'') (hα₁α : α₁ ≤ α)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hG : ∀ γ : ℝ, -ε₁ < γ → γ < 0 →
      ordinalValue (translatedTruncation ((aeval σ.lift F : Series K) : K⟦ℝ⟧) γ) < ω^ α₁)
    (hwin : ∀ d ∈ F.support, ∀ (k : ℕ) (ρ : NatOrdinal), 2 ≤ k → TermDegree wt d k ρ → ρ < α'')
    (v' : ι) {τ : NatOrdinal} (hτ : α'' ≤ τ + wt v') :
    ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 →
      componentsGE wt τ (σ.pol hx α
        (translatedTruncation ((aeval σ.lift (pderiv v' F) : Series K) : K⟦ℝ⟧) γ)) ∈
      Ideal.span (Set.range fun j : {j : ι // j ∈ F.vars ∧ wt v' < wt j} ↦ pderiv j.1 F) := by
  classical
  have hFdeg : ∀ d ∈ F.support, Finsupp.weight wt d ≤ α :=
    fun d hd ↦ (hF (mem_support_iff.mp hd)).le
  obtain ⟨ε₂, hε₂, hD⟩ := σ.exists_forall_pol_translatedTruncation_aeval_pderiv hx hinj F hFdeg
    hvars v'
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun γ hγε hγ0 ↦ ?_⟩
  have hγ₁ : -ε₁ < γ := by linarith [min_le_left ε₁ ε₂]
  have hγ₂ : -ε₂ < γ := by linarith [min_le_right ε₁ ε₂]
  obtain ⟨E, E', hE, hE', heq⟩ := hD γ hγ₂ hγ0
  rw [heq, componentsGE_add, componentsGE_sub, componentsGE_sub]
  -- a monomial `m'` with `v' m'` of degree below `α''` has degree below `τ`
  have hlow : ∀ d' : ι →₀ ℕ, Finsupp.weight wt d' + wt v' < α'' → Finsupp.weight wt d' < τ :=
    fun d' h ↦ lt_of_add_lt_add_right (h.trans_le hτ)
  -- `∂/∂X_{v'} pol(G^{|γ})`
  have h1 : componentsGE wt τ (pderiv v' (σ.pol hx α
      (translatedTruncation ((aeval σ.lift F : Series K) : K⟦ℝ⟧) γ))) = 0 := by
    refine componentsGE_eq_zero_of_forall_lt wt fun d' hd' ↦ ?_
    obtain ⟨d, hd, hw⟩ := exists_add_eq_weight_of_mem_support_pderiv wt hd'
    refine hlow d' ?_
    rw [hw]
    exact (degreeLT_iff.mp (σ.pol_degreeLT_of_lt hx hinj hα₁α (hG γ hγ₁ hγ0)) d hd).trans_le hα₁
  -- the remainder for `F`, differentiated
  have h2 : componentsGE wt τ (pderiv v' E) = 0 := by
    refine componentsGE_eq_zero_of_forall_lt wt fun d' hd' ↦ ?_
    obtain ⟨d, hd, hw⟩ := exists_add_eq_weight_of_mem_support_pderiv wt hd'
    obtain ⟨d₀, hd₀, k, hk, hρ⟩ := hE d hd
    refine hlow d' ?_
    rw [hw]
    exact hwin d₀ hd₀ k _ hk hρ
  -- the remainder for `∂F/∂X_{v'}`
  have h3 : componentsGE wt τ E' = 0 := by
    refine componentsGE_eq_zero_of_forall_lt wt fun d' hd' ↦ ?_
    obtain ⟨d, hd, k, hk, hρ⟩ := hE' d' hd'
    refine hlow d' ?_
    exact hwin _ (add_single_mem_support_of_mem_support_pderiv hd) k _ hk (hρ.untrunc v')
  rw [h1, h2, h3, zero_sub, sub_zero, add_zero]
  refine neg_mem ?_
  -- the sum: only the variables of degree above `wt v'` contribute
  rw [← Finset.sum_filter_add_sum_filter_not F.vars fun j ↦ wt v' < wt j, componentsGE_add]
  have hzero : ∑ j ∈ F.vars.filter (fun j ↦ ¬ wt v' < wt j),
      pderiv v' (σ.pol hx α (translatedTruncation (σ.lift j : K⟦ℝ⟧) γ)) * pderiv j F = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hj' := (Finset.mem_filter.mp hj).2
    rw [not_lt] at hj'
    have hdeg : DegreeLT wt (σ.pol hx α (translatedTruncation (σ.lift j : K⟦ℝ⟧) γ)) (wt j) :=
      σ.pol_degreeLT_of_lt hx hinj (hvars j (Finset.mem_filter.mp hj).1).le
        (hσ.ordinalValue_translatedTruncation_lift_lt j hγ0)
    rw [pderiv_eq_zero_of_degreeLT_le hdeg hj', zero_mul]
  rw [hzero, componentsGE_zero, add_zero]
  -- the generators are homogeneous
  have hgen : ∀ j : {j : ι // j ∈ F.vars ∧ wt v' < wt j},
      ∃ c, IsWeightedHomogeneous wt (pderiv j.1 F) c := by
    intro j
    by_cases h : ∃ β, β + wt j.1 = α
    · obtain ⟨β, hβ⟩ := h
      exact ⟨β, isWeightedHomogeneous_pderiv wt hF j.1 hβ⟩
    · exact ⟨0, by
        rw [pderiv_eq_zero_of_isWeightedHomogeneous wt hF j.1 h]
        exact isWeightedHomogeneous_zero _ _ _⟩
  choose c hc using hgen
  have : Finite {j : ι // j ∈ F.vars ∧ wt v' < wt j} :=
    (F.vars.finite_toSet.subset fun j (hj : j ∈ F.vars ∧ wt v' < wt j) ↦ hj.1).to_subtype
  refine componentsGE_mem_span wt hc ?_ τ
  refine Ideal.sum_mem _ fun j hj ↦ ?_
  have hj' := Finset.mem_filter.mp hj
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨j, hj'.1, hj'.2⟩, rfl⟩)

end Lifts

end Berarducci
