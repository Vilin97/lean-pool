/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.LimitOrdinalRelationAtCutoff
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.OrdinalExpansion
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.RemainderBound

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Injectivity when the degree is a limit ordinal

Evaluation at a minimal system is injective when the degree is a nonzero limit ordinal, provided
it is injective in every smaller degree.

Suppose not, and take a relation of that degree. Choose a variable of maximal degree. If the
leading coefficient is scalar, or its last Cantor term is no later than the last term of the
maximal weight, the leading-coefficient hypothesis gives a contradiction. Otherwise, translated
truncations of the evaluated relation and the nonlinear terms in the convolution formula admit
uniform smaller-degree bounds. Linearity of the maximal variable and the partial-derivative
identities then give the contradiction.
-/

universe u v w

open scoped NatOrdinal Topology

open Filter MvPolynomial HahnSeries HahnSeries.Nonpositive

public noncomputable section

namespace HahnSeries.Germ

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

variable {ι : Type w} {wt : ι → NatOrdinal.{u}}
  {xg : ι → (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded}
variable (σ : LiftFamily wt xg)

/-- **The truncations of a relation drop below a degree short of the limit.** The evaluated
relation has degree strictly below the limit, truncation does not raise the degree, and a limit
leaves room for a strict bound in between. -/
theorem exists_lt_forall_degree_translatedTruncLE_lt {α : NatOrdinal.{u}} (hα0 : α ≠ 0)
    {F : MvPolynomial ι K} (hF : IsWeightedHomogeneous wt F α)
    (h0 : aeval xg F = 0) :
    ∃ α₁ : NatOrdinal.{u}, α₁ < α ∧
      ∀ᶠ γ in 𝓝[<] (0 : G),
        ν (translatedTruncLE γ (aeval σ.lift F)) < (α₁ : WithBot NatOrdinal) := by
  have hlt := σ.degree_aeval_lt_of_aeval_eq_zero hF h0
  obtain ⟨α₁, hle, hα₁⟩ : ∃ α₁ : NatOrdinal.{u},
      ν (aeval σ.lift F) ≤ (α₁ : WithBot NatOrdinal.{u}) ∧ α₁ < α := by
    cases hb : ν (aeval σ.lift F) with
    | bot => exact ⟨0, bot_le, pos_iff_ne_zero.mpr hα0⟩
    | coe g =>
      refine ⟨g, le_rfl, ?_⟩
      rw [hb] at hlt
      exact WithBot.coe_lt_coe.mp hlt
  exact ⟨α₁, hα₁, eventually_degree_translatedTruncLE_lt _ α₁ hle⟩

variable (hx : OrdinalGraded.IsMinimalSystem
  (DirectSum.rangeLof K (cantorBendixsonDegreeValuation (G := G) (R := K)).Component) wt xg)
variable {α : NatOrdinal.{u}}
include hx

/-- Evaluation is injective when the degree is a nonzero limit ordinal.

Injectivity below the degree enters through three mathematical obligations: exclusion by the
leading coefficient, linearity of a maximal variable, and the partial-derivative identities. -/
@[blueprint "lem:cantor-bendixson-limit-ordinal-evaluation"
  (phase := "Algebraic independence in graded rings")
  (title := "Injectivity of evaluation when the degree is a limit ordinal")
  (statement := /--
    Let $K$ be a field of characteristic zero and $G$ a nontrivial complete
    ordered abelian group equipped with a compatible additive uniformity whose
    topology is the order topology. Let $x_i$ be a minimal
    homogeneous generating system for the associated graded ring of the
    degree filtration, with weights $w_i$, and choose series $b_i$
    representing $x_i$ in degree $w_i$. Let $\alpha\ne0$ have zero constant
    Cantor coefficient.

    Assume first that the following leading-coefficient case is impossible.
    If $0\ne F\in K[X_i:i\in I]$ is weighted homogeneous of degree $\alpha$,
    $F(x)=0$, $X_{B_0}$ has maximal weight among the variables of $F$, and
    \[
      \Delta+D w_{B_0}=\alpha,
      \qquad D=\deg_{B_0}F,
    \]
    where $w_{B_0}<\alpha$, then $\Delta=0$ or the last Cantor term of
    $\Delta$ being at most the last Cantor term of $w_{B_0}$ gives a
    contradiction.

    In the complementary case, suppose the following two conclusions hold
    whenever ordinals $\beta,\lambda_0,\alpha_1$ and data
    $F,B_0,\Delta,D$ satisfy all of these conditions:
    $F\ne0$ is weighted homogeneous of degree $\alpha$ and $F(x)=0$; every
    variable $X_i$ of $F$ has $w_i<\alpha$ and zero constant Cantor
    coefficient; $X_{B_0}$ has maximal weight; $\Delta+D w_{B_0}=\alpha$;
    $\Delta\ne0$ and every Cantor term of $\Delta$ is at least
    $\omega^\beta$; the last Cantor term of $w_{B_0}$ is below
    $\omega^\beta$; $\lambda_0<\alpha_{<\beta}$;
    \[
      \alpha_1\le\alpha_{\ge\beta}\oplus\lambda_0,
      \qquad \alpha_1\le\alpha;
    \]
    near $0$, every translated truncation of $F(b)$ has degree below
    $\alpha_1$; and every convolution term $\rho$ using at least two
    translated truncations satisfies
    $\rho<\alpha_{\ge\beta}\oplus\lambda_0$.

    The two required conclusions are:

    1. $D=1$.
    2. If $X_{B'}$ occurs in $F$ and
       $(w_{B'})_{<\beta}\oplus\eta=\lambda_0$ for some $\eta$, then there
       are a finite set $S$ and polynomials $U_B$ such that
       \[
         \partial_{B'}F=\sum_{B\in S}(\partial_BF)U_B,
         \qquad \partial_{B_0}U_B=0\quad(B\in S),
       \]
       and every $B\in S$ occurs in $F$ and satisfies either
       $(w_B)_{<\beta}=\alpha_{<\beta}$, or
       \[
         0\ne(w_B)_{<\beta}\ne\alpha_{<\beta},\qquad
         \nexists\eta,\ (w_B)_{<\beta}\oplus\eta=\lambda_0,
         \qquad w_{B'}<w_B.
       \]

    Then evaluation at $x_i$ is injective on the weighted-homogeneous
    polynomials of degree $\alpha$.
  -/)
  (proof := /--
  By \ref{thm:cantor-bendixson-value-multiplicative}, the
  Cantor--Bendixson degree defines the associated graded ring in which
  injectivity is tested.

  Assume a nonzero homogeneous relation $F$ of degree $\alpha$ and choose a
  variable $X_{B_0}$ of maximal weight.  Write $F$ as a polynomial in
  $X_{B_0}$. By
  \ref{lem:variables-of-homogeneous-relation-have-smaller-degree}, every
  variable of $F$ has weight below $\alpha$. If the degree $\Delta$ of the
  leading coefficient is zero, or its last Cantor term is no later than that
  of $w_{B_0}$, the first hypothesis is contradictory.

  Otherwise write the last Cantor term of $\Delta$ as $\omega^\beta$.
  The evaluated relation has degree below $\alpha$, so its translated
  truncations have degrees bounded by some $\alpha_1<\alpha$. The part
  $\alpha_{<\beta}$ is nonzero and has zero constant Cantor coefficient.
  By \ref{lem:two-truncations-below}, there is a uniform bound. Enlarging it
  to include the part of $\alpha_1$ below $\omega^\beta$ supplies
  $\lambda_0<\alpha_{<\beta}$ and the required bound on every nonlinear
  convolution term.

  The two remaining hypotheses now make $X_{B_0}$ occur linearly and supply
  the partial-derivative identities.
  \ref{lem:relation-at-limit-ordinal-partial-contradiction} excludes this case as well.
  Hence no nonzero relation of degree $\alpha$ exists.
  -/)]
theorem injectiveAt_of_limit
    (hleading : ∀ {F : MvPolynomial ι K}, IsWeightedHomogeneous wt F α → aeval xg F = 0 →
      ∀ {B₀ : ι}, B₀ ∈ F.vars → (∀ i ∈ F.vars, wt i ≤ wt B₀) → wt B₀ < α →
      ∀ {degHD : NatOrdinal.{u}}, degHD + degreeOf B₀ F • wt B₀ = α →
      (degHD = 0 ∨ NatOrdinal.leastTerm degHD ≤ NatOrdinal.leastTerm (wt B₀)) → False)
    (hlin : ∀ S : LimitOrdinalRelationAtCutoff σ α, degreeOf S.B₀ S.F = 1)
    (hpartials : ∀ S : LimitOrdinalRelationAtCutoff σ α, ∀ v', v' ∈ S.F.vars →
      S.LowDegreePartAlgebraicLE v' →
      ∃ (s : Finset ι) (U : ι → MvPolynomial ι K), (∀ v ∈ s,
        S.ContributesToPartialDerivativeAt v' v) ∧
        (∀ v ∈ s, pderiv S.B₀ (U v) = 0) ∧ pderiv v' S.F = ∑ v ∈ s, pderiv v S.F * U v)
    (hα0 : α ≠ 0) (hα : α.constantCoeff = 0) :
    OrdinalGraded.InjectiveAt K wt xg α := by
  classical
  rw [OrdinalGraded.injectiveAt_iff]
  intro F hF h0
  by_contra hF0
  -- a variable `B₀` of `F` of maximal degree
  obtain ⟨d₀, hd₀⟩ := exists_coeff_ne_zero hF0
  have hd₀w : Finsupp.weight wt d₀ = α := hF hd₀
  have hd₀ne : d₀ ≠ 0 := by rintro rfl; rw [map_zero] at hd₀w; exact hα0 hd₀w.symm
  obtain ⟨i₀, hi₀⟩ := Finsupp.support_nonempty_iff.mpr hd₀ne
  have hvars : F.vars.Nonempty :=
    ⟨i₀, (mem_vars_iff_mem_support i₀).mpr ⟨d₀, mem_support_iff.mpr hd₀, hi₀⟩⟩
  obtain ⟨B₀, hB₀, hmax⟩ := Finset.exists_max_image F.vars wt hvars
  have hvarslt : ∀ i ∈ F.vars, wt i < α := fun i hi ↦
    hx.wt_lt_of_mem_vars_of_aeval_eq_zero hα0 hF h0 hi
  have hg : wt B₀ < α := hvarslt B₀ hB₀
  have hlimit : ∀ i ∈ F.vars, (wt i).constantCoeff = 0 := fun i hi ↦
    constantCoeff_wt_eq_zero_of_mem_vars hF hα hi
  -- the degree `α ⊖ (δ ⊙ D)` of `H_D`, the coefficient of `X_{B₀}^D` in `F`
  have hFD : xCoeff B₀ (degreeOf B₀ F) F ≠ 0 := xCoeff_degreeOf_ne_zero B₀ hF0
  obtain ⟨degHD, hdegHD⟩ := exists_add_nsmul_eq_of_xCoeff_ne_zero B₀ wt hF hFD
  -- `H_D` is constant, or its least term precedes the least term of `δ`.
  by_cases hleadingTerm :
      degHD = 0 ∨ NatOrdinal.leastTerm degHD ≤ NatOrdinal.leastTerm (wt B₀)
  · exact hleading hF h0 hB₀ hmax hg hdegHD hleadingTerm
  push Not at hleadingTerm
  obtain ⟨hdegHD0, hlt⟩ := hleadingTerm
  obtain ⟨β, hβ⟩ := NatOrdinal.exists_leastTerm_eq_wpow hdegHD0
  have hbad : NatOrdinal.leastTerm (wt B₀) < ω^ β := hβ ▸ hlt
  have hdegHDterms : ∀ t ∈ degHD.val.additivePrincipalTerms, (ω^ β).val ≤ t :=
    fun _ ht ↦ NatOrdinal.wpow_le_of_mem_additivePrincipalTerms_of_leastTerm_eq hdegHD0 hβ ht
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [NatOrdinal.wpow_zero] at hbad
    exact absurd (NatOrdinal.one_le_leastTerm (hx.ne_zero B₀)) (not_le.mpr hbad)
  -- the translated truncations of `F(b_𝓑)`
  obtain ⟨α₁, hα₁α, hcuts⟩ :=
    exists_lt_forall_degree_translatedTruncLE_lt σ hα0 hF h0
  -- the part `α_{<β}` of `α` below `β` is a nonzero limit
  have hμcc : (NatOrdinal.partLT β α).constantCoeff = 0 := by
    rw [NatOrdinal.constantCoeff_partLT hβ0, hα]
  have hμ : NatOrdinal.partLT β α ≠ 0 := by
    obtain ⟨e, he⟩ := NatOrdinal.exists_leastTerm_eq_wpow (hx.ne_zero B₀)
    have heβ : e < β := by rwa [he, NatOrdinal.wpow_lt_wpow] at hbad
    have h1 : NatOrdinal.partLT β (wt B₀) ≠ 0 :=
      NatOrdinal.partLT_ne_zero_of_leastTerm_lt (hx.ne_zero B₀) he heβ
    have h2 : NatOrdinal.partLT β α =
        degreeOf B₀ F • NatOrdinal.partLT β (wt B₀) := by
      rw [← hdegHD, NatOrdinal.partLT_add, NatOrdinal.partLT_eq_zero_of_forall_le hdegHDterms,
        zero_add, NatOrdinal.partLT_nsmul]
    rw [h2]
    exact NatOrdinal.nsmul_ne_zero_of_ne_zero h1
      (Nat.one_le_iff_ne_zero.mpr (mem_vars_iff_degreeOf_ne_zero.mp hB₀))
  -- the bound `λ_E` on the terms of the remainder, and `λ₀`
  have htail : ∀ i ∈ F.vars, NatOrdinal.partLT β (wt i) ≠ 0 →
      ∃ e, e ≠ 0 ∧ NatOrdinal.leastTerm (NatOrdinal.partLT β (wt i)) = ω^ e := by
    intro i hi hne
    refine NatOrdinal.exists_leastTerm_eq_wpow_ne_zero hne ?_
    rw [NatOrdinal.constantCoeff_partLT hβ0]
    exact hlimit i hi
  obtain ⟨lamE, hlamE, hwinE⟩ := exists_forall_partLT_le_of_termDegree F
    (fun d hd ↦ hF (mem_support_iff.mp hd)) hμ htail
  set l₁ : NatOrdinal := if NatOrdinal.partGE β α₁ = NatOrdinal.partGE β α then
    NatOrdinal.partLT β α₁ else 0 with hl₁def
  set lam₀ : NatOrdinal := max (lamE + 1) l₁ with hlam₀def
  have hlamE1 : lamE + 1 < NatOrdinal.partLT β α := by
    refine lt_of_le_of_ne (Order.add_one_le_of_lt hlamE) fun heq ↦ ?_
    have := congrArg NatOrdinal.constantCoeff heq
    rw [hμcc, show lamE + 1 = lamE + ((1 : ℕ) : NatOrdinal) by rw [Nat.cast_one],
      NatOrdinal.constantCoeff_add_natCast] at this
    omega
  have hl₁ : l₁ < NatOrdinal.partLT β α := by
    rw [hl₁def]
    split_ifs with h
    · exact NatOrdinal.partLT_lt_of_lt_of_partGE_eq hα₁α h
    · exact pos_iff_ne_zero.mpr hμ
  have hlam₀ : lam₀ < NatOrdinal.partLT β α := max_lt hlamE1 hl₁
  have hα₁le : α₁ ≤ NatOrdinal.partGE β α + lam₀ := by
    by_cases h : NatOrdinal.partGE β α₁ = NatOrdinal.partGE β α
    · have hl : l₁ = NatOrdinal.partLT β α₁ := by rw [hl₁def, ite_eq_left h]
      calc α₁ = NatOrdinal.partGE β α₁ + NatOrdinal.partLT β α₁ :=
            (NatOrdinal.partGE_add_partLT β α₁).symm
        _ = NatOrdinal.partGE β α + l₁ := by rw [h, hl]
        _ ≤ NatOrdinal.partGE β α + lam₀ := add_le_add_right (le_max_right _ _) _
    · have h1 : NatOrdinal.partGE β α₁ < NatOrdinal.partGE β α :=
        lt_of_le_of_ne (NatOrdinal.partGE_mono hα₁α.le) h
      have h2 : α₁ < NatOrdinal.partGE β α := by
        refine NatOrdinal.lt_of_partGE_lt (β := β) ?_
        rwa [NatOrdinal.partGE_partGE]
      exact h2.le.trans (le_add_of_nonneg_right zero_le)
  have hwindow : ∀ d ∈ F.support, ∀ (k : ℕ) (ρ : NatOrdinal), 2 ≤ k → TermDegree wt d k ρ →
      ρ < NatOrdinal.partGE β α + lam₀ := by
    intro d hd k ρ hk hρ
    have hρα : ρ < α := by
      have := hρ.lt_weight (by omega)
      rwa [hF (mem_support_iff.mp hd)] at this
    by_cases hhigh : NatOrdinal.partGE β ρ = NatOrdinal.partGE β α
    · have hlow := hwinE d hd k ρ hk hρ hhigh
      calc ρ = NatOrdinal.partGE β ρ + NatOrdinal.partLT β ρ :=
            (NatOrdinal.partGE_add_partLT β ρ).symm
        _ ≤ NatOrdinal.partGE β α + lamE := by rw [hhigh]; exact add_le_add_right hlow _
        _ < NatOrdinal.partGE β α + (lamE + 1) := add_lt_add_right (lt_add_one lamE) _
        _ ≤ NatOrdinal.partGE β α + lam₀ := add_le_add_right (le_max_left _ _) _
    · have h1 : NatOrdinal.partGE β ρ < NatOrdinal.partGE β α :=
        lt_of_le_of_ne (NatOrdinal.partGE_mono hρα.le) hhigh
      have h2 : ρ < NatOrdinal.partGE β α := by
        refine NatOrdinal.lt_of_partGE_lt (β := β) ?_
        rwa [NatOrdinal.partGE_partGE]
      exact h2.trans_le (le_add_of_nonneg_right zero_le)
  -- Package the remaining ordinal data and the cutoff `β`.
  let S : LimitOrdinalRelationAtCutoff σ α :=
    { F := F, hom := hF, eval_zero := h0, ne_zero := hF0, vars_lt := hvarslt, vars_limit := hlimit,
      B₀ := B₀, mem := hB₀, max := hmax, β := β, degHD := degHD, hdegHD := hdegHD,
      degHD_terms := hdegHDterms,
      degHD_ne_zero := hdegHD0, term_lt := hbad, lam₀ := lam₀, lam₀_lt := hlam₀,
      α₁ := α₁,
      α₁_le := hα₁le,
      α₁_le_α := hα₁α.le, truncation_lt := hcuts,
      remainder_lt := hwindow }
  exact S.false_of_lowDegreePartAlgebraicLE_decomposition hx (hlin S) (hpartials S)

end HahnSeries.Germ

end
