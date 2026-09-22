/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.FinitePartVars

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.PartialDerivativeIndices
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.IdealFromTruncations

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Finset.FilterCard
import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Partial derivatives and algebraic order of low-degree parts

When `(deg B')_{<β} ≼ λ₀` in the algebraic order,

`∂F/∂X_{B'} = ∑_B (∂F/∂X_B) U_B`

over finitely many variables `B`: those whose low-degree part is all of `α_{<β}`, or larger
variables whose proper low-degree part does not precede `λ₀`. Moreover `∂U_B/∂X_{B₀} = 0`.

*Proof*, by induction on the number of variables of `F` of degree above `deg B'`. Put
`λ' := λ₀ ⊖ (deg B')_{<β}` and `τ := (α ⊖ deg B')_{≥β} ⊕ λ'`. For all `γ < 0`
sufficiently close to `0`, the part at or above `τ` of
`pol((∂F/∂X_{B'})(b_𝓑)^{|γ})` lies in the ideal of the
`∂F/∂X_B` over the variables `B` of `F` with `deg B > deg B'`
(`exists_forall_componentsGE_pol_translatedTruncation_aeval_pderiv_mem`). A variable above `B'`
has a low-degree part equal to `α_{<β}`, outside the algebraic bound `λ₀`, or preceding `λ₀`; in
the last case `∂F/∂X_B` already lies in the ideal by induction. Among the retained derivatives,
those whose degree `σ_B ≼ α ⊖ deg B'` satisfy (n) against `τ`, and the others contribute nothing
in `[τ, α ⊖ deg B')`; so the translated truncations of
`(∂F/∂X_{B'})(b_𝓑)` satisfy (p) for the retained generators and `τ`, and ideal membership
of a
class from the condition (p) on its translated truncations
(`IsPrincipal.of_principalComponentMk_mem_span_of_forall_componentsGE_mem`) gives the class of
`(∂F/∂X_{B'})(b_𝓑)` in `P_{α ⊖ deg B'}` as a combination of the generators with
homogeneous
cofactors. Polynomial preimages of the cofactors and injectivity below `α` turn this into the
polynomial identity; the cofactors have degree below `δ = deg B₀`, so `∂U_B/∂X_{B₀} = 0`.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial OrdinalGraded

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

namespace Lifts.LimitOrdinalRelationAtCutoff

variable {σ : Lifts wt x} {α : NatOrdinal} (S : σ.LimitOrdinalRelationAtCutoff α)
  (hx : IsMinimalSystem (principalGrading K) wt x) (hinj : ∀ β < α, InjectiveAt K wt x β)
  (hσ : σ.IsPrincipal)
include S hx hinj hσ

/-- A variable contributes to the derivative at `v'` when its low-degree part is all of
`α_{<β}`, or when it is larger than `v'` and its proper low-degree part does not precede `λ₀`. -/
def ContributesToPartialDerivativeAt (v' v : ι) : Prop :=
  v ∈ S.F.vars ∧
    (S.LowDegreePartEq v ∨ (S.HasProperLowDegreePartNotAlgebraicLE v ∧ wt v' < wt v))

omit hx hinj hσ in
theorem contributesToPartialDerivativeAt_iff (v' v : ι) :
    S.ContributesToPartialDerivativeAt v' v ↔
      v ∈ S.F.vars ∧
        (S.LowDegreePartEq v ∨ (S.HasProperLowDegreePartNotAlgebraicLE v ∧ wt v' < wt v)) :=
  (Iff.rfl)

omit hx hinj hσ in
theorem finite_setOf_contributesToPartialDerivativeAt (v' : ι) :
    Finite {v // S.ContributesToPartialDerivativeAt v' v} :=
  (S.F.vars.finite_toSet.subset fun v
    (hv : S.ContributesToPartialDerivativeAt v' v) ↦ hv.1).to_subtype

/-- **The partial derivative when the low-degree part precedes `λ₀`.** If
`S.LowDegreePartAlgebraicLE v'`, then
`∂F/∂X_{v'} = ∑_v (∂F/∂X_v) U_v` over finitely many contributing variables, with
`∂U_v/∂X_{B₀} = 0`. -/
@[blueprint "prop:partials-when-low-degree-part-is-algebraically-bounded"
  (phase := "Limit ordinals in the degree induction")
  (title := "Partial-derivative syzygy when $(w_{B'})_{<\\beta}\\oplus\\eta=\\lambda_0$ \
    for some $\\eta$")
  (statement := /--
    Let $K$ be a field. Let $(x_i)_{i\in I}$ be a minimal homogeneous
    generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$, and choose principal series $b_i$ of degree
    $w_i$ representing $x_i$. Assume evaluation at $(x_i)$ is injective on
    every homogeneous degree below $\alpha$.

    Let $0\ne F\in K[X_i:i\in I]$ be weighted homogeneous of degree $\alpha$
    with $F(x)=0$. Suppose every variable of $F$ has weight below $\alpha$
    and zero constant Cantor coefficient. Choose $X_{B_0}$ of maximal weight
    among the variables of $F$, and put $D=\deg_{X_{B_0}}F$. Suppose there are
    ordinals $\beta,\Delta,\lambda_0,\alpha_1$ such that
    \[
      \Delta\ne0,\qquad
      \Delta\oplus D w_{B_0}=\alpha,\qquad
      \lambda_0<\alpha_{<\beta},
    \]
    every Cantor term of $\Delta$ is at least $\omega^\beta$, and the last
    Cantor term of $w_{B_0}$ is below $\omega^\beta$. Assume also
    \[
      \alpha_1\le\alpha_{\ge\beta}\oplus\lambda_0,
      \qquad \alpha_1\le\alpha,
    \]
    that for some $\varepsilon_1>0$ every $\gamma\in(-\varepsilon_1,0)$
    satisfies
    \[
      v_J\bigl(F(b)^{\vert\gamma}\bigr)<\omega^{\alpha_1},
    \]
    and that in the convolution expansion of any monomial of $F$, every term
    $\rho$ using at least two translated truncations satisfies
    $\rho<\alpha_{\ge\beta}\oplus\lambda_0$.

    Let $X_{B'}$ occur in $F$, and suppose
    $(w_{B'})_{<\beta}\preccurlyeq\lambda_0$ in the algebraic order. Then
    there are a finite set $E$ of variables and
    polynomials $(U_B)_{B\in E}$ such that every $B\in E$ occurs in $F$ and
    either
    \[
      (w_B)_{<\beta}=\alpha_{<\beta},
    \]
    or
    \[
      0<(w_B)_{<\beta}\ne\alpha_{<\beta},\qquad
      (w_B)_{<\beta}\not\preccurlyeq\lambda_0,
      \qquad w_{B'}<w_B.
    \]
    Moreover $\partial_{B_0}U_B=0$ for every $B\in E$, and
    \[
      \partial_{B'}F=\sum_{B\in E}(\partial_BF)U_B.
    \]
  -/)
  (proof := /--
  Use strong induction on the number of variables of $F$ whose weight exceeds
  $w_{B'}$. The assertion is immediate when $\partial_{B'}F=0$. Otherwise
  write
  \[
    h\oplus w_{B'}=\alpha,
    \qquad
    (w_{B'})_{<\beta}\oplus\lambda'=\lambda_0,
    \qquad
    \tau=h_{\ge\beta}\oplus\lambda'.
  \]
  Weighted homogeneity and injectivity below $\alpha$ give
  $v_J((\partial_{B'}F)(b))=\omega^h$ and the required polynomial
  representatives of its translated truncations. By
  \ref{lem:differentiated-relation}, their components of weight at least
  $\tau$ lie in the ideal generated by $\partial_BF$ with $w_{B'}<w_B$.
  Apply the induction hypothesis to every such $B$ whose part below $\beta$
  precedes $\lambda_0$ in the algebraic order. The remaining generators are exactly
  those listed in the statement.

  The Cantor decompositions give $\tau\oplus1<h$. For each remaining
  generator, \ref{lem:complementary-cantor-tail} identifies the high Cantor
  terms of the complementary degree, and \ref{lem:separation} gives
  $\rho_B\oplus\theta<\tau$ for every $\theta<\sigma_B$, where $\sigma_B$ is
  the weight of $\partial_BF$.
  Thus \ref{prop:ideal-from-truncations}, applied to
  $(\partial_{B'}F)(b)$, puts its degree-$h$ class in the ideal generated by
  the degree classes of the remaining $\partial_BF$.

  Take homogeneous cofactors of the complementary weights in this ideal
  expression and represent them by weighted-homogeneous polynomials $U_B$.
  Evaluating the difference gives zero, and injectivity in degree $h<\alpha$
  gives the displayed polynomial identity. Finally each $U_B$ has weight
  below $w_{B_0}$, so $\partial_{B_0}U_B=0$.
  -/)]
theorem exists_finset_pderiv_eq_sum_of_lowDegreePartAlgebraicLE {v' : ι} (hv' : v' ∈ S.F.vars)
    (hdiff : S.LowDegreePartAlgebraicLE v') :
    ∃ (s : Finset ι) (U : ι → MvPolynomial ι K),
      (∀ v ∈ s, S.ContributesToPartialDerivativeAt v' v) ∧
      (∀ v ∈ s, pderiv S.B₀ (U v) = 0) ∧
      pderiv v' S.F = ∑ v ∈ s, pderiv v S.F * U v := by
  classical
  suffices H : ∀ n : ℕ, ∀ v' ∈ S.F.vars,
      (S.F.vars.filter fun v ↦ wt v' < wt v).card = n →
      S.LowDegreePartAlgebraicLE v' →
      ∃ (s : Finset ι) (U : ι → MvPolynomial ι K),
        (∀ v ∈ s, S.ContributesToPartialDerivativeAt v' v) ∧
        (∀ v ∈ s, pderiv S.B₀ (U v) = 0) ∧
        pderiv v' S.F = ∑ v ∈ s, pderiv v S.F * U v from
    H _ v' hv' rfl hdiff
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v' hv' hn hdiff
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ, Θ = pderiv v' S.F := ⟨_, rfl⟩
  rw [← hΘdef]
  rcases eq_or_ne Θ 0 with hΘ0 | hΘ0
  · exact ⟨∅, fun _ ↦ 0, fun v hv ↦ absurd hv (Finset.notMem_empty v),
      fun v hv ↦ absurd hv (Finset.notMem_empty v), by rw [hΘ0, Finset.sum_empty]⟩
  -- the degree `h = α ⊖ deg v'` and `τ = h_{≥β} ⊕ λ'`
  obtain ⟨h, hh⟩ := exists_add_wt_eq_of_mem_vars S.hom hv'
  have hhα : h < α := by
    rw [← hh]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.mpr (hx.ne_zero v'))
  have hΘhom : IsWeightedHomogeneous wt Θ h := by rw [hΘdef]; exact S.pderiv_hom hh
  obtain ⟨lam', hlam'⟩ := NatOrdinal.algebraicLE_iff.mp
    ((S.lowDegreePartAlgebraicLE_iff v').mp hdiff)
  obtain ⟨τ, hτdef⟩ : ∃ τ : NatOrdinal,
      τ = NatOrdinal.partGE S.β h + lam' := ⟨_, rfl⟩
  -- the variables above `v'`
  have hτ : NatOrdinal.partGE S.β α + S.lam₀ ≤ τ + wt v' := by
    have := S.αGE_add_lam₀_eq hh hlam'
    rw [S.αGE_def, ← hτdef] at this
    exact this.le
  obtain ⟨ε₂, hε₂, h2⟩ :=
    σ.exists_forall_componentsGE_pol_translatedTruncation_aeval_pderiv_mem hx hinj hσ
      S.hom S.vars_lt S.α₁_le S.α₁_le_α S.ε₁_pos S.truncation_lt S.remainder_lt v' hτ
  rw [← hΘdef] at h2
  -- the partials of the variables above `v'` lie in the ideal of the generators
  have habove : ∀ j ∈ S.F.vars, wt v' < wt j →
      pderiv j S.F ∈
        Ideal.span (Set.range fun v : {v // S.ContributesToPartialDerivativeAt v' v} ↦
          pderiv v.1 S.F) := by
    intro j hj hlt
    by_cases htop : S.LowDegreePartEq j
    · exact Ideal.subset_span ⟨⟨j, hj, Or.inl htop⟩, rfl⟩
    by_cases hL : S.HasProperLowDegreePartNotAlgebraicLE j
    · exact Ideal.subset_span ⟨⟨j, hj, Or.inr ⟨hL, hlt⟩⟩, rfl⟩
    -- The low-degree part of `j` precedes `λ₀`: use the induction hypothesis.
    have hdj : S.LowDegreePartAlgebraicLE j := by
      by_contra hnd
      rcases eq_or_ne (S.degLT j) 0 with ht | ht
      · exact hnd ((S.lowDegreePartAlgebraicLE_iff j).mpr (by
          rw [ht]
          exact NatOrdinal.algebraicLE_zero _))
      · exact hL ((S.hasProperLowDegreePartNotAlgebraicLE_iff j).mpr ⟨hj, ht, htop, hnd⟩)
    have hcard : (S.F.vars.filter fun v ↦ wt j < wt v).card < n :=
      (ConwayRefinement.card_filter_above_lt wt S.F.vars hj hlt).trans_eq hn
    obtain ⟨s, U, hs, -, heq⟩ := ih _ hcard j hj rfl hdj
    rw [heq]
    refine Ideal.sum_mem _ fun v hv ↦
      Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨⟨v, ?_⟩, rfl⟩)
    exact ⟨(hs v hv).1, (hs v hv).2.elim Or.inl fun h' ↦ Or.inr ⟨h'.1, hlt.trans h'.2⟩⟩
  have h2' : ∀ γ : ℝ, -ε₂ < γ → γ < 0 →
      componentsGE wt τ (σ.pol hx α
        (translatedTruncation ((aeval σ.lift Θ : Series K) : K⟦ℝ⟧) γ)) ∈
        Ideal.span (Set.range fun v : {v // S.ContributesToPartialDerivativeAt v' v} ↦
          pderiv v.1 S.F) := by
    intro γ hγε hγ0
    refine Ideal.span_le.mpr ?_ (h2 γ hγε hγ0)
    rintro _ ⟨j, rfl⟩
    exact habove j.1 j.2.1 j.2.2
  -- the generator degrees `σ_v = α ⊖ deg v` and cofactor degrees `b_v = deg v ⊖ deg v'`
  have : Finite {v // S.ContributesToPartialDerivativeAt v' v} :=
    S.finite_setOf_contributesToPartialDerivativeAt v'
  have hcd : ∀ v : {v // S.ContributesToPartialDerivativeAt v' v}, ∃ c, c + wt v.1 = α :=
    fun v ↦ exists_add_wt_eq_of_mem_vars S.hom v.2.1
  choose cd hcd using hcd
  have hqG : ∀ v : {v // S.ContributesToPartialDerivativeAt v' v},
      IsWeightedHomogeneous wt (pderiv v.1 S.F) (cd v) :=
    fun v ↦ S.pderiv_hom (hcd v)
  -- generators with `σ_v ≼ h`, equivalently `deg v' ≼ deg v`
  obtain ⟨A, hAdef⟩ : ∃ A : {v // S.ContributesToPartialDerivativeAt v' v} → Prop,
      A = fun v ↦ NatOrdinal.AlgebraicLE (wt v') (wt v.1) := ⟨_, rfl⟩
  have hAiff : ∀ v, A v ↔ NatOrdinal.AlgebraicLE (wt v') (wt v.1) := fun v ↦ by rw [hAdef]
  have : Finite {v : {v // S.ContributesToPartialDerivativeAt v' v} // A v} :=
    Finite.of_injective (fun v ↦ v.1) Subtype.val_injective
  have hbA : ∀ v : {v : {v // S.ContributesToPartialDerivativeAt v' v} // A v},
      ∃ b, b + wt v' = wt v.1.1 := fun v ↦ by
    obtain ⟨c, hc⟩ := NatOrdinal.algebraicLE_iff.mp ((hAiff v.1).mp v.2)
    exact ⟨c, by rw [add_comm]; exact hc⟩
  choose b hb using hbA
  have hbc : ∀ v : {v : {v // S.ContributesToPartialDerivativeAt v' v} // A v},
      b v + cd v.1 = h := by
    intro v
    have h1 : b v + cd v.1 + wt v' = h + wt v' := by
      rw [add_right_comm, hb v, add_comm, hcd v.1, hh]
    exact add_right_cancel h1
  -- for the other generators, `σ_v \not\preccurlyeq h`
  have hnotA : ∀ v : {v // S.ContributesToPartialDerivativeAt v' v}, ¬ A v →
      ¬ NatOrdinal.AlgebraicLE (cd v) h := by
    intro v hA hce
    obtain ⟨b', hb'⟩ := NatOrdinal.algebraicLE_iff.mp hce
    refine hA ((hAiff v).mpr (NatOrdinal.algebraicLE_iff.mpr ⟨b', ?_⟩))
    have h1 : cd v + (b' + wt v') = cd v + wt v.1 := by
      rw [← add_assoc, hb', hh, hcd v]
    rw [add_comm]
    exact add_left_cancel h1
  -- the ordinal value of `(∂F/∂X_{v'})(b_𝓑)` and of its translated truncations
  have hu : ordinalValue (aeval σ.lift Θ) = ω^ h :=
    σ.ordinalValue_aeval_eq_of_injectiveAt (hinj h hhα) hΘhom hΘ0
  have hu' : ordinalValue (aeval σ.lift Θ) < ω^ (h + 1) := by
    rw [hu]; exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one h)
  obtain ⟨ε₃, hε₃, h3⟩ := exists_forall_ordinalValue_translatedTruncation_lt hu'
  -- ideal membership of the class from the condition (p) on the translated truncations
  have hτh : τ + 1 < h := hτdef ▸ S.τ_add_one_lt hx hh hlam'
  have hsep : ∀ v : {v : {v // S.ContributesToPartialDerivativeAt v' v} // A v},
      ∀ θ, θ < cd v.1 → b v + θ < τ := by
    intro v θ hθ
    have hc0 := S.cdeg_ne_zero v.1.2.1 (hcd v.1)
    obtain ⟨ε, hε⟩ := NatOrdinal.exists_leastTerm_eq_wpow hc0
    refine NatOrdinal.add_lt_of_lt_of_partGE_le hc0 hε (hbc v) ?_ hθ
    rw [hτdef]
    rcases v.1.2.2 with htop | ⟨hL, -⟩
    · exact S.partGE_le_τ_of_lowDegreePartEq v.1.2.1 (hcd v.1) htop hε h
    · have hne := S.partLT_cdeg_ne_zero (hcd v.1)
        ((S.hasProperLowDegreePartNotAlgebraicLE_iff _).mp hL).2.2.1
      rw [NatOrdinal.leastTerm_eq_leastTerm_partLT hne] at hε
      exact S.partGE_le_τ_of_hasProperLowDegreePartNotAlgebraicLE hx (hcd v.1) hh hlam' hL hε
  have htrunc : ∀ γ : ℝ, -(min ε₂ ε₃) < γ → γ < 0 →
      componentsGE wt τ (σ.pol hx α
        (translatedTruncation ((aeval σ.lift Θ : Series K) : K⟦ℝ⟧) γ)) ∈
        Ideal.span (Set.range fun v :
          {v : {v // S.ContributesToPartialDerivativeAt v' v} // A v} ↦ pderiv v.1.1 S.F) := by
    intro γ hγε hγ0
    have hγ₂ : -ε₂ < γ := by linarith [min_le_left ε₂ ε₃]
    have hγ₃ : -ε₃ < γ := by linarith [min_le_right ε₂ ε₃]
    refine componentsGE_mem_span_subtype wt hqG (h2' γ hγ₂ hγ0)
      (σ.pol_degreeLT_of_lt hx hinj hhα.le (h3 γ hγ₃ hγ0)) A
      fun v hA e hτe heh ⟨β', hβ'⟩ ↦ ?_
    have hce : NatOrdinal.AlgebraicLE (cd v) e :=
      NatOrdinal.algebraicLE_iff.mpr ⟨β', by rw [add_comm]; exact hβ'⟩
    rw [hτdef] at hτe
    rcases v.2.2 with htop | ⟨hL, -⟩
    · exact S.not_algebraicLE_of_lowDegreePartEq_of_not
        (hcd v) hlam' htop (hnotA v hA) hτe heh hce
    · exact S.not_algebraicLE_of_hasProperLowDegreePartNotAlgebraicLE_of_not
        hx (hcd v) hh hlam' hL (hnotA v hA) hτe heh hce
  have hmem := IsPrincipal.of_principalComponentMk_mem_span_of_forall_componentsGE_mem σ hx hinj
    hσ (ι' := {v : {v // S.ContributesToPartialDerivativeAt v' v} // A v})
    (q := fun v ↦ pderiv v.1.1 S.F)
    (c := fun v ↦ cd v.1) (τ := τ) (h := h) (b := b)
    (u := aeval σ.lift Θ) (η := -(min ε₂ ε₃))
    (fun v ↦ hqG v.1) (fun v ↦ S.cdeg_constantCoeff hx (hcd v.1))
    (fun v ↦ S.cdeg_ne_zero v.1.2.1 (hcd v.1)) hbc hsep hτh hhα hu hu'
    (neg_neg_of_pos (lt_min hε₂ hε₃)) htrunc
  -- back to polynomials
  cases nonempty_fintype {v : {v // S.ContributesToPartialDerivativeAt v' v} // A v}
  have hq' : ∀ v : {v : {v // S.ContributesToPartialDerivativeAt v' v} // A v},
      aeval x (pderiv v.1.1 S.F) ∈ principalGrading K (cd v.1) :=
    fun v ↦ aeval_mem_of_forall_mem hx.mem (hqG v.1)
  obtain ⟨u, hu_mem, -, hsum⟩ := exists_eq_sum_mul_of_mem_span (𝒜 := principalGrading K) hq'
    (of_mem_principalGrading _ _) hmem
  have hU : ∀ v : {v : {v // S.ContributesToPartialDerivativeAt v' v} // A v},
      ∃ U : MvPolynomial ι K,
      IsWeightedHomogeneous wt U (b v) ∧ aeval x U = u v :=
    fun v ↦ hx.exists_aeval_eq (principalGrading_gradeZeroScalars K) (b v) (u v)
      (hu_mem v (b v) (hbc v))
  choose U hUhom hUu using hU
  obtain ⟨Θ', hΘ'def⟩ : ∃ Θ', Θ' = Θ - ∑ v, pderiv v.1.1 S.F * U v := ⟨_, rfl⟩
  have hS : IsWeightedHomogeneous wt (∑ v, pderiv v.1.1 S.F * U v) h :=
    IsWeightedHomogeneous.sum _ _ _ fun v _ ↦ by
      have := IsWeightedHomogeneous.mul (hqG v.1) (hUhom v)
      rwa [add_comm, hbc v] at this
  have hΘ'hom : IsWeightedHomogeneous wt Θ' h := by
    rw [hΘ'def, sub_eq_add_neg]
    refine IsWeightedHomogeneous.add hΘhom ?_
    intro d hd
    rw [coeff_neg, neg_ne_zero] at hd
    exact hS hd
  have hΘ'0 : aeval x Θ' = 0 := by
    rw [hΘ'def, map_sub, map_sum, ← (σ.aeval_represents hΘhom).of_principalComponentMk, hsum]
    simp only [map_mul, hUu]
    exact sub_self _
  have hΘ' : Θ' = 0 := (injectiveAt_iff h).mp (hinj h hhα) Θ' hΘ'hom hΘ'0
  have hΘeq : Θ = ∑ v, pderiv v.1.1 S.F * U v := by
    rw [← sub_eq_zero, ← hΘ'def]; exact hΘ'
  -- the cofactors have degree below `δ = deg B₀`, so `∂/∂X_{B₀}` annihilates them
  have hUB₀ : ∀ v : {v : {v // S.ContributesToPartialDerivativeAt v' v} // A v},
      pderiv S.B₀ (U v) = 0 := by
    intro v
    have hbg : b v < wt S.B₀ := by
      have h1 : b v < wt v.1.1 := by
        rw [← hb v]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.mpr (hx.ne_zero v'))
      exact h1.trans_le (S.max _ v.1.2.1)
    exact pderiv_eq_zero_of_degreeLT_le ((hUhom v).degreeLT hbg) le_rfl
  -- Extend the cofactor family by zero, then reindex along the inclusion of contributing variables.
  let index : {v : {v // S.ContributesToPartialDerivativeAt v' v} // A v} → ι :=
    fun v ↦ v.1.1
  have hinjv : Function.Injective index := fun v w hvw ↦ Subtype.ext (Subtype.ext hvw)
  refine ⟨Finset.univ.image index, Function.extend index U (fun _ ↦ 0), ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hi
    exact v.1.2
  · intro i hi
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hi
    rw [hinjv.extend_apply]
    exact hUB₀ v
  · rw [hΘeq, Finset.sum_image fun v _ w _ h ↦ hinjv h]
    exact Finset.sum_congr rfl fun v _ ↦ by rw [hinjv.extend_apply]

end Lifts.LimitOrdinalRelationAtCutoff

end Berarducci
