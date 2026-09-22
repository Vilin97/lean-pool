/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.AlgebraicIndependence
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.CantorBendixsonRepresentatives
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.Partials

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# The real partial-derivative argument

The polynomiality induction for the Cantor–Bendixson degree is generic. For real exponents, a
relation whose degree is a limit ordinal in the generic Hahn ring gives the corresponding relation
in `P̂` after replacing an eventual left-neighborhood statement by an interval `(-ε, 0)`. The
required partial-derivative decomposition then follows from real translated truncations.
-/

universe v w

open scoped HahnSeries NatOrdinal Topology

open Filter Berarducci HahnSeries MvPolynomial

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K]
variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}
variable {σ : Lifts wt x} {α : NatOrdinal}

namespace Lifts

namespace RealPartialDecomposition

variable (S : HahnSeries.Germ.LimitOrdinalRelationAtCutoff σ.cantorBendixson α)

/-- A generic relation of limit-ordinal degree reinterpreted in the real principal subring. -/
@[expose] def principal : σ.LimitOrdinalRelationAtCutoff α := by
  let hex := eventually_nhdsLT_iff_exists.mp S.truncation_lt
  let l := Classical.choose hex
  have hl := (Classical.choose_spec hex).1
  have htrunc := (Classical.choose_spec hex).2
  refine
    { F := S.F
      hom := S.hom
      eval_zero := ?_
      ne_zero := S.ne_zero
      vars_lt := S.vars_lt
      vars_limit := S.vars_limit
      B₀ := S.B₀
      mem := S.mem
      max := S.max
      β := S.β
      degHD := S.degHD
      hdegHD := S.hdegHD
      degHD_terms := S.degHD_terms
      degHD_ne_zero := S.degHD_ne_zero
      term_lt := S.term_lt
      lam₀ := S.lam₀
      lam₀_lt := S.lam₀_lt
      α₁ := S.α₁
      α₁_le := S.α₁_le
      α₁_le_α := S.α₁_le_α
      ε₁ := -l
      ε₁_pos := neg_pos.mpr hl
      truncation_lt := ?_
      remainder_lt := S.remainder_lt }
  · apply principalSubringCantorBendixsonAlgEquiv.injective
    rw [map_zero, principalSubringCantorBendixsonAlgEquiv_aeval, S.eval_zero]
  · intro γ hγl hγ0
    apply (ordinalValueDegree_lt_coe_iff _ _).mp
    rw [show -l = -l by rfl] at hγl
    have hcb := htrunc γ (by linarith) hγ0
    rw [show σ.cantorBendixson.lift = σ.lift by
      funext i
      exact cantorBendixson_lift σ i] at hcb
    rw [ordinalValueDegree_eq_cantorBendixsonDegree]
    simpa only [translatedTruncLE_eq_translatedTruncation] using hcb

@[simp]
theorem principal_F : (principal S).F = S.F := rfl

@[simp]
theorem principal_B₀ : (principal S).B₀ = S.B₀ := rfl

@[simp]
theorem principal_lowDegreePartEq (i : ι) :
    (principal S).LowDegreePartEq i ↔ S.LowDegreePartEq i := by
  rw [Berarducci.Lifts.LimitOrdinalRelationAtCutoff.lowDegreePartEq_iff,
    HahnSeries.Germ.LimitOrdinalRelationAtCutoff.lowDegreePartEq_iff,
    Berarducci.Lifts.LimitOrdinalRelationAtCutoff.degLT_def,
    Berarducci.Lifts.LimitOrdinalRelationAtCutoff.αLT_def,
    HahnSeries.Germ.LimitOrdinalRelationAtCutoff.degLT_def,
    HahnSeries.Germ.LimitOrdinalRelationAtCutoff.αLT_def]
  rfl

@[simp]
theorem principal_lowDegreePartAlgebraicLE (i : ι) :
    (principal S).LowDegreePartAlgebraicLE i ↔ S.LowDegreePartAlgebraicLE i := by
  rw [Berarducci.Lifts.LimitOrdinalRelationAtCutoff.lowDegreePartAlgebraicLE_iff,
    HahnSeries.Germ.LimitOrdinalRelationAtCutoff.lowDegreePartAlgebraicLE_iff,
    Berarducci.Lifts.LimitOrdinalRelationAtCutoff.degLT_def,
    HahnSeries.Germ.LimitOrdinalRelationAtCutoff.degLT_def]
  rfl

@[simp]
theorem principal_hasProperLowDegreePartNotAlgebraicLE (i : ι) :
    (principal S).HasProperLowDegreePartNotAlgebraicLE i ↔
      S.HasProperLowDegreePartNotAlgebraicLE i := by
  rw [Berarducci.Lifts.LimitOrdinalRelationAtCutoff.hasProperLowDegreePartNotAlgebraicLE_iff,
    HahnSeries.Germ.LimitOrdinalRelationAtCutoff.hasProperLowDegreePartNotAlgebraicLE_iff]
  simp only [principal_F, principal_lowDegreePartEq, principal_lowDegreePartAlgebraicLE,
    Berarducci.Lifts.LimitOrdinalRelationAtCutoff.degLT_def,
    HahnSeries.Germ.LimitOrdinalRelationAtCutoff.degLT_def]
  rfl

@[simp]
theorem principal_contributesToPartialDerivativeAt (v' v : ι) :
    (principal S).ContributesToPartialDerivativeAt v' v ↔
      S.ContributesToPartialDerivativeAt v' v := by
  rw [Berarducci.Lifts.LimitOrdinalRelationAtCutoff.contributesToPartialDerivativeAt_iff,
    HahnSeries.Germ.LimitOrdinalRelationAtCutoff.contributesToPartialDerivativeAt_iff]
  simp only [principal_F, principal_lowDegreePartEq, principal_hasProperLowDegreePartNotAlgebraicLE]

/-- The partial-derivative decomposition at a variable whose part of the degree below `β`
precedes `λ₀` in the algebraic order. -/
@[blueprint "lem:real-translated-truncation-partials"
  (phase := "Principal RV-elements")
  (title := "Transport of the Jacobian syzygy to the Cantor--Bendixson grading")
  (statement := /--
    Let $K$ be a field of characteristic zero. Let $(x_i)_{i\in I}$ be a
    minimal homogeneous generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$, and choose principal series $b_i$ of degree
    $w_i$ representing $x_i$. Under the canonical isomorphism
    \[
      \widehat{\mathrm P}\simeq_K
      \operatorname{gr}_{\delta_{\mathrm{CB}}}K((\mathbb R^{\le0})),
    \]
    write $\bar x_i$ for the image of $x_i$, and assume evaluation at
    $(\bar x_i)$ is injective on every homogeneous degree below $\alpha$.

    Let $0\ne F\in K[X_i:i\in I]$ be weighted homogeneous of degree $\alpha$
    with $F(\bar x)=0$. Suppose every variable of $F$ has weight below
    $\alpha$ and zero constant Cantor coefficient. Choose $X_{B_0}$ of
    maximal weight among the variables of $F$, and put
    $D=\deg_{X_{B_0}}F$. Suppose there are ordinals
    $\beta,\Delta,\lambda_0,\alpha_1$ such that
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
    that for all $\gamma<0$ sufficiently close to $0$,
    \[
      \delta_{\mathrm{CB}}\bigl(F(b)^{\vert\gamma}\bigr)<\alpha_1,
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
  \ref{lem:principal-subring-cantor-bendixson} identifies the
  Cantor--Bendixson degree with $\deg_J$. It therefore carries
  $F(\bar x)=0$, injectivity below $\alpha$, and the eventual degree bound to
  $\widehat{\mathrm P}$, while leaving $F$, the weights, the cutoff data, and the
  chosen series unchanged.

  Apply \ref{prop:partials-when-low-degree-part-is-algebraically-bounded} there. The isomorphism
  preserves the three conditions on the part of a weight below $\beta$, so
  the same finite set $E$ and the same polynomials $U_B$ give the asserted
  identity and the equations $\partial_{B_0}U_B=0$.
  -/)]
theorem lowDegreePartAlgebraicLE_partials
    (hx : OrdinalGraded.IsMinimalSystem (principalGrading K) wt x)
    (hinj : ∀ β < α, OrdinalGraded.InjectiveAt K wt
      (fun i ↦ principalSubringCantorBendixsonAlgEquiv (x i)) β)
    (hσ : σ.IsPrincipal) {v' : ι} (hv' : v' ∈ S.F.vars)
    (hlowDegree : S.LowDegreePartAlgebraicLE v') :
    ∃ (s : Finset ι) (U : ι → MvPolynomial ι K),
      (∀ v ∈ s, S.ContributesToPartialDerivativeAt v' v) ∧
      (∀ v ∈ s, pderiv S.B₀ (U v) = 0) ∧
        pderiv v' S.F = ∑ v ∈ s, pderiv v S.F * U v := by
  let Sp := principal S
  have hinj' : ∀ β < α, OrdinalGraded.InjectiveAt K wt x β := fun β hβα ↦
    (principalSubringCantorBendixson_injectiveAt_iff β).mpr (hinj β hβα)
  obtain ⟨s, U, hs, hU, heq⟩ :=
    Sp.exists_finset_pderiv_eq_sum_of_lowDegreePartAlgebraicLE hx hinj' hσ hv'
      ((principal_lowDegreePartAlgebraicLE S v').mpr hlowDegree)
  exact ⟨s, U, fun v hv ↦ (principal_contributesToPartialDerivativeAt S v' v).mp (hs v hv), hU, heq⟩

end RealPartialDecomposition

end Lifts

end Berarducci
