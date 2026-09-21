/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.LeadingCoefficient
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.LinearMaximal
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Obligations
public import
  LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.PartialDerivativesAtLimitOrdinal
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Scalar
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.ArchimedeanBallBase
public import Mathlib.RingTheory.AlgebraicIndependent.Defs

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Algebraic independence for the Cantor--Bendixson degree

A minimal system of homogeneous generators is algebraically independent. Equivalently, polynomial
evaluation at the generators is injective. The proof is a transfinite induction on weighted degree.
Degree zero is scalar. A successor weighted degree is handled by the lowering derivation. At a
non-zero limit weighted degree, maximal-variable linearity and the required partial-derivative
identities are established together.

The argument for a successor degree is stated over an arbitrary filter. The argument for a limit
ordinal degree uses the hypotheses supplied by its ordered-group setting. This file records what
the induction needs and does not otherwise depend on the setting, so that what remains for the
Cantor--Bendixson degree is exactly the list of hypotheses below.
-/

universe u v w x

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
variable (hx : OrdinalGraded.IsMinimalSystem
  (DirectSum.rangeLof K (cantorBendixsonDegreeValuation (G := G) (R := K)).Component) wt xg)
include hx

/-- **Polynomiality, degree by degree.** Evaluation at a minimal system is injective in every
degree, given the successor step and the three inputs of the limit step in every degree below. -/
theorem injectiveAt_of_isMinimalSystem
    (hleading : ∀ α : NatOrdinal.{u}, (∀ β < α, OrdinalGraded.InjectiveAt K wt xg β) →
      ∀ {F : MvPolynomial ι K}, IsWeightedHomogeneous wt F α → aeval xg F = 0 →
      ∀ {B₀ : ι}, B₀ ∈ F.vars → (∀ i ∈ F.vars, wt i ≤ wt B₀) → wt B₀ < α →
      ∀ {degHD : NatOrdinal.{u}}, degHD + degreeOf B₀ F • wt B₀ = α →
      (degHD = 0 ∨ NatOrdinal.leastTerm degHD ≤ NatOrdinal.leastTerm (wt B₀)) → False)
    (hlin : ∀ α : NatOrdinal.{u}, (∀ β < α, OrdinalGraded.InjectiveAt K wt xg β) →
      ∀ S : LimitOrdinalRelationAtCutoff σ α, degreeOf S.B₀ S.F = 1)
    (hpartials : ∀ α : NatOrdinal.{u}, (∀ β < α, OrdinalGraded.InjectiveAt K wt xg β) →
      ∀ S : LimitOrdinalRelationAtCutoff σ α, ∀ v', v' ∈ S.F.vars → S.LowDegreePartAlgebraicLE v' →
      ∃ (s : Finset ι) (U : ι → MvPolynomial ι K), (∀ v ∈ s,
        S.ContributesToPartialDerivativeAt v' v) ∧
        (∀ v ∈ s, pderiv S.B₀ (U v) = 0) ∧ pderiv v' S.F = ∑ v ∈ s, pderiv v S.F * U v)
    (α : NatOrdinal.{u}) : OrdinalGraded.InjectiveAt K wt xg α := by
  letI : Nontrivial ((cantorBendixsonDegreeValuation (G := G) (R := K)).Component 0) :=
    Function.Injective.nontrivial
      (cantorBendixsonLayerScalarHom_injective (G := G) (K := K))
  letI : Nontrivial (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded :=
    Function.Injective.nontrivial (DirectSum.of_injective 0)
  exact OrdinalGraded.injectiveAt_of_zero_successor_limit
    (OrdinalGraded.injectiveAt_zero hx.ne_zero)
    (fun _ hcc ih ↦ HahnSeries.Nonpositive.injectiveAt_of_forall_lt hx
      (pos_iff_ne_zero.mpr hcc) ih)
    (fun α hα hcc ih ↦
      injectiveAt_of_limit σ hx (hleading α ih) (hlin α ih) (hpartials α ih) hα hcc)
    α

/-- **Polynomiality, degree by degree.** The leading-coefficient obstruction has been discharged;
only linearity of the maximal variable and the partial-derivative identities remain. -/
@[blueprint "lem:cantor-bendixson-degree-induction"
  (phase := "Algebraic independence in graded rings")
  (title := "Degreewise injectivity of homogeneous evaluation")
  (statement := /--
    Let $K$ be a field of characteristic zero and $G$ a nontrivial complete
    ordered abelian group with compatible additive uniformity and order
    topology. Let $\nu$ be the Cantor--Bendixson degree on
    $K((G^{\le0}))$. Let $x_i\in(\operatorname{gr}_\nu)_{w_i}$ be a minimal
    homogeneous generating system, and choose series $b_i$ representing
    $x_i$ in degree $w_i$. Suppose
    \[
      \nu(b_i)\le w_i,
      \qquad \nu(b_i^{\vert y})<w_i\quad(y<0).
    \]

    For every degree $\alpha$, assume evaluation is injective in all degrees
    below $\alpha$. Consider any data
    \[
      0\ne F\in K[X_i:i\in I],\quad B_0\in\operatorname{vars}(F),
      \quad \beta,\Delta,\lambda_0,\alpha_1,
    \]
    satisfying all of the following conditions:

    * $F$ is weighted homogeneous of degree $\alpha$, $F(x)=0$, every
      variable $X_i$ of $F$ has $w_i<\alpha$ and zero constant Cantor
      coefficient, and $w_i\le w_{B_0}$;
    * with $D=\deg_{B_0}F$, one has
      $\Delta\oplus D w_{B_0}=\alpha$, $\Delta\ne0$, every Cantor term of
      $\Delta$ is at least $\omega^\beta$, and the last Cantor term of
      $w_{B_0}$ is below $\omega^\beta$;
    * $\lambda_0<\alpha_{<\beta}$ and
      \[
        \alpha_1\le\alpha_{\ge\beta}\oplus\lambda_0,
        \qquad \alpha_1\le\alpha;
      \]
    * for all $y<0$ sufficiently close to $0$, the translated truncation of
      $F(b)$ at $y$ has degree below $\alpha_1$, and every convolution term
      $\rho$ from a monomial of $F$ using at least two translated
      truncations satisfies
      $\rho<\alpha_{\ge\beta}\oplus\lambda_0$.

    Suppose first that $D=1$ for every such choice of data. Suppose also that
    whenever $X_{B'}$ occurs in $F$ and
    $(w_{B'})_{<\beta}\oplus\eta=\lambda_0$ for some $\eta$, there are a
    finite set $S$ and polynomials $U_B$ for $B\in S$ such that
    \[
      \frac{\partial F}{\partial X_{B'}}
        =\sum_{B\in S}\frac{\partial F}{\partial X_B}U_B,
      \qquad \frac{\partial U_B}{\partial X_{B_0}}=0.
    \]
    Every $B\in S$ occurs in $F$ and satisfies either
    $(w_B)_{<\beta}=\alpha_{<\beta}$, or
    \[
      0\ne(w_B)_{<\beta}\ne\alpha_{<\beta},\qquad
      \nexists\xi,\ (w_B)_{<\beta}\oplus\xi=\lambda_0,
      \qquad w_{B'}<w_B.
    \]

    Then, for every $\alpha$, a weighted-homogeneous polynomial $P$ of
    degree $\alpha$ with $P(x)=0$ is zero.
  -/)
  (proof := /--
  Proceed by transfinite induction on $\alpha$. Degree zero contains only
  scalars because every $w_i$ is positive.

  If the constant Cantor coefficient of $\alpha$ is positive,
  \ref{lem:cantor-bendixson-successor-step} gives injectivity directly
  from the induction hypothesis.

  It remains to consider $\alpha\ne0$ with zero constant Cantor coefficient.
  For the representatives $b_i$, the translated-truncation hypothesis and
  \ref{lem:cantor-bendixson-leading-coefficient} exclude the case in which
  the leading coefficient in a maximal variable is scalar or has no smaller
  last Cantor term. In the complementary case, the assumed equation
  $D=1$ and the partial-derivative decompositions are exactly the remaining
  hypotheses of \ref{lem:cantor-bendixson-limit-ordinal-evaluation}, which gives
  injectivity in degree $\alpha$.
  -/)]
theorem injectiveAt_of_isMinimalSystem_of_limitOrdinalCases
    (hσ : LiftFamily.HasLowerTruncationDegrees σ)
    (hlin : ∀ α : NatOrdinal.{u}, (∀ β < α, OrdinalGraded.InjectiveAt K wt xg β) →
      ∀ S : LimitOrdinalRelationAtCutoff σ α, degreeOf S.B₀ S.F = 1)
    (hpartials : ∀ α : NatOrdinal.{u}, (∀ β < α, OrdinalGraded.InjectiveAt K wt xg β) →
      ∀ S : LimitOrdinalRelationAtCutoff σ α, ∀ v', v' ∈ S.F.vars → S.LowDegreePartAlgebraicLE v' →
      ∃ (s : Finset ι) (U : ι → MvPolynomial ι K), (∀ v ∈ s,
        S.ContributesToPartialDerivativeAt v' v) ∧
        (∀ v ∈ s, pderiv S.B₀ (U v) = 0) ∧
          pderiv v' S.F = ∑ v ∈ s, pderiv v S.F * U v)
    (α : NatOrdinal.{u}) : OrdinalGraded.InjectiveAt K wt xg α :=
  injectiveAt_of_isMinimalSystem σ hx
    (fun _ hinj _ hF hF0 _ hB₀ hmax hg _ hdegHD hcase ↦
      false_of_aeval_eq_zero_of_leastTerm_le σ hx hσ hinj
        hF hF0 hB₀ hmax hg hdegHD hcase)
    hlin hpartials α

/-- **Berarducci.** Evaluation at a minimal system of homogeneous generators is injective. -/
theorem aeval_injective_of_isMinimalSystem
    (hleading : ∀ α : NatOrdinal.{u}, (∀ β < α, OrdinalGraded.InjectiveAt K wt xg β) →
      ∀ {F : MvPolynomial ι K}, IsWeightedHomogeneous wt F α → aeval xg F = 0 →
      ∀ {B₀ : ι}, B₀ ∈ F.vars → (∀ i ∈ F.vars, wt i ≤ wt B₀) → wt B₀ < α →
      ∀ {degHD : NatOrdinal.{u}}, degHD + degreeOf B₀ F • wt B₀ = α →
      (degHD = 0 ∨ NatOrdinal.leastTerm degHD ≤ NatOrdinal.leastTerm (wt B₀)) → False)
    (hlin : ∀ α : NatOrdinal.{u}, (∀ β < α, OrdinalGraded.InjectiveAt K wt xg β) →
      ∀ S : LimitOrdinalRelationAtCutoff σ α, degreeOf S.B₀ S.F = 1)
    (hpartials : ∀ α : NatOrdinal.{u}, (∀ β < α, OrdinalGraded.InjectiveAt K wt xg β) →
      ∀ S : LimitOrdinalRelationAtCutoff σ α, ∀ v', v' ∈ S.F.vars → S.LowDegreePartAlgebraicLE v' →
      ∃ (s : Finset ι) (U : ι → MvPolynomial ι K), (∀ v ∈ s,
        S.ContributesToPartialDerivativeAt v' v) ∧
        (∀ v ∈ s, pderiv S.B₀ (U v) = 0) ∧ pderiv v' S.F = ∑ v ∈ s, pderiv v S.F * U v) :
    Function.Injective (aeval xg :
      MvPolynomial ι K →ₐ[K] (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded) :=
  OrdinalGraded.aeval_injective_of_forall_injectiveAt hx.mem
    (injectiveAt_of_isMinimalSystem σ hx hleading hlin hpartials)

/-- **Algebraic independence.** A minimal homogeneous generating system is algebraically
independent once maximal variables occur linearly and the partial-derivative identities hold. -/
@[blueprint "thm:cantor-bendixson-polynomiality"
  (phase := "Algebraic independence in graded rings")
  (title := "Algebraic independence of a minimal homogeneous generating system")
  (statement := /--
    Let $K,G,\nu,(x_i),(w_i)$, and the representatives $(b_i)$ satisfy the
    ambient, minimality, representation, and translated-truncation hypotheses
    of \ref{lem:cantor-bendixson-degree-induction}. Assume, conditionally on
    injectivity in all degrees below $\alpha$, both conclusions required there
    for every tuple satisfying its relation, cutoff, translated-truncation,
    and convolution hypotheses: the maximal variable occurs with degree one,
    and each indicated partial derivative has the displayed finite
    decomposition with coefficients independent of $X_{B_0}$ and with the
    displayed restrictions on the indices. Then $(x_i)$ is algebraically
    independent over $K$.
  -/)
  (proof := /--
  By \ref{lem:cantor-bendixson-degree-induction}, evaluation at $(x_i)$ is
  injective on weighted-homogeneous polynomials of every degree. If a
  polynomial $P$ evaluates to zero, then its evaluated component in degree
  $\alpha$ is the evaluation of the weighted-homogeneous component $P_\alpha$.
  Hence every $P_\alpha$ is zero. Since $P$ is the finite sum of these
  components, $P=0$. Thus polynomial evaluation at $(x_i)$ is injective,
  which is equivalent to algebraic independence over $K$.
  -/)]
theorem algebraicIndependent_of_isMinimalSystem_of_limitOrdinalCases
    (hσ : LiftFamily.HasLowerTruncationDegrees σ)
    (hlin : ∀ α : NatOrdinal.{u}, (∀ β < α, OrdinalGraded.InjectiveAt K wt xg β) →
      ∀ S : LimitOrdinalRelationAtCutoff σ α, degreeOf S.B₀ S.F = 1)
    (hpartials : ∀ α : NatOrdinal.{u}, (∀ β < α, OrdinalGraded.InjectiveAt K wt xg β) →
      ∀ S : LimitOrdinalRelationAtCutoff σ α, ∀ v', v' ∈ S.F.vars → S.LowDegreePartAlgebraicLE v' →
      ∃ (s : Finset ι) (U : ι → MvPolynomial ι K), (∀ v ∈ s,
        S.ContributesToPartialDerivativeAt v' v) ∧
        (∀ v ∈ s, pderiv S.B₀ (U v) = 0) ∧
          pderiv v' S.F = ∑ v ∈ s, pderiv v S.F * U v) :
    AlgebraicIndependent K xg :=
  algebraicIndependent_iff_injective_aeval.mpr
    (OrdinalGraded.aeval_injective_of_forall_injectiveAt hx.mem
      (injectiveAt_of_isMinimalSystem_of_limitOrdinalCases σ hx hσ hlin hpartials))

/-- **Cantor--Bendixson polynomiality from a convex subgroup base, degree by degree.** The
leading-coefficient, linearity, and partial-derivative obligations are all discharged. -/
theorem injectiveAt_of_isMinimalSystem_of_subgroupBase
    [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
    {κ : Type x} [LinearOrder κ] [WellFoundedLT κ]
    (U : κ → AddSubgroup G)
    (hUmono : ∀ {i j : κ}, i ≤ j → (U j : Set G) ⊆ (U i : Set G))
    (hUopen : ∀ i, IsOpen (U i : Set G))
    (hUconv : ∀ i, (U i : Set G).OrdConnected)
    (hUbase : ∀ ε : G, 0 < ε → ∃ i, (U i : Set G) ⊆ Set.Ioo (-ε) ε)
    (hσ : LiftFamily.HasLowerTruncationDegrees σ) (α : NatOrdinal.{u}) :
    OrdinalGraded.InjectiveAt K wt xg α :=
  injectiveAt_of_isMinimalSystem_of_limitOrdinalCases σ hx hσ
    (fun _ hinj S ↦ S.degreeOf_eq_one hx hσ hinj)
    (fun _ hinj S _ hv' hpartials ↦
      S.exists_finset_pderiv_eq_sum_of_lowDegreePartAlgebraicLE U hUmono hUopen hUconv hUbase
        hx hinj hσ hv' hpartials)
    α

/-- **Cantor--Bendixson polynomiality from a convex subgroup base.** Evaluation at a minimal system
of homogeneous generators is injective. -/
theorem aeval_injective_of_isMinimalSystem_of_subgroupBase
    [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
    {κ : Type x} [LinearOrder κ] [WellFoundedLT κ]
    (U : κ → AddSubgroup G)
    (hUmono : ∀ {i j : κ}, i ≤ j → (U j : Set G) ⊆ (U i : Set G))
    (hUopen : ∀ i, IsOpen (U i : Set G))
    (hUconv : ∀ i, (U i : Set G).OrdConnected)
    (hUbase : ∀ ε : G, 0 < ε → ∃ i, (U i : Set G) ⊆ Set.Ioo (-ε) ε)
    (hσ : LiftFamily.HasLowerTruncationDegrees σ) :
    Function.Injective (aeval xg : MvPolynomial ι K →ₐ[K]
      (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded) :=
  OrdinalGraded.aeval_injective_of_forall_injectiveAt hx.mem
    (injectiveAt_of_isMinimalSystem_of_subgroupBase σ hx U hUmono hUopen hUconv hUbase hσ)

/-- A minimal system of homogeneous generators is algebraically independent when the nonzero
Archimedean classes have no smallest magnitude. -/
@[blueprint "thm:cantor-bendixson-minimal-generators-independent"
  (phase := "Algebraic independence in graded rings")
  (title := "Algebraic independence in the Cantor--Bendixson associated graded ring")
  (statement := /--
    Let $K$ be a field of characteristic zero and let $G$ be a nontrivial,
    densely ordered abelian group without endpoints, equipped with a compatible
    additive uniformity and order topology.  Assume that $G$ is Cauchy complete.
    Suppose the
    nonzero Archimedean classes of $G$ have no least element in the magnitude
    order.  Let $\nu$ be the Cantor--Bendixson degree on $K((G^{\le0}))$.

    If $x_i\in(\operatorname{gr}_\nu)_{w_i}$ is a minimal homogeneous
    generating system and each $x_i$ is represented by a series $b_i$ such
    that
    \[
      \nu(b_i)\le w_i,
      \qquad \nu(b_i^{\vert y})<w_i\quad(y<0),
    \]
    then the family $(x_i)$ is algebraically independent over $K$.
  -/)
  (proof := /--
    By \ref{lem:cantor-bendixson-degree-induction}, injectivity of homogeneous
    evaluation reduces to the two nontrivial requirements when the degree is a limit ordinal.
    These requirements follow from \ref{lem:linear-occurrence} and
    \ref{lem:limit-ordinal-partial-derivative-decomposition}.
    By \ref{lem:well-founded-archimedean-ball-basis}, the hypothesis on
    Archimedean classes supplies a decreasing well-founded neighbourhood
    basis of open order-convex additive subgroups.
    Evaluation is therefore injective in every homogeneous degree, hence on
    the whole polynomial ring.
  -/)]
theorem algebraicIndependent_of_minimal_system
    [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
    [NoMaxOrder (FiniteArchimedeanClass G)]
    (hσ : LiftFamily.HasLowerTruncationDegrees σ) : AlgebraicIndependent K xg := by
  obtain ⟨κ, hlin, hwf, U, hUmono, hUopen, hUconv, hUbase⟩ :=
    ArchimedeanClass.exists_wellFounded_archimedeanBall_basis (G := G)
  letI := hlin
  letI := hwf
  exact algebraicIndependent_iff_injective_aeval.mpr
    (aeval_injective_of_isMinimalSystem_of_subgroupBase σ hx U
      (fun hij ↦ hUmono hij) hUopen hUconv hUbase hσ)

end HahnSeries.Germ

end
