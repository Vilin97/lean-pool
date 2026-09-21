/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
import Mathlib.RingTheory.AlgebraicIndependent.Basic

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.RealPartials

/-!
# The polynomiality of `P̂`

Let `K` be a field of characteristic `0` and `𝓑` a minimal system of homogeneous generators of
`P̂ = ⨁_α P_α`; in Lean the generators are `x i`, of degrees `wt i`. Evaluation
`K[X_B : B ∈ 𝓑] → P̂`, `X_B ↦ B`, is injective.

For real Hahn series, Berarducci's ordinal value is `omega` raised to the Cantor–Bendixson rank of
zero in the closed support. Thus LM24's Cantor degree is that rank, and `P̂` is
canonically the associated graded algebra of the Cantor–Bendixson degree. Its polynomiality is the
generic degree-induction theorem. The interval-based partial-derivative argument is the remaining
step specific to the real exponent group.
-/

universe v w

open scoped NatOrdinal
open MvPolynomial OrdinalGraded Berarducci

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] [CharZero K] {ι : Type w} {wt : ι → NatOrdinal}
  {x : ι → PrincipalSubring K}

private theorem algebraicIndependent_cantorBendixson
    (hx : IsMinimalSystem (principalGrading K) wt x) :
    AlgebraicIndependent K x := by
  let e := principalSubringCantorBendixsonAlgEquiv (K := K)
  let xg := fun i ↦ e (x i)
  have hxg : IsMinimalSystem
      (DirectSum.rangeLof K (HahnSeries.Nonpositive.cantorBendixsonDegreeValuation
        (G := ℝ) (R := K)).Component) wt xg :=
    minimalSystem_cantorBendixson hx
  obtain ⟨σ, hσ⟩ := Lifts.exists_isPrincipal hx
  let σg := σ.cantorBendixson
  have hσg : HahnSeries.Nonpositive.LiftFamily.HasLowerTruncationDegrees σg :=
    hσ.cantorBendixson
  have haixg : AlgebraicIndependent K xg :=
    HahnSeries.Germ.algebraicIndependent_of_isMinimalSystem_of_limitOrdinalCases σg hxg hσg
      (fun _ hinj S ↦ S.degreeOf_eq_one hxg hσg hinj)
      (fun α hinj S v' hv' hlowDegree ↦ by
        change HahnSeries.Germ.LimitOrdinalRelationAtCutoff σ.cantorBendixson α at S
        change ∀ β < α, InjectiveAt K wt
          (fun i ↦ principalSubringCantorBendixsonAlgEquiv (x i)) β at hinj
        exact Lifts.RealPartialDecomposition.lowDegreePartAlgebraicLE_partials S hx hinj hσ hv'
          hlowDegree)
  have hxg_eq : e.toAlgHom ∘ x = xg := by rfl
  rw [← hxg_eq] at haixg
  exact (e.toAlgHom.algebraicIndependent_iff e.injective).mp haixg

/-- **The polynomiality of `P̂`, degree by degree.** For a minimal system of homogeneous
generators `x` of degrees `wt`, evaluation is injective in every degree `α`: a polynomial
homogeneous of degree `α` that evaluates to `0` in `P̂` is `0`. -/
theorem injectiveAt_of_isMinimalSystem (hx : IsMinimalSystem (principalGrading K) wt x)
    (α : NatOrdinal) : InjectiveAt K wt x α := by
  rw [OrdinalGraded.injectiveAt_iff]
  intro F _ hF
  apply algebraicIndependent_iff_injective_aeval.mp (algebraicIndependent_cantorBendixson hx)
  rw [hF, map_zero]

/-- **The algebraic independence of minimal systems in `P̂`.** Every minimal system of
homogeneous generators is algebraically independent. -/
@[blueprint "thm:polynomial"
  (phase := "Principal RV-elements")
  (title := "Minimal homogeneous generators of $\\widehat{\\mathrm P}$ are algebraically \
    independent")
  (statement := /--
    Let $K$ be a field of characteristic zero. If $(x_i)_{i\in I}$ is a
    minimal homogeneous generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$, then $(x_i)_{i\in I}$ is algebraically
    independent over $K$.
  -/)
  (proof := /--
  Choose principal series representatives $b_i$ of the $x_i$.
  By \ref{lem:principal-representatives-cantor-bendixson}, $(x_i)$ is a minimal
  homogeneous generating system of
  $\operatorname{gr}_{\delta_{\mathrm{CB}}}K((\mathbb R^{\le0}))$, and the
  same $b_i$ have the required degree and translated-truncation
  properties for the Cantor--Bendixson grading.

  Apply \ref{thm:cantor-bendixson-polynomiality}. Its two nontrivial relation
  hypotheses follow from \ref{lem:linear-occurrence} and
  \ref{lem:real-translated-truncation-partials}. Thus the
  transported family is algebraically independent. Injectivity of the graded
  isomorphism transports algebraic independence back to $(x_i)$ in
  $\widehat{\mathrm P}$.
  -/)
  (highlight)]
theorem algebraicIndependent_of_isMinimalSystem
    (hx : IsMinimalSystem (principalGrading K) wt x) : AlgebraicIndependent K x :=
  algebraicIndependent_cantorBendixson hx

/-- **The polynomiality of `P̂`.** Evaluation `K[X_B : B ∈ 𝓑] → P̂` at a minimal system of
homogeneous generators is injective. -/
theorem aeval_injective_of_isMinimalSystem (hx : IsMinimalSystem (principalGrading K) wt x) :
    Function.Injective (aeval x : MvPolynomial ι K →ₐ[K] PrincipalSubring K) :=
  algebraicIndependent_iff_injective_aeval.mp (algebraicIndependent_of_isMinimalSystem hx)

end Berarducci
