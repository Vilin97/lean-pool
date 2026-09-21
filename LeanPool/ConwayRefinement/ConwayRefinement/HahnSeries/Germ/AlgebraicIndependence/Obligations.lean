/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.DerivationIdeal
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.SyzygyIntegration
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.GermFinitePartIdeal
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.GermSuccessorStep

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Integration for the Cantor–Bendixson derivation

The polynomiality induction over an arbitrary filter takes the integration statements as
hypotheses, because the abstract lowering-derivation interface does not supply them. The
Cantor–Bendixson setting proves them by integrating prescribed homogeneous classes along cofinal
cutoffs, and this file matches those statements to the forms required by the induction.

The only work is the passage between a degree with positive finite part and its predecessor: the
induction states the hypothesis for a degree whose finite part is positive, and the
Cantor–Bendixson theorem states it for a successor.
-/

universe u v w

open scoped NatOrdinal Topology

open Filter MvPolynomial HahnSeries HahnSeries.Nonpositive

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

/-- Ideal membership from the Cantor–Bendixson derivative germ. A degree with positive finite part
is a successor, so the predecessor form of the integration theorem applies. -/
theorem hasIdealIntegration {ι' : Type w} [Finite ι'] {q : ι' → (ν).AssociatedGraded}
    {c : ι' → NatOrdinal.{u}}
    (hq : ∀ j, q j ∈ DirectSum.rangeLof K (ν).Component (c j))
    (hc : ∀ j, (c j).constantCoeff = 0)
    {b : NatOrdinal.{u}} (hb : 0 < b.constantCoeff)
    {y : (ν).AssociatedGraded} (hy : y ∈ DirectSum.rangeLof K (ν).Component b)
    {f : G → (ν).AssociatedGraded} (hf : ∀ t, f t ∈ Ideal.span (Set.range q))
    (hD : cantorBendixsonGradedDerivation y =
      (f : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded)) :
    y ∈ Ideal.span (Set.range q) := by
  have hsucc : b.removeNat 1 + 1 = b := by
    have hstep := NatOrdinal.removeNat_add_natCast (a := b) (n := 1) hb
    rwa [Nat.cast_one] at hstep
  refine mem_span_of_cantorBendixsonGradedDerivation_eq_coe hq hc (δ := b.removeNat 1) ?_ hf hD
  rwa [hsucc]

/-- The ideal-integration theorem for the Cantor–Bendixson derivation. -/
theorem hasIdealIntegrationDerivation {ι' : Type w} [Finite ι']
    {q : ι' → (ν).AssociatedGraded} {c : ι' → NatOrdinal.{u}}
    (hq : ∀ j, q j ∈ DirectSum.rangeLof K (ν).Component (c j))
    (hc : ∀ j, (c j).constantCoeff = 0)
    {b : NatOrdinal.{u}} (hb : 0 < b.constantCoeff)
    {y : (ν).AssociatedGraded} (hy : y ∈ DirectSum.rangeLof K (ν).Component b)
    {f : G → (ν).AssociatedGraded} (hf : ∀ t, f t ∈ Ideal.span (Set.range q))
    (hD : cantorBendixsonDerivation y =
      (f : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded)) :
    y ∈ Ideal.span (Set.range q) :=
  hasIdealIntegration hq hc hb hy hf (cantorBendixsonDerivation_apply y ▸ hD)

/-- The successor step for the Cantor–Bendixson derivation. -/
@[blueprint "lem:cantor-bendixson-successor-step"
  (phase := "Algebraic independence in graded rings")
  (title := "Successor step for Cantor--Bendixson homogeneous evaluation")
  (statement := /--
    Let $K$ be a field of characteristic zero, and let $G$ be a nontrivial
    ordered abelian group with compatible additive uniformity and order
    topology.  Assume that $G$ is Cauchy complete, and let $\nu$ be the
    Cantor--Bendixson degree on
    $K((G^{\le0}))$.  Let $(x_i)$ be a minimal homogeneous generating system
    of $\operatorname{gr}_\nu$, with weights $w_i$.  If the coefficient of
    $1=\omega^0$ in the Cantor normal form of $\delta$ is positive and
    homogeneous evaluation at $(x_i)$ is injective in every degree below
    $\delta$, then it is injective in degree $\delta$.
  -/)
  (proof := /--
    Suppose a nonzero weighted-homogeneous polynomial $F$ of degree $\delta$
    evaluates to zero.  The chain rule for the Cantor--Bendixson lowering
    derivation makes the derivative values of each relevant partial derivative
    pointwise combinations of the distinguished partial derivatives.  By
    \ref{lem:successor-ideal-membership-from-cantor-bendixson-derivative},
    these pointwise combinations give ideal membership. Then
    \ref{lem:weighted-euler-identity} places $F$ in that ideal.

    By \ref{lem:successor-relation-decomposition}, choose a
    finite family of relevant partial derivatives.  Their polynomial syzygies
    have a finite generating family by \ref{lem:syzygies-finite-variables}.
    Homogeneous ideal decomposition expresses every remaining partial
    derivative in the chosen family, producing a homogeneous coefficient tuple
    whose evaluation is a syzygy.
    \ref{lem:simultaneous-cantor-bendixson-derivative-representatives}
    supplies representatives that define a polynomial derivation.  By
    \ref{lem:polynomial-vector-field-lowers-degree}, it lowers the constant
    Cantor coefficient.  Apply the induction hypothesis to the resulting
    lower-degree syzygies, express them in the finite generating family, and
    choose homogeneous polynomial representatives by \ref{lem:generate}.
    This expresses the evaluated cofactor tuple as a combination of evaluated
    syzygies.  Consequently its linear part lies in the square of the
    positive-degree ideal, contradicting the defining independence of a
    minimal homogeneous generating system modulo that square.
  -/)]
theorem injectiveAt_of_forall_lt
    {ι : Type w} {wt : ι → NatOrdinal.{u}} {x : ι → (ν).AssociatedGraded}
    (hx : OrdinalGraded.IsMinimalSystem
      (DirectSum.rangeLof K (ν).Component) wt x)
    {δ : NatOrdinal.{u}} (hδ : 0 < δ.constantCoeff)
    (hinj : ∀ β < δ, OrdinalGraded.InjectiveAt K wt x β) :
    OrdinalGraded.InjectiveAt K wt x δ :=
  OrdinalGraded.injectiveAt_of_forall_lt hx
    cantorBendixson_isLoweringDerivation cantorBendixson_gradeZeroScalars
    hasIdealIntegrationDerivation
    (fun lam ↦ hasSyzygyIntegration lam) hδ hinj

end HahnSeries.Nonpositive

end
