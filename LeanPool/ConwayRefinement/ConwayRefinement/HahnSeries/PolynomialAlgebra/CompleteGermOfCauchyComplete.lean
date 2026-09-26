/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PolynomialAlgebra.CompleteGerm

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Polynomial presentation of a germ ring

For a Cauchy-complete exponent group, a minimal homogeneous generating system for the
Cantor--Bendixson degree is algebraically independent. Representatives of the generators identify
the quotient by series bounded strictly below zero with a polynomial ring.
-/

open Set
open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
  [NoMaxOrder (FiniteArchimedeanClass G)]
  [Field K] [CharZero K]

/-- For an ordered exponent group that is Cauchy complete and has no smallest nonzero magnitude,
the quotient by series supported away from zero is a polynomial algebra. -/
@[blueprint "thm:complete-hahn-germ-polynomial-algebra"
  (phase := "Polynomial presentations")
  (title := "Polynomial presentation of the germ ring over a Cauchy-complete exponent group")
  (statement := /--
    Let $K$ be a field of characteristic zero and let $G$ be a nontrivial,
    densely ordered abelian group with no least or greatest element and with
    no least nonzero Archimedean class in the magnitude order.  Assume that
    $G$ is Cauchy complete for its additive uniformity.  If $J$ is the ideal
    of series in $K((G^{\le 0}))$ whose support is bounded strictly below zero,
    then for some set $I$ there is a $K$-algebra isomorphism
    \[
      K[X_i:i\in I]\simeq K((G^{\le 0}))/J.
    \]
  -/)
  (proof := /--
    Applying \ref{lem:extend-to-minimal-system} to the empty family gives a
    minimal homogeneous generating system of the associated graded ring of the
    Cantor--Bendixson degree.  Well-order the nonzero Archimedean classes and
    retain each class that is smaller in magnitude than every earlier class.
    The resulting family is coinitial in the magnitude order and well-founded
    when ordered by reverse magnitude.  Its groups $G_{\prec\sigma}$ therefore
    form a decreasing neighbourhood basis at zero.  Choose
    series representing the generators.  By
    \ref{thm:cantor-bendixson-minimal-generators-independent}, these generators
    are algebraically independent.  Minimality makes homogeneous evaluation
    surjective.  Evaluation at the representatives is therefore surjective
    modulo $J$, while its highest nonzero weighted-homogeneous component proves
    injectivity modulo $J$.
  -/)]
theorem exists_mvPolynomial_algEquiv_germ :
    ∃ ι : Type (max (u + 1) v), Nonempty
      (MvPolynomial ι K ≃ₐ[K]
        Nonpositive G K ⧸ (cantorBendixsonValuation (G := G) (R := K)).supp) := by
  let ν := cantorBendixsonDegreeValuation (G := G) (R := K)
  obtain ⟨ι, weight, generators, hminimal⟩ := OrdinalGraded.exists_isMinimalSystem
    (DirectSum.rangeLof K (ν).Component)
  obtain ⟨lifts, hlower⟩ := exists_liftFamily_hasLowerTruncationDegrees hminimal.mem
  have hindependent : AlgebraicIndependent K generators :=
    HahnSeries.Germ.algebraicIndependent_of_minimal_system
      lifts hminimal hlower
  have hgenerate : Function.Surjective (MvPolynomial.aeval generators :
      MvPolynomial ι K →ₐ[K] (ν).AssociatedGraded) :=
    cantorBendixson_ordinalMinimalSystem_aeval_surjective weight generators hminimal
  exact ⟨ι, ⟨HahnSeries.Germ.germAlgEquiv lifts hindependent hgenerate⟩⟩

end HahnSeries.Nonpositive
