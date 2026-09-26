/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PolynomialAlgebra.CompleteGermOfCauchyComplete

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Refinement of a complete generalised-power-series germ ring

The polynomial presentation of the quotient by series bounded strictly below zero gives
four-factor refinement in that quotient.
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

/-- An ordered exponent group that is Cauchy complete and has no smallest nonzero magnitude has
four-factor refinement modulo series bounded away from zero. -/
@[blueprint "thm:complete-hahn-germ-refinement"
  (phase := "Refinement over Archimedean classes")
  (title := "Four-factor refinement in the germ ring over a Cauchy-complete exponent group")
  (statement := /--
    Under the hypotheses of
    \ref{thm:complete-hahn-germ-polynomial-algebra}, if
    $a,b,c,d\in K((G^{\le 0}))$ and $ab=cd$, then there are
    $e,f,g,h\in K((G^{\le 0}))$ such that, modulo series whose support is
    bounded strictly below zero,
    \[
      a=ef,\qquad b=gh,\qquad c=eg,\qquad d=fh.
    \]
  -/)
  (proof := /--
    By \ref{thm:complete-hahn-germ-polynomial-algebra}, the germ ring is a
    polynomial ring over $K$, hence is a unique factorisation domain and has
    the refinement property.  Refine the four images in the quotient and
    choose series representing the four factors.
  -/)]
theorem exists_germ_refinement_of_complete_exponent_group
    (a b c d : Nonpositive G K) (habcd : a * b = c * d) :
    ∃ e f g h : Nonpositive G K,
      (∃ r < (0 : G), ∀ q > r,
        (a : HahnSeries G K).coeff q = (e * f : Nonpositive G K).1.coeff q) ∧
      (∃ r < (0 : G), ∀ q > r,
        (b : HahnSeries G K).coeff q = (g * h : Nonpositive G K).1.coeff q) ∧
      (∃ r < (0 : G), ∀ q > r,
        (c : HahnSeries G K).coeff q = (e * g : Nonpositive G K).1.coeff q) ∧
      (∃ r < (0 : G), ∀ q > r,
        (d : HahnSeries G K).coeff q = (f * h : Nonpositive G K).1.coeff q) := by
  let J := (cantorBendixsonValuation (G := G) (R := K)).supp
  obtain ⟨ι, ⟨equiv⟩⟩ := exists_mvPolynomial_algEquiv_germ (G := G) (K := K)
  let : DecompositionMonoid (Nonpositive G K ⧸ J) :=
    MulEquiv.decompositionMonoid equiv.symm.toMulEquiv
  have hrefinement : HasFourFactorRefinement (Nonpositive G K ⧸ J) :=
    hasFourFactorRefinement_of_decompositionMonoid
  obtain ⟨qe, qf, qg, qh, heq, hfq, hgq, hhq⟩ := hrefinement.refine
    (show Ideal.Quotient.mk J a * Ideal.Quotient.mk J b =
      Ideal.Quotient.mk J c * Ideal.Quotient.mk J d by
        simpa only [map_mul] using congrArg (Ideal.Quotient.mk J) habcd)
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective qe
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective qf
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective qg
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective qh
  refine ⟨e, f, g, h, ?_, ?_, ?_, ?_⟩
  · exact cantorBendixson_germ_eq_iff a (e * f) |>.mp heq
  · exact cantorBendixson_germ_eq_iff b (g * h) |>.mp hfq
  · exact cantorBendixson_germ_eq_iff c (e * g) |>.mp hgq
  · exact cantorBendixson_germ_eq_iff d (f * h) |>.mp hhq
end HahnSeries.Nonpositive
