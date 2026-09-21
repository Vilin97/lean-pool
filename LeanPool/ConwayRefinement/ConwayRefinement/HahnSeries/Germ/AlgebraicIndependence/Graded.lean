/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Germ
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGradedDomain
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Degree

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# The associated graded domain of the Cantor–Bendixson degree

Taking Cantor degree of the Cantor–Bendixson valuation gives an additive degree with natural
ordinal addition. At zero in the closed support this degree is exactly the support's
Cantor--Bendixson rank; away from the closed support it is bottom. Its kernel is the ideal
of series bounded strictly below zero.

The associated graded ring has no zero divisors by multiplicativity. The initial form of
one is nonzero, so this is a domain rather than a possibly trivial graded ring. The
construction retains the full ordered exponent group, assumed Cauchy complete, and the
hypotheses on the characteristic-zero coefficient domain. It supplies a graded domain, not a
polynomial presentation.
-/

public noncomputable section
open Set
open scoped NatOrdinal
universe u v
namespace HahnSeries.Nonpositive
variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CommRing R] [NoZeroDivisors R] [CharZero R]

/-- The Cantor degree of the Cantor–Bendixson valuation, with bottom on series bounded below
zero. -/
def cantorBendixsonDegreeValuation : MaxAddDegree (Nonpositive G R) NatOrdinal.{u} where
  toFun b := NatOrdinal.cantorDegree (cantorBendixsonValuation b)
  map_zero' := by rw [map_zero, NatOrdinal.cantorDegree_zero]
  map_one_le_zero' := by
    rw [map_one]
    rw [NatOrdinal.cantorDegree_eq_ordinalCantorDegree, NatOrdinal.val_one]
    exact Ordinal.cantorDegree_one.le
  map_neg' b := by rw [Valuation.map_neg]
  map_add_le_max' b c := by
    simp only [NatOrdinal.cantorDegree_eq_ordinalCantorDegree]
    rcases le_max_iff.mp (cantorBendixsonValuation.map_add b c) with h | h
    · exact le_max_of_le_left (Ordinal.cantorDegree_mono h)
    · exact le_max_of_le_right (Ordinal.cantorDegree_mono h)
  map_mul_le_add' b c := by
    rw [map_mul, NatOrdinal.cantorDegree_mul]

/-- Evaluation uses the Cantor degree of the Cantor–Bendixson value. -/
@[simp]
theorem cantorBendixsonDegreeValuation_apply (b : Nonpositive G R) :
    cantorBendixsonDegreeValuation b =
      NatOrdinal.cantorDegree (cantorBendixsonValuation b) := (rfl)

/-- The Cantor--Bendixson degree is multiplicative. -/
@[blueprint "thm:cantor-bendixson-degree-multiplicative"
  (phase := "Cantor–Bendixson ranks of supports")
  (title := "Multiplicativity of the Cantor--Bendixson degree")
  (statement := /--
    Let $R$ be a characteristic-zero domain and let $G$ be a nontrivial
    ordered abelian group equipped with a compatible additive uniformity and
    its order topology.  Assume that $G$ is Cauchy complete.  For all
    $b,c\in R((G^{\le0}))$,
    \[
      \deg\bigl(V_{\mathrm{CB}}(bc)\bigr)
        =\deg\bigl(V_{\mathrm{CB}}(b)\bigr)
          \oplus\deg\bigl(V_{\mathrm{CB}}(c)\bigr),
    \]
    where $\deg$ is Cantor degree, with value $-\infty$ at $0$, and
    $\oplus$ is Hessenberg's natural sum.
  -/)
  (proof := /--
    Take Cantor degree in
    \ref{thm:cantor-bendixson-value-multiplicative}.  Cantor degree sends
    Hessenberg's natural product to Hessenberg's natural sum.
  -/)]
theorem cantorBendixsonDegreeValuation_mul (b c : Nonpositive G R) :
    cantorBendixsonDegreeValuation (b * c) =
      cantorBendixsonDegreeValuation b + cantorBendixsonDegreeValuation c := by
  simp only [cantorBendixsonDegreeValuation_apply, map_mul, NatOrdinal.cantorDegree_mul]

instance : (cantorBendixsonDegreeValuation (G := G) (R := R)).IsMultiplicative := by
  constructor
  exact cantorBendixsonDegreeValuation_mul

/-- At a closed-support point zero, the degree is precisely its Cantor--Bendixson rank. -/
theorem cantorBendixsonDegreeValuation_of_mem (b : Nonpositive G R)
    (hb : 0 ∈ (b : HahnSeries G R).closedSupport) :
    cantorBendixsonDegreeValuation b =
      (NatOrdinal.of ((b : HahnSeries G R).cantorBendixsonRank 0) : WithBot NatOrdinal) := by
  rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
    cantorBendixsonValue_of_mem _ ((mem_closedSupport _ _).mp hb),
    NatOrdinal.of_omega0_opow, NatOrdinal.cantorDegree_wpow]

/-- The bottom degree is exactly the ideal defining germs at zero. -/
theorem cantorBendixsonDegreeValuation_eq_bot_iff (b : Nonpositive G R) :
    cantorBendixsonDegreeValuation b = ⊥ ↔
      ∃ c < (0 : G), (b : HahnSeries G R).support ⊆ Iic c := by
  rw [cantorBendixsonDegreeValuation_apply, NatOrdinal.cantorDegree_eq_bot,
    ← Valuation.mem_supp_iff, mem_cantorBendixsonValuation_supp]

/-- The associated graded ring for the Cantor–Bendixson degree is a domain. -/
theorem cantorBendixson_associatedGraded_isDomain :
    IsDomain
      (cantorBendixsonDegreeValuation (G := G) (R := R)).AssociatedGraded := by
  let ν := cantorBendixsonDegreeValuation (G := G) (R := R)
  have h1 : ν 1 ≠ ⊥ := by
    rw [cantorBendixsonDegreeValuation_apply, map_one, ne_eq, NatOrdinal.cantorDegree_eq_bot]
    exact one_ne_zero
  letI : Nontrivial ν.AssociatedGraded :=
    ⟨⟨ν.initialForm 1, 0, ν.initialForm_ne_zero_of_ne_bot h1⟩⟩
  exact NoZeroDivisors.to_isDomain ν.AssociatedGraded

end HahnSeries.Nonpositive
