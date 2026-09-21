/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.AlgebraicIndependence
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.Extension
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.Refinement
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Refinement in the quotient by series bounded strictly below zero

The homogeneous generators of the associated graded ring of the Cantor–Bendixson degree are
algebraically independent. Representatives of these generators present the germ quotient as the
same polynomial ring.
Surjectivity removes leading homogeneous classes until only a bounded-away-from-zero series
remains. Injectivity follows because the highest nonzero weighted homogeneous part cannot evaluate
to a bounded-away-from-zero series.

The resulting algebra equivalence transports four-factor refinement from the polynomial ring to
the germ quotient. This is the precise bridge from algebraic independence to germ refinement; no
lifting of a chosen graded factorisation is required.
-/

universe u v w

open scoped NatOrdinal Topology

open MvPolynomial HahnSeries HahnSeries.Nonpositive

public noncomputable section

namespace HahnSeries.Germ

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))
local notation "J" => Valuation.supp (cantorBendixsonValuation (G := G) (R := K))

variable {ι : Type w} {wt : ι → NatOrdinal.{u}}
  {xg : ι → (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded}
variable (σ : LiftFamily wt xg)

/-- Evaluation at representatives, followed by passage to the quotient by bounded series. -/
def germAlgHom : MvPolynomial ι K →ₐ[K] Nonpositive G K ⧸ J :=
  (Ideal.Quotient.mkₐ K J).comp (aeval σ.lift)

theorem germAlgHom_apply (F : MvPolynomial ι K) :
    germAlgHom σ F = Ideal.Quotient.mk J (aeval σ.lift F) := by
  rfl

/-- Generation of the associated graded ring makes evaluation at the lifts surjective on germs. -/
theorem germAlgHom_surjective
    (hgenerate : Function.Surjective
      (aeval xg : MvPolynomial ι K →ₐ[K] (ν).AssociatedGraded)) :
    Function.Surjective (germAlgHom σ) := by
  intro g
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨α, huα⟩ : ∃ α : NatOrdinal.{u}, ν u < (α : WithBot NatOrdinal) := by
    cases hν : ν u with
    | bot => exact ⟨0, WithBot.bot_lt_coe 0⟩
    | coe β => exact ⟨β + 1, WithBot.coe_lt_coe.mpr (lt_add_one β)⟩
  obtain ⟨F, -, -, hF⟩ := exists_forall_weight_lt_and_degree_sub_aeval_eq_bot
    xg σ.represents α (fun β _ y hy ↦ by
      obtain ⟨P, hP⟩ := hgenerate y
      exact ⟨weightedHomogeneousComponent wt β P,
        weightedHomogeneousComponent_isWeightedHomogeneous (w := wt) (n := β) (φ := P),
        (OrdinalGraded.decompose_aeval (𝒜 := DirectSum.rangeLof K (ν).Component)
          (fun i ↦ HahnSeries.Nonpositive.Represents.mem_rangeLof (σ.represents i)) P β).symm.trans
          (by
            rw [hP]
            exact DirectSum.decompose_of_mem_same _ hy)⟩) u huα
  refine ⟨F, ?_⟩
  rw [germAlgHom_apply, Ideal.Quotient.eq]
  rw [mem_cantorBendixsonValuation_supp,
    ← cantorBendixsonDegreeValuation_eq_bot_iff]
  rw [← neg_sub, MaxAddDegree.map_neg]
  exact hF

/-- Graded injectivity makes evaluation at the lifts injective after passage to germs. -/
theorem germAlgHom_injective
    (hinj : Function.Injective (aeval xg : MvPolynomial ι K →ₐ[K] (ν).AssociatedGraded)) :
    Function.Injective (germAlgHom σ) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro F hF
  by_contra hF0
  let β := F.support.sup (Finsupp.weight wt)
  obtain ⟨d, hd, hβ⟩ := Finset.exists_mem_eq_sup F.support
    (MvPolynomial.support_nonempty.mpr hF0) (Finsupp.weight wt)
  have hcomponent : weightedHomogeneousComponent wt β F ≠ 0 := by
    rw [MvPolynomial.ne_zero_iff]
    refine ⟨d, ?_⟩
    rw [coeff_weightedHomogeneousComponent, ite_eq_left hβ.symm]
    exact MvPolynomial.mem_support_iff.mp hd
  have hgraded : aeval xg (weightedHomogeneousComponent wt β F) ≠ 0 := by
    intro h
    apply hcomponent
    apply hinj
    simpa using h
  have hdegree : ν (aeval σ.lift F) = (β : WithBot NatOrdinal) :=
    degree_aeval_eq_of_aeval_weightedHomogeneousComponent_ne_zero xg σ.represents
      (fun _ hd' ↦ Finset.le_sup hd') hgraded
  rw [germAlgHom_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_cantorBendixsonValuation_supp,
    ← cantorBendixsonDegreeValuation_eq_bot_iff] at hF
  exact WithBot.coe_ne_bot (hdegree.symm.trans hF)

/-- Under graded polynomiality and generation, the quotient by series bounded strictly below zero
is a polynomial algebra on the chosen representatives. -/
def germAlgEquiv
    (hindependent : AlgebraicIndependent K xg)
    (hgenerate : Function.Surjective
      (aeval xg : MvPolynomial ι K →ₐ[K] (ν).AssociatedGraded)) :
    MvPolynomial ι K ≃ₐ[K] Nonpositive G K ⧸ J :=
  AlgEquiv.ofBijective (germAlgHom σ)
    ⟨germAlgHom_injective σ (algebraicIndependent_iff_injective_aeval.mp hindependent),
      germAlgHom_surjective σ hgenerate⟩

/-- The quotient by series bounded strictly below zero is a polynomial ring, hence refines
products, when homogeneous generators are algebraically independent and have representatives. -/
theorem hasFourFactorRefinement_of_algebraicIndependent_generators
    (σ : LiftFamily wt xg)
    (hindependent : AlgebraicIndependent K xg)
    (hgenerate : Function.Surjective
      (aeval xg : MvPolynomial ι K →ₐ[K] (ν).AssociatedGraded)) :
    HasFourFactorRefinement (Nonpositive G K ⧸ J) := by
  letI : DecompositionMonoid (Nonpositive G K ⧸ J) :=
    MulEquiv.decompositionMonoid (germAlgEquiv σ hindependent hgenerate).symm.toMulEquiv
  exact hasFourFactorRefinement_of_decompositionMonoid

end HahnSeries.Germ

end
