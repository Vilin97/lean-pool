/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupport
public import Mathlib.Algebra.GCDMonoid.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportGCDProof
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportNormalization
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportUnit

/-!
# A normalized GCD structure on finite-support nonpositive series

LM24, Fact 2.5.2 shows that the finite-support nonpositive Hahn-series ring is a GCD domain and
that its units are precisely the nonzero constants. The normalization here represents the zero
associate class by zero and every nonzero class by the unique associate whose coefficient at its
greatest support exponent is one. This turns the existing pairwise GCD theorem into a
`NormalizedGCDMonoid` structure.
-/

open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
variable [Field K]

private theorem normalizedAssociateRepresentative_one :
    normalizedAssociateRepresentative
        (1 : Associates (finiteSupportSubring (G := G) (K := K))) = 1 := by
  apply normalizedAssociateRepresentative_eq_of_is isUnit_finiteSupport_iff_exists_scalar
  rw [isNormalizedAssociateRepresentative_iff]
  exact Or.inr ⟨one_ne_zero, by simp, isMonicFiniteSupport_one⟩

private theorem normalizedAssociateRepresentative_mul
    (a b : Associates (finiteSupportSubring (G := G) (K := K))) :
    normalizedAssociateRepresentative (a * b) =
      normalizedAssociateRepresentative a * normalizedAssociateRepresentative b := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hb : b = 0
  · subst b
    simp
  apply normalizedAssociateRepresentative_eq_of_is isUnit_finiteSupport_iff_exists_scalar
  rw [isNormalizedAssociateRepresentative_iff]
  refine Or.inr ⟨mul_ne_zero ha hb, ?_, ?_⟩
  · rw [← Associates.mk_mul_mk, normalizedAssociateRepresentative_mk,
      normalizedAssociateRepresentative_mk]
  · exact (normalizedAssociateRepresentative_isMonic_of_ne_zero ha).mul
      (normalizedAssociateRepresentative_isMonic_of_ne_zero hb)

private noncomputable def normalizedAssociateRepresentativeMonoidHom :
    Associates (finiteSupportSubring (G := G) (K := K)) →*
      finiteSupportSubring (G := G) (K := K) where
  toFun := normalizedAssociateRepresentative
  map_one' := normalizedAssociateRepresentative_one
  map_mul' := normalizedAssociateRepresentative_mul

@[implicit_reducible]
private noncomputable def finiteSupportNormalizationMonoid :
    NormalizationMonoid (finiteSupportSubring (G := G) (K := K)) := by
  classical
  exact normalizationMonoidOfMonoidHomRightInverse normalizedAssociateRepresentativeMonoidHom
    normalizedAssociateRepresentative_mk

/-- The nonpositive finite-support Hahn-series ring over a field is a normalized GCD domain. -/
theorem nonemptyNormalizedGCDMonoid_finiteSupport :
    Nonempty (NormalizedGCDMonoid (finiteSupportSubring (G := G) (K := K))) := by
  classical
  letI : NormalizationMonoid (finiteSupportSubring (G := G) (K := K)) :=
    finiteSupportNormalizationMonoid
  exact ⟨normalizedGCDMonoidOfExistsGCD finiteSupport_pairwise_gcd_exists⟩

end HahnSeries.Nonpositive
