/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.FiniteMathlibTopologyComparison
public import Mathlib.Topology.Algebra.Group.Quotient
/-!
# Continuity of the comparison with Mathlib's idèle class group

The algebraic equivalence from the restricted-product idèle class group to
Mathlib's adele-unit quotient is continuous. This is the quotient descent of
the continuous map on idèles.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-- The idèle-class comparison is continuous in the forward direction. -/
theorem continuous_ideleClassGroupEquivMathlib :
    Continuous (ideleClassGroupEquivMathlib K) := by
  apply (QuotientGroup.isQuotientMap_mk (principalSubgroup K)).continuous_iff.mpr
  have h : Continuous (fun a : IdeleGroup K =>
      QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)
        (equivAdeleRingUnits a)) :=
    QuotientGroup.continuous_mk.comp (continuous_equivAdeleRingUnits K)
  exact h.congr (fun _ => rfl)

/-- The restricted-product and adele-unit presentations of the idèle class
group are canonically isomorphic as topological groups. -/
noncomputable def ideleClassGroupContinuousMulEquivMathlib :
    IdeleClassGroup K ≃ₜ* NumberField.IdeleClassGroup (𝓞 K) K := by
  refine
    { toMulEquiv := ideleClassGroupEquivMathlib K
      continuous_toFun := continuous_ideleClassGroupEquivMathlib K
      continuous_invFun := ?_ }
  apply (QuotientGroup.isQuotientMap_mk
    (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)).continuous_iff.mpr
  have h : Continuous (fun a : NumberField.IdeleGroup (𝓞 K) K =>
      QuotientGroup.mk' (principalSubgroup K)
        ((equivAdeleRingUnitsContinuousMulEquiv K).symm a)) :=
    QuotientGroup.continuous_mk.comp
      (equivAdeleRingUnitsContinuousMulEquiv K).symm.continuous
  exact h.congr (fun _ => rfl)

end IdeleGroup
