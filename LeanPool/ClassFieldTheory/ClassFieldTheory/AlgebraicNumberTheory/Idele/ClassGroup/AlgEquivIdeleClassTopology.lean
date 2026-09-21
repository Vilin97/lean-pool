/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivAdeleTopology
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.FiniteMathlibTopologyComparison
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Units
/-!
# Idèle and idèle-class transport under a number-field equivalence

The continuous adele-ring transport induces continuous transport of units
and then of the quotient by principal idèles. These topological equivalences
have the previously defined algebraic maps as their underlying maps.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Algebra ℚ K]
  [Field M] [NumberField M] [Algebra ℚ M]

/-- Reversing the field equivalence reverses the adelic transport. -/
theorem adeleCongr_symm (e : K ≃ₐ[ℚ] M) :
    (adeleCongr e).symm = adeleCongr e.symm := by
  rfl

/-- Adelic field-isomorphism transport is a topological group equivalence. -/
noncomputable def adeleCongrContinuousMulEquiv (e : K ≃ₐ[ℚ] M) :
    NumberField.AdeleRing (𝓞 K) K ≃ₜ*
      NumberField.AdeleRing (𝓞 M) M := by
  refine
    { toMulEquiv := (adeleCongr e).toMulEquiv
      continuous_toFun := continuous_adeleCongr e
      continuous_invFun := ?_ }
  change Continuous ((adeleCongr e).symm)
  rw [adeleCongr_symm]
  exact continuous_adeleCongr e.symm

/-- The existing idèle transport is an equivalence of topological groups. -/
noncomputable def ideleCongrContinuousMulEquiv (e : K ≃ₐ[ℚ] M) :
    IdeleGroup K ≃ₜ* IdeleGroup M :=
  (IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv K).trans
    ((Units.mapContinuousMulEquiv (adeleCongrContinuousMulEquiv e)).trans
      (IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv M).symm)

/-- The topological and algebraic transports of idèles agree. -/
@[simp]
theorem ideleCongrContinuousMulEquiv_apply
    (e : K ≃ₐ[ℚ] M) (a : IdeleGroup K) :
    ideleCongrContinuousMulEquiv e a = ideleCongr e a :=
  rfl

/-- The existing idèle-class transport is an equivalence of topological
groups. -/
noncomputable def ideleClassCongrContinuousMulEquiv
    (e : K ≃ₐ[ℚ] M) :
    IdeleClassGroup K ≃ₜ* IdeleClassGroup M := by
  refine
    { toMulEquiv := ideleClassCongr e
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply (QuotientGroup.isQuotientMap_mk
      (IdeleGroup.principalSubgroup K)).continuous_iff.mpr
    have h : Continuous (fun a : IdeleGroup K =>
        QuotientGroup.mk' (IdeleGroup.principalSubgroup M)
          (ideleCongr e a)) :=
      QuotientGroup.continuous_mk.comp
        (ideleCongrContinuousMulEquiv e).continuous
    exact h.congr (fun a => (ideleClassCongr_mk e a).symm)
  · apply (QuotientGroup.isQuotientMap_mk
      (IdeleGroup.principalSubgroup M)).continuous_iff.mpr
    have h : Continuous (fun a : IdeleGroup M =>
        QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
          ((ideleCongr e).symm a)) :=
      QuotientGroup.continuous_mk.comp
        (ideleCongrContinuousMulEquiv e).symm.continuous
    exact h.congr (fun _ => rfl)

/-- The topological and algebraic transports of idèle classes agree. -/
@[simp]
theorem ideleClassCongrContinuousMulEquiv_apply
    (e : K ≃ₐ[ℚ] M) (a : IdeleClassGroup K) :
    ideleClassCongrContinuousMulEquiv e a = ideleClassCongr e a :=
  rfl

end
