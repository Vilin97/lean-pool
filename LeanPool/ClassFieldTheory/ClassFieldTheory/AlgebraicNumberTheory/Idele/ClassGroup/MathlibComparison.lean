/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import Mathlib.NumberTheory.NumberField.AdeleRing
/-!
# Comparison with Mathlib's idèle class group

The restricted-product idèle group and Mathlib's adele-unit idèle group are
already multiplicatively equivalent. The principal subgroups correspond,
so the equivalence descends to idèle classes. The one-place map comparison
needed for the public local--global reciprocity theorem is recorded below.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-- The algebraic idèle equivalence carries each principal idèle to Mathlib's
diagonal idèle. -/
theorem equivAdeleRingUnits_principalIdele (x : Kˣ) :
    equivAdeleRingUnits (principalIdele K x) =
      NumberField.IdeleGroup.unitEmbedding (𝓞 K) K x := by
  change equivAdeleRingUnits
    ((equivAdeleRingUnits (K := K)).symm
      (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K x)) = _
  exact (equivAdeleRingUnits (K := K)).apply_symm_apply _

/-- The induced multiplicative equivalence of idèle class groups. -/
def ideleClassGroupEquivMathlib :
    IdeleClassGroup K ≃* NumberField.IdeleClassGroup (𝓞 K) K := by
  let e := equivAdeleRingUnits (K := K)
  let N := principalSubgroup K
  let M := NumberField.IdeleGroup.principalSubgroup (𝓞 K) K
  have hforward : N ≤ M.comap e.toMonoidHom := by
    rintro a ⟨x, rfl⟩
    exact ⟨x, equivAdeleRingUnits_principalIdele K x⟩
  have hbackward : M ≤ N.comap e.symm.toMonoidHom := by
    rintro a ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    apply e.injective
    rw [equivAdeleRingUnits_principalIdele K x]
    exact (e.apply_symm_apply _).symm
  let f : IdeleClassGroup K →* NumberField.IdeleClassGroup (𝓞 K) K :=
    QuotientGroup.map N M e.toMonoidHom hforward
  let g : NumberField.IdeleClassGroup (𝓞 K) K →* IdeleClassGroup K :=
    QuotientGroup.map M N e.symm.toMonoidHom hbackward
  exact
    { toFun := f
      invFun := g
      left_inv := by
        intro a
        refine QuotientGroup.induction_on a (fun x => ?_)
        change QuotientGroup.mk' N (e.symm (e x)) = QuotientGroup.mk' N x
        rw [e.symm_apply_apply]
      right_inv := by
        intro a
        refine QuotientGroup.induction_on a (fun x => ?_)
        change QuotientGroup.mk' M (e (e.symm x)) = QuotientGroup.mk' M x
        rw [e.apply_symm_apply]
      map_mul' := f.map_mul }

/-- The algebraic idèle comparison carries a one-place idèle to Mathlib's
one-place adele-unit idèle. -/
theorem equivAdeleRingUnits_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    equivAdeleRingUnits (finitePlaceIdele v x) =
      NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v x := by
  classical
  apply Units.ext
  apply Prod.ext
  · rfl
  · apply RestrictedProduct.ext
    intro w
    change ((finitePlaceIdele v x).2 w : w.adicCompletion K) =
      (RestrictedProduct.mulSingle
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K)
        v (x : v.adicCompletion K)) w
    by_cases hw : w = v
    · subst w
      rw [RestrictedProduct.mulSingle_eq_same]
      exact congrArg (fun u : (v.adicCompletion K)ˣ =>
        (u : v.adicCompletion K))
        (finitePlaceIdele_finiteComponent_same v x)
    · rw [RestrictedProduct.mulSingle_eq_of_ne
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K)
        (x : v.adicCompletion K) hw]
      have h := finitePlaceIdele_finiteComponent_of_ne v w x hw
      exact congrArg (fun u : (w.adicCompletion K)ˣ =>
        (u : w.adicCompletion K)) h

/-- The class-group comparison respects the one-place idèle-class maps. -/
theorem ideleClassGroupEquivMathlib_finitePlaceIdeleClass
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ideleClassGroupEquivMathlib K (finitePlaceIdeleClass v x) =
      NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x := by
  change QuotientGroup.mk'
      (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)
      (equivAdeleRingUnits (finitePlaceIdele v x)) =
    QuotientGroup.mk'
      (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)
      (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v x)
  rw [equivAdeleRingUnits_finitePlaceIdele K v x]

end IdeleGroup
