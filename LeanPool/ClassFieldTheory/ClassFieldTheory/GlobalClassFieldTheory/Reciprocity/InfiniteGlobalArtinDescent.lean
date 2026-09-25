/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinCompatibility
/-!
# Descent of the infinite global Artin homomorphism

The finite global Artin product formula at every finite Galois intermediate
field shows that the infinite global Artin homomorphism kills principal ideles.
This file descends that homomorphism to the idele class group and retains its
ordinary quotient topology.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K Ω : Type}
    [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]

open scoped Classical in
private theorem
    continuousMulEquivToLimit_infiniteGlobalArtinMonoidHom_apply
    (a : IdeleGroup K) :
    InfiniteGalois.continuousMulEquivToLimit K Ω
        (infiniteGlobalArtinMonoidHom K Ω a) =
      infiniteGlobalArtinToLimit K Ω a := by
  exact
    (InfiniteGalois.continuousMulEquivToLimit K Ω).apply_symm_apply _

open scoped Classical in
/-- The infinite global Artin homomorphism is trivial on every principal
idele. -/
@[simp]
theorem infiniteGlobalArtinMonoidHom_principalIdele
    (x : Kˣ) :
    infiniteGlobalArtinMonoidHom K Ω
        (IdeleGroup.principalIdele K x) =
      1 := by
  let (E : FiniteGaloisIntermediateField K Ω) : NumberField E :=
    NumberField.of_module_finite K E
  let (E : FiniteGaloisIntermediateField K Ω) : IsAbelianGalois K E :=
    IsAbelianGalois.of_algHom E.toIntermediateField.val
  apply (InfiniteGalois.continuousMulEquivToLimit K Ω).injective
  rw [
    continuousMulEquivToLimit_infiniteGlobalArtinMonoidHom_apply,
    map_one]
  apply Subtype.ext
  funext E
  exact
    globalArtinMonoidHom_principalIdele
      (K := K) (L := E.unop) x

open scoped Classical in
/-- The infinite global Artin homomorphism descended through the subgroup of
principal ideles. -/
noncomputable def infiniteGlobalIdeleClassArtinMonoidHom :
    IdeleClassGroup K →* (Ω ≃ₐ[K] Ω) :=
  QuotientGroup.lift
    (IdeleGroup.principalSubgroup K)
    (infiniteGlobalArtinMonoidHom K Ω).toMonoidHom
    (by
      intro a ha
      change infiniteGlobalArtinMonoidHom K Ω a = 1
      rcases ha with ⟨x, rfl⟩
      exact
        infiniteGlobalArtinMonoidHom_principalIdele
          (K := K) (Ω := Ω) x)

open scoped Classical in
/-- Evaluation of the descended infinite global Artin homomorphism on an idele
representative recovers the original infinite Artin homomorphism. -/
theorem infiniteGlobalIdeleClassArtinMonoidHom_mk
    (a : IdeleGroup K) :
    infiniteGlobalIdeleClassArtinMonoidHom
        (K := K) (Ω := Ω)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      infiniteGlobalArtinMonoidHom K Ω a := by
  rw [infiniteGlobalIdeleClassArtinMonoidHom]
  exact QuotientGroup.lift_mk _ _ _

open scoped Classical in
private theorem infiniteGlobalIdeleClassArtinMonoidHom_continuous :
    Continuous
      (infiniteGlobalIdeleClassArtinMonoidHom
        (K := K) (Ω := Ω)) := by
  refine
    (QuotientGroup.isQuotientMap_mk
      (G := IdeleGroup K)
      (N := IdeleGroup.principalSubgroup K)).continuous_iff.2 ?_
  convert
    (infiniteGlobalArtinMonoidHom K Ω).continuous_toFun using 1
  funext a
  exact
    infiniteGlobalIdeleClassArtinMonoidHom_mk
      (K := K) (Ω := Ω) a

open scoped Classical in
/-- The descended infinite global Artin homomorphism, retaining the ordinary
quotient topology on the idele class group. -/
noncomputable def infiniteGlobalIdeleClassArtinContinuousMonoidHom :
    IdeleClassGroup K →ₜ* (Ω ≃ₐ[K] Ω) where
  toMonoidHom :=
    infiniteGlobalIdeleClassArtinMonoidHom
      (K := K) (Ω := Ω)
  continuous_toFun :=
    infiniteGlobalIdeleClassArtinMonoidHom_continuous
      (K := K) (Ω := Ω)

open scoped Classical in
/-- The descended infinite global Artin homomorphism has dense image in the
Krull topology. -/
theorem infiniteGlobalIdeleClassArtinContinuousMonoidHom_denseRange :
    DenseRange
      (infiniteGlobalIdeleClassArtinContinuousMonoidHom
        (K := K) (Ω := Ω)) := by
  refine
    (infiniteGlobalArtinMonoidHom_denseRange K Ω).mono ?_
  rintro σ ⟨a, rfl⟩
  refine
    ⟨QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K) a, ?_⟩
  exact
    infiniteGlobalIdeleClassArtinMonoidHom_mk
      (K := K) (Ω := Ω) a

end Reciprocity
end GlobalClassFieldTheory
