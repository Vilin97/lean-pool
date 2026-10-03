/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.NormQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
/-!
# Finite local families of ideles

A finite family of local elements, extended by `1`, is the product of its
one-place ideles.  Applying the global norm-quotient map gives the finite
product identity.  The quotient map itself factors through idele classes
and therefore kills principal ideles.
-/

@[expose] public section

open scoped NumberField BigOperators
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- A finite local family is the product of its one-place ideles. -/
theorem prod_finitePlaceIdele_eq_ideleOfFiniteLocalFamily
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ) :
    (∏ v : ↥S, finitePlaceIdele v.1 (a v)) =
      IdeleGroup.ideleOfFiniteLocalFamily S a := by
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change
      IdeleGroup.infiniteComponent w
          (∏ v : ↥S, finitePlaceIdele v.1 (a v)) =
        IdeleGroup.infiniteComponent w
          (IdeleGroup.ideleOfFiniteLocalFamily S a)
    rw [map_prod]
    have hfactor :
        ∀ v : ↥S,
          IdeleGroup.infiniteComponent w
              (finitePlaceIdele v.1 (a v)) = 1 := by
      intro v
      exact finitePlaceIdele_infiniteComponent v.1 w (a v)
    have hright :
        IdeleGroup.infiniteComponent w
            (IdeleGroup.ideleOfFiniteLocalFamily S a) = 1 :=
      rfl
    rw [hright]
    simp_rw [hfactor]
    simp
  · apply RestrictedProduct.ext
    intro w
    change
      IdeleGroup.finiteComponent w
          (∏ v : ↥S, finitePlaceIdele v.1 (a v)) =
        (IdeleGroup.ideleOfFiniteLocalFamily S a).2 w
    rw [map_prod]
    by_cases hw : w ∈ S
    · let vw : ↥S := ⟨w, hw⟩
      rw [Finset.prod_eq_single vw]
      · calc
          IdeleGroup.finiteComponent w
              (finitePlaceIdele vw.1 (a vw)) =
              a vw := by
                simpa [vw] using
                  finitePlaceIdele_finiteComponent_same
                    w (a vw)
          _ = (IdeleGroup.ideleOfFiniteLocalFamily S a).2 w :=
            (IdeleGroup.finiteIdeleOfFinset_apply_mem
              S a vw).symm
      · intro b _ hbw
        apply finitePlaceIdele_finiteComponent_of_ne
        intro h
        apply hbw
        apply Subtype.ext
        exact h.symm
      · intro hvw
        exact (hvw (Finset.mem_univ vw)).elim
    · calc
        ∏ v : ↥S,
            IdeleGroup.finiteComponent w
              (finitePlaceIdele v.1 (a v)) =
            1 := by
              apply Finset.prod_eq_one
              intro v _
              apply finitePlaceIdele_finiteComponent_of_ne
              intro h
              apply hw
              rw [h]
              exact v.2
        _ = (IdeleGroup.ideleOfFiniteLocalFamily S a).2 w :=
          (IdeleGroup.finiteIdeleOfFinset_apply_notMem
            S a w hw).symm

open scoped Classical in
/-- Applying any multiplicative global symbol to a finite local family
gives the product of the one-place symbols. -/
theorem map_ideleOfFiniteLocalFamily_eq_prod_local
    {A : Type*} [CommGroup A]
    (f : IdeleGroup K →* A)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ) :
    f (IdeleGroup.ideleOfFiniteLocalFamily S a) =
      ∏ v : ↥S, f (finitePlaceIdele v.1 (a v)) := by
  rw [← map_prod,
    prod_finitePlaceIdele_eq_ideleOfFiniteLocalFamily]

section NormQuotient

variable
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

open scoped Classical in
local instance finiteLocalFamilyIdeleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] finiteLocalFamilyIdeleClassGroupIsMulCommutative

open scoped Classical in
/-- The idele class group carries its canonical commutative group structure. -/
local instance finiteLocalFamilyIdeleClassGroupCommGroup :
    CommGroup (IdeleClassGroup K) :=
  open scoped IsMulCommutative in
  inferInstance

attribute [local instance] finiteLocalFamilyIdeleClassGroupCommGroup

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The finite-support product formula for the global
norm-quotient symbol. -/
theorem globalNormClass_finiteLocalFamily
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ) :
    globalNormClassFromIdele K L
        (IdeleGroup.ideleOfFiniteLocalFamily S a) =
      ∏ v : ↥S,
        globalNormClassFromIdele K L
          (finitePlaceIdele v.1 (a v)) :=
  map_ideleOfFiniteLocalFamily_eq_prod_local
    (globalNormClassFromIdele K L) S a

end NormQuotient

end Reciprocity
end GlobalClassFieldTheory
