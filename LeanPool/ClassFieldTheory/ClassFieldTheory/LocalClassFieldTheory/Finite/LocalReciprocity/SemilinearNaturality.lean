/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction
/-!
# Semilinear naturality of finite local reciprocity

The actual finite local Artin map is natural when both the base local field
and the finite abelian extension are replaced by compatible field
equivalences.  The proof realizes the base equivalence as a degree-one
vertical extension and applies the genuine norm--restriction theorem.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory
open scoped ValuativeRel

/-- A base-field equivalence preserves the chosen valuations.  Keeping the
transported `Algebra` structure behind this opaque predicate prevents every
consumer of semilinear Artin naturality from storing a dependent `letI` in
its public theorem type. -/
def SemilinearValuationCompatible
    (K K' : Type)
    [Field K] [ValuativeRel K]
    [Field K'] [ValuativeRel K']
    (eK : K ≃+* K') : Prop :=
  letI : Algebra K K' := eK.toRingHom.toAlgebra
  (ValuativeRel.valuation K).HasExtension
    (ValuativeRel.valuation K')

/-- A certificate that an extension-field equivalence restricts to the
specified base-field equivalence.  Its generic head is cheap to expose in
public APIs even when the concrete algebra towers are large. -/
structure SemilinearBaseCompatible
    (K K' L L' : Type)
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L') : Prop where
  /-- The extension equivalence agrees with the base equivalence. -/
  commutes : ∀ x : K,
    eL (algebraMap K L x) =
      algebraMap K' L' (eK x)

/-- Conjugation of relative Galois groups by compatible equivalences of the
base and extension fields.  Compatibility is semilinear: `eL` restricts to
`eK` on the base field. -/
noncomputable def semilinearGaloisGroupCongr
    (K K' L L' : Type)
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomm : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    Gal(L / K) ≃* Gal(L' / K') := by
  let conjugate (σ : Gal(L / K)) :
      Gal(L' / K') :=
    AlgEquiv.ofRingEquiv
      (f := eL.symm.trans (σ.toRingEquiv.trans eL))
      (fun x => by
        change
          eL (σ (eL.symm (algebraMap K' L' x))) =
            algebraMap K' L' x
        have hpre :
            eL.symm (algebraMap K' L' x) =
              algebraMap K L (eK.symm x) := by
          apply eL.injective
          rw [eL.apply_symm_apply, hcomm, eK.apply_symm_apply]
        rw [hpre, σ.commutes, hcomm, eK.apply_symm_apply])
  let unconjugate (τ : Gal(L' / K')) :
      Gal(L / K) :=
    AlgEquiv.ofRingEquiv
      (f := eL.trans (τ.toRingEquiv.trans eL.symm))
      (fun x => by
        change
          eL.symm (τ (eL (algebraMap K L x))) =
            algebraMap K L x
        rw [hcomm, τ.commutes, ← hcomm,
          eL.symm_apply_apply])
  refine
    { toFun := conjugate
      invFun := unconjugate
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · intro σ
    apply AlgEquiv.ext
    intro x
    simp [conjugate, unconjugate]
  · intro τ
    apply AlgEquiv.ext
    intro x
    simp [conjugate, unconjugate]
  · intro σ τ
    apply AlgEquiv.ext
    intro x
    simp [conjugate, AlgEquiv.mul_apply]

/-- Semilinear conjugation intertwines the two actions through the target
field equivalence. -/
@[simp]
theorem semilinearGaloisGroupCongr_apply_equiv
    (K K' L L' : Type)
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomm : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (σ : Gal(L / K)) (x : L) :
    semilinearGaloisGroupCongr K K' L L' eK eL hcomm σ (eL x) =
      eL (σ x) := by
  change eL (σ (eL.symm (eL x))) = eL (σ x)
  rw [eL.symm_apply_apply]

/-- Evaluate certified semilinear conjugation on an element of the extension
field. -/
theorem SemilinearBaseCompatible.conjugation_apply
    {K K' L L' : Type}
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    {eK : K ≃+* K'} {eL : L ≃+* L'}
    (h : SemilinearBaseCompatible K K' L L' eK eL)
    (sigma : Gal(L / K)) (x : L) :
    semilinearGaloisGroupCongr
        K K' L L' eK eL h.commutes sigma (eL x) =
      eL (sigma x) :=
  semilinearGaloisGroupCongr_apply_equiv
    K K' L L' eK eL h.commutes sigma x

/-- The actual finite abelian local Artin map commutes with simultaneous
semilinear equivalences of the base local field and the target extension.

The valuation-extension condition says that the local-field valuation on
`K'`, pulled back through `eK`, is the valuation on `K`.  It is the genuine
valued-field compatibility needed by norm--restriction, rather than an
assumption of the desired Artin equality. -/
theorem abelianLocalArtinMonoidHom_semilinear_conjugation
    (K K' L L' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomm : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (hExt : SemilinearValuationCompatible K K' eK) :
    (semilinearGaloisGroupCongr K K' L L' eK eL hcomm).toMonoidHom.comp
        (abelianLocalArtinMonoidHom K L) =
      (abelianLocalArtinMonoidHom K' L').comp
        (Units.map eK.toMonoidHom) := by
  let : Algebra K K' := eK.toRingHom.toAlgebra
  change
    (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation K') at hExt
  let : Algebra K L' :=
    ((algebraMap K' L').comp eK.toRingHom).toAlgebra
  let : Algebra L L' := eL.toRingHom.toAlgebra
  let : IsScalarTower K K' L' :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L L' :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (hcomm x).symm)
  let eKAlg : K ≃ₐ[K] K' :=
    { eK with
      commutes' := fun _ => rfl }
  let : FiniteDimensional K K' :=
    FiniteDimensional.of_surjective
      eKAlg.toLinearMap eKAlg.surjective
  let : Algebra.IsSeparable K K' :=
    AlgEquiv.Algebra.isSeparable eKAlg
  let :
      (ValuativeRel.valuation K).HasExtension
        (ValuativeRel.valuation K') :=
    hExt
  let conjugation :=
    semilinearGaloisGroupCongr K K' L L' eK eL hcomm
  let restriction :
      Gal(L' / K') →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  have hrestriction (τ : Gal(L' / K')) :
      restriction τ = conjugation.symm τ := by
    apply AlgEquiv.ext
    intro x
    apply eL.injective
    calc
      eL (restriction τ x) =
          τ (eL x) := by
        exact
          AlgEquiv.restrictNormal_commutes
            ((AlgEquiv.restrictScalarsHom K) τ) L x
      _ = eL (conjugation.symm τ x) := by
        simp [conjugation, semilinearGaloisGroupCongr]
  have hnorm (a : Kˣ) :
      normUnits K K' (Units.map eK.toMonoidHom a) = a := by
    apply Units.ext
    change Algebra.norm K (eK (a : K)) = (a : K)
    have hnorm :=
      normUnits_mapEquiv
        K K K K'
        (RingEquiv.refl K) eK
        (by
          apply RingHom.ext
          intro x
          rfl)
        a
    simpa [normUnits_apply_coe, Units.coe_mapEquiv, Algebra.norm_self] using
      congrArg Units.val hnorm
  have hnaturality :=
    abelianLocalArtinMonoidHom_norm_restriction K K' L L'
  apply MonoidHom.ext
  intro a
  have hpoint :=
    DFunLike.congr_fun hnaturality
      (Units.map eK.toMonoidHom a)
  change
    restriction
        (abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom a)) =
      abelianLocalArtinMonoidHom K L
        (normUnits K K' (Units.map eK.toMonoidHom a)) at hpoint
  rw [hrestriction, hnorm] at hpoint
  change
    conjugation (abelianLocalArtinMonoidHom K L a) =
      abelianLocalArtinMonoidHom K' L'
        (Units.map eK.toMonoidHom a)
  calc
    conjugation (abelianLocalArtinMonoidHom K L a) =
        conjugation
          (conjugation.symm
            (abelianLocalArtinMonoidHom K' L'
              (Units.map eK.toMonoidHom a))) :=
      congrArg conjugation hpoint.symm
    _ =
        abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom a) :=
      conjugation.apply_symm_apply _

/-- Pointwise Galois-automorphism form of semilinear naturality for the
abelian local Artin map.  Concrete consumers should use this opaque generic
boundary instead of specializing `DFunLike.congr_fun` to a large dependent
local-field instance tower. -/
theorem abelianLocalArtinMonoidHom_semilinear_conjugation_apply
    (K K' L L' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomm : ∀ x : K,
      eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (hExt : SemilinearValuationCompatible K K' eK)
    (u : Kˣ) :
    semilinearGaloisGroupCongr K K' L L' eK eL hcomm
        (abelianLocalArtinMonoidHom K L u) =
      abelianLocalArtinMonoidHom K' L'
        (Units.map eK.toMonoidHom u) :=
  DFunLike.congr_fun
    (abelianLocalArtinMonoidHom_semilinear_conjugation
      K K' L L' eK eL hcomm hExt) u

/-- Triviality transports backwards through a semilinear equivalence of local
Artin data.  Keeping the injectivity calculation generic prevents concrete
finite-place instance towers from entering consumer proof terms. -/
theorem abelianLocalArtinMonoidHom_eq_one_of_semilinear
    (K K' L L' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomm : ∀ x : K,
      eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (hExt : SemilinearValuationCompatible K K' eK)
    (u : Kˣ)
    (htrivial :
      abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom u) = 1) :
    abelianLocalArtinMonoidHom K L u = 1 := by
  let conjugation :=
    semilinearGaloisGroupCongr K K' L L' eK eL hcomm
  apply conjugation.injective
  calc
    conjugation (abelianLocalArtinMonoidHom K L u) =
        abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom u) :=
      abelianLocalArtinMonoidHom_semilinear_conjugation_apply
        K K' L L' eK eL hcomm hExt u
    _ = 1 := htrivial
    _ = conjugation 1 := (map_one conjugation).symm

/-- Pointwise form of semilinear naturality for the abelian local Artin map.

This theorem keeps the equality of Galois automorphisms and its dependent
instance tower behind an opaque generic boundary.  Concrete consumers can
transport the action on one element without specializing and then reducing
the full monoid-hom equality. -/
theorem abelianLocalArtinMonoidHom_semilinear_action
    (K K' L L' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomm : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (hExt : SemilinearValuationCompatible K K' eK)
    (u : Kˣ) (z : L) :
    eL (abelianLocalArtinMonoidHom K L u z) =
      abelianLocalArtinMonoidHom K' L'
        (Units.map eK.toMonoidHom u) (eL z) := by
  have hArtin :=
    DFunLike.congr_fun
      (abelianLocalArtinMonoidHom_semilinear_conjugation
        K K' L L' eK eL hcomm hExt) u
  calc
    eL (abelianLocalArtinMonoidHom K L u z) =
        semilinearGaloisGroupCongr
          K K' L L' eK eL hcomm
          (abelianLocalArtinMonoidHom K L u) (eL z) :=
      (semilinearGaloisGroupCongr_apply_equiv
        K K' L L' eK eL hcomm
        (abelianLocalArtinMonoidHom K L u) z).symm
    _ = abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom u) (eL z) :=
      congrArg (fun sigma : Gal(L' / K') => sigma (eL z)) hArtin

end LocalClassFieldTheory
