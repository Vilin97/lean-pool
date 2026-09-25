/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteLocalFamily
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.OnePlaceNormKernel
/-!
# The local--global norm-symbol bridge

This file isolates the exact quotient calculation used by the Hilbert-symbol
product formula.  The one-place embedding sends the chosen local norm group
directly into the ordinary idele-class norm group, so it descends without an
intermediate raw-idele quotient.  The resulting character identity gives the
finite-support and
principal-idèle product identities for every character of that target.
-/

@[expose] public section

open scoped NumberField BigOperators
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped Classical in
private theorem productFormulaIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] productFormulaIdeleClassGroupIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

open scoped Classical in
/-- The one-place embedding, descended directly from the chosen local norm
quotient to the ordinary idele-class norm quotient. -/
noncomputable def finitePlaceNormQuotientToGlobalClass
    (v : HeightOneSpectrum (𝓞 K)) :
    ChosenFinitePlaceNormQuotient
      (K := K) (L := L) v →*
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range :=
  QuotientGroup.lift
    (chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v)
    ((globalNormClassFromIdele K L).comp
      (finitePlaceIdele v))
    (by
      intro x hx
      have hnorm :
          finitePlaceIdele v x ∈
            ideleNormSubgroup (K := K) (L := L) :=
        (finitePlaceIdele_mem_ideleNormSubgroup_iff_chosenLocalNorm
          (K := K) (L := L) v x).2 hx
      obtain ⟨z, hz⟩ := hnorm
      change
        QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (finitePlaceIdele v x)) = 1
      apply (QuotientGroup.eq_one_iff _).2
      refine
        ⟨QuotientGroup.mk'
            (IdeleGroup.principalSubgroup L)
            (relativeIdeleBaseChangeMulEquiv
              (K := K) (L := L) z), ?_⟩
      rw [_root_.ideleClassNorm_mk,
        IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv,
        hz])

open scoped Classical in
/-- Exact local--global compatibility on representatives. -/
@[simp]
theorem finitePlaceNormQuotientToGlobalClass_localClass
    (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) :
    finitePlaceNormQuotientToGlobalClass
        (K := K) (L := L) v
        (finitePlaceTensorNormClass
          (K := K) (L := L) v a) =
      globalNormClassFromIdele K L
        (finitePlaceIdele v a) := by
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
open scoped Classical in
/-- A character of the global class norm quotient, restricted to the
one-place class at `v`. -/
noncomputable def finitePlaceGlobalSymbol
    {A : Type*} [CommGroup A]
    (chi :
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) →* A)
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* A :=
  chi.comp
    ((globalNormClassFromIdele K L).comp
      (finitePlaceIdele v))

open scoped Classical in
/-- The one-place global symbol is the character of the transported local norm
class. -/
@[simp]
theorem finitePlaceGlobalSymbol_eq_localNormClass
    {A : Type*} [CommGroup A]
    (chi :
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) →* A)
    (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) :
    finitePlaceGlobalSymbol (K := K) (L := L) chi v a =
      chi
        (finitePlaceNormQuotientToGlobalClass
          (K := K) (L := L) v
          (finitePlaceTensorNormClass
            (K := K) (L := L) v a)) := by
  rw [finitePlaceGlobalSymbol, MonoidHom.comp_apply,
    MonoidHom.comp_apply,
    finitePlaceNormQuotientToGlobalClass_localClass]

omit [FiniteDimensional K L] [IsGalois K L] in
open scoped Classical in
/-- Finite-support form of the product formula for a global norm-quotient
character. -/
theorem finitePlaceGlobalSymbol_finiteLocalFamily
    {A : Type*} [CommGroup A]
    (chi :
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) →* A)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ) :
    ∏ v : ↥S,
        finitePlaceGlobalSymbol (K := K) (L := L) chi v.1 (a v) =
      chi
        (globalNormClassFromIdele K L
          (IdeleGroup.ideleOfFiniteLocalFamily S a)) := by
  let : CommGroup (IdeleClassGroup K) :=
    QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup K)
  rw [globalNormClass_finiteLocalFamily]
  rw [map_prod]
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
open scoped Classical in
/-- A global norm-quotient character is trivial on a principal idèle. -/
theorem globalNormQuotientCharacter_principal
    {A : Type*} [CommGroup A]
    (chi :
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) →* A)
    (x : Kˣ) :
  chi
        (globalNormClassFromIdele K L
          (IdeleGroup.principalIdele K x)) = 1 := by
  rw [globalNormClassFromIdele_principalIdele, map_one]

omit [FiniteDimensional K L] [IsGalois K L] in
open scoped Classical in
/-- Exact bridge from a finite local representative of a principal global
norm class to the product-one identity.  The premise is a concrete equality
in `C_K / N C_L`, not a product-formula assumption. -/
theorem finitePlaceGlobalSymbol_product_eq_one_of_eq_principal
    {A : Type*} [CommGroup A]
    (chi :
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) →* A)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ)
    (x : Kˣ)
    (hprincipal :
      globalNormClassFromIdele K L
          (IdeleGroup.ideleOfFiniteLocalFamily S a) =
        globalNormClassFromIdele K L
          (IdeleGroup.principalIdele K x)) :
    ∏ v : ↥S,
        finitePlaceGlobalSymbol (K := K) (L := L) chi v.1 (a v) = 1 := by
  rw [finitePlaceGlobalSymbol_finiteLocalFamily]
  rw [hprincipal]
  exact globalNormQuotientCharacter_principal chi x

end Reciprocity
end GlobalClassFieldTheory
