/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicAuxiliaryField
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.OnePlaceNormKernel
/-!
# Factorization of the global Artin map through local Artin maps

This module completes the auxiliary-field argument, factors the global
norm-residue map through each local Artin quotient, and proves the
finite-place local-global compatibility theorem.
-/

open scoped IsMulCommutative NumberField
open NumberField
open AlgebraicNumberTheory.Valuations
open HilbertRamification

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open CyclicCohomology
open KummerTheory

attribute [local instance]
  finitePadicAuxiliaryExtensionQuotientIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The finite quotient coordinate remains primary after transport to
the relative Galois group. -/
private theorem numberFieldTowerFiniteQuotientCoordinate_mem_primary
    (p : Nat.Primes) (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (σ' : Gal(L / K))
    (hτσ :
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) = σ')
    (hprimary :
      σ' ∈ CommGroup.primaryComponent (Gal(L / K)) p.1) :
    numberFieldTowerFiniteQuotientCoordinate
        (K := K) (L := L) τ ∈
      CommGroup.primaryComponent
        ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
          extensionSubgroup
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
        p.1 := by
  obtain ⟨m, hm⟩ := hprimary
  refine ⟨m, ?_⟩
  apply (numberFieldTowerExtensionQuotientEquivGaloisGroup K L).injective
  calc
    (numberFieldTowerExtensionQuotientEquivGaloisGroup K L)
        (numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ^ (p.1 ^ m)) =
      (numberFieldTowerExtensionQuotientEquivGaloisGroup K L
        (numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ)) ^ (p.1 ^ m) := map_pow _ _ _
    _ = σ' ^ (p.1 ^ m) :=
      congrArg (fun g => g ^ (p.1 ^ m)) hτσ
    _ = 1 := hm
    _ = numberFieldTowerExtensionQuotientEquivGaloisGroup K L 1 :=
      (map_one _).symm

/-- The cyclotomic auxiliary-field construction supplies a local
representative on which the local and global Artin values agree. -/
private theorem exists_finitePlacePrimary_localGlobalRepresentative
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1)
    (hgenerate :
      Subgroup.closure
          ({σ.1} : Set (Gal(L / K))) =
        ⊤)
    (hprimary :
      σ.1 ∈
        CommGroup.primaryComponent
          (Gal(L / K)) p.1) :
    ∃ z : (v.adicCompletion K)ˣ,
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v z = σ.1 ∧
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) = σ.1 := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseScalarTower K L
  let := numberFieldTowerExtensionSubgroup_normal K L
  obtain
      ⟨τ, hτσ, hτdecomposition, hτdegree,
        _hfinite, _hbase, _hintersection, _hcontainment,
        n, hn, hdegree⟩ :=
    exists_finitePlacePrimaryCyclotomicAuxiliaryFixedField
      (K := K) (L := L) v p σ hgenerate hprimary
  have hprimaryQuotient :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1 :=
    numberFieldTowerFiniteQuotientCoordinate_mem_primary
      (K := K) (L := L) p τ σ.1 hτσ hprimary
  let data :=
    numberFieldTowerFinitePadicAuxiliaryLocalGlobalRepresentative
      (K := K) (L := L) v p τ hτdegree hτdecomposition
      n hn hdegree hprimaryQuotient
  exact ⟨data.1, data.2.1.trans hτσ, data.2.2.trans hτσ⟩

omit [NumberField L] in
/-- Triviality of the actual chosen finite-place Artin symbol is
equivalent to membership in the actual chosen local norm subgroup. -/
@[simp]
theorem chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x = 1 ↔
      x ∈ chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  change
    x ∈ (chosenFinitePlaceArtinMonoidHom
      (K := K) (L := L) v).ker ↔ _
  rw [chosenFinitePlaceArtinMonoidHom_ker
    (K := K) (L := L) v]

/-- A finite-place element killed by the actual local Artin
homomorphism is also killed by the global norm-residue homomorphism
after insertion as a one-place idele class. -/
theorem globalNormResidueMonoidHom_finitePlaceIdeleClass_eq_one_of_localArtin_eq_one
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (hx :
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x = 1) :
    globalNormResidueMonoidHom K L
        (IdeleGroup.finitePlaceIdeleClass v x) = 1 := by
  rw [globalNormResidueMonoidHom_eq_one_iff]
  exact
    finitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_chosenLocalNorm
      (K := K) (L := L) v x
      ((chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm
        (K := K) (L := L) v x).1 hx)

/-- The chosen local norm subgroup lies in the kernel of the global
norm-residue homomorphism restricted to the one-place finite idele
class map. -/
theorem chosenFinitePlaceLocalNormSubgroup_le_globalNormResidueKernel
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v ≤
      ((globalNormResidueMonoidHom K L).comp
        (IdeleGroup.finitePlaceIdeleClass v)).ker := by
  intro x hx
  exact
    globalNormResidueMonoidHom_finitePlaceIdeleClass_eq_one_of_localArtin_eq_one
      (K := K) (L := L) v x
      ((chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm
        (K := K) (L := L) v x).2 hx)

/-- The restriction of the global norm-residue homomorphism to one
finite-place idele class depends only on the corresponding local Artin
symbol.

This is the exact quotient step used in the prime-primary reduction:
the already proved inclusion of the local norm subgroup in the global
norm kernel makes the value independent of the chosen local preimage. -/
theorem globalNormResidue_finitePlaceIdeleClass_eq_of_localArtin_eq
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x y : (v.adicCompletion K)ˣ)
    (hxy :
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v x =
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v y) :
    globalNormResidueMonoidHom K L
        (IdeleGroup.finitePlaceIdeleClass v x) =
      globalNormResidueMonoidHom K L
        (IdeleGroup.finitePlaceIdeleClass v y) := by
  let f :
      (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
    (globalNormResidueMonoidHom K L).comp
      (IdeleGroup.finitePlaceIdeleClass v)
  let g :
      (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
    chosenFinitePlaceArtinMonoidHom
      (K := K) (L := L) v
  have hlocal :
      g (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hglobal :
      f (x * y⁻¹) = 1 := by
    exact
      globalNormResidueMonoidHom_finitePlaceIdeleClass_eq_one_of_localArtin_eq_one
        (K := K) (L := L) v (x * y⁻¹) hlocal
  have hquotient :
      f x * (f y)⁻¹ = 1 := by
    simpa only [map_mul, map_inv] using hglobal
  exact mul_inv_eq_one.mp hquotient

/-- Finite-place local--global compatibility for a `p`-primary
decomposition automorphism which generates the whole relative Galois
group.  The auxiliary-field construction is isolated in an opaque
representative lemma, so consumers only see this short quotient step. -/
theorem
    globalNormResidueMonoidHom_finitePlaceIdeleClass_eq_of_primary_generator
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1)
    (hgenerate :
      Subgroup.closure ({σ.1} : Set (Gal(L / K))) = ⊤)
    (hprimary :
      σ.1 ∈ CommGroup.primaryComponent (Gal(L / K)) p.1)
    (x : (v.adicCompletion K)ˣ)
    (hx :
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v x = σ.1) :
    globalNormResidueMonoidHom K L
        (IdeleGroup.finitePlaceIdeleClass v x) = σ.1 := by
  obtain ⟨z, hlocal, hglobal⟩ :=
    exists_finitePlacePrimary_localGlobalRepresentative
      (K := K) (L := L) v p σ hgenerate hprimary
  exact
    (globalNormResidue_finitePlaceIdeleClass_eq_of_localArtin_eq
      (K := K) (L := L) v x z (hx.trans hlocal.symm)).trans hglobal

/-- The global norm-residue symbol at one finite place, factored
through the actual image of the chosen local Artin homomorphism.

The definition uses a preimage only to specify the value.  Its
well-definedness and multiplicativity are consequences of the genuine
one-place norm-kernel theorem above. -/
noncomputable def finitePlaceGlobalNormResidueFactor
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v).range →*
      (L ≃ₐ[K] L) := by
  let g :
      (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
    chosenFinitePlaceArtinMonoidHom
      (K := K) (L := L) v
  let f :
      (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
    (globalNormResidueMonoidHom K L).comp
      (IdeleGroup.finitePlaceIdeleClass v)
  have hker : g.rangeRestrict.ker ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    simpa only [g, f, chosenFinitePlaceArtinMonoidHom_ker] using
      chosenFinitePlaceLocalNormSubgroup_le_globalNormResidueKernel
        (K := K) (L := L) v
  exact
    g.rangeRestrict.liftOfSurjective
      g.rangeRestrict_surjective ⟨f, hker⟩

/-- Factoring and then evaluating the actual local Artin symbol gives
the original one-place global norm-residue value. -/
theorem finitePlaceGlobalNormResidueFactor_comp_rangeRestrict
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (finitePlaceGlobalNormResidueFactor
        (K := K) (L := L) v).comp
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).rangeRestrict =
      (globalNormResidueMonoidHom K L).comp
        (IdeleGroup.finitePlaceIdeleClass v) := by
  let g :
      (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
    chosenFinitePlaceArtinMonoidHom
      (K := K) (L := L) v
  let f :
      (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
    (globalNormResidueMonoidHom K L).comp
      (IdeleGroup.finitePlaceIdeleClass v)
  have hker : g.rangeRestrict.ker ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    simpa only [g, f, chosenFinitePlaceArtinMonoidHom_ker] using
      chosenFinitePlaceLocalNormSubgroup_le_globalNormResidueKernel
        (K := K) (L := L) v
  change
    (g.rangeRestrict.liftOfSurjective
        g.rangeRestrict_surjective ⟨f, hker⟩).comp
        g.rangeRestrict =
      f
  simpa only [MonoidHom.liftOfSurjective] using
    g.rangeRestrict.liftOfRightInverse_comp
      (Function.surjInv g.rangeRestrict_surjective)
      (Function.rightInverse_surjInv
        g.rangeRestrict_surjective)
      ⟨f, hker⟩

/-- Pointwise norm/restriction naturality, with the coercion from the
homomorphism equality normalized once outside the descent construction. -/
private theorem globalNormResidueMonoidHomOfEmbedding_norm_restriction_apply
    (K K' L L' : Type)
    [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Field L] [NumberField L]
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K') :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
          (globalNormResidueMonoidHomOfEmbedding K' L' j c) =
      globalNormResidueMonoidHomOfEmbedding K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))
        (_root_.ideleClassNorm K K' c) := by
  exact
    DFunLike.congr_fun
      (globalNormResidueMonoidHomOfEmbedding_norm_restriction
        (K := K) (L := L) (K' := K') (L' := L') j) c

/-- Norming one upper representative down a finite Galois base-change
transports both its chosen local Artin value and its global norm-residue
value.  All fields and places are explicit here, so no constructed
fixed-field tower occurs in the declaration type. -/
private opaque exists_finitePlaceNormDescent_localGlobalRepresentative
    {M : Type}
    [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    [Algebra M L] [FiniteDimensional M L] [IsAbelianGalois M L]
    [IsScalarTower K M L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (W : IsDedekindDomain.HeightOneSpectrum (𝓞 M))
    (hWbelow : finitePlaceBelow (K := K) W = v)
    (σM : Gal(L / M)) (σG : Gal(L / K))
    (hrestrict :
      ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σM = σG)
    (y : (W.adicCompletion M)ˣ)
    (hy :
      chosenFinitePlaceArtinMonoidHom
          (K := M) (L := L) W y = σM)
    (hglobalM :
      globalNormResidueMonoidHom M L
          (IdeleGroup.finitePlaceIdeleClass W y) = σM) :
    ∃ z : (v.adicCompletion K)ˣ,
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v z = σG ∧
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) = σG := by
  let Wover :
      {W' : IsDedekindDomain.HeightOneSpectrum (𝓞 M) //
        finitePlaceBelow (K := K) W' = v} :=
    ⟨W, hWbelow⟩
  let :
      Algebra (v.adicCompletion K) (W.adicCompletion M) :=
    (finitePlaceAdicCompletionMap K M v Wover).toAlgebra
  let z : (v.adicCompletion K)ˣ :=
    LocalFieldTheory.normUnits
      (v.adicCompletion K) (W.adicCompletion M) y
  have hlocalNorm :
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v z =
        σG := by
    have hnat :=
      DFunLike.congr_fun
        (chosenFinitePlaceArtinMonoidHom_norm_restriction_of_below_eq
          (K := K) (L := L) (K' := M) (L' := L)
          v W hWbelow) y
    change
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.adicCompletion M) y) =
        σG
    calc
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.adicCompletion M) y) =
        ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
            (chosenFinitePlaceArtinMonoidHom
              (K := M) (L := L) W y) := by
                simpa only [MonoidHom.coe_comp, Function.comp_apply]
                  using hnat.symm
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σM :=
        congrArg
          (((AlgEquiv.restrictNormalHom L).comp
            (AlgEquiv.restrictScalarsHom K)) : Gal(L / M) →* Gal(L / K)) hy
      _ = σG := hrestrict
  let j : L →ₐ[ℚ] SeparableClosure ℚ :=
    AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L
  have hjLower :
      j.comp (IsScalarTower.toAlgHom ℚ L L) =
        AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L := by
    apply AlgHom.ext
    intro a
    rfl
  have hnormClass :
      _root_.ideleClassNorm K M
          (IdeleGroup.finitePlaceIdeleClass W y) =
        IdeleGroup.finitePlaceIdeleClass v z := by
    simpa only [Wover, z] using
      (IdeleGroup.ideleClassNorm_finitePlaceIdeleClass_eq_normUnits
        (K := K) (L := M) v Wover y)
  have hglobalNorm :
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) =
        σG := by
    calc
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) =
          globalNormResidueMonoidHom K L
            (_root_.ideleClassNorm K M
              (IdeleGroup.finitePlaceIdeleClass W y)) :=
        congrArg (globalNormResidueMonoidHom K L) hnormClass.symm
      _ = globalNormResidueMonoidHomOfEmbedding K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L))
          (_root_.ideleClassNorm K M
            (IdeleGroup.finitePlaceIdeleClass W y)) := by
        rw [hjLower,
          ← globalNormResidueMonoidHom_eq_ofEmbedding_standard]
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
          (globalNormResidueMonoidHomOfEmbedding M L j
            (IdeleGroup.finitePlaceIdeleClass W y)) := by
        apply Eq.symm
        apply
          globalNormResidueMonoidHomOfEmbedding_norm_restriction_apply
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
          (globalNormResidueMonoidHom M L
            (IdeleGroup.finitePlaceIdeleClass W y)) := by
        exact congrArg
          ((AlgEquiv.restrictNormalHom L).comp
            (AlgEquiv.restrictScalarsHom K))
          (DFunLike.congr_fun
            (globalNormResidueMonoidHom_eq_ofEmbedding_standard
              (K := M) (L := L))
            (IdeleGroup.finitePlaceIdeleClass W y)).symm
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σM :=
        congrArg
          ((AlgEquiv.restrictNormalHom L).comp
            (AlgEquiv.restrictScalarsHom K)) hglobalM
      _ = σG := hrestrict
  exact ⟨z, hlocalNorm, hglobalNorm⟩

/-- A primary generator at an explicit upper place can first be realized
by the auxiliary construction and then normed through an explicit base
change.  This short bridge keeps the auxiliary witness out of the
cyclic-fixed-field construction. -/
private opaque exists_finitePlacePrimaryNormDescent_localGlobalRepresentative
    {M : Type}
    [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    [Algebra M L] [FiniteDimensional M L] [IsAbelianGalois M L]
    [IsScalarTower K M L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (W : IsDedekindDomain.HeightOneSpectrum (𝓞 M))
    (hWbelow : finitePlaceBelow (K := K) W = v)
    (p : Nat.Primes)
    (δM :
      absoluteValueDecompositionGroup M
        (chosenFinitePlaceExtension (L := L) W).1)
    (hgenerate :
      Subgroup.closure ({δM.1} : Set (Gal(L / M))) = ⊤)
    (hprimary :
      δM.1 ∈ CommGroup.primaryComponent (Gal(L / M)) p.1)
    (σG : Gal(L / K))
    (hrestrict :
      ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) δM.1 = σG) :
    ∃ z : (v.adicCompletion K)ˣ,
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v z = σG ∧
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) = σG := by
  obtain ⟨y, hy, hglobalM⟩ :=
    exists_finitePlacePrimary_localGlobalRepresentative
      (K := M) (L := L) W p δM hgenerate hprimary
  exact
    exists_finitePlaceNormDescent_localGlobalRepresentative
      (K := K) (L := L) v W hWbelow
      δM.1 σG hrestrict y hy hglobalM

/-- Cyclic fixed-field descent turns a primary decomposition
automorphism into a lower representative without exposing the constructed
field tower in the declaration type. -/
private opaque exists_finitePlacePrimary_cyclicFixedFieldRepresentative
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (δ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1)
    (hprimary :
      δ.1 ∈ CommGroup.primaryComponent (Gal(L / K)) p.1) :
    ∃ z : (v.adicCompletion K)ˣ,
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v z = δ.1 ∧
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) = δ.1 := by
  let σG : Gal(L / K) := δ.1
  let M := automorphismCyclicFixedField σG
  let : NumberField M := NumberField.of_module_finite K M
  let W := automorphismCyclicFixedPlace v σG
  let σM : Gal(L / M) := automorphismOverCyclicFixedField σG
  have hσMdecomposition :
      σM ∈
        absoluteValueDecompositionGroup M
          (chosenFinitePlaceExtension (L := L) W).1 := by
    exact
      automorphismOverCyclicFixedField_mem_chosenFinitePlaceDecompositionGroup
        (K := K) (L := L) v δ
  let δM :
      absoluteValueDecompositionGroup M
        (chosenFinitePlaceExtension (L := L) W).1 :=
    ⟨σM, hσMdecomposition⟩
  have hσMrestrict : σM.restrictScalars K = σG :=
    automorphismOverCyclicFixedField_restrictScalars σG
  have hσMprimary :
      σM ∈ CommGroup.primaryComponent (Gal(L / M)) p.1 := by
    obtain ⟨n, hn⟩ := hprimary
    have hnG : σG ^ (p.1 ^ n) = 1 := hn
    refine ⟨n, ?_⟩
    apply AlgEquiv.restrictScalars_injective K
    change
      (AlgEquiv.restrictScalarsHom K) (σM ^ (p.1 ^ n)) =
        (AlgEquiv.restrictScalarsHom K) (1 : Gal(L / M))
    rw [
      map_pow,
      AlgEquiv.restrictScalarsHom_apply,
      hσMrestrict,
      hnG,
      map_one
    ]
  have hWbelow : finitePlaceBelow (K := K) W = v :=
    finitePlaceBelow_automorphismCyclicFixedPlace
      (K := K) (L := L) v σG
  have hrestrictσM :
      ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σM =
        σG := by
    simpa only [
      MonoidHom.coe_comp,
      Function.comp_apply,
      AlgEquiv.restrictNormalHom_id,
      MonoidHom.id_apply,
      AlgEquiv.restrictScalarsHom_apply
    ] using hσMrestrict
  exact
    exists_finitePlacePrimaryNormDescent_localGlobalRepresentative
      (K := K) (L := L) v W hWbelow p δM
      (automorphismOverCyclicFixedField_generates σG)
      hσMprimary σG hrestrictσM

/-- On every primary component of the actual decomposition-group
image, the one-place global norm-residue factor is the tautological
inclusion.  An arbitrary primary element is reduced to the cyclic
extension cut out by that element, where the auxiliary-field theorem
above applies to its genuine generator. -/
theorem finitePlaceGlobalNormResidueFactor_eq_subtype_on_primary
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (p : ℕ) (hp : Fact p.Prime)
    (σ :
      CommGroup.primaryComponent
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).range p) :
    finitePlaceGlobalNormResidueFactor
        (K := K) (L := L) v σ =
      (σ :
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).range) := by
  let σG : Gal(L / K) :=
    (σ :
      (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v).range)
  have hσdecomposition :
      σG ∈
        absoluteValueDecompositionGroup K
          (chosenFinitePlaceExtension (L := L) v).1 := by
    change σG ∈ finitePlaceDecompositionGroup
      (K := K) (L := L) v
    rw [
      ← chosenFinitePlaceArtinMonoidHom_range
        (K := K) (L := L) v]
    exact
      (σ :
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).range).property
  let δ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1 :=
    ⟨σG, hσdecomposition⟩
  have hσprimary :
      σG ∈ CommGroup.primaryComponent (Gal(L / K)) p := by
    obtain ⟨n, hn⟩ := σ.property
    exact ⟨n, congrArg Subtype.val hn⟩
  let pPrime : Nat.Primes := ⟨p, hp.out⟩
  obtain ⟨z, hlocal, hglobal⟩ :=
    exists_finitePlacePrimary_cyclicFixedFieldRepresentative
      (K := K) (L := L) v pPrime δ hσprimary
  have hfactor :=
    DFunLike.congr_fun
      (finitePlaceGlobalNormResidueFactor_comp_rangeRestrict
        (K := K) (L := L) v) z
  have hrange :
      (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).rangeRestrict z =
        (σ :
          (chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v).range) := by
    apply Subtype.ext
    simpa only [MonoidHom.coe_rangeRestrict, δ, σG] using hlocal
  calc
    finitePlaceGlobalNormResidueFactor
          (K := K) (L := L) v σ =
        finitePlaceGlobalNormResidueFactor
          (K := K) (L := L) v
          ((chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v).rangeRestrict z) :=
      congrArg
        (finitePlaceGlobalNormResidueFactor
          (K := K) (L := L) v) hrange.symm
    _ = globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) := by
      simpa only [MonoidHom.coe_comp, Function.comp_apply] using hfactor
    _ = σG := by
      simpa only [δ] using hglobal
    _ = (σ :
          (chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v).range) := rfl

/-- The desired finite-place local--global compatibility is equivalent
to saying that the factor induced on the actual decomposition-group
image is its inclusion into the global Galois group. -/
theorem globalNormResidueMonoidHom_comp_finitePlaceIdeleClass_iff
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (globalNormResidueMonoidHom K L).comp
          (IdeleGroup.finitePlaceIdeleClass v) =
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v ↔
      finitePlaceGlobalNormResidueFactor
          (K := K) (L := L) v =
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).range.subtype := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro σ
    obtain ⟨x, hx⟩ := σ.property
    have hσ :
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).rangeRestrict x = σ :=
      Subtype.ext hx
    calc
      finitePlaceGlobalNormResidueFactor
            (K := K) (L := L) v σ =
          finitePlaceGlobalNormResidueFactor
            (K := K) (L := L) v
            ((chosenFinitePlaceArtinMonoidHom
              (K := K) (L := L) v).rangeRestrict x) :=
        congrArg (finitePlaceGlobalNormResidueFactor
          (K := K) (L := L) v) hσ.symm
      _ = globalNormResidueMonoidHom K L
            (IdeleGroup.finitePlaceIdeleClass v x) :=
        DFunLike.congr_fun
          (finitePlaceGlobalNormResidueFactor_comp_rangeRestrict
            (K := K) (L := L) v) x
      _ = chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v x := DFunLike.congr_fun h x
      _ = (chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v).range.subtype σ := hx
  · intro h
    calc
      (globalNormResidueMonoidHom K L).comp
          (IdeleGroup.finitePlaceIdeleClass v) =
          (finitePlaceGlobalNormResidueFactor
            (K := K) (L := L) v).comp
              (chosenFinitePlaceArtinMonoidHom
                (K := K) (L := L) v).rangeRestrict :=
        (finitePlaceGlobalNormResidueFactor_comp_rangeRestrict
          (K := K) (L := L) v).symm
      _ =
          (chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v).range.subtype.comp
              (chosenFinitePlaceArtinMonoidHom
                (K := K) (L := L) v).rangeRestrict := by
        rw [h]
      _ =
          chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v :=
        MonoidHom.subtype_comp_rangeRestrict
          (chosenFinitePlaceArtinMonoidHom
            (K := K) (L := L) v)

/-- Equality of the induced decomposition-group map with the inclusion
is characterized by equality on every primary component.  This is the
exact finite-group reduction in the proof of finite-place local--global
compatibility. -/
theorem finitePlaceGlobalNormResidueFactor_eq_subtype_iff_primary
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    finitePlaceGlobalNormResidueFactor
          (K := K) (L := L) v =
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).range.subtype ↔
      ∀ (p : ℕ) (_hp : Fact p.Prime)
        (σ :
          CommGroup.primaryComponent
            (chosenFinitePlaceArtinMonoidHom
              (K := K) (L := L) v).range p),
        finitePlaceGlobalNormResidueFactor
            (K := K) (L := L) v σ =
          (σ :
            (chosenFinitePlaceArtinMonoidHom
              (K := K) (L := L) v).range) := by
  constructor
  · intro h p hp σ
    exact congrArg
      (fun f :
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).range →* Gal(L / K) => f σ)
      h
  · intro h
    apply MonoidHom.ext_of_eq_on_finitePrimaryComponents
    intro p hp σ
    exact h p hp σ

/-- The factor of the one-place global norm-residue map through the
actual local Artin image is exactly the inclusion of that decomposition
subgroup into the global Galois group. -/
theorem finitePlaceGlobalNormResidueFactor_eq_subtype
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    finitePlaceGlobalNormResidueFactor
          (K := K) (L := L) v =
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v).range.subtype := by
  apply
    (finitePlaceGlobalNormResidueFactor_eq_subtype_iff_primary
      (K := K) (L := L) v).2
  intro p hp σ
  exact
    finitePlaceGlobalNormResidueFactor_eq_subtype_on_primary
      (K := K) (L := L) v p hp σ

/-- The global norm-residue symbol restricted to a genuine one-place
finite idele class is the actual chosen local Artin symbol. -/
theorem globalNormResidueMonoidHom_comp_finitePlaceIdeleClass
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (globalNormResidueMonoidHom K L).comp
          (IdeleGroup.finitePlaceIdeleClass v) =
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v := by
  apply
    (globalNormResidueMonoidHom_comp_finitePlaceIdeleClass_iff
      (K := K) (L := L) v).2
  exact
    finitePlaceGlobalNormResidueFactor_eq_subtype
      (K := K) (L := L) v

end Reciprocity
end GlobalClassFieldTheory
