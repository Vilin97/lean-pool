/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinCompatibility
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidueAbelianization
/-!
# Arithmetic normalization of global reciprocity

The valuation used by the local class-formation implementation is the
logarithm of the multiplicative absolute value.  Consequently its
distinguished element of value `1` is the inverse of a DVR uniformizer.
The resulting field-facing reciprocity map sends a usual uniformizer to
geometric Frobenius.

The arithmetic global norm-residue symbol uses the opposite
normalization: a DVR uniformizer maps to arithmetic Frobenius and a
ramified cyclotomic unit `u` acts by `u⁻¹`.  For an abelian target the two
normalizations differ by the canonical inversion automorphism.  This file
records that normalization explicitly, including its topology and its
local-global compatibility.  Thus no sign convention is hidden in an
unbundled equality.
-/

open scoped IsMulCommutative NumberField
open NumberField IsDedekindDomain
open IdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

private theorem arithmeticNormIdeleClassIsMulCommutative
    (K : Type) [Field K] [NumberField K] :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] arithmeticNormIdeleClassIsMulCommutative

/-- Inversion as a topological multiplicative automorphism of a
commutative topological group. -/
def commutativeGroupInversionContinuousMulEquiv
    (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    G ≃ₜ* G :=
  { MulEquiv.inv G with
    continuous_toFun := continuous_inv
    continuous_invFun := continuous_inv }

section FiniteGalois

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Reuse the quotient topology chosen by topological global reciprocity. -/
local instance
    arithmeticGlobalNormResidueAbelianization_galoisAbelianizationTopology :
    TopologicalSpace (Abelianization (Gal(L / K))) :=
  topologicalGlobalNormResidueAbelianization_galoisAbelianizationTopology
    K L

/-- The quotient topology above carries the quotient topological-group
structure. -/
local instance
    arithmeticGlobalNormResidueAbelianization_galoisAbelianizationIsTopologicalGroup :
    IsTopologicalGroup (Abelianization (Gal(L / K))) := by
  change
    IsTopologicalGroup
      (Gal(L / K) ⧸ commutator (Gal(L / K)))
  infer_instance

/-- The global norm-residue homomorphism with arithmetic
Frobenius normalization, for an arbitrary finite Galois extension. -/
noncomputable def arithmeticGlobalNormResidueAbelianizationMonoidHom :
    IdeleClassGroup K →*
      Abelianization (Gal(L / K)) :=
  (MulEquiv.inv
      (Abelianization (Gal(L / K)))).toMonoidHom.comp
    (globalNormResidueAbelianizationMonoidHom K L)

/-- Arithmetic normalization evaluates by inverting the geometric
norm-residue symbol. -/
@[simp]
theorem arithmeticGlobalNormResidueAbelianizationMonoidHom_apply
    (c : IdeleClassGroup K) :
    arithmeticGlobalNormResidueAbelianizationMonoidHom K L c =
      (globalNormResidueAbelianizationMonoidHom K L c)⁻¹ := by
  rfl

/-- Arithmetic normalization does not change the genuine norm kernel. -/
@[simp]
theorem arithmeticGlobalNormResidueAbelianizationMonoidHom_ker :
    (arithmeticGlobalNormResidueAbelianizationMonoidHom K L).ker =
      (_root_.ideleClassNorm K L).range := by
  ext c
  simp only [MonoidHom.mem_ker,
    arithmeticGlobalNormResidueAbelianizationMonoidHom_apply,
    inv_eq_one]
  exact globalNormResidueAbelianizationMonoidHom_eq_one_iff K L c

/-- The arithmetic global norm-residue homomorphism is surjective. -/
theorem arithmeticGlobalNormResidueAbelianizationMonoidHom_surjective :
    Function.Surjective
      (arithmeticGlobalNormResidueAbelianizationMonoidHom K L) :=
  (MulEquiv.inv
      (Abelianization (Gal(L / K)))).surjective.comp
    (globalNormResidueAbelianizationMonoidHom_surjective K L)

/-- The arithmetic finite-Galois norm-residue isomorphism, with the
native idèle-class quotient topology and the finite Krull quotient
topology on the Galois abelianization. -/
noncomputable def
    arithmeticGlobalNormResidueAbelianizationContinuousMulEquiv :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃ₜ*
      Abelianization (Gal(L / K)) :=
  (globalNormResidueAbelianizationContinuousMulEquiv K L).trans
    (commutativeGroupInversionContinuousMulEquiv
      (Abelianization (Gal(L / K))))

/-- The arithmetic abelianized norm-residue equivalence is pointwise the
inverse of the geometric equivalence. -/
@[simp]
theorem
    arithmeticGlobalNormResidueAbelianizationContinuousMulEquiv_apply
    (q :
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :
    arithmeticGlobalNormResidueAbelianizationContinuousMulEquiv K L q =
      (globalNormResidueAbelianizationContinuousMulEquiv K L q)⁻¹ := by
  calc
    arithmeticGlobalNormResidueAbelianizationContinuousMulEquiv K L q =
        commutativeGroupInversionContinuousMulEquiv
          (Abelianization (Gal(L / K)))
          (globalNormResidueAbelianizationContinuousMulEquiv K L q) :=
      ContinuousMulEquiv.trans_apply
        (globalNormResidueAbelianizationContinuousMulEquiv K L)
        (commutativeGroupInversionContinuousMulEquiv
          (Abelianization (Gal(L / K)))) q
    _ = (globalNormResidueAbelianizationContinuousMulEquiv K L q)⁻¹ :=
      rfl

/-- The canonical reciprocity isomorphism
`Gal(L/K)ᵃᵇ ≃ₜ* C_K / N_{L/K}(C_L)`, in the direction stated in the
global reciprocity theorem. -/
noncomputable def
    arithmeticGlobalReciprocityAbelianizationContinuousMulEquiv :
    Abelianization (Gal(L / K)) ≃ₜ*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  (arithmeticGlobalNormResidueAbelianizationContinuousMulEquiv
    K L).symm

/-- The inverse of arithmetic reciprocity is literally the arithmetic
global norm-residue symbol on every idèle class. -/
@[simp]
theorem
    arithmeticGlobalReciprocityAbelianizationContinuousMulEquiv_symm_mk
    (c : IdeleClassGroup K) :
    (arithmeticGlobalReciprocityAbelianizationContinuousMulEquiv
        K L).symm
      (QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range c) =
      arithmeticGlobalNormResidueAbelianizationMonoidHom K L c := by
  let q :=
    QuotientGroup.mk'
      (_root_.ideleClassNorm K L).range c
  calc
    (arithmeticGlobalReciprocityAbelianizationContinuousMulEquiv
        K L).symm q =
        arithmeticGlobalNormResidueAbelianizationContinuousMulEquiv
          K L q :=
      DFunLike.congr_fun
        (ContinuousMulEquiv.symm_symm
          (arithmeticGlobalNormResidueAbelianizationContinuousMulEquiv
            K L)) q
    _ = (globalNormResidueAbelianizationContinuousMulEquiv K L q)⁻¹ :=
      arithmeticGlobalNormResidueAbelianizationContinuousMulEquiv_apply
        K L q
    _ = (globalNormResidueAbelianizationMonoidHom K L c)⁻¹ := by
      rw [globalNormResidueAbelianizationContinuousMulEquiv_apply,
        globalNormResidueAbelianizationMonoidHom_apply]
    _ = arithmeticGlobalNormResidueAbelianizationMonoidHom K L c :=
      (arithmeticGlobalNormResidueAbelianizationMonoidHom_apply
        K L c).symm

end FiniteGalois

section FiniteAbelian

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The global norm-residue homomorphism in arithmetic Frobenius
normalization for a finite abelian extension. -/
noncomputable def arithmeticGlobalNormResidueMonoidHom :
    IdeleClassGroup K →* Gal(L / K) :=
  (MulEquiv.inv (Gal(L / K))).toMonoidHom.comp
    (globalNormResidueMonoidHom K L)

/-- Arithmetic normalization evaluates by inverting the geometric global
norm-residue symbol. -/
@[simp]
theorem arithmeticGlobalNormResidueMonoidHom_apply
    (c : IdeleClassGroup K) :
    arithmeticGlobalNormResidueMonoidHom K L c =
      (globalNormResidueMonoidHom K L c)⁻¹ := by
  rfl

/-- Arithmetic normalization leaves the global norm kernel unchanged. -/
@[simp]
theorem arithmeticGlobalNormResidueMonoidHom_ker :
    (arithmeticGlobalNormResidueMonoidHom K L).ker =
      (_root_.ideleClassNorm K L).range := by
  ext c
  simp only [MonoidHom.mem_ker,
    arithmeticGlobalNormResidueMonoidHom_apply, inv_eq_one]
  exact globalNormResidueMonoidHom_eq_one_iff K L c

/-- The arithmetic global norm-residue homomorphism is surjective. -/
theorem arithmeticGlobalNormResidueMonoidHom_surjective :
    Function.Surjective
      (arithmeticGlobalNormResidueMonoidHom K L) :=
  (MulEquiv.inv (Gal(L / K))).surjective.comp
    (globalNormResidueMonoidHom_surjective K L)

/-- The arithmetic global norm-residue map is continuous for the
ordinary idèle-class topology and the finite Krull topology. -/
theorem arithmeticGlobalNormResidueMonoidHom_continuous :
    Continuous (arithmeticGlobalNormResidueMonoidHom K L) := by
  exact continuous_inv.comp
    (globalNormResidueMonoidHom_continuous K L)

/-- Arithmetic global norm-residue as a homeomorphic multiplicative
equivalence of the native norm quotient with the finite Krull Galois
group. -/
noncomputable def arithmeticGlobalNormResidueContinuousMulEquiv :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃ₜ*
      Gal(L / K) :=
  (globalNormResidueContinuousMulEquiv K L).trans
    (commutativeGroupInversionContinuousMulEquiv
      (Gal(L / K)))

/-- The arithmetic norm-residue equivalence is pointwise the inverse of the
geometric equivalence. -/
@[simp]
theorem arithmeticGlobalNormResidueContinuousMulEquiv_apply
    (q :
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :
    arithmeticGlobalNormResidueContinuousMulEquiv K L q =
      (globalNormResidueContinuousMulEquiv K L q)⁻¹ := by
  rfl

/-- The canonical arithmetic reciprocity isomorphism in the direction
`Gal(L/K) ≃ₜ* C_K / N_{L/K}(C_L)`. -/
noncomputable def arithmeticGlobalReciprocityContinuousMulEquiv :
    Gal(L / K) ≃ₜ*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  (arithmeticGlobalNormResidueContinuousMulEquiv K L).symm

/-- Applying inverse arithmetic reciprocity to a quotient representative
recovers the arithmetic norm-residue symbol. -/
@[simp]
theorem arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk
    (c : IdeleClassGroup K) :
    (arithmeticGlobalReciprocityContinuousMulEquiv K L).symm
      (QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range c) =
      arithmeticGlobalNormResidueMonoidHom K L c := by
  rfl

/-- Arithmetic reciprocity sends the arithmetic norm-residue symbol of an
idèle class to its literal representative in the norm quotient. -/
@[simp]
theorem arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue
    (c : IdeleClassGroup K) :
    arithmeticGlobalReciprocityContinuousMulEquiv K L
        (arithmeticGlobalNormResidueMonoidHom K L c) =
      QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range c := by
  let e := arithmeticGlobalReciprocityContinuousMulEquiv K L
  calc
    e (arithmeticGlobalNormResidueMonoidHom K L c) =
        e
          (e.symm
            (QuotientGroup.mk'
              (_root_.ideleClassNorm K L).range c)) :=
      congrArg e
        (arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk
          K L c).symm
    _ = QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range c :=
      e.apply_symm_apply _

/-- The chosen finite-place Artin homomorphism in arithmetic
normalization.  A usual local uniformizer therefore maps to arithmetic
Frobenius. -/
noncomputable def arithmeticChosenFinitePlaceArtinMonoidHom
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* Gal(L / K) :=
  (MulEquiv.inv (Gal(L / K))).toMonoidHom.comp
    (chosenFinitePlaceArtinMonoidHom
      (K := K) (L := L) v)

omit [NumberField L] in
/-- Arithmetic finite-place Artin symbols are inverses of the geometric
chosen local symbols. -/
@[simp]
theorem arithmeticChosenFinitePlaceArtinMonoidHom_apply
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    arithmeticChosenFinitePlaceArtinMonoidHom K L v x =
      (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x)⁻¹ := by
  rfl

/-- Finite-place local-global compatibility in arithmetic
normalization. -/
theorem
    arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
    (v : HeightOneSpectrum (𝓞 K)) :
    (arithmeticGlobalNormResidueMonoidHom K L).comp
        (IdeleGroup.finitePlaceIdeleClass v) =
      arithmeticChosenFinitePlaceArtinMonoidHom K L v := by
  apply MonoidHom.ext
  intro x
  change
    (globalNormResidueMonoidHom K L
      (IdeleGroup.finitePlaceIdeleClass v x))⁻¹ =
      (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x)⁻¹
  simpa only [MonoidHom.comp_apply] using
    congrArg (fun σ : Gal(L / K) => σ⁻¹)
      (DFunLike.congr_fun
        (globalNormResidueMonoidHom_comp_finitePlaceIdeleClass
          (K := K) (L := L) v) x)

/-- The chosen infinite-place Artin homomorphism in arithmetic
normalization. -/
noncomputable def arithmeticChosenInfinitePlaceArtinMonoidHom
    (v : InfinitePlace K) :
    v.Completionˣ →* Gal(L / K) :=
  (MulEquiv.inv (Gal(L / K))).toMonoidHom.comp
    (chosenInfinitePlaceArtinMonoidHom
      (K := K) (L := L) v)

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- Arithmetic infinite-place Artin symbols are inverses of the geometric
chosen local symbols. -/
@[simp]
theorem arithmeticChosenInfinitePlaceArtinMonoidHom_apply
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    arithmeticChosenInfinitePlaceArtinMonoidHom K L v x =
      (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v x)⁻¹ := by
  rfl

/-- Infinite-place local-global compatibility in arithmetic
normalization. -/
theorem
    arithmeticGlobalNormResidueMonoidHom_comp_infinitePlaceIdeleClass
    (v : InfinitePlace K) :
    (arithmeticGlobalNormResidueMonoidHom K L).comp
        (IdeleGroup.infinitePlaceIdeleClass v) =
      arithmeticChosenInfinitePlaceArtinMonoidHom K L v := by
  apply MonoidHom.ext
  intro x
  change
    (globalNormResidueMonoidHom K L
      (IdeleGroup.infinitePlaceIdeleClass v x))⁻¹ =
      (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v x)⁻¹
  simpa only [MonoidHom.comp_apply] using
    congrArg (fun σ : Gal(L / K) => σ⁻¹)
      (DFunLike.congr_fun
        (globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass
          (K := K) (L := L) v) x)

/-- The idèle-level global Artin product in arithmetic normalization. -/
noncomputable def arithmeticGlobalArtinMonoidHom :
    IdeleGroup K →* Gal(L / K) :=
  (MulEquiv.inv (Gal(L / K))).toMonoidHom.comp
    (globalArtinMonoidHom (K := K) (L := L))

omit [FiniteDimensional K L] in
/-- The arithmetic global Artin symbol is the inverse of the geometric global
Artin symbol. -/
@[simp]
theorem arithmeticGlobalArtinMonoidHom_apply
    (a : IdeleGroup K) :
    arithmeticGlobalArtinMonoidHom K L a =
      (globalArtinMonoidHom (K := K) (L := L) a)⁻¹ := by
  rfl

/-- The arithmetic global Artin symbol of a finite one-place idèle is
literally the arithmetic chosen local Artin symbol. -/
@[simp]
theorem arithmeticGlobalArtinMonoidHom_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    arithmeticGlobalArtinMonoidHom K L
        (finitePlaceIdele v x) =
      arithmeticChosenFinitePlaceArtinMonoidHom K L v x := by
  rw [arithmeticGlobalArtinMonoidHom_apply,
    globalArtinMonoidHom_finitePlaceIdele,
    arithmeticChosenFinitePlaceArtinMonoidHom_apply]

omit [FiniteDimensional K L] in
/-- The arithmetic global Artin symbol of an infinite one-place idèle
is literally the arithmetic chosen local Artin symbol. -/
@[simp]
theorem arithmeticGlobalArtinMonoidHom_infinitePlaceIdele
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    arithmeticGlobalArtinMonoidHom K L
        (infinitePlaceIdele v x) =
      arithmeticChosenInfinitePlaceArtinMonoidHom K L v x := by
  rw [arithmeticGlobalArtinMonoidHom_apply,
    globalArtinMonoidHom_infinitePlaceIdele,
    arithmeticChosenInfinitePlaceArtinMonoidHom_apply]

/-- Arithmetic global Artin kills every principal idèle. -/
@[simp]
theorem arithmeticGlobalArtinMonoidHom_principalIdele
    (x : Kˣ) :
    arithmeticGlobalArtinMonoidHom K L
        (IdeleGroup.principalIdele K x) =
      1 := by
  rw [arithmeticGlobalArtinMonoidHom_apply,
    globalArtinMonoidHom_principalIdele, inv_one]

/-- Descending the arithmetic local-product Artin map through principal
idèles gives the arithmetic global norm-residue homomorphism literally. -/
theorem
    arithmeticGlobalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin :
    (arithmeticGlobalNormResidueMonoidHom K L).comp
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)) =
      arithmeticGlobalArtinMonoidHom K L := by
  apply MonoidHom.ext
  intro a
  change
    (globalNormResidueMonoidHom K L
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a))⁻¹ =
      (globalArtinMonoidHom (K := K) (L := L) a)⁻¹
  simpa only [MonoidHom.comp_apply] using
    congrArg (fun σ : Gal(L / K) => σ⁻¹)
      (DFunLike.congr_fun
        (globalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin
          (K := K) (L := L)) a)

end FiniteAbelian

end Reciprocity
end GlobalClassFieldTheory
