/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicIdealArtinKernelComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicIdealNormQuotientComparison
/-!
# The ideal norm subgroup is the Artin kernel

This is the ideal-theoretic norm-kernel form of finite abelian reciprocity.
The ideal norms are norms of fractional ideals prime to the modulus; the
principal ray ideals are absorbed by the ray quotient.
-/

@[expose] public section

open scoped NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

open scoped Classical in
open GlobalClassFieldTheory.IdealClassFieldTheory renaming
  idealArtinKernel_eq_idealNormSubgroup_of_finiteExtension →
    idealArtinKernel_eq_idealNormSubgroup_of_finiteExtension in
/-- For finite abelian reciprocity data, the image of genuine ideal norms
in the ideal ray class group equals the normalized Artin kernel. -/
theorem rayClassIdealNormImage_eq_artinKer
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    rayClassIdealNormImage K L D.modulus = D.artin.ker := by
  let m := GlobalClassFieldComparison.rayClassModulusToOriginal K D.modulus
  have hsource :=
    idealArtinKernel_eq_idealNormSubgroup_of_finiteExtension
      (K := K) (L := L) m
      (GlobalClassFieldComparison.finiteAbelianReciprocity_modulus_isDefining K L D)
  have hquot :=
    GlobalClassFieldComparison.publicIdealNormImage_comap_rayQuotient
      K L D.modulus
  apply Subgroup.ext
  intro x
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
    (rayPrincipalIdealSubgroupInPrimeTo D.modulus) x
  have hnorm :
      (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo D.modulus) I) ∈
        rayClassIdealNormImage K L D.modulus ↔
      I ∈ RayClass.idealNormSubgroup (K := K) (L := L) m := by
    exact Subgroup.ext_iff.mp hquot I
  rw [hnorm, ← hsource]
  exact (GlobalClassFieldComparison.publicArtinKer_iff_idealArtinKernel
    K L D I).symm

end ClassFieldTheory
