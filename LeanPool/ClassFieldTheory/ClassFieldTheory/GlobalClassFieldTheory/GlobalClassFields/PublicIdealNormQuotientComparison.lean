/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
/-!
# Comparing source and public ideal-norm subgroups

The source ideal norm is defined before quotienting by principal ray ideals.
The public ideal-norm image is its image in the ideal ray class group.  This
file records the exact comparison, including the principal-ray kernel.
-/

@[expose] public section

open scoped NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory.GlobalClassFieldComparison

open scoped Classical in
private theorem publicIdealNormDomain_eq_source'
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (m : RayClassModulus K) :
    rayClassPrimeToIdealNormDomain K L m =
      RayClass.primeToModulusIdeals
        (RayClass.idealNormLiftedModulus (K := K) (L := L)
          (rayClassModulusToOriginal K m)) := by
  apply Subgroup.ext
  intro I
  change (∀ W, fractionalIdealNormPrimeBelow K L W ∈
      m.finitePart.support →
        FractionalIdeal.count L W
          (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = 0) ↔
    (∀ W, W ∈ (RayClass.idealNormLiftedModulus
      (K := K) (L := L) (rayClassModulusToOriginal K m)).finitePart.support →
        FractionalIdeal.count L W
          (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = 0)
  have hbelow (W : HeightOneSpectrum (𝓞 L)) :
      fractionalIdealNormPrimeBelow K L W =
        _root_.finitePlaceBelow (K := K) W := by
    ext
    rfl
  constructor
  · intro h W hW
    apply h W
    rw [hbelow]
    exact (RayClass.mem_idealNormLiftedModulus_support_iff
      (K := K) (L := L) (rayClassModulusToOriginal K m) W).mp hW
  · intro h W hW
    apply h W
    rw [RayClass.mem_idealNormLiftedModulus_support_iff, ← hbelow]
    exact hW

open scoped Classical in
/-- The preimage of the public ideal-norm image under the ray quotient is
exactly the original norm subgroup, including principal ray ideals. -/
theorem publicIdealNormImage_comap_rayQuotient
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (m : RayClassModulus K) :
    (rayClassIdealNormImage K L m).comap
        (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)) =
      RayClass.idealNormSubgroup (K := K) (L := L)
        (rayClassModulusToOriginal K m) := by
  let m' := rayClassModulusToOriginal K m
  let q : RayClass.primeToModulusIdeals m' →* RayClassGroup m :=
    QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
  let N := (RayClass.primeToModulusIdealNorm (K := K) (L := L) m').range
  have hdomain := publicIdealNormDomain_eq_source' K L m
  have hnorm : rayClassIdealNormImage K L m = N.map q := by
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨I, rfl⟩
      let J : RayClass.primeToModulusIdeals
          (RayClass.idealNormLiftedModulus (K := K) (L := L) m') :=
        ⟨I, by rw [← hdomain]; exact I.property⟩
      refine ⟨RayClass.primeToModulusIdealNorm (K := K) (L := L) m' J,
        ⟨J, rfl⟩, ?_⟩
      apply congrArg (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m))
      apply Subtype.ext
      change RayClass.fractionalIdealNorm (K := K) (L := L) (J : _) =
        fractionalIdealNorm K L (I : _)
      exact congrArg (fun f => f (I : _))
        (RayClass.fractionalIdealNorm_eq_public (K := K) (L := L))
    · rintro ⟨I, ⟨J, rfl⟩, rfl⟩
      let J' : rayClassPrimeToIdealNormDomain K L m :=
        ⟨J, by rw [hdomain]; exact J.property⟩
      refine ⟨J', ?_⟩
      apply congrArg (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m))
      apply Subtype.ext
      change fractionalIdealNorm K L (J' : _) =
        RayClass.fractionalIdealNorm (K := K) (L := L) (J : _)
      exact (congrArg (fun f => f (J : _))
        (RayClass.fractionalIdealNorm_eq_public (K := K) (L := L))).symm
  rw [hnorm]
  change (N.map q).comap q = N ⊔
    RayClass.principalRayIdealSubgroup m'
  rw [Subgroup.comap_map_eq]
  rw [show q.ker = rayPrincipalIdealSubgroupInPrimeTo m by
    exact QuotientGroup.ker_mk' (rayPrincipalIdealSubgroupInPrimeTo m)]
  rw [rayPrincipalIdealSubgroup_eq]

end ClassFieldTheory.GlobalClassFieldComparison
