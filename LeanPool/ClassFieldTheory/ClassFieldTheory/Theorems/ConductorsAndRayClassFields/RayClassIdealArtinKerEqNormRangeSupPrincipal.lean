/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassIdealNormImageEqArtinKer
/-!
# Ideal Artin kernel before passage to ray classes

The kernel in prime-to-modulus ideals is the product of the genuine ideal
norm image and the principal ray-ideal subgroup.
-/

open scoped Classical NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- Before passing to ray classes, the Artin kernel is the product of the
genuine ideal-norm subgroup and the principal ray-ideal subgroup. -/
theorem rayClassIdealArtinKer_eq_normRange_sup_principal
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    (D.artin.comp
      (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo D.modulus))).ker =
      (rayClassPrimeToIdealNorm K L D.modulus).range ⊔
        rayPrincipalIdealSubgroupInPrimeTo D.modulus := by
  let q : rayClassPrimeToIdeals D.modulus →* RayClassGroup D.modulus :=
    QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo D.modulus)
  let N := (rayClassPrimeToIdealNorm K L D.modulus).range
  change (D.artin.comp q).ker = N ⊔
    rayPrincipalIdealSubgroupInPrimeTo D.modulus
  calc
    (D.artin.comp q).ker = D.artin.ker.comap q := by
      exact (MonoidHom.comap_ker D.artin q).symm
    _ = (rayClassIdealNormImage K L D.modulus).comap q := by
      rw [rayClassIdealNormImage_eq_artinKer K L D]
    _ = (N.map q).comap q := by
      rw [← MonoidHom.range_comp]
      rfl
    _ = N ⊔ rayPrincipalIdealSubgroupInPrimeTo D.modulus := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

end ClassFieldTheory
