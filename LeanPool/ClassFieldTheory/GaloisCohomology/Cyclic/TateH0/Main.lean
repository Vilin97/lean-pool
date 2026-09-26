/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.TateH0.NormImage
/-!
# Degree-zero Tate cohomology and the norm quotient

This module identifies degree-zero Tate cohomology of the multiplicative group
of a finite Galois extension with the corresponding field norm quotient.
-/

@[expose] public section

namespace CyclicCohomology

open LocalFieldTheory

noncomputable
section

/-- The canonical comparison between mathlib's degree-zero Tate cohomology of
`Lˣ` and the field norm quotient `Kˣ / N_{L/K}(Lˣ)` for a finite Galois
extension. -/
def H0TateUnitsIsoNormQuotient (K L : Type)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    CategoryTheory.Iso (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0)
      (ModuleCat.of Int (Additive (NormQuotient K L))) := by
  letI := AlgEquiv.fintype K L
  let eInv :
      (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) ≃ₗ[Int]
        (Additive Kˣ ⧸ (additiveNormSubgroup K L).toIntSubmodule) :=
    Submodule.Quotient.equiv
      (unitsTateH0NormSubmodule K L)
      ((additiveNormSubgroup K L).toIntSubmodule)
      (invariantsUnitsEquivBaseUnits K L)
      (invariantsUnitsEquivBaseUnits_map_tateNormSubmodule K L)
  let eNorm :
      (Additive Kˣ ⧸ (additiveNormSubgroup K L).toIntSubmodule) ≃+
        Additive (NormQuotient K L) :=
    (QuotientAddGroup.quotientAddEquivOfEq
        (additiveNormSubgroup_eq_ker_quotient_map K L)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (MonoidHom.toAdditive (normClass K L)) (by
          change Function.Surjective
            (QuotientGroup.mk' (localNormSubgroup K L))
          exact QuotientGroup.mk'_surjective _))
  exact tateUnitsH0IsoInvariantsQuotient K L ≪≫
    eInv.toModuleIso ≪≫ eNorm.toIntLinearEquiv.toModuleIso

end
end CyclicCohomology
