/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicIdealNormArtinKernel
/-!
# Ideal norms are killed by the ray-class Artin map

This is the forward direction of the ideal-theoretic norm-kernel formula.
The subgroup is formed from actual fractional-ideal norms, not from idèle
norms. Equality requires the separate reverse approximation theorem.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- For finite abelian reciprocity data, the image of genuine ideal norms
in the ray class group lies in the normalized Artin kernel. -/
theorem rayClassIdealNormImage_le_artinKer
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    rayClassIdealNormImage K L D.modulus ≤ D.artin.ker :=
  GlobalClassFieldComparison.idealNormImage_le_finiteAbelianReciprocityArtinKer K L D

end ClassFieldTheory
