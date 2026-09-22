/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinDescent
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinSurjectivity
/-!
# Global Artin map for the maximal abelian extension

This module specializes the continuous infinite global Artin map to the
maximal abelian subextension of the separable closure.  It also exposes the
idele-representative evaluation and its finite Galois projections.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
/-- The continuous global Artin homomorphism from the idele class group to
the Galois group of the maximal abelian extension. -/
noncomputable def maximalAbelianGlobalArtin :
    IdeleClassGroup K →ₜ* Gal(maximalAbelianExtension K/K) :=
  infiniteGlobalIdeleClassArtinContinuousMonoidHom
    (K := K) (Ω := maximalAbelianExtension K)

open scoped Classical in
/-- Evaluation of the maximal abelian global Artin map on an idele
representative recovers the infinite global Artin map. -/
theorem maximalAbelianGlobalArtin_mk (a : IdeleGroup K) :
    maximalAbelianGlobalArtin K
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a) =
      infiniteGlobalArtinMonoidHom K (maximalAbelianExtension K) a :=
  infiniteGlobalIdeleClassArtinMonoidHom_mk
    (K := K) (Ω := maximalAbelianExtension K) a

open scoped Classical in
/-- Projection of the maximal abelian global Artin map at an idele
representative to a finite Galois intermediate field agrees with the finite
global Artin map. -/
theorem maximalAbelianGlobalArtin_finiteProjection
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K (maximalAbelianExtension K)) :
    letI : NumberField E := NumberField.of_module_finite K E
    AlgEquiv.restrictNormalHom E
        (maximalAbelianGlobalArtin K
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a)) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  let : NumberField E := NumberField.of_module_finite K E
  rw [maximalAbelianGlobalArtin_mk]
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom
      K (maximalAbelianExtension K) a E

open scoped Classical in
/-- The maximal abelian global Artin homomorphism is surjective. -/
theorem maximalAbelianGlobalArtin_surjective :
    Function.Surjective (maximalAbelianGlobalArtin K) :=
  infiniteGlobalIdeleClassArtinContinuousMonoidHom_surjective
    K (maximalAbelianExtension K)

end Reciprocity
end GlobalClassFieldTheory
