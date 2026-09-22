/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
/-!
# Principal ideles and the idele class group

This file formalizes the diagonal
embedding of `Kˣ` into the idele group and the resulting idele class group.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

namespace IdeleGroup

/-- The diagonal embedding of `Kˣ` into the idele group. -/
def principalIdele : Kˣ →* IdeleGroup K :=
  (equivAdeleRingUnits (K := K)).symm.toMonoidHom.comp
    (Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K)))

variable {K}

/-- The finite component of a principal idele is the image of the
underlying field element in the corresponding completion. -/
theorem finiteComponent_principalIdele
    (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((finiteComponent v (principalIdele K x) :
      (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : K) :=
  rfl

/-- The infinite component of a principal idele is the image of the
underlying field element in the corresponding completion. -/
theorem infiniteComponent_principalIdele
    (x : Kˣ) (w : InfinitePlace K) :
    ((infiniteComponent w (principalIdele K x) :
      w.Completionˣ) : w.Completion) = (x : K) :=
  rfl

variable (K)

/-- The diagonal map from field units to ideles is injective. -/
theorem principalIdele_injective :
    Function.Injective (principalIdele K) := by
  apply (equivAdeleRingUnits (K := K)).symm.injective.comp
  exact Units.map_injective
    (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K))

/-- The subgroup of principal ideles. -/
def principalSubgroup : Subgroup (IdeleGroup K) :=
  (principalIdele K).range

/-- The multiplicative group `Kˣ`, identified with the subgroup of principal
ideles. -/
def principalEquiv : Kˣ ≃* principalSubgroup K :=
  MonoidHom.ofInjective (principalIdele_injective K)

@[simp]
theorem coe_principalEquiv (x : Kˣ) :
    (principalEquiv K x : IdeleGroup K) = principalIdele K x :=
  MonoidHom.ofInjective_apply (principalIdele_injective K)

end IdeleGroup

/-- The idele class group `C_K = I_K / Kˣ`. -/
abbrev IdeleClassGroup :=
  IdeleGroup K ⧸ IdeleGroup.principalSubgroup K
