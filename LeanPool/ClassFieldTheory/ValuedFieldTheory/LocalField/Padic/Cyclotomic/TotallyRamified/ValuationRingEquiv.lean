/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.IntegralTranslate
/-!
# The valuation-ring equivalence for the totally ramified cyclotomic extension

This file constructs the concrete equivalence from `ℤ_[p][ζ - 1]` to the actual valuation subring.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial
open scoped Polynomial

universe u

section CyclotomicExtension

variable {p k : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [Algebra ℚ_[p] L]

/-- The `ℤ_[p]`-algebra on the cyclotomic extension is induced through `ℚ_[p]`. -/
local instance padicCyclotomicTotallyRamifiedValuationRingEquivAlgebraPadicInt : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

local instance padicCyclotomicTotallyRamifiedValuationRingEquivScalarTowerPadicInt :
    IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The concrete ring `ℤ_[p][ζ - 1]` is canonically equivalent to the
valuation subring in the actual-integral-closure complete-DVF model, and the
equivalence preserves the represented element of `L`. -/
theorem padicCyclotomicTotallyRamified_exists_adjoin_sub_one_equiv_valuationSubring
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤)
    (target : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} L)
    [hExt : (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
      p).valuation.HasExtension
      target.valuation]
    [hTarget : IsIntegralClosure target.valuationSubring
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring L] :
    ∃ q : Algebra.adjoin ℤ_[p] ({ζ - 1} : Set L) ≃+*
        target.valuationSubring,
      ∀ z, algebraMap target.valuationSubring L (q z) =
        algebraMap (Algebra.adjoin ℤ_[p] ({ζ - 1} : Set L)) L z := by
  let A := Algebra.adjoin ℤ_[p] ({ζ - 1} : Set L)
  let Aζ := Algebra.adjoin ℤ_[p] ({ζ} : Set L)
  have hA : A = Aζ := by
    simpa [A, Aζ] using padicCyclotomicTotallyRamified_adjoin_sub_one_eq_adjoin ζ
  let eTranslate : A ≃+* Aζ :=
    (Subalgebra.equivOfEq A Aζ hA).toRingEquiv
  let base := LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  let V := base.valuationSubring
  let : Algebra V L := Algebra.ofSubsemiring base.valuation.valuationSubring
  let : IsScalarTower V ℚ_[p] L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsIntegralClosure target.valuationSubring V L := by
    simpa [V, base] using hTarget
  let : IsScalarTower V target.valuationSubring L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : IsIntegralClosure Aζ ℤ_[p] L := by
    simpa [Aζ] using padicCyclotomicTotallyRamified_isIntegralClosure_adjoin ζ hζ hgen
  let eZV : ℤ_[p] ≃+* V :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring p
  have heZV : (algebraMap V L).comp eZV.toRingHom = algebraMap ℤ_[p] L := by
    ext z
    rfl
  let eIC : integralClosure ℤ_[p] L ≃+* integralClosure V L :=
    { toFun := fun z => ⟨z.1, (eZV.isIntegral_iff heZV z.1).mp z.2⟩
      invFun := fun z => ⟨z.1, (eZV.isIntegral_iff heZV z.1).mpr z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let eAζ : Aζ ≃+* integralClosure ℤ_[p] L :=
    (IsIntegralClosure.equiv ℤ_[p] Aζ L
      (integralClosure ℤ_[p] L)).toRingEquiv
  let eTarget : integralClosure V L ≃+* target.valuationSubring :=
    (IsIntegralClosure.equiv V (integralClosure V L) L
      target.valuationSubring).toRingEquiv
  let q : A ≃+* target.valuationSubring :=
    eTranslate.trans (eAζ.trans (eIC.trans eTarget))
  refine ⟨q, ?_⟩
  intro z
  have heAζ :
      algebraMap (integralClosure ℤ_[p] L) L (eAζ (eTranslate z)) =
        algebraMap Aζ L (eTranslate z) :=
    IsIntegralClosure.algebraMap_equiv ℤ_[p] Aζ L
      (integralClosure ℤ_[p] L) (eTranslate z)
  have heTarget :
      algebraMap target.valuationSubring L
          (eTarget (eIC (eAζ (eTranslate z)))) =
        algebraMap (integralClosure V L) L (eIC (eAζ (eTranslate z))) :=
    IsIntegralClosure.algebraMap_equiv V (integralClosure V L) L
      target.valuationSubring (eIC (eAζ (eTranslate z)))
  calc
    algebraMap target.valuationSubring L (q z) =
        algebraMap target.valuationSubring L
          (eTarget (eIC (eAζ (eTranslate z)))) := rfl
    _ = algebraMap (integralClosure V L) L
          (eIC (eAζ (eTranslate z))) := heTarget
    _ = algebraMap (integralClosure ℤ_[p] L) L
          (eAζ (eTranslate z)) := rfl
    _ = algebraMap Aζ L (eTranslate z) := heAζ
    _ = algebraMap A L z := rfl

end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
