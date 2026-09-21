/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.LocalizationRamificationGroups
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.PadicLocalization
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalFieldTheory.Padic.Cyclotomic.Unramified.CanonicalExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaIntegralClosure
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueExtensionCoefficients
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring
/-!
# The valuation on the p-adic localization in the global cyclotomic inertia argument

The localization constructed in is transported from the absolute
value completion of `ℚ` to the concrete field `ℚ_p`.  Uniqueness of the
absolute-value extension identifies its valuation ring with the canonical
norm-formula valuation ring used in the unramified cyclotomic extension theorem.
-/

noncomputable section

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations

variable (p : ℕ) [Fact p.Prime]
variable (L : Type) [Field L] [Algebra ℚ L]
  [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L]

/-- The absolute-value comparison statement for the raw algebraic localization,
with the transported `ℚ_p` structure kept internal. -/
noncomputable def globalPadicLocalizationCanonicalAbsoluteValueProperty
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) L) : Prop := by
  let vK := Rat.AbsoluteValue.padic p
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
  letI : SMul ℚ w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  letI hE : Field E := inferInstance
  letI hBaseE : Algebra vK.Completion E := inferInstance
  let e := padicAbsoluteValueCompletionRingEquiv p
  letI : Algebra ℚ_[p] E :=
    @transportedAlgebraAlongRingEquiv vK.Completion ℚ_[p] E _ _
      (@CommRing.toCommSemiring E hE.toCommRing) hBaseE e
  letI : Module.Finite vK.Completion E :=
    globalPadicLocalizationModuleFinite p L w
  letI : Algebra ℚ_[p] vK.Completion := e.symm.toRingHom.toAlgebra
  letI : IsScalarTower ℚ_[p] vK.Completion E :=
    IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  letI : Module.Finite ℚ_[p] vK.Completion :=
    FiniteDimensional.of_surjective
      (Algebra.linearMap ℚ_[p] vK.Completion) e.symm.surjective
  letI : Module.Finite ℚ_[p] E := Module.Finite.trans vK.Completion E
  exact AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2 =
    padicFiniteExtensionAbsoluteValue p E

/-- The algebraic-localization absolute value is exactly the canonical
norm-formula absolute value on its transported finite `ℚ_p`-extension. -/
theorem globalPadicLocalizationAbsoluteValue_eq_canonical
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) L) :
    globalPadicLocalizationCanonicalAbsoluteValueProperty p L w := by
  let vK := Rat.AbsoluteValue.padic p
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
  let : SMul ℚ w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let hE : Field E := inferInstance
  let hBaseE : Algebra vK.Completion E := inferInstance
  let e := padicAbsoluteValueCompletionRingEquiv p
  let hQpE : Algebra ℚ_[p] E :=
    @transportedAlgebraAlongRingEquiv vK.Completion ℚ_[p] E _ _
      (@CommRing.toCommSemiring E hE.toCommRing) hBaseE e
  let : Module.Finite vK.Completion E :=
    globalPadicLocalizationModuleFinite p L w
  let : Algebra ℚ_[p] vK.Completion := e.symm.toRingHom.toAlgebra
  let : IsScalarTower ℚ_[p] vK.Completion E :=
    IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  let : Module.Finite ℚ_[p] vK.Completion :=
    FiniteDimensional.of_surjective
      (Algebra.linearMap ℚ_[p] vK.Completion) e.symm.surjective
  let : Module.Finite ℚ_[p] E := Module.Finite.trans vK.Completion E
  change AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2 =
    padicFiniteExtensionAbsoluteValue p E
  let aE := AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
  have hQpExt : ∀ x : ℚ_[p],
      aE (algebraMap ℚ_[p] E x) =
        NormedField.toAbsoluteValue ℚ_[p] x := by
    intro x
    change aE (algebraMap vK.Completion E (e.symm x)) = ‖x‖
    rw [AbsoluteValue.algebraicLocalizationAbsoluteValue_extends]
    change ‖e.symm x‖ = ‖x‖
    have hnorm :=
      (padicAbsoluteValueCompletionRingHom_isometry p).norm_map_of_map_zero
        (map_zero (padicAbsoluteValueCompletionRingHom p)) (e.symm x)
    calc
      ‖e.symm x‖ =
          ‖padicAbsoluteValueCompletionRingHom p (e.symm x)‖ := hnorm.symm
      _ = ‖e (e.symm x)‖ := rfl
      _ = ‖x‖ := by rw [e.apply_symm_apply]
  have hLocalUnique :=
    AbsoluteValue.eq_spectralExtension_of_extends
      (NormedField.toAbsoluteValue ℚ_[p])
      (completeSpace_withAbs_of_isCompleteForAbsoluteValue _
        (padicFieldAbsoluteValue_complete p))
      ((LubinTate.Valuations.strong_triangle_iff_isNonarchimedean _).1
        (LubinTate.Valuations.strong_triangle_of_nonarchimedean _
          (padicFieldAbsoluteValue_nonarchimedean p)))
      (padicFieldAbsoluteValue_isNontrivial p)
      aE hQpExt
  have hCanonicalUnique :=
    AbsoluteValue.eq_spectralExtension_of_extends
      (NormedField.toAbsoluteValue ℚ_[p])
      (completeSpace_withAbs_of_isCompleteForAbsoluteValue _
        (padicFieldAbsoluteValue_complete p))
      ((LubinTate.Valuations.strong_triangle_iff_isNonarchimedean _).1
        (LubinTate.Valuations.strong_triangle_of_nonarchimedean _
          (padicFieldAbsoluteValue_nonarchimedean p)))
      (padicFieldAbsoluteValue_isNontrivial p)
      (padicFiniteExtensionAbsoluteValue p E)
      (padicFiniteExtensionAbsoluteValue_extends p E)
  exact hLocalUnique.trans hCanonicalUnique.symm

/-- The valuation-ring comparison statement for the raw algebraic localization,
with all transported local instances kept internal. -/
noncomputable def globalPadicLocalizationCanonicalValuationProperty
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) L) : Prop := by
  let vK := Rat.AbsoluteValue.padic p
  let hv := rationalPadicAbsoluteValue_nonarchimedean p
  let hw := HilbertRamification.absoluteValueExtension_nonarchimedean_of_base vK w hv
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
  letI : SMul ℚ w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  letI hE : Field E := inferInstance
  letI hBaseE : Algebra vK.Completion E := inferInstance
  let e := padicAbsoluteValueCompletionRingEquiv p
  letI hQpE : Algebra ℚ_[p] E :=
    @transportedAlgebraAlongRingEquiv vK.Completion ℚ_[p] E _ _
      (@CommRing.toCommSemiring E hE.toCommRing) hBaseE e
  letI : Module.Finite vK.Completion E :=
    globalPadicLocalizationModuleFinite p L w
  letI : Algebra ℚ_[p] vK.Completion := e.symm.toRingHom.toAlgebra
  letI : IsScalarTower ℚ_[p] vK.Completion E :=
    IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  letI : Module.Finite ℚ_[p] vK.Completion :=
    FiniteDimensional.of_surjective
      (Algebra.linearMap ℚ_[p] vK.Completion) e.symm.surjective
  letI : Module.Finite ℚ_[p] E := Module.Finite.trans vK.Completion E
  exact
    HilbertRamification.algebraicLocalizationValuationSubring vK w hw =
      absoluteValueValuationSubring
        (padicFiniteExtensionAbsoluteValue p E)
        (padicFiniteExtensionAbsoluteValue_nonarchimedean p E)

/-- The algebraic-localization valuation ring is the canonical valuation
ring on the transported finite extension of `ℚ_p`. -/
theorem globalPadicLocalizationValuationSubring_eq_canonical
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) L) :
    globalPadicLocalizationCanonicalValuationProperty p L w := by
  let vK := Rat.AbsoluteValue.padic p
  let hv := rationalPadicAbsoluteValue_nonarchimedean p
  let hw := HilbertRamification.absoluteValueExtension_nonarchimedean_of_base vK w hv
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
  let : SMul ℚ w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let hE : Field E := inferInstance
  let hBaseE : Algebra vK.Completion E := inferInstance
  let e := padicAbsoluteValueCompletionRingEquiv p
  let hQpE : Algebra ℚ_[p] E :=
    @transportedAlgebraAlongRingEquiv vK.Completion ℚ_[p] E _ _
      (@CommRing.toCommSemiring E hE.toCommRing) hBaseE e
  let : Module.Finite vK.Completion E :=
    globalPadicLocalizationModuleFinite p L w
  let : Algebra ℚ_[p] vK.Completion := e.symm.toRingHom.toAlgebra
  let : IsScalarTower ℚ_[p] vK.Completion E :=
    IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  let : Module.Finite ℚ_[p] vK.Completion :=
    FiniteDimensional.of_surjective
      (Algebra.linearMap ℚ_[p] vK.Completion) e.symm.surjective
  let : Module.Finite ℚ_[p] E := Module.Finite.trans vK.Completion E
  change
    HilbertRamification.algebraicLocalizationValuationSubring vK w hw =
      absoluteValueValuationSubring
        (padicFiniteExtensionAbsoluteValue p E)
        (padicFiniteExtensionAbsoluteValue_nonarchimedean p E)
  let aE := AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
  have hQpExt : ∀ x : ℚ_[p],
      aE (algebraMap ℚ_[p] E x) =
        NormedField.toAbsoluteValue ℚ_[p] x := by
    intro x
    change aE (algebraMap vK.Completion E (e.symm x)) = ‖x‖
    rw [AbsoluteValue.algebraicLocalizationAbsoluteValue_extends]
    change ‖e.symm x‖ = ‖x‖
    have hnorm :=
      (padicAbsoluteValueCompletionRingHom_isometry p).norm_map_of_map_zero
        (map_zero (padicAbsoluteValueCompletionRingHom p)) (e.symm x)
    calc
      ‖e.symm x‖ =
          ‖padicAbsoluteValueCompletionRingHom p (e.symm x)‖ := hnorm.symm
      _ = ‖e (e.symm x)‖ := rfl
      _ = ‖x‖ := by rw [e.apply_symm_apply]
  have hLocalUnique :=
    AbsoluteValue.eq_spectralExtension_of_extends
      (NormedField.toAbsoluteValue ℚ_[p])
      (completeSpace_withAbs_of_isCompleteForAbsoluteValue _
        (padicFieldAbsoluteValue_complete p))
      ((LubinTate.Valuations.strong_triangle_iff_isNonarchimedean _).1
        (LubinTate.Valuations.strong_triangle_of_nonarchimedean _
          (padicFieldAbsoluteValue_nonarchimedean p)))
      (padicFieldAbsoluteValue_isNontrivial p)
      aE hQpExt
  have hCanonicalUnique :=
    AbsoluteValue.eq_spectralExtension_of_extends
      (NormedField.toAbsoluteValue ℚ_[p])
      (completeSpace_withAbs_of_isCompleteForAbsoluteValue _
        (padicFieldAbsoluteValue_complete p))
      ((LubinTate.Valuations.strong_triangle_iff_isNonarchimedean _).1
        (LubinTate.Valuations.strong_triangle_of_nonarchimedean _
          (padicFieldAbsoluteValue_nonarchimedean p)))
      (padicFieldAbsoluteValue_isNontrivial p)
      (padicFiniteExtensionAbsoluteValue p E)
      (padicFiniteExtensionAbsoluteValue_extends p E)
  have hAbsolute :
      aE = padicFiniteExtensionAbsoluteValue p E :=
    hLocalUnique.trans hCanonicalUnique.symm
  change absoluteValueValuationSubring aE _ = _
  ext x
  simp only [mem_absoluteValueValuationSubring_iff,
    hAbsolute]

end HilbertRamification

end
