/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
/-!
# Unramified normalization of the chosen finite-place Artin map

The chosen order-one input has normalized local valuation `-1` in the
geometric finite-place construction. Its local Artin image is therefore
inverse arithmetic Frobenius in the actual chosen completion.
-/

@[expose] public section

open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations LocalFieldTheory

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]

open scoped Classical in
/-- Arithmetic Frobenius of the actual chosen unramified local extension. -/
noncomputable def chosenFinitePlaceLocalArithmeticFrobenius
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v ≃ₐ[ChosenFinitePlaceBaseCompletion
      (K := K) v]
      ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v := by
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  letI : IsGalois C E :=
    chosenFinitePlaceLocalizedIsGalois (K := K) (L := L) v
  letI : Valuation.HasExtension
      (ValuativeRel.valuation C) (ValuativeRel.valuation E) :=
    chosenFinitePlaceLocalizedValuationHasExtension (K := K) (L := L) v
  letI : IsIntegralClosure 𝒪[E] 𝒪[C] E :=
    chosenFinitePlaceLocalizedIsIntegralClosure (K := K) (L := L) v
  letI : Module.Finite 𝒪[C] 𝒪[E] :=
    chosenFinitePlaceLocalizedIntegerModuleFinite (K := K) (L := L) v
  letI : IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      C E := hunram
  exact arithmeticFrobeniusOfUnramifiedValuation C E

open scoped Classical in
/-- At an unramified chosen finite place, the chosen geometric local Artin
symbol of the order-one section is inverse arithmetic Frobenius. -/
theorem chosenFinitePlaceLocalArtin_eq_arithmeticFrobenius_inv_of_unramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    finitePlaceLocalArtinMonoidHom (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v)
        (FiniteIdeleGroup.chosenLocalOrderSection v 1) =
      (chosenFinitePlaceLocalArithmeticFrobenius
        (K := K) (L := L) v hunram)⁻¹ := by
  let w := chosenFinitePlaceExtension (L := L) v
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let x : (v.adicCompletion K)ˣ :=
    FiniteIdeleGroup.chosenLocalOrderSection v 1
  let : Algebra C E := finitePlaceLocalArtinLocalizedAlgebra v w
  let : FiniteDimensional C E := finitePlaceLocalArtinFiniteDimensional v w
  let : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois v w hKLfinite
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : IsIntegralClosure 𝒪[E] 𝒪[C] E :=
    chosenFinitePlaceLocalizedIsIntegralClosure (K := K) (L := L) v
  let : Module.Finite 𝒪[C] 𝒪[E] :=
    chosenFinitePlaceLocalizedIntegerModuleFinite (K := K) (L := L) v
  let : IsNonarchimedeanLocalField.IsUnramifiedValuedExtension C E := hunram
  have hval :
      IsNonarchimedeanLocalField.valuationMap C
        (Additive.ofMul (finitePlaceLocalArtinInput v x)) = -1 :=
    finitePlaceLocalArtinInput_chosenLocalOrderSection_valuationMap v
  have hfrob :=
    LocalClassFieldTheory.abelianLocalArtinMonoidHom_eq_frobenius_zpow
      C E (finitePlaceLocalArtinInput v x)
  have hnorm :
      LocalClassFieldTheory.abelianLocalArtinMonoidHom C E
          (finitePlaceLocalArtinInput v x) =
        (arithmeticFrobeniusOfUnramifiedValuation C E)⁻¹ := by
    simpa only [hval, zpow_neg_one] using hfrob
  calc
    finitePlaceLocalArtinMonoidHom (K := K) (L := L) v w x =
        LocalClassFieldTheory.abelianLocalArtinMonoidHom C E
          (finitePlaceLocalArtinInput v x) := by
      rfl
    _ = (chosenFinitePlaceLocalArithmeticFrobenius
          (K := K) (L := L) v hunram)⁻¹ := by
      exact hnorm

end Reciprocity
end GlobalClassFieldTheory
