/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.Norm
/-!
# Local norms at an unramified chosen finite place

This file proves that the concrete adic integer units lie in the actual local
norm subgroup of the chosen localized completion.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- At a chosen finite place which is unramified in `L`, every concrete
adic integer unit is an actual norm from the chosen localization. -/
theorem adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
    (v₀ : HeightOneSpectrum (𝓞 K))
    (hunram :
      ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v₀) :
    (v₀.adicCompletionIntegers K).units ≤
      chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v₀ := by
  let vK := HeightOneSpectrum.adicAbv K v₀
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v₀
  let :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        vK.Completion E := by
    simpa [ChosenFinitePlaceIsUnramified] using hunram
  intro x hx
  let e :=
    finitePlaceCompletionUnitsContinuousMulEquiv v₀
  let x₀ : vK.Completionˣ := e.symm x
  have hx₀map : e x₀ = x :=
    e.apply_symm_apply x
  rw [Submonoid.mem_units_iff] at hx
  have hx₀norm :
      ‖(x₀ : vK.Completion)‖ ≤ 1 := by
    have hval :=
      congrArg
        (fun q : (v₀.adicCompletion K)ˣ =>
          (q : v₀.adicCompletion K)) hx₀map
    have hnorm :
        ‖finitePlaceCompletionRingHom v₀
            (x₀ : vK.Completion)‖ =
          ‖(x₀ : vK.Completion)‖ :=
      (finitePlaceCompletionRingHom_isometry v₀).norm_map_of_map_zero
        (map_zero (finitePlaceCompletionRingHom v₀)) _
    rw [← hnorm]
    rw [show finitePlaceCompletionRingHom v₀
          (x₀ : vK.Completion) = (x : v₀.adicCompletion K) by
      exact hval]
    exact norm_le_one_of_mem_adicCompletionIntegers v₀ hx.1
  have hx₀invnorm :
      ‖((x₀⁻¹ : vK.Completionˣ) : vK.Completion)‖ ≤ 1 := by
    have hval :=
      congrArg
        (fun q : (v₀.adicCompletion K)ˣ =>
          (q : v₀.adicCompletion K))
        (congrArg Inv.inv hx₀map)
    have hnorm :
        ‖finitePlaceCompletionRingHom v₀
            ((x₀⁻¹ : vK.Completionˣ) : vK.Completion)‖ =
          ‖((x₀⁻¹ : vK.Completionˣ) : vK.Completion)‖ :=
      (finitePlaceCompletionRingHom_isometry v₀).norm_map_of_map_zero
        (map_zero (finitePlaceCompletionRingHom v₀)) _
    rw [← hnorm]
    rw [show finitePlaceCompletionRingHom v₀
          ((x₀⁻¹ : vK.Completionˣ) : vK.Completion) =
        ((x⁻¹ : (v₀.adicCompletion K)ˣ) :
          v₀.adicCompletion K) by
      exact hval]
    exact norm_le_one_of_mem_adicCompletionIntegers v₀ hx.2
  have hBaseMem (a : vK.Completion) :
      a ∈ 𝒪[vK.Completion] ↔ ‖a‖ ≤ 1 := by
    simpa [vK] using
      (finitePlaceCompletion_mem_integers_iff_norm_le_one
        vK (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) a)
  let x₀O : 𝒪[vK.Completion]ˣ :=
    { val := ⟨x₀, (hBaseMem (x₀ : vK.Completion)).2 hx₀norm⟩
      inv :=
        ⟨x₀⁻¹,
          by
            simpa using
              (hBaseMem
                ((x₀⁻¹ : vK.Completionˣ) :
                  vK.Completion)).2 hx₀invnorm⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  have hx₀O :
      integerUnitsToFieldUnits vK.Completion x₀O = x₀ := by
    apply Units.ext
    rfl
  obtain ⟨yO, hyO⟩ :=
    LocalClassFieldTheory.normIntegerUnits_surjective_unramified_of_isIntegralClosure
      vK.Completion E x₀O
  have hx₀Norm :
      x₀ ∈ localNormSubgroup vK.Completion E := by
    rw [← hx₀O, ← hyO,
      LocalClassFieldTheory.normIntegerUnits_to_fieldUnits]
    exact ⟨integerUnitsToFieldUnits E yO, rfl⟩
  change
    x ∈
      (localNormSubgroup vK.Completion E).map e.toMonoidHom
  exact ⟨x₀, hx₀Norm, hx₀map⟩
