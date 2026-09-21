/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Comparison of base and coefficient localizations

For an `R`-algebra `C`, localizing a `C`-module at the image of a submonoid
`S ≤ R` agrees with localizing it as an `R`-module at `S`.
-/

namespace AlgebraicAnalysis.BaseLocalizationModuleComparison

noncomputable section

variable {R C E : Type*}
variable [CommRing R] [CommRing C] [Algebra R C]
variable [AddCommGroup E] [Module R E] [Module C E]
variable [IsScalarTower R C E]

variable (S : Submonoid R)

local notation "SC" => Algebra.algebraMapSubmonoid C S

/-- The coefficient-algebra denominator induced by a base denominator. -/
def coefficientDenominator (s : S) : SC :=
  ⟨algebraMap R C s, ⟨s, s.property, rfl⟩⟩

local instance : IsScalarTower R C (LocalizedModule SC E) where
  smul_assoc r c p := by
    induction p with
    | _ m s =>
      simp [LocalizedModule.smul'_mk, Algebra.smul_def, mul_smul,
        IsScalarTower.algebraMap_smul C]

theorem localizedModule_isLocalizedOverBase :
    IsLocalizedModule S
      ((LocalizedModule.mkLinearMap SC E).restrictScalars R) := by
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid C S)
      (LocalizedModule.mkLinearMap SC E) := by
    infer_instance
  exact IsLocalizedModule.restrictScalars S (LocalizedModule.mkLinearMap SC E)
theorem localizedModule_isLocalizedOverCoefficient :
    IsLocalizedModule SC (LocalizedModule.mkLinearMap SC E) := by
  infer_instance

/-- The localized coefficient module viewed over the base localization. -/
local instance localizedBaseModule :
    Module (Localization S) (LocalizedModule SC E) :=
  Module.compHom _ (algebraMap (Localization S) (Localization SC))

local instance : IsScalarTower R (Localization S) (LocalizedModule SC E) := by
  constructor
  intro r x p
  simp only [Algebra.smul_def]
  rw [mul_smul]
  change algebraMap (Localization S) (Localization SC)
      (algebraMap R (Localization S) r) •
        algebraMap (Localization S) (Localization SC) x • p = r •
        algebraMap (Localization S) (Localization SC) x • p
  rw [← IsScalarTower.algebraMap_apply R (Localization S) (Localization SC),
    IsScalarTower.algebraMap_smul (Localization SC)]

/-- The canonical equivalence between base and coefficient localizations. -/
noncomputable def localizedModuleComparison :
    LocalizedModule S E ≃ₗ[Localization S] LocalizedModule SC E :=
  let : IsLocalizedModule S
      ((LocalizedModule.mkLinearMap SC E).restrictScalars R) :=
    localizedModule_isLocalizedOverBase S
  (IsLocalizedModule.linearEquiv S
      (LocalizedModule.mkLinearMap S E)
      ((LocalizedModule.mkLinearMap SC E).restrictScalars R)).extendScalarsOfIsLocalization
        S (Localization S)

@[simp] theorem localizedModuleComparison_mkLinearMap (m : E) :
    localizedModuleComparison S (LocalizedModule.mkLinearMap S E m) =
      LocalizedModule.mkLinearMap SC E m := by
  let : IsLocalizedModule S
      ((LocalizedModule.mkLinearMap SC E).restrictScalars R) :=
    localizedModule_isLocalizedOverBase S
  exact IsLocalizedModule.linearEquiv_apply S
    (LocalizedModule.mkLinearMap S E)
    ((LocalizedModule.mkLinearMap SC E).restrictScalars R) m

@[simp] theorem localizedModuleComparison_mk (m : E) (s : S) :
    localizedModuleComparison S (LocalizedModule.mk m s) =
      (LocalizedModule.mk m (coefficientDenominator (C := C) S s) :
        LocalizedModule SC E) := by
  have h : LocalizedModule.mk m s =
      Localization.mk (1 : R) s • LocalizedModule.mkLinearMap S E m := by
    rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_smul_mk]
    simp
  rw [h, map_smul, localizedModuleComparison_mkLinearMap]
  change algebraMap (Localization S) (Localization SC) (Localization.mk 1 s) •
      (LocalizedModule.mk m (1 : SC) : LocalizedModule SC E) = _
  rw [Localization.mk_eq_mk',
    IsLocalization.algebraMap_mk' (R := R) (S := C)
      (Rₘ := Localization S) (Sₘ := Localization SC)]
  have hs : (⟨algebraMap R C s,
      Algebra.mem_algebraMapSubmonoid_of_mem s⟩ : SC) =
      coefficientDenominator (C := C) S s := Subtype.ext rfl
  rw [map_one, hs]
  rw [← Localization.mk_eq_mk', LocalizedModule.mk_smul_mk]
  simp

theorem localizedModuleComparison_natural
    {F : Type*} [AddCommGroup F] [Module R F] [Module C F]
    [IsScalarTower R C F] (f : E →ₗ[C] F) (x : LocalizedModule S E) :
    localizedModuleComparison S
        (LocalizedModule.map S (f.restrictScalars R) x) =
      LocalizedModule.map SC f (localizedModuleComparison S x) := by
  induction x with
  | _ m s => simp

end

end AlgebraicAnalysis.BaseLocalizationModuleComparison
