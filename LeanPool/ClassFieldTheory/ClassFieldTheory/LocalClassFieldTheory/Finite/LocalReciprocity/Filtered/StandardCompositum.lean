/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.AbstractUnramified
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Compositum
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardFixedFieldComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardLubinTate
/-!
# Filtered reciprocity for the standard finite abelian compositum

The characteristic-independent standard compositum consists of the
canonical unramified factor and a canonical standard Lubin--Tate factor.
At nonnegative indices the unramified factor contributes trivially, while
filtered reciprocity holds on the Lubin--Tate factor.  Joint injectivity of
the two restriction maps gives the equality on their compositum.
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open RamificationTheory.LocalField
open LubinTate

open LocalClassFieldTheory
open LocalFieldTheory

/-- Real filtered local reciprocity for the fixed field represented by the
characteristic-independent standard finite abelian compositum. -/
theorem standardLubinTateFiniteAbelianCompositum_filteredLocalReciprocity
    (K : Type) [Field K]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d n : ℕ) (hd : 0 < d)
    (t : ℝ) (ht : 0 ≤ t) :
    let P := standardLubinTateFiniteAbelianCompositum K d n hd
    let F :=
      abstractFixedField K (SeparableClosure K) P.field
    letI : FiniteDimensional K F :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) P.field
          (finiteAbelianSubextension_finite_over_absoluteBase K P)
    letI : IsAbelianGalois K F :=
      finiteAbelianSubextension_fixedField_isAbelianGalois K P
    artinPrincipalUnitStepGroup K F t =
      localUpperRamificationGroup K F t := by
  let U := localFiniteUnramifiedAbelianSubextension K d hd
  let H₁ := localFiniteUnramifiedAbstractField K d hd
  let T := standardLubinTateFiniteAbelianSubextension K (n - 1)
  let P := standardLubinTateFiniteAbelianCompositum K d n hd
  let E₁ :=
    abstractFixedField K (SeparableClosure K) H₁.field
  let E₂ :=
    abstractFixedField K (SeparableClosure K) T.field
  let F :=
    abstractFixedField K (SeparableClosure K) P.field
  let : FiniteDimensional K E₁ :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H₁.field H₁.finite
  let : FiniteDimensional K E₂ :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) T.field
        (finiteAbelianSubextension_finite_over_absoluteBase K T)
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) P.field
        (finiteAbelianSubextension_finite_over_absoluteBase K P)
  let : IsAbelianGalois K E₁ :=
    by
      change IsAbelianGalois K
        (abstractFixedField K (SeparableClosure K) U.field)
      exact finiteAbelianSubextension_fixedField_isAbelianGalois K U
  let : IsAbelianGalois K E₂ :=
    finiteAbelianSubextension_fixedField_isAbelianGalois K T
  let : IsAbelianGalois K F :=
    finiteAbelianSubextension_fixedField_isAbelianGalois K P
  have hsup : E₁ ⊔ E₂ = F := by
    simpa only [E₁, E₂, F, H₁, U, T, P,
      localFiniteUnramifiedAbstractField_field] using
      (standardLubinTateFiniteAbelianCompositum_fixedField_eq_sup
        K d n hd).symm
  have hE₁ : E₁ ≤ F := by
    rw [← hsup]
    exact le_sup_left
  have hE₂ : E₂ ≤ F := by
    rw [← hsup]
    exact le_sup_right
  have hArtin₁ :
      artinPrincipalUnitStepGroup K E₁ t = ⊥ := by
    simpa only [E₁, H₁] using
      artinPrincipalUnitStepGroup_finiteUnramifiedAbelianExtension_eq_bot
        K d hd t
  have hUpper₁ :
      localUpperRamificationGroup K E₁ t = ⊥ := by
    simpa only [E₁, H₁] using
      localUpperRamificationGroup_finiteUnramifiedAbelianExtension_eq_bot
        K d hd t ht
  have hfiltered₂ :
      artinPrincipalUnitStepGroup K E₂ t =
        localUpperRamificationGroup K E₂ t := by
    simpa only [E₂, T] using
      standardLubinTateFiniteAbelianSubextension_filteredLocalReciprocity
        K (n - 1) t ht
  exact
    filteredLocalReciprocity_of_compositum
      K E₁ E₂ F hE₁ hE₂ hsup t hArtin₁ hUpper₁ hfiltered₂

end LocalClassFieldTheory

end
