/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardSubgroupIntersection
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormContainment
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardNormSubgroupExact
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm
/-!
# Standard Lubin--Tate factors for finite local existence

The canonical standard Lubin--Tate level is already an intermediate field
of the fixed separable closure.  This module retains it as a named finite
abelian subextension, identifies its represented fixed field and norm
subgroup, and combines it with the canonical unramified factor.

Unlike the earlier transported Laurent-series construction, this source is
characteristic-independent.
-/

@[expose] public section

noncomputable
section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open ClassFormation
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Canonical standard Lubin--Tate level `m`, retained as a finite abelian
subextension of the fixed local separable closure. -/
noncomputable def standardLubinTateFiniteAbelianSubextension
    (m : ℕ) :
    FiniteAbelianSubextension (intrinsicAbstractBase K) := by
  let hπ := standardLocalFieldUniformizer_isUniformizer K
  let E := standardLubinTateLevelField hπ m
  letI : FiniteDimensional K E :=
    standardLubinTateLevelField_finiteDimensional hπ m
  letI : IsAbelianGalois K E :=
    standardLubinTateLevelField_isAbelianGalois
      (standardLocalField K) hπ m
  exact
    finiteAbelianAbstractExtensionOfEmbedding K E E.val

/-- The concrete standard level is base-linearly equivalent to the fixed
field represented by its named finite abelian subextension. -/
noncomputable def standardLubinTateFiniteAbelianSubextensionFixedFieldEquiv
    (m : ℕ) :
    let hπ := standardLocalFieldUniformizer_isUniformizer K
    let E := standardLubinTateLevelField hπ m
    E ≃ₐ[K]
      abstractFixedField K (SeparableClosure K)
        (standardLubinTateFiniteAbelianSubextension K m).field := by
  let hπ := standardLocalFieldUniformizer_isUniformizer K
  let E := standardLubinTateLevelField hπ m
  letI : FiniteDimensional K E :=
    standardLubinTateLevelField_finiteDimensional hπ m
  letI : IsAbelianGalois K E :=
    standardLubinTateLevelField_isAbelianGalois
      (standardLocalField K) hπ m
  let i : E →ₐ[K] SeparableClosure K := E.val
  let T := standardLubinTateFiniteAbelianSubextension K m
  have hfixed :
      abstractFixedField K (SeparableClosure K) T.field =
        finiteGaloisFieldRangeOfEmbedding K E i := by
    change
      IntermediateField.fixedField
          (finiteGaloisFieldRangeOfEmbedding K E i).fixingSubgroup =
        finiteGaloisFieldRangeOfEmbedding K E i
    exact
      InfiniteGalois.fixedField_fixingSubgroup
        (finiteGaloisFieldRangeOfEmbedding K E i)
  rw [hfixed]
  exact finiteGaloisFieldRangeEquivOfEmbedding K E i

/-- The named standard level has exactly the canonical normalized
uniformizer/principal-unit norm subgroup. -/
theorem
    standardLubinTateFiniteAbelianSubextension_normSubgroup_map_eq
    (m : ℕ) :
    let T := standardLubinTateFiniteAbelianSubextension K m
    (T.normSubgroup (intrinsicAbsoluteUnits K)).map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
      (LocalFieldTheory.uniformizerPrincipalSubgroup K
        (inverseIntegerRingUniformizerFieldUnit K) 1 (m + 1)).toAddSubgroup := by
  let hπ := standardLocalFieldUniformizer_isUniformizer K
  let E := standardLubinTateLevelField hπ m
  let : FiniteDimensional K E :=
    standardLubinTateLevelField_finiteDimensional hπ m
  let : IsAbelianGalois K E :=
    standardLubinTateLevelField_isAbelianGalois
      (standardLocalField K) hπ m
  let i : E →ₐ[K] SeparableClosure K := E.val
  let T := standardLubinTateFiniteAbelianSubextension K m
  calc
    (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
        CyclicCohomology.additiveNormSubgroup K E := by
      simpa [T, standardLubinTateFiniteAbelianSubextension, i, E, hπ] using
        map_finiteAbelianAbstractExtension_normSubgroup_eq K E i
    _ =
        (LocalFieldTheory.uniformizerPrincipalSubgroup K
          (inverseIntegerRingUniformizerFieldUnit K)
          1 (m + 1)).toAddSubgroup := by
      simpa [CyclicCohomology.additiveNormSubgroup, E, hπ,
        standardLubinTateNormSubgroup] using
          congrArg Subgroup.toAddSubgroup
            (standardLubinTateCanonicalNormSubgroup_eq_normalizedUniformizerPrincipalSubgroup
              K m)

/-- The characteristic-independent standard finite abelian compositum:
the canonical unramified degree-`d` factor together with standard
Lubin--Tate level `n - 1`. -/
noncomputable def standardLubinTateFiniteAbelianCompositum
    (d n : ℕ) (hd : 0 < d) :
    FiniteAbelianSubextension (intrinsicAbstractBase K) :=
  (localFiniteUnramifiedAbelianSubextension K d hd).compositum
    (standardLubinTateFiniteAbelianSubextension K (n - 1))

/-- The fixed field represented by the standard compositum is the
compositum of its unramified and Lubin--Tate fixed fields. -/
theorem standardLubinTateFiniteAbelianCompositum_fixedField_eq_sup
    (d n : ℕ) (hd : 0 < d) :
    abstractFixedField K (SeparableClosure K)
        (standardLubinTateFiniteAbelianCompositum K d n hd).field =
      abstractFixedField K (SeparableClosure K)
          (localFiniteUnramifiedAbelianSubextension K d hd).field ⊔
        abstractFixedField K (SeparableClosure K)
          (standardLubinTateFiniteAbelianSubextension K (n - 1)).field := by
  simpa [standardLubinTateFiniteAbelianCompositum] using
    (finiteAbelianSubextension_compositum_fixedField K
      (localFiniteUnramifiedAbelianSubextension K d hd)
      (standardLubinTateFiniteAbelianSubextension K (n - 1)))

/-- If an overgroup contains the canonical standard subgroup
`⟨ϖ^d⟩ U_K^n`, the ordinary norm subgroup of the standard unramified /
Lubin--Tate compositum is contained in that overgroup. -/
theorem standardLubinTateFiniteAbelianCompositum_nativeNormSubgroup_le
    (H : Subgroup Kˣ) (d n : ℕ)
    (hd : 0 < d) (hn : 0 < n)
    (hstandard :
      LocalFieldTheory.uniformizerPrincipalSubgroup K
          (inverseIntegerRingUniformizerFieldUnit K) d n ≤
        H) :
    finiteAbelianNormSubgroup K
        (standardLubinTateFiniteAbelianCompositum K d n hd) ≤
      H := by
  let ϖ := inverseIntegerRingUniformizerFieldUnit K
  let U := localFiniteUnramifiedAbelianSubextension K d hd
  let T := standardLubinTateFiniteAbelianSubextension K (n - 1)
  have hϖ : valuationMap K (Additive.ofMul ϖ) = 1 := by
    rw [valuationMap_apply]
    simpa only [ϖ] using v_inverseIntegerRingUniformizerFieldUnit K
  have hUle :
      (U.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (unramifiedNormSubgroup K d).toAddSubgroup := by
    simpa only [U] using
      localFiniteUnramifiedAbelianSubextension_normSubgroup_map_le
        K d hd
  have hTle :
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup := by
    have hT :=
      standardLubinTateFiniteAbelianSubextension_normSubgroup_map_eq
        K (n - 1)
    simpa only [T, ϖ, Nat.sub_add_cancel hn] using hT.le
  have hP :
      (U.compositum T).normSubgroup (intrinsicAbsoluteUnits K) ≤
        H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom :=
    finiteAbelianCompositum_normSubgroup_le_of_standard
      K H ϖ d n hϖ hstandard U T hUle hTle
  simpa [standardLubinTateFiniteAbelianCompositum, U, T] using
    (finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map
      K (U.compositum T) H hP)

end LocalClassFieldTheory

end
