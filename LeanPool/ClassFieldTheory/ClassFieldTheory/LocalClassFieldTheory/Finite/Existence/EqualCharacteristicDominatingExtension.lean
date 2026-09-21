/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.EqualCharacteristic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
/-!
# Equal-characteristic dominating extensions

Every finite abelian extension of a positive-characteristic local field
embeds into the fixed field represented by a finite abelian compositum of an
unramified factor and a transported Lubin--Tate factor.  This is the
source-producing field extension used for descent of filtered reciprocity.
-/

noncomputable section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open ClassFormation CyclicCohomology
open KummerTheory
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- Source-producing form retaining the uniformizer, the unramified degree,
the Lubin--Tate level, and the named standard compositum. -/
theorem exists_equalCharacteristicFiniteAbelianDominatingStandardCompositum
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ (ϖ : Kˣ) (d n : ℕ)
        (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
        (hd : 0 < d) (_hn : 0 < n),
      Nonempty
        (L →ₐ[K]
          abstractFixedField K (SeparableClosure K)
            (equalCharacteristicStandardFiniteAbelianCompositum
              K p ϖ hϖ d n hd).field) := by
  let ϖ := inverseIntegerRingUniformizerFieldUnit K
  have hϖ : valuationMap K (Additive.ofMul ϖ) = 1 := by
    rw [valuationMap_apply]
    exact v_inverseIntegerRingUniformizerFieldUnit K
  obtain ⟨d, n, hd, hn, hstandard⟩ :=
    exists_uniformizerPrincipalSubgroup_le_normSubgroup K L ϖ
  let P :=
    equalCharacteristicStandardFiniteAbelianCompositum
      K p ϖ hϖ d n hd
  have hP :
      finiteAbelianNormSubgroup K P ≤ localNormSubgroup K L := by
    simpa [P] using
      (equalCharacteristicStandardFiniteAbelianCompositum_nativeNormSubgroup_le
        K p (localNormSubgroup K L) ϖ d n hϖ hd hn hstandard)
  refine ⟨ϖ, d, n, hϖ, hd, hn, ?_⟩
  let E := abstractFixedField K (SeparableClosure K) P.field
  let : Finite
      ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
        extensionSubgroup
          (baseField (intrinsicAbsoluteGalois K)) P.field
          (le_baseField P.field)) :=
    finiteAbelianSubextension_finite_over_absoluteBase K P
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) P.field inferInstance
  let : IsAbelianGalois K E :=
    finiteAbelianSubextension_fixedField_isAbelianGalois K P
  apply nonempty_algHom_of_normSubgroup_le K L E
  simpa [E, P, finiteAbelianNormSubgroup] using hP

/-- A finite abelian extension of an equal-characteristic local field embeds
into a finite abelian fixed field whose norm subgroup is obtained from the
standard unramified/Lubin--Tate construction. -/
theorem exists_equalCharacteristicFiniteAbelianDominatingFixedField
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ P : FiniteAbelianSubextension (intrinsicAbstractBase K),
      Nonempty
        (L →ₐ[K]
          abstractFixedField K (SeparableClosure K) P.field) := by
  obtain ⟨ϖ, d, n, hϖ, hd, _hn, hEmbed⟩ :=
    exists_equalCharacteristicFiniteAbelianDominatingStandardCompositum
      K L p
  exact
    ⟨equalCharacteristicStandardFiniteAbelianCompositum
        K p ϖ hϖ d n hd,
      hEmbed⟩

end LocalClassFieldTheory
