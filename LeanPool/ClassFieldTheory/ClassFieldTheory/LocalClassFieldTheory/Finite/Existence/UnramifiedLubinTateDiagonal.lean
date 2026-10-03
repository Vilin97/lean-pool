/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.LubinTateUniformizerDiagonal
/-!
# The unramified--Lubin--Tate diagonal field

This module is the standard-uniformizer specialization of
`LubinTateUniformizerDiagonal`.  The construction itself is carried out for
an arbitrary explicit uniformizer there; specializing it here keeps the
canonical API definitionally aligned with that reusable construction.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open LubinTate

/-- With the canonical spectral valuation, a standard Lubin--Tate level has
residue degree one over the topology-first local base field. -/
theorem standardLubinTateLevel_spectral_inertiaDeg_eq_one
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    let hπ := standardLocalFieldUniformizer_isUniformizer K
    let T := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K T :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : NontriviallyNormedField T :=
      finiteExtensionSpectralNormedField K T
    letI : ValuativeRel T :=
      finiteExtensionSpectralValuativeRel K T
    letI : IsNonarchimedeanLocalField T :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K T
    letI : Valuation.HasExtension (ValuativeRel.valuation K)
        (ValuativeRel.valuation T) :=
      finiteExtensionSpectralValuation_hasExtension K T
    letI :
        (LocalFieldTheory.localCompleteDVF K).valuation.HasExtension
          (LocalFieldTheory.localCompleteDVF T).valuation :=
      localCompleteDVFValuation_hasExtension K T
    (LocalFieldTheory.localCompleteDVF T).maximalIdeal.inertiaDeg
      (LocalFieldTheory.localCompleteDVF K).valuationSubring = 1 := by
  simpa only using lubinTateLevel_spectral_inertiaDeg_eq_one K
    (standardLocalFieldUniformizer_isUniformizer K) n

/-- The canonical degree-`d` unramified field and the standard Lubin--Tate
level have trivial intersection in the chosen separable closure. -/
theorem localFiniteUnramifiedField_inf_standardLubinTateLevelField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) (n : ℕ) :
    localFiniteUnramifiedField K d hd ⊓
        standardLubinTateLevelField
          (standardLocalFieldUniformizer_isUniformizer K) n =
      ⊥ := by
  simpa only using localFiniteUnramifiedField_inf_lubinTateLevelField K
    (standardLocalFieldUniformizer_isUniformizer K) d hd n

/-- The canonical unramified field and standard Lubin--Tate level are
linearly disjoint over the local base field. -/
theorem localFiniteUnramifiedField_linearDisjoint_standardLubinTateLevelField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (localFiniteUnramifiedField K d hd).LinearDisjoint
      (standardLubinTateLevelField
        (standardLocalFieldUniformizer_isUniformizer K) n) := by
  simpa only using
    localFiniteUnramifiedField_linearDisjoint_lubinTateLevelField K
      (standardLocalFieldUniformizer_isUniformizer K) d hd n

/-- The standard-uniformizer instance of the unramified--Lubin--Tate
diagonal compositum. -/
abbrev standardLubinTateDiagonalCompositumField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    IntermediateField K (SeparableClosure K) :=
  lubinTateUniformizerDiagonalCompositumField K
    (standardLocalFieldUniformizer_isUniformizer K) n u

/-- The standard diagonal compositum is finite over the base field. -/
theorem standardLubinTateDiagonalCompositumField_finiteDimensional
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    FiniteDimensional K
      (standardLubinTateDiagonalCompositumField K n u) := by
  simpa only using
    lubinTateUniformizerDiagonalCompositumField_finiteDimensional K
      (standardLocalFieldUniformizer_isUniformizer K) n u

/-- The standard diagonal compositum is Galois over the base field. -/
theorem standardLubinTateDiagonalCompositumField_isGalois
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    IsGalois K (standardLubinTateDiagonalCompositumField K n u) := by
  simpa only using lubinTateUniformizerDiagonalCompositumField_isGalois K
    (standardLocalFieldUniformizer_isUniformizer K) n u

/-- The standard-uniformizer diagonal automorphism, restricting to arithmetic
Frobenius on the unramified factor and inverse unit action on the level. -/
abbrev standardLubinTateDiagonalAutomorphism
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    Gal((standardLubinTateDiagonalCompositumField K n u)/K) :=
  lubinTateUniformizerDiagonalAutomorphism K
    (standardLocalFieldUniformizer_isUniformizer K) n u

/-- The field fixed by the standard-uniformizer diagonal automorphism. -/
abbrev standardLubinTateDiagonalFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    IntermediateField K
      (standardLubinTateDiagonalCompositumField K n u) :=
  lubinTateUniformizerDiagonalFixedField K
    (standardLocalFieldUniformizer_isUniformizer K) n u

/-- The standard diagonal fixed field has the degree of its Lubin--Tate
level; the auxiliary unramified factor disappears after taking fixed points. -/
theorem standardLubinTateDiagonalFixedField_finrank
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ) (u : (standardLocalField K).valuationSubringˣ) :
    Module.finrank K (standardLubinTateDiagonalFixedField K n u) =
      Module.finrank K
        (standardLubinTateLevelField
          (standardLocalFieldUniformizer_isUniformizer K) n) := by
  simpa only using lubinTateUniformizerDiagonalFixedField_finrank K
    (standardLocalFieldUniformizer_isUniformizer K) n u

end LocalClassFieldTheory

end
