/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.LocalizationDensity
/-!
# Localization of inertia and ramification groups

This file packages the decomposition-group equivalence of the localization and decomposition
  comparison
as equivalences of the valuation-subring decomposition, inertia, and
ramification groups.  The difficult global-to-local implications use density
of `L` in the algebraic localization, proved in
`RamificationTheory.HilbertRamification.LocalizationDensity`.
-/

@[expose] public section

noncomputable
section

universe u v

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations
open scoped Pointwise

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [IsGalois K L]

section

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
  (w : AbsoluteValueExtension vK L)
  (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1)

/-- The completion at the extended absolute value is a `K`-algebra through the original
extension. -/
local instance irCompletionBaseAlgebra : Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := K) w.1

/-- The action of `K` on the extended completion is induced by its completion algebra. -/
local instance irCompletionBaseSMul : SMul K w.1.Completion :=
  (AbsoluteValue.extensionCompletionAlgebra (K := K) w.1).toSMul

/-- The completion at the extended absolute value is an algebra over the completed base field. -/
local instance irCompletionAlgebra : Algebra vK.Completion w.1.Completion :=
  AbsoluteValue.completionAlgebra vK w.1 w.2

/-- The algebraic localization `L K_v` occurring in the localization and decomposition
comparison. -/
abbrev localizationRamificationGroupsLocalization :
    IntermediateField vK.Completion w.1.Completion :=
  AbsoluteValue.algebraicLocalization vK w.1 w.2

/-- The valuation subring of `L` defined by `w`. -/
abbrev absoluteValueExtensionValuationSubring :
    _root_.ValuationSubring L :=
  absoluteValueValuationSubring w.1 hw

/-- The valuation subring of the algebraic localization defined by the
extended absolute value. -/
abbrev algebraicLocalizationValuationSubring :
    _root_.ValuationSubring (localizationRamificationGroupsLocalization vK w) :=
  absoluteValueValuationSubring
    (AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2)
    (algebraicLocalizationDensity_localization_nonarchimedean vK w hw)

include hvK

omit [IsGalois K L] in
private theorem mem_extensionValuationSubring_smul
    (sigma : absoluteValueDecompositionGroup K w.1) :
    (sigma : L ≃ₐ[K] L) •
        absoluteValueExtensionValuationSubring vK w hw =
      absoluteValueExtensionValuationSubring vK w hw := by
  ext x
  rw [_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    mem_absoluteValueValuationSubring_iff,
    mem_absoluteValueValuationSubring_iff]
  have h := absoluteValueDecompositionGroup_preserves_absoluteValue
    vK hvK w sigma ((sigma : L ≃ₐ[K] L)⁻¹ x)
  calc
    w.1 ((sigma : L ≃ₐ[K] L)⁻¹ x) ≤ 1 ↔
        w.1 ((sigma : L ≃ₐ[K] L)
          ((sigma : L ≃ₐ[K] L)⁻¹ x)) ≤ 1 := by rw [h]
    _ ↔ w.1 x ≤ 1 := by simp

/-- The chosen-valuation decomposition group is the valuation-subring decomposition
group attached to the same absolute value. -/
def localizationRamificationGroupsAbsoluteValueDecompositionGroupEquiv :
    absoluteValueDecompositionGroup K w.1 ≃*
      RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
        (absoluteValueExtensionValuationSubring vK w hw) where
  toFun sigma :=
    ⟨(sigma : L ≃ₐ[K] L),
      by exact mem_extensionValuationSubring_smul vK (hvK := hvK) w hw sigma⟩
  invFun sigma := by
    refine ⟨(sigma : L ≃ₐ[K] L), ?_⟩
    intro x
    rw [← algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one w.1 hw,
      ← algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one w.1 hw]
    rw [_root_.ValuationSubring.mem_nonunits_iff_or,
      _root_.ValuationSubring.mem_nonunits_iff_or]
    have hmem (y : L) :
        (sigma : L ≃ₐ[K] L) y ∈
            absoluteValueExtensionValuationSubring vK w hw ↔
          y ∈ absoluteValueExtensionValuationSubring vK w hw := by
      have h := congrArg
        (fun A : _root_.ValuationSubring L ↦
          (sigma : L ≃ₐ[K] L) y ∈ A) sigma.property
      have h' :
          (y ∈ absoluteValueExtensionValuationSubring vK w hw) =
            ((sigma : L ≃ₐ[K] L) y ∈
              absoluteValueExtensionValuationSubring vK w hw) := by
        simpa [_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
          AlgEquiv.smul_def] using h
      exact Eq.to_iff h'.symm
    have hinv :
        ((sigma : L ≃ₐ[K] L) x)⁻¹ ∈
            absoluteValueExtensionValuationSubring vK w hw ↔
          x⁻¹ ∈ absoluteValueExtensionValuationSubring vK w hw := by
      simpa only [map_inv₀] using hmem x⁻¹
    constructor
    · rintro (hzero | hnot)
      · exact Or.inl ((sigma : L ≃ₐ[K] L).injective (by simpa using hzero))
      · exact Or.inr (fun hx ↦ hnot (hinv.mpr hx))
    · rintro (hzero | hnot)
      · subst x
        exact Or.inl (map_zero (sigma : L ≃ₐ[K] L))
      · exact Or.inr (fun hx ↦ hnot (hinv.mp hx))
  left_inv sigma := by
    apply Subtype.ext
    rfl
  right_inv sigma := by
    apply Subtype.ext
    rfl
  map_mul' sigma tau := by
    apply Subtype.ext
    rfl

private theorem local_mem_localizationValuationSubring_smul
    (tau : localizationRamificationGroupsLocalization vK w ≃ₐ[vK.Completion]
      localizationRamificationGroupsLocalization vK w) :
    tau • algebraicLocalizationValuationSubring vK w hw =
      algebraicLocalizationValuationSubring vK w hw := by
  ext z
  rw [_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    mem_absoluteValueValuationSubring_iff,
    mem_absoluteValueValuationSubring_iff]
  have h := localizationAbsoluteValue_algEquiv vK hvK w tau (tau⁻¹ z)
  calc
    AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2 (tau⁻¹ z) ≤ 1 ↔
        AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (tau (tau⁻¹ z)) ≤ 1 := by rw [h]
    _ ↔ AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2 z ≤ 1 := by simp

/-- Every automorphism of the localization over `K_v` belongs to its
valuation-subring decomposition group. -/
def localizationRamificationGroupsLocalDecompositionGroupEquiv :
    (localizationRamificationGroupsLocalization vK w ≃ₐ[vK.Completion]
      localizationRamificationGroupsLocalization vK w) ≃*
      RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup vK.Completion
        (algebraicLocalizationValuationSubring vK w hw) where
  toFun tau :=
    ⟨tau, local_mem_localizationValuationSubring_smul
      vK (hvK := hvK) w hw tau⟩
  invFun tau := tau
  left_inv tau := rfl
  right_inv tau := by
    apply Subtype.ext
    rfl
  map_mul' sigma tau := by
    apply Subtype.ext
    rfl

/-- The localization and decomposition comparison for valuation-subring decomposition groups. -/
def localizationRamificationGroupsValuationDecompositionGroupEquiv :
    RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
        (absoluteValueExtensionValuationSubring vK w hw) ≃*
      RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup vK.Completion
        (algebraicLocalizationValuationSubring vK w hw) :=
  (localizationRamificationGroupsAbsoluteValueDecompositionGroupEquiv
      vK (hvK := hvK) w hw).symm.trans
    ((decompositionGroupEquivAlgebraicLocalizationAut vK hvK w).trans
      (localizationRamificationGroupsLocalDecompositionGroupEquiv
        vK (hvK := hvK) w hw))

@[simp] theorem localizationRamificationGroups_valuationDecompositionGroupEquiv_toLocalization
    (sigma : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
      (absoluteValueExtensionValuationSubring vK w hw))
    (x : L) :
    (((localizationRamificationGroupsValuationDecompositionGroupEquiv
        vK (hvK := hvK) w hw sigma :
        RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup vK.Completion
          (algebraicLocalizationValuationSubring vK w hw)) :
        localizationRamificationGroupsLocalization vK w ≃ₐ[vK.Completion]
          localizationRamificationGroupsLocalization vK w)
      (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        ((sigma : L ≃ₐ[K] L) x) := by
  exact localizationRamificationGroups_decompositionGroupEquiv_toLocalization
    vK hvK w
    ((localizationRamificationGroupsAbsoluteValueDecompositionGroupEquiv
      vK (hvK := hvK) w hw).symm sigma) x

/-- The decomposition-group equivalence carries inertia precisely to
inertia.  The global-to-local implication is the residue-density argument;
the converse is restriction along `L → L K_v`. -/
theorem localizationRamificationGroups_valuationDecompositionGroupEquiv_mem_inertia_iff
    (sigma : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
      (absoluteValueExtensionValuationSubring vK w hw)) :
    localizationRamificationGroupsValuationDecompositionGroupEquiv
        vK (hvK := hvK) w hw sigma ∈
        RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup vK.Completion
          (algebraicLocalizationValuationSubring vK w hw) ↔
      sigma ∈ RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K
        (absoluteValueExtensionValuationSubring vK w hw) := by
  constructor
  · intro hsigma
    rw [ValuationSubring.mem_inertiaGroup_iff_sub_mem_nonunits]
    intro x
    rw [algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one]
    let xLocal : algebraicLocalizationValuationSubring vK w hw :=
      ⟨AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (x : L), by
        rw [mem_absoluteValueValuationSubring_iff,
          AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization]
        exact
          (mem_absoluteValueValuationSubring_iff
            w.1 hw (x : L)).mp x.property⟩
    have hlocalNonunit :=
      (ValuationSubring.mem_inertiaGroup_iff_sub_mem_nonunits
        (algebraicLocalizationValuationSubring vK w hw)
        (localizationRamificationGroupsValuationDecompositionGroupEquiv
          vK (hvK := hvK) w hw sigma)).mp hsigma xLocal
    have hlocal :
        AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (((localizationRamificationGroupsValuationDecompositionGroupEquiv
              vK (hvK := hvK) w hw sigma :
                RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup
                  vK.Completion
                  (algebraicLocalizationValuationSubring vK w hw)) :
              localizationRamificationGroupsLocalization vK w ≃ₐ[vK.Completion]
                localizationRamificationGroupsLocalization vK w)
            (xLocal : localizationRamificationGroupsLocalization vK w) -
              (xLocal : localizationRamificationGroupsLocalization vK w)) < 1 :=
      (algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one
        (AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2)
        (algebraicLocalizationDensity_localization_nonarchimedean vK w hw) _).mp hlocalNonunit
    calc
      w.1 (((sigma : L ≃ₐ[K] L) (x : L)) - (x : L)) =
          AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
            (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
              (((sigma : L ≃ₐ[K] L) (x : L)) - (x : L))) :=
        (AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 _).symm
      _ = AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (((localizationRamificationGroupsValuationDecompositionGroupEquiv
              vK (hvK := hvK) w hw sigma :
                RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup
                  vK.Completion
                  (algebraicLocalizationValuationSubring vK w hw)) :
              localizationRamificationGroupsLocalization vK w ≃ₐ[vK.Completion]
                localizationRamificationGroupsLocalization vK w)
            (xLocal : localizationRamificationGroupsLocalization vK w) -
              (xLocal : localizationRamificationGroupsLocalization vK w)) := by
        congr 1
        rw [map_sub,
          localizationRamificationGroups_valuationDecompositionGroupEquiv_toLocalization]
      _ < 1 := hlocal
  · intro hsigma
    apply algebraicLocalizationDensity_localization_mem_inertia_of_commutes vK w hvK hw
      (localizationRamificationGroupsValuationDecompositionGroupEquiv
        vK (hvK := hvK) w hw sigma) sigma
    · intro x
      exact localizationRamificationGroups_valuationDecompositionGroupEquiv_toLocalization
        vK hvK w hw sigma x
    · exact hsigma

/-- The localization and decomposition comparison for inertia groups. -/
def inertiaGroupEquivAlgebraicLocalization :
    RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K
        (absoluteValueExtensionValuationSubring vK w hw) ≃*
      RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup vK.Completion
        (algebraicLocalizationValuationSubring vK w hw) where
  toFun sigma :=
    ⟨localizationRamificationGroupsValuationDecompositionGroupEquiv
        vK (hvK := hvK) w hw sigma,
      (localizationRamificationGroups_valuationDecompositionGroupEquiv_mem_inertia_iff
        vK hvK w hw sigma).mpr sigma.property⟩
  invFun tau := by
    let sigma := (localizationRamificationGroupsValuationDecompositionGroupEquiv
      vK (hvK := hvK) w hw).symm
        (tau : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup
          vK.Completion
          (algebraicLocalizationValuationSubring vK w hw))
    refine ⟨sigma, ?_⟩
    apply (localizationRamificationGroups_valuationDecompositionGroupEquiv_mem_inertia_iff
      vK hvK w hw sigma).mp
    simp [sigma, tau.property]
  left_inv sigma := by
    apply Subtype.ext
    exact (localizationRamificationGroupsValuationDecompositionGroupEquiv
      vK (hvK := hvK) w hw).symm_apply_apply sigma
  right_inv tau := by
    apply Subtype.ext
    exact (localizationRamificationGroupsValuationDecompositionGroupEquiv
      vK (hvK := hvK) w hw).apply_symm_apply tau
  map_mul' sigma tau := by
    apply Subtype.ext
    exact map_mul (localizationRamificationGroupsValuationDecompositionGroupEquiv
      vK (hvK := hvK) w hw)
        (sigma : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
          (absoluteValueExtensionValuationSubring vK w hw))
        (tau : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
          (absoluteValueExtensionValuationSubring vK w hw))

@[simp] theorem localizationRamificationGroups_inertiaGroupEquiv_toLocalization
    (sigma : RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K
      (absoluteValueExtensionValuationSubring vK w hw))
    (x : L) :
    ((((inertiaGroupEquivAlgebraicLocalization vK hvK w hw sigma :
          RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup vK.Completion
            (algebraicLocalizationValuationSubring vK w hw)) :
          RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup vK.Completion
            (algebraicLocalizationValuationSubring vK w hw)) :
          localizationRamificationGroupsLocalization vK w ≃ₐ[vK.Completion]
            localizationRamificationGroupsLocalization vK w)
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        (((sigma : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
          (absoluteValueExtensionValuationSubring vK w hw)) :
            L ≃ₐ[K] L) x) :=
  localizationRamificationGroups_valuationDecompositionGroupEquiv_toLocalization
    vK hvK w hw sigma x

/-- The inertia-group equivalence carries ramification precisely to
ramification.  The global-to-local implication uses density modulo principal
units; the converse follows by restricting unit quotients. -/
theorem localizationRamificationGroups_inertiaGroupEquiv_mem_ramification_iff
    (sigma : RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K
      (absoluteValueExtensionValuationSubring vK w hw)) :
    inertiaGroupEquivAlgebraicLocalization vK hvK w hw sigma ∈
        RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup vK.Completion
          (algebraicLocalizationValuationSubring vK w hw) ↔
      sigma ∈ RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup K
        (absoluteValueExtensionValuationSubring vK w hw) := by
  constructor
  · intro hsigma
    rw [RamificationTheory.HilbertRamification.ValuationSubring.mem_ramificationGroup_iff]
    intro x
    rw [algebraicLocalizationDensity_mem_principalUnitGroup_iff_abs_lt_one]
    let j : L →+* localizationRamificationGroupsLocalization vK w :=
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
    let xLocal : (localizationRamificationGroupsLocalization vK w)ˣ := Units.map j x
    let sigmaGlobal : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
        (absoluteValueExtensionValuationSubring vK w hw) := sigma
    let sigmaLocal : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup
      vK.Completion
        (algebraicLocalizationValuationSubring vK w hw) :=
      inertiaGroupEquivAlgebraicLocalization vK hvK w hw sigma
    have hquotient :
        Units.map j
            (RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient K
              (absoluteValueExtensionValuationSubring vK w hw)
              sigmaGlobal x) =
          RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient
            vK.Completion
            (algebraicLocalizationValuationSubring vK w hw)
            sigmaLocal xLocal := by
      ext
      simp [RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient,
        sigmaGlobal,
        sigmaLocal, xLocal, j,
        localizationRamificationGroups_inertiaGroupEquiv_toLocalization]
    have hlocalPrincipal :=
      (RamificationTheory.HilbertRamification.ValuationSubring.mem_ramificationGroup_iff
        vK.Completion
        (algebraicLocalizationValuationSubring vK w hw)
        (inertiaGroupEquivAlgebraicLocalization vK hvK w hw sigma)).mp
          hsigma xLocal
    have hlocal :
        AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (((RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient
            vK.Completion
              (algebraicLocalizationValuationSubring vK w hw)
              sigmaLocal xLocal :
                (localizationRamificationGroupsLocalization vK w)ˣ) :
              localizationRamificationGroupsLocalization vK w) - 1) < 1 :=
      (algebraicLocalizationDensity_mem_principalUnitGroup_iff_abs_lt_one
        (AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2)
        (algebraicLocalizationDensity_localization_nonarchimedean vK w hw) _).mp
          hlocalPrincipal
    calc
      w.1 (((RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient K
          (absoluteValueExtensionValuationSubring vK w hw)
          sigmaGlobal x : Lˣ) : L) - 1) =
        AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (j (((RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient K
            (absoluteValueExtensionValuationSubring vK w hw)
            sigmaGlobal x : Lˣ) : L) - 1)) :=
        (AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 _).symm
      _ = AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
          (((RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient
            vK.Completion
              (algebraicLocalizationValuationSubring vK w hw)
              sigmaLocal xLocal :
                (localizationRamificationGroupsLocalization vK w)ˣ) :
              localizationRamificationGroupsLocalization vK w) - 1) := by
        congr 1
        rw [← hquotient]
        simp [j]
      _ < 1 := hlocal
  · intro hsigma
    apply algebraicLocalizationDensity_localization_mem_ramification_of_commutes
      vK w hvK hw
      (inertiaGroupEquivAlgebraicLocalization vK hvK w hw sigma) sigma
    · intro x
      exact localizationRamificationGroups_inertiaGroupEquiv_toLocalization
        vK hvK w hw sigma x
    · exact hsigma

/-- The localization and decomposition comparison for ramification groups. -/
def localizationRamificationGroupsRamificationGroupEquiv :
    RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup K
        (absoluteValueExtensionValuationSubring vK w hw) ≃*
      RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup vK.Completion
        (algebraicLocalizationValuationSubring vK w hw) where
  toFun sigma :=
    ⟨inertiaGroupEquivAlgebraicLocalization vK hvK w hw sigma,
      (localizationRamificationGroups_inertiaGroupEquiv_mem_ramification_iff
        vK hvK w hw sigma).mpr sigma.property⟩
  invFun tau := by
    let sigma := (inertiaGroupEquivAlgebraicLocalization vK hvK w hw).symm
      (tau : RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup vK.Completion
        (algebraicLocalizationValuationSubring vK w hw))
    refine ⟨sigma, ?_⟩
    apply (localizationRamificationGroups_inertiaGroupEquiv_mem_ramification_iff
      vK hvK w hw sigma).mp
    simp [sigma, tau.property]
  left_inv sigma := by
    apply Subtype.ext
    exact (inertiaGroupEquivAlgebraicLocalization
      vK hvK w hw).symm_apply_apply sigma
  right_inv tau := by
    apply Subtype.ext
    exact (inertiaGroupEquivAlgebraicLocalization
      vK hvK w hw).apply_symm_apply tau
  map_mul' sigma tau := by
    apply Subtype.ext
    exact map_mul (inertiaGroupEquivAlgebraicLocalization vK hvK w hw)
      (sigma : RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K
        (absoluteValueExtensionValuationSubring vK w hw))
      (tau : RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K
        (absoluteValueExtensionValuationSubring vK w hw))

@[simp] theorem localizationRamificationGroups_ramificationGroupEquiv_toLocalization
    (sigma : RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup K
      (absoluteValueExtensionValuationSubring vK w hw))
    (x : L) :
    ((show localizationRamificationGroupsLocalization vK w ≃ₐ[vK.Completion]
          localizationRamificationGroupsLocalization vK w from
        (((localizationRamificationGroupsRamificationGroupEquiv vK hvK w hw sigma :
            RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup vK.Completion
              (algebraicLocalizationValuationSubring vK w hw)) :
            RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup vK.Completion
              (algebraicLocalizationValuationSubring vK w hw)) :
            RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup vK.Completion
              (algebraicLocalizationValuationSubring vK w hw)))
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        ((show L ≃ₐ[K] L from
          ((sigma : RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K
            (absoluteValueExtensionValuationSubring vK w hw)) :
            RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
              (absoluteValueExtensionValuationSubring vK w hw))) x) :=
  localizationRamificationGroups_inertiaGroupEquiv_toLocalization
    vK hvK w hw sigma x

end

end HilbertRamification

end
