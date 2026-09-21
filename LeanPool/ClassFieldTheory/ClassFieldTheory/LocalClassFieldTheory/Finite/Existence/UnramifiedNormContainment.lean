/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalHenselianValuation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm
/-!
# The unramified norm containment

For the canonical unramified extension of degree d, every relative norm has
normalized valuation divisible by d. This file transports that abstract norm
subgroup from fixed coefficients to the ordinary multiplicative group of the
local field.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory

/-! The two transport lemmas below isolate propositionally equal presentations
of the ground field, making the main proof insensitive to proof terms carried
by extensionSubgroup. -/

private theorem valuationAt_coe_eq_of_closedSubgroup_eq
    {G : Type} [Group G] [TopologicalSpace G]
    {D : DegreeData G} {A : Rep ℤ G}
    (v : ValuationData D A)
    (H H' : FiniteAbstractField G)
    (hHH' : H.field = H'.field)
    (x : ambientFixedAddSubgroup A H.field)
    (x' : ambientFixedAddSubgroup A H'.field)
    (hxx' : x.1 = x'.1) :
    ((v.valuationAt H x : v.valueGroup) : ZHat) =
      ((v.valuationAt H' x' : v.valueGroup) : ZHat) := by
  have hH : H = H' := by
    cases H
    cases H'
    cases hHH'
    rfl
  subst H'
  have hx : x = x' := Subtype.ext hxx'
  subst x'
  rfl

/-- At the distinguished abstract base field, the normalized valuation is
the original henselian valuation. -/
private theorem valuationAt_baseField_coe
    {G : Type} [Group G] [TopologicalSpace G]
    {D : DegreeData G} {A : Rep ℤ G}
    (v : ValuationData D A)
    (x : ambientFixedAddSubgroup A (baseField G)) :
    ((v.valuationAt (FiniteAbstractField.base G) x : v.valueGroup) : ZHat) =
      v.toAddMonoidHom x := by
  have hdivided :=
    v.residueDegree_nsmul_dividedAt (FiniteAbstractField.base G) x
  simp at hdivided
  change v.dividedAt (FiniteAbstractField.base G) x = v.toAddMonoidHom x
  rw [hdivided]
  let : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) (baseField G) le_rfl) := by
    simpa [FiniteAbstractField.base] using (FiniteAbstractField.base G).finite
  change v.toAddMonoidHom
      (relativeNorm A (baseField G) (baseField G)
        (le_baseField (baseField G)) x) = v.toAddMonoidHom x
  have hle : le_baseField (baseField G) =
      (le_refl (baseField G).toSubgroup) :=
    Subsingleton.elim _ _
  rw [hle, relativeNorm_self]

/-- The norm subgroup of the canonical unramified extension of degree d,
transported from fixed coefficients to the ordinary multiplicative group, is
contained in the subgroup whose normalized valuation is divisible by d. -/
theorem finiteUnramifiedNormSubgroup_map_le_unramifiedNormSubgroup
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    let D := localResidueDatum K
    let Kfinite : FiniteAbstractField (intrinsicAbsoluteGalois K) :=
      intrinsicFiniteAbstractBase K
    let Kresidue := Kfinite.toFiniteResidueAbstractField D
    let U := ClassFormation.DegreeData.finiteUnramifiedExtension D
      Kresidue d hd
    (ClassFormation.FiniteGaloisSubextension.normSubgroup (intrinsicAbsoluteUnits K) U).map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
      (unramifiedNormSubgroup K d).toAddSubgroup := by
  let G := intrinsicAbsoluteGalois K
  let A := intrinsicAbsoluteUnits K
  let D := localResidueDatum K
  let v := localHenselianValuation K
  let K₀ := intrinsicAbstractBase K
  let Kfinite : FiniteAbstractField G := intrinsicFiniteAbstractBase K
  let Kresidue := Kfinite.toFiniteResidueAbstractField D
  let U : FiniteGaloisSubextension K₀ := by
    have h :=
      ClassFormation.DegreeData.finiteUnramifiedExtension D Kresidue d hd
    change FiniteGaloisSubextension K₀ at h
    exact h
  dsimp only

  let hUfinite : Finite
      (K₀.toSubgroup ⧸ extensionSubgroup K₀ U.field U.below) :=
    U.finite
  let hK₀finite : Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K₀ (le_baseField K₀)) :=
    Kfinite.finite
  let hUabsoluteFinite : Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) U.field
          (le_baseField U.field)) :=
    relativeTowerQuotientFinite (baseField G) K₀ U.field U.below
      (le_baseField K₀)
  let Ufinite : FiniteAbstractField G := ⟨U.field, hUabsoluteFinite⟩
  let EU : FiniteAbstractFieldExtension G :=
    { field := Ufinite
      base := Kfinite
      below := U.below
      finiteQuotient := U.finite }

  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  change y ∈ ClassFormation.FiniteGaloisSubextension.normSubgroup A U at hy
  rcases hy with ⟨a, rfl⟩

  have hres : (EU.residueDegree D : ℕ) = d := by
    have h :=
      ClassFormation.DegreeData.finiteUnramifiedExtension_residueDegree
        D Kresidue d hd
    change (EU.residueDegree D : ℕ) = d at h
    exact h
  have hvaluation :
      ((v.valuationAt Kfinite
        (relativeNorm A K₀ U.field U.below a) : v.valueGroup) : ZHat) =
        d • ((v.valuationAt Ufinite a : v.valueGroup) : ZHat) := by
    rw [← hres]
    exact (v.normalizedValuation_tower EU a).symm

  have hbase : K₀ = baseField G := by
    exact closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K)
  let eBase : ambientFixedAddSubgroup A K₀ ≃+
      ambientFixedAddSubgroup A (baseField G) :=
    AddEquiv.addSubgroupCongr
      (congrArg (ambientFixedAddSubgroup A) hbase)
  let yBase : ambientFixedAddSubgroup A (baseField G) :=
    eBase (relativeNorm A K₀ U.field U.below a)

  let BaseFinite : FiniteAbstractField G :=
    FiniteAbstractField.base G
  have hyTransport :
      ((v.valuationAt Kfinite
        (relativeNorm A K₀ U.field U.below a) : v.valueGroup) : ZHat) =
        ((v.valuationAt BaseFinite yBase : v.valueGroup) : ZHat) := by
    apply valuationAt_coe_eq_of_closedSubgroup_eq v Kfinite BaseFinite hbase
    rfl
  have hyBase : yBase = baseFieldUnitsEquiv K
      ((baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
        (relativeNorm A K₀ U.field U.below a)) := by
    apply Subtype.ext
    change (relativeNorm A K₀ U.field U.below a).1 =
      ((baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K))
        ((baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
          (relativeNorm A K₀ U.field U.below a))).1
    exact congrArg Subtype.val
      ((baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).apply_symm_apply
        (relativeNorm A K₀ U.field U.below a)).symm
  have hnative :
      ((v.valuationAt Kfinite
        (relativeNorm A K₀ U.field U.below a) : v.valueGroup) : ZHat) =
        Int.castRingHom ZHat
          (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
            ((baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
              (relativeNorm A K₀ U.field U.below a))) := by
    rw [hyTransport, valuationAt_baseField_coe, hyBase]
    change localBaseValuation K
        (baseFieldUnitsEquiv K
          ((baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
            (relativeNorm A K₀ U.field U.below a))) = _
    exact localBaseValuation_baseFieldUnitsEquiv K _

  apply (mem_unramifiedNormSubgroup_iff K d _).2
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).1
  rw [← zHatReduction_int d hd]
  calc
    zHatReduction d hd
        (Int.castRingHom ZHat
          (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
            ((baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
              (relativeNorm A K₀ U.field U.below a)))) =
        zHatReduction d hd
          ((v.valuationAt Kfinite
            (relativeNorm A K₀ U.field U.below a) : v.valueGroup) : ZHat) := by
      simpa only using congrArg (zHatReduction d hd) hnative.symm
    _ = 0 := by
      rw [hvaluation, map_nsmul]
      simp

/-- The canonical unramified extension of positive degree supplies a finite
Galois subextension whose transported norm subgroup consists of elements with
valuation divisible by that degree. -/
theorem exists_unramifiedFiniteGaloisExtension_normSubgroup_map_le
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    ∃ U : FiniteGaloisSubextension (intrinsicAbstractBase K),
      (U.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (unramifiedNormSubgroup K d).toAddSubgroup := by
  let A := intrinsicAbsoluteUnits K
  let B := intrinsicAbstractBase K
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  let D := localResidueDatum K
  let Bfinite : FiniteAbstractField (intrinsicAbsoluteGalois K) :=
    intrinsicFiniteAbstractBase K
  let Bresidue := Bfinite.toFiniteResidueAbstractField D
  let U : FiniteGaloisSubextension B := by
    have h := D.finiteUnramifiedExtension Bresidue d hd
    change FiniteGaloisSubextension B at h
    exact h
  refine ⟨U, ?_⟩
  simpa [A, B, e, D, Bfinite, Bresidue, U] using
    (finiteUnramifiedNormSubgroup_map_le_unramifiedNormSubgroup
      K d hd)

/-- The canonical degree-`d` unramified factor, retained as a named finite
abelian subextension of the local absolute Galois group. -/
noncomputable def localFiniteUnramifiedAbelianSubextension
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    FiniteAbelianSubextension (intrinsicAbstractBase K) := by
  let D := localResidueDatum K
  let Bfinite : FiniteAbstractField (intrinsicAbsoluteGalois K) :=
    intrinsicFiniteAbstractBase K
  let Bresidue := Bfinite.toFiniteResidueAbstractField D
  exact D.finiteUnramifiedAbelianExtension Bresidue d hd

/-- The named finite unramified abelian factor satisfies the expected
valuation-divisibility norm containment. -/
theorem localFiniteUnramifiedAbelianSubextension_normSubgroup_map_le
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    let U := localFiniteUnramifiedAbelianSubextension K d hd
    (U.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (unramifiedNormSubgroup K d).toAddSubgroup := by
  let A := intrinsicAbsoluteUnits K
  let B := intrinsicAbstractBase K
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  let D := localResidueDatum K
  let Bfinite : FiniteAbstractField (intrinsicAbsoluteGalois K) :=
    intrinsicFiniteAbstractBase K
  let Bresidue := Bfinite.toFiniteResidueAbstractField D
  let U := localFiniteUnramifiedAbelianSubextension K d hd
  simpa [A, B, e, D, Bfinite, Bresidue, U,
    localFiniteUnramifiedAbelianSubextension,
    FiniteAbstractField.toFiniteResidueAbstractField,
    DegreeData.finiteUnramifiedAbelianExtension,
    FiniteAbelianSubextension.normSubgroup,
    FiniteGaloisSubextension.normSubgroup] using
    (finiteUnramifiedNormSubgroup_map_le_unramifiedNormSubgroup
      K d hd)

/-- The canonical unramified extension can be retained as a finite abelian
subextension, with the same norm-subgroup containment. -/
theorem exists_unramifiedFiniteAbelianExtension_normSubgroup_map_le
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    ∃ U : FiniteAbelianSubextension (intrinsicAbstractBase K),
      (U.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (unramifiedNormSubgroup K d).toAddSubgroup := by
  exact
    ⟨localFiniteUnramifiedAbelianSubextension K d hd,
      localFiniteUnramifiedAbelianSubextension_normSubgroup_map_le
        K d hd⟩

end LocalClassFieldTheory

end
