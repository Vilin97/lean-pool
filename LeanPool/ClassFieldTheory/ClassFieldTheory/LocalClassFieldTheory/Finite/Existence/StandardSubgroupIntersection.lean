/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.NormTopology
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm
/-!
# Intersecting standard norm conditions

The unramified degree-`d` factor forces the normalized valuation to be
divisible by `d`.  The totally ramified Lubin--Tate factor forces an element
to lie in `⟨ϖ⟩ U^n`.  Their intersection therefore lies in `⟨ϖ^d⟩ U^n`.
This is the elementary subgroup calculation used in local existence proofs.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

universe u

/-- The intersection of the unramified valuation condition and the
principal-unit condition is contained in the corresponding standard subgroup. -/
theorem unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_le
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    unramifiedNormSubgroup K d ⊓
        LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n ≤
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n := by
  intro x hx
  rcases Subgroup.mem_sup.mp hx.2 with ⟨y, hy, z, hz, hyz⟩
  rcases Subgroup.mem_zpowers_iff.mp hy with ⟨k, hky⟩
  have hky' : ϖ ^ k = y := by
    simpa using hky
  change z ∈ (principalUnits K n).map
    (integerUnitsToFieldUnits K) at hz
  rcases hz with ⟨u, hu, huz⟩
  have hvz : valuationMap K (Additive.ofMul z) = 0 := by
    rw [← huz]
    exact v_integerUnitsToFieldUnits K u
  have hvx : valuationMap K (Additive.ofMul x) = k := by
    calc
      valuationMap K (Additive.ofMul x) =
          valuationMap K (Additive.ofMul (y * z)) :=
        congrArg _ hyz.symm
      _ = valuationMap K (Additive.ofMul y) +
          valuationMap K (Additive.ofMul z) :=
        valuationMap_ofMul_mul K y z
      _ = valuationMap K (Additive.ofMul (ϖ ^ k)) + 0 := by
        rw [hky', hvz]
      _ = k * 1 + 0 := by
        rw [valuationMap_ofMul_zpow, hϖ]
      _ = k := by ring
  have hdk : (d : ℤ) ∣ k := by
    rw [← hvx]
    exact (mem_unramifiedNormSubgroup_iff K d x).1 hx.1
  obtain ⟨t, ht⟩ := hdk
  have hyTarget : y ∈ Subgroup.zpowers (ϖ ^ d) := by
    rw [← hky', Subgroup.mem_zpowers_iff]
    refine ⟨t, ?_⟩
    calc
      (ϖ ^ d) ^ t = (ϖ ^ (d : ℤ)) ^ t := by
        rw [zpow_natCast]
      _ = ϖ ^ ((d : ℤ) * t) := by
        rw [zpow_mul]
      _ = ϖ ^ k := by rw [← ht]
  exact Subgroup.mem_sup.mpr
    ⟨y, hyTarget, z, ⟨u, hu, huz⟩, hyz⟩

/-- If an unramified norm condition and a principal-unit norm condition are
realized by finite Galois subextensions, their compositum has norm subgroup
contained in every subgroup containing the corresponding standard subgroup. -/
theorem finiteGaloisCompositum_normSubgroup_le_of_standard
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H)
    (U T : ClassFormation.FiniteGaloisSubextension (intrinsicAbstractBase K))
    (hUle :
      (U.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (unramifiedNormSubgroup K d).toAddSubgroup)
    (hTle :
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup) :
    (U.compositum T).normSubgroup (intrinsicAbsoluteUnits K) ≤
      H.toAddSubgroup.map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom := by
  let A := intrinsicAbsoluteUnits K
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  intro x hx
  have hxU : x ∈ U.normSubgroup A :=
    U.normSubgroup_compositum_le_left A T hx
  have hxT : x ∈ T.normSubgroup A :=
    U.normSubgroup_compositum_le_right A T hx
  have hxUnramAdd : e.symm x ∈
      (unramifiedNormSubgroup K d).toAddSubgroup :=
    hUle ⟨x, hxU, rfl⟩
  have hxPrincipalAdd : e.symm x ∈
      (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup :=
    hTle ⟨x, hxT, rfl⟩
  have hxUnram : Additive.toMul (e.symm x) ∈
      unramifiedNormSubgroup K d := hxUnramAdd
  have hxPrincipal : Additive.toMul (e.symm x) ∈
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n := hxPrincipalAdd
  have hxStandard : Additive.toMul (e.symm x) ∈
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n :=
    unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_le
      K ϖ d n hϖ ⟨hxUnram, hxPrincipal⟩
  have hxH : e.symm x ∈ H.toAddSubgroup := by
    change Additive.toMul (e.symm x) ∈ H
    exact hstandard hxStandard
  exact ⟨e.symm x, hxH, e.apply_symm_apply x⟩

/-- The same standard-subgroup containment while retaining both inputs and
their compositum as finite abelian subextensions. -/
theorem finiteAbelianCompositum_normSubgroup_le_of_standard
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H)
    (U T : ClassFormation.FiniteAbelianSubextension
      (intrinsicAbstractBase K))
    (hUle :
      (U.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (unramifiedNormSubgroup K d).toAddSubgroup)
    (hTle :
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup) :
    (U.compositum T).normSubgroup (intrinsicAbsoluteUnits K) ≤
      H.toAddSubgroup.map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom := by
  let A := intrinsicAbsoluteUnits K
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  intro x hx
  have hxUT :
      x ∈ U.normSubgroup A ⊓ T.normSubgroup A :=
    ClassFormation.FiniteAbelianSubextension.normSubgroup_compositum_le_inf
      A U T hx
  have hxUnramAdd : e.symm x ∈
      (unramifiedNormSubgroup K d).toAddSubgroup :=
    hUle ⟨x, hxUT.1, rfl⟩
  have hxPrincipalAdd : e.symm x ∈
      (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup :=
    hTle ⟨x, hxUT.2, rfl⟩
  have hxStandard : Additive.toMul (e.symm x) ∈
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n :=
    unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_le
      K ϖ d n hϖ ⟨hxUnramAdd, hxPrincipalAdd⟩
  have hxH : e.symm x ∈ H.toAddSubgroup := by
    change Additive.toMul (e.symm x) ∈ H
    exact hstandard hxStandard
  exact ⟨e.symm x, hxH, e.apply_symm_apply x⟩

end LocalClassFieldTheory

end
