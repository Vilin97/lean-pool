/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletion
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.MultiplicativeDecomposition
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
/-!
# The profinite completion of a local multiplicative group

Every nontrivial element of `Kˣ` is detected by an open finite quotient.  A
nonzero valuation is detected by a finite cyclic quotient of `ℤ`; an element
of valuation zero is detected by a finite quotient of the profinite unit
group.  Consequently the canonical map from `Kˣ` to its completion by open
finite quotients is injective.
-/

noncomputable section

universe u v

namespace LocalClassFieldTheory

open scoped ValuativeRel WithZero
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The kernel of a continuous homomorphism to a finite discrete group is an
open finite-index normal subgroup. -/
def finiteTargetKernelOpenFiniteIndexNormalSubgroup
    {G : Type u} {F : Type v}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group F] [Finite F] [TopologicalSpace F] [DiscreteTopology F]
    (f : G →ₜ* F) : OpenFiniteIndexNormalSubgroup G :=
  ⟨
    { toOpenSubgroup :=
        { toSubgroup := f.toMonoidHom.ker
          isOpen' := by
            change IsOpen (f ⁻¹' {1})
            exact (isOpen_discrete {1}).preimage f.continuous_toFun }
      isNormal' := by
        infer_instance },
    Subgroup.finiteIndex_ker f.toMonoidHom⟩

/-- The normalized valuation reduced modulo `n`, as a continuous
multiplicative homomorphism.  The topology on the finite target is supplied by
the caller so that no global instance is introduced for the type tag. -/
def valuationModContinuousMonoidHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ)
    [TopologicalSpace (Multiplicative (ZMod n))]
    [DiscreteTopology (Multiplicative (ZMod n))] :
    Kˣ →ₜ* Multiplicative (ZMod n) where
  toMonoidHom :=
    (Int.castAddHom (ZMod n)).toMultiplicative.comp (valuationUnitsMulHom K)
  continuous_toFun := by
    exact (continuous_of_discreteTopology : Continuous
      (Int.castAddHom (ZMod n)).toMultiplicative).comp
        (valuationUnitsMulHom_continuous K)

/-- Every nontrivial element of `Kˣ` is omitted by some open finite-index
normal subgroup. -/
theorem exists_openFiniteIndexNormalSubgroup_not_mem_localMultiplicativeGroup
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (hx : x ≠ 1) :
    ∃ H : OpenFiniteIndexNormalSubgroup Kˣ,
      x ∉ H.toOpenNormalSubgroup.toSubgroup := by
  let valuationExponent : ℤ := valuationMap K (Additive.ofMul x)
  by_cases hvaluation : valuationExponent = 0
  · have hvaluation' : valuationMap K (Additive.ofMul x) = 0 := by
      simpa [valuationExponent] using hvaluation
    let unitFactor : Kˣ →ₜ* LocalFieldTheory.localUnits_profinite K :=
      localUnitFactorContinuousMonoidHom K
    let ux : LocalFieldTheory.localUnits_profinite K := unitFactor x
    have hux : ux ≠ 1 := by
      intro h
      apply hx
      have hembed : integerUnitsToFieldUnits K (unitFactor x) = x := by
        change integerUnitsToFieldUnits K
          (uniformizerUnitFactor K (chosenLocalUniformizer K)
            (chosenLocalUniformizer_spec K) x) = x
        rw [integerUnitsToFieldUnits_uniformizerUnitFactor, hvaluation']
        simp
      calc
        x = integerUnitsToFieldUnits K (unitFactor x) := hembed.symm
        _ = integerUnitsToFieldUnits K ux := rfl
        _ = integerUnitsToFieldUnits K 1 := congrArg _ h
        _ = 1 := map_one (integerUnitsToFieldUnits K)
    have hone : (1 : LocalFieldTheory.localUnits_profinite K) ∈
        ({ux}ᶜ : Set (LocalFieldTheory.localUnits_profinite K)) := by
      simpa using hux.symm
    obtain ⟨N, hN⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (isOpen_compl_singleton : IsOpen
          ({ux}ᶜ : Set (LocalFieldTheory.localUnits_profinite K))) hone
    let H : OpenFiniteIndexNormalSubgroup Kˣ :=
      topologicalProfiniteCompletionPreimageIndex
        (LocalFieldTheory.localUnits_profinite K) unitFactor N
    refine ⟨H, ?_⟩
    intro hmem
    have hunit : unitFactor x ∈ N := hmem
    have hnot : unitFactor x ∈
        ({ux}ᶜ : Set (LocalFieldTheory.localUnits_profinite K)) := hN hunit
    exact hnot (by rfl)
  · let n : ℕ := valuationExponent.natAbs + 1
    let : TopologicalSpace (Multiplicative (ZMod n)) := ⊥
    let : DiscreteTopology (Multiplicative (ZMod n)) := ⟨rfl⟩
    let valuationMod : Kˣ →ₜ* Multiplicative (ZMod n) :=
      valuationModContinuousMonoidHom K n
    let H : OpenFiniteIndexNormalSubgroup Kˣ :=
      finiteTargetKernelOpenFiniteIndexNormalSubgroup valuationMod
    refine ⟨H, ?_⟩
    change valuationMod x ≠ 1
    have hcast : (valuationExponent : ZMod n) ≠ 0 := by
      intro hzero
      have hdvd : (n : ℤ) ∣ valuationExponent :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd valuationExponent n).mp hzero
      have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hvaluation
      simp only [Int.natAbs_natCast, n] at hle
      omega
    change Multiplicative.ofAdd ((valuationExponent : ℤ) : ZMod n) ≠ 1
    simpa using hcast

/-- The intersection of the open finite-index normal subgroups of `Kˣ` is
trivial. -/
theorem localMultiplicativeGroup_residuallyFinite
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (⨅ H : OpenFiniteIndexNormalSubgroup Kˣ,
      H.toOpenNormalSubgroup.toSubgroup) = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_bot]
    by_contra hne
    obtain ⟨H, hxH⟩ :=
      exists_openFiniteIndexNormalSubgroup_not_mem_localMultiplicativeGroup K x hne
    exact hxH (Subgroup.mem_iInf.mp hx H)
  · exact bot_le

/-- The canonical map from a local multiplicative group to its completion by
open finite quotients is injective. -/
theorem topologicalProfiniteCompletionMap_injective_localField
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Injective (topologicalProfiniteCompletionMap Kˣ) :=
  topologicalProfiniteCompletionMap_injective_of_iInf_eq_bot Kˣ
    (localMultiplicativeGroup_residuallyFinite K)

end LocalClassFieldTheory
