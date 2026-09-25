/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitStructure
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.NonarchimedeanLocalField
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.GroupTheory.Torsion
/-!
# Unit decomposition of the p-adic integers

This file constructs the reusable topological decomposition of
`ℤ_[p]ˣ` into its finite factor and its principal `p`-adic factor.
-/

@[expose] public section

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  continuousMulEquivOfCompactToT2 →
    continuousMulEquivOfCompactToT2

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  residueRootsOfUnityContinuousMulEquivZMod →
    residueRootsOfUnityContinuousMulEquivZMod

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  residueRootsOfUnityEquivResidueFieldUnits →
    residueRootsOfUnityEquivResidueFieldUnits

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  valuationSubringUnitsEquivRootsTimesPrincipalUnits →
    valuationSubringUnitsEquivRootsTimesPrincipalUnits

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply →
    valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply


open scoped Topology

noncomputable section

namespace LocalFieldTheory
namespace Padic

open scoped WithZero
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

theorem padicDVRValuation_surjective
    (p : ℕ) [Fact p.Prime] :
    Function.Surjective (padicDVRValuation p) := by
  intro y
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  let π :=
    valuation_exists_uniformizer ℚ_[p]
      (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) |>.choose
  have hπ :
      padicDVRValuation p π =
        WithZero.exp (-1 : ℤ) :=
    valuation_exists_uniformizer ℚ_[p]
      (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) |>.choose_spec
  refine ⟨π ^ (- WithZero.log y), ?_⟩
  rw [map_zpow₀ (padicDVRValuation p) π (- WithZero.log y)]
  rw [hπ]
  rw [← WithZero.exp_zsmul]
  simpa using WithZero.exp_log hy

local instance padicDVRResidueFinite
    (p : ℕ) [Fact p.Prime] :
    Finite
      (IsLocalRing.ResidueField
        (padicDVRValuation p).valuationSubring) := by
  simpa [padicCompleteDVF] using
    padicCompleteDVF_residueField_finite p

/-- The residue field of the valuation-theoretic presentation of `ℚ_[p]`
is canonically `ZMod p`. -/
noncomputable def padicResidueEquivZMod
    (p : ℕ) [Fact p.Prime] :
    (LocalField.ofWithZeroValuation
      (padicDVRValuation p)).residueField ≃+* ZMod p :=
  (IsLocalRing.ResidueField.mapEquiv
      (padicIntEquivValuationSubring p)).symm.trans
    (padicIntResidueFieldEquivZMod p)

theorem padic_residueCharacteristic_eq
    (p : ℕ) [Fact p.Prime] :
    (LocalField.ofWithZeroValuation
      (padicDVRValuation p)).residueCharacteristic = p := by
  let F :=
    LocalField.ofWithZeroValuation
      (padicDVRValuation p)
  let e : F.residueField ≃+* ZMod p :=
    padicResidueEquivZMod p
  have : CharP F.residueField p := by
    constructor
    intro n
    rw [← e.injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff (ZMod p) p n
  exact ringChar.eq F.residueField p

theorem padicDVRValued_uniformSpace_eq_standard
    (p : ℕ) [Fact p.Prime] :
    (Valued.mk' (padicDVRValuation p)).toUniformSpace =
      (inferInstance : UniformSpace ℚ_[p]) := by
  let v := padicDVRValuation p
  let standard : Valued ℚ_[p] NNReal :=
    NormedField.toValued
  let w : Valuation ℚ_[p] NNReal := standard.v
  have hvw : v.IsEquiv w := by
    apply Valuation.isEquiv_of_val_le_one
    intro x
    change v x ≤ 1 ↔ ‖x‖₊ ≤ 1
    rw [LocalField.padicDVRValuation_le_one_iff_norm_le_one]
    change
      (↑‖x‖₊ : ℝ) ≤ (↑(1 : NNReal) : ℝ) ↔ ‖x‖₊ ≤ 1
    exact NNReal.coe_le_coe
  have hmk :
      (Valued.mk' v).toUniformSpace =
        (Valued.mk' w).toUniformSpace := by
    apply le_antisymm
    · rw [le_iff_uniformContinuous_id]
      simpa using hvw.symm.uniformContinuous
    · rw [le_iff_uniformContinuous_id]
      simpa using hvw.uniformContinuous
  have hstandard :
      standard.toUniformSpace =
        (Valued.mk' w).toUniformSpace :=
    (@Valued.toUniformSpace_eq ℚ_[p] _ NNReal _ standard).trans
      (@Valued.toUniformSpace_eq ℚ_[p] _ NNReal _
        (Valued.mk' w)).symm
  exact hmk.trans hstandard.symm

theorem padic_finrank_eq_one
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v :=
      LocalField.mixedWithZeroValuationContext v
    Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p] = 1 := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  let : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  dsimp only
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  refine ⟨RingHom.injective _, ?_⟩
  let direct : Valued ℚ_[p] (WithZero (Multiplicative ℤ)) :=
    Valued.mk' v
  let restricted : Valued ℚ_[p] F.mrangeValueGroup :=
    CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  have hrestricted :
      @IsUniformInducing
        ℚ_[F.residueCharacteristic] ℚ_[p]
        inferInstance restricted.toUniformSpace
        (algebraMap ℚ_[F.residueCharacteristic] ℚ_[p]) := by
    let : Valued ℚ_[p] F.mrangeValueGroup := restricted
    change IsUniformInducing
      (fun x : ℚ_[F.residueCharacteristic] =>
        ((F.qpadicNumbersEquivQpadicClosureSubfield x :
          F.qpadicClosureSubfield) : ℚ_[p]))
    exact isUniformEmbedding_subtype_val.isUniformInducing.comp
      F.qpadicNumbersToQpadicClosureSubfield_isUniformInducing
  have huniform :
      direct.toUniformSpace = restricted.toUniformSpace := by
    change
      (Valued.mk' v).toUniformSpace =
        (CompleteDVF.mrangeRestrictValued
          (WithZeroValuationTopology.completeDVF v)).toUniformSpace
    exact WithZeroValuationTopology.valuedMk_uniformSpace_eq_mrangeRestrict v
  have hUR :
      (PseudoMetricSpace.toUniformSpace : UniformSpace ℚ_[p]) =
        restricted.toUniformSpace :=
    (padicDVRValued_uniformSpace_eq_standard p).symm.trans huniform
  have hclosed :
      @IsClosed ℚ_[p] restricted.toTopologicalSpace
        (Set.range
          (algebraMap ℚ_[F.residueCharacteristic] ℚ_[p])) := by
    have hembedding :
        @IsUniformEmbedding
          ℚ_[F.residueCharacteristic] ℚ_[p]
          inferInstance restricted.toUniformSpace
          (algebraMap ℚ_[F.residueCharacteristic] ℚ_[p]) :=
      ⟨hrestricted, RingHom.injective _⟩
    exact hembedding.isClosedEmbedding.isClosed_range
  have hratDense :
      @DenseRange ℚ_[p] restricted.toTopologicalSpace
        ℚ ((↑) : ℚ → ℚ_[p]) := by
    have htop :
        (PseudoMetricSpace.toUniformSpace :
          UniformSpace ℚ_[p]).toTopologicalSpace =
            restricted.toTopologicalSpace :=
      congrArg (fun U : UniformSpace ℚ_[p] => U.toTopologicalSpace) hUR
    let P := fun T : TopologicalSpace ℚ_[p] =>
      @DenseRange ℚ_[p] T ℚ ((↑) : ℚ → ℚ_[p])
    exact (congrArg P htop).mp (Padic.denseRange_ratCast p)
  have hdense :
      @DenseRange ℚ_[p] restricted.toTopologicalSpace
        ℚ_[F.residueCharacteristic]
        (algebraMap ℚ_[F.residueCharacteristic] ℚ_[p]) := by
    apply DenseRange.of_comp
      (g := ((↑) : ℚ → ℚ_[F.residueCharacteristic]))
    have hcomp :
        (algebraMap ℚ_[F.residueCharacteristic] ℚ_[p]) ∘
            ((↑) : ℚ → ℚ_[F.residueCharacteristic]) =
          ((↑) : ℚ → ℚ_[p]) := by
      funext q
      simpa only [Function.comp_apply] using
        (map_ratCast
          (algebraMap ℚ_[F.residueCharacteristic] ℚ_[p]) q)
    rw [hcomp]
    exact hratDense
  rw [← Set.range_eq_univ]
  exact hclosed.closure_eq.symm.trans hdense.closure_range

/-- After identifying the residue characteristic with `p` and the relative
degree with one, the free additive factor is canonically `ℤ_[p]`. -/
noncomputable def padicFreeContinuousAddEquivOfEq
    (p q d : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hq : q = p) (hd : d = 1) :
    (Fin d → ℤ_[q]) ≃ₜ+ ℤ_[p] := by
  subst q
  subst d
  exact
    { AddEquiv.funUnique (Fin 1) ℤ_[p] with
      continuous_toFun := continuous_apply 0
      continuous_invFun := continuous_pi fun _ => continuous_id }

/-- The free additive factor in the mixed-characteristic structure theorem
for `ℚ_[p]` is continuously equivalent to `ℤ_[p]`. -/
noncomputable def padicFreeContinuousAddEquiv
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v :=
      LocalField.mixedWithZeroValuationContext v
    let d := Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p]
    (Fin d → ℤ_[F.residueCharacteristic]) ≃ₜ+ ℤ_[p] := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  letI : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  let q := F.residueCharacteristic
  let d := Module.finrank ℚ_[q] ℚ_[p]
  change (Fin d → ℤ_[q]) ≃ₜ+ ℤ_[p]
  have hq : q = p := by
    simpa [q, F, v] using padic_residueCharacteristic_eq p
  have hd : d = 1 := by
    simpa [d, F, v] using padic_finrank_eq_one p
  exact padicFreeContinuousAddEquivOfEq p q d hq hd

theorem padicIntEquivValuationSubring_coe
    (p : ℕ) [Fact p.Prime] (z : ℤ_[p]) :
    ((padicIntEquivValuationSubring p z :
      (padicDVRValuation p).valuationSubring) : ℚ_[p]) =
        (z : ℚ_[p]) := by
  rfl

theorem padicIntEquivValuationSubring_symm_coe
    (p : ℕ) [Fact p.Prime]
    (z : (padicDVRValuation p).valuationSubring) :
    (((padicIntEquivValuationSubring p).symm z : ℤ_[p]) : ℚ_[p]) =
      (z : ℚ_[p]) := by
  calc
    (((padicIntEquivValuationSubring p).symm z : ℤ_[p]) : ℚ_[p]) =
        ((padicIntEquivValuationSubring p
          ((padicIntEquivValuationSubring p).symm z) :
            (padicDVRValuation p).valuationSubring) : ℚ_[p]) := by
      symm
      exact padicIntEquivValuationSubring_coe p _
    _ = (z : ℚ_[p]) := by
      rw [RingEquiv.apply_symm_apply]

/-- The standard `p`-adic integers and the valuation subring of `ℚ_[p]`
are continuously multiplicatively equivalent. -/
noncomputable def padicIntValuationSubringContinuousMulEquiv
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    ℤ_[p] ≃ₜ* v.valuationSubring := by
  let v := padicDVRValuation p
  let e := padicIntEquivValuationSubring p
  exact
    { e.toMulEquiv with
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact isometry_subtype_coe.continuous.congr fun z =>
          padicIntEquivValuationSubring_coe p z
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact isometry_subtype_coe.continuous.congr fun z =>
          (padicIntEquivValuationSubring_symm_coe p z).symm }

/-- Multiplicative tagging turns a continuous additive equivalence into a
continuous multiplicative equivalence. -/
noncomputable def continuousMultiplicativeEquivOfAddEquiv
    {A B : Type*} [AddZeroClass A] [AddZeroClass B]
    [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ+ B) :
    Multiplicative A ≃ₜ* Multiplicative B :=
  { e.toAddEquiv.toMultiplicative with
    continuous_toFun := e.continuous_toFun
    continuous_invFun := e.continuous_invFun }

/-- Multiplicative tagging commutes continuously with binary products. -/
noncomputable def prodMultiplicativeContinuousMulEquiv
    (A B : Type*) [AddZeroClass A] [AddZeroClass B]
    [TopologicalSpace A] [TopologicalSpace B] :
    Multiplicative (A × B) ≃ₜ*
      Multiplicative A × Multiplicative B :=
  { MulEquiv.prodMultiplicative A B with
    continuous_toFun := continuous_fst.prodMk continuous_snd
    continuous_invFun := continuous_fst.prodMk continuous_snd }

/-- The product of two continuous multiplicative equivalences. -/
noncomputable def continuousMulEquivProdCongr
    {A B C D : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D]
    [MulOneClass A] [MulOneClass B] [MulOneClass C] [MulOneClass D]
    (e : A ≃ₜ* B) (f : C ≃ₜ* D) :
    A × C ≃ₜ* B × D :=
  { MulEquiv.prodCongr e.toMulEquiv f.toMulEquiv with
    continuous_toFun :=
      (e.continuous_toFun.comp continuous_fst).prodMk
        (f.continuous_toFun.comp continuous_snd)
    continuous_invFun :=
      (e.continuous_invFun.comp continuous_fst).prodMk
        (f.continuous_invFun.comp continuous_snd) }

/-- Continuous multiplicative reassociation of a triple product. -/
noncomputable def continuousMulEquivProdAssoc
    (A B C : Type*) [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [MulOneClass A] [MulOneClass B] [MulOneClass C] :
    (A × B) × C ≃ₜ* A × (B × C) :=
  { MulEquiv.prodAssoc with
    continuous_toFun :=
      (continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    continuous_invFun :=
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd) }

/-- The topology on the first principal-unit group induced directly from
the valuation topology on `ℚ_[p]`. -/
@[implicit_reducible]
noncomputable def padicPrincipalUnitDirectTopology
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    TopologicalSpace
      (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1) := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  letI : Valued ℚ_[p] (WithZero (Multiplicative ℤ)) :=
    Valued.mk' v
  exact inferInstance

/-- The standard topology on the first principal-unit group of `ℚ_[p]`. -/
@[implicit_reducible]
noncomputable def padicPrincipalUnitStandardTopology
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    TopologicalSpace
      (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1) := by
  exact inferInstance

/-- The directly induced valuation topology agrees with the standard topology
on the first principal-unit group of `ℚ_[p]`. -/
theorem padicPrincipalUnitDirectTopology_eq_standard
    (p : ℕ) [Fact p.Prime] :
    padicPrincipalUnitDirectTopology p =
      padicPrincipalUnitStandardTopology p := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  let U := CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1
  let liftTopology := fun T : TopologicalSpace ℚ_[p] => by
    letI : TopologicalSpace ℚ_[p] := T
    exact (inferInstance : TopologicalSpace U)
  unfold padicPrincipalUnitDirectTopology
    padicPrincipalUnitStandardTopology
  change
    liftTopology (Valued.mk' v).toTopologicalSpace =
      liftTopology PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact congrArg liftTopology
    (congrArg (fun U : UniformSpace ℚ_[p] => U.toTopologicalSpace)
      (padicDVRValued_uniformSpace_eq_standard p))

/-- The mixed-characteristic structure data for the first principal units,
using the valuation-induced topology directly. -/
noncomputable def padicPrincipalDataDirect
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v :=
      LocalField.mixedWithZeroValuationContext v
    letI : Valued ℚ_[p] (WithZero (Multiplicative ℤ)) :=
      Valued.mk' v
    let d := Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p]
    Σ a : ℕ,
      Multiplicative
          (ZMod (F.residueCharacteristic ^ a) ×
            (Fin d → ℤ_[F.residueCharacteristic])) ≃ₜ*
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1 := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  letI : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  letI : Valued ℚ_[p] (WithZero (Multiplicative ℤ)) :=
    Valued.mk' v
  exact LocalField.chosenMixedFirstPrincipalUnitStructureOfWithZeroValuation
    v (padicDVRValuation_surjective p)

/-- The multiplicative equivalence underlying the first-principal-unit
structure data for `ℚ_[p]`. -/
noncomputable def padicPrincipalMulData
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v :=
      LocalField.mixedWithZeroValuationContext v
    let d := Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p]
    Σ a : ℕ,
      Multiplicative
          (ZMod (F.residueCharacteristic ^ a) ×
            (Fin d → ℤ_[F.residueCharacteristic])) ≃*
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1 := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  letI : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  letI : Valued ℚ_[p] (WithZero (Multiplicative ℤ)) :=
    Valued.mk' v
  exact ⟨(padicPrincipalDataDirect p).1,
    (padicPrincipalDataDirect p).2.toMulEquiv⟩

/-- Forgetting topology preserves the finite cyclic exponent in the principal-unit data. -/
theorem padicPrincipalMulData_fst (p : ℕ) [Fact p.Prime] :
    (padicPrincipalMulData p).1 = (padicPrincipalDataDirect p).1 := rfl

/-- The first-principal-unit structure data transported to the standard
`p`-adic topology. -/
noncomputable def padicPrincipalData
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v :=
      LocalField.mixedWithZeroValuationContext v
    let d := Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p]
    Σ a : ℕ,
      Multiplicative
          (ZMod (F.residueCharacteristic ^ a) ×
            (Fin d → ℤ_[F.residueCharacteristic])) ≃ₜ*
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1 := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  letI : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  let d := Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p]
  let U := CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1
  let direct : Valued ℚ_[p] (WithZero (Multiplicative ℤ)) :=
    Valued.mk' v
  letI : Valued ℚ_[p] (WithZero (Multiplicative ℤ)) := direct
  let raw :=
    LocalField.chosenMixedFirstPrincipalUnitStructureOfWithZeroValuation
      v (padicDVRValuation_surjective p)
  let directTopology : TopologicalSpace U := inferInstance
  let standardTopology : TopologicalSpace U :=
    padicPrincipalUnitStandardTopology p
  have hdirect :
      directTopology = padicPrincipalUnitDirectTopology p := by
    unfold directTopology padicPrincipalUnitDirectTopology
    rfl
  have htop : directTopology = standardTopology :=
    hdirect.trans (padicPrincipalUnitDirectTopology_eq_standard p)
  let P := fun T : TopologicalSpace U => by
    letI : TopologicalSpace U := T
    exact Σ a : ℕ,
      Multiplicative
          (ZMod (F.residueCharacteristic ^ a) ×
            (Fin d → ℤ_[F.residueCharacteristic])) ≃ₜ* U
  have hraw : P directTopology := raw
  have hstandard : P standardTopology :=
    (congrArg P htop).mp hraw
  exact hstandard

/-- The finite factor in the topological decomposition of `ℤ_pˣ`. -/
noncomputable abbrev padicUnitFiniteFactor
    (p : ℕ) [Fact p.Prime] : Type :=
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  letI : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  Multiplicative
      (ZMod (Nat.card F.residueField - 1)) ×
    Multiplicative
      (ZMod
        (F.residueCharacteristic ^ (padicPrincipalData p).1))

/-- The standard topological decomposition
`ℤ_pˣ ≃ finite × ℤ_p` used in the local reciprocity calculation. -/
noncomputable def padicUnitDecomposition
    (p : ℕ) [Fact p.Prime] :
    padicUnitFiniteFactor p × Multiplicative ℤ_[p] ≃ₜ*
      ℤ_[p]ˣ := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  letI : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  let d := Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p]
  let a := (padicPrincipalData p).1
  let RootCyc :=
    Multiplicative
      (ZMod (Nat.card F.residueField - 1))
  let FinCyc :=
    Multiplicative (ZMod (F.residueCharacteristic ^ a))
  let Free :=
    Fin d → ℤ_[F.residueCharacteristic]
  let RootGroup :=
    CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup
      F.toCompleteDVF
  let U :=
    CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1
  change (RootCyc × FinCyc) × Multiplicative ℤ_[p] ≃ₜ*
    ℤ_[p]ˣ
  let rootsAlg : RootCyc ≃* RootGroup := by
    letI : Valued ℚ_[p]
        (MonoidHom.mrange
          F.toCompleteDVF.valuation.toMonoidWithZeroHom) :=
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
        F.toCompleteDVF
    exact
      (residueRootsOfUnityContinuousMulEquivZMod
        F.toCompleteDVF).toMulEquiv
  letI : Finite RootGroup :=
    Finite.of_equiv F.residueFieldˣ
      (residueRootsOfUnityEquivResidueFieldUnits
        F.toCompleteDVF).symm.toEquiv
  letI : Finite RootCyc :=
    Finite.of_equiv RootGroup rootsAlg.symm.toEquiv
  letI : NeZero (F.residueCharacteristic ^ a) :=
    ⟨pow_ne_zero _
      F.residueCharacteristic_prime.ne_zero⟩
  let roots : RootCyc ≃ₜ* RootGroup :=
    { rootsAlg with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  let principalRaw : Multiplicative (ZMod
      (F.residueCharacteristic ^ a) × Free) ≃ₜ* U := by
    exact (padicPrincipalData p).2
  let principalSplit : FinCyc × Multiplicative Free ≃ₜ* U :=
    (prodMultiplicativeContinuousMulEquiv
      (ZMod (F.residueCharacteristic ^ a)) Free).symm.trans
        principalRaw
  let free :
      Multiplicative Free ≃ₜ* Multiplicative ℤ_[p] :=
    continuousMultiplicativeEquivOfAddEquiv
      (padicFreeContinuousAddEquiv p)
  let principal :
      FinCyc × Multiplicative ℤ_[p] ≃ₜ* U :=
    (continuousMulEquivProdCongr
      (ContinuousMulEquiv.refl FinCyc) free.symm).trans
        principalSplit
  let factors : (RootCyc × FinCyc) × Multiplicative ℤ_[p] ≃ₜ*
      RootGroup × U :=
    (continuousMulEquivProdAssoc
      RootCyc FinCyc (Multiplicative ℤ_[p])).trans
        (continuousMulEquivProdCongr roots principal)
  let unitsAlg : RootGroup × U ≃*
      F.valuationSubringˣ :=
    valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F.toCompleteDVF
  let totalAlg :
      (RootCyc × FinCyc) × Multiplicative ℤ_[p] ≃*
        F.valuationSubringˣ :=
    factors.toMulEquiv.trans unitsAlg
  have hUnitsAlg : Continuous unitsAlg := by
    have hmul : Continuous (fun z : RootGroup × U =>
        (z.1 : F.valuationSubringˣ) *
          (z.2 : F.valuationSubringˣ)) :=
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
    refine hmul.congr ?_
    intro z
    exact
      (valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply
        F.toCompleteDVF z).symm
  have hTotal : Continuous totalAlg :=
    hUnitsAlg.comp factors.continuous_toFun
  let total :
      (RootCyc × FinCyc) × Multiplicative ℤ_[p] ≃ₜ*
        F.valuationSubringˣ :=
    continuousMulEquivOfCompactToT2
      totalAlg hTotal
  let integral :
      ℤ_[p]ˣ ≃ₜ* F.valuationSubringˣ := by
    exact Units.mapContinuousMulEquiv
      (padicIntValuationSubringContinuousMulEquiv p)
  exact total.trans integral.symm

noncomputable instance padicUnitFiniteFactor_finite
    (p : ℕ) [Fact p.Prime] :
    Finite (padicUnitFiniteFactor p) := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  let : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  let a := (padicPrincipalData p).1
  change Finite
    (Multiplicative
        (ZMod (Nat.card F.residueField - 1)) ×
      Multiplicative
        (ZMod (F.residueCharacteristic ^ a)))
  let : NeZero (Nat.card F.residueField - 1) :=
    ⟨by
      have hcard : 1 < Nat.card F.residueField :=
        Finite.one_lt_card
      omega⟩
  let : NeZero (F.residueCharacteristic ^ a) :=
    ⟨pow_ne_zero _ F.residueCharacteristic_prime.ne_zero⟩
  infer_instance

end Padic
end LocalFieldTheory
