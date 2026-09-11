/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.AdeleSpace.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Exact dimensions of adele divisor quotients

This file proves the exact rank formula for the adele filtration and the sandwich identity.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero
open IsDedekindDomain Cardinal

noncomputable section

namespace FunctionField.Chart

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

/-- Decidable equality on `k(X)` for adele filter proofs. -/
local instance instDecidableEqRatFuncAdeleFilter : DecidableEq k⟮X⟯ := Classical.decEq _
/-- Decidable equality on coordinate places for adele filter proofs. -/
local instance instDecidableEqPlaceAAdeleFilter : DecidableEq (PlaceA k K) := Classical.decEq _
/-- Additive group structure on adele filtration pieces. -/
local instance adeleFiltAddCommGroup (D' : DivisorA k K) : AddCommGroup (adeleFilt k K D') :=
  Submodule.addCommGroup _
/-- Module structure on adele filtration pieces. -/
local instance adeleFiltModule (D' : DivisorA k K) : Module k (adeleFilt k K D') :=
  Submodule.module _

/-- The zero adele. -/
def zeroAdele : AdeleSpace k K := ⟨0, by simp⟩

/-- Lift an adele to the valuation subring at a finite place, scaled by a uniformizer power. -/
noncomputable def finiteAdeleLocalResidueToSubring (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K))
    (a : adeleFilt k K (D + Finsupp.single (Sum.inl v) 1)) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v := by
  let π : K := Classical.choose (v.valuation_exists_uniformizer K)
  let n : ℤ := D (Sum.inl v) + 1
  refine ⟨π ^ n * (a.val : AdeleSpace k K).val (Sum.inl v), ?_⟩
  have hmem : v.valuation K (π ^ n * (a.val : AdeleSpace k K).val (Sum.inl v)) ≤ 1 := by
    have hπpow : v.valuation K (π ^ n) = WithZero.exp (-1) ^ n := by
      rw [map_zpow₀, Classical.choose_spec (v.valuation_exists_uniformizer K)]
    rw [map_mul, hπpow]
    have hf : v.valuation K ((a.val : AdeleSpace k K).val (Sum.inl v)) ≤ WithZero.exp n := by
      have := a.property (Sum.inl v)
      simpa [memAdeleFilt, placeValuation, n, Finsupp.add_apply, Finsupp.single_apply,
        add_comm] using this
    calc
      WithZero.exp (-1) ^ n * v.valuation K ((a.val : AdeleSpace k K).val (Sum.inl v))
          ≤ WithZero.exp (-1) ^ n * WithZero.exp n := mul_le_mul_right hf _
      _ = 1 := by
        rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
        convert WithZero.exp_zero
        simp
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff]
  exact hmem

/-- One-step local residue map on adeles at a finite coordinate place. -/
noncomputable def finiteAdeleLocalResidueMap (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    adeleFilt k K (D + Finsupp.single (Sum.inl v) 1) →ₗ[k] v.asIdeal.ResidueField :=
  let A := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v
  letI : Algebra k A :=
    ((algebraMap (ringOfIntegers k K) A).comp
      (algebraMap k (ringOfIntegers k K))).toAlgebra
  letI : IsScalarTower k (ringOfIntegers k K) A :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  {
    toFun := fun a =>
      IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v
        (finiteAdeleLocalResidueToSubring k K D v a)
    map_add' := fun a b => by
      rw [← map_add]
      congr 1
      simp [finiteAdeleLocalResidueToSubring, mul_add]
    map_smul' := fun c a => by
      let π : K := Classical.choose (v.valuation_exists_uniformizer K)
      let n : ℤ := D (Sum.inl v) + 1
      have hz :
          finiteAdeleLocalResidueToSubring k K D v (c • a) =
            algebraMap k A c * finiteAdeleLocalResidueToSubring k K D v a := by
        apply Subtype.ext
        simp only [finiteAdeleLocalResidueToSubring, Submodule.coe_smul_of_tower, Algebra.smul_def,
          Pi.smul_apply]
        let α : PlaceA k K → K := (a.val : AdeleSpace k K).val
        change π ^ n * (algebraMap k K c * α (Sum.inl v)) =
          (↑(algebraMap k A c) : K) * (π ^ n * α (Sum.inl v))
        have hcA : (↑(algebraMap k A c) : K) = algebraMap k K c := by
          calc
            (↑(algebraMap k A c) : K) =
                ↑(algebraMap (ringOfIntegers k K) A
                  (algebraMap k (ringOfIntegers k K) c)) := by
              rw [IsScalarTower.algebraMap_apply k (ringOfIntegers k K) A]
            _ = algebraMap (ringOfIntegers k K) K
                (algebraMap k (ringOfIntegers k K) c) := rfl
            _ = algebraMap k K c :=
              (IsScalarTower.algebraMap_apply k (ringOfIntegers k K) K c).symm
        rw [hcA]
        ring
      rw [hz, map_mul, Algebra.smul_def]
      congr 1
      rw [IsScalarTower.algebraMap_apply k (ringOfIntegers k K) A]
      rw [IsDedekindDomain.HeightOneSpectrum.residueHom, IsLocalization.lift_eq]
      exact (IsScalarTower.algebraMap_apply k (ringOfIntegers k K)
        v.asIdeal.ResidueField c).symm }

theorem finiteAdeleLocalResidueMap_ker (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    (finiteAdeleLocalResidueMap k K D v).ker =
      Submodule.comap (adeleFilt k K (D + Finsupp.single (Sum.inl v) 1)).subtype
        (adeleFilt k K D) := by
  ext a
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype,
    finiteAdeleLocalResidueMap, finiteAdeleLocalResidueToSubring]
  change IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v
      ⟨(Classical.choose (v.valuation_exists_uniformizer K)) ^
          (D (Sum.inl v) + 1) * ((a.val : AdeleSpace k K).val (Sum.inl v)), _⟩ = 0 ↔
    ∀ w, placeValuation k K w ((a.val : AdeleSpace k K).val w) ≤ WithZero.exp (D w)
  rw [IsDedekindDomain.HeightOneSpectrum.residueHom_eq_zero_iff]
  have hπ := Classical.choose_spec (v.valuation_exists_uniformizer K)
  rw [map_mul, map_zpow₀, hπ]
  rw [← WithZero.exp_zsmul]
  have hnsmul : (D (Sum.inl v) + 1) • (-1 : ℤ) = -(D (Sum.inl v) + 1) := by simp
  rw [hnsmul]
  have hlocal : WithZero.exp (-(D (Sum.inl v) + 1)) *
      v.valuation K ((a.val : AdeleSpace k K).val (Sum.inl v)) < 1 ↔
      v.valuation K ((a.val : AdeleSpace k K).val (Sum.inl v)) ≤
        WithZero.exp (D (Sum.inl v)) := by
    simpa using exp_neg_mul_lt_one_iff_le
      (v.valuation K ((a.val : AdeleSpace k K).val (Sum.inl v))) (D (Sum.inl v) + 1)
  rw [hlocal]
  constructor
  · intro hv w
    by_cases hw : w = Sum.inl v
    · subst hw
      exact hv
    · simpa [placeValuation, hw] using a.property w
  · intro hf
    simpa [placeValuation] using hf (Sum.inl v)

theorem finiteAdeleLocalResidueMap_surjective (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    Function.Surjective (finiteAdeleLocalResidueMap k K D v) := by
  let π : K := Classical.choose (v.valuation_exists_uniformizer K)
  let n : ℤ := D (Sum.inl v) + 1
  intro y
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective y
  let z : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v :=
    IsDedekindDomain.HeightOneSpectrum.localizationAlgEquiv (K := K) v x
  have hz : IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v z = y := by
    rwa [IsDedekindDomain.HeightOneSpectrum.residueHom_apply_localizationAlgEquiv]
  let xK : K := π ^ (-n) * (z : K)
  let a₀ : AdeleSpace k K := adeleUpdate k K (zeroAdele k K) (Sum.inl v) xK
  have ha₀ : a₀ ∈ adeleFilt k K (D + Finsupp.single (Sum.inl v) 1) := by
    intro w
    by_cases hw : w = Sum.inl v
    · subst hw
      simp only [placeValuation, Finsupp.add_apply, Finsupp.single_apply]
      have hπpow : v.valuation K (π ^ (-n)) = WithZero.exp (-1) ^ (-n) := by
        rw [map_zpow₀, Classical.choose_spec (v.valuation_exists_uniformizer K)]
      have hzle : v.valuation K (z : K) ≤ 1 := by
        simpa [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
          Valuation.mem_valuationSubring_iff] using z.property
      have hval :
          (v.valuation K) (a₀.val (Sum.inl v)) ≤ WithZero.exp (D (Sum.inl v) + 1) := by
        have hmul' : (v.valuation K) (a₀.val (Sum.inl v)) =
            (v.valuation K) (π ^ (-n)) * (v.valuation K) (z : K) := by
          change (v.valuation K)
              (Function.update (0 : PlaceA k K → K) (Sum.inl v) xK (Sum.inl v)) = _
          simp only [Function.update_self, xK]
          exact Valuation.map_mul (v.valuation K) _ _
        have hbound :
            (v.valuation K) (π ^ (-n)) * (v.valuation K) (z : K) ≤ WithZero.exp n := by
          have hπpow : v.valuation K (π ^ (-n)) = WithZero.exp (-1) ^ (-n) := by
            rw [map_zpow₀, Classical.choose_spec (v.valuation_exists_uniformizer K)]
          rw [hπpow]
          have hzle0 : (v.valuation K) (z : K) ≤ WithZero.exp (0 : ℤ) := by
            simpa [WithZero.exp_zero] using hzle
          calc
            WithZero.exp (-1) ^ (-n) * (v.valuation K) (z : K)
                ≤ WithZero.exp (-1) ^ (-n) * WithZero.exp 0 := mul_le_mul_right hzle0 _
            _ = WithZero.exp n := by
              rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
              simp
        simpa [n] using (le_of_eq hmul').trans hbound
      exact hval
    · simp only [placeValuation, zeroAdele, adeleUpdate, a₀,
        Function.update_of_ne hw, Pi.zero_apply, Valuation.map_zero,
        Finsupp.add_apply, Finsupp.single_apply]
      exact zero_le
  refine ⟨⟨a₀, ha₀⟩, ?_⟩
  have hmul : (finiteAdeleLocalResidueToSubring k K D v ⟨a₀, ha₀⟩ : K) = (z : K) := by
    dsimp [finiteAdeleLocalResidueToSubring, a₀, adeleUpdate, xK, zeroAdele, n, π]
    simp only [Function.update_self]
    have hπne : π ≠ 0 := by
      intro h0
      have huniform := Classical.choose_spec (v.valuation_exists_uniformizer K)
      have hπdef : v.valuation K π = WithZero.exp (-1) := by dsimp [π]; exact huniform
      rw [h0, Valuation.map_zero] at hπdef
      exact absurd hπdef.symm WithZero.exp_ne_zero
    have h1 : π ^ (D (Sum.inl v) + 1) * π ^ (-(D (Sum.inl v) + 1)) = (1 : K) := by
      rw [← zpow_add₀ hπne, add_neg_cancel, zpow_zero]
    calc
      π ^ (D (Sum.inl v) + 1) * (π ^ (-(D (Sum.inl v) + 1)) * (z : K))
          = (π ^ (D (Sum.inl v) + 1) * π ^ (-(D (Sum.inl v) + 1))) * (z : K) := by ring
      _ = (z : K) := by rw [h1, one_mul]
  simp only [finiteAdeleLocalResidueMap, finiteAdeleLocalResidueToSubring]
  exact congr_arg (IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v)
    (Subtype.ext_iff.mpr hmul) ▸ hz

theorem finrankAdeleFiltDiff_single_finite (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    finrankAdeleFiltDiff k K D (D + Finsupp.single (Sum.inl v) 1) =
      placeDegree k K (Sum.inl v) := by
  let f := finiteAdeleLocalResidueMap k K D v
  let e : (ringOfIntegers k K ⧸ v.asIdeal) ≃ₗ[k] v.asIdeal.ResidueField :=
    finiteResidueFieldEquiv k K v
  let : FiniteDimensional k v.asIdeal.ResidueField := e.finiteDimensional
  have hker := finiteAdeleLocalResidueMap_ker k K D v
  have hsurj := finiteAdeleLocalResidueMap_surjective k K D v
  rw [finrankAdeleFiltDiff, ← hker, f.quotKerEquivRange.finrank_eq]
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
  calc
    Module.finrank k v.asIdeal.ResidueField = Module.finrank k (ringOfIntegers k K ⧸ v.asIdeal) :=
      e.finrank_eq.symm
    _ = placeDegree k K (Sum.inl v) := rfl

/-- Lift an adele to the valuation subring at an infinite place, scaled by a uniformizer power. -/
noncomputable def infiniteAdeleLocalResidueToSubring (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K))
    (a : adeleFilt k K (D + Finsupp.single (Sum.inr v) 1)) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v := by
  let π : K := Classical.choose (v.valuation_exists_uniformizer K)
  let n : ℤ := D (Sum.inr v) + 1
  refine ⟨π ^ n * (a.val : AdeleSpace k K).val (Sum.inr v), ?_⟩
  have hmem : v.valuation K (π ^ n * (a.val : AdeleSpace k K).val (Sum.inr v)) ≤ 1 := by
    have hπpow : v.valuation K (π ^ n) = WithZero.exp (-1) ^ n := by
      rw [map_zpow₀, Classical.choose_spec (v.valuation_exists_uniformizer K)]
    rw [map_mul, hπpow]
    have hf : v.valuation K ((a.val : AdeleSpace k K).val (Sum.inr v)) ≤ WithZero.exp n := by
      have := a.property (Sum.inr v)
      rw [Finsupp.add_apply, Finsupp.single_eq_same] at this
      exact this
    calc
      WithZero.exp (-1) ^ n * v.valuation K ((a.val : AdeleSpace k K).val (Sum.inr v))
          ≤ WithZero.exp (-1) ^ n * WithZero.exp n := mul_le_mul_right hf _
      _ = 1 := by
        rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
        convert WithZero.exp_zero
        simp
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff]
  exact hmem

/-- One-step local residue map on adeles at an infinite coordinate place. -/
noncomputable def infiniteAdeleLocalResidueMap (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    adeleFilt k K (D + Finsupp.single (Sum.inr v) 1) →ₗ[k] v.asIdeal.ResidueField :=
  let A := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v
  letI : Algebra k A :=
    ((algebraMap (infiniteIntegers k K) A).comp
      (algebraMap k (infiniteIntegers k K))).toAlgebra
  letI : IsScalarTower k (infiniteIntegers k K) A :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  {
    toFun := fun a =>
      IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v
        (infiniteAdeleLocalResidueToSubring k K D v a)
    map_add' := fun a b => by
      rw [← map_add]
      congr 1
      simp [infiniteAdeleLocalResidueToSubring, mul_add]
    map_smul' := fun c a => by
      let π : K := Classical.choose (v.valuation_exists_uniformizer K)
      let n : ℤ := D (Sum.inr v) + 1
      have hz :
          infiniteAdeleLocalResidueToSubring k K D v (c • a) =
            algebraMap k A c * infiniteAdeleLocalResidueToSubring k K D v a := by
        apply Subtype.ext
        simp only [infiniteAdeleLocalResidueToSubring, Submodule.coe_smul_of_tower,
          Algebra.smul_def,
          Pi.smul_apply]
        let α : PlaceA k K → K := (a.val : AdeleSpace k K).val
        change π ^ n * (algebraMap k K c * α (Sum.inr v)) =
          (↑(algebraMap k A c) : K) * (π ^ n * α (Sum.inr v))
        have hcA : (↑(algebraMap k A c) : K) = algebraMap k K c := by
          calc
            (↑(algebraMap k A c) : K) =
                ↑(algebraMap (infiniteIntegers k K) A
                  (algebraMap k (infiniteIntegers k K) c)) := by
              rw [IsScalarTower.algebraMap_apply k (infiniteIntegers k K) A]
            _ = algebraMap (infiniteIntegers k K) K
                (algebraMap k (infiniteIntegers k K) c) := rfl
            _ = algebraMap k K c :=
              (IsScalarTower.algebraMap_apply k (infiniteIntegers k K) K c).symm
        rw [hcA]
        ring
      rw [hz, map_mul, Algebra.smul_def]
      congr 1
      rw [IsScalarTower.algebraMap_apply k (infiniteIntegers k K) A]
      rw [IsDedekindDomain.HeightOneSpectrum.residueHom, IsLocalization.lift_eq]
      exact (IsScalarTower.algebraMap_apply k (infiniteIntegers k K)
        v.asIdeal.ResidueField c).symm }

theorem infiniteAdeleLocalResidueMap_ker (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    (infiniteAdeleLocalResidueMap k K D v).ker =
      Submodule.comap (adeleFilt k K (D + Finsupp.single (Sum.inr v) 1)).subtype
        (adeleFilt k K D) := by
  ext a
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype,
    infiniteAdeleLocalResidueMap, infiniteAdeleLocalResidueToSubring]
  change IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v
      ⟨(Classical.choose (v.valuation_exists_uniformizer K)) ^
          (D (Sum.inr v) + 1) * ((a.val : AdeleSpace k K).val (Sum.inr v)), _⟩ = 0 ↔
    ∀ w, placeValuation k K w ((a.val : AdeleSpace k K).val w) ≤ WithZero.exp (D w)
  rw [IsDedekindDomain.HeightOneSpectrum.residueHom_eq_zero_iff]
  have hπ := Classical.choose_spec (v.valuation_exists_uniformizer K)
  rw [map_mul, map_zpow₀, hπ]
  rw [← WithZero.exp_zsmul]
  have hnsmul : (D (Sum.inr v) + 1) • (-1 : ℤ) = -(D (Sum.inr v) + 1) := by simp
  rw [hnsmul]
  have hlocal : WithZero.exp (-(D (Sum.inr v) + 1)) *
      v.valuation K ((a.val : AdeleSpace k K).val (Sum.inr v)) < 1 ↔
      v.valuation K ((a.val : AdeleSpace k K).val (Sum.inr v)) ≤
        WithZero.exp (D (Sum.inr v)) := by
    simpa using exp_neg_mul_lt_one_iff_le
      (v.valuation K ((a.val : AdeleSpace k K).val (Sum.inr v))) (D (Sum.inr v) + 1)
  rw [hlocal]
  constructor
  · intro hv w
    by_cases hw : w = Sum.inr v
    · subst hw
      exact hv
    · simpa [placeValuation, hw] using a.property w
  · intro hf
    simpa [placeValuation] using hf (Sum.inr v)

theorem infiniteAdeleLocalResidueMap_surjective (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    Function.Surjective (infiniteAdeleLocalResidueMap k K D v) := by
  let π : K := Classical.choose (v.valuation_exists_uniformizer K)
  let n : ℤ := D (Sum.inr v) + 1
  intro y
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective y
  let z : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v :=
    IsDedekindDomain.HeightOneSpectrum.localizationAlgEquiv (K := K) v x
  have hz : IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v z = y := by
    rwa [IsDedekindDomain.HeightOneSpectrum.residueHom_apply_localizationAlgEquiv]
  let xK : K := π ^ (-n) * (z : K)
  let a₀ : AdeleSpace k K := adeleUpdate k K (zeroAdele k K) (Sum.inr v) xK
  have ha₀ : a₀ ∈ adeleFilt k K (D + Finsupp.single (Sum.inr v) 1) := by
    intro w
    by_cases hw : w = Sum.inr v
    · subst hw
      simp only [placeValuation, Finsupp.add_apply, Finsupp.single_apply]
      have hπpow : v.valuation K (π ^ (-n)) = WithZero.exp (-1) ^ (-n) := by
        rw [map_zpow₀, Classical.choose_spec (v.valuation_exists_uniformizer K)]
      have hzle : v.valuation K (z : K) ≤ 1 := by
        simpa [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
          Valuation.mem_valuationSubring_iff] using z.property
      have hval :
          (v.valuation K) (a₀.val (Sum.inr v)) ≤ WithZero.exp (D (Sum.inr v) + 1) := by
        have hmul' : (v.valuation K) (a₀.val (Sum.inr v)) =
            (v.valuation K) (π ^ (-n)) * (v.valuation K) (z : K) := by
          change (v.valuation K)
              (Function.update (0 : PlaceA k K → K) (Sum.inr v) xK (Sum.inr v)) = _
          simp only [Function.update_self, xK]
          exact Valuation.map_mul (v.valuation K) _ _
        have hbound :
            (v.valuation K) (π ^ (-n)) * (v.valuation K) (z : K) ≤ WithZero.exp n := by
          have hπpow : v.valuation K (π ^ (-n)) = WithZero.exp (-1) ^ (-n) := by
            rw [map_zpow₀, Classical.choose_spec (v.valuation_exists_uniformizer K)]
          rw [hπpow]
          have hzle0 : (v.valuation K) (z : K) ≤ WithZero.exp (0 : ℤ) := by
            simpa [WithZero.exp_zero] using hzle
          calc
            WithZero.exp (-1) ^ (-n) * (v.valuation K) (z : K)
                ≤ WithZero.exp (-1) ^ (-n) * WithZero.exp 0 := mul_le_mul_right hzle0 _
            _ = WithZero.exp n := by
              rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
              simp
        simpa [n] using (le_of_eq hmul').trans hbound
      exact hval
    · simp only [placeValuation, zeroAdele, adeleUpdate, a₀,
        Function.update_of_ne hw, Pi.zero_apply, Valuation.map_zero,
        Finsupp.add_apply, Finsupp.single_apply]
      exact zero_le
  refine ⟨⟨a₀, ha₀⟩, ?_⟩
  have hmul : (infiniteAdeleLocalResidueToSubring k K D v ⟨a₀, ha₀⟩ : K) = (z : K) := by
    dsimp [infiniteAdeleLocalResidueToSubring, a₀, adeleUpdate, xK, zeroAdele, n, π]
    simp only [Function.update_self]
    have hπne : π ≠ 0 := by
      intro h0
      have huniform := Classical.choose_spec (v.valuation_exists_uniformizer K)
      have hπdef : v.valuation K π = WithZero.exp (-1) := by dsimp [π]; exact huniform
      rw [h0, Valuation.map_zero] at hπdef
      exact absurd hπdef.symm WithZero.exp_ne_zero
    have h1 : π ^ (D (Sum.inr v) + 1) * π ^ (-(D (Sum.inr v) + 1)) = (1 : K) := by
      rw [← zpow_add₀ hπne, add_neg_cancel, zpow_zero]
    calc
      π ^ (D (Sum.inr v) + 1) * (π ^ (-(D (Sum.inr v) + 1)) * (z : K))
          = (π ^ (D (Sum.inr v) + 1) * π ^ (-(D (Sum.inr v) + 1))) * (z : K) := by ring
      _ = (z : K) := by rw [h1, one_mul]
  simp only [infiniteAdeleLocalResidueMap, infiniteAdeleLocalResidueToSubring]
  exact congr_arg (IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v)
    (Subtype.ext_iff.mpr hmul) ▸ hz

theorem finrankAdeleFiltDiff_single_infinite (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    finrankAdeleFiltDiff k K D (D + Finsupp.single (Sum.inr v) 1) =
      placeDegree k K (Sum.inr v) := by
  let f := infiniteAdeleLocalResidueMap k K D v
  let e : (infiniteIntegers k K ⧸ v.asIdeal) ≃ₗ[k] v.asIdeal.ResidueField :=
    infiniteResidueFieldEquiv k K v
  let : FiniteDimensional k v.asIdeal.ResidueField := e.finiteDimensional
  have hker := infiniteAdeleLocalResidueMap_ker k K D v
  have hsurj := infiniteAdeleLocalResidueMap_surjective k K D v
  rw [finrankAdeleFiltDiff, ← hker, f.quotKerEquivRange.finrank_eq]
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
  calc
    Module.finrank k v.asIdeal.ResidueField =
        Module.finrank k (infiniteIntegers k K ⧸ v.asIdeal) :=
      e.finrank_eq.symm
    _ = placeDegree k K (Sum.inr v) := rfl

theorem finrankAdeleFiltDiff_single_one (D : DivisorA k K) (v : PlaceA k K) :
    finrankAdeleFiltDiff k K D (D + Finsupp.single v 1) = placeDegree k K v := by
  rcases v with v | v
  · exact finrankAdeleFiltDiff_single_finite k K D v
  · exact finrankAdeleFiltDiff_single_infinite k K D v

theorem finiteAdeleFiltDiff_quotient_single (D : DivisorA k K) (v : PlaceA k K) :
    Module.Finite k ((adeleFilt k K (D + Finsupp.single v 1)) ⧸
      Submodule.comap (adeleFilt k K (D + Finsupp.single v 1)).subtype (adeleFilt k K D)) := by
  classical
  rcases v with v | v
  · let : AddCommGroup (adeleFilt k K (D + Finsupp.single (Sum.inl v) 1)) :=
      Submodule.addCommGroup _
    let : Module k (adeleFilt k K (D + Finsupp.single (Sum.inl v) 1)) := Submodule.module _
    let f := finiteAdeleLocalResidueMap k K D v
    let e : (ringOfIntegers k K ⧸ v.asIdeal) ≃ₗ[k] v.asIdeal.ResidueField :=
      finiteResidueFieldEquiv k K v
    let : FiniteDimensional k v.asIdeal.ResidueField := e.finiteDimensional
    let p := Submodule.comap (adeleFilt k K (D + Finsupp.single (Sum.inl v) 1)).subtype
      (adeleFilt k K D)
    have : Module.Finite k f.range := inferInstance
    have : Module.Finite k
        (adeleFilt k K (D + Finsupp.single (Sum.inl v) 1) ⧸ f.ker) :=
      Module.Finite.equiv f.quotKerEquivRange.symm
    exact Module.Finite.equiv (Submodule.quotEquivOfEq f.ker p
      (finiteAdeleLocalResidueMap_ker k K D v))
  · let : AddCommGroup (adeleFilt k K (D + Finsupp.single (Sum.inr v) 1)) :=
      Submodule.addCommGroup _
    let : Module k (adeleFilt k K (D + Finsupp.single (Sum.inr v) 1)) := Submodule.module _
    let f := infiniteAdeleLocalResidueMap k K D v
    let e : (infiniteIntegers k K ⧸ v.asIdeal) ≃ₗ[k] v.asIdeal.ResidueField :=
      infiniteResidueFieldEquiv k K v
    let : FiniteDimensional k v.asIdeal.ResidueField := e.finiteDimensional
    let p := Submodule.comap (adeleFilt k K (D + Finsupp.single (Sum.inr v) 1)).subtype
      (adeleFilt k K D)
    have : Module.Finite k f.range := inferInstance
    have : Module.Finite k
        (adeleFilt k K (D + Finsupp.single (Sum.inr v) 1) ⧸ f.ker) :=
      Module.Finite.equiv f.quotKerEquivRange.symm
    exact Module.Finite.equiv (Submodule.quotEquivOfEq f.ker p
      (infiniteAdeleLocalResidueMap_ker k K D v))

theorem finiteAdeleFiltDiff_quotient_self (D : DivisorA k K) :
    Module.Finite k ((adeleFilt k K D) ⧸
      Submodule.comap (adeleFilt k K D).subtype (adeleFilt k K D)) := by
  rw [show Submodule.comap (adeleFilt k K D).subtype (adeleFilt k K D) = ⊤ from
    Submodule.comap_subtype_self (adeleFilt k K D)]
  infer_instance

theorem finiteAdeleFiltDiff_quotient_mono_add {D M N : DivisorA k K}
    (hDM : D ≤ M) (hMN : M ≤ N)
    [Module.Finite k ((adeleFilt k K N) ⧸
      Submodule.comap (adeleFilt k K N).subtype (adeleFilt k K M))]
    [Module.Finite k ((adeleFilt k K M) ⧸
      Submodule.comap (adeleFilt k K M).subtype (adeleFilt k K D))] :
    Module.Finite k ((adeleFilt k K N) ⧸
      Submodule.comap (adeleFilt k K N).subtype (adeleFilt k K D)) := by
  let p := adeleFilt k K N
  let q := Submodule.comap p.subtype (adeleFilt k K D)
  let r := Submodule.comap p.subtype (adeleFilt k K M)
  let pM := adeleFilt k K M
  let qM := Submodule.comap pM.subtype (adeleFilt k K D)
  have hqr : q ≤ r := Submodule.comap_mono (adeleFilt_mono k K hDM)
  let eR := Submodule.comapSubtypeEquivOfLe (adeleFilt_mono k K hMN)
  let qInR : Submodule k ↥r := Submodule.comap r.subtype q
  have hqmap : qM.map (eR.symm : pM →ₗ[k] r) = qInR := by
    rw [Submodule.map_equiv_eq_comap_symm eR.symm qM]
    rfl
  have eMq : (pM ⧸ qM) ≃ₗ[k] (r ⧸ qInR) := Submodule.Quotient.equiv qM qInR eR.symm hqmap
  have : Module.Finite k (r ⧸ qInR) := Module.Finite.equiv eMq
  have hker : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).ker = qInR := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).range = r.map q.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have eQuot : (r ⧸ qInR) ≃ₗ[k] r.map q.mkQ := by
    rw [← hker, ← hrange]
    exact LinearMap.quotKerEquivRange (q.mkQ.comp (r.subtype : r →ₗ[k] p))
  have : Module.Finite k (r.map q.mkQ) := Module.Finite.equiv eQuot
  have eThird := Submodule.quotientQuotientEquivQuotient q r hqr
  have : Module.Finite k (p ⧸ r) := by dsimp only [p, r]; infer_instance
  have : Module.Finite k ((p ⧸ q) ⧸ Submodule.map q.mkQ r) := Module.Finite.equiv eThird.symm
  exact Module.Finite.of_submodule_quotient (Submodule.map q.mkQ r)

theorem finiteAdeleFiltDiff_quotient_single_nat (D : DivisorA k K) (v : PlaceA k K) (n : ℕ) :
    Module.Finite k ((adeleFilt k K (D + Finsupp.single v (n : ℤ))) ⧸
      Submodule.comap (adeleFilt k K (D + Finsupp.single v (n : ℤ))).subtype
        (adeleFilt k K D)) := by
  induction n with
  | zero =>
      have heq : D + Finsupp.single v ((0 : ℕ) : ℤ) = D := by simp
      rw [heq]
      exact finiteAdeleFiltDiff_quotient_self k K D
  | succ n ih =>
      have heq : D + Finsupp.single v ((n + 1 : ℕ) : ℤ) =
          D + Finsupp.single v (n : ℤ) + Finsupp.single v 1 := by
        ext w
        simp only [Finsupp.add_apply, Finsupp.single_apply]
        split <;> omega
      have hDM : D ≤ D + Finsupp.single v (n : ℤ) := by
        intro w
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      have hMN : D + Finsupp.single v (n : ℤ) ≤
          D + Finsupp.single v (n : ℤ) + Finsupp.single v 1 := by
        intro w
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      let := ih
      have := finiteAdeleFiltDiff_quotient_single k K (D + Finsupp.single v (n : ℤ)) v
      rw [heq]
      exact finiteAdeleFiltDiff_quotient_mono_add k K hDM hMN

theorem finiteAdeleFiltDiff_quotient_add_effective (D E : DivisorA k K)
    (hE : IsEffective k K E) :
    Module.Finite k ((adeleFilt k K (D + E)) ⧸
      Submodule.comap (adeleFilt k K (D + E)).subtype (adeleFilt k K D)) := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero =>
      rw [add_zero]
      exact finiteAdeleFiltDiff_quotient_self k K D
  | single_add a b f ha hb ih =>
      have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
      have hff : IsEffective k K f := by
        intro w
        by_cases hw : w = a
        · subst w
          rw [hfa]
        · simpa [Finsupp.single_apply, hw] using hE w
      have hb0 : 0 ≤ b := by
        simpa [Finsupp.single_apply, hfa] using hE a
      let := ih D hff
      have := finiteAdeleFiltDiff_quotient_single_nat k K (D + f) a b.toNat
      have hbcast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
      have heq : D + (Finsupp.single a b + f) =
          (D + f) + Finsupp.single a (b.toNat : ℤ) := by
        rw [hbcast]
        abel
      have hDM : D ≤ D + f := by
        intro w
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (hff w)
      have hMN : D + f ≤ (D + f) + Finsupp.single a (b.toNat : ℤ) := by
        intro w
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      rw [heq]
      exact finiteAdeleFiltDiff_quotient_mono_add k K hDM hMN

theorem finiteAdeleFiltDiff_quotient_add_eq {M N : DivisorA k K}
    (hN : N = M + (N - M)) (hE : IsEffective k K (N - M)) :
    Module.Finite k ((adeleFilt k K N) ⧸
      Submodule.comap (adeleFilt k K N).subtype (adeleFilt k K M)) :=
  hN ▸ finiteAdeleFiltDiff_quotient_add_effective k K M (N - M) hE

theorem finrankAdeleFiltDiff_mono_add {D M N : DivisorA k K}
    (hDM : D ≤ M) (hMN : M ≤ N) :
    finrankAdeleFiltDiff k K D N =
      finrankAdeleFiltDiff k K D M + finrankAdeleFiltDiff k K M N := by
  let p := adeleFilt k K N
  let q := Submodule.comap p.subtype (adeleFilt k K D)
  let r := Submodule.comap p.subtype (adeleFilt k K M)
  have hqr : q ≤ r := Submodule.comap_mono (adeleFilt_mono k K hDM)
  have hDN : D ≤ N := hDM.trans hMN
  have hE := (le_iff_sub_effective k K).mp hDN
  have hEN := (le_iff_sub_effective k K).mp hMN
  have hND : D + (N - D) = N := by ext w; simp [sub_eq_add_neg]
  have hNM : M + (N - M) = N := by ext w; simp [sub_eq_add_neg]
  have : Module.Finite k (p ⧸ q) :=
    finiteAdeleFiltDiff_quotient_add_eq k K (M := D) hND.symm hE
  have : Module.Finite k (p ⧸ r) :=
    finiteAdeleFiltDiff_quotient_add_eq k K (M := M) hNM.symm hEN
  dsimp only [finrankAdeleFiltDiff]
  have e := Submodule.quotientQuotientEquivQuotient q r hqr
  have hadd := Submodule.finrank_quotient_add_finrank (r.map q.mkQ)
  have hrmap : Module.finrank k (r.map q.mkQ) = finrankAdeleFiltDiff k K D M := by
    let pM := adeleFilt k K M
    let qM := Submodule.comap pM.subtype (adeleFilt k K D)
    let qInR : Submodule k ↥r := Submodule.comap r.subtype q
    let eR := Submodule.comapSubtypeEquivOfLe (adeleFilt_mono k K hMN)
    have hqmap : qM.map (eR.symm : pM →ₗ[k] r) = qInR := by
      rw [Submodule.map_equiv_eq_comap_symm eR.symm qM]
      rfl
    have eM : (pM ⧸ qM) ≃ₗ[k] (r ⧸ qInR) := Submodule.Quotient.equiv qM qInR eR.symm hqmap
    have hker : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).ker = qInR := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    have hrange : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).range = r.map q.mkQ := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have eQuot : (r ⧸ qInR) ≃ₗ[k] r.map q.mkQ := by
      rw [← hker, ← hrange]
      exact LinearMap.quotKerEquivRange (q.mkQ.comp (r.subtype : r →ₗ[k] p))
    dsimp [finrankAdeleFiltDiff]
    rw [← eQuot.finrank_eq, eM.finrank_eq]
  calc
    Module.finrank k (↥p ⧸ q)
        = Module.finrank k ((↥p ⧸ q) ⧸ Submodule.map q.mkQ r) +
            Module.finrank k ↥(Submodule.map q.mkQ r) := hadd.symm
    _ = Module.finrank k (↥p ⧸ r) + finrankAdeleFiltDiff k K D M := by
      rw [e.finrank_eq, hrmap]
    _ = finrankAdeleFiltDiff k K D M + finrankAdeleFiltDiff k K M N := by
      dsimp only [finrankAdeleFiltDiff]
      rw [add_comm]

theorem finrankAdeleFiltDiff_add_one {D M : DivisorA k K} (v : PlaceA k K) (hDM : D ≤ M) :
    finrankAdeleFiltDiff k K D (M + Finsupp.single v 1) =
      finrankAdeleFiltDiff k K D M + placeDegree k K v := by
  have hMN : M ≤ M + Finsupp.single v 1 := by
    intro w
    simp only [Finsupp.add_apply]
    exact le_add_of_nonneg_right (by
      simp only [Finsupp.single_apply]
      split <;> omega)
  rw [finrankAdeleFiltDiff_mono_add k K hDM hMN, finrankAdeleFiltDiff_single_one]

theorem finrankAdeleFiltDiff_add_effective (D E : DivisorA k K)
    (hE : IsEffective k K E) :
    finrankAdeleFiltDiff k K D (D + E) = (deg k K E).toNat := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero =>
      rw [add_zero, finrankAdeleFiltDiff, deg_zero]
      have hp : Submodule.comap (adeleFilt k K D).subtype (adeleFilt k K D) = ⊤ := by
        ext a
        simp
      rw [hp]
      exact Module.finrank_eq_zero_of_subsingleton k _
  | single_add a b f ha hb ih =>
      have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
      have hff : IsEffective k K f := by
        intro w
        by_cases hw : w = a
        · subst w
          rw [hfa]
        · have hwE := hE w
          simpa [Finsupp.single_apply, hw] using hwE
      have hb0 : 0 ≤ b := by
        have haE := hE a
        simpa [Finsupp.single_apply, hfa] using haE
      let M := D + f
      let N := M + Finsupp.single a (b.toNat : ℤ)
      have hDM : D ≤ M := by
        intro w
        dsimp only [M]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (hff w)
      have hMN : M ≤ N := by
        intro w
        dsimp only [N]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      have hfirst := ih D hff
      have hsecond : finrankAdeleFiltDiff k K M N = b.toNat * placeDegree k K a := by
        have hbcast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
        have heq : N = M + Finsupp.single a (b.toNat : ℤ) := rfl
        rw [heq]
        induction b.toNat with
        | zero =>
            simp only [Nat.cast_zero, Finsupp.single_zero, add_zero, zero_mul]
            rw [finrankAdeleFiltDiff]
            have hp : Submodule.comap (adeleFilt k K M).subtype (adeleFilt k K M) = ⊤ := by
              ext a
              simp
            rw [hp]
            exact Module.finrank_eq_zero_of_subsingleton k _
        | succ n ihN =>
            let P := M + Finsupp.single a (n : ℤ)
            have hMP : M ≤ P := by
              intro w
              dsimp only [P]
              simp only [Finsupp.add_apply]
              exact le_add_of_nonneg_right (by
                simp only [Finsupp.single_apply]
                split <;> omega)
            have heqP : M + Finsupp.single a ((n + 1 : ℕ) : ℤ) = P + Finsupp.single a 1 := by
              dsimp [P]
              ext w
              simp only [Finsupp.add_apply, Finsupp.single_apply]
              split <;> omega
            have hadd := finrankAdeleFiltDiff_add_one k K (M := P) a hMP
            have hcast : M + Finsupp.single a (Int.ofNat (n + 1)) =
                M + Finsupp.single a ((n + 1 : ℕ) : ℤ) := by simp [Int.ofNat_eq_natCast]
            calc
              finrankAdeleFiltDiff k K M (M + Finsupp.single a ↑(n + 1))
                  = finrankAdeleFiltDiff k K M (M + Finsupp.single a (Int.ofNat (n + 1))) := by
                simp [Int.ofNat_eq_natCast]
              _ = finrankAdeleFiltDiff k K M (M + Finsupp.single a ((n + 1 : ℕ) : ℤ)) := by
                rw [hcast]
              _ = finrankAdeleFiltDiff k K M (P + Finsupp.single a 1) := by rw [heqP]
              _ = finrankAdeleFiltDiff k K M P + placeDegree k K a := hadd
              _ = n * placeDegree k K a + placeDegree k K a := by
                rw [← ihN]
              _ = (n + 1) * placeDegree k K a := by ring
      have hdegf : 0 ≤ deg k K f := deg_nonneg k K hff
      have hdegE : deg k K (Finsupp.single a b + f) =
          b * (placeDegree k K a : ℤ) + deg k K f := by
        rw [deg_add]
        simp [deg]
      have hdegE0 : 0 ≤ deg k K (Finsupp.single a b + f) := deg_nonneg k K hE
      have hdegNat : (deg k K (Finsupp.single a b + f)).toNat =
          b.toNat * placeDegree k K a + (deg k K f).toNat := by
        have hfcast : ((deg k K f).toNat : ℤ) = deg k K f := Int.toNat_of_nonneg hdegf
        have hEcast : ((deg k K (Finsupp.single a b + f)).toNat : ℤ) =
            deg k K (Finsupp.single a b + f) := Int.toNat_of_nonneg hdegE0
        apply Int.ofNat_injective
        change ((deg k K (Finsupp.single a b + f)).toNat : ℤ) =
          ((b.toNat * placeDegree k K a + (deg k K f).toNat : ℕ) : ℤ)
        rw [hEcast, Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hb0, hfcast]
        exact hdegE
      have htotal : finrankAdeleFiltDiff k K D N =
          (deg k K (Finsupp.single a b + f)).toNat := by
        have hadd := finrankAdeleFiltDiff_mono_add k K hDM hMN
        rw [hadd, hfirst, hsecond, hdegNat, Nat.add_comm]
      have heq : D + (Finsupp.single a b + f) = N := by
        dsimp only [N, M]
        rw [Int.toNat_of_nonneg hb0]
        abel
      rw [heq]
      exact htotal

theorem finrank_adeleFilt_quotient {D D' : DivisorA k K} (h : D ≤ D') :
    finrankAdeleFiltDiff k K D D' = (deg k K (D' - D)).toNat := by
  have hE : IsEffective k K (D' - D) := (le_iff_sub_effective k K).mp h
  have hrank := finrankAdeleFiltDiff_add_effective k K D (D' - D) hE
  have heq : D + (D' - D) = D' := by abel
  rw [heq] at hrank
  exact hrank

theorem finrank_map_comap_mkQ_eq_quotient {D' : DivisorA k K}
    {s t : Submodule k (AdeleSpace k K)} (_hs : s ≤ adeleFilt k K D')
    (ht : t ≤ adeleFilt k K D') (_hst : s ≤ t) :
    Module.finrank k (Submodule.map (Submodule.comap (adeleFilt k K D').subtype s).mkQ
      (Submodule.comap (adeleFilt k K D').subtype t)) =
      Module.finrank k
        (↥(Submodule.comap (adeleFilt k K D').subtype t) ⧸
          Submodule.comap (Submodule.comap (adeleFilt k K D').subtype t).subtype
            (Submodule.comap (adeleFilt k K D').subtype s)) := by
  classical
  let p := adeleFilt k K D'
  let qp := Submodule.comap p.subtype s
  let qt := Submodule.comap p.subtype t
  let st := Submodule.comap t.subtype s
  let qpInQt := Submodule.comap qt.subtype qp
  let : AddCommGroup ↥t := Submodule.addCommGroup _
  let : Module k ↥t := Submodule.module _
  let : AddCommGroup ↥qt := Submodule.addCommGroup _
  let : Module k ↥qt := Submodule.module _
  let eT := Submodule.comapSubtypeEquivOfLe ht
  have hmap : st.map (eT.symm : ↥t →ₗ[k] ↥qt) = qpInQt := by
    ext x
    simp [Submodule.mem_comap, st, qpInQt, qp, qt, eT]
  have hker : (qp.mkQ.comp (qt.subtype : qt →ₗ[k] p)).ker = qpInQt := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : (qp.mkQ.comp (qt.subtype : qt →ₗ[k] p)).range = Submodule.map qp.mkQ qt := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have eQuot : (↥qt ⧸ qpInQt) ≃ₗ[k] Submodule.map qp.mkQ qt := by
    rw [← hker, ← hrange]
    exact LinearMap.quotKerEquivRange (qp.mkQ.comp (qt.subtype : qt →ₗ[k] p))
  have eTS : ((↥t) ⧸ st) ≃ₗ[k] ((↥qt) ⧸ qpInQt) :=
    Submodule.Quotient.equiv st qpInQt eT.symm hmap
  rw [← eQuot.finrank_eq, ← eTS.finrank_eq]

theorem sandwich {D D' : DivisorA k K} (h : D ≤ D') :
    sandwichRank k K D D' = deg k K D' - ell k K D' - (deg k K D - ell k K D) := by
  let p := adeleFilt k K D'
  let s := adeleFilt k K D
  let r := diagonalSubmodule k K
  let l := Submodule.map (diagonal k K) (RRspace k K D')
  let t := l ⊔ s
  have hs_le_p : s ≤ p := adeleFilt_mono k K h
  have hst : s ≤ t := le_sup_right
  have htp : t ≤ p := by
    rintro x hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    rcases hy with ⟨f, hf, rfl⟩
    exact Submodule.add_mem p
      hf (hs_le_p hz)
  have hmod : p ⊓ (s + r) = s + p ⊓ r := by
    apply le_antisymm
    · rintro x ⟨hxp, hxsr⟩
      rcases Submodule.mem_sup.mp hxsr with ⟨a, has, y, hy, rfl⟩
      obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hy
      refine Submodule.mem_sup.mpr ⟨a, has, (diagonal k K f), ?_, rfl⟩
      exact Submodule.mem_inf.mpr
        ⟨(by simpa [sub_add_cancel] using Submodule.sub_mem p hxp (hs_le_p has)), hy⟩
    · rintro x hx
      rcases Submodule.mem_sup.mp hx with ⟨a, has, y, hy, rfl⟩
      rcases Submodule.mem_inf.mp hy with ⟨hyp, hyr⟩
      refine ⟨Submodule.add_mem p (hs_le_p has) hyp,
        Submodule.add_mem (s + r) (Submodule.mem_sup_left has) (Submodule.mem_sup_right hyr)⟩
  have hinter : p ⊓ (s + r) = t := by
    have hpr : p ⊓ r = l := adeleFilt_inf_diagonal k K D'
    calc p ⊓ (s + r) = s + (p ⊓ r) := hmod
      _ = s + l := by rw [hpr]
      _ = t := by simp [t, Submodule.add_eq_sup, sup_comm]
  let : AddCommGroup ↥p := Submodule.addCommGroup _
  let : Module k ↥p := Submodule.module _
  let : AddCommGroup ↥(p + r) := Submodule.addCommGroup _
  let : Module k ↥(p + r) := Submodule.module _
  let qp := Submodule.comap p.subtype s
  let qt := Submodule.comap p.subtype t
  have hqp : qp ≤ qt := Submodule.comap_mono hst
  have hpsum : p ⊔ (s + r) = p + r := by
    rw [← Submodule.add_eq_sup]
    apply le_antisymm
    · refine sup_le le_sup_left (add_le_add hs_le_p le_rfl)
    · intro x hx
      rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
      have hb' : b ∈ s + r := Submodule.mem_sup_right hb
      exact Submodule.add_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb')
  have : AddCommGroup ↥(p ⊔ (s + r)) := Submodule.addCommGroup _
  have : Module k ↥(p ⊔ (s + r)) := Submodule.module _
  have e1 := LinearMap.quotientInfEquivSupQuotient p (s + r)
  have hsand :
      Module.finrank k (↥(p + r) ⧸ Submodule.comap (p + r).subtype (s + r)) =
        Module.finrank k (↥p ⧸ qt) := by
    have hinfl :
        Submodule.comap p.subtype p ⊓ Submodule.comap p.subtype (s + r) = qt := by
      rw [← Submodule.comap_inf, hinter]
    have hfin := e1.symm.finrank_eq
    rw [← hpsum.symm, hinfl] at hfin
    exact hfin
  have hE : IsEffective k K (D' - D) := (le_iff_sub_effective k K).mp h
  have e2 := Submodule.quotientQuotientEquivQuotient qp qt hqp
  have hdiv : D + (D' - D) = D' := by ext w; simp [sub_eq_add_neg]
  have : Module.Finite k (↥p ⧸ qp) :=
    finiteAdeleFiltDiff_quotient_add_eq k K (M := D) hdiv.symm hE
  have hsecond : Module.finrank k (Submodule.map qp.mkQ qt) = finrankRRspaceDiff k K D D' := by
    have hld : l ⊓ s = Submodule.map (diagonal k K) (RRspace k K D) := by
      refine Submodule.ext fun a => ⟨?_, ?_⟩
      · rintro ⟨hxl, hxs⟩
        rcases hxl with ⟨f, hf, rfl⟩
        refine ⟨f, fun v => ?_, rfl⟩
        have hxv := hxs v
        simpa [memRRspace, memAdeleFilt, placeValuation, diagonal, adeleFilt, s] using hxv
      · rintro ⟨f, hf, rfl⟩
        refine ⟨⟨f, RRspace_mono k K h hf, rfl⟩, fun v => ?_⟩
        simpa [memRRspace, memAdeleFilt, placeValuation, diagonal, adeleFilt, s] using hf v
    have hfin_map := finrank_map_comap_mkQ_eq_quotient k K hs_le_p htp hst
    let st := Submodule.comap t.subtype s
    let qpInQt := Submodule.comap qt.subtype qp
    let : AddCommGroup ↥t := Submodule.addCommGroup _
    let : Module k ↥t := Submodule.module _
    let eT := Submodule.comapSubtypeEquivOfLe htp
    have hmap : st.map (eT.symm : ↥t →ₗ[k] ↥qt) = qpInQt := by
      ext x
      simp [Submodule.mem_comap, st, qpInQt, qp, qt, eT]
    have eTS : ((↥t) ⧸ st) ≃ₗ[k] ((↥qt) ⧸ qpInQt) :=
      Submodule.Quotient.equiv st qpInQt eT.symm hmap
    have e3 := LinearMap.quotientInfEquivSupQuotient l s
    let : AddCommGroup ↥(l ⊔ s) := Submodule.addCommGroup _
    let : Module k ↥(l ⊔ s) := Submodule.module _
    let : AddCommGroup ↥l := Submodule.addCommGroup _
    let : Module k ↥l := Submodule.module _
    dsimp [finrankRRspaceDiff]
    calc
      Module.finrank k (Submodule.map qp.mkQ qt)
          = Module.finrank k (↥qt ⧸ Submodule.comap qt.subtype qp) := hfin_map
      _ = Module.finrank k (↥t ⧸ st) := eTS.finrank_eq.symm
      _ = Module.finrank k (↥(l ⊔ s) ⧸ Submodule.comap (l ⊔ s).subtype s) := rfl
      _ = Module.finrank k
          (↥l ⧸ (Submodule.comap l.subtype l ⊓ Submodule.comap l.subtype s)) :=
        e3.symm.finrank_eq
      _ = Module.finrank k
          ((RRspace k K D') ⧸ Submodule.comap (RRspace k K D').subtype (RRspace k K D)) := by
        let pR := RRspace k K D'
        let qR := Submodule.comap pR.subtype (RRspace k K D)
        let qInL : Submodule k ↥l :=
          Submodule.comap l.subtype (Submodule.map (diagonal k K) (RRspace k K D))
        let f' := (diagonal k K).comp pR.subtype
        have hf' : ∀ g, f' g ∈ l := fun g => Submodule.mem_map.mpr ⟨g, g.property, rfl⟩
        let f : pR →ₗ[k] l := f'.codRestrict l hf'
        have hf_ker : f.ker = ⊥ := by
          rw [eq_bot_iff]
          intro g hg
          apply Subtype.ext
          let w : PlaceA k K := Classical.choice (nonempty_placeA k K)
          have hfg := LinearMap.mem_ker.mp hg
          have hzero : (f g : AdeleSpace k K) = 0 := congrArg Subtype.val hfg
          have hz : ((f g : AdeleSpace k K).val : PlaceA k K → K) w = 0 := by
            rw [hzero]
            simp
          simpa [f, f', diagonal, LinearMap.comp_apply, Submodule.coe_subtype] using hz
        have hf_inj : Function.Injective f := by
          intro g₁ g₂ hfg
          have hmem : g₁ - g₂ ∈ f.ker := by
            rw [LinearMap.mem_ker, map_sub, hfg, sub_self]
          rw [hf_ker] at hmem
          exact sub_eq_zero.mp hmem
        have hf_surj : Function.Surjective f := by
          rintro ⟨a, g, hg, rfl⟩
          exact ⟨⟨g, hg⟩, rfl⟩
        let eL : pR ≃ₗ[k] l := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
        have hmap : qR.map f = qInL := by
          ext x
          simp only [Submodule.mem_map, Submodule.mem_comap, qR, qInL, l]
          constructor
          · rintro ⟨g, hg, heq⟩
            refine ⟨g.val, ?_, ?_⟩
            · simpa [mem_RRspace_iff] using hg
            · rw [← heq]
              rfl
          · rintro ⟨y, hy, hxy⟩
            refine ⟨⟨y, RRspace_mono k K h hy⟩, ?_, ?_⟩
            · simpa [mem_RRspace_iff] using hy
            · apply Subtype.ext
              exact hxy
        have eQuot : (pR ⧸ qR) ≃ₗ[k] (l ⧸ qInL) := Submodule.Quotient.equiv qR qInL eL hmap
        rw [← Submodule.comap_inf, hld, eQuot.finrank_eq]
  have hsplit :
      Module.finrank k (↥p ⧸ qt) =
        finrankAdeleFiltDiff k K D D' - finrankRRspaceDiff k K D D' := by
    unfold finrankAdeleFiltDiff
    have hfin := finrank_adeleFilt_quotient k K h
    have hle' : finrankRRspaceDiff k K D D' ≤ finrankAdeleFiltDiff k K D D' := by
      rw [hfin]
      exact finrank_RRspace_quotient_le k K h
    have hadd := Submodule.finrank_quotient_add_finrank (Submodule.map qp.mkQ qt)
    rw [e2.finrank_eq, hsecond] at hadd
    exact (Nat.sub_eq_of_eq_add hadd.symm).symm
  have hfin := finrank_adeleFilt_quotient k K h
  have hdeg : 0 ≤ deg k K (D' - D) := deg_nonneg k K hE
  have htoNat : ((deg k K (D' - D)).toNat : ℤ) = deg k K (D' - D) :=
    Int.toNat_of_nonneg hdeg
  have hrr := finrankRRspaceDiff_add_ell k K h
  have hle : finrankRRspaceDiff k K D D' ≤ finrankAdeleFiltDiff k K D D' := by
    rw [hfin]
    exact finrank_RRspace_quotient_le k K h
  dsimp only [sandwichRank]
  have hmain :
      (Int.ofNat (Module.finrank k (↥(p + r) ⧸ Submodule.comap (p + r).subtype (s + r)))) =
        (finrankAdeleFiltDiff k K D D' - finrankRRspaceDiff k K D D') := by
    rw [hsand, hsplit]
    simp only [Int.ofNat_eq_natCast, Nat.cast_sub hle]
  rw [hmain, hfin, htoNat]
  have hrrZ : (finrankRRspaceDiff k K D D' : ℤ) = ell k K D' - ell k K D := by
    rw [finrankRRspaceDiff, ell, ell,
      ← (Submodule.comapSubtypeEquivOfLe (RRspace_mono k K h)).finrank_eq] at hrr ⊢
    omega
  rw [hrrZ, deg_sub k K D' D]
  omega

theorem sandwichDiagonal_inter {D D' : DivisorA k K} (h : D ≤ D') :
    adeleFilt k K D' ⊓ (adeleFilt k K D + diagonalSubmodule k K) =
      Submodule.map (diagonal k K) (RRspace k K D') ⊔ adeleFilt k K D := by
  let p := adeleFilt k K D'
  let s := adeleFilt k K D
  let r := diagonalSubmodule k K
  let l := Submodule.map (diagonal k K) (RRspace k K D')
  let t := l ⊔ s
  have hs_le_p : s ≤ p := adeleFilt_mono k K h
  have hmod : p ⊓ (s + r) = s + p ⊓ r := by
    apply le_antisymm
    · rintro x ⟨hxp, hxsr⟩
      rcases Submodule.mem_sup.mp hxsr with ⟨a, has, y, hy, rfl⟩
      obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hy
      refine Submodule.mem_sup.mpr ⟨a, has, (diagonal k K f), ?_, rfl⟩
      exact Submodule.mem_inf.mpr
        ⟨(by simpa [sub_add_cancel] using Submodule.sub_mem p hxp (hs_le_p has)), hy⟩
    · rintro x hx
      rcases Submodule.mem_sup.mp hx with ⟨a, has, y, hy, rfl⟩
      rcases Submodule.mem_inf.mp hy with ⟨hyp, hyr⟩
      refine ⟨Submodule.add_mem p (hs_le_p has) hyp,
        Submodule.add_mem (s + r) (Submodule.mem_sup_left has) (Submodule.mem_sup_right hyr)⟩
  have hpr : p ⊓ r = l := adeleFilt_inf_diagonal k K D'
  calc
    p ⊓ (s + r) = s + p ⊓ r := hmod
    _ = s + l := by rw [hpr]
    _ = t := by simp [t, Submodule.add_eq_sup, sup_comm]

theorem sandwichDiagonalSubmodule_eq_of_rank_zero {D D' : DivisorA k K} (hle : D ≤ D')
    (h0 : sandwichRank k K D D' = 0) :
    adeleFilt k K D' + diagonalSubmodule k K = adeleFilt k K D + diagonalSubmodule k K := by
  let p := adeleFilt k K D'
  let s := adeleFilt k K D
  let r := diagonalSubmodule k K
  let t := Submodule.map (diagonal k K) (RRspace k K D') ⊔ s
  let qp := Submodule.comap p.subtype s
  let qt := Submodule.comap p.subtype t
  have hqp_le : qp ≤ qt := Submodule.comap_mono le_sup_right
  have hE : IsEffective k K (D' - D) := (le_iff_sub_effective k K).mp hle
  have hdiv : D + (D' - D) = D' := by abel
  have : Module.Finite k (↥p ⧸ qp) :=
    finiteAdeleFiltDiff_quotient_add_eq k K (M := D) hdiv.symm hE
  have htp : t ≤ p := by
    rintro x hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    rcases hy with ⟨f, hf, rfl⟩
    exact Submodule.add_mem p
      hf (adeleFilt_mono k K hle hz)
  let : AddCommGroup ↥p := Submodule.addCommGroup _
  let : Module k ↥p := Submodule.module _
  let : AddCommGroup ↥(p + r) := Submodule.addCommGroup _
  let : Module k ↥(p + r) := Submodule.module _
  let : AddCommGroup ↥(adeleFilt k K D' + diagonalSubmodule k K) := Submodule.addCommGroup _
  let : Module k ↥(adeleFilt k K D' + diagonalSubmodule k K) := Submodule.module _
  have hfin_qt : Module.finrank k (↥p ⧸ qt) = 0 := by
    have hfin_sandwich :
        Module.finrank k
            (↥(adeleFilt k K D' + diagonalSubmodule k K) ⧸
              Submodule.comap (adeleFilt k K D' + diagonalSubmodule k K).subtype
                (adeleFilt k K D + diagonalSubmodule k K)) = 0 :=
      Int.ofNat_eq_zero.mp (by simpa [sandwichRank] using h0)
    have hinter := sandwichDiagonal_inter k K hle
    have hinfl : Submodule.comap p.subtype p ⊓ Submodule.comap p.subtype (s + r) = qt := by
      rw [← Submodule.comap_inf, hinter]
    have hpsum : p ⊔ (s + r) = p + r := by
      rw [← Submodule.add_eq_sup]
      apply le_antisymm
      · refine sup_le le_sup_left (add_le_add (adeleFilt_mono k K hle) le_rfl)
      · intro x hx
        rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
        have hb' : b ∈ s + r := Submodule.mem_sup_right hb
        exact Submodule.add_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb')
    have hsand :=
      (LinearMap.quotientInfEquivSupQuotient p (s + r)).symm.finrank_eq
    rw [hpsum, hinfl] at hsand
    exact hsand.symm.trans hfin_sandwich
  have : Module.Finite k (↥p ⧸ qt) :=
    Module.Finite.equiv (Submodule.quotientQuotientEquivQuotient qp qt hqp_le)
  have hrk : Module.rank k (↥p ⧸ qt) = 0 := by
    rw [← Module.finrank_eq_rank, hfin_qt, Nat.cast_zero]
  have hsub : Subsingleton (↥p ⧸ qt) := rank_zero_iff.mp hrk
  have htopqt : qt = ⊤ := Submodule.Quotient.subsingleton_iff.mp hsub
  have hp_le_t : p ≤ t := Submodule.comap_subtype_eq_top.mp htopqt
  have hp_eq_t : p = t := le_antisymm hp_le_t htp
  have hinter := sandwichDiagonal_inter k K hle
  have hp_le_sr : p ≤ s + r := by
    have h := inf_le_right (a := p) (b := s + r)
    rw [hinter] at h
    exact hp_eq_t.symm ▸ h
  have hsr_le_pr : s + r ≤ p + r := add_le_add (adeleFilt_mono k K hle) le_rfl
  have hpr_le_sr : p + r ≤ s + r := by
    intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨a, hap, y, hyr, rfl⟩
    rcases Submodule.mem_sup.mp (hp_le_sr hap) with ⟨b, hbs, w, hwr, hbc⟩
    refine Submodule.mem_sup.mpr
      ⟨b, hbs, w + y, Submodule.add_mem r hwr hyr, by rw [← hbc, add_assoc]⟩
  exact le_antisymm hpr_le_sr hsr_le_pr

end FunctionField.Chart

end
