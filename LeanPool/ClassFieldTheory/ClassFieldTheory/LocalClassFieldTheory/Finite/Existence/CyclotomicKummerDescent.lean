/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.NumberTheory.Cyclotomic.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.MaximalKummerNorm
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormSubgroupFunctoriality
/-!
# Cyclotomic descent for maximal Kummer norm subgroups

For an exponent nonzero in the base field, adjoining the roots of unity,
applying maximal Kummer theory, and descending the norm inclusion produces a
finite Galois extension whose norm subgroup is contained in `Kˣⁿ`.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped NNReal ValuativeRel
open CyclicCohomology KummerTheory ClassFormation
open LocalFieldTheory.DiscreteValuationField LocalFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- There is a finite Galois extension whose local norm subgroup is contained
in the `n`-th-power subgroup, without assuming roots of unity in the base. -/
theorem exists_finiteGalois_normSubgroup_le_powMonoidHom_range
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
      localNormSubgroup K (E : IntermediateField K (SeparableClosure K)) ≤
        (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : NeZero ((n : ℕ) : K) := ⟨hnK⟩
  let C := CyclotomicField (n : ℕ) K
  let : FiniteDimensional K C :=
    IsCyclotomicExtension.finiteDimensional {(n : ℕ)} K C
  let : IsGalois K C :=
    IsCyclotomicExtension.isGalois {(n : ℕ)} K C
  obtain ⟨zeta, hzeta⟩ :=
    (CyclotomicField.isCyclotomicExtension (n : ℕ) K).exists_isPrimitiveRoot
      (Set.mem_singleton (n : ℕ)) n.ne_zero
  let j : C →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let K1 := AlgHom.fieldRange j
  let eC : C ≃ₐ[K] K1 := AlgEquiv.ofInjectiveField j
  let : FiniteDimensional K K1 := eC.toLinearEquiv.finiteDimensional
  let : IsGalois K K1 := IsGalois.of_algEquiv eC
  have hnK1 : ((n : ℕ) : K1) ≠ 0 := by
    intro h
    apply hnK
    apply (algebraMap K K1).injective
    simpa using h
  have hmu1 : (primitiveRoots (n : ℕ) K1).Nonempty :=
    ⟨eC zeta, (mem_primitiveRoots n.pos).2
      (hzeta.map_of_injective eC.injective)⟩
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  let : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : Valued K (ValuativeRel.ValueGroupWithZero K) := inferInstance
  let : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)
  let : CompleteSpace K := inferInstance
  let : NontriviallyNormedField K1 :=
    spectralNorm.nontriviallyNormedField K K1
  let : NormedSpace K K1 := spectralNorm.normedSpace K K1
  let : NormedAlgebra K K1 :=
    { (inferInstance : Algebra K K1) with
      norm_smul_le := NormedSpace.norm_smul_le }
  let : CompleteSpace K1 := spectralNorm.completeSpace K K1
  let : LocallyCompactSpace K1 :=
    LocallyCompactSpace.of_finiteDimensional_of_complete K K1
  let : IsUltrametricDist K1 :=
    ⟨fun x y z => by
      change ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖
      rw [← sub_add_sub_cancel x y z]
      exact isNonarchimedean_spectralNorm
        (K := K) (L := K1) (x - y) (y - z)⟩
  let : Valued K1 ℝ≥0 := NormedField.toValued
  let vK1 : Valuation K1 ℝ≥0 := Valued.v
  let : vK1.IsNontrivial :=
    (inferInstance : (NormedField.valuation (K := K1)).IsNontrivial)
  let : ValuativeRel K1 := ValuativeRel.ofValuation vK1
  let : vK1.Compatible := Valuation.Compatible.ofValuation vK1
  let : ValuativeRel.IsNontrivial K1 :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vK1).2 inferInstance
  let : IsValuativeTopology K1 :=
    isValuativeTopology_of_valued_ofValuation K1 ℝ≥0
  let : IsNonarchimedeanLocalField K1 :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let : IsScalarTower K K1 (SeparableClosure K) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Algebra.IsSeparable K1 (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable K K1 (SeparableClosure K)
  let : IsSepClosure K1 (SeparableClosure K) :=
    { sep_closed := inferInstance
      separable := inferInstance }
  let Delta := KummerTheory.maximalKummerSubgroup K1 n
  let L1 := kummerRadicalExtension
    (K := K1) (Omega := SeparableClosure K) n Delta.1
  let : IsGalois K1 L1 :=
    kummerRadicalExtension_isGalois
      (K := K1) (Omega := SeparableClosure K) n Delta.1
  let : FiniteDimensional K1 L1 :=
    KummerTheory.maximalKummerRadicalExtension_finiteDimensional
      (K := K1) (Omega := SeparableClosure K) n hnK1 hmu1
  let : Module.Free K1 L1 := Module.Free.of_divisionRing K1 L1
  have hnormK1 :
      localNormSubgroup K1 L1 = (powMonoidHom (n : ℕ) : K1ˣ →* K1ˣ).range := by
    simpa only [L1, Delta] using
      maximalKummerNormSubgroup_eq_powMonoidHom_range
        (K := K1) (Omega := SeparableClosure K) n hnK1 hmu1
  have hnormL1 :
      localNormSubgroup K L1 ≤ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
    rintro x ⟨y, rfl⟩
    have hy : normUnits K1 L1 y ∈ (powMonoidHom (n : ℕ) : K1ˣ →* K1ˣ).range := by
      rw [← hnormK1]
      exact ⟨y, rfl⟩
    rw [MonoidHom.mem_range] at hy ⊢
    obtain ⟨a, ha⟩ := hy
    refine ⟨normUnits K K1 a, ?_⟩
    calc
      normUnits K K1 a ^ (n : ℕ) =
          normUnits K K1 (a ^ (n : ℕ)) := by rw [map_pow]
      _ = normUnits K K1 (normUnits K1 L1 y) := congrArg _ ha
      _ = normUnits K L1 y := LocalFieldTheory.normUnits_tower K K1 L1 y
  let L0 := L1.restrictScalars K
  let : FiniteDimensional K L1 := FiniteDimensional.trans K K1 L1
  let eLin : L0 ≃ₗ[K] L1 :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro x; ext; rfl
      map_add' := by intro x y; ext; rfl
      map_smul' := by intro a x; ext; rfl }
  let : FiniteDimensional K L0 := Module.Finite.equiv eLin.symm
  let eL : L1 ≃ₐ[K] L0 :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro x; ext; rfl
      map_add' := by intro x y; ext; rfl
      map_mul' := by intro x y; ext; rfl
      commutes' := by intro x; ext; rfl }
  have hnormL0 :
      localNormSubgroup K L0 ≤ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
    rw [LocalFieldTheory.normSubgroup_algEquiv K L1 L0 eL]
    exact hnormL1
  let F := IntermediateField.normalClosure K L0 (SeparableClosure K)
  let : FiniteDimensional K F :=
    normalClosure.is_finiteDimensional K L0 (SeparableClosure K)
  let : IsGalois K F :=
    IsGalois.normalClosure K L0 (SeparableClosure K)
  let hAlgL0F : Algebra L0 F :=
    (IntermediateField.inclusion
      (IntermediateField.le_normalClosure L0)).toAlgebra
  let : SMul L0 F := Algebra.toSMul (self := hAlgL0F)
  let : Module L0 F := @Algebra.toModule L0 F _ _ hAlgL0F
  let : IsScalarTower K L0 F := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : FiniteDimensional L0 F := FiniteDimensional.right K L0 F
  have hnormFL0 : localNormSubgroup K F ≤ localNormSubgroup K L0 :=
    LocalFieldTheory.normSubgroup_le_of_tower K L0 F
  have hnormF : localNormSubgroup K F ≤ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
    intro x hx
    exact hnormL0 (hnormFL0 hx)
  let E : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { toIntermediateField := F
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  exact ⟨E, by simpa [E] using hnormF⟩

end LocalClassFieldTheory

end
