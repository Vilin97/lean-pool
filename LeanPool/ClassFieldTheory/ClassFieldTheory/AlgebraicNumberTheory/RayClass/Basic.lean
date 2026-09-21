/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalTopology
import Mathlib.RingTheory.Ideal.Quotient.Operations
/-!
# Finite ray-modulus data

This file contains the finite local data used by ray congruence subgroups.
A full modulus, including a selected set of real places, is defined in
`AlgebraicNumberTheory.RayClass.FullModulus`.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-- A finite ray modulus. Its finite support records the prime powers
dividing the modulus. -/
abbrev FiniteModulus (K : Type*) [Field K] [NumberField K] :=
  HeightOneSpectrum (𝓞 K) →₀ ℕ

/-- Reduction of local integral units modulo the `n`-th power of the maximal
ideal. -/
def localHigherUnitMap
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (v.adicCompletionIntegers K).units →*
      ((v.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ n)ˣ :=
  (Units.map
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ n)).toMonoidHom).comp
    (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.toMonoidHom

/-- The local higher unit group `U_v^(n)`. -/
def localHigherUnitGroup
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (v.adicCompletion K)ˣ :=
  Subgroup.map
    (v.adicCompletionIntegers K).units.subtype
    (localHigherUnitMap v n).ker

theorem mem_localHigherUnitGroup_iff
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ localHigherUnitGroup v n ↔
      ∃ y : (v.adicCompletionIntegers K).units,
        (y : (v.adicCompletion K)ˣ) = x ∧
        localHigherUnitMap v n y = 1 := by
  rw [localHigherUnitGroup, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, rfl, MonoidHom.mem_ker.mp hy⟩
  · rintro ⟨y, rfl, hy⟩
    exact ⟨y, MonoidHom.mem_ker.mpr hy, rfl⟩

/-- The zeroth higher unit group is the full group of local integral
units. -/
theorem localHigherUnitGroup_zero
    (v : HeightOneSpectrum (𝓞 K)) :
    localHigherUnitGroup v 0 =
      (v.adicCompletionIntegers K).units := by
  ext x
  rw [mem_localHigherUnitGroup_iff]
  constructor
  · rintro ⟨y, rfl, _hy⟩
    exact y.property
  · intro hx
    let y : (v.adicCompletionIntegers K).units := ⟨x, hx⟩
    refine ⟨y, rfl, ?_⟩
    change Units.map
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ 0)).toMonoidHom
        ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y) =
      1
    let : Subsingleton
        ((v.adicCompletionIntegers K) ⧸
          (IsLocalRing.maximalIdeal
            (v.adicCompletionIntegers K)) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    apply Units.ext
    exact Subsingleton.elim _ _

/-- Positivity at a real infinite place.  At a complex place the condition
is vacuous, so this is the whole local multiplicative group. -/
def infinitePositiveSubgroup (v : InfinitePlace K) :
    Subgroup v.Completionˣ where
  carrier := {x | ∀ hv : v.IsReal,
    0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
      hv (x : v.Completion)}
  one_mem' hv := by simp
  mul_mem' {x y} hx hy hv := by
    change 0 <
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
        hv ((x : v.Completion) * (y : v.Completion))
    rw [map_mul]
    exact mul_pos (hx hv) (hy hv)
  inv_mem' {x} hx hv := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_pos.mpr (hx hv)

omit [NumberField K] in
@[simp]
theorem mem_infinitePositiveSubgroup_iff
    (v : InfinitePlace K) (x : v.Completionˣ) :
    x ∈ infinitePositiveSubgroup v ↔
      ∀ hv : v.IsReal,
        0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
          hv (x : v.Completion) :=
  Iff.rfl

/-- The finite idele congruence subgroup attached to a modulus. -/
def finiteCongruenceSubgroup (m : FiniteModulus K) :
    Subgroup (FiniteIdeleGroup K) where
  carrier := {a | ∀ v, a v ∈ localHigherUnitGroup v (m v)}
  one_mem' v := (localHigherUnitGroup v (m v)).one_mem
  mul_mem' ha hb v :=
    (localHigherUnitGroup v (m v)).mul_mem (ha v) (hb v)
  inv_mem' ha v :=
    (localHigherUnitGroup v (m v)).inv_mem (ha v)

@[simp]
theorem mem_finiteCongruenceSubgroup_iff
    (m : FiniteModulus K) (a : FiniteIdeleGroup K) :
    a ∈ finiteCongruenceSubgroup m ↔
      ∀ v, a v ∈ localHigherUnitGroup v (m v) :=
  Iff.rfl

/-- Ideles positive at every real infinite place. -/
def narrowInfiniteCongruenceSubgroup :
    Subgroup (InfiniteIdeleGroup K) :=
  Subgroup.comap ContinuousMulEquiv.piUnits.toMonoidHom
    (Subgroup.pi Set.univ (fun v => infinitePositiveSubgroup v))

omit [NumberField K] in
@[simp]
theorem mem_narrowInfiniteCongruenceSubgroup_iff
    (a : InfiniteIdeleGroup K) :
    a ∈ narrowInfiniteCongruenceSubgroup (K := K) ↔
      ∀ v, ContinuousMulEquiv.piUnits a v ∈
        infinitePositiveSubgroup v := by
  change ContinuousMulEquiv.piUnits a ∈
      Subgroup.pi Set.univ (fun v => infinitePositiveSubgroup v) ↔ _
  rw [Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies]

end RayClass
