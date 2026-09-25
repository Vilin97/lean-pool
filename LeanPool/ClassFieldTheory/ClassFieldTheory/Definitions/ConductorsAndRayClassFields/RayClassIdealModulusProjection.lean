/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsRayCongruent
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import Mathlib.Data.Finsupp.Order
public import Mathlib.GroupTheory.QuotientGroup.Basic
/-!
# Projection between ideal-theoretic ray class groups

Enlarging a modulus strengthens its finite congruences and real positivity
conditions. The induced inclusions of prime-to-modulus ideals and ray-principal
ideals give the canonical quotient map from the larger modulus to the smaller.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

universe u

open scoped Classical in
private def rayLocalIntegralValue
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (y : (v.adicCompletionIntegers K).units) :
    v.adicCompletionIntegers K :=
  ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y :
    (v.adicCompletionIntegers K)ˣ).1

open scoped Classical in
private theorem rayLocalHigherUnitMap_eq_one_iff
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (y : (v.adicCompletionIntegers K).units) :
    rayLocalHigherUnitMap v n y = 1 ↔
      rayLocalIntegralValue v y - 1 ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n := by
  let I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n
  change Units.map (Ideal.Quotient.mk I).toMonoidHom
      ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y) =
        1 ↔ _
  rw [Units.ext_iff]
  change Ideal.Quotient.mk I (rayLocalIntegralValue v y) =
      Ideal.Quotient.mk I 1 ↔ _
  exact Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := I) (rayLocalIntegralValue v y)
      (1 : v.adicCompletionIntegers K)

open scoped Classical in
private theorem rayLocalHigherUnitGroup_antitone
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    {m n : ℕ} (hmn : m ≤ n) :
    rayLocalHigherUnitGroup v n ≤ rayLocalHigherUnitGroup v m := by
  intro x hx
  change x ∈ Subgroup.map
    (v.adicCompletionIntegers K).units.subtype
    (rayLocalHigherUnitMap v n).ker at hx
  change x ∈ Subgroup.map
    (v.adicCompletionIntegers K).units.subtype
    (rayLocalHigherUnitMap v m).ker
  rw [Subgroup.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, ?_, rfl⟩
  change rayLocalHigherUnitMap v n y = 1 at hy
  change rayLocalHigherUnitMap v m y = 1
  rw [rayLocalHigherUnitMap_eq_one_iff] at hy ⊢
  exact Ideal.pow_le_pow_right hmn hy

open scoped Classical in
private theorem rayCongruent_of_le
    {K : Type u} [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n)
    {x : Kˣ} (hx : IsRayCongruent n x) :
    IsRayCongruent m x := by
  constructor
  · intro v hv
    have hvn : v ∈ n.finitePart.support := by
      apply Finsupp.mem_support_iff.mpr
      have hpos : 0 < m.finitePart v :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
      exact Nat.ne_of_gt (lt_of_lt_of_le hpos (hmn.1 v))
    exact rayLocalHigherUnitGroup_antitone v (hmn.1 v) (hx.1 v hvn)
  · intro v hv
    exact hx.2 v (hmn.2 hv)

open scoped Classical in
private theorem rayPrimeToIdeals_antitone
    {K : Type u} [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n) :
    rayClassPrimeToIdeals n ≤ rayClassPrimeToIdeals m := by
  intro I hI v hv
  exact hI v (Finsupp.support_mono hmn.1 hv)

open scoped Classical in
private theorem rayPrincipalIdeals_antitone
    {K : Type u} [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n) :
    rayPrincipalIdealSubgroup n ≤ rayPrincipalIdealSubgroup m := by
  apply Subgroup.closure_mono
  rintro I ⟨x, hx, hIx⟩
  exact ⟨x, rayCongruent_of_le hmn hx, hIx⟩

open scoped Classical in
/-- The ideal-theoretic ray class group modulo a larger modulus projects to
the ray class group modulo a smaller modulus. -/
def rayClassIdealModulusProjection
    (K : Type u) [Field K] [NumberField K]
    {m n : RayClassModulus K} (hmn : m ≤ n) :
    RayClassGroup n →* RayClassGroup m := by
  let hI : rayClassPrimeToIdeals n ≤ rayClassPrimeToIdeals m :=
    by exact rayPrimeToIdeals_antitone hmn
  letI : (rayPrincipalIdealSubgroupInPrimeTo m).Normal :=
    Subgroup.normal_of_isMulCommutative _
  refine QuotientGroup.map
    (rayPrincipalIdealSubgroupInPrimeTo n)
    (rayPrincipalIdealSubgroupInPrimeTo m)
    (Subgroup.inclusion hI) ?_
  intro I hI'
  change (I : NumberFieldFractionalIdealGroup K) ∈
    rayPrincipalIdealSubgroup n at hI'
  change (I : NumberFieldFractionalIdealGroup K) ∈
    rayPrincipalIdealSubgroup m
  exact (by exact rayPrincipalIdeals_antitone hmn hI')

end ClassFieldTheory
