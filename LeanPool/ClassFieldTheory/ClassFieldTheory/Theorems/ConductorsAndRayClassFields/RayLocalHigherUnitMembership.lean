/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
/-!
# Congruence description of local higher units

An element of the `n`-th higher-unit group is an integral unit congruent to
`1` modulo the `n`-th power of the maximal ideal. This also applies at `n = 0`,
where the condition reduces to being an integral unit.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

open NumberField IsDedekindDomain

/-- Membership in the `n`-th local higher-unit group is precisely the
congruence `y ≡ 1 (mod 𝔪_v^n)` for an integral-unit representative. -/
theorem mem_rayLocalHigherUnitGroup_iff
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ rayLocalHigherUnitGroup v n ↔
      ∃ y : (v.adicCompletionIntegers K)ˣ,
        ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm y :
          (v.adicCompletion K)ˣ) = x ∧
        (y : v.adicCompletionIntegers K) - 1 ∈
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n := by
  change x ∈ RayClass.localHigherUnitGroup v n ↔ _
  rw [RayClass.mem_localHigherUnitGroup_iff]
  constructor
  · rintro ⟨y, hxy, hmap⟩
    let z : (v.adicCompletionIntegers K)ˣ :=
      (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y
    refine ⟨z, ?_, ?_⟩
    · have hback :
          (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm z = y := by
        exact Equiv.symm_apply_apply _ _
      rw [hback]
      exact hxy
    · have hq : Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
          (z : v.adicCompletionIntegers K) = 1 := by
        have hv := congrArg Units.val hmap
        change Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
          (z : v.adicCompletionIntegers K) = 1 at hv
        exact hv
      exact (Ideal.Quotient.mk_eq_one_iff_sub_mem
        (I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
        (z : v.adicCompletionIntegers K)).mp hq
  · rintro ⟨z, hz, hcong⟩
    let y : (v.adicCompletionIntegers K).units :=
      (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm z
    refine ⟨y, hz, ?_⟩
    apply Units.ext
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
      (z : v.adicCompletionIntegers K) = 1
    exact (Ideal.Quotient.mk_eq_one_iff_sub_mem
      (I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
      (z : v.adicCompletionIntegers K)).mpr hcong

end ClassFieldTheory
