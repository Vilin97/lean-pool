/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayLocalHigherUnitMembership
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.Ring
/-!
# Positive-depth higher units as `1 + 𝔪ᵛⁿ`

At positive depth, every element of `1 + 𝔪ᵛⁿ` is automatically a unit in
the local integer ring. Consequently no integral-unit witness is needed in
the membership criterion below.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

/-- For `n ≥ 1`, a local field unit belongs to the `n`-th higher-unit
group exactly when its value is `1 + t` for some `t` in the `n`-th power of
the maximal ideal of the local integer ring. -/
theorem mem_rayLocalHigherUnitGroup_iff_exists_one_add
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 1 ≤ n)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ rayLocalHigherUnitGroup v n ↔
      ∃ t : v.adicCompletionIntegers K,
        t ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n ∧
          (x : v.adicCompletion K) =
            ((1 + t : v.adicCompletionIntegers K) : v.adicCompletion K) := by
  constructor
  · intro hx
    obtain ⟨y, hxy, hcong⟩ :=
      (mem_rayLocalHigherUnitGroup_iff v n x).mp hx
    refine ⟨(y : v.adicCompletionIntegers K) - 1, hcong, ?_⟩
    have hval := congrArg Units.val hxy
    change ((y : v.adicCompletionIntegers K) : v.adicCompletion K) =
      (x : v.adicCompletion K) at hval
    calc
      (x : v.adicCompletion K) =
          ((y : v.adicCompletionIntegers K) : v.adicCompletion K) := hval.symm
      _ = ((1 + ((y : v.adicCompletionIntegers K) - 1) :
            v.adicCompletionIntegers K) : v.adicCompletion K) := by
        congr 1
        ring
  · rintro ⟨t, ht, hx⟩
    have htmax : t ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
      (Ideal.pow_le_self (Nat.ne_of_gt hn)) ht
    have hnon : -t ∈ nonunits (v.adicCompletionIntegers K) :=
      (IsLocalRing.mem_maximalIdeal (-t)).mp
        ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).neg_mem htmax)
    have hunit : IsUnit (1 + t : v.adicCompletionIntegers K) := by
      simpa only [sub_neg_eq_add] using
        (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-t) hnon)
    obtain ⟨y, hy⟩ := hunit
    apply (mem_rayLocalHigherUnitGroup_iff v n x).mpr
    refine ⟨y, ?_, ?_⟩
    · apply Units.ext
      change ((y : v.adicCompletionIntegers K) : v.adicCompletion K) =
        (x : v.adicCompletion K)
      calc
        ((y : v.adicCompletionIntegers K) : v.adicCompletion K) =
            ((1 + t : v.adicCompletionIntegers K) : v.adicCompletion K) :=
          congrArg
            (fun z : v.adicCompletionIntegers K =>
              (z : v.adicCompletion K)) hy
        _ = (x : v.adicCompletion K) := hx.symm
    · have hsub : (y : v.adicCompletionIntegers K) - 1 = t := by
        rw [hy]
        ring
      rw [hsub]
      exact ht

end ClassFieldTheory
