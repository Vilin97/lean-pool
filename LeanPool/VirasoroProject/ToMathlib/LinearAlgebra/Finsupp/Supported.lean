/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# LeanPool.VirasoroProject.ToMathlib.LinearAlgebra.Finsupp.Supported
-/

--import Mathlib

lemma finsum_mem_span {ι R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (vs : ι → V) (cfs : ι → R) :
    ∑ᶠ i, cfs i • vs i ∈ Submodule.span R (Set.range vs) := by
  by_cases h : {i | cfs i • vs i ≠ 0}.Finite
  · let s : Finset ι := h.toFinset
    rw [finsum_eq_finsetSum_of_support_subset (s := s) _ (fun i hi ↦ by simpa [s] using hi)]
    apply Submodule.sum_smul_mem
    exact fun i his ↦ Submodule.mem_span_of_mem (Set.mem_range_self i)
  · suffices junk : ∑ᶠ i, cfs i • vs i = 0 by simp [junk]
    simpa [Function.support] using finsum_mem_eq_zero_of_infinite (s := Set.univ)
      (by simpa [Function.support] using h)

lemma finsum_mem_mem_span {ι R V : Type*}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (vs : ι → V) (cfs : ι → R) (s : Set ι) :
    ∑ᶠ i ∈ s, cfs i • vs i ∈ Submodule.span R (vs '' s) := by
  by_cases h : {i | cfs i • vs i ≠ 0 ∧ i ∈ s}.Finite
  · let t : Finset ι := h.toFinset
    rw [finsum_eq_finsetSum_of_support_subset (s := t) _ ?_]
    · classical
      apply Submodule.sum_mem
      intro i _
      by_cases his : i ∈ s
      · simpa [his] using Submodule.smul_mem (Submodule.span R (vs '' s)) (cfs i)
          (Submodule.mem_span_of_mem (Set.mem_image_of_mem vs his))
      · simp [his]
    · intro i hi
      simp only [ne_eq, Set.Finite.coe_toFinset, Set.mem_setOf_eq, t]
      refine ⟨?_, ?_⟩ <;>
      · by_contra con
        simp [con] at hi
  · suffices junk : ∑ᶠ i ∈ s, cfs i • vs i = 0 by simp [junk]
    exact finsum_mem_eq_zero_of_infinite (by simpa [Function.support, Set.inter_comm,
      Set.setOf_and] using h)


--#min_imports
