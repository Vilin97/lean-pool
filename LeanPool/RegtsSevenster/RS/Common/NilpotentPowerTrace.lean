/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# A last nonzero power trace

If a linear functional is nonzero on a nilpotent element, some
positive power has nonzero value and every higher power of that
element has value zero. This is the reduction in Schrijver's
factorial-rank proof of nilpotent-trace vanishing
(arXiv:1211.3561, Proposition 4).
-/

@[expose] public section

namespace RS

/-- A nonzero trace whose powers of degree at least two have zero
trace. No normalization of the nonzero value is required. -/
structure SinglePowerTrace {A : Type*} [Ring A] [Algebra ℂ A]
    (τ : A →ₗ[ℂ] ℂ) (y : A) : Prop where
  /-- The first power has nonzero trace. -/
  trace_ne_zero : τ y ≠ 0
  /-- All higher powers have zero trace. -/
  higher_eq_zero : ∀ m : ℕ, 2 ≤ m → τ (y ^ m) = 0

/-- A nilpotent element with nonzero trace has a positive power
whose first trace is nonzero and whose higher power traces vanish. -/
theorem exists_singlePowerTrace_pow {A : Type*} [Ring A] [Algebra ℂ A]
    (τ : A →ₗ[ℂ] ℂ) {g : A} (hg : IsNilpotent g) (hτ : τ g ≠ 0) :
    ∃ r : ℕ, 1 ≤ r ∧ SinglePowerTrace τ (g ^ r) := by
  classical
  obtain ⟨N, hN⟩ := hg
  have hzero : ∀ m, N ≤ m → τ (g ^ m) = 0 := by
    intro m hm
    have hpow : g ^ m = 0 := by
      rw [show m = N + (m - N) from (Nat.add_sub_of_le hm).symm,
        pow_add, hN, zero_mul]
    rw [hpow, map_zero]
  let s := (Finset.range N).filter (fun m => τ (g ^ m) ≠ 0)
  have hmem : 1 ∈ s := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · by_contra h
      exact hτ (by simpa using hzero 1 (by omega))
    · simpa using hτ
  have hs : s.Nonempty := ⟨1, hmem⟩
  let r := s.max' hs
  have hrmem : r ∈ s := Finset.max'_mem s hs
  have hr : 1 ≤ r := Finset.le_max' s 1 hmem
  refine ⟨r, hr, ⟨(Finset.mem_filter.mp hrmem).2, ?_⟩⟩
  intro m hm
  rw [← pow_mul]
  by_cases hlarge : N ≤ r * m
  · exact hzero _ hlarge
  · by_contra hnonzero
    have hprod : r * m ∈ s :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnonzero⟩
    have hle : r * m ≤ r := Finset.le_max' s _ hprod
    nlinarith

end RS
