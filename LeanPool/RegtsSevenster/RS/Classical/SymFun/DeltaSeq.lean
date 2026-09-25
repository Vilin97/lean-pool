/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.ColourCycleSum

/-!
# The delta power-sum sequence

At the sequence `t₀ = (1, 0, 0, …)` the completed cycle weight is
the identity indicator and the complete homogeneous values are
inverse factorials; the Frobenius formula then evaluates the
Jacobi–Trudi character degree as `n!` times the Jacobi–Trudi
determinant at `t₀`.
-/

@[expose] public section

namespace RS

open Finset

/-- The delta power-sum sequence. -/
noncomputable def deltaSeq : ℕ → ℂ :=
  fun c => if c = 1 then 1 else 0

/-- The delta sequence's first value is `1`. -/
@[simp]
theorem deltaSeq_one : deltaSeq 1 = 1 := by
  rw [deltaSeq, ite_eq_left rfl]

/-- Complete homogeneous values of the delta sequence are inverse
factorials. -/
theorem newtonH_deltaSeq (d : ℕ) :
    newtonH deltaSeq d = ((d.factorial : ℂ))⁻¹ := by
  induction d with
  | zero =>
    rw [newtonH_zero, Nat.factorial_zero, Nat.cast_one, inv_one]
  | succ d ih =>
    rw [newtonH]
    rw [Finset.sum_eq_single 0
      (fun i _ hi => by
        rw [show deltaSeq (i + 1) = 0 from by
          rw [deltaSeq, ite_eq_right (by omega)]]
        rw [zero_mul])
      (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
    rw [show deltaSeq (0 + 1) = 1 from by
      rw [deltaSeq]
      norm_num]
    rw [Nat.sub_zero, one_mul, ih]
    rw [Nat.factorial_succ]
    push_cast
    rw [mul_inv]

/-- The completed cycle weight of the delta sequence is the
identity indicator. -/
theorem cycleProd_deltaSeq {n : ℕ} (π : Equiv.Perm (Fin n)) :
    cycleProd deltaSeq π = if π = 1 then 1 else 0 := by
  rw [cycleProd, deltaSeq_one, one_pow, mul_one]
  by_cases hπ : π = 1
  · rw [ite_eq_left hπ, hπ, Equiv.Perm.cycleType_one,
      Multiset.map_zero, Multiset.prod_zero]
  · rw [ite_eq_right hπ]
    have hne : π.cycleType ≠ 0 := by
      intro hc
      exact hπ (Equiv.Perm.cycleType_eq_zero.mp hc)
    obtain ⟨c, hc⟩ := Multiset.exists_mem_of_ne_zero hne
    refine Multiset.prod_eq_zero ?_
    rw [Multiset.mem_map]
    refine ⟨c, hc, ?_⟩
    rw [deltaSeq, ite_eq_right]
    have := Equiv.Perm.two_le_of_mem_cycleType hc
    omega

/-- **The degree evaluation**: the Jacobi–Trudi character degree
is `n!` times the Jacobi–Trudi determinant at the delta
sequence. -/
theorem jtChar_one_eq (μ : YoungDiagram) :
    jtChar μ 1 = (μ.card.factorial : ℂ) * diagramSchur μ deltaSeq := by
  have h := jtChar_frobenius' μ deltaSeq
  rw [Finset.sum_congr rfl (fun π (_ : π ∈ Finset.univ) => by
    rw [cycleProd_deltaSeq π])] at h
  rw [Finset.sum_eq_single 1
    (fun π _ hπ => by rw [ite_eq_right hπ, mul_zero])
    (fun hmem => absurd (Finset.mem_univ _) hmem)] at h
  rw [ite_eq_left rfl, mul_one] at h
  have hfac : ((μ.card.factorial : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero μ.card
  field_simp at h
  rw [h]

end RS
