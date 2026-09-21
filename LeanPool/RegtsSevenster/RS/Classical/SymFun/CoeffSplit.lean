/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.PowCount

/-!
# The pointwise convolution form of product coefficients

`MvPolynomial.coeff` of a product, reindexed from the Finsupp
antidiagonal to guarded pointwise splits over a bounded pi-set —
the shape produced by the colour-character convolution.
-/

namespace RS

open Finset MvPolynomial

variable {k : ℕ}

open scoped Classical in
/-- **The guarded pointwise convolution.** -/
theorem coeff_mul_split (P Q : MvPolynomial (Fin k) ℂ)
    (α : Fin k → ℕ) (n : ℕ) (hn : ∀ a, α a ≤ n) :
    (P * Q).coeff (∑ a, Finsupp.single a (α a)) =
    ∑ w ∈ Fintype.piFinset
        (fun _ : Fin k => Finset.range (n + 1)),
      (if ∀ a, w a ≤ α a
        then P.coeff (∑ a, Finsupp.single a (α a - w a)) *
          Q.coeff (∑ a, Finsupp.single a (w a))
        else 0) := by
  classical
  rw [MvPolynomial.coeff_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij'
    (fun p => fun a => p.2 a)
    (fun w => (∑ a, Finsupp.single a (α a - w a),
      ∑ a, Finsupp.single a (w a)))
    ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    have hpt : ∀ a, p.1 a + p.2 a = α a := by
      intro a
      have h1 := congrArg (fun f : Fin k →₀ ℕ => f a) hp
      rw [Finsupp.add_apply, sum_single_apply] at h1
      exact h1
    rw [Finset.mem_filter]
    constructor
    · rw [Fintype.mem_piFinset]
      intro a
      rw [Finset.mem_range]
      have := hpt a
      have := hn a
      omega
    · intro a
      show p.2 a ≤ α a
      have := hpt a
      omega
  · -- backward membership
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_antidiagonal]
    ext a
    rw [show ((∑ b, Finsupp.single b (α b - w b)) +
        ∑ b, Finsupp.single b (w b)) a =
      (∑ b, Finsupp.single b (α b - w b)) a +
        (∑ b, Finsupp.single b (w b)) a from rfl]
    rw [sum_single_apply, sum_single_apply, sum_single_apply]
    have := hw.2 a
    omega
  · -- left inverse
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    have hpt : ∀ a, p.1 a + p.2 a = α a := by
      intro a
      have h1 := congrArg (fun f : Fin k →₀ ℕ => f a) hp
      rw [Finsupp.add_apply, sum_single_apply] at h1
      exact h1
    refine Prod.ext ?_ ?_
    · show (∑ a, Finsupp.single a (α a - p.2 a)) = p.1
      ext a
      rw [sum_single_apply]
      have := hpt a
      omega
    · show (∑ a, Finsupp.single a (p.2 a)) = p.2
      ext a
      rw [sum_single_apply]
  · -- right inverse
    intro w hw
    funext a
    show (∑ b, Finsupp.single b (w b)) a = w a
    rw [sum_single_apply]
  · -- value transfer
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    have hpt : ∀ a, p.1 a + p.2 a = α a := by
      intro a
      have h1 := congrArg (fun f : Fin k →₀ ℕ => f a) hp
      rw [Finsupp.add_apply, sum_single_apply] at h1
      exact h1
    congr 1
    · congr 1
      ext a
      rw [sum_single_apply]
      show p.1 a = α a - p.2 a
      have := hpt a
      omega
    · congr 1
      ext a
      rw [sum_single_apply]

end RS
