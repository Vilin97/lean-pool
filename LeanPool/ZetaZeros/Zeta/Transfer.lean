/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import LeanPool.ZetaZeros.Zeta.Kernel

/-!
# Transfer of the Hilbert-space inequalities to zeta zeros

Conjugation invariance of the rescaled zero multiset, the identification of its finite kernel sum
with the canonical sum over zeros, and the transfer of the two abstract finite-set inequalities to
the three zero-counting functions.
-/

@[expose] public section

namespace ZetaZeros


/-- **The finite-set lower bound transferred to simple zeros on the critical line.** -/
@[zz_tag "lem_N_simple_lower"]
theorem simpleOnLineCount_lower {lam T : ℝ} {eta : ℝ → ℝ}
    (hT : 1 < T) (hη : IsAdmissible lam eta) :
    2 * (zeroCount T : ℝ) - (unweightedKernelSum eta T).re
      ≤ (simpleOnLineCount T : ℝ) := by
  have hbound := card_simpleRealPart_lower hη (isConjInvariant_rescaledZerosFinset hT)
  have hsum :
      ∑ z ∈ rescaledZerosFinset T, (rescaledMult T z : ℝ) = (zeroCount T : ℝ) := by
    exact_mod_cast sum_rescaledMult_eq_zeroCount hT
  have hkernel := congrArg Complex.re
    (sum_testKernel_sq_eq_finsum_rescaledDiff hT eta)
  change _ = (unweightedKernelSum eta T).re at hkernel
  simp only [Nat.cast_mul] at hkernel
  have hcard :
      ((simpleRealPart (rescaledZerosFinset T) (rescaledMult T)).card : ℝ) =
        (simpleOnLineCount T : ℝ) := by
    exact_mod_cast card_simpleRealPart_rescaled_eq_simpleOnLineCount hT
  rwa [hsum, hkernel, hcard] at hbound

/-- **The finite-set lower bound transferred to distinct zeros.** -/
@[zz_tag "lem_N_distinct_lower"]
theorem distinctZeroCount_lower {lam T : ℝ} {eta : ℝ → ℝ}
    (hT : 1 < T) (hη : IsAdmissible lam eta) :
    3 / 2 * (zeroCount T : ℝ) - (unweightedKernelSum eta T).re / 2
      ≤ (distinctZeroCount T : ℝ) := by
  have hbound := card_lower hη (isConjInvariant_rescaledZerosFinset hT)
  have hsum :
      ∑ z ∈ rescaledZerosFinset T, (rescaledMult T z : ℝ) = (zeroCount T : ℝ) := by
    exact_mod_cast sum_rescaledMult_eq_zeroCount hT
  have hkernel := congrArg Complex.re
    (sum_testKernel_sq_eq_finsum_rescaledDiff hT eta)
  change _ = (unweightedKernelSum eta T).re at hkernel
  simp only [Nat.cast_mul] at hkernel
  have hcard : ((rescaledZerosFinset T).card : ℝ) = (distinctZeroCount T : ℝ) := by
    exact_mod_cast card_rescaledZerosFinset_eq_distinctZeroCount hT
  rw [hsum, hkernel, hcard] at hbound
  calc
    3 / 2 * (zeroCount T : ℝ) - (unweightedKernelSum eta T).re / 2 =
        (3 / 2 : ℝ) * (zeroCount T : ℝ) -
          (1 / 2 : ℝ) * (unweightedKernelSum eta T).re := by ring
    _ ≤ (distinctZeroCount T : ℝ) := hbound

end ZetaZeros
