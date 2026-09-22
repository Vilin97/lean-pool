/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidt

/-! # Hilbert Schmidt Finite Rank -/

open TauCeti.DavisKahan.Sylvester

/-!
# Finite-rank estimates for the paper square norm

Davis and Kahan write the bound norm with a subscript one.  Their fallback
following Theorem 6.2 is therefore an operator-norm estimate, not a trace-norm
estimate.  This module records the two exact comparisons needed to derive it:

* operator norm is bounded by the square norm;
* a rank-at-most-`r` operator has square norm at most
  `sqrt r * operatorNorm`.

Both statements follow directly from the approximation singular-value
sequence, so they apply to rectangular real and complex operators without a
basis choice.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal

noncomputable section

universe u v vF

/-- Approximation singular values vanish once the admissible approximation
rank reaches the rank of the operator itself. -/
theorem approximationSingularValue_eq_zero_of_rank_le
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] 
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] 
    {A : E →L[𝕜] F} {n : ℕ}
    (hA : A.rank ≤ (n : Cardinal)) :
    approximationSingularValue n A = 0 := by
  have h : A.approximationNumber n ≤ ‖A - A‖ :=
    A.approximationNumber_le_norm_sub (R := A) hA
  rw [sub_self, norm_zero] at h
  exact le_antisymm h (A.approximationNumber_nonneg n)

/-- If `A` has rank at most `r`, every term after the first `r` terms of its
approximation singular-value sequence vanishes. -/
theorem approximationSingularValue_eq_zero_of_rank_le_nat
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] F} {r n : ℕ}
    (hA : A.rank ≤ (r : Cardinal)) (hrn : r ≤ n) :
    approximationSingularValue n A = 0 := by
  apply approximationSingularValue_eq_zero_of_rank_le
  exact hA.trans (by exact_mod_cast hrn)

/-- The extended square energy of a rank-at-most-`r` operator is a finite sum. -/
theorem approximationNumberEnergy_eq_sum_range_of_rank_le
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] F} {r : ℕ}
    (hA : A.rank ≤ (r : Cardinal)) :
    approximationNumberEnergy A =
      ∑ n ∈ Finset.range r,
        ENNReal.ofReal ((approximationSingularValue n A) ^ 2) := by
  unfold approximationNumberEnergy
  rw [tsum_eq_sum (s := Finset.range r)]
  intro n hn
  have hrn : r ≤ n := Nat.le_of_not_gt (by simpa using hn)
  rw [approximationSingularValue_eq_zero_of_rank_le_nat hA hrn]
  simp

/-- A finite-rank operator belongs to the canonical square ideal. -/
theorem approximationNumberEnergy_ne_top_of_rank_le
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] F} {r : ℕ}
    (hA : A.rank ≤ (r : Cardinal)) :
    approximationNumberEnergy A ≠ ⊤ := by
  rw [approximationNumberEnergy_eq_sum_range_of_rank_le hA]
  exact ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top

/-- Finite-rank square energy is bounded by rank times squared operator norm. -/
theorem approximationNumberEnergy_le_rank_mul_opNorm_sq
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] F} {r : ℕ}
    (hA : A.rank ≤ (r : Cardinal)) :
    approximationNumberEnergy A ≤
      (r : ENNReal) * ENNReal.ofReal (‖A‖ ^ 2) := by
  rw [approximationNumberEnergy_eq_sum_range_of_rank_le hA]
  calc
    (∑ n ∈ Finset.range r,
        ENNReal.ofReal ((approximationSingularValue n A) ^ 2))
        ≤ ∑ _n ∈ Finset.range r, ENNReal.ofReal (‖A‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀
          (approximationSingularValue_nonneg n A)
          (approximationSingularValue_le_opNorm n A) 2)
    _ = (r : ENNReal) * ENNReal.ofReal (‖A‖ ^ 2) := by
      simp [Finset.card_range, nsmul_eq_mul]

end

end ExactSinTheta
end DavisKahan
end TauCeti
