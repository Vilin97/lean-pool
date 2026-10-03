/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtBasis

/-!
# The Hilbert--Schmidt norm, read from the approximation-number sequence

The paper computes the Hilbert--Schmidt norm as `√(Σ aₙ²)`; the canonical ideal
computes it from an orthonormal expansion.  `hilbertSchmidtNorm_eq_sqrt_approximationNumberEnergy`
says they are the same number, unconditionally, so there is one norm and this
module states the paper's estimates *about that norm* rather than about a second
one that happens to equal it.

Everything here therefore needs the coordinate bridge and lives downstream of it.
The facts that need no bridge -- nonnegativity, vanishing at zero, negation,
homogeneity, adjoint invariance, the triangle inequality and the two-sided ideal
bound -- are the canonical `ContinuousLinearMap.hilbertSchmidtNorm_*` lemmas and
are not restated.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal

noncomputable section

universe u vE vF vG vH vE1 vF1 vE2 vF2

/-- **Complete singular-value equality preserves the Hilbert--Schmidt norm.**
Two operators with the same approximation-number sequence have the same norm even
when they act between different spaces, which is what lets a paper estimate be
transported along a unitary rearrangement. -/
theorem SameApproximationSingularSequence.hilbertSchmidtNorm_eq
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ : Type vE1} {F₁ : Type vF1}
    {E₂ : Type vE2} {F₂ : Type vF2}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) :
    A.hilbertSchmidtNorm = B.hilbertSchmidtNorm := by
  rw [hilbertSchmidtNorm_eq_sqrt_approximationNumberEnergy,
    hilbertSchmidtNorm_eq_sqrt_approximationNumberEnergy, h.approximationNumberEnergy_eq]

/-- The modulus has the same Hilbert--Schmidt norm as the operator. -/
theorem hilbertSchmidtNorm_operatorModulus
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) :
    (ContinuousLinearMap.modulus A).hilbertSchmidtNorm = A.hilbertSchmidtNorm :=
  SameApproximationSingularSequence.hilbertSchmidtNorm_eq
    (modulus_hasSameApproximationNumbers A)

/-- Real complexification preserves the Hilbert--Schmidt norm. -/
theorem hilbertSchmidtNorm_complexify
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) :
    (RealComplexification.complexify A).hilbertSchmidtNorm = A.hilbertSchmidtNorm := by
  rw [hilbertSchmidtNorm_eq_sqrt_approximationNumberEnergy,
    hilbertSchmidtNorm_eq_sqrt_approximationNumberEnergy,
    approximationNumberEnergy_complexify]

/-- **The squared norm is the approximation-number energy.**  The finiteness
hypothesis is what makes the right-hand side a real number rather than `0`. -/
theorem sq_hilbertSchmidtNorm
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] F} (_hA : approximationNumberEnergy A ≠ ⊤) :
    A.hilbertSchmidtNorm ^ 2 = (approximationNumberEnergy A).toReal := by
  rw [hilbertSchmidtNorm_eq_sqrt_approximationNumberEnergy, Real.sq_sqrt]
  exact ENNReal.toReal_nonneg

/-- **The Hilbert--Schmidt norm dominates the operator norm**, because the
operator norm is the first term of the square-summable singular sequence. -/
theorem opNorm_le_hilbertSchmidtNorm
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] F} (hA : approximationNumberEnergy A ≠ ⊤) :
    ‖A‖ ≤ A.hilbertSchmidtNorm := by
  have hterm : ENNReal.ofReal (‖A‖ ^ 2) ≤ approximationNumberEnergy A := by
    unfold approximationNumberEnergy
    simpa only [approximationSingularValue_zero] using (ENNReal.le_tsum (f := fun n : ℕ =>
      ENNReal.ofReal ((approximationSingularValue n A) ^ 2)) 0)
  have hreal : ‖A‖ ^ 2 ≤ (approximationNumberEnergy A).toReal := by
    have := ENNReal.toReal_mono hA hterm
    simpa [ENNReal.toReal_ofReal (sq_nonneg ‖A‖)] using this
  rw [← sq_hilbertSchmidtNorm hA] at hreal
  nlinarith [norm_nonneg A, ContinuousLinearMap.hilbertSchmidtNorm_nonneg A]

/-- A rank-`r` operator has Hilbert--Schmidt norm at most `√r` times its
operator norm. -/
theorem hilbertSchmidtNorm_le_sqrt_rank_mul_opNorm
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] F} {r : ℕ}
    (hA : A.rank ≤ (r : Cardinal)) :
    A.hilbertSchmidtNorm ≤ Real.sqrt r * ‖A‖ := by
  have hmem := approximationNumberEnergy_ne_top_of_rank_le hA
  have henergy := approximationNumberEnergy_le_rank_mul_opNorm_sq hA
  have hreal : (approximationNumberEnergy A).toReal ≤ (r : ℝ) * ‖A‖ ^ 2 := by
    have := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top r) ENNReal.ofReal_ne_top) henergy
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg ‖A‖)] using this
  have hsq : A.hilbertSchmidtNorm ^ 2 ≤ (Real.sqrt r * ‖A‖) ^ 2 := by
    rw [sq_hilbertSchmidtNorm hmem, mul_pow, Real.sq_sqrt (Nat.cast_nonneg r)]
    simpa [pow_two] using hreal
  have hb : (0 : ℝ) ≤ Real.sqrt r * ‖A‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg A)
  exact (pow_le_pow_iff_left₀ (ContinuousLinearMap.hilbertSchmidtNorm_nonneg A) hb
    (by norm_num)).1 hsq

end

end ExactSinTheta
end DavisKahan
end TauCeti
