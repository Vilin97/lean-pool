/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Sylvester.HilbertSchmidtPairwise

/-! # Hilbert Schmidt Estimate -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Source-facing square-norm Sylvester theorem

This module restores the public declarations originally planned for the
Davis--Kahan square-norm Sylvester estimate.  The completed proof route is the
defect-first Hilbert-tensor argument in `HilbertSchmidtDefectFirst` and
`HilbertSchmidtPairwise`; it does not require a separate joint-PVM Plancherel
construction for rectangular operators.

The extended-energy statement is recovered from the norm theorem.  When the
defect energy is infinite the inequality is immediate.  When it is finite,
the direct pairwise-gap theorem proves Hilbert--Schmidt membership of the
solution and the sharp norm estimate; squaring and converting between finite
`ENNReal` energies gives the claimed inequality.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace ENNReal


noncomputable section

universe v

/-- Pairwise spectral distance gives the squared Hilbert--Schmidt energy
inequality, including the case of infinite defect energy. -/
theorem hilbertSchmidtEnergy_sylvester_le_of_pairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    {X C : F →L[ℂ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C) :
    ENNReal.ofReal (δ ^ 2) * approximationNumberEnergy X ≤
      approximationNumberEnergy C := by
  by_cases hC : approximationNumberEnergy C ≠ ⊤
  · have hmain :=
      hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
        hA hB hδ hgap hEq hC
    have hsq :
        (δ * ContinuousLinearMap.hilbertSchmidtNorm X) ^ 2 ≤
          ContinuousLinearMap.hilbertSchmidtNorm C ^ 2 :=
      (sq_le_sq₀
        (mul_nonneg hδ.le (ContinuousLinearMap.hilbertSchmidtNorm_nonneg X))
        (ContinuousLinearMap.hilbertSchmidtNorm_nonneg C)).2 hmain.2
    have hreal :
        (ENNReal.ofReal (δ ^ 2) * approximationNumberEnergy X).toReal ≤
          (approximationNumberEnergy C).toReal := by
      rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (sq_nonneg δ),
        ← sq_hilbertSchmidtNorm hmain.1,
        ← sq_hilbertSchmidtNorm hC]
      simpa [mul_pow] using hsq
    exact (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmain.1) hC).mp hreal
  · have htop : approximationNumberEnergy C = ⊤ := by
      by_contra hne
      exact hC hne
    rw [htop]
    exact le_top

/-- **Davis--Kahan inequality (5.1), closed-operator square-norm form.** -/
theorem hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    {X C : F →L[ℂ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : approximationNumberEnergy C ≠ ⊤) :
    approximationNumberEnergy X ≠ ⊤ ∧
      δ * ContinuousLinearMap.hilbertSchmidtNorm X ≤ ContinuousLinearMap.hilbertSchmidtNorm C :=
  hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
    hA hB hδ hgap hEq hC

/-- Real closed-operator form, obtained by exact complexification. -/
theorem hilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    {X C : F →L[ℝ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ lam ∈ TauCeti.LinearPMap.realSpectrum A, ∀ α ∈ TauCeti.LinearPMap.realSpectrum B,
      δ ≤ |lam - α|)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : approximationNumberEnergy C ≠ ⊤) :
    approximationNumberEnergy X ≠ ⊤ ∧
      δ * ContinuousLinearMap.hilbertSchmidtNorm X ≤ ContinuousLinearMap.hilbertSchmidtNorm C :=
  hilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap_direct
    hA hB hδ hgap hEq hC

end

end ExactSinTheta
end DavisKahan
end TauCeti
