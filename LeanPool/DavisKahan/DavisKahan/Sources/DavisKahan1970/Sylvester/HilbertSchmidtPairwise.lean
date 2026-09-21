/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.Released under Apache 2.0 license as described in the file LICENSE.Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtApproximationNorm
import LeanPool.DavisKahan.DavisKahan.Sylvester.PairwiseSpectrumGap
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.Complexification
import LeanPool.DavisKahan.DavisKahan.Sylvester.PairwiseHomogeneousUniqueness
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Sylvester.HilbertSchmidtDefectFirst
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralGap

/-! # Hilbert Schmidt Pairwise -/

open TauCeti.DavisKahan.Sylvester

/-!
# Pairwise-gap square-norm Sylvester theorem

This file discharges the two hypotheses left by the defect-first reduction.Positive pairwise separation of the original self-adjoint spectra:

* gives bounded homogeneous uniqueness through rectangular spectral
  intertwining; and
* gives a global spectral gap for the left-minus-right Hilbert--Schmidt tensor
  flow through the pure-tensor product-measure formula.The resulting theorem has the exact hypothesis and constant of the
square-norm Sylvester estimate used in Davis--Kahan Theorem 6.2.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open TauCeti.RealComplexification
-- The complexification of a bounded operator sits under the foundation namespace.

noncomputable section

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The defect has the vector spectral gap dictated by the pairwise separation
of the original spectra.  In fact the Sylvester flow has this gap at every
vector.

The pairwise gap is stated over `ℂ`; on real spectral points the complex norm is
the real absolute value, which is the only conversion this needs. -/
theorem hilbertSchmidtTensor_hasVectorSpectralGap
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {C : F →L[ℂ] E} {δ : ℝ}
    (hgap : PairwiseSpectrumGap A B δ)
    (hC : approximationNumberEnergy C ≠ ⊤) :
    TauCeti.LinearPMap.HasVectorSpectralGap
      (TauCeti.HilbertSchmidt.isSelfAdjoint_generator_sylvesterGroup
        (TauCeti.LinearPMap.genToGroup hA) (TauCeti.LinearPMap.genToGroup hB) (hSBasis F))
      δ (hilbertSchmidtTensor C hC) := by
  refine TauCeti.HilbertSchmidt.hasVectorSpectralGap_sylvesterGroup hA hB (hSBasis F)
    ?_ (hilbertSchmidtTensor C hC)
  intro lam hlam alp halp
  have h := hgap (lam : ℂ) hlam (alp : ℂ) halp
  rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h

/-- **Davis--Kahan square-norm Sylvester estimate at arbitrary pairwise
spectral separation.**  This is the direct, non-circular completion of the
analytic engine required by Theorem 6.2. -/
theorem hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    {X C : F →L[ℂ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : approximationNumberEnergy C ≠ ⊤) :
    approximationNumberEnergy X ≠ ⊤ ∧
      δ * ContinuousLinearMap.hilbertSchmidtNorm X ≤ ContinuousLinearMap.hilbertSchmidtNorm C := by
  apply hilbertSchmidt_sylvester_defectFirst
    hA hB hδ hEq
  · intro Y hY
    exact closedSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
      hA hB hδ hgap hY
  -- Supplying the gap instantiates the tensor's own membership argument, so
  -- there is no further obligation.
  · exact hilbertSchmidtTensor_hasVectorSpectralGap hA hB hgap hC


/-- Real closed-operator form of the direct pairwise-gap theorem, obtained by
exact complexification. -/
theorem hilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap_direct
    {ER FR : Type v}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [CompleteSpace ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [CompleteSpace FR]
    {A : ER →ₗ.[ℝ] ER}
    {B : FR →ₗ.[ℝ] FR}
    {X C : FR →L[ℝ] ER}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ lam ∈ TauCeti.LinearPMap.realSpectrum A, ∀ α ∈ TauCeti.LinearPMap.realSpectrum B,
      δ ≤ |lam - α|)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : approximationNumberEnergy C ≠ ⊤) :
    approximationNumberEnergy X ≠ ⊤ ∧
      δ * ContinuousLinearMap.hilbertSchmidtNorm X ≤ ContinuousLinearMap.hilbertSchmidtNorm C := by
  have hgapC : PairwiseSpectrumGap
      (PartialMapComplexification.complexify A)
      (PartialMapComplexification.complexify B) δ := by
    intro lam hlam α hα
    -- The canonical spectrum lives in `ℂ`; `hgap` constrains only real points, so
    -- first use self-adjointness to see that there are no others.
    obtain ⟨lr, -, rfl⟩ :=
      spectrum_subset_real_of_isSelfAdjoint
        (PartialMapComplexification.isSelfAdjoint_complexify hA) hlam
    obtain ⟨ar, -, rfl⟩ :=
      spectrum_subset_real_of_isSelfAdjoint
        (PartialMapComplexification.isSelfAdjoint_complexify hB) hα
    have h := hgap lr (by
        rwa [PartialMapComplexification.realSpectrum_complexify A,
          Set.mem_preimage]) ar (by
        rwa [PartialMapComplexification.realSpectrum_complexify B,
          Set.mem_preimage])
    rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hCcomplex : approximationNumberEnergy
      (RealComplexification.complexify C) ≠ ⊤ :=
    (approximationNumberEnergy_ne_top_complexify_iff C).2 hC
  have hmain := hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
    (PartialMapComplexification.isSelfAdjoint_complexify hA)
    (PartialMapComplexification.isSelfAdjoint_complexify hB)
    hδ hgapC
    (PartialMapComplexification.closedSylvesterEquation_complexify hEq)
    hCcomplex
  constructor
  · exact (approximationNumberEnergy_ne_top_complexify_iff X).1 hmain.1
  · simpa [hilbertSchmidtNorm_complexify] using hmain.2

end

end ExactSinTheta
end DavisKahan
end TauCeti
