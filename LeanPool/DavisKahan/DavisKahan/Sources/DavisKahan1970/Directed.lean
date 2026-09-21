/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63InfiniteTrial
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm

/-! # Directed -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 6.3 at the paper's unitarily invariant norms, over `ℂ`

Theorem 6.3 is printed "for every unitarily invariant norm".  The repository's
complex directed endpoints
(`…TanTheta.theorem6_3_infiniteTrial_ideal` and its finite-trial
siblings) are stated at `KyFanDominantIdealFamily (𝕜 := ℂ)`, while the real
endpoint `tanTheta_directed_bounded_symmetricNorming_real` is stated at the paper's own
`SymmetricNormingFunction`.  This module supplies the missing complex half, so
the two scalar fields carry the same norm abstraction.

## Nothing is transported across scalar fields

`SymmetricNormingFunction` is a normalized symmetric norming function: it is
scalar-agnostic *data*, and every one of its laws that Theorem 6.3 needs
(`SymmetricNormingFunction.mul_gauge_le_of_all_mul_kyFan_le`) is `RCLike`-generic
and consumes nothing but the family of Ky Fan approximation-gauge inequalities.
So a complex operator is measured by a paper norm directly, and no ideal family
is compared across fields — the manoeuvre the real transport had to avoid.

`theorem6_3_all_kyFan_core_infiniteTrial` already supplies **every** Ky Fan
prefix, which is exactly what Fan dominance consumes, so the paper-norm endpoint
is the ideal-family endpoint's sibling rather than a weakening of it: both are
consequences of the same Ky Fan core, and
`all_mul_kyFan_le_of_every_symmetricNorming_gauge_le` recovers the whole Ky Fan family
back from the paper norms, so neither abstraction dominates the other.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Theorem 6.3 and the Appendix to
  Section 6.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace BigOperators
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.TanTheta

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Davis--Kahan 1970, Theorem 6.3 at every source unitarily invariant norm,
over a complex Hilbert space and an arbitrary complete trial subspace**, from the
Rayleigh--Ritz form bounds.

The paper's hypotheses: `T` symmetric, `V` reducing, the upper form bound `α` on
the Ritz compression, the one-sided lower form bound `α + δ` off `V`, and
membership of the residual in the chosen source norm.  The conclusion exhibits a
directed tangent representative with the paper's complete singular-value
sequence, concludes its membership, and gives `δ N(tan Θ₀) ≤ N(R)`.

The trial space carries no dimension hypothesis and the printed strict-rank
comparison is not assumed; both are recorded on the ideal-family endpoints as
already-inert, so dropping them strengthens rather than narrows.  This is the
exact complex counterpart of `tanTheta_directed_bounded_symmetricNorming_real`. -/
theorem tanTheta_directed_bounded_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    [CompleteSpace Z]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (hResidual : N.Mem (theorem63Residual T Z)) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
        N.Mem tanTheta0 ∧
        delta * N.gauge tanTheta0 ≤ N.gauge (theorem63Residual T Z) := by
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersInfinite Z V
      (fun n => approximationSingularValue_sineBlock_lt_one_infiniteTrial T V Z hT hV
        hdelta hCompressionUpper hUnwantedLower n)
  have hky : ∀ k : ℕ,
      delta * kyFanApproximationGauge k tanTheta0 ≤
        kyFanApproximationGauge k (theorem63Residual T Z) := by
    intro k
    have hcore := theorem6_3_all_kyFan_core_infiniteTrial T V Z hT hV hdelta
      hCompressionUpper hUnwantedLower k
    have htanKy : kyFanApproximationGauge k tanTheta0 =
        ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlock Z V))) := by
      unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
      refine Finset.sum_congr rfl fun n _ => ?_
      have h := htan n
      unfold approximationSingularValue at h
      exact h
    rw [htanKy]
    exact hcore
  obtain ⟨hmem, hbound⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hdelta hResidual hky
  exact ⟨tanTheta0, htan, hmem, hbound⟩

/-- **Davis--Kahan 1970, Theorem 6.3 at every source unitarily invariant norm,
in the printed spectral orientation.**

The Ritz compression's spectrum lies in `[β, α]`, the spectrum of the restriction
to the unwanted exact subspace lies in `[α + δ, ∞)`, and the conclusion is
`δ N(tan Θ₀) ≤ N(R)` for the paper's norm class, with the tangent representative
exhibited and its membership concluded.

Grounded on `tanTheta_directed_bounded_symmetricNorming_complex`; the spectral placement is converted
to the form bounds by the same two `SpectralOrder` lemmas the ideal-family
endpoint `theorem6_3_infiniteTrial_ideal` uses. -/
theorem tanTheta_directed_bounded_spectralGap_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    [CompleteSpace Z]
    (hV : T.Reduces V)
    {beta alpha delta : ℝ} (_hbetaalpha : beta ≤ alpha) (hdelta : 0 < delta)
    (hCompressionSpectrum :
      spectrum ℝ (theorem63Compression T Z) ⊆ Set.Icc beta alpha)
    (hUnwantedSpectrum :
      spectrum ℝ (T.restrict (hV.orthogonalComplement).1) ⊆
        Set.Ici (alpha + delta))
    (hResidual : N.Mem (theorem63Residual T Z)) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
        N.Mem tanTheta0 ∧
        delta * N.gauge tanTheta0 ≤ N.gauge (theorem63Residual T Z) := by
  have hTsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hMsa : IsSelfAdjoint (theorem63Compression T Z) := by
    simpa [theorem63Compression, DavisKahan.Sylvester.compressOperator] using
      DavisKahan.Sylvester.isSelfAdjoint_compressOperator hTsa Z
  have hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2 := by
    intro z
    refine SpectralOrder.re_inner_le_of_spectrum_subset_Iic
      (theorem63Compression T Z) hMsa ?_ z
    intro r hr
    exact (hCompressionSpectrum hr).2
  have hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ := fun y hy =>
    SpectralOrder.le_re_inner_on_subspace_of_restriction_spectrum_subset_Ici
      hT (hV.orthogonalComplement).1 hUnwantedSpectrum hy
  exact tanTheta_directed_bounded_symmetricNorming_complex N T hT V Z hV hdelta hCompressionUpper
    hUnwantedLower hResidual

end

end DavisKahan1970
end TauCeti
