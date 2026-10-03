/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.ScalarGeneric
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNormLaws
public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.TanTheta.RitzResidual
public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DoubleAngle.SinTwoThetaResidual
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaBranchFree

/-!
# Scalar-generic headline review surfaces

This module gives the remaining three trigonometric headline theorems compact,
reviewer-facing declarations over a generic `RCLike` scalar field.

The goal is semantic auditability rather than a new proof route.  The wrappers
promote existing scalar-generic Ky Fan/UI-norm engines to the literal
`SymmetricNormingFunction` used by the source census, and spell out source
spectral hypotheses instead of hiding them in local gap structures whenever
that can be done without weakening the theorem.

The single-angle sine theorem lives in `SineTheta/ScalarGeneric.lean` because
its unbounded scalar-generic engine is substantial enough to merit its own
module.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace BigOperators

noncomputable section

universe u v

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.FiniteDimensional

section FiniteGeneric

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Finite-dimensional headline coordinates are automatically complete.  Keep
these implementation instances local so completeness does not appear as an
extra mathematical hypothesis in the reviewer-facing theorem signatures. -/
local instance headlineCompleteE : CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E

local instance headlineCompleteF : CompleteSpace F :=
  FiniteDimensional.complete 𝕜 F

/-- **Davis--Kahan 1970, Section 2 `tan Theta`, scalar-generic directed
headline form.**

This is the paper's sharp residual conclusion

`delta * N(tan Theta0) <= N(R)`

for a Rayleigh--Ritz trial subspace.  The one-sided spectral placement is
written directly in the theorem type rather than through
`TanThetaIntervalGap`: the Ritz compression lies in `[beta, alpha]` and the
unwanted exact spectrum lies in `[alpha + delta, infinity)`.

The theorem is finite-dimensional only because this wrapper reuses the
scalar-generic singular-value engine.  The source census separately points to
the arbitrary-dimensional/unbounded source theorems as scope companions. -/
theorem tanTheta_directed_finiteDimensional_symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E)
    (_hrank : Module.finrank 𝕜 F = Module.finrank 𝕜 U)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hCompressionSpectrum :
      PointSpectrumIn (compression A X) ⊤ (Set.Icc β α))
    (hUnwantedSpectrum : PointSpectrumIn A Uᗮ (Set.Ici (α + δ)))
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U)
    (hR : N.Mem (ritzResidual A X).toContinuousLinearMap) :
    N.Mem tanTheta0.toContinuousLinearMap ∧
      δ * N.gauge tanTheta0.toContinuousLinearMap ≤
        N.gauge (ritzResidual A X).toContinuousLinearMap := by
  have hgap : TanThetaIntervalGap A U X β α δ :=
    ⟨hCompressionSpectrum, hUnwantedSpectrum⟩
  apply N.mul_gauge_le_of_all_mul_kyFan_le hδ hR
  intro k
  rw [← kyFanSum_eq_kyFanApproximationGauge k tanTheta0,
    ← kyFanSum_eq_kyFanApproximationGauge k (ritzResidual A X)]
  exact kyFan_tanTheta0_ritzResidual_le hA hU X hβα hδ hgap tanTheta0 htan k

/-- **Davis--Kahan 1970, Section 2 `sin (2 Theta0)`, scalar-generic directed
headline form.**

The interval/exterior separation and the residual are explicit in the type.
The conclusion is the paper's factor-two bound for every source
unitary-invariant norm:

`delta * N(sin (2 Theta0)) <= 2 * N(R)`.

As for the tangent wrapper above, this particular scalar-generic facade uses
the finite-dimensional singular-value engine; arbitrary-dimensional and
unbounded scope remains certified by the source-specific companion theorems. -/
theorem sinTwoTheta_directed_finiteDimensional_symmetricNorming_rclike
    (N : SymmetricNormingFunction)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {β α δ : ℝ} (_hβα : β ≤ α) (hδ : 0 < δ)
    (hCompressionSpectrum : PointSpectrumIn M ⊤ (Set.Icc β α))
    (hUnwantedSpectrum :
      PointSpectrumIn A Uᗮ {lam : ℝ | lam ≤ β - δ ∨ α + δ ≤ lam})
    (hR : N.Mem (residual A X M).toContinuousLinearMap) :
    N.Mem (sinTwoThetaEmbedding U X).toContinuousLinearMap ∧
      δ * N.gauge (sinTwoThetaEmbedding U X).toContinuousLinearMap ≤
        2 * N.gauge (residual A X M).toContinuousLinearMap := by
  let S := (sinTwoThetaEmbedding U X).toContinuousLinearMap
  let R := (residual A X M).toContinuousLinearMap
  have htwo : ‖((2 : ℝ) : 𝕜)‖ = 2 := by
    rw [RCLike.norm_ofReal]
    norm_num
  have hscaled : ∀ k : ℕ,
      δ * kyFanApproximationGauge k S ≤
        kyFanApproximationGauge k (((2 : ℝ) : 𝕜) • R) := by
    intro k
    rw [kyFanApproximationGauge_smul, htwo]
    change δ * kyFanApproximationGauge k
        (sinTwoThetaEmbedding U X).toContinuousLinearMap ≤
      2 * kyFanApproximationGauge k (residual A X M).toContinuousLinearMap
    rw [← kyFanSum_eq_kyFanApproximationGauge k (sinTwoThetaEmbedding U X),
      ← kyFanSum_eq_kyFanApproximationGauge k (residual A X M)]
    have hOutside :
        PointSpectrumIn A Uᗮ {lam : ℝ | lam ∉ Set.Ioo (β - δ) (α + δ)} := by
      intro lam hlam
      have hout := hUnwantedSpectrum hlam
      change lam ≤ β - δ ∨ α + δ ≤ lam at hout
      change ¬ (β - δ < lam ∧ lam < α + δ)
      rcases hout with hlow | hhigh
      · intro hinside
        exact (not_lt_of_ge hlow) hinside.1
      · intro hinside
        exact (not_lt_of_ge hhigh) hinside.2
    have hk := sinTwoTheta_residual_le
      (UnitarilyInvariantSeminorm.kyFan
        (𝕜 := 𝕜) (E := F) (F := E) k)
      hA hU X hM hδ hCompressionSpectrum hOutside
    simpa only [UnitarilyInvariantSeminorm.kyFan_apply] using hk
  have hMem2 : N.Mem (((2 : ℝ) : 𝕜) • R) := by
    intro htop
    rw [N.extendedGauge_smul, htwo] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hR h
    · exact absurd h (by simp)
  obtain ⟨hmem, hle⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hδ hMem2 hscaled
  refine ⟨hmem, ?_⟩
  rw [N.gauge_smul _ hR, htwo] at hle
  exact hle

end FiniteGeneric

end

end DavisKahan1970
end TauCeti
