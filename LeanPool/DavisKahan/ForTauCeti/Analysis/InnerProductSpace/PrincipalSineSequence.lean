/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.EnergyComparison
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Gap

/-!
# Principal-sine sequences in arbitrary Hilbert dimension

The directed sine operator of a pair of closed subspaces is the restriction

`P_{Vᗮ}|_U : U → H`.

Its approximation numbers form the principal-sine sequence.  In finite
dimension this agrees with the usual singular-value list of the directed cross
projection.  In arbitrary dimension it remains defined without choosing
singular vectors, and its squared `ℓ²` energy is the Hilbert--Schmidt energy of
the directed sine operator.

The extended-real energy identity includes divergent sums, so it applies
without a summability hypothesis.
-/

open scoped ENNReal InnerProductSpace

public section

namespace TauCeti

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The directed sine operator `P_{Vᗮ}|_U`. -/
noncomputable def principalSineOperator (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[𝕜] H :=
  Vᗮ.starProjection ∘L U.subtypeL

/-- Evaluating the principal sine operator. -/
@[simp]
theorem principalSineOperator_apply (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : U) :
    principalSineOperator U V x = Vᗮ.starProjection (x : H) := by
  simp only [principalSineOperator, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]

/-- Principal sines in arbitrary Hilbert dimension, ordered decreasingly and
padded by zero when the directed sine operator has finite rank. -/
noncomputable def principalSineSequence (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (n : ℕ) : ℝ :=
  (principalSineOperator U V).approximationNumber n

/-- Principal sines are nonnegative. -/
theorem principalSineSequence_nonneg (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (n : ℕ) :
    0 ≤ principalSineSequence U V n :=
  (principalSineOperator U V).approximationNumber_nonneg n

/-- Every principal sine lies in the unit interval. -/
theorem principalSineSequence_le_one (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (n : ℕ) :
    principalSineSequence U V n ≤ 1 := by
  refine ((principalSineOperator U V).approximationNumber_le_norm n).trans ?_
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  change ‖Vᗮ.starProjection (x : H)‖ ≤ 1 * ‖x‖
  simpa using Vᗮ.norm_starProjection_apply_le (x : H)

/-- The principal-sine sequence is decreasing. -/
theorem principalSineSequence_antitone (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Antitone (principalSineSequence U V) :=
  (principalSineOperator U V).approximationNumber_antitone

variable [CompleteSpace H]

local instance sourceCompleteSpace (U : Submodule 𝕜 H) [U.HasOrthogonalProjection] :
    CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-- The squared principal-sine sequence is exactly the Hilbert--Schmidt energy
of `P_{Vᗮ}|_U`.  Both sides take values in `ℝ≥0∞`, so divergence is represented
by `⊤`. -/
theorem tsum_sq_principalSineSequence_eq_hilbertSchmidtEnergy
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {ι : Type v} (b : HilbertBasis ι 𝕜 U) :
    (∑' n : ℕ, ENNReal.ofReal (principalSineSequence U V n) ^ 2) =
      (principalSineOperator U V).hilbertSchmidtEnergy b :=
  ContinuousLinearMap.tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy
    (principalSineOperator U V) b

/-- Basis form of the principal-sine energy identity. -/
theorem tsum_sq_principalSineSequence_eq_tsum_enorm_projection
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {ι : Type v} (b : HilbertBasis ι 𝕜 U) :
    (∑' n : ℕ, ENNReal.ofReal (principalSineSequence U V n) ^ 2) =
      ∑' i, ‖Vᗮ.starProjection ((b i : U) : H)‖ₑ ^ 2 := by
  rw [tsum_sq_principalSineSequence_eq_hilbertSchmidtEnergy U V b,
    ContinuousLinearMap.hilbertSchmidtEnergy_def]
  rfl

end

end TauCeti

end
