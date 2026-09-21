/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.PrincipalSineSequence

/-!
# Principal-angle sequences in arbitrary Hilbert dimension

The principal-sine sequence of a pair of closed subspaces is the decreasing
approximation-number sequence of the directed sine operator `P_{Vᗮ}|_U`.
Since that operator is a contraction, every principal sine lies in `[0, 1]`.
Applying `arcsin` therefore gives a canonical principal-angle sequence in
`[0, π / 2]` whose sine is exactly the principal-sine sequence.

This is the sequence-level dictionary used by Davis--Kahan 1970 Section 4.
It does not require compactness: compactness is needed in the paper to obtain a
discrete angle list from spectral theory, whereas approximation numbers already
provide a decreasing sequence for every bounded directed sine operator.
-/

open scoped ENNReal InnerProductSpace

public section

namespace TauCeti

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Principal angles in arbitrary Hilbert dimension, ordered by the
approximation-number principal sines. -/
noncomputable def principalAngleSequence (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (n : ℕ) : ℝ :=
  Real.arcsin (principalSineSequence U V n)

/-- Principal angles are nonnegative. -/
theorem principalAngleSequence_nonneg (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (n : ℕ) :
    0 ≤ principalAngleSequence U V n := by
  exact Real.arcsin_nonneg.mpr (principalSineSequence_nonneg U V n)

/-- Principal angles lie in the first quadrant. -/
theorem principalAngleSequence_le_pi_div_two (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (n : ℕ) :
    principalAngleSequence U V n ≤ Real.pi / 2 := by
  exact Real.arcsin_le_pi_div_two _

/-- The sine of the `n`th principal angle is the `n`th principal sine. -/
@[simp]
theorem sin_principalAngleSequence (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (n : ℕ) :
    Real.sin (principalAngleSequence U V n) = principalSineSequence U V n := by
  rw [principalAngleSequence]
  exact Real.sin_arcsin
    (by linarith [principalSineSequence_nonneg U V n])
    (principalSineSequence_le_one U V n)

/-- The squared-sine energy of the principal-angle sequence is exactly the
squared principal-sine energy.  The equality is in `ℝ≥0∞`, so it includes a
divergent infinite sum. -/
theorem tsum_sq_sin_principalAngleSequence_eq_tsum_sq_principalSineSequence
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (∑' n : ℕ, ENNReal.ofReal (Real.sin (principalAngleSequence U V n)) ^ 2) =
      ∑' n : ℕ, ENNReal.ofReal (principalSineSequence U V n) ^ 2 := by
  refine tsum_congr fun n => ?_
  rw [sin_principalAngleSequence]

end

end TauCeti

end
