/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section3Proposition35
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section3AcuteCounterexample

/-!
# Dependency audit for Davis--Kahan 1970, Proposition 3.5

The paper states Proposition 3.5 for real or complex Hilbert spaces without a
finite-dimensional restriction.  This audit checks the arbitrary-dimensional
`RCLike` source surface and instantiates its commutation theorem over both real
and complex Hilbert spaces, so neither scalar field is covered merely by prose.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970
namespace Section3Audit

section Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]
variable (U V : Submodule ℝ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

-- The projections are written as `Submodule.starProjection`, not as the short
-- name `projection`: two different declarations carry that short name
-- (`TauCeti.DavisKahan.projection`, a continuous linear map, and
-- `TauCeti.projection`, a plain linear map), and which one a bare occurrence
-- picks up depends on the enclosing namespace.  Spelling the underlying
-- `starProjection` fixes the reading here and simultaneously checks that the
-- endpoint's projections really are the orthogonal ones.
example (hacute : TauCeti.IsAcute U V) :
    Commute (proposition3_5_angleOperator U V) (U.starProjection : H →L[ℝ] H) ∧
      Commute (proposition3_5_angleOperator U V) (V.starProjection : H →L[ℝ] H) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_quarterTurn U V) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_directRotation U V) :=
  proposition3_5_commutations_acute U V hacute

-- The printed commutation clause carries no acuteness hypothesis; only a crossed-defect
-- isometry, which is the paper's matched-crossing condition (3.5).
example (J : TauCeti.DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℝ]
      TauCeti.DavisKahan.halmosTargetDefect U V) :
    Commute (proposition3_5_angleOperator U V) (U.starProjection : H →L[ℝ] H) ∧
      Commute (proposition3_5_angleOperator U V) (V.starProjection : H →L[ℝ] H) ∧
      Commute (proposition3_5_angleOperator U V) (corollary3_2_nonacuteQuarterTurn U V J) ∧
      Commute (proposition3_5_angleOperator U V)
        (TauCeti.DavisKahan.nonacuteDirectRotation U V J) :=
  proposition3_5_commutations U V J

end Real

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

example (hacute : TauCeti.IsAcute U V) :
    Commute (proposition3_5_angleOperator U V) (U.starProjection : H →L[ℂ] H) ∧
      Commute (proposition3_5_angleOperator U V) (V.starProjection : H →L[ℂ] H) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_quarterTurn U V) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_directRotation U V) :=
  proposition3_5_commutations_acute U V hacute

-- The printed commutation clause carries no acuteness hypothesis; only a crossed-defect
-- isometry, which is the paper's matched-crossing condition (3.5).
example (J : TauCeti.DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      TauCeti.DavisKahan.halmosTargetDefect U V) :
    Commute (proposition3_5_angleOperator U V) (U.starProjection : H →L[ℂ] H) ∧
      Commute (proposition3_5_angleOperator U V) (V.starProjection : H →L[ℂ] H) ∧
      Commute (proposition3_5_angleOperator U V) (corollary3_2_nonacuteQuarterTurn U V J) ∧
      Commute (proposition3_5_angleOperator U V)
        (TauCeti.DavisKahan.nonacuteDirectRotation U V J) :=
  proposition3_5_commutations U V J

end Complex

end Section3Audit
end DavisKahan1970
end TauCeti
