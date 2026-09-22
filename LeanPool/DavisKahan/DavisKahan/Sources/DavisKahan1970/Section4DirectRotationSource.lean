/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section4Real
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section3Proposition32
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.SourceDirectRotation

/-!
# Section 4 on the source's own object: the direct rotation

Davis and Kahan enter Section 4 with **a direct rotation already fixed** by
Section 3, and say the competing unitary's displacement is minimized when
`V = U`.  Their statements are about that rotation.  They are not about *some*
rotation, and they are not about a chosen isometry `J` between the two crossed
defect spaces, which is an artefact of the construction.

So each façade below takes the rotation as a hypothesis:

```lean
(D : H →L[𝕜] H) (hD : IsSourceDirectRotation U V D)
```

`IsSourceDirectRotation` is Davis and Kahan's Definition 3.1 — the repository's
`IsDirectRotation` records the diagonal compressions only through their
numerical range, which is strictly weaker and for which these statements are
false.  Section 4's standing convention (3.5) is not a separate hypothesis: by
Proposition 3.2 the existence of `D` *is* (3.5).

Proposition 3.2 also says the direct rotation is not unique, so a statement
about "the" direct rotation is only meaningful because the displacement `1 − D`
does not depend on which one is taken.  That is
`norm_one_sub_apply_eq_of_isSourceDirectRotation`, proved in
`Geometry/Polar/SourceDirectRotation.lean` from the uniqueness of nonnegative
square roots; it is what lets each façade discharge its conclusion against the
`nonacuteDirectRotation U V J` the constructions underneath actually use.

Proposition 4.2 needs no façade: its canonical statement already takes
`CrossedDefectsEquivalent` and never names a rotation, because its conclusion is
about the principal angles and an arbitrary competitor.
-/

open TauCeti.DavisKahan.Angle

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace
open DavisKahan.ExactSinTheta

noncomputable section

universe v

section Bridges

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal

/-- The displacement of a Definition 3.1 direct rotation, read on `U`, has the
same approximation numbers as the displacement of the construction the proofs
underneath use. -/
theorem hasSameApproximationNumbers_displacement_of_isSourceDirectRotation
    {D : H →L[𝕜] H} (hD : DavisKahan.IsSourceDirectRotation U V D)
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[𝕜] DavisKahan.halmosTargetDefect U V) :
    ((1 - D) ∘L U.starProjection).HasSameApproximationNumbers
      ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L U.starProjection) :=
  ContinuousLinearMap.hasSameApproximationNumbers_of_norm_apply_eq _ _ fun _ =>
    DavisKahan.norm_one_sub_apply_eq_of_isSourceDirectRotation U V hD J _

/-- The full displacement's Gram operator does not depend on which Definition 3.1
direct rotation is taken. -/
theorem fullDisplacement_gram_eq_of_isSourceDirectRotation
    {D : H →L[𝕜] H} (hD : DavisKahan.IsSourceDirectRotation U V D)
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[𝕜] DavisKahan.halmosTargetDefect U V) :
    (1 - star D) * (1 - D) =
      (1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - DavisKahan.nonacuteDirectRotation U V J) := by
  have h1 := DavisKahan.star_one_sub_mul_one_sub_of_unitary hD.unitary_mem
  have h2 := DavisKahan.star_one_sub_mul_one_sub_of_unitary
    (DavisKahan.nonacuteDirectRotation_mem_unitary U V J)
  rw [star_sub, star_one] at h1 h2
  rw [h1, h2, DavisKahan.IsSourceDirectRotation.add_star_eq_nonacuteDirectRotation U V hD J]

/-- Section 4's standing convention (3.5) is not an extra hypothesis: by
Proposition 3.2 a direct rotation exists exactly when it holds. -/
theorem crossedDefectsEquivalent_of_isSourceDirectRotation
    {D : H →L[𝕜] H} (hD : DavisKahan.IsSourceDirectRotation U V D) :
    DavisKahan.CrossedDefectsEquivalent U V :=
  (proposition3_2_exists_iff_crossedDefectsEquivalent U V).mp ⟨D, hD.toIsDirectRotation⟩

end Bridges

/-! ### Over `ℂ` -/

section Complex

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Davis--Kahan 1970, Proposition 4.1, on the source's own direct rotation.**

For the direct rotation `D` the paper has fixed, both printed formulations hold:
the pointwise angle bound against an arbitrary competitor `W`, and the
singular-value identity and domination. -/
theorem proposition4_1_directRotation_sourceExact_complex
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (D : H →L[ℂ] H) (hD : DavisKahan.IsSourceDirectRotation U V D)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∃ v : {n : ℕ // 0 < TauCeti.principalSineSequence U V n} → U,
        Orthonormal ℂ v ∧
          ∀ n : {n : ℕ // 0 < TauCeti.principalSineSequence U V n},
            TauCeti.principalAngleSequence U V (n : ℕ) ≤
              TauCeti.vectorAngle ℂ (v n : H) (W (v n : H))) ∧
      (∀ n : ℕ,
        (ContinuousLinearMap.approximationNumber
            ((1 - D) ∘L U.starProjection) n : Real) =
          2 * Real.sin (TauCeti.principalAngleSequence U V n / 2)) ∧
      ∀ n : ℕ,
        ContinuousLinearMap.approximationNumber
            ((1 - D) ∘L U.starProjection) n ≤
          ContinuousLinearMap.approximationNumber
            ((1 - W) ∘L U.starProjection) n := by
  obtain ⟨J⟩ := crossedDefectsEquivalent_of_isSourceDirectRotation U V hD
  obtain ⟨hv, heq, hle⟩ :=
    proposition4_1_compact_nonacute_complex U V hcompact J W hWunitary hWmap
  have hsame := hasSameApproximationNumbers_displacement_of_isSourceDirectRotation U V hD J
  exact ⟨hv, fun n => (hsame n).trans (heq n), fun n => (hsame n).trans_le (hle n)⟩

/-- **Davis--Kahan 1970, Corollary 4.1, on the source's own direct rotation.**

The displacement of the fixed direct rotation is minimal in every normalized
unitarily invariant norm. -/
theorem corollary4_1_directRotation_sourceExact_complex
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (D : H →L[ℂ] H) (hD : DavisKahan.IsSourceDirectRotation U V D)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - W) ∘L U.starProjection)) :
    N.Mem ((1 - D) ∘L U.starProjection) ∧
      N.gauge ((1 - D) ∘L U.starProjection) ≤
        N.gauge ((1 - W) ∘L U.starProjection) := by
  obtain ⟨J⟩ := crossedDefectsEquivalent_of_isSourceDirectRotation U V hD
  obtain ⟨hmem₀, hle₀⟩ :=
    corollary4_1_compact_nonacute_sourceExact_complex N U V hcompact J W
      hWunitary hWmap hWmem
  have hsame := hasSameApproximationNumbers_displacement_of_isSourceDirectRotation U V hD J
  obtain ⟨hmem, hle⟩ :=
    N.toFanDominantIdealFamily.majorization_mem_and_gauge_le hmem₀
      (fun k => le_of_eq (hsame.kyFanGauge_eq k))
  exact ⟨hmem, hle.trans hle₀⟩

/-- **Davis--Kahan 1970, Proposition 4.3, on the source's own direct rotation.** -/
theorem proposition4_3_directRotation_sourceExact_complex
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (D : H →L[ℂ] H) (hD : DavisKahan.IsSourceDirectRotation U V D)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star D) * (1 - D)) ∧
      N.gauge ((1 - star D) * (1 - D)) ≤ N.gauge ((1 - star W) * (1 - W)) := by
  obtain ⟨J⟩ := crossedDefectsEquivalent_of_isSourceDirectRotation U V hD
  rw [fullDisplacement_gram_eq_of_isSourceDirectRotation U V hD J]
  exact proposition4_3_compact_nonacute_sourceExact_complex N U V hcompact J W
    hWunitary hWmap hWmem

end Complex

/-! ### Over `ℝ` -/

section Real

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- **Davis--Kahan 1970, Proposition 4.1 over `ℝ`, on the source's own direct
rotation.** -/
theorem proposition4_1_directRotation_sourceExact_real
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (D : E →L[ℝ] E) (hD : DavisKahan.IsSourceDirectRotation U V D)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∃ v : {n : ℕ // 0 < TauCeti.principalSineSequence U V n} → U,
        Orthonormal ℝ v ∧
          ∀ n : {n : ℕ // 0 < TauCeti.principalSineSequence U V n},
            TauCeti.principalAngleSequence U V (n : ℕ) ≤
              TauCeti.vectorAngle ℝ (v n : E) (W (v n : E))) ∧
      (∀ n : ℕ,
        (ContinuousLinearMap.approximationNumber
            ((1 - D) ∘L U.starProjection) n : Real) =
          2 * Real.sin (TauCeti.principalAngleSequence U V n / 2)) ∧
      ∀ n : ℕ,
        ContinuousLinearMap.approximationNumber
            ((1 - D) ∘L U.starProjection) n ≤
          ContinuousLinearMap.approximationNumber
            ((1 - W) ∘L U.starProjection) n := by
  obtain ⟨J⟩ := crossedDefectsEquivalent_of_isSourceDirectRotation U V hD
  obtain ⟨hv, heq, hle⟩ :=
    proposition4_1_compact_nonacute_real U V hcompact J W hWunitary hWmap
  have hsame := hasSameApproximationNumbers_displacement_of_isSourceDirectRotation U V hD J
  exact ⟨hv, fun n => (hsame n).trans (heq n), fun n => (hsame n).trans_le (hle n)⟩

/-- **Davis--Kahan 1970, Corollary 4.1 over `ℝ`, on the source's own direct
rotation.** -/
theorem corollary4_1_directRotation_sourceExact_real
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (D : E →L[ℝ] E) (hD : DavisKahan.IsSourceDirectRotation U V D)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - W) ∘L U.starProjection)) :
    N.Mem ((1 - D) ∘L U.starProjection) ∧
      N.gauge ((1 - D) ∘L U.starProjection) ≤
        N.gauge ((1 - W) ∘L U.starProjection) := by
  obtain ⟨J⟩ := crossedDefectsEquivalent_of_isSourceDirectRotation U V hD
  obtain ⟨hmem₀, hle₀⟩ :=
    corollary4_1_compact_nonacute_sourceExact_real N U V hcompact J W
      hWunitary hWmap hWmem
  have hsame := hasSameApproximationNumbers_displacement_of_isSourceDirectRotation U V hD J
  obtain ⟨hmem, hle⟩ :=
    N.toFanDominantIdealFamily.majorization_mem_and_gauge_le hmem₀
      (fun k => le_of_eq (hsame.kyFanGauge_eq k))
  exact ⟨hmem, hle.trans hle₀⟩

/-- **Davis--Kahan 1970, Proposition 4.3 over `ℝ`, on the source's own direct
rotation.** -/
theorem proposition4_3_directRotation_sourceExact_real
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (D : E →L[ℝ] E) (hD : DavisKahan.IsSourceDirectRotation U V D)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star D) * (1 - D)) ∧
      N.gauge ((1 - star D) * (1 - D)) ≤ N.gauge ((1 - star W) * (1 - W)) := by
  obtain ⟨J⟩ := crossedDefectsEquivalent_of_isSourceDirectRotation U V hD
  rw [fullDisplacement_gram_eq_of_isSourceDirectRotation U V hD J]
  exact proposition4_3_compact_nonacute_sourceExact_real N U V hcompact J W
    hWunitary hWmem hWmap

end Real

end

end DavisKahan1970
end TauCeti
