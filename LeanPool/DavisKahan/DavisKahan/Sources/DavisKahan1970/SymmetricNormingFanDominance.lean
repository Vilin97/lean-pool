/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.KyFanNorm
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section4Real
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section5
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNormLaws
import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.NormalizedUnitaryInvariantNorm

/-! # Symmetric Norming Fan Dominance -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Reading the ideal-gauge results at the paper's own unitarily invariant norm

Several results Davis and Kahan state "for every unitary-invariant norm" are
proved here at an arbitrary `KyFanDominantIdealFamily`, and stated source-facing
at an arbitrary `SymmetricNormingFunction`.  The two are different Lean objects,
and a reviewer comparing a Lean statement with the paper is entitled to ask which
one is the printed quantifier.

**Neither is, on its own, and it does not matter, because a bound proved in one
holds in the other.**  Both bridges are theorems here:

* `symmetricNorming_of_kyFanDominant` -- an estimate holding at every
  Fan-dominant ideal gauge holds at every symmetric norming function.  Instantiate
  at the finite Ky Fan gauges, which are such families, to get Ky Fan
  majorization, then apply Fan dominance
  (`SymmetricNormingFunction.mul_gauge_le_of_all_mul_kyFan_le`).
* `kyFanDominant_of_symmetricNorming` -- the converse.  Instantiate at
  `kyFanNormingFunction k`, the Ky Fan gauge presented as a coherent symmetric
  norming function (`Ideals/KyFanNorm.lean`), to get the same majorization, then
  apply the family's own dominance field.

So both quantifiers are equivalent to weak Ky Fan majorization, which is exactly
the criterion the paper's Section 1 states it will use: "Fan dominance is used in
the strong form: `‖K‖ ≤ ‖L‖` for every unitary-invariant norm iff the inequality
holds for every Ky Fan norm."

That equivalence is what makes the source-facing endpoints cover the *printed*
norm class rather than only the Gohberg--Krein symmetrically normed ideals.  A
unitarily invariant norm on `B(H)` such as `T ↦ ‖T‖ + ‖π(T)‖`, with `π` the Calkin
quotient map, agrees with the operator norm on finite-rank operators and so is not
the prefix-supremum extension of any symmetric gauge -- it is *not* a
`SymmetricNormingFunction`.  It is a Fan-dominant ideal family, though, so the
displayed estimates hold in it, by `kyFanDominant_of_symmetricNorming` applied to
the source-facing endpoint.

This module adds no mathematics beyond the two bridges: each endpoint is the
already proved ideal-gauge theorem, read at the source's norm.

## Main results

* `symmetricNorming_of_kyFanDominant` and `kyFanDominant_of_symmetricNorming`;
* `corollary4_1_compact_nonacute_symmetricNorming_complex` and `..._real`;
* `proposition4_3_compact_nonacute_symmetricNorming_complex` and `..._real`;
* `theorem5_2_symmetricNorming_complex` and `theorem5_2_symmetricNorming_real`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Corollary 4.1, Proposition 4.3,
  Theorem 5.2.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan.ExactSinTheta


open TauCeti.DavisKahan
open TauCeti.ApproximationNumber

noncomputable section

universe u v

/-! ## The bridge -/

/-- **Fan dominance turns an ideal-gauge estimate into a source-norm estimate.**

If `d · gauge X ≤ gauge Y` holds in every Fan-dominant unitarily invariant ideal
gauge, then it holds at every normalized unitarily invariant norm in the source's
sense, and `X` lies in that norm's ideal whenever `Y` does.

The proof instantiates the hypothesis at the finite Ky Fan gauges, which are
themselves such families, and then applies Fan dominance. -/
theorem symmetricNorming_of_kyFanDominant
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (N : SymmetricNormingFunction) {X Y : E →L[𝕜] F} {d : ℝ} (hd : 0 < d)
    (hY : N.Mem Y)
    (h : ∀ M : FanDominantIdealFamily.{u, v} 𝕜,
      M.Mem Y → M.Mem X ∧ d * M.gauge X ≤ M.gauge Y) :
    N.Mem X ∧ d * N.gauge X ≤ N.gauge Y := by
  refine N.mul_gauge_le_of_all_mul_kyFan_le hd hY (fun k => ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [kyFanApproximationGauge, kyFanApproximationGauge,
      ContinuousLinearMap.kyFanGauge_zero_index,
      ContinuousLinearMap.kyFanGauge_zero_index, mul_zero]
  · have hM := h (KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk)
      (KyFanDominantIdealFamily.kyFan_mem k hk Y)
    rw [KyFanDominantIdealFamily.kyFan_gauge,
      KyFanDominantIdealFamily.kyFan_gauge] at hM
    exact hM.2

/-- **The converse bridge: a source-norm estimate holds at every Fan-dominant
ideal gauge.**

If `d · N(X) ≤ N(Y)` holds at every normalized unitarily invariant norm in the
source's sense, then it holds at every Fan-dominant unitarily invariant ideal
gauge, and `X` lies in that gauge's ideal whenever `Y` does.

The proof instantiates the hypothesis at `kyFanNormingFunction k`, the Ky Fan
gauge presented as a coherent symmetric norming function; every bounded operator
lies in its ideal, so the hypothesis applies unconditionally and yields Ky Fan
majorization, which is what a Fan-dominant family consumes.

With `symmetricNorming_of_kyFanDominant` this says the two norm quantifiers used
in this development are equivalent: each is weak Ky Fan majorization, the
criterion the paper's Section 1 announces it will use.  In particular a
source-facing endpoint stated over `SymmetricNormingFunction` is not confined to
the symmetrically normed ideals: it delivers the same bound in every unitarily
invariant norm that is Fan dominant, including norms on `B(H)` such as
`‖·‖ + ‖π(·)‖` that no symmetric gauge generates. -/
theorem kyFanDominant_of_symmetricNorming
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    (M : FanDominantIdealFamily.{u, v} 𝕜) {X : E' →L[𝕜] F'} {Y : E →L[𝕜] F}
    {d : ℝ} (hd : 0 < d)
    (hY : M.Mem Y)
    (h : ∀ N : SymmetricNormingFunction, N.Mem Y → N.Mem X ∧ d * N.gauge X ≤ N.gauge Y) :
    M.Mem X ∧ d * M.gauge X ≤ M.gauge Y := by
  refine mem_and_scaled_gauge_le_of_all_scaled_kyFan_le M hd hY (fun k => ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [kyFanApproximationGauge, kyFanApproximationGauge,
      ContinuousLinearMap.kyFanGauge_zero_index,
      ContinuousLinearMap.kyFanGauge_zero_index, mul_zero]
  · have hN := (h (kyFanNormingFunction k hk) (kyFanNormingFunction_mem k hk Y)).2
    rwa [kyFanNormingFunction_gauge, kyFanNormingFunction_gauge] at hN

/-- **The two norm quantifiers of this development are equivalent.**

Read together, `symmetricNorming_of_kyFanDominant` and
`kyFanDominant_of_symmetricNorming` say that "`d · N(X) ≤ N(Y)` at every source
norming function" and "`d · M(X) ≤ M(Y)` at every Fan-dominant ideal gauge" are the
same assertion, modulo the membership side condition each carries.  Registering
this as a theorem rather than a remark is the point: a reviewer asking which
quantifier is the paper's does not have to choose. -/
theorem symmetricNorming_iff_kyFanDominant
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {X Y : E →L[𝕜] F} {d : ℝ} (hd : 0 < d) :
    (∀ N : SymmetricNormingFunction, N.Mem Y → N.Mem X ∧ d * N.gauge X ≤ N.gauge Y) ↔
      (∀ M : FanDominantIdealFamily.{u, v} 𝕜,
        M.Mem Y → M.Mem X ∧ d * M.gauge X ≤ M.gauge Y) :=
  ⟨fun h M hY => kyFanDominant_of_symmetricNorming M hd hY h,
    fun h N hY => symmetricNorming_of_kyFanDominant N hd hY (fun M hM => h M hM)⟩

/-! ## Corollary 4.1 and Proposition 4.3 at the source norm -/

section Complex

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, Corollary 4.1, at every source unitarily invariant
norm**: `N((1 − V)P)` is minimized, among unitaries carrying `P H` onto `Q H`, by
the direct rotation.

`corollary4_1_compact_nonacute_complex` is the same statement at an arbitrary
Fan-dominant ideal gauge; this is it read at the paper's norm object, which is the
quantifier the printed corollary uses. -/
theorem corollary4_1_compact_nonacute_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - W) ∘L U.starProjection)) :
    N.Mem ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L U.starProjection) ∧
      N.gauge ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L
          U.starProjection) ≤
        N.gauge ((1 - W) ∘L U.starProjection) := by
  obtain ⟨hmem, hle⟩ := symmetricNorming_of_kyFanDominant N one_pos hWmem
    (fun M hM => by
      obtain ⟨h₁, h₂⟩ :=
        corollary4_1_compact_nonacute_complex M U V hcompact J W hWunitary hWmap hM
      exact ⟨h₁, by rw [one_mul]; exact h₂⟩)
  exact ⟨hmem, by rw [one_mul] at hle; exact hle⟩

/-- **Davis--Kahan 1970, Proposition 4.3, at every source unitarily invariant
norm**: the squared displacement `N((1 − V⋆)(1 − V))` is minimized by the direct
rotation. -/
theorem proposition4_3_compact_nonacute_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - DavisKahan.nonacuteDirectRotation U V J)) ∧
      N.gauge ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - DavisKahan.nonacuteDirectRotation U V J)) ≤
        N.gauge ((1 - star W) * (1 - W)) := by
  obtain ⟨hmem, hle⟩ := symmetricNorming_of_kyFanDominant N one_pos hWmem
    (fun M hM => by
      obtain ⟨h₁, h₂⟩ :=
        proposition4_3_compact_nonacute_idealGauge M U V hcompact J W hWunitary hWmap hM
      exact ⟨h₁, by rw [one_mul]; exact h₂⟩)
  exact ⟨hmem, by rw [one_mul] at hle; exact hle⟩

/-! ### Source-exact façades for the Section 4 and Section 5 results

The same discipline as Section 2: each façade states its result at the printed
scope -- separable Hilbert spaces, and the literal `NormalizedUnitaryInvariantNorm`
class -- and the arbitrary-Hilbert `SymmetricNormingFunction` theorem above it is
retained as a registered generalization.

These are one step shorter than the Section 2 façades.  The theorems here were
already proved from `KyFanDominantIdealFamily` statements, so a source norm
reaches them by its own projection rather than through the Fan-dominance bridge;
`normalizedUnitaryInvariant_toKyFanDominant` is that projection, and it is the
statement that the source class sits inside the Fan-dominant one. -/

/-- **Davis--Kahan 1970, Corollary 4.1 at the printed source scope over `ℂ`.** -/
theorem corollary4_1_compact_nonacute_sourceExact_complex
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - W) ∘L U.starProjection)) :
    N.Mem ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L U.starProjection) ∧
      N.gauge ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L
          U.starProjection) ≤
        N.gauge ((1 - W) ∘L U.starProjection) :=
  corollary4_1_compact_nonacute_complex N.toFanDominantIdealFamily U V hcompact J W
    hWunitary hWmap hWmem

/-- **Davis--Kahan 1970, Proposition 4.3 at the printed source scope over `ℂ`.** -/
theorem proposition4_3_compact_nonacute_sourceExact_complex
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - DavisKahan.nonacuteDirectRotation U V J)) ∧
      N.gauge ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - DavisKahan.nonacuteDirectRotation U V J)) ≤
        N.gauge ((1 - star W) * (1 - W)) :=
  proposition4_3_compact_nonacute_idealGauge N.toFanDominantIdealFamily U V hcompact J W
    hWunitary hWmap hWmem

/-- **Proposition 4.3 from the source's own hypothesis, over `ℂ`.**

Davis and Kahan inherit the *condition* under which the direct rotation exists --
the crossed defects are equivalent -- and speak of "the" direct rotation.  A
caller should therefore supply that condition, not a chosen identification.

The theorem above quantifies over every identification `J`, which is the stronger
reading and the one to use when a particular rotation is in hand.  This
corollary is for the caller who has only the source's hypothesis: it names a
direct rotation and asserts the minimality for it. -/
theorem proposition4_3_compact_nonacute_sourceExact_ofCrossedDefects_complex
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (hcrossed : DavisKahan.CrossedDefectsEquivalent U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    ∃ J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ] DavisKahan.halmosTargetDefect U V,
      N.Mem ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - DavisKahan.nonacuteDirectRotation U V J)) ∧
        N.gauge ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
            (1 - DavisKahan.nonacuteDirectRotation U V J)) ≤
          N.gauge ((1 - star W) * (1 - W)) :=
  hcrossed.elim fun J =>
    ⟨J, proposition4_3_compact_nonacute_sourceExact_complex N U V hcompact J W
      hWunitary hWmap hWmem⟩

end Complex

section Real

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Davis--Kahan 1970, Corollary 4.1 over `ℝ`, at every source unitarily
invariant norm.** -/
theorem corollary4_1_compact_nonacute_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℝ]
      DavisKahan.halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - W) ∘L U.starProjection)) :
    N.Mem ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L U.starProjection) ∧
      N.gauge ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L
          U.starProjection) ≤
        N.gauge ((1 - W) ∘L U.starProjection) := by
  obtain ⟨hmem, hle⟩ := symmetricNorming_of_kyFanDominant N one_pos hWmem
    (fun M hM => by
      obtain ⟨h₁, h₂⟩ :=
        corollary4_1_compact_nonacute_real U V M hcompact J W hWunitary hWmap hM
      exact ⟨h₁, by rw [one_mul]; exact h₂⟩)
  exact ⟨hmem, by rw [one_mul] at hle; exact hle⟩

/-- **Davis--Kahan 1970, Proposition 4.3 over `ℝ`, at every source unitarily
invariant norm.** -/
theorem proposition4_3_compact_nonacute_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℝ]
      DavisKahan.halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - DavisKahan.nonacuteDirectRotation U V J)) ∧
      N.gauge ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - DavisKahan.nonacuteDirectRotation U V J)) ≤
        N.gauge ((1 - star W) * (1 - W)) := by
  obtain ⟨hmem, hle⟩ := symmetricNorming_of_kyFanDominant N one_pos hWmem
    (fun M hM => by
      obtain ⟨h₁, h₂⟩ :=
        proposition4_3_compact_nonacute_real_idealGauge U V M hcompact J W hWunitary hWmap hM
      exact ⟨h₁, by rw [one_mul]; exact h₂⟩)
  exact ⟨hmem, by rw [one_mul] at hle; exact hle⟩

/-- **Davis--Kahan 1970, Corollary 4.1 at the printed source scope over `ℝ`.** -/
theorem corollary4_1_compact_nonacute_sourceExact_real
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℝ]
      DavisKahan.halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - W) ∘L U.starProjection)) :
    N.Mem ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L U.starProjection) ∧
      N.gauge ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L
          U.starProjection) ≤
        N.gauge ((1 - W) ∘L U.starProjection) :=
  corollary4_1_compact_nonacute_real U V N.toFanDominantIdealFamily hcompact J W
    hWunitary hWmap hWmem

/-- **Davis--Kahan 1970, Proposition 4.3 at the printed source scope over `ℝ`.** -/
theorem proposition4_3_compact_nonacute_sourceExact_real
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℝ]
      DavisKahan.halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmem : N.Mem ((1 - star W) * (1 - W)))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    N.Mem ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - DavisKahan.nonacuteDirectRotation U V J)) ∧
      N.gauge ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - DavisKahan.nonacuteDirectRotation U V J)) ≤
        N.gauge ((1 - star W) * (1 - W)) :=
  proposition4_3_compact_nonacute_real_idealGauge U V N.toFanDominantIdealFamily hcompact
    J W hWunitary hWmap hWmem

/-- **Proposition 4.3 from the source's own hypothesis, over `ℝ`.**  See the
complex sibling for why the crossed-defect condition, not a chosen
identification, is what a caller should supply. -/
theorem proposition4_3_compact_nonacute_sourceExact_ofCrossedDefects_real
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (hcrossed : DavisKahan.CrossedDefectsEquivalent U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmem : N.Mem ((1 - star W) * (1 - W)))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    ∃ J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℝ] DavisKahan.halmosTargetDefect U V,
      N.Mem ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - DavisKahan.nonacuteDirectRotation U V J)) ∧
        N.gauge ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
            (1 - DavisKahan.nonacuteDirectRotation U V J)) ≤
          N.gauge ((1 - star W) * (1 - W)) :=
  hcrossed.elim fun J =>
    ⟨J, proposition4_3_compact_nonacute_sourceExact_real N U V hcompact J W
      hWunitary hWmem hWmap⟩

end Real

/-! ## Theorem 5.2 at the source norm -/

section Sylvester

/-- **Davis--Kahan 1970, Theorem 5.2, at every source unitarily invariant
norm**: for closed self-adjoint `A ≥ c + δ > c ≥ B` and a bounded solution of
`A X = X B + R`, `δ N(X) ≤ N(R)`, and `X` lies in the norm's ideal whenever `R`
does. -/
theorem theorem5_2_symmetricNorming_complex
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (N : SymmetricNormingFunction) {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℂ] E} {c δ : ℝ} (hδ : 0 < δ)
    (hAlow : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hsyl : TauCeti.LinearPMap.SylvesterEquation A B X R)
    (hR : N.Mem R) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge R :=
  symmetricNorming_of_kyFanDominant N hδ hR
    (fun M hM => theorem5_2 M hA hB hδ hAlow hBhigh hsyl hM)

/-- **Davis--Kahan 1970, Theorem 5.2 over a real Hilbert space, at every source
unitarily invariant norm.**

The real endpoint takes the whole `FormBoundedSylvesterGap`, which is the weaker
separation hypothesis and therefore the stronger theorem: the printed ordered
configuration `A ≥ c + δ > c ≥ B` is its `leftAboveRightBelow` constructor. -/
theorem theorem5_2_symmetricNorming_real
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (N : SymmetricNormingFunction) {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℝ] E} {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hsyl : TauCeti.LinearPMap.SylvesterEquation A B X R)
    (hR : N.Mem R) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge R :=
  symmetricNorming_of_kyFanDominant N hδ hR
    (fun M hM => DavisKahan.Sylvester.davisKahan1970_sylvester_real
      M hA hB hδ hgap hsyl hM)

/-- **Davis--Kahan 1970, Theorem 5.2 over a real Hilbert space, at the printed ordered
separation.**

`A ≥ c + δ > c ≥ B` in the printed form -- one semibound each way -- rather than the
`FormBoundedSylvesterGap` abstraction, which also covers the interval/exterior and reversed
configurations and is therefore a broader hypothesis than Theorem 5.2 prints.

`theorem5_2_symmetricNorming_real` is the general theorem and is not weakened; this is its
instance at the printed hypothesis, and it is what the source row's canonical evidence names.
The complex endpoint `theorem5_2_symmetricNorming_complex` was already in this shape. -/
theorem theorem5_2_orderedGap_symmetricNorming_real
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (N : SymmetricNormingFunction) {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℝ] E} {c δ : ℝ} (hδ : 0 < δ)
    (hAlow : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hsyl : TauCeti.LinearPMap.SylvesterEquation A B X R)
    (hR : N.Mem R) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge R :=
  theorem5_2_symmetricNorming_real N hA hB hδ
    (DavisKahan.Sylvester.FormBoundedSylvesterGap.leftAboveRightBelow c hAlow hBhigh) hsyl hR

/-- **Davis--Kahan 1970, Theorem 5.2 at the printed source scope over `ℂ`.**

Arbitrary complex Hilbert spaces, and the literal normalized unitarily invariant
norm class.  The printed ordered separation `A ≥ c + δ > c ≥ B`, not the broader
gap abstraction.

**No separability**, and that is deliberate.  Section 5 announces that it is
abandoning the earlier notation and working in a more general setting; Theorem
5.2 says only that `X` and `Y` are Hilbert spaces.  The paper-wide separable
ambient scope does not survive a local reset of scope, and a façade that
reimposed it would state strictly less than the printed theorem.  Separability
was carried here until 2026-09-05, when a source-first review caught it. -/
theorem theorem5_2_sourceExact_complex
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ) {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℂ] E} {c δ : ℝ} (hδ : 0 < δ)
    (hAlow : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hsyl : TauCeti.LinearPMap.SylvesterEquation A B X R)
    (hR : N.Mem R) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge R :=
  theorem5_2 N.toFanDominantIdealFamily hA hB hδ hAlow hBhigh hsyl hR

/-- **Davis--Kahan 1970, Theorem 5.2 at the printed source scope over `ℝ`.**
Arbitrary real Hilbert spaces; see the complex sibling on why separability is
absent. -/
theorem theorem5_2_sourceExact_real
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ) {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℝ] E} {c δ : ℝ} (hδ : 0 < δ)
    (hAlow : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hsyl : TauCeti.LinearPMap.SylvesterEquation A B X R)
    (hR : N.Mem R) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge R :=
  DavisKahan.Sylvester.davisKahan1970_sylvester_real
    N.toFanDominantIdealFamily hA hB hδ
    (DavisKahan.Sylvester.FormBoundedSylvesterGap.leftAboveRightBelow c hAlow hBhigh)
    hsyl hR

end Sylvester

/-! ## The source's own norm class

`NormalizedUnitaryInvariantNorm` is the Lean type for the object Davis--Kahan
quantify over in Section 1.  The theorem below is the source's own reduction,
formalized: an estimate established for every `SymmetricNormingFunction` holds
for every normalized unitarily invariant norm.

The route is exactly the one the paper announces at (1.11)-(1.13).  A source norm
is Fan dominant by construction, so it is a `KyFanDominantIdealFamily`; and
`kyFanDominant_of_symmetricNorming` transports an estimate across that class by
instantiating at the Ky Fan gauges.  Nothing analytic is rebuilt here.

This is what lets a source-facing façade quantify over the literal source class
while its proof discharges through the existing machinery in one step. -/

/-- **The Fan-dominance bridge into the source's norm class.**

An estimate `d ‖X‖ ≤ ‖Y‖` proved for every symmetric norming function holds for
every normalized unitarily invariant norm -- which is the class Davis--Kahan
actually quantify over. -/
theorem normalizedUnitaryInvariant_of_symmetricNorming
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    (N : NormalizedUnitaryInvariantNorm.{u, v} 𝕜) {X : E' →L[𝕜] F'} {Y : E →L[𝕜] F} {d : ℝ}
    (hd : 0 < d) (hY : N.Mem Y)
    (h : ∀ M : SymmetricNormingFunction, M.Mem Y → M.Mem X ∧ d * M.gauge X ≤ M.gauge Y) :
    N.Mem X ∧ d * N.gauge X ≤ N.gauge Y :=
  kyFanDominant_of_symmetricNorming N.toFanDominantIdealFamily hd hY h

/-- **The Fan-dominance bridge with the source's constant on the right.**

Several Section 2 conclusions read `δ ‖X‖ ≤ c ‖Y‖` with `c` the printed constant
(2 for the double-angle theorems).  Dividing by `c` puts them in the shape the
base bridge takes, so this is the form the façades for those families use. -/
theorem normalizedUnitaryInvariant_of_symmetricNorming_mul
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    (N : NormalizedUnitaryInvariantNorm.{u, v} 𝕜) {X : E' →L[𝕜] F'} {Y : E →L[𝕜] F} {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) (hY : N.Mem Y)
    (h : ∀ M : SymmetricNormingFunction, M.Mem Y →
      M.Mem X ∧ d * M.gauge X ≤ c * M.gauge Y) :
    N.Mem X ∧ d * N.gauge X ≤ c * N.gauge Y := by
  have hdc : 0 < d / c := div_pos hd hc
  obtain ⟨hmem, hle⟩ :=
    normalizedUnitaryInvariant_of_symmetricNorming N hdc hY fun M hM => by
      obtain ⟨hm, hl⟩ := h M hM
      refine ⟨hm, ?_⟩
      rw [div_mul_eq_mul_div, div_le_iff₀ hc]
      linarith
  refine ⟨hmem, ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hle
  linarith

/-- The converse direction, for completeness: an estimate proved for every
normalized unitarily invariant norm says nothing weaker than one proved for every
Fan-dominant family, provided the family is normalized.

Stated as the projection it is, so a reader can see that the source class sits
*inside* the Fan-dominant one and the façades are therefore genuinely weaker
statements than the theorems that prove them -- which is the point of registering
them separately. -/
theorem normalizedUnitaryInvariant_toKyFanDominant
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    (N : NormalizedUnitaryInvariantNorm.{u, v} 𝕜) {X : E' →L[𝕜] F'} {Y : E →L[𝕜] F} {d : ℝ}
    (h : ∀ M : FanDominantIdealFamily.{u, v} 𝕜,
      M.Mem Y → M.Mem X ∧ d * M.gauge X ≤ M.gauge Y)
    (hY : N.Mem Y) :
    N.Mem X ∧ d * N.gauge X ≤ N.gauge Y :=
  h N.toFanDominantIdealFamily hY

end

end DavisKahan1970
end TauCeti
