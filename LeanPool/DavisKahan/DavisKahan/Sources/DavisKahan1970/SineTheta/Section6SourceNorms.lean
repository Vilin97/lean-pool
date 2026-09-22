/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.NormalizedUnitaryInvariantNormExamples
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Lemma61

/-!
# Section 6's lemmas over the literal source norm class

Davis--Kahan state Lemmas 6.1 and 6.2 for *every* unitary-invariant norm.  The
compiled endpoints beneath are stated over `SymmetricNormingFunction`, the
Gohberg--Krein reading, and Lemma 6.1's is stronger still: it takes Ky Fan
inequalities as its premise, which is weaker than the printed universal-norm
premise.  Both are good analytic theorems; neither is the printed statement.

This module supplies the printed ones, over `NormalizedUnitaryInvariantNorm`.

Two directions of the Fan-dominance bridge are used, and it is worth naming which
is which.  The *conclusion* passes through
`normalizedUnitaryInvariant_of_symmetricNorming`: a bound holding for every
symmetric norming function holds for every member of the source class.  The
*premise* of Lemma 6.1 goes the other way -- from a bound assumed for every
member of the source class down to the Ky Fan inequalities the engine wants --
and that step needs the class to contain the Ky Fan norms, which is
`kyFanNormalizedUnitaryInvariantNorm`.  Without an inhabitant the printed premise
could not be used at all.
-/

namespace TauCeti
namespace DavisKahan1970

open DavisKahan
open DavisKahan.ExactSinTheta

section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
  [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] in
/-- **Davis--Kahan 1970, Lemma 6.2, over the literal source norm class.**

`‖Ω K Υ + Ω^⊥ K Υ^⊥‖ ≤ ‖K‖` for every normalized unitarily invariant norm. -/
theorem lemma6_2_sourceExact
    (N : NormalizedUnitaryInvariantNorm.{u, v} 𝕜)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {K : E →L[𝕜] E} (hK : N.Mem K) :
    N.Mem (diagonalPair U V K) ∧
      N.gauge (diagonalPair U V K) ≤ N.gauge K := by
  have hbridge := normalizedUnitaryInvariant_of_symmetricNorming
    (X := diagonalPair U V K) (Y := K) N one_pos hK fun M hM => by
      obtain ⟨hmem, hle⟩ := diagonalPair_normingGauge_le M U V hM
      exact ⟨hmem, by simpa using hle⟩
  simpa using hbridge

omit [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] [CompleteSpace E] in
/-- The Ky Fan gauge at level `0` is the empty sum. -/
private theorem kyFanApproximationGauge_zero' {F : Type v}
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] 
    (A : E →L[𝕜] F) : kyFanApproximationGauge 0 A = 0 := by
  simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]

/-- A bound assumed for every member of the source norm class gives the Ky Fan
inequalities at every level, because the Ky Fan norms *are* members. -/
private theorem all_kyFan_le_of_forall_normalizedUnitaryInvariantNorm
    {X Y : E →L[𝕜] E}
    (h : ∀ M : NormalizedUnitaryInvariantNorm.{u, v} 𝕜,
      M.Mem Y → M.Mem X ∧ M.gauge X ≤ M.gauge Y) (k : ℕ) :
    kyFanApproximationGauge k X ≤ kyFanApproximationGauge k Y := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [kyFanApproximationGauge_zero' X, kyFanApproximationGauge_zero' Y]
  · obtain ⟨-, hle⟩ := h (kyFanNormalizedUnitaryInvariantNorm (𝕜 := 𝕜) k hk)
      (mem_kyFanNormalizedUnitaryInvariantNorm k hk Y)
    rwa [gauge_kyFanNormalizedUnitaryInvariantNorm k hk X,
      gauge_kyFanNormalizedUnitaryInvariantNorm k hk Y] at hle

/-- **Davis--Kahan 1970, Lemma 6.1, over the literal source norm class.**

Both the premise and the conclusion quantify over every normalized unitarily
invariant norm, as the paper prints them.  The engine underneath takes Ky Fan
premises, which is a weaker hypothesis and hence a stronger theorem; the printed
premise reaches it because the Ky Fan norms belong to the source class. -/
theorem lemma6_1_sourceExact
    (N : NormalizedUnitaryInvariantNorm.{u, v} 𝕜)
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[𝕜] E)
    (h₀ : ∀ M : NormalizedUnitaryInvariantNorm.{u, v} 𝕜,
      M.Mem (projectionBlock Ω Γ L) →
        M.Mem (projectionBlock Ω Γ K) ∧
          M.gauge (projectionBlock Ω Γ K) ≤ M.gauge (projectionBlock Ω Γ L))
    (h₁ : ∀ M : NormalizedUnitaryInvariantNorm.{u, v} 𝕜,
      M.Mem (projectionBlock Ωᗮ Γᗮ Ltilde) →
        M.Mem (projectionBlock Ωᗮ Γᗮ Ktilde) ∧
          M.gauge (projectionBlock Ωᗮ Γᗮ Ktilde) ≤
            M.gauge (projectionBlock Ωᗮ Γᗮ Ltilde))
    (hL : N.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde)) :
    N.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ∧
      N.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ≤
        N.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde) := by
  have hk₀ := all_kyFan_le_of_forall_normalizedUnitaryInvariantNorm h₀
  have hk₁ := all_kyFan_le_of_forall_normalizedUnitaryInvariantNorm h₁
  have hbridge := normalizedUnitaryInvariant_of_symmetricNorming
    (X := projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde)
    (Y := projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde)
    N one_pos hL fun M hM => by
      have hle := lemma61_every_unitarilyInvariantNorm M Ω Γ K Ktilde L Ltilde hk₀ hk₁
      have hmem : M.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) := by
        intro htop
        rw [htop] at hle
        exact hM (top_le_iff.mp hle)
      refine ⟨hmem, ?_⟩
      have : M.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ≤
          M.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde) :=
        (ENNReal.toReal_le_toReal hmem hM).mpr hle
      simpa using this
  simpa using hbridge

/-- **Davis--Kahan 1970, Lemma 6.1's converse, over the literal source norm
class.**

The printed converse: under the two equisingularity hypotheses on the diagonal
blocks, the inequality on the sums gives back the inequality on the `Ω` blocks,
for every normalized unitarily invariant norm. -/
theorem lemma6_1_converse_sourceExact
    (N : NormalizedUnitaryInvariantNorm.{u, v} 𝕜)
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[𝕜] E)
    (hK : SameApproximationSingularValues
      (projectionBlock Ω Γ K) (projectionBlock Ωᗮ Γᗮ Ktilde))
    (hL : SameApproximationSingularValues
      (projectionBlock Ω Γ L) (projectionBlock Ωᗮ Γᗮ Ltilde))
    (hsum : ∀ M : NormalizedUnitaryInvariantNorm.{u, v} 𝕜,
      M.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde) →
        M.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ∧
          M.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ≤
            M.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde))
    (hLmem : N.Mem (projectionBlock Ω Γ L)) :
    N.Mem (projectionBlock Ω Γ K) ∧
      N.gauge (projectionBlock Ω Γ K) ≤ N.gauge (projectionBlock Ω Γ L) := by
  have hkFan := lemma61_converse Ω Γ K Ktilde L Ltilde hK hL
    (all_kyFan_le_of_forall_normalizedUnitaryInvariantNorm hsum)
  have hbridge := normalizedUnitaryInvariant_of_symmetricNorming
    (X := projectionBlock Ω Γ K) (Y := projectionBlock Ω Γ L)
    N one_pos hLmem fun M hM => by
      have hle : M.extendedGauge (projectionBlock Ω Γ K) ≤
          M.extendedGauge (projectionBlock Ω Γ L) :=
        M.extendedGauge_le_of_all_kyFan_le hkFan
      have hmem : M.Mem (projectionBlock Ω Γ K) := by
        intro htop
        rw [htop] at hle
        exact hM (top_le_iff.mp hle)
      refine ⟨hmem, ?_⟩
      have : M.gauge (projectionBlock Ω Γ K) ≤ M.gauge (projectionBlock Ω Γ L) :=
        (ENNReal.toReal_le_toReal hmem hM).mpr hle
      simpa using this
  simpa using hbridge

end

/-! ### The printed scalar scope

The theorems above carry `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere`,
which is a capability class rather than a Davis--Kahan hypothesis: it is what
makes the Ky Fan gauge available over an abstract `RCLike` field.  Both `ℝ` and
`ℂ` are instances of it, so the source-facing statements are the two fixed-field
specializations, which carry no capability class at all.

Only Lemma 6.1 needs them.  Lemma 6.2's premise does not mention a Ky Fan norm,
so its scalar-generic statement is already free of the capability class and is
itself source-exact over both fields. -/

section FixedScalar

universe v

/-- **Lemma 6.1 at the printed source scope over `ℂ`.** -/
theorem lemma6_1_sourceExact_complex
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[ℂ] E)
    (h₀ : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℂ,
      M.Mem (projectionBlock Ω Γ L) →
        M.Mem (projectionBlock Ω Γ K) ∧
          M.gauge (projectionBlock Ω Γ K) ≤ M.gauge (projectionBlock Ω Γ L))
    (h₁ : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℂ,
      M.Mem (projectionBlock Ωᗮ Γᗮ Ltilde) →
        M.Mem (projectionBlock Ωᗮ Γᗮ Ktilde) ∧
          M.gauge (projectionBlock Ωᗮ Γᗮ Ktilde) ≤
            M.gauge (projectionBlock Ωᗮ Γᗮ Ltilde))
    (hL : N.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde)) :
    N.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ∧
      N.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ≤
        N.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde) :=
  lemma6_1_sourceExact N Ω Γ K Ktilde L Ltilde h₀ h₁ hL

/-- **Lemma 6.1 at the printed source scope over `ℝ`.** -/
theorem lemma6_1_sourceExact_real
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (Ω Γ : Submodule ℝ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[ℝ] E)
    (h₀ : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℝ,
      M.Mem (projectionBlock Ω Γ L) →
        M.Mem (projectionBlock Ω Γ K) ∧
          M.gauge (projectionBlock Ω Γ K) ≤ M.gauge (projectionBlock Ω Γ L))
    (h₁ : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℝ,
      M.Mem (projectionBlock Ωᗮ Γᗮ Ltilde) →
        M.Mem (projectionBlock Ωᗮ Γᗮ Ktilde) ∧
          M.gauge (projectionBlock Ωᗮ Γᗮ Ktilde) ≤
            M.gauge (projectionBlock Ωᗮ Γᗮ Ltilde))
    (hL : N.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde)) :
    N.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ∧
      N.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ≤
        N.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde) :=
  lemma6_1_sourceExact N Ω Γ K Ktilde L Ltilde h₀ h₁ hL

/-- **Lemma 6.1's converse at the printed source scope over `ℂ`.** -/
theorem lemma6_1_converse_sourceExact_complex
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[ℂ] E)
    (hK : SameApproximationSingularValues
      (projectionBlock Ω Γ K) (projectionBlock Ωᗮ Γᗮ Ktilde))
    (hL : SameApproximationSingularValues
      (projectionBlock Ω Γ L) (projectionBlock Ωᗮ Γᗮ Ltilde))
    (hsum : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℂ,
      M.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde) →
        M.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ∧
          M.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ≤
            M.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde))
    (hLmem : N.Mem (projectionBlock Ω Γ L)) :
    N.Mem (projectionBlock Ω Γ K) ∧
      N.gauge (projectionBlock Ω Γ K) ≤ N.gauge (projectionBlock Ω Γ L) :=
  lemma6_1_converse_sourceExact N Ω Γ K Ktilde L Ltilde hK hL hsum hLmem

/-- **Lemma 6.1's converse at the printed source scope over `ℝ`.** -/
theorem lemma6_1_converse_sourceExact_real
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    (Ω Γ : Submodule ℝ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[ℝ] E)
    (hK : SameApproximationSingularValues
      (projectionBlock Ω Γ K) (projectionBlock Ωᗮ Γᗮ Ktilde))
    (hL : SameApproximationSingularValues
      (projectionBlock Ω Γ L) (projectionBlock Ωᗮ Γᗮ Ltilde))
    (hsum : ∀ M : NormalizedUnitaryInvariantNorm.{0, v} ℝ,
      M.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde) →
        M.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ∧
          M.gauge (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ Ktilde) ≤
            M.gauge (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ Ltilde))
    (hLmem : N.Mem (projectionBlock Ω Γ L)) :
    N.Mem (projectionBlock Ω Γ K) ∧
      N.gauge (projectionBlock Ω Γ K) ≤ N.gauge (projectionBlock Ω Γ L) :=
  lemma6_1_converse_sourceExact N Ω Γ K Ktilde L Ltilde hK hL hsum hLmem


end FixedScalar

end DavisKahan1970
end TauCeti
