/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63FiniteSource
import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63InfiniteTrial

/-! # Section2Tan Theta Perturbation -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan Section 2, tan Θ: the perturbation companion

The Section 2 tangent theorem comes in two forms.  The **residual** form bounds
the tangent by the Rayleigh--Ritz residual of a trial subspace; that form is
`theorem6_3_generalizedTanTheta_of_formBounds_equalRank`, proved at arbitrary
Hilbert-space and ideal-gauge scope.  The **perturbation** form bounds it by the
perturbation itself, when the trial subspace is invariant for the perturbed
operator rather than arbitrary.

This module supplies the second, and the bridge between them is one line of
algebra rather than a new estimate:

```
residual(T, Z) = P_Zᗮ T|_Z = P_Zᗮ (T + E)|_Z − P_Zᗮ E|_Z = − P_Zᗮ E|_Z,
```

because `Z` being invariant for `T + E` kills the middle term.  So the residual
is a contraction applied to the perturbation restricted to `Z`, its
approximation numbers are dominated termwise, and Fan dominance carries that to
every supported ideal gauge.

## Scope

Arbitrary complete complex Hilbert space, finite-dimensional trial space, every
Fan-dominant unitarily invariant ideal gauge, and no comparison of the ranks of
`Z` and `V` — see the `DirectedTangentExistence` section of
`DavisKahan/TanTheta/Theorem63FiniteSource.lean` for why the printed dimension
hypothesis is redundant here.  The tangent representative is the one that file
constructs, so nothing is assumed about it either.

The right-hand side is `E ∘L Z.subtypeL`, the perturbation *restricted to the
trial space*, not `E` itself: the two live in different spaces, so an ideal
gauge cannot compare them directly, and the restriction is what the estimate
actually controls.  It is the sharper statement in any case.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.TanTheta
open Module (finrank)

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- **The Ritz residual of an invariant trial space is the compressed
perturbation.**

If `Z` is invariant for `T + E` then `P_Zᗮ (T + E)|_Z = 0`, so the residual of
`T` on `Z` is exactly `−P_Zᗮ E|_Z`.  This is what turns the residual form of the
tangent theorem into the perturbation form; no estimate is involved. -/
theorem theorem63Residual_eq_neg_of_invariant
    (T E : H →L[ℂ] H) (Z : Submodule ℂ H) [Z.HasOrthogonalProjection]
    (hinv : ∀ x ∈ Z, (T + E) x ∈ Z) :
    theorem63Residual T Z =
      -(Zᗮ.starProjection ∘L (E ∘L Z.subtypeL)) := by
  apply ContinuousLinearMap.ext
  intro z
  have hz : ((T + E) (z : H)) ∈ Z := hinv (z : H) z.property
  have hzero : Zᗮ.starProjection ((T + E) (z : H)) = 0 := by
    refine (Submodule.starProjection_apply_eq_zero_iff Zᗮ).mpr ?_
    rw [Submodule.orthogonal_orthogonal]
    exact hz
  have hsplit : Zᗮ.starProjection (T (z : H)) +
      Zᗮ.starProjection (E (z : H)) = 0 := by
    rw [← map_add]
    simpa using hzero
  have hres : theorem63Residual T Z z = Zᗮ.starProjection (T (z : H)) := by
    rw [theorem63Residual_eq_complementaryProjection]
    rfl
  rw [hres]
  have : Zᗮ.starProjection (T (z : H)) = -Zᗮ.starProjection (E (z : H)) :=
    eq_neg_of_add_eq_zero_left hsplit
  simpa using this

/-- Termwise domination of the residual's approximation numbers by those of the
restricted perturbation. -/
theorem approximationSingularValue_theorem63Residual_le_of_invariant
    (T E : H →L[ℂ] H) (Z : Submodule ℂ H) [Z.HasOrthogonalProjection]
    [CompleteSpace Z]
    (hinv : ∀ x ∈ Z, (T + E) x ∈ Z) (n : ℕ) :
    approximationSingularValue n (theorem63Residual T Z) ≤
      approximationSingularValue n (E ∘L Z.subtypeL) := by
  rw [theorem63Residual_eq_neg_of_invariant T E Z hinv,
    approximationSingularValue_neg]
  have hcomp := approximationSingularValue_comp_le (𝕜 := ℂ) n
    (Zᗮ.starProjection) (E ∘L Z.subtypeL) (1 : Z →L[ℂ] Z)
  have hid : (Zᗮ.starProjection ∘L ((E ∘L Z.subtypeL) ∘L
      (1 : Z →L[ℂ] Z))) = Zᗮ.starProjection ∘L (E ∘L Z.subtypeL) := by
    ext x
    simp
  rw [hid] at hcomp
  refine hcomp.trans ?_
  have hP : ‖(Zᗮ.starProjection : H →L[ℂ] H)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      simpa only [one_mul] using Submodule.norm_starProjection_apply_le Zᗮ x
  have hone : ‖(1 : Z →L[ℂ] Z)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hnn : 0 ≤ approximationSingularValue n (E ∘L Z.subtypeL) :=
    approximationSingularValue_nonneg _ _
  calc
    ‖(Zᗮ.starProjection : H →L[ℂ] H)‖ *
        approximationSingularValue n (E ∘L Z.subtypeL) *
          ‖(1 : Z →L[ℂ] Z)‖ ≤
        1 * approximationSingularValue n (E ∘L Z.subtypeL) * 1 := by
      have h1 : ‖(Zᗮ.starProjection : H →L[ℂ] H)‖ *
          approximationSingularValue n (E ∘L Z.subtypeL) ≤
          1 * approximationSingularValue n (E ∘L Z.subtypeL) :=
        mul_le_mul_of_nonneg_right hP hnn
      exact mul_le_mul h1 hone (norm_nonneg (1 : Z →L[ℂ] Z)) (by linarith)
    _ = approximationSingularValue n (E ∘L Z.subtypeL) := by ring

/-- **Davis--Kahan Section 2, tangent theorem, perturbation form.**

If the finite-dimensional trial space `Z` is invariant for the perturbed
operator `T + E`, and `T` reduces `V` with the source gap, then the directed
tangent is bounded by the perturbation restricted to `Z`, in every Fan-dominant
unitarily invariant ideal gauge:

`δ · N(tan Θ₀) ≤ N(E|_Z)`.

No rank comparison between `Z` and `V`, no assumed tangent representative, and
an arbitrary complete complex Hilbert space. -/
theorem theorem6_3_perturbation_equalRank
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (T E : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (hinv : ∀ x ∈ Z, (T + E) x ∈ Z)
    (hEmem : N.Mem (E ∘L Z.subtypeL)) :
    N.Mem (theorem63DirectedTangent Z V) ∧
      delta * N.gauge (theorem63DirectedTangent Z V) ≤
        N.gauge (E ∘L Z.subtypeL) := by
  have : CompleteSpace Z := FiniteDimensional.complete ℂ Z
  refine mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N.toFanDominantIdealFamily hdelta
    hEmem ?_
  intro k
  refine le_trans
    (theorem6_3_all_kyFan_core_directedTangent Z V T hT hV hdelta
      hCompressionUpper hUnwantedLower k) ?_
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  exact Finset.sum_le_sum fun n _ =>
    approximationSingularValue_theorem63Residual_le_of_invariant T E Z hinv n

/-- **Davis--Kahan Section 2, tangent theorem, perturbation form, at arbitrary trial
dimension.**

The trial space `Z` carries no dimension hypothesis — only completeness.  If `Z` is
invariant for the perturbed operator `T + E` and `T` reduces `V` with the source gap, then
some tangent representative with the paper's approximation numbers satisfies
`δ · N(tan Θ₀) ≤ N(E|_Z)` in every Fan-dominant unitarily invariant ideal gauge.  This is
the perturbation companion of the equal-dimensional infinite/noncompact residual theorem
`TanTheta.theorem6_3_infiniteTrial_of_formBounds_exists`; the bridge is the same one
line of algebra as in the finite case. -/
theorem theorem6_3_perturbation_infiniteTrial
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (T E : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (hinv : ∀ x ∈ Z, (T + E) x ∈ Z)
    (hEmem : N.Mem (E ∘L Z.subtypeL)) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge (E ∘L Z.subtypeL) := by
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersInfinite Z V
      (fun n => approximationSingularValue_sineBlock_lt_one_infiniteTrial T V Z hT hV
        hdelta hCompressionUpper hUnwantedLower n)
  refine ⟨tanTheta0, htan, ?_⟩
  refine mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N.toFanDominantIdealFamily hdelta hEmem fun k => ?_
  have hKyTan : kyFanApproximationGauge k tanTheta0 =
      ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := htan n
    unfold approximationSingularValue at h
    exact h
  have hcore := theorem6_3_all_kyFan_core_infiniteTrial T V Z hT hV hdelta
    hCompressionUpper hUnwantedLower k
  have hRE : kyFanApproximationGauge k (theorem63Residual T Z) ≤
      kyFanApproximationGauge k (E ∘L Z.subtypeL) := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    refine Finset.sum_le_sum fun n _ => ?_
    have h := approximationSingularValue_theorem63Residual_le_of_invariant T E Z hinv n
    unfold approximationSingularValue at h
    exact h
  rw [hKyTan]
  exact hcore.trans hRE

end DavisKahan1970
end TauCeti
