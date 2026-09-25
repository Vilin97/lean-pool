/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedExact
public import LeanPool.DavisKahan.DavisKahan.TanTheta.RitzPair
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngle
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotation
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.ReducingCutoff

/-! # Tan Two Theta Unbounded Reducing -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# `tan 2Θ` at an arbitrary reducing subspace

`TanTwoThetaUnboundedExact.lean` and `TanTwoThetaUnboundedAmbientExact.lean`
state the unbounded `tan 2Θ` endpoints at the spectral subspace
`U = 1_{(-∞,c]}(A)`.  That was never a hypothesis of the source: Davis and Kahan
assume a *splitting* of the spectrum into a part at most `a` and a part at least
`b`, and the trial subspace is whichever reducing subspace realises it.

The spectral form was an artefact of the cutoff construction, which supplied the
Appendix's `Ω_τ → I` only for a half-line.
`ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/ReducingCutoff.lean` removes
that: every reducing subspace carries the bands of its own restriction.  This
module restates the two endpoints at the source's hypothesis.

Everything between the pole exclusion and the conclusion — the Ky Fan chain, the
two-corner Lemma 6.1/6.2 assembly, the reflection tangent's oddness and
skew-adjointness — was already stated for an arbitrary reducing `U`, so the only
changes here are the three `have`s that were spectral.

## Main results

* `tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_complex` and its
  subspace-first form
  `tanTwoTheta_directed_unboundedResidual_reducing_derivedReflection_symmetricNorming_complex`,
  which also identifies the corner's singular values with the tangents of the
  directed doubled angles.
* `tanTwoTheta_ambient_unbounded_blockRepresentative_reducing_symmetricNorming_complex`
  and `tanTwoTheta_ambient_unbounded_reducing_symmetricNorming_complex`, in
  `TanTwoThetaUnboundedAmbientExact.lean`, which owns the block-assembly lemmas.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46, Section 7 and the Appendix to
  Section 6.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace
open Filter
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.ApproximationNumber
open scoped TauCeti.CompleteSubspace

noncomputable section

universe u

variable {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G]

/-- The cutoffs of a reducing subspace, compressed to that subspace, converge
strongly to its identity. -/
theorem stronglyTendsto_cutoffCorner_reducingCutoffSeq
    {A : G →ₗ.[ℂ] G} (hA : IsSelfAdjoint A) {U : Submodule ℂ G}
    [U.HasOrthogonalProjection] (hred : TauCeti.LinearPMap.ReducesSubspace A U) :
    StronglyTendsto
      (fun n : ℕ => cutoffCorner (TauCeti.reducingCutoffSeq hA hred n))
      atTop (ContinuousLinearMap.id ℂ U) := by
  intro y
  apply tendsto_subtype_rng.mpr
  have h := TauCeti.tendsto_reducingCutoffSeq hA hred y.property
  simpa only [Function.comp_apply, ContinuousLinearMap.id_apply,
    coe_cutoffCorner_apply] using h

section Endpoints

variable {A : G →ₗ.[ℂ] G} {B Z : G →L[ℂ] G} {U : Submodule ℂ G}
  [U.HasOrthogonalProjection] {a b : ℝ}

variable (hA : IsSelfAdjoint A) (hred : TauCeti.LinearPMap.ReducesSubspace A U)
  (hB : TauCeti.IsOddFor U B)
  (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
  (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
  (hZcomm : ∀ x : A.domain,
    A ⟨Z (x : G), hZdom x⟩ + B (Z (x : G)) = Z (A x) + Z (B (x : G)))
  (hUa : ∀ x : A.domain, (x : G) ∈ U →
    RCLike.re ⟪A x, (x : G)⟫_ℂ ≤ a * ‖(x : G)‖ ^ 2)
  (hUb : ∀ x : A.domain, (x : G) ∈ Uᗮ →
    b * ‖(x : G)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : G)⟫_ℂ)
  (hab : a < b)

include hA hred hB hZsa hZ2 hZdom hZcomm hUa hUb hab

/-- The cross-block contraction bound at an arbitrary reducing subspace. -/
theorem norm_offDiagonalPart_lt_one_reducing_exact :
    ‖U.offDiagonalPart Z‖ < 1 :=
  TauCeti.norm_offDiagonalPart_lt_one_reducing hA hred hB hZsa hZ2 hZdom hZcomm
    hUa hUb hab

/-- Pole exclusion at an arbitrary reducing subspace: the reflection's diagonal
block is invertible. -/
theorem isUnit_diagonalPart_sq_reducing_exact :
    IsUnit (U.diagonalPart Z * U.diagonalPart Z) :=
  isUnit_diagonalPart_sq_of_forall_mem hZsa hZ2
    (TauCeti.crossBlockBound_nonneg (norm_nonneg B))
    (crossBlockBound_lt_one (sub_pos.mpr hab) (norm_nonneg B))
    (fun _ hy => TauCeti.norm_offDiagonalPart_apply_le_reducing hA hred hB hZsa
      hZ2 hZdom hZcomm hUa hUb hab hy)

/-- The Ky Fan chain at an arbitrary reducing subspace. -/
theorem gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan_reducing (k : ℕ) :
    (b - a) * kyFanApproximationGauge k (reflectionTangentCorner U Z) ≤
      2 * kyFanApproximationGauge k (reflectionResidualCorner U B) :=
  gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan hred hB hZsa hZ2 hZdom
    hZcomm hUa hUb hab
    (norm_offDiagonalPart_lt_one_reducing_exact hA hred hB hZsa hZ2 hZdom hZcomm
      hUa hUb hab)
    (σ := fun n : ℕ => (n : ℝ)) (fun n : ℕ => by positivity)
    (fun n : ℕ => TauCeti.reducingCutoffSeq hA hred n)
    (stronglyTendsto_cutoffCorner_reducingCutoffSeq hA hred) k

/-- **Davis--Kahan 1970, `tan 2Θ`, unbounded directed residual form, at an
arbitrary reducing subspace.**

`δ N(tan 2Θ₀) ≤ 2 N(R)` with `δ = b - a`, `R` the residual corner, and `U` any
subspace reducing `A` on which the form is at most `a` while it is at least `b`
on `Uᗮ`.  The pole exclusion is a conclusion, not a hypothesis.

This is `tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex`
with the spectral selection of `U` removed. -/
theorem tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (hRmem : N.Mem (blockCompression Uᗮ U B)) :
    IsUnit (U.diagonalPart Z * U.diagonalPart Z) ∧
      N.Mem (reflectionTangentCorner U Z) ∧
      (b - a) * N.gauge (reflectionTangentCorner U Z) ≤
        2 * N.gauge (blockCompression Uᗮ U B) := by
  have hCC := isUnit_diagonalPart_sq_reducing_exact hA hred hB hZsa hZ2 hZdom
    hZcomm hUa hUb hab
  have hhalf : 0 < (b - a) / 2 := by linarith
  have hscaled : ∀ k : ℕ,
      ((b - a) / 2) * kyFanApproximationGauge k (reflectionTangentCorner U Z) ≤
        kyFanApproximationGauge k (reflectionResidualCorner U B) := by
    intro k
    have h := gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan_reducing hA
      hred hB hZsa hZ2 hZdom hZcomm hUa hUb hab k
    linarith
  have hRmem' : N.Mem (reflectionResidualCorner U B) := hRmem
  have hUI := N.mul_gauge_le_of_all_mul_kyFan_le hhalf hRmem' hscaled
  refine ⟨hCC, hUI.1, ?_⟩
  nlinarith [hUI.2]


end Endpoints

section DerivedReflection

/-- **Davis--Kahan 1970, `tan 2Θ`, unbounded directed residual form, at an
arbitrary reducing subspace, on the paper's directed double-angle sine.**

`(b − a) N(tan 2Θ₀) ≤ 2 N(R)`, with the directed doubled tangent read off the
paper's directed double-angle sine `P_U P_{J_V Uᗮ}` through the monotone
`u ↦ tan (arcsin u)`.  The first two components make that reading a theorem:

* every approximation number of the directed double-angle sine is `< 1`, which
  is the quarter-turn exclusion the source derives; and
* the corner the bound is proved for has exactly the singular-value sequence
  `tan (arcsin aₙ(sin 2Θ₀))`, so each directed principal angle is counted
  **once**.

The doubled angle is presented by *its own* sine.  Reading it instead off the
single-angle sine by `sin 2θ = 2 sin θ cos θ` would be wrong at arbitrary
dimension: `θ ↦ sin 2θ` is not monotone on `[0, π/2]`, so applying it index by
index to an ordered singular-value sequence need not give an ordered sequence
(principal angles `75°` and `30°` already invert the order). -/
theorem tanTwoTheta_directed_unboundedResidual_reducing_derivedReflection_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : G →ₗ.[ℂ] G} {B : G →L[ℂ] G} {a b : ℝ}
    {U : Submodule ℂ G} [U.HasOrthogonalProjection]
    (V : Submodule ℂ G) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A) (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hB : TauCeti.IsOddFor U B)
    (hV : DavisKahan.ReflectionIntertwines A B V)
    (hUa : ∀ x : A.domain, (x : G) ∈ U →
      RCLike.re ⟪A x, (x : G)⟫_ℂ ≤ a * ‖(x : G)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : G) ∈ Uᗮ →
      b * ‖(x : G)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : G)⟫_ℂ)
    (hab : a < b) (hRmem : N.Mem (blockCompression Uᗮ U B)) :
    (∀ n : ℕ, (DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n < 1) ∧
      (∀ n : ℕ,
        (reflectionTangentCorner U V.reflectionOperator).approximationNumber n =
          Real.tan (Real.arcsin
            ((DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n))) ∧
      N.Mem (reflectionTangentCorner U V.reflectionOperator) ∧
      (b - a) * N.gauge (reflectionTangentCorner U V.reflectionOperator) ≤
        2 * N.gauge (blockCompression Uᗮ U B) := by
  have hZsa := TauCeti.DavisKahanExt.isSelfAdjoint_reflectionOperator V
  have hZ2 := TauCeti.DavisKahan.reflectionOperator_mul_self_complex V
  have hS1 : ‖U.offDiagonalPart V.reflectionOperator‖ < 1 :=
    norm_offDiagonalPart_lt_one_reducing_exact hA hred hB hZsa hZ2 hV.mapsDomain
      hV.commutes hUa hUb hab
  have hsame := hasSameApproximationNumbers_reflectionSineCorner_sinTwoThetaIdealBlock U V
  have hcorner : ∀ n : ℕ,
      (reflectionSineCorner U V.reflectionOperator).approximationNumber n < 1 := fun n =>
    lt_of_le_of_lt
      ((reflectionSineCorner U V.reflectionOperator).approximationNumber_le_norm n)
      (lt_of_le_of_lt norm_reflectionSineCorner_le hS1)
  obtain ⟨-, hmem, hle⟩ :=
    tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_complex hA hred hB
      hZsa hZ2 hV.mapsDomain hV.commutes hUa hUb hab N hRmem
  refine ⟨fun n => ?_, fun n => ?_, hmem, hle⟩
  · rw [← hsame n]; exact hcorner n
  · rw [← hsame n]
    exact approximationNumber_reflectionTangentCorner hZsa hZ2 hS1 n

end DerivedReflection

end

end DavisKahan1970
end TauCeti
