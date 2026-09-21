/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.AngleFunctionalCalculusReal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbient
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanThetaAmbient
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaReflectionAmbient
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.FormTransport
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.SubmoduleEquiv
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.Spectrum
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.ComplexificationGauge

/-! # Ambient Real -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Source-facing Section 2 angle bounds over a **real** Hilbert space

Standing assumption 1 of Davis--Kahan 1970 is that the Hilbert space is "real or
complex".  The ambient (whole-space) conclusions

`δ ‖tan Θ‖ ≤ ‖H‖`,  `δ ‖sin 2Θ‖ ≤ 2‖H‖`,  `δ ‖tan 2Θ‖ ≤ 2‖H‖`,

and the directed residual conclusion

`δ ‖tan 2Θ₀‖ ≤ 2‖R‖`

are proved over `ℂ` in the corresponding source modules.  This module states and
proves their real-Hilbert-space counterparts with **no** loss:

* the space, operators, and subspaces are real; ambient angle operators use
  `DavisKahan/Geometry/Angle/AngleFunctionalCalculusReal.lean`, while the directed
  `Θ₀` convention follows `sourceDirectedAngleR` and is represented on the
  canonical complexification, which preserves its complete singular data;
* the constants `δ`, `1` and `2` are unchanged;
* ideal membership is *concluded*, exactly as in the complex statements, not
  assumed;
* every source unitarily invariant norm is covered at once, because
  `SymmetricNormingFunction.gauge_complexify` says the gauge of a real operator
  and of its complexification agree.

## How the transport works

There is no perturbation theory here.  The real configuration is complexified,
the complex theorem is applied verbatim, and the conclusion is read back.  Three
kinds of hypothesis have to travel, and all three were already available:

* quadratic form bounds and invariance/off-diagonality conditions, by
  `DavisKahan/SpectralTheory/Complexification/FormTransport.lean`;
* compressions to a subspace, by `complexifySubmoduleEquiv` — the adapter
  identifying `RealComplexification ↥Z` with `↥(complexifySubmodule Z)`, which
  supports the source-facing real lifts in this file;
* the real spectrum of a compression, by `realSpectrum_conjEquiv` and
  `realSpectrum_complexify`, assembled here as
  `spectrum_compressOperator_complexifySubmodule`.

## Main results

* `TauCeti.DavisKahan1970.tanTheta_ambient_bounded_symmetricNorming_real_of_transversality`
* `TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_symmetricNorming_real`
* `TauCeti.DavisKahan1970.tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_symmetricNorming_real`
* `TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_spectralGap_symmetricNorming_real`

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: standing assumption 1, the four
  theorems of Section 2, and their proofs in Sections 6 and 7.
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation
open TauCeti.DavisKahan.Foundation.RealComplexification

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-! ### Transporting the compression hypotheses -/

section Compression

variable (Z : Submodule ℝ E) [Z.HasOrthogonalProjection]

/-- The real orthogonal compression of an operator to a closed subspace.

This is the real-scalar spelling of `compressOperator`, and it is that operator:
`DavisKahan.Sylvester.compressOperator` is `RCLike`-generic, and at `𝕜 = ℝ` its body is
this one, so `compressOperatorReal Z A = compressOperator Z A` holds by `rfl` and
`compressOperator_eq_restrict_of_invariant` applies to it verbatim.  (`ℂ`-only
spellings such as `theorem63Compression` are a separate matter; it is Mathlib's
functional calculus, not the compression, that forces those.)  The two names
should eventually be one; until then, do not restate a compression fact for both. -/
def compressOperatorReal (A : E →L[ℝ] E) : Z →L[ℝ] Z :=
  Z.orthogonalProjectionOnto ∘L A ∘L Z.subtypeL

omit [CompleteSpace E] in
/-- **Compressing to a complexified subspace is a unitary conjugate of the
complexified real compression.** -/
theorem compressOperator_complexifySubmodule (A : E →L[ℝ] E) :
    compressOperator (complexifySubmodule Z) (complexify A) =
      RealComplexification.conjEquiv (complexifySubmoduleEquiv Z)
        (complexify (compressOperatorReal Z A)) := by
  refine ContinuousLinearMap.ext fun z => ?_
  have h := orthogonalProjectionOnto_complexify_apply Z A
    ((complexifySubmoduleEquiv Z).symm z)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h

omit [CompleteSpace E] in
/-- **The real spectrum of a compression survives complexification.**  Stated
with the subspace as a hypothesis so that it applies to `(complexifySubmodule Z)ᗮ`
as written, without a dependent rewrite under the projection instance. -/
theorem realSpectrum_compressOperator_complexifySubmodule
    {W : Submodule ℂ (RealComplexification E)} [W.HasOrthogonalProjection]
    (A : E →L[ℝ] E) (hW : W = complexifySubmodule Z) :
    realSpectrum (compressOperator W (complexify A)) =
      realSpectrum (compressOperatorReal Z A) := by
  subst hW
  rw [compressOperator_complexifySubmodule Z A,
    RealComplexification.realSpectrum_conjEquiv,
    RealComplexification.realSpectrum_complexify]

omit [CompleteSpace E] in
/-- A real upper form bound on a compression transports to the complexified
compression with the same constant. -/
theorem re_inner_compressOperator_le (A : E →L[ℝ] E) {alpha : ℝ}
    (h : ∀ z : Z, ⟪compressOperatorReal Z A z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (z : complexifySubmodule Z) :
    RCLike.re ⟪compressOperator (complexifySubmodule Z) (complexify A) z, z⟫_ℂ ≤
      alpha * ‖z‖ ^ 2 := by
  obtain ⟨w, rfl⟩ : ∃ w, (complexifySubmoduleEquiv Z) w = z :=
    ⟨_, (complexifySubmoduleEquiv Z).apply_symm_apply z⟩
  rw [compressOperator_complexifySubmodule Z A,
    RealComplexification.conjEquiv_apply, LinearIsometryEquiv.symm_apply_apply,
    (complexifySubmoduleEquiv Z).inner_map_map, LinearIsometryEquiv.norm_map,
    re_inner_complexify, TauCeti.RealComplexification.norm_sq]
  calc ⟪compressOperatorReal Z A (re w), re w⟫_ℝ +
        ⟪compressOperatorReal Z A (im w), im w⟫_ℝ
      ≤ alpha * ‖re w‖ ^ 2 + alpha * ‖im w‖ ^ 2 :=
        add_le_add (h _) (h _)
    _ = alpha * (‖re w‖ ^ 2 + ‖im w‖ ^ 2) := by ring

end Compression

/-! ### The real directed `tan 2Θ₀` source representative -/

/-- The canonical source-norm representative of the real directed
`tan(2Θ₀)` corner.

As with `sourceDirectedAngleR`, the real source geometry is represented on
its canonical complexification.  This loses no source information: every
`SymmetricNormingFunction` is defined from singular values and complexification
preserves those values exactly.  Keeping the representative here avoids
introducing a second real functional-calculus implementation solely for an
operator whose only source use is through a unitarily invariant norm. -/
noncomputable def tanTwoDirectedCornerR
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    RealComplexification E →L[ℂ] RealComplexification E :=
  projectionBlock (complexifySubmodule U)ᗮ (complexifySubmodule U)
    (2 * (projectorDifference (complexifySubmodule U) (complexifySubmodule V) *
      doubleSecant (complexifySubmodule U) (complexifySubmodule V)))

omit [CompleteSpace E] in
/-- The real directed residual projection block commutes with complexification.
This is the square-ambient version needed to descend the exact source norm. -/
theorem projectionBlock_complexifySubmodule_real
    (U : Submodule ℝ E) [U.HasOrthogonalProjection] (K : E →L[ℝ] E) :
    projectionBlock (complexifySubmodule U)ᗮ (complexifySubmodule U)
        (complexify K) =
      complexify (projectionBlock Uᗮ U K) := by
  rw [projectionBlock, projectionBlock,
    starProjection_complexifySubmodule_orthogonal, starProjection_complexifySubmodule,
    complexify_comp, complexify_comp]

/-! ### The three ambient theorems over a real Hilbert space -/

variable {A H T B : E →L[ℝ] E} {U V : Submodule ℝ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, the whole-space `tan Θ` theorem over a REAL Hilbert
space, for every source unitarily invariant norm**: `δ ‖tan Θ‖ ≤ ‖H‖`, the
second conclusion of the Section 2 tangent theorem.

No dimension hypothesis, no compactness hypothesis; `[U.HasOrthogonalProjection]`
is the formal encoding of the paper's "closed subspace".  As in the complex
statement, uniform transversality `‖sin Θ‖ < 1` is assumed — that is what makes
`tan Θ` the tangent — and membership of `tan Θ` in the norm's ideal is
concluded. -/
theorem tanTheta_ambient_bounded_symmetricNorming_real_of_transversality
    (N : SymmetricNormingFunction)
    (hT : IsSelfAdjoint T) (hA : IsSelfAdjoint A)
    (hV : T.Reduces V) (hAU : ∀ x ∈ U, A x ∈ U)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : U, ⟪compressOperatorReal U T z, z⟫_ℝ ≤
      alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ)
    (htr : ‖sinAngleOperatorR U V‖ < 1)
    (hMem : N.Mem (T - A)) :
    N.Mem (tanAngleOperatorR U V) ∧
      delta * N.gauge (tanAngleOperatorR U V) ≤ N.gauge (T - A) := by
  have htrC : ‖sinAngleOperatorC (complexifySubmodule U)
      (complexifySubmodule V)‖ < 1 := by
    rwa [← complexify_sinAngleOperatorR U V, norm_complexify]
  have hMemC : N.Mem (complexify T - complexify A) := by
    rw [← complexify_sub]
    exact (SymmetricNormingFunction.mem_complexify_iff N (T - A)).2 hMem
  obtain ⟨hmemC, hboundC⟩ :=
    tanTheta_ambient_bounded_symmetricNorming_complex_of_transversality (E := RealComplexification E) N
      (T := complexify T) (A := complexify A)
      (U := complexifySubmodule U) (V := complexifySubmodule V)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
        ((complexify_isSelfAdjoint_iff T).2 hT))
      ((complexify_isSelfAdjoint_iff A).2 hA)
      ((complexify_reduces_iff T V).2 hV)
      (fun z hz => mapsTo_complexifySubmodule hAU hz)
      hdelta
      (fun z => re_inner_compressOperator_le U T hCompressionUpper z)
      (fun y hy => by
        rw [← complexifySubmodule_orthogonal V] at hy
        exact le_re_inner_of_mem_complexifySubmodule hUnwantedLower hy)
      htrC hMemC
  rw [← complexify_tanAngleOperatorR U V] at hmemC hboundC
  rw [← complexify_sub] at hboundC
  refine ⟨(SymmetricNormingFunction.mem_complexify_iff N _).1 hmemC, ?_⟩
  rwa [SymmetricNormingFunction.gauge_complexify,
    SymmetricNormingFunction.gauge_complexify] at hboundC

/-- **Davis--Kahan 1970, the whole-space `sin 2Θ` theorem over a REAL Hilbert
space, for every source unitarily invariant norm**: `δ ‖sin 2Θ‖ ≤ 2‖H‖`, the
second conclusion of the Section 2 `sin 2Θ` theorem and equation (7.5). -/
theorem sinTwoTheta_ambient_bounded_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperatorReal U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperatorReal Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    (hMem : N.Mem (B - A)) :
    N.Mem (sinTwoAngleOperatorR U V) ∧
      d * N.gauge (sinTwoAngleOperatorR U V) ≤ 2 * N.gauge (B - A) := by
  have hMemC : N.Mem (complexify B - complexify A) := by
    rw [← complexify_sub]
    exact (SymmetricNormingFunction.mem_complexify_iff N (B - A)).2 hMem
  obtain ⟨hmemC, hboundC⟩ :=
    sinTwoTheta_ambient_bounded_symmetricNorming_complex (E := RealComplexification E) N
      (A := complexify A) (B := complexify B)
      (U := complexifySubmodule U) (V := complexifySubmodule V)
      ((complexify_isSelfAdjoint_iff A).2 hA)
      ((complexify_isSelfAdjoint_iff B).2 hB)
      ((complexify_reduces_iff A U).2 hU)
      ((complexify_reduces_iff B V).2 hV)
      hd hab
      (fun r hr => by
        -- `realSpectrum` is `spectrum` over the *native* scalar field, so it is
        -- free of the real-algebra diamond that a bare `spectrum ℝ` rewrite
        -- would have to cross here.
        have hr' : r ∈ realSpectrum
            (compressOperator (complexifySubmodule U) (complexify A)) := hr
        rw [realSpectrum_compressOperator_complexifySubmodule U A rfl] at hr'
        exact hUspec hr')
      (fun r hr => by
        have hr' : r ∈ realSpectrum
            (compressOperator (complexifySubmodule U)ᗮ (complexify A)) := hr
        rw [realSpectrum_compressOperator_complexifySubmodule (E := E) Uᗮ A
          (W := (complexifySubmodule U)ᗮ)
          (complexifySubmodule_orthogonal U).symm] at hr'
        exact hUspec' r hr')
      hMemC
  rw [← complexify_sinTwoAngleOperatorR U V] at hmemC hboundC
  rw [← complexify_sub] at hboundC
  refine ⟨(SymmetricNormingFunction.mem_complexify_iff N _).1 hmemC, ?_⟩
  rwa [SymmetricNormingFunction.gauge_complexify,
    SymmetricNormingFunction.gauge_complexify] at hboundC

/-- A useful stronger-placement specialization of the whole-space `tan 2Θ`
theorem over a real Hilbert space.

This older endpoint assumes ordered form bounds on both the unperturbed `U`
blocks and the perturbed `V` blocks.  It is retained as reusable infrastructure;
the literal Section 2 source signature, which does **not** assume the `V`-block
placement, is `tanTwoTheta_ambient_bounded_spectralGap_symmetricNorming_real` below. -/
theorem tanTwoTheta_ambient_bounded_orderedForm_symmetricNorming_real
    (N : SymmetricNormingFunction) {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hUperpLow : ∀ x ∈ Uᗮ, ⟪A x, x⟫_ℝ ≤ a * ‖x‖ ^ 2)
    (hVhigh : ∀ x ∈ V, b * ‖x‖ ^ 2 ≤ ⟪(A + H) x, x⟫_ℝ)
    (hVperpLow : ∀ x ∈ Vᗮ, ⟪(A + H) x, x⟫_ℝ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hHmem : N.Mem H) :
    N.Mem (tanTwoAngleOperatorR U V) ∧
      (b - a) * N.gauge (tanTwoAngleOperatorR U V) ≤ 2 * N.gauge H := by
  have hsum : complexify A + complexify H = complexify (A + H) :=
    (complexify_add A H).symm
  obtain ⟨hmemC, hboundC⟩ :=
    tanTwoTheta_ambient_bounded_orderedForm_symmetricNorming_complex (E := RealComplexification E) N
      (A := complexify A) (H := complexify H)
      (U := complexifySubmodule U) (V := complexifySubmodule V)
      ((complexify_isSelfAdjoint_iff A).2 hA)
      ((complexify_isSelfAdjoint_iff H).2 hH)
      (fun z hz => mapsTo_complexifySubmodule hAU hz)
      (fun z hz => by
        rw [hsum]
        exact mapsTo_complexifySubmodule hAplusH_V hz)
      hab
      (fun z hz => le_re_inner_of_mem_complexifySubmodule hUhigh hz)
      (fun z hz => by
        rw [← complexifySubmodule_orthogonal U] at hz
        exact re_inner_le_of_mem_complexifySubmodule hUperpLow hz)
      (fun z hz => by
        rw [hsum]
        exact le_re_inner_of_mem_complexifySubmodule hVhigh hz)
      (fun z hz => by
        rw [← complexifySubmodule_orthogonal V] at hz
        rw [hsum]
        exact re_inner_le_of_mem_complexifySubmodule hVperpLow hz)
      (fun z hz => mapsTo_orthogonal_complexifySubmodule U hHU hz)
      (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule U hHUperp hz)
      ((SymmetricNormingFunction.mem_complexify_iff N H).2 hHmem)
  rw [← complexify_tanTwoAngleOperatorR U V] at hmemC hboundC
  refine ⟨(SymmetricNormingFunction.mem_complexify_iff N _).1 hmemC, ?_⟩
  rwa [SymmetricNormingFunction.gauge_complexify,
    SymmetricNormingFunction.gauge_complexify] at hboundC

/-- **Davis--Kahan 1970, Section 2 `tan 2Θ₀`, directed residual
conclusion over a REAL Hilbert space, exactly from the printed hypotheses.**

This is the real-scalar counterpart of
`tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_symmetricNorming_complex`.  It assumes only the
paper's interval/half-line separation for the two blocks of `A`, positivity of
`δ`, `H₀ = H₁ = 0`, and invariance of the comparison subspace for `A+H`.
There is no quarter-angle branch, no caller-supplied pole exclusion, and no
spectral-placement hypothesis on the `A+H` blocks.

The left side uses `tanTwoDirectedCornerR`, the same canonical
complexification convention already used for the paper's real directed angle.
The residual norm on the right is genuinely real. -/
theorem tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_symmetricNorming_real
    (N : SymmetricNormingFunction)
    {A H : E →L[ℝ] E} {U V : Submodule ℝ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {β α δ : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperatorReal U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperatorReal Uᗮ A) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hRmem : N.Mem (projectionBlock Uᗮ U H)) :
    N.Mem (tanTwoDirectedCornerR U V) ∧
      δ * N.gauge (tanTwoDirectedCornerR U V) ≤
        2 * N.gauge (projectionBlock Uᗮ U H) := by
  have hsum : complexify A + complexify H = complexify (A + H) :=
    (complexify_add A H).symm
  have hRblock :
      projectionBlock (complexifySubmodule U)ᗮ (complexifySubmodule U)
          (complexify H) =
        complexify (projectionBlock Uᗮ U H) :=
    projectionBlock_complexifySubmodule_real U H
  have hRmemC : N.Mem
      (projectionBlock (complexifySubmodule U)ᗮ (complexifySubmodule U)
        (complexify H)) := by
    rw [hRblock]
    exact (SymmetricNormingFunction.mem_complexify_iff N _).2 hRmem
  obtain ⟨hmemC, hboundC⟩ :=
    tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_symmetricNorming_complex
      (E := RealComplexification E) N
      (A := complexify A) (H := complexify H)
      (U := complexifySubmodule U) (V := complexifySubmodule V)
      ((complexify_isSelfAdjoint_iff A).2 hA)
      ((complexify_isSelfAdjoint_iff H).2 hH)
      (fun z hz => mapsTo_complexifySubmodule hAU hz)
      (fun z hz => by
        rw [hsum]
        exact mapsTo_complexifySubmodule hAplusH_V hz)
      hδ
      (fun r hr => by
        have hr' : r ∈ realSpectrum
            (compressOperator (complexifySubmodule U) (complexify A)) := hr
        rw [realSpectrum_compressOperator_complexifySubmodule U A rfl] at hr'
        exact hA0spec hr')
      (fun r hr => by
        have hr' : r ∈ realSpectrum
            (compressOperator (complexifySubmodule U)ᗮ (complexify A)) := hr
        rw [realSpectrum_compressOperator_complexifySubmodule (E := E) Uᗮ A
          (W := (complexifySubmodule U)ᗮ)
          (complexifySubmodule_orthogonal U).symm] at hr'
        exact hA1spec hr')
      (fun z hz => mapsTo_orthogonal_complexifySubmodule U hHU hz)
      (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule U hHUperp hz)
      hRmemC
  change N.Mem (tanTwoDirectedCornerR U V) at hmemC
  change δ * N.gauge (tanTwoDirectedCornerR U V) ≤
      2 * N.gauge
        (projectionBlock (complexifySubmodule U)ᗮ (complexifySubmodule U)
          (complexify H)) at hboundC
  rw [hRblock, SymmetricNormingFunction.gauge_complexify] at hboundC
  exact ⟨hmemC, hboundC⟩

/-- **Davis--Kahan 1970, Section 2 `tan 2Θ`, ambient conclusion over a REAL
Hilbert space, exactly from the printed hypotheses.**

This is the real-scalar counterpart of
`tanTwoTheta_ambient_bounded_spectralGap_symmetricNorming_complex`.  In particular it assumes only the
paper's interval/half-line separation for the two blocks of `A`, positivity of
`δ`, `H₀ = H₁ = 0`, and invariance of the comparison subspace for `A+H`.
There is no quarter-angle branch, no pole-exclusion hypothesis, and no
spectral-placement hypothesis for the blocks of `A+H`. -/
theorem tanTwoTheta_ambient_bounded_spectralGap_symmetricNorming_real
    (N : SymmetricNormingFunction)
    {β α δ : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperatorReal U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperatorReal Uᗮ A) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hHmem : N.Mem H) :
    N.Mem (tanTwoAngleOperatorR U V) ∧
      δ * N.gauge (tanTwoAngleOperatorR U V) ≤ 2 * N.gauge H := by
  have hsum : complexify A + complexify H = complexify (A + H) :=
    (complexify_add A H).symm
  -- Keep these spectrum transports inline.  On a complex operator there are
  -- multiple elaboration paths for `spectrum ℝ`; the expected argument type of
  -- the complex theorem selects the native `realSpectrum` path, avoiding the
  -- real-algebra diamond (as in `sinTwoTheta_ambient_bounded_symmetricNorming_real`).
  obtain ⟨hmemC, hboundC⟩ :=
    tanTwoTheta_ambient_bounded_spectralGap_symmetricNorming_complex (E := RealComplexification E) N
      (A := complexify A) (H := complexify H)
      (U := complexifySubmodule U) (V := complexifySubmodule V)
      ((complexify_isSelfAdjoint_iff A).2 hA)
      ((complexify_isSelfAdjoint_iff H).2 hH)
      (fun z hz => mapsTo_complexifySubmodule hAU hz)
      (fun z hz => by
        rw [hsum]
        exact mapsTo_complexifySubmodule hAplusH_V hz)
      hδ
      (fun r hr => by
        have hr' : r ∈ realSpectrum
            (compressOperator (complexifySubmodule U) (complexify A)) := hr
        rw [realSpectrum_compressOperator_complexifySubmodule U A rfl] at hr'
        exact hA0spec hr')
      (fun r hr => by
        have hr' : r ∈ realSpectrum
            (compressOperator (complexifySubmodule U)ᗮ (complexify A)) := hr
        rw [realSpectrum_compressOperator_complexifySubmodule (E := E) Uᗮ A
          (W := (complexifySubmodule U)ᗮ)
          (complexifySubmodule_orthogonal U).symm] at hr'
        exact hA1spec hr')
      (fun z hz => mapsTo_orthogonal_complexifySubmodule U hHU hz)
      (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule U hHUperp hz)
      ((SymmetricNormingFunction.mem_complexify_iff N H).2 hHmem)
  rw [← complexify_tanTwoAngleOperatorR U V] at hmemC hboundC
  refine ⟨(SymmetricNormingFunction.mem_complexify_iff N _).1 hmemC, ?_⟩
  rwa [SymmetricNormingFunction.gauge_complexify,
    SymmetricNormingFunction.gauge_complexify] at hboundC

end

end DavisKahan1970
end TauCeti
