/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.5 Thinking
-/
module


public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.UnitarilyInvariant
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation

/-!
# Prose-like wrappers for the finite Davis--Kahan `sin Θ` theorem

This file is intentionally additive.  It does not replace the current proof
primitive or the stable `PartIII` facade.  Instead it experiments with a
prose-facing layer whose statements are closer to the way Davis--Kahan is
usually quoted:

`‖sin Θ‖ ≤ ‖S - T‖ / gap`.

The existing primitive exposes the proof-critical ingredients explicitly:
orthogonal projections, invariant subspaces, and quadratic-form gap bounds.
Here we give names to the two pieces that make the statement look unlike the
paper:

* `directedSinThetaOperatorProseLike U V` abbreviates `P_V ∘ P_U`, the directed
  sine/leakage operator.
* `AboveBelowGapProseLike T S U V c g` packages the self-adjointness,
  invariance, positivity of the gap, and quadratic-form separation hypotheses.

The suffix `ProseLike` is deliberate: these names are exploratory wrappers for
readability while the final public API shape is still being refined.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- The directed sine-of-angle operator, in prose-like Davis--Kahan notation.

For `x ∈ U`, this applies the orthogonal projection onto `V`.  Thus its
singular values measure how much `U` leaks into the forbidden/complementary
subspace `V`.  In the Part III `sin Θ` theorem, this is the formal object behind
`sin Θ`; the direction matters because `V` is usually the opposite spectral
subspace rather than the matching one. -/
noncomputable def directedSinThetaOperatorProseLike
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    E →L[𝕜] E :=
  V.starProjection ∘L U.starProjection

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- The prose-like directed sine-theta operator agrees with the canonical one. -/
@[simp]
theorem directedSinThetaOperatorProseLike_apply
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (x : E) :
    directedSinThetaOperatorProseLike U V x = V.starProjection (U.starProjection x) :=
  rfl

/-- Quadratic-form above/below gap hypotheses for the prose-like `sin Θ` API.

This packages the assumptions that the proof primitive needs.  Read it as:

* `T` and `S` are self-adjoint;
* `U` is a `T`-invariant high spectral subspace;
* `V` is an `S`-invariant low spectral subspace;
* the two sides are separated by the positive gap `g` around the cut `c`.

The fields use quadratic-form inequalities rather than explicit spectral sets,
which keeps this wrapper basis-free and independent of a particular spectral
projection construction. -/
structure AboveBelowGapProseLike (T S : E →ₗ[𝕜] E)
    (U V : Submodule 𝕜 E) (c g : ℝ) : Prop where
  T_symm : T.IsSymmetric
  S_symm : S.IsSymmetric
  U_inv : ∀ x ∈ U, T x ∈ U
  V_inv : ∀ x ∈ V, S x ∈ V
  gap_pos : 0 < g
  U_above : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜
  V_below : ∀ x ∈ V, RCLike.re ⟪S x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2

/-- Prose-like Davis--Kahan Part III `sin Θ` theorem in every unitarily
invariant norm.

This is a thin wrapper around the canonical finite UI-norm sine theorem.
The mathematical content is unchanged, but the statement now visibly has the
shape

`N (sin Θ) ≤ N (S - T) / gap`,

with the directed `sin Θ` operator and the gap hypotheses named explicitly. -/
theorem partIII_sinTheta_uiNorm_prose_like
    (N : UnitarilyInvariantSeminorm 𝕜 E E) {T S : E →ₗ[𝕜] E}
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {c g : ℝ} (hgap : AboveBelowGapProseLike T S U V c g) :
    N ((directedSinThetaOperatorProseLike U V : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / g := by
  exact UnitarilyInvariantSeminorm.apply_starProjection_comp_starProjection_le N
    hgap.T_symm hgap.S_symm hgap.U_inv hgap.V_inv hgap.gap_pos
    hgap.U_above hgap.V_below

/-- Spectral-set version of the prose-like above/below gap hypotheses.

This version is closer to the paper's prose: `U` carries the part of the
spectrum of `T` above `c + g`, while `V` carries the part of the spectrum of `S`
below `c`.  It is still directional: the theorem bounds the leakage from `U`
into `V`. -/
structure AboveBelowSpectralGapProseLike (T S : E →ₗ[𝕜] E)
    (U V : Submodule 𝕜 E) (c g : ℝ) : Prop where
  T_symm : T.IsSymmetric
  S_symm : S.IsSymmetric
  U_reduces : IsInvariant T U
  V_reduces : IsInvariant S V
  gap_pos : 0 < g
  U_spectrum : PointSpectrumIn T U (Set.Ici (c + g))
  V_spectrum : PointSpectrumIn S V (Set.Iic c)

omit [CompleteSpace E] in
/-- Spectral-hypothesis prose-like Davis--Kahan Part III `sin Θ` theorem.

This wrapper is one layer closer to the paper statement than
`partIII_sinTheta_uiNorm_prose_like`: the above/below assumptions are stated as
spectral containment hypotheses, then discharged by the existing spectral
coercivity bridge. -/
theorem partIII_sinTheta_uiNorm_spectral_prose_like
    (N : UnitarilyInvariantSeminorm 𝕜 E E) {T S : E →ₗ[𝕜] E}
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {c g : ℝ} (hgap : AboveBelowSpectralGapProseLike T S U V c g) :
    N ((directedSinThetaOperatorProseLike U V : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / g := by
  exact uiNorm_directed_sinTheta_le N hgap.T_symm hgap.S_symm hgap.U_reduces
    hgap.V_reduces hgap.gap_pos hgap.U_spectrum hgap.V_spectrum

/-- Canonical spectral-subspace gap hypotheses for the prose-like `sin Θ` API.

The parameters `s` and `t` name the selected spectral sets.  The theorem below
uses the canonical spectral subspaces associated to those sets, so callers do
not need to mention invariant subspaces or reductions explicitly. -/
structure CanonicalSpectralGapProseLike (T S : E →ₗ[𝕜] E)
    (s t : Set ℝ) (c g : ℝ) : Prop where
  T_symm : T.IsSymmetric
  S_symm : S.IsSymmetric
  gap_pos : 0 < g
  U_spectrum : PointSpectrumIn T (pointSpectralSubspace T s) (Set.Ici (c + g))
  V_spectrum : PointSpectrumIn S (pointSpectralSubspace S t) (Set.Iic c)

omit [CompleteSpace E] in
/-- Canonical spectral-subspace prose-like Davis--Kahan Part III `sin Θ`
theorem.

This is the most paper-like wrapper in this file: choose spectral sets `s` and
`t`, assume they are separated by the above/below gap encoded in `hgap`, and
obtain the usual `‖sin Θ‖ ≤ ‖S - T‖ / g` estimate for every unitarily invariant
norm. -/
theorem partIII_sinTheta_uiNorm_canonical_spectral_prose_like
    (N : UnitarilyInvariantSeminorm 𝕜 E E) {T S : E →ₗ[𝕜] E}
    {s t : Set ℝ} {c g : ℝ} (hgap : CanonicalSpectralGapProseLike T S s t c g) :
    N ((directedSinThetaOperatorProseLike (pointSpectralSubspace T s) (pointSpectralSubspace S t) :
        E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / g := by
  exact uiNorm_pointSpectralSubspace_directed_sinTheta_le N hgap.T_symm hgap.S_symm
    hgap.gap_pos hgap.U_spectrum hgap.V_spectrum

end DavisKahan.FiniteDimensional
end TauCeti
