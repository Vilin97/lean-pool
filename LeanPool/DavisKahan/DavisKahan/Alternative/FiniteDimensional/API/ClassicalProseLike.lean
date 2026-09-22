/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.5 Thinking
-/

import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.UnitarilyInvariant
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DoubleAngle.SinTheta
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.TanTheta.Vector
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DoubleAngle.TanTheta

/-!
# Prose-like wrappers for the finite Davis--Kahan classical API

This file is intentionally additive.  It does not replace the current proof
primitives or the stable `PartIII` facade.  Instead it experiments with a
paper-facing layer whose statements are closer to the way the classical
finite Davis--Kahan theorems are quoted:

* `‖sin Θ‖ ≤ ‖S - T‖ / gap`,
* `‖sin 2Θ‖ ≤ 2 ‖S - T‖ / gap`,
* `tan Θ ≤ residual / gap`,
* `tan 2Θ ≤ 2 perturbation / gap`,
* `‖P_U - P_V‖ ≤ perturbation / gap`.

The suffix `ClassicalProseLike` is deliberate.  These names are exploratory
wrappers for readability while the final public API shape is still being
refined.  The mathematical content is supplied by the canonical theorem
declarations underlying the proved Part III facade.

The definitions in this file avoid the speculative angle-operator constructors
from `DavisKahan.FiniteDimensional.Core.AngleOperators`
whose full spectral-functional-calculus interpretations remain open work.
For the two sine theorems we name the actual projection products used by the
proved theorems.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-! ## Prose-like angle and projection operators -/

/-- The directed sine-of-angle operator used by the Part III `sin Θ` theorem.

For `x ∈ U`, this applies the orthogonal projection onto `V`.  Thus its
singular values measure how much `U` leaks into the forbidden/complementary
subspace `V`.  In Davis--Kahan sine theorems, `V` is usually the opposite
spectral subspace of the perturbed operator, so this is the formal object
behind the prose notation `sin Θ`.
-/
noncomputable def directedSinThetaOperatorClassicalProseLike
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    E →L[𝕜] E :=
  V.starProjection ∘L U.starProjection

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- The prose-like directed sine-theta operator agrees with the canonical one. -/
@[simp]
theorem directedSinThetaOperatorClassicalProseLike_apply
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (x : E) :
    directedSinThetaOperatorClassicalProseLike U V x =
      V.starProjection (U.starProjection x) :=
  rfl

/-- The one-sided half-`sin 2Θ` operator used by the proved finite `sin 2Θ`
theorem.

The classical source theorem is usually written for `sin 2Θ`.  The proved
Lean theorem controls the normalized cross block
`P_{Uᗮ} P_V P_U`, whose nonzero singular values are one half of the corresponding
`sin 2Θ` singular values.  This name keeps that normalization explicit rather
than hiding a factor of two.
-/
noncomputable def directedHalfSinTwoThetaOperatorClassicalProseLike
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    E →L[𝕜] E :=
  (Uᗮ.starProjection ∘L V.starProjection) ∘L U.starProjection

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- The prose-like directed half-sine-two-theta operator agrees with the canonical one. -/
@[simp]
theorem directedHalfSinTwoThetaOperatorClassicalProseLike_apply
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (x : E) :
    directedHalfSinTwoThetaOperatorClassicalProseLike U V x =
      Uᗮ.starProjection (V.starProjection (U.starProjection x)) :=
  rfl

/-- Projector difference operator for the sharp finite projector theorem. -/
noncomputable def projectorDifferenceOperatorClassicalProseLike
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    E →L[𝕜] E :=
  U.starProjection - V.starProjection

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- The prose-like projector-difference operator agrees with the canonical one. -/
@[simp]
theorem projectorDifferenceOperatorClassicalProseLike_apply
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (x : E) :
    projectorDifferenceOperatorClassicalProseLike U V x =
      U.starProjection x - V.starProjection x :=
  rfl

/-! ## `sin Θ` -/

/-- Above/below spectral-gap hypotheses for the prose-like `sin Θ` API.

Read this as: `U` is a high `T` subspace, `V` is a low `S` subspace, and the two
sides are separated by the positive gap `g` around the cut `c`.
-/
structure SinThetaGapClassicalProseLike (T S : E →ₗ[𝕜] E)
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

This is a thin wrapper around the canonical finite UI-norm sine theorem; its
conclusion visibly has the paper shape `N (sin Θ) ≤ N (S - T) / gap`.
-/
theorem partIII_sinTheta_uiNorm_classical_prose_like
    (N : UnitarilyInvariantSeminorm 𝕜 E E) {T S : E →ₗ[𝕜] E}
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {c g : ℝ} (hgap : SinThetaGapClassicalProseLike T S U V c g) :
    N ((directedSinThetaOperatorClassicalProseLike U V : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / g := by
  exact UnitarilyInvariantSeminorm.apply_starProjection_comp_starProjection_le N
    hgap.T_symm hgap.S_symm hgap.U_inv hgap.V_inv hgap.gap_pos
    hgap.U_above hgap.V_below

/-! ## `sin 2Θ` -/

/-- Split-gap hypotheses for the prose-like `sin 2Θ` API.

The reference operator `T` has a two-block form gap across `U ⊕ Uᗮ`; `V` is an
`S`-invariant comparison subspace.  This is the hypothesis shape used by the
proved every-UI-norm `sin 2Θ` theorem.
-/
structure SinTwoThetaGapClassicalProseLike (T S : E →ₗ[𝕜] E)
    (U V : Submodule 𝕜 E) (a b : ℝ) : Prop where
  T_symm : T.IsSymmetric
  S_symm : S.IsSymmetric
  U_inv : ∀ x ∈ U, T x ∈ U
  V_inv : ∀ x ∈ V, S x ∈ V
  gap_pos : a < b
  U_above : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜
  Uperp_below : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2

/-- Prose-like Davis--Kahan Part III `sin 2Θ` theorem in every unitarily
invariant norm, stated for the normalized half-`sin 2Θ` cross block.

Equivalently, after multiplying the left side by two, this is the classical
source shape `‖sin 2Θ‖ ≤ 2 ‖S - T‖ / gap`.
-/
theorem partIII_half_sinTwoTheta_uiNorm_classical_prose_like
    (N : UnitarilyInvariantSeminorm 𝕜 E E) {T S : E →ₗ[𝕜] E}
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ} (hgap : SinTwoThetaGapClassicalProseLike T S U V a b) :
    N ((directedHalfSinTwoThetaOperatorClassicalProseLike U V : E →L[𝕜] E) :
        E →ₗ[𝕜] E)
      ≤ N (S - T) / (b - a) := by
  exact UnitarilyInvariantSeminorm.sin_two_theta_starProjection_le N
    hgap.T_symm hgap.S_symm hgap.U_inv hgap.V_inv hgap.gap_pos
    hgap.U_above hgap.Uperp_below

/-! ## `tan Θ` -/

/-- Pole-free prose-like hypotheses for the source-faithful finite `tan Θ`
theorem.

`Z` is the trial/test subspace and `V` is the exact invariant subspace.  The
conclusion keeps the tangent pole out of the statement by comparing the
orthogonal and projected parts of each `x ∈ Z`.
-/
structure TanThetaVectorGapClassicalProseLike (T : E →ₗ[𝕜] E)
    (Z V : Submodule 𝕜 E) (α β δ ρ : ℝ) : Prop where
  T_symm : T.IsSymmetric
  V_inv : ∀ x ∈ V, T x ∈ V
  strip_order : α ≤ β
  gap_pos : 0 < δ
  residual_nonneg : 0 ≤ ρ
  Z_outside_strip : ∀ x ∈ Z, ((β - α) / 2 + δ) * ‖x‖
    ≤ ‖Z.starProjection (T x) - (((α + β) / 2 : ℝ) : 𝕜) • x‖
  Vperp_lower : ∀ x ∈ Vᗮ, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜
  Vperp_upper : ∀ x ∈ Vᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ β * ‖x‖ ^ 2
  residual_bound : ∀ x ∈ Z, ‖T x - Z.starProjection (T x)‖ ≤ ρ * ‖x‖

omit [CompleteSpace E] in
/-- Prose-like Davis--Kahan Part III `tan Θ` theorem in the currently proved
pole-free vector form.

The conclusion is the vector version of `tan Θ ≤ residual / gap`:
`δ ‖x - P_V x‖ ≤ ρ ‖P_V x‖` for every vector in the trial subspace `Z`.
-/
theorem partIII_tanTheta_vector_classical_prose_like
    {T : E →ₗ[𝕜] E} {Z V : Submodule 𝕜 E}
     [V.HasOrthogonalProjection]
    {α β δ ρ : ℝ} (hgap : TanThetaVectorGapClassicalProseLike T Z V α β δ ρ) :
    ∀ x ∈ Z, δ * ‖x - V.starProjection x‖ ≤ ρ * ‖V.starProjection x‖ := by
  exact TauCeti.tan_theta_le hgap.T_symm hgap.V_inv hgap.strip_order
    hgap.gap_pos hgap.residual_nonneg hgap.Z_outside_strip hgap.Vperp_lower
    hgap.Vperp_upper hgap.residual_bound

/-! ## `tan 2Θ` -/

/-- Source-faithful finite `tan 2Θ` hypotheses.

The perturbation `S - T` is off-diagonal with respect to the reference split
`U ⊕ Uᗮ`, and both `T` and `S` satisfy the same high/low form gap across their
respective subspaces.  The conclusion is the sharp operator-norm branch theorem.
-/
structure TanTwoThetaGapClassicalProseLike (T S : E →ₗ[𝕜] E)
    (U V : Submodule 𝕜 E) (a b ε : ℝ) : Prop where
  T_symm : T.IsSymmetric
  S_symm : S.IsSymmetric
  U_inv : ∀ x ∈ U, T x ∈ U
  V_inv : ∀ x ∈ V, S x ∈ V
  split_pos : a < b
  perturbation_nonneg : 0 ≤ ε
  U_above : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜
  Uperp_below : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2
  V_above : ∀ x ∈ V, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪S x, x⟫_𝕜
  Vperp_below : ∀ x ∈ Vᗮ, RCLike.re ⟪S x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2
  offdiag_U : ∀ x ∈ U, ∀ y ∈ U, ⟪x, (S - T) y⟫_𝕜 = 0
  offdiag_Uperp : ∀ x ∈ Uᗮ, ∀ y ∈ Uᗮ, ⟪x, (S - T) y⟫_𝕜 = 0
  perturbation_bound : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖

omit [CompleteSpace E] in
/-- Prose-like Davis--Kahan Part III `tan 2Θ` theorem in the proved sharp
operator-norm form.

The first conjunct is the strict quarter-turn conclusion.  The second conjunct
is the pole-free algebraic form of `tan 2Θ ≤ 2 ε / (b - a)`.
-/
theorem partIII_tanTwoTheta_opNorm_classical_prose_like
    {T S : E →ₗ[𝕜] E} {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b ε : ℝ} (hgap : TanTwoThetaGapClassicalProseLike T S U V a b ε) :
    ‖projectorDifferenceOperatorClassicalProseLike U V‖ ^ 2 < 1 / 2 ∧
      (b - a) * (2 * ‖projectorDifferenceOperatorClassicalProseLike U V‖
          * Real.sqrt (1 - ‖projectorDifferenceOperatorClassicalProseLike U V‖ ^ 2))
        ≤ 2 * ε * (1 - 2 * ‖projectorDifferenceOperatorClassicalProseLike U V‖ ^ 2) := by
  exact TauCeti.tan_two_theta_norm_sub_le hgap.T_symm hgap.S_symm
    hgap.U_inv hgap.V_inv hgap.split_pos hgap.perturbation_nonneg
    hgap.U_above hgap.Uperp_below hgap.V_above hgap.Vperp_below
    hgap.offdiag_U hgap.offdiag_Uperp hgap.perturbation_bound

/-! ## Sharp projector-difference theorem -/

/-- Two-sided spectral-gap hypotheses for the sharp projector-difference theorem
in reducing-subspace form.

This packages the factor-one finite projector theorem as
`‖P_U - P_W‖ ≤ ε / g`.
-/
structure ProjectorDifferenceGapClassicalProseLike (A B : E →ₗ[𝕜] E)
    (U W : Submodule 𝕜 E) (c g ε : ℝ) : Prop where
  A_symm : A.IsSymmetric
  B_symm : B.IsSymmetric
  U_reduces : IsInvariant A U
  W_reduces : IsInvariant B W
  gap_pos : 0 < g
  U_high : PointSpectrumIn A U (Set.Ici (c + g))
  Uperp_low : PointSpectrumIn A Uᗮ (Set.Iic c)
  W_high : PointSpectrumIn B W (Set.Ici (c + g))
  Wperp_low : PointSpectrumIn B Wᗮ (Set.Iic c)
  perturbation_nonneg : 0 ≤ ε
  perturbation_bound : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖

omit [CompleteSpace E] in
/-- Prose-like sharp finite projector-difference theorem.

This is a thin wrapper around `projector_difference_opNorm` with all spectral
and perturbation hypotheses collected into one named object.
-/
theorem projector_difference_opNorm_classical_prose_like
    {A B : E →ₗ[𝕜] E} {U W : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    {c g ε : ℝ} (hgap : ProjectorDifferenceGapClassicalProseLike A B U W c g ε) :
    ‖projectorDifferenceOperatorClassicalProseLike U W‖ ≤ ε / g := by
  exact opNorm_starProjection_sub_le hgap.A_symm hgap.B_symm
    hgap.U_reduces hgap.W_reduces hgap.gap_pos hgap.U_high
    hgap.Uperp_low hgap.W_high hgap.Wperp_low hgap.perturbation_nonneg
    hgap.perturbation_bound

/-- Canonical spectral-subspace hypotheses for the sharp projector-difference
theorem.

This is the prose-like wrapper closest to the usual paper language: choose the
selected spectral sets `s` and `t`, assume selected and complementary spectral
gaps, and bound the difference of the corresponding spectral projectors.
-/
structure CanonicalProjectorDifferenceGapClassicalProseLike (A B : E →ₗ[𝕜] E)
    (s t : Set ℝ) (c g ε : ℝ) : Prop where
  A_symm : A.IsSymmetric
  B_symm : B.IsSymmetric
  gap_pos : 0 < g
  A_high : PointSpectrumIn A (pointSpectralSubspace A s) (Set.Ici (c + g))
  Aperp_low : PointSpectrumIn A (pointSpectralSubspace A s)ᗮ (Set.Iic c)
  B_high : PointSpectrumIn B (pointSpectralSubspace B t) (Set.Ici (c + g))
  Bperp_low : PointSpectrumIn B (pointSpectralSubspace B t)ᗮ (Set.Iic c)
  perturbation_nonneg : 0 ≤ ε
  perturbation_bound : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖

omit [CompleteSpace E] in
/-- Prose-like sharp projector-difference theorem for canonical finite spectral
subspaces. -/
theorem spectralProjector_difference_opNorm_classical_prose_like
    {A B : E →ₗ[𝕜] E} {s t : Set ℝ} {c g ε : ℝ}
    (hgap : CanonicalProjectorDifferenceGapClassicalProseLike A B s t c g ε) :
    ‖projectorDifferenceOperatorClassicalProseLike
        (pointSpectralSubspace A s) (pointSpectralSubspace B t)‖ ≤ ε / g := by
  exact opNorm_pointSpectralSubspace_sub_le hgap.A_symm hgap.B_symm hgap.gap_pos
    hgap.A_high hgap.Aperp_low hgap.B_high hgap.Bperp_low
    hgap.perturbation_nonneg hgap.perturbation_bound

end DavisKahan.FiniteDimensional
end TauCeti
