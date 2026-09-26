/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.TanTheta.UnboundedVector
public import LeanPool.DavisKahan.DavisKahan.TanTheta.Spectrum
public import LeanPool.DavisKahan.ForTauCeti.Analysis.CStarAlgebra.SelfAdjointGapInverse

/-!
# The unbounded tangent theorem with a genuine trial spectrum

This module packages a domain-contained trial subspace for a closed
self-adjoint operator.  The package records a bounded self-adjoint Ritz block,
its identification with the projected unbounded action, and a bounded residual
into the ambient Hilbert space.

An exterior spectral hypothesis on the Ritz block gives the test-side
coercivity required by the domain-aware vector theorem.  The residual operator
supplies the columnwise residual bound through its operator norm.  Combining
those two facts with the canonical interval spectral range of the exact
operator yields a genuine-spectrum unbounded tangent estimate.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace TanTheta


section ScalarGeneric

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A bounded Ritz block and residual for a trial subspace contained in the
operator domain.  The Ritz block is exactly the compression of the unbounded
operator to the trial subspace, and the residual is the complementary column.

The bundle is *bounded data*: nothing in it mentions the ambient operator except
through the two identities `operator_apply` and `residual_apply`.  It is
therefore scalar-generic, over a real or a complex Hilbert space alike. -/
structure BoundedCompressionTrialBlock
    (A : H →ₗ.[𝕜] H) (Z : Submodule 𝕜 H)
    [Z.HasOrthogonalProjection] [CompleteSpace Z] where
  domain_le : Z ≤ A.domain
  /-- The bounded self-adjoint compression of the ambient partial operator to the trial
  subspace. -/
  operator : Z →L[𝕜] Z
  operator_selfAdjoint : IsSelfAdjoint operator
  operator_apply (x : Z) :
    (operator x : H) =
      Z.starProjection
        (A ⟨(x : H), domain_le x.property⟩)
  /-- The bounded residual between the ambient operator and its trial-space compression. -/
  residual : Z →L[𝕜] H
  residual_apply (x : Z) :
    residual x =
      A ⟨(x : H), domain_le x.property⟩ -
        (operator x : H)

namespace BoundedCompressionTrialBlock

variable {A : H →ₗ.[𝕜] H}
  {Z : Submodule 𝕜 H} [Z.HasOrthogonalProjection] [CompleteSpace Z]

/-- The bundled residual is the part of the unbounded action orthogonal to the
trial subspace. -/
theorem residual_eq_sub_starProjection
    (D : BoundedCompressionTrialBlock A Z) (x : Z) :
    D.residual x =
      A ⟨(x : H), D.domain_le x.property⟩ -
        Z.starProjection
          (A ⟨(x : H), D.domain_le x.property⟩) := by
  rw [D.residual_apply, D.operator_apply]

/-- The bundled trial residual is orthogonal to the trial subspace. -/
theorem residual_mem_orthogonal
    (D : BoundedCompressionTrialBlock A Z) (x : Z) :
    D.residual x ∈ Zᗮ := by
  rw [D.residual_eq_sub_starProjection]
  exact Z.sub_starProjection_mem_orthogonal _

/-- The operator norm of the bundled residual supplies the columnwise bound
used by the vector tangent theorem. -/
theorem norm_sub_starProjection_le
    (D : BoundedCompressionTrialBlock A Z) (x : Z) :
    ‖A ⟨(x : H), D.domain_le x.property⟩ -
        Z.starProjection
          (A ⟨(x : H), D.domain_le x.property⟩)‖ ≤
      ‖D.residual‖ * ‖(x : H)‖ := by
  rw [← D.residual_eq_sub_starProjection]
  exact D.residual.le_opNorm x

end BoundedCompressionTrialBlock

end ScalarGeneric

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
/-- A bounded self-adjoint operator whose real spectrum avoids the enlarged
interval is coercive after centering at the interval midpoint. -/
theorem coercive_of_selfAdjoint_spectrum_exterior
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    {M : K →L[ℂ] K} (hM : IsSelfAdjoint M)
    {α β δ : ℝ} (hαβ : α ≤ β) (hδ : 0 < δ)
    (hspec : ∀ x ∈ spectrum ℝ M,
      x ≤ α - δ ∨ β + δ ≤ x) :
    ∀ x : K, ((β - α) / 2 + δ) * ‖x‖ ≤
      ‖M x - (((α + β) / 2 : ℝ) : ℂ) • x‖ := by
  have hrd : (0 : ℝ) < (β - α) / 2 + δ := by
    linarith
  set M₁ : K →L[ℂ] K := M -
    algebraMap ℝ (K →L[ℂ] K) ((α + β) / 2) with hM₁def
  have hM₁sa : IsSelfAdjoint M₁ := by
    rw [hM₁def]
    exact TauCeti.DavisKahanExt.isSelfAdjoint_sub_algebraMap hM _
  have hM₁spec : ∀ x ∈ spectrum ℝ M₁,
      (β - α) / 2 + δ ≤ |x| := by
    rw [hM₁def]
    exact TauCeti.DavisKahanExt.le_abs_of_spectrum_exterior hspec
  have hM₁unit : IsUnit M₁ :=
    TauCeti.isUnit_of_forall_le_abs (A := K →L[ℂ] K) hrd hM₁spec
  set J : K →L[ℂ] K := Ring.inverse M₁
  have hJleft : J * M₁ = 1 := Ring.inverse_mul_cancel _ hM₁unit
  have hJnorm : ‖J‖ ≤ ((β - α) / 2 + δ)⁻¹ :=
    TauCeti.IsSelfAdjoint.norm_ringInverse_le (A := K →L[ℂ] K) hM₁sa hrd hM₁spec
  intro x
  have hJx : J (M₁ x) = x := by
    exact DFunLike.congr_fun hJleft x
  have hcoer : ((β - α) / 2 + δ) * ‖x‖ ≤ ‖M₁ x‖ := by
    have hbound : ‖x‖ ≤ ((β - α) / 2 + δ)⁻¹ * ‖M₁ x‖ := by
      calc
        ‖x‖ = ‖J (M₁ x)‖ := by rw [hJx]
        _ ≤ ‖J‖ * ‖M₁ x‖ := J.le_opNorm _
        _ ≤ ((β - α) / 2 + δ)⁻¹ * ‖M₁ x‖ :=
          mul_le_mul_of_nonneg_right hJnorm (norm_nonneg _)
    calc
      ((β - α) / 2 + δ) * ‖x‖ ≤
          ((β - α) / 2 + δ) *
            (((β - α) / 2 + δ)⁻¹ * ‖M₁ x‖) :=
        mul_le_mul_of_nonneg_left hbound hrd.le
      _ = ‖M₁ x‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ hrd.ne', one_mul]
  calc
    ((β - α) / 2 + δ) * ‖x‖ ≤ ‖M₁ x‖ := hcoer
    _ = ‖M x - (((α + β) / 2 : ℝ) : ℂ) • x‖ := by
      rw [hM₁def, sub_apply, Algebra.algebraMap_eq_smul_one,
        smul_apply, one_apply_eq_self,
        RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl

/-- The unbounded tangent theorem with a genuine Ritz spectrum.

The exact complementary block is the canonical interval spectral range of
`A`.  The test subspace is represented by `D`; the spectrum of its bounded
self-adjoint Ritz block lies outside the enlarged interval.  The conclusion is
controlled directly by the operator norm of the bundled residual. -/
theorem tanTheta_unbounded_exactSpectralIcc_trialBlock
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z)
    {α β δ : ℝ} (hαβ : α ≤ β) (hδ : 0 < δ)
    (hZspec : ∀ x ∈ spectrum ℝ D.operator,
      x ≤ α - δ ∨ β + δ ≤ x) :
    let W := selfAdjointSpectralSubspace A hA (Set.Icc α β)
      measurableSet_Icc
    ∀ x : H, ∀ _hx : x ∈ Z,
      δ * ‖x - Wᗮ.starProjection x‖ ≤
        ‖D.residual‖ * ‖Wᗮ.starProjection x‖ := by
  let W := selfAdjointSpectralSubspace A hA (Set.Icc α β)
    measurableSet_Icc
  have hZcoercive : ∀ x : H, ∀ hx : x ∈ Z,
      ((β - α) / 2 + δ) * ‖x‖ ≤
        ‖Z.starProjection
              (A ⟨x, D.domain_le hx⟩) -
            (((α + β) / 2 : ℝ) : ℂ) • x‖ := by
    intro x hx
    let z : Z := ⟨x, hx⟩
    have hz := coercive_of_selfAdjoint_spectrum_exterior
      D.operator_selfAdjoint hαβ hδ hZspec z
    calc
      ((β - α) / 2 + δ) * ‖x‖ =
          ((β - α) / 2 + δ) * ‖z‖ := rfl
      _ ≤ ‖D.operator z - (((α + β) / 2 : ℝ) : ℂ) • z‖ := hz
      _ = ‖Z.starProjection
              (A ⟨x, D.domain_le hx⟩) -
            (((α + β) / 2 : ℝ) : ℂ) • x‖ := by
        change ‖(D.operator z : H) -
            (((α + β) / 2 : ℝ) : ℂ) • (z : H)‖ = _
        rw [D.operator_apply]
  have hρ : ∀ x : H, ∀ hx : x ∈ Z,
      ‖A ⟨x, D.domain_le hx⟩ -
          Z.starProjection (A ⟨x, D.domain_le hx⟩)‖ ≤
        ‖D.residual‖ * ‖x‖ := by
    intro x hx
    let z : Z := ⟨x, hx⟩
    have hz := D.norm_sub_starProjection_le z
    exact hz
  exact tanTheta_unbounded_exactSpectralIcc
    A hA hαβ hδ (norm_nonneg D.residual) D.domain_le hZcoercive hρ

end TanTheta
end DavisKahan
end TauCeti
