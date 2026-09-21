/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaAmbient
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TanTwoThetaApproximatePair

/-! # Tan Two Theta Ambient Branch Free -/

open TauCeti.DavisKahan.Angle


/-!
# Branch-free ambient `tan 2Θ`: residual and assembly layer

This module isolates two pieces of the branch-free ambient half of the
Davis--Kahan Section 2 `tan 2Θ` theorem that do **not** require choosing the
quarter-angle branch.

First, the approximate-singular-pair argument is strengthened so its Ky Fan
right-hand side is the actual residual corner `P_{Uᗮ} H P_U`, rather than the
whole perturbation.  This is the sharp form needed before Lemma 6.1: using
`H` at the directed-corner stage costs another factor of two in the ambient
assembly.

Second, the final ambient Lemma-6.1 / Lemma-6.2 assembly is factored away from
the quarter-acute construction.  It accepts an arbitrary self-adjoint
branch-free self-adjoint symbol `K` whose complementary off-diagonal pair has
the same Ky Fan data as the actual ambient `tanTwoAngleOperatorC`, together
with the sharp residual estimate for one corner, and proves the printed ambient
Ky Fan and source UI-norm conclusions.

Thus the genuinely hard remaining lemma has a narrow interface: construct the
**actual** branch-free corner/representative and discharge its residual Ky Fan
estimate.  In particular, this module never assumes that the nonmonotone graph
transform `4x/(1-x)^2` preserves approximation-number order across `x = 1`.
-/

namespace TauCeti
namespace DavisKahan.TanTwoTheta

open TauCeti.DavisKahanExt

open TauCeti.DavisKahan.ExactSinTheta


open scoped InnerProductSpace
open DavisKahan.ExactSinTheta

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-! ## Residual form of the approximate-pair estimate -/

/-- The ambient realization of the residual corner from `U` to `Uᗮ`.

It remains an endomorphism of `E`, so the existing ambient Ky Fan variational
principle applies directly to the same orthonormal approximate-singular
families. -/
def branchFreeResidualCompression (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (H : E →L[𝕜] E) : E →L[𝕜] E :=
  Uᗮ.starProjection ∘L H ∘L U.starProjection

omit [CompleteSpace E] in
/-- On `U`, if `H` maps into `Uᗮ`, the residual compression acts exactly as
`H`. -/
theorem branchFreeResidualCompression_apply_of_mem
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (H : E →L[𝕜] E)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) {x : E} (hx : x ∈ U) :
    branchFreeResidualCompression U H x = H x := by
  simp only [branchFreeResidualCompression, ContinuousLinearMap.comp_apply]
  rw [Submodule.starProjection_eq_self_iff.mpr hx,
    Submodule.starProjection_eq_self_iff.mpr (hHU x hx)]

/-- **Residual form of the branch-free approximate-pair Ky Fan estimate.**

The scalar equation-(7.6) proof already pairs `H u` against `v` with
`u ∈ U` and `v ∈ Uᗮ`.  Under the fully off-diagonal hypothesis this is
literally the pairing against `P_{Uᗮ} H P_U`.  Reusing the existing magnitude
Ky Fan variational theorem with that compressed operator therefore keeps the
printed residual on the right without changing the pole argument. -/
theorem sum_absDoubleAngleTangent_le_of_approximatePairs_residual
    {A H T : E →L[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hab : a < b)
    {m : ℕ} {u v : Fin m → E} {t : Fin m → ℝ} {ε : ℝ}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (humem : ∀ i, u i ∈ U) (hvmem : ∀ i, v i ∈ Uᗮ)
    (ht0 : ∀ i, 0 ≤ t i) (hε1 : ε ≤ 1)
    (hTu : ∀ i, ‖T (u i) - ((t i : ℝ) : 𝕜) • v i‖ ≤ ε)
    (hTv : ∀ i, ‖ContinuousLinearMap.adjoint T (v i) -
      ((t i : ℝ) : 𝕜) • u i‖ ≤ ε)
    (hsmall : approximatePairErrorCoefficient A H T * ε ≤ (b - a) / 4) :
    (b - a) * ∑ i, absDoubleAngleTangent (t i) ≤
      2 * kyFanApproximationGauge m (branchFreeResidualCompression U H) +
        m * (branchFreeTangentErrorCoefficient A H T (b - a) * ε) := by
  classical
  set C : ℝ := branchFreeTangentErrorCoefficient A H T (b - a) with hC
  have hpair : ∀ i, ((b - a) * absDoubleAngleTangent (t i) - C * ε) / 2 ≤
      |RCLike.re ⟪v i, H (u i)⟫_𝕜| := by
    intro i
    have h := absDoubleAngleTangent_approximate_scalar hA hH hAU hHU hHUperp
      hTmem hUb hUa hinv hab (humem i) (hvmem i) (hu.norm_eq_one i)
      (hv.norm_eq_one i) (ht0 i) hε1 (hTu i) (hTv i) hsmall
    rw [← hC] at h
    linarith
  have hpairResidual : ∀ i,
      ((b - a) * absDoubleAngleTangent (t i) - C * ε) / 2 ≤
        |RCLike.re ⟪v i, branchFreeResidualCompression U H (u i)⟫_𝕜| := by
    intro i
    rw [branchFreeResidualCompression_apply_of_mem U H hHU (humem i)]
    exact hpair i
  have hvar := sum_abs_le_kyFanApproximationGauge_of_orthonormal
    (branchFreeResidualCompression U H) hv hu
    (t := fun i => ((b - a) * absDoubleAngleTangent (t i) - C * ε) / 2)
    hpairResidual
  have hsum :
      ∑ i : Fin m, ((b - a) * absDoubleAngleTangent (t i) - C * ε) / 2 =
        ((b - a) * ∑ i, absDoubleAngleTangent (t i) - m * (C * ε)) / 2 := by
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum] at hvar
  linarith

end
end DavisKahan.TanTwoTheta

namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-! ## Branch-independent ambient assembly -/

omit [CompleteSpace E] in
private theorem comp_eq_mul_branchFree (f g : E →L[ℂ] E) : f ∘L g = f * g := rfl

omit [CompleteSpace E] in
private theorem projectionBlock_lower_branchFree
    {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    (K : E →L[ℂ] E) :
    projectionBlock Uᗮ U K =
      (1 - U.starProjection) * K * U.starProjection := by
  rw [projectionBlock, Submodule.starProjection_orthogonal',
    comp_eq_mul_branchFree, comp_eq_mul_branchFree, mul_assoc]

omit [CompleteSpace E] in
private theorem projectionBlock_upper_branchFree
    {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    (K : E →L[ℂ] E) :
    projectionBlock Uᗮᗮ Uᗮ K =
      U.starProjection * K * (1 - U.starProjection) := by
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  rw [projectionBlock]
  simp only [hUperp, Submodule.starProjection_orthogonal', comp_eq_mul_branchFree]
  rw [mul_assoc]

private theorem kyFan_lowerBlock_eq_upperBlock_branchFree
    {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    (K : E →L[ℂ] E) (hK : IsSelfAdjoint K) (k : ℕ) :
    kyFanApproximationGauge k (projectionBlock Uᗮ U K) =
      kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ K) := by
  have hadj : projectionBlock Uᗮᗮ Uᗮ K =
      (projectionBlock Uᗮ U K).adjoint := by
    rw [projectionBlock_upper_branchFree, projectionBlock_lower_branchFree]
    change _ = star _
    simp only [star_mul, star_sub, star_one,
      (isSelfAdjoint_starProjection U).star_eq, hK.star_eq]
    noncomm_ring
  rw [hadj, kyFanApproximationGauge_adjoint]

omit [CompleteSpace E] in
private theorem projectionBlock_smul_branchFree
    (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (c : ℂ) (K : E →L[ℂ] E) :
    projectionBlock Ω Γ (c • K) = c • projectionBlock Ω Γ K := by
  ext x
  simp [projectionBlock]

/-- **Branch-independent ambient assembly, Ky Fan form.**

This is exactly the final Lemma-6.1 / Lemma-6.2 part of the whole-space proof,
with the quarter-angle-specific construction abstracted into `K`, `hblockModulus`,
and `hcorner`.  `hblockModulus` deliberately identifies the ambient modulus with
the two complementary off-diagonal blocks of `K`; this is the exact bridge the
branch-free reflection construction must supply.  No branch or graph-coordinate
monotonicity assumption occurs here. -/
theorem tanTwoTheta_ambient_bounded_kyFan_complex_of_block
    {H K : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (hab : a < b)
    (hblockModulus : ∀ k : ℕ,
      kyFanApproximationGauge k (tanTwoAngleOperatorC U V) =
        kyFanApproximationGauge k (diagonalPair Uᗮ U K))
    (hcorner : ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k (projectionBlock Uᗮ U K) ≤
        2 * kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ H)) :
    ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k (tanTwoAngleOperatorC U V) ≤
        2 * kyFanApproximationGauge k H := by
  intro k
  have hd : (0 : ℝ) < (b - a) / 2 := by linarith
  have hcnorm : ‖((((b - a) / 2 : ℝ)) : ℂ)‖ = (b - a) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  have h₀ : ∀ j : ℕ,
      kyFanApproximationGauge j (projectionBlock Uᗮ U
          (((((b - a) / 2 : ℝ)) : ℂ) • K)) ≤
        kyFanApproximationGauge j (projectionBlock Uᗮ U H) := by
    intro j
    rw [projectionBlock_smul_branchFree, kyFanApproximationGauge_smul, hcnorm,
      kyFan_lowerBlock_eq_upperBlock_branchFree H hH j]
    linarith [hcorner j]
  have h₁ : ∀ j : ℕ,
      kyFanApproximationGauge j (projectionBlock Uᗮᗮ Uᗮ
          (((((b - a) / 2 : ℝ)) : ℂ) • K)) ≤
        kyFanApproximationGauge j (projectionBlock Uᗮᗮ Uᗮ H) := by
    intro j
    rw [projectionBlock_smul_branchFree, kyFanApproximationGauge_smul, hcnorm,
      ← kyFan_lowerBlock_eq_upperBlock_branchFree K hK j]
    linarith [hcorner j]
  have hcombine := lemma61_all_kyFan Uᗮ U
    (((((b - a) / 2 : ℝ)) : ℂ) • K)
    (((((b - a) / 2 : ℝ)) : ℂ) • K) H H h₀ h₁ k
  have hsum :
      projectionBlock Uᗮ U (((((b - a) / 2 : ℝ)) : ℂ) • K) +
        projectionBlock Uᗮᗮ Uᗮ (((((b - a) / 2 : ℝ)) : ℂ) • K) =
      ((((b - a) / 2 : ℝ)) : ℂ) • diagonalPair Uᗮ U K := by
    rw [diagonalPair, projectionBlock_smul_branchFree,
      projectionBlock_smul_branchFree, ← smul_add]
    rfl
  have hsumH :
      projectionBlock Uᗮ U H + projectionBlock Uᗮᗮ Uᗮ H =
        diagonalPair Uᗮ U H := rfl
  rw [hsum, hsumH, kyFanApproximationGauge_smul, hcnorm] at hcombine
  have hpinch := diagonalPair_all_kyFan_le Uᗮ U H k
  rw [hblockModulus k]
  linarith [hcombine.trans hpinch]

/-- **Branch-independent ambient assembly, source UI-norm form.** -/
theorem tanTwoTheta_ambient_bounded_symmetricNorming_complex_of_block
    (N : SymmetricNormingFunction)
    {H K : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (hab : a < b)
    (hblockModulus : ∀ k : ℕ,
      kyFanApproximationGauge k (tanTwoAngleOperatorC U V) =
        kyFanApproximationGauge k (diagonalPair Uᗮ U K))
    (hcorner : ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k (projectionBlock Uᗮ U K) ≤
        2 * kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ H))
    (hHmem : N.Mem H) :
    N.Mem (tanTwoAngleOperatorC U V) ∧
      (b - a) * N.gauge (tanTwoAngleOperatorC U V) ≤ 2 * N.gauge H := by
  have htwo : ‖((2 : ℝ) : ℂ)‖ = 2 := by norm_num
  have hd : (0 : ℝ) < b - a := by linarith
  have hscaled : ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k (tanTwoAngleOperatorC U V) ≤
        kyFanApproximationGauge k (((2 : ℝ) : ℂ) • H) := by
    intro k
    rw [kyFanApproximationGauge_smul, htwo]
    exact tanTwoTheta_ambient_bounded_kyFan_complex_of_block hH hK hab
      hblockModulus hcorner k
  have hMem2 : N.Mem (((2 : ℝ) : ℂ) • H) := by
    intro htop
    rw [N.extendedGauge_smul, htwo] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hHmem h
    · exact absurd h (by simp)
  obtain ⟨hmem, hle⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hd hMem2 hscaled
  refine ⟨hmem, ?_⟩
  rwa [N.gauge_smul _ hHmem, htwo] at hle

end
end DavisKahan1970
end TauCeti
