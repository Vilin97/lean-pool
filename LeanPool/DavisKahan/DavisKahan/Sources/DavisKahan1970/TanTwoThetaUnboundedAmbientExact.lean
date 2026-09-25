/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedExact
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedReducing
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.ProjectionBlocks
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngle
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotation
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TangentTransport
import LeanPool.DavisKahan.DavisKahan.TanTheta.RitzPair
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance

/-! # Tan Two Theta Unbounded Ambient Exact -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Exact source-facing unbounded ambient `tan 2Theta`

`TanTwoThetaUnboundedExact.lean` closes the difficult directed residual half of
Davis--Kahan's unbounded extension.  The ambient half needs no second spectral
argument.  It is the same block assembly as the bounded Section 7 proof:

* the reflection tangent is purely off diagonal and skew-adjoint;
* the self-adjoint perturbation is purely off diagonal by `H₀ = H₁ = 0`;
* the directed estimate therefore holds on both complementary corners; and
* Davis--Kahan Lemmas 6.1 and 6.2 assemble the two corners without changing the
  sharp factor `2`.

All spectral cutoffs and pole exclusion remain internal.  No quarter-angle
branch, finite-rank hypothesis, compactness hypothesis, or externally supplied
cutoff family occurs in the source-facing theorem below.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace
open Filter
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.ApproximationNumber
open scoped TauCeti.CompleteSubspace

section

universe u

variable {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G]

/-! ## Block bookkeeping -/

omit [CompleteSpace G] in
private theorem comp_eq_mul_unboundedAmbientExact (f g : G →L[ℂ] G) :
    f ∘L g = f * g := rfl

omit [CompleteSpace G] in
private theorem projectionBlock_lower_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection]
    (K : G →L[ℂ] G) :
    projectionBlock Uᗮ U K =
      (1 - U.starProjection) * K * U.starProjection := by
  rw [projectionBlock, Submodule.starProjection_orthogonal',
    comp_eq_mul_unboundedAmbientExact, comp_eq_mul_unboundedAmbientExact, mul_assoc]

omit [CompleteSpace G] in
private theorem projectionBlock_upper_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection]
    (K : G →L[ℂ] G) :
    projectionBlock Uᗮᗮ Uᗮ K =
      U.starProjection * K * (1 - U.starProjection) := by
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  rw [projectionBlock]
  simp only [hUperp, Submodule.starProjection_orthogonal',
    comp_eq_mul_unboundedAmbientExact]
  rw [mul_assoc]

omit [CompleteSpace G] in
private theorem projectionBlock_smul_unboundedAmbientExact
    (Ω Γ : Submodule ℂ G)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (c : ℂ) (K : G →L[ℂ] G) :
    projectionBlock Ω Γ (c • K) = c • projectionBlock Ω Γ K := by
  ext x
  simp [projectionBlock]

private theorem kyFan_upper_eq_lower_of_selfAdjoint_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection]
    (K : G →L[ℂ] G) (hK : IsSelfAdjoint K) (k : ℕ) :
    kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ K) =
      kyFanApproximationGauge k (projectionBlock Uᗮ U K) := by
  have hadj : projectionBlock Uᗮᗮ Uᗮ K =
      (projectionBlock Uᗮ U K).adjoint := by
    rw [projectionBlock_upper_unboundedAmbientExact,
      projectionBlock_lower_unboundedAmbientExact]
    change _ = star _
    simp only [star_mul, star_sub, star_one,
      (isSelfAdjoint_starProjection U).star_eq, hK.star_eq]
    noncomm_ring
  rw [hadj, kyFanApproximationGauge_adjoint]

private theorem kyFan_upper_eq_lower_of_skewAdjoint_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection]
    (K : G →L[ℂ] G) (hK : K.adjoint = -K) (k : ℕ) :
    kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ K) =
      kyFanApproximationGauge k (projectionBlock Uᗮ U K) := by
  have hadj : projectionBlock Uᗮᗮ Uᗮ K =
      -(projectionBlock Uᗮ U K).adjoint := by
    rw [projectionBlock_upper_unboundedAmbientExact,
      projectionBlock_lower_unboundedAmbientExact]
    change _ = -star _
    have hKstar : star K = -K := by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact hK
    simp only [star_mul, star_sub, star_one,
      (isSelfAdjoint_starProjection U).star_eq, hKstar]
    noncomm_ring
  rw [hadj, kyFanApproximationGauge_neg, kyFanApproximationGauge_adjoint]

omit [CompleteSpace G] in
private theorem diagonalPart_eq_zero_of_isOddFor_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection] {K : G →L[ℂ] G}
    (hK : TauCeti.IsOddFor U K) : U.diagonalPart K = 0 := by
  ext x
  rw [Submodule.diagonalPart_apply]
  have hlow : K (U.starProjection x) ∈ Uᗮ :=
    hK.1 _ (U.starProjection_apply_mem x)
  have hupp : K (Uᗮ.starProjection x) ∈ U :=
    hK.2 _ (Uᗮ.starProjection_apply_mem x)
  have hupp' : K (Uᗮ.starProjection x) ∈ Uᗮᗮ :=
    U.le_orthogonal_orthogonal hupp
  rw [(U.starProjection_apply_eq_zero_iff).mpr hlow,
    (Uᗮ.starProjection_apply_eq_zero_iff).mpr hupp', zero_add]
  rfl

omit [CompleteSpace G] in
private theorem diagonalPair_orthogonal_eq_offDiagonalPart_unboundedAmbientExact
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] (K : G →L[ℂ] G) :
    diagonalPair Uᗮ U K = U.offDiagonalPart K := by
  rw [diagonalPair, Submodule.offDiagonalPart_eq, Submodule.diagonalPart_eq]
  simp only [Submodule.orthogonal_orthogonal, Submodule.starProjection_orthogonal',
    comp_eq_mul_unboundedAmbientExact]
  have hp : U.starProjection * U.starProjection = U.starProjection :=
    U.isIdempotentElem_starProjection
  noncomm_ring [hp]

omit [CompleteSpace G] in
private theorem diagonalPair_orthogonal_eq_self_of_isOddFor_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection] {K : G →L[ℂ] G}
    (hK : TauCeti.IsOddFor U K) : diagonalPair Uᗮ U K = K := by
  rw [diagonalPair_orthogonal_eq_offDiagonalPart_unboundedAmbientExact]
  rw [Submodule.offDiagonalPart_eq,
    diagonalPart_eq_zero_of_isOddFor_unboundedAmbientExact hK, sub_zero]

/-! ## The reflection tangent is an odd skew-adjoint block -/

omit [CompleteSpace G] in
private theorem ringInverse_diagonalPart_sq_mem_orthogonal_of_mem_orthogonal_unboundedAmbientExact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection] {Z : G →L[ℂ] G}
    (hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z))
    {y : G} (hy : y ∈ Uᗮ) :
    Ring.inverse (U.diagonalPart Z * U.diagonalPart Z) y ∈ Uᗮ := by
  have hcomm : Commute U.starProjection
      (Ring.inverse (U.diagonalPart Z * U.diagonalPart Z)) :=
    commute_ringInverse hCC
      ((commute_starProjection_diagonalPart U Z).mul_right
        (commute_starProjection_diagonalPart U Z))
  have h := congrArg (fun S : G →L[ℂ] G => S y) hcomm.eq
  simp only [_root_.mul_apply_eq_comp] at h
  have hy0 : U.starProjection y = 0 :=
    (U.starProjection_apply_eq_zero_iff).mpr hy
  rw [hy0, map_zero] at h
  exact (U.starProjection_apply_eq_zero_iff).mp h

omit [CompleteSpace G] in
/-- The whole reflection tangent exchanges the two source summands. -/
theorem isOddFor_unboundedReflectionTangent_exact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection] {Z : G →L[ℂ] G}
    (hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z)) :
    TauCeti.IsOddFor U (unboundedReflectionTangent U Z) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    exact unboundedReflectionTangent_mem_orthogonal_of_mem U Z hCC hy
  · intro y hy
    rw [unboundedReflectionTangent_eq]
    simp only [_root_.mul_apply_eq_comp]
    exact TauCeti.offDiagonalPart_mem_of_mem_orthogonal U Z
      (ringInverse_diagonalPart_sq_mem_orthogonal_of_mem_orthogonal_unboundedAmbientExact
        hCC (TauCeti.diagonalPart_mem_orthogonal_of_mem_orthogonal U Z hy))

/-- The whole reflection tangent is skew-adjoint.  This is the operator form of
having two complementary directed tangent blocks that are adjoints up to sign. -/
theorem adjoint_unboundedReflectionTangent_eq_neg_exact
    {U : Submodule ℂ G} [U.HasOrthogonalProjection] {Z : G →L[ℂ] G}
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z)) :
    (unboundedReflectionTangent U Z).adjoint = -unboundedReflectionTangent U Z := by
  set C := U.diagonalPart Z
  set S := U.offDiagonalPart Z
  set T := unboundedReflectionTangent U Z
  set D := Ring.inverse (C * C)
  have hCsa : IsSelfAdjoint C := TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa
  have hSsa : IsSelfAdjoint S := TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa
  have hDCC : D * (C * C) = 1 := by
    dsimp only [D, C]
    exact Ring.inverse_mul_cancel _ hCC
  have hTformula : T = S * D * C := by
    rfl
  have hTC : T * C = S := by
    rw [hTformula]
    calc
      S * D * C * C = S * (D * (C * C)) := by noncomm_ring
      _ = S := by rw [hDCC, mul_one]
  have hCTstar : C * T.adjoint = S := by
    have h := congrArg ContinuousLinearMap.adjoint hTC
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.mul_def, hCsa.adjoint_eq, hSsa.adjoint_eq] at h
    exact h
  have hanti : C * S + S * C = 0 := by
    simpa only [C, S] using
      TauCeti.diagonalPart_mul_offDiagonalPart_add_offDiagonalPart_mul_diagonalPart
        (U := U) hZ2
  have hCS : C * S = -(S * C) := add_eq_zero_iff_eq_neg.mp hanti
  have hCD : Commute C D := by
    dsimp only [D]
    exact commute_ringInverse hCC ((Commute.refl C).mul_right (Commute.refl C))
  have hCT : C * T = -S := by
    rw [hTformula]
    calc
      C * (S * D * C) = (C * S) * D * C := by noncomm_ring
      _ = -(S * C) * D * C := by rw [hCS]
      _ = -(S * (C * D) * C) := by noncomm_ring
      _ = -(S * (D * C) * C) := by rw [hCD.eq]
      _ = -(S * D * (C * C)) := by noncomm_ring
      _ = -(S * (D * (C * C))) := by rw [mul_assoc]
      _ = -S := by rw [hDCC, mul_one]
  have hCunit : IsUnit C := ((Commute.refl C).isUnit_mul_iff.mp hCC).1
  have hsum : C * (T.adjoint + T) = 0 := by
    rw [mul_add, hCTstar, hCT]
    abel
  have hleft : Ring.inverse C * C = 1 := Ring.inverse_mul_cancel C hCunit
  have hzero : T.adjoint + T = 0 := by
    calc
      T.adjoint + T = 1 * (T.adjoint + T) := by rw [one_mul]
      _ = (Ring.inverse C * C) * (T.adjoint + T) := by rw [hleft]
      _ = Ring.inverse C * (C * (T.adjoint + T)) := by noncomm_ring
      _ = 0 := by rw [hsum, mul_zero]
  exact eq_neg_of_add_eq_zero_left hzero

/-! ## Exact ambient endpoint -/

/-- **Paper-exact unbounded ambient `tan 2Theta` theorem, complex form.**

This is the ambient conclusion of the Section 2 headline theorem at the
unbounded self-adjoint scope advertised by Davis--Kahan.  The caller supplies
only source data: the unbounded self-adjoint `A`, its low-energy spectral
subspace, a bounded self-adjoint fully off-diagonal perturbation `B`, the
reducing reflection `Z` of `A+B`, and the separated form bounds.  Membership of
`B` in the selected source ideal is the only norm-domain premise.

The canonical spectral cutoffs, pole exclusion, directed residual estimate,
and both-corner Lemma-6.1 assembly are all internal. -/
theorem tanTwoTheta_ambient_unbounded_blockRepresentative_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : G →ₗ.[ℂ] G} {B Z : G →L[ℂ] G} {a b c : ℝ}
    (hA : IsSelfAdjoint A)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : G), hZdom x⟩ + B (Z (x : G)) = Z (A x) + Z (B (x : G)))
    (hUa : ∀ x : A.domain,
      (x : G) ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
      RCLike.re ⟪A x, (x : G)⟫_ℂ ≤ a * ‖(x : G)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : G) ∈
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : G)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : G)⟫_ℂ)
    (hab : a < b) (hBmem : N.Mem B) :
    IsUnit
        ((TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z *
          (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z) ∧
      N.Mem (unboundedReflectionTangent
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) Z) ∧
      (b - a) * N.gauge (unboundedReflectionTangent
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) Z) ≤
        2 * N.gauge B := by
  let U : Submodule ℂ G :=
    TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic
  have hred : TauCeti.LinearPMap.ReducesSubspace A U :=
    TauCeti.LinearPMap.reducesSubspace_specRange hA (Set.Iic c) measurableSet_Iic
  have hgU : ∀ y ∈ U,
      ‖U.offDiagonalPart Z y‖ ≤ TauCeti.crossBlockBound (b - a) ‖B‖ * ‖y‖ := by
    intro y hy
    exact TauCeti.norm_offDiagonalPart_apply_le_specRange hA hB hZsa hZ2 hZdom
      hZcomm hUa hUb hab hy
  have hg0 : 0 ≤ TauCeti.crossBlockBound (b - a) ‖B‖ :=
    TauCeti.crossBlockBound_nonneg (norm_nonneg B)
  have hg1 : TauCeti.crossBlockBound (b - a) ‖B‖ < 1 :=
    crossBlockBound_lt_one (sub_pos.mpr hab) (norm_nonneg B)
  have hSle : ‖U.offDiagonalPart Z‖ ≤ TauCeti.crossBlockBound (b - a) ‖B‖ :=
    norm_offDiagonalPart_le hZsa hg0 hgU
  have hS1 : ‖U.offDiagonalPart Z‖ < 1 := lt_of_le_of_lt hSle hg1
  have hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z) :=
    isUnit_diagonalPart_sq_of_forall_mem hZsa hZ2 hg0 hg1 hgU
  have hstrong : StronglyTendsto
      (fun n : ℕ => cutoffCorner (TauCeti.spectralCutoffSeq hA c n)) atTop
      (ContinuousLinearMap.id ℂ U) := by
    simpa [U] using stronglyTendsto_cutoffCorner_spectralCutoffSeq hA c
  have hcorner : ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k (reflectionTangentCorner U Z) ≤
        2 * kyFanApproximationGauge k (reflectionResidualCorner U B) := by
    intro k
    exact gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan hred hB hZsa hZ2
      hZdom hZcomm hUa hUb hab hS1
      (σ := fun n : ℕ => |c| + n) (fun n : ℕ => by positivity)
      (fun n : ℕ => TauCeti.spectralCutoffSeq hA c n) hstrong k
  let T : G →L[ℂ] G := unboundedReflectionTangent U Z
  have hTodd : TauCeti.IsOddFor U T := by
    simpa only [T] using isOddFor_unboundedReflectionTangent_exact
      (U := U) (Z := Z) hCC
  have hTskew : T.adjoint = -T := by
    simpa only [T] using adjoint_unboundedReflectionTangent_eq_neg_exact
      (U := U) (Z := Z) hZsa hZ2 hCC
  have hhalf : 0 < (b - a) / 2 := by linarith
  have hcnorm : ‖((((b - a) / 2 : ℝ)) : ℂ)‖ = (b - a) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhalf]
  have h₀ : ∀ k : ℕ,
      kyFanApproximationGauge k (projectionBlock Uᗮ U
          (((((b - a) / 2 : ℝ)) : ℂ) • T)) ≤
        kyFanApproximationGauge k (projectionBlock Uᗮ U B) := by
    intro k
    rw [projectionBlock_smul_unboundedAmbientExact,
      kyFanApproximationGauge_smul, hcnorm]
    rw [(projectionBlock_same_compression Uᗮ U T).kyFanApproximationGauge_eq k,
      (projectionBlock_same_compression Uᗮ U B).kyFanApproximationGauge_eq k]
    change ((b - a) / 2) * kyFanApproximationGauge k (reflectionTangentCorner U Z) ≤
      kyFanApproximationGauge k (reflectionResidualCorner U B)
    linarith [hcorner k]
  have h₁ : ∀ k : ℕ,
      kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ
          (((((b - a) / 2 : ℝ)) : ℂ) • T)) ≤
        kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ B) := by
    intro k
    rw [projectionBlock_smul_unboundedAmbientExact,
      kyFanApproximationGauge_smul, hcnorm,
      kyFan_upper_eq_lower_of_skewAdjoint_unboundedAmbientExact T hTskew k,
      kyFan_upper_eq_lower_of_selfAdjoint_unboundedAmbientExact B hBsa k]
    have hk := h₀ k
    rw [projectionBlock_smul_unboundedAmbientExact,
      kyFanApproximationGauge_smul, hcnorm] at hk
    exact hk
  have hcombine := lemma61_all_kyFan Uᗮ U
    (((((b - a) / 2 : ℝ)) : ℂ) • T)
    (((((b - a) / 2 : ℝ)) : ℂ) • T) B B h₀ h₁
  have hpairT : diagonalPair Uᗮ U T = T :=
    diagonalPair_orthogonal_eq_self_of_isOddFor_unboundedAmbientExact hTodd
  have hpairB : diagonalPair Uᗮ U B = B :=
    diagonalPair_orthogonal_eq_self_of_isOddFor_unboundedAmbientExact hB
  have hwhole : ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k T ≤ 2 * kyFanApproximationGauge k B := by
    intro k
    have h := hcombine k
    have hsumT :
        projectionBlock Uᗮ U (((((b - a) / 2 : ℝ)) : ℂ) • T) +
          projectionBlock Uᗮᗮ Uᗮ (((((b - a) / 2 : ℝ)) : ℂ) • T) =
        ((((b - a) / 2 : ℝ)) : ℂ) • T := by
      rw [projectionBlock_smul_unboundedAmbientExact,
        projectionBlock_smul_unboundedAmbientExact, ← smul_add]
      change (((((b - a) / 2 : ℝ)) : ℂ) • diagonalPair Uᗮ U T) = _
      rw [hpairT]
    have hsumB :
        projectionBlock Uᗮ U B + projectionBlock Uᗮᗮ Uᗮ B = B := by
      change diagonalPair Uᗮ U B = B
      exact hpairB
    rw [hsumT, hsumB, kyFanApproximationGauge_smul, hcnorm] at h
    linarith
  have hscaled : ∀ k : ℕ,
      ((b - a) / 2) * kyFanApproximationGauge k T ≤ kyFanApproximationGauge k B := by
    intro k
    linarith [hwhole k]
  have hUI := N.mul_gauge_le_of_all_mul_kyFan_le hhalf hBmem hscaled
  change IsUnit (U.diagonalPart Z * U.diagonalPart Z) ∧
      N.Mem T ∧ (b - a) * N.gauge T ≤ 2 * N.gauge B
  refine ⟨hCC, hUI.1, ?_⟩
  nlinarith [hUI.2]


/-! ### The same theorem at an arbitrary reducing subspace

`TanTwoThetaUnboundedReducing.lean` removes the spectral selection of the trial
subspace from the pole exclusion.  The block assembly above never used it, so
the ambient endpoint restates verbatim; only the three previously spectral
`have`s change.  These live here rather than in that module because the assembly
lemmas they use are private to this file. -/

section AmbientReducing

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

/-- **Davis--Kahan 1970, `tan 2Θ`, unbounded ambient form, at an arbitrary
reducing subspace**, on the block representative.

`δ N(tan 2Θ) ≤ 2 N(B)` with the whole perturbation on the right.  This is
`tanTwoTheta_ambient_unbounded_blockRepresentative_symmetricNorming_complex` with the
spectral selection of `U` removed. -/
theorem tanTwoTheta_ambient_unbounded_blockRepresentative_reducing_symmetricNorming_complex
    (N : SymmetricNormingFunction) (hBsa : IsSelfAdjoint B) (hBmem : N.Mem B) :
    IsUnit (U.diagonalPart Z * U.diagonalPart Z) ∧
      N.Mem (unboundedReflectionTangent U Z) ∧
      (b - a) * N.gauge (unboundedReflectionTangent U Z) ≤ 2 * N.gauge B := by
  have hCC := isUnit_diagonalPart_sq_reducing_exact hA hred hB hZsa hZ2 hZdom
    hZcomm hUa hUb hab
  have hcorner := gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan_reducing
    hA hred hB hZsa hZ2 hZdom hZcomm hUa hUb hab
  set T : G →L[ℂ] G := unboundedReflectionTangent U Z with hTdef
  have hTodd : TauCeti.IsOddFor U T :=
    isOddFor_unboundedReflectionTangent_exact (U := U) (Z := Z) hCC
  have hTskew : T.adjoint = -T :=
    adjoint_unboundedReflectionTangent_eq_neg_exact (U := U) (Z := Z) hZsa hZ2 hCC
  have hhalf : 0 < (b - a) / 2 := by linarith
  have hcnorm : ‖((((b - a) / 2 : ℝ)) : ℂ)‖ = (b - a) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhalf]
  have h₀ : ∀ k : ℕ,
      kyFanApproximationGauge k (projectionBlock Uᗮ U
          (((((b - a) / 2 : ℝ)) : ℂ) • T)) ≤
        kyFanApproximationGauge k (projectionBlock Uᗮ U B) := by
    intro k
    rw [projectionBlock_smul_unboundedAmbientExact,
      kyFanApproximationGauge_smul, hcnorm]
    rw [(projectionBlock_same_compression Uᗮ U T).kyFanApproximationGauge_eq k,
      (projectionBlock_same_compression Uᗮ U B).kyFanApproximationGauge_eq k]
    change ((b - a) / 2) * kyFanApproximationGauge k (reflectionTangentCorner U Z) ≤
      kyFanApproximationGauge k (reflectionResidualCorner U B)
    linarith [hcorner k]
  have h₁ : ∀ k : ℕ,
      kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ
          (((((b - a) / 2 : ℝ)) : ℂ) • T)) ≤
        kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ B) := by
    intro k
    rw [projectionBlock_smul_unboundedAmbientExact,
      kyFanApproximationGauge_smul, hcnorm,
      kyFan_upper_eq_lower_of_skewAdjoint_unboundedAmbientExact T hTskew k,
      kyFan_upper_eq_lower_of_selfAdjoint_unboundedAmbientExact B hBsa k]
    have hk := h₀ k
    rw [projectionBlock_smul_unboundedAmbientExact,
      kyFanApproximationGauge_smul, hcnorm] at hk
    exact hk
  have hcombine := lemma61_all_kyFan Uᗮ U
    (((((b - a) / 2 : ℝ)) : ℂ) • T)
    (((((b - a) / 2 : ℝ)) : ℂ) • T) B B h₀ h₁
  have hpairT : diagonalPair Uᗮ U T = T :=
    diagonalPair_orthogonal_eq_self_of_isOddFor_unboundedAmbientExact hTodd
  have hpairB : diagonalPair Uᗮ U B = B :=
    diagonalPair_orthogonal_eq_self_of_isOddFor_unboundedAmbientExact hB
  have hwhole : ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k T ≤ 2 * kyFanApproximationGauge k B := by
    intro k
    have h := hcombine k
    have hsumT :
        projectionBlock Uᗮ U (((((b - a) / 2 : ℝ)) : ℂ) • T) +
          projectionBlock Uᗮᗮ Uᗮ (((((b - a) / 2 : ℝ)) : ℂ) • T) =
        ((((b - a) / 2 : ℝ)) : ℂ) • T := by
      rw [projectionBlock_smul_unboundedAmbientExact,
        projectionBlock_smul_unboundedAmbientExact, ← smul_add]
      change (((((b - a) / 2 : ℝ)) : ℂ) • diagonalPair Uᗮ U T) = _
      rw [hpairT]
    have hsumB :
        projectionBlock Uᗮ U B + projectionBlock Uᗮᗮ Uᗮ B = B := by
      change diagonalPair Uᗮ U B = B
      exact hpairB
    rw [hsumT, hsumB, kyFanApproximationGauge_smul, hcnorm] at h
    linarith
  have hscaled : ∀ k : ℕ,
      ((b - a) / 2) * kyFanApproximationGauge k T ≤ kyFanApproximationGauge k B := by
    intro k
    linarith [hwhole k]
  have hUI := N.mul_gauge_le_of_all_mul_kyFan_le hhalf hBmem hscaled
  refine ⟨hCC, hUI.1, ?_⟩
  nlinarith [hUI.2]


end AmbientReducing


/-- **Davis--Kahan 1970, `tan 2Θ`, unbounded ambient form, at an arbitrary
reducing subspace, on the paper's angle operator.**

The endpoint the source states: `A` self-adjoint and possibly unbounded, `U` any
subspace reducing `A` with the form at most `a` on `U` and at least `b` on `Uᗮ`,
`B` a bounded self-adjoint perturbation off-diagonal for that splitting, `V`
reducing `A + B`.  Then

`(b − a) N(|tan 2Θ|) ≤ 2 N(B)`

for every source unitarily invariant norm, with `Θ` the angle between `U` and
`V` and each ambient principal angle counted with its ambient multiplicity.

The first component is the **derived** pole exclusion `cos 2θ ≠ 0` on the angle
spectrum, which Section 7 proves rather than assumes; no branch is selected, and
`|tan 2Θ|` is what a unitarily invariant norm sees past a quarter turn. -/
theorem tanTwoTheta_ambient_unbounded_reducing_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : G →ₗ.[ℂ] G} {B : G →L[ℂ] G} {a b : ℝ}
    {U : Submodule ℂ G} [U.HasOrthogonalProjection]
    (V : Submodule ℂ G) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A) (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hBsa : IsSelfAdjoint B) (hB : TauCeti.IsOddFor U B)
    (hV : DavisKahan.ReflectionIntertwines A B V)
    (hUa : ∀ x : A.domain, (x : G) ∈ U →
      RCLike.re ⟪A x, (x : G)⟫_ℂ ≤ a * ‖(x : G)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : G) ∈ Uᗮ →
      b * ‖(x : G)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : G)⟫_ℂ)
    (hab : a < b) (hBmem : N.Mem B) :
    (∀ t ∈ spectrum ℝ (TauCeti.DavisKahan.Angle.angleOperatorC U V),
        Real.cos (2 * t) ≠ 0) ∧
      N.Mem (TauCeti.DavisKahan.Angle.absTanTwoAngleOperatorC U V) ∧
      (b - a) * N.gauge
          (TauCeti.DavisKahan.Angle.absTanTwoAngleOperatorC U V) ≤
        2 * N.gauge B := by
  obtain ⟨hunit, hmem, hle⟩ :=
    tanTwoTheta_ambient_unbounded_blockRepresentative_reducing_symmetricNorming_complex
      hA hred hB (TauCeti.DavisKahanExt.isSelfAdjoint_reflectionOperator V)
      (TauCeti.DavisKahan.reflectionOperator_mul_self_complex V)
      hV.mapsDomain hV.commutes hUa hUb hab N hBsa hBmem
  have hcos := DavisKahan.cos_two_ne_zero_of_isUnit_diagonalPart_reflection_sq
    U V hunit
  have hgauge := DavisKahan.extendedGauge_unboundedReflectionTangent_complex
    U V N hcos
  refine ⟨hcos, ?_, ?_⟩
  · unfold SymmetricNormingFunction.Mem at hmem ⊢
    rwa [← hgauge]
  · unfold SymmetricNormingFunction.gauge at hle ⊢
    rwa [← hgauge]

/-! ### The subspace-first interface

The theorem above asks its caller for a reflection `Z` together with four facts
about it.  Two of those, self-adjointness and `Z² = 1`, are not hypotheses at
all: a subspace determines its reflection and the reflection has both properties
by construction.  The other two are genuine mathematics -- they say the
reflection intertwines the perturbed operator -- and they belong to the subspace,
not to a caller-built operator.

`ReflectionIntertwines A B V` carries exactly those two, and the theorem below
takes the reducing subspace `V`, builds `Z = V.reflectionOperator` internally, and
supplies the two structural facts itself.

What is *not* internalized here is the conclusion: it still names
`unboundedReflectionTangent U (V.reflectionOperator)`, the block tangent, rather
than the paper's canonical double-angle tangent.  Bringing it to the canonical
object needs the tan-2Θ analogue of
`DavisKahan.sinTwoThetaIdealBlock_hasSameApproximationNumbers`, which is not
proved here. -/

/-- **Davis--Kahan 1970, `tan 2Θ`, unbounded ambient form, taking the reducing
subspace rather than a reflection witness.**

`tanTwoTheta_ambient_unbounded_blockRepresentative_symmetricNorming_complex` with `Z =
  V.reflectionOperator`
and with `Z` self-adjoint and involutive supplied by the library. -/
theorem tanTwoTheta_ambient_unbounded_blockRepresentative_derivedReflection_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : G →ₗ.[ℂ] G} {B : G →L[ℂ] G} {a b c : ℝ}
    (V : Submodule ℂ G) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hV : DavisKahan.ReflectionIntertwines A B V)
    (hUa : ∀ x : A.domain,
      (x : G) ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
      RCLike.re ⟪A x, (x : G)⟫_ℂ ≤ a * ‖(x : G)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : G) ∈
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : G)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : G)⟫_ℂ)
    (hab : a < b) (hBmem : N.Mem B) :
    IsUnit
        ((TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart
            (V.reflectionOperator) *
          (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart
            (V.reflectionOperator)) ∧
      N.Mem (unboundedReflectionTangent
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)
        (V.reflectionOperator)) ∧
      (b - a) * N.gauge (unboundedReflectionTangent
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)
        (V.reflectionOperator)) ≤
        2 * N.gauge B :=
  tanTwoTheta_ambient_unbounded_blockRepresentative_symmetricNorming_complex N hA hBsa hB
    (TauCeti.DavisKahanExt.isSelfAdjoint_reflectionOperator V)
    (TauCeti.DavisKahan.reflectionOperator_mul_self_complex V)
    hV.mapsDomain hV.commutes hUa hUb hab hBmem

/-- **Davis--Kahan 1970, `tan 2Θ`, unbounded ambient form, on the paper's angle
operator.**

The same theorem as
  `tanTwoTheta_ambient_unbounded_blockRepresentative_derivedReflection_symmetricNorming_complex`, with the
proof's block tangent replaced by the paper's ambient `|tan 2Θ|`.  The two have
the same approximation numbers -- `unboundedReflectionTangent U J_V = Ξ · J_U`
with `J_U` a self-adjoint unitary, and `|Ξ| = |tan 2Θ|` -- so every source
unitarily invariant norm sees them identically; see
`DavisKahan.extendedGauge_unboundedReflectionTangent_complex`.

**No pole hypothesis is asked of the caller, and the conclusion says so.**  The
transport needs `cos 2θ ≠ 0` on the angle spectrum, and that is not an independent
assumption here: the ordered gap already forces the reflection's diagonal block to be
invertible -- the first component of
`tanTwoTheta_ambient_unbounded_blockRepresentative_derivedReflection_symmetricNorming_complex`
-- and `DavisKahan.cos_two_ne_zero_of_isUnit_diagonalPart_reflection_sq` turns that unit
into pole exclusion.  Since 2026-09-05 that exclusion is a *conjunct of the conclusion*
rather than a fact buried in the proof, which is what stops a reader having to open the
proof to learn that `|tan 2Θ|` here is the paper's object and not the value Mathlib's
totalised `cfc` assigns at a quarter turn.  Finding F3.2 of the 2026-09-04 hostile review.

No branch is chosen either: principal angles may exceed `π/4`, and `|tan 2Θ|` is what a
norm sees there. -/
theorem tanTwoTheta_ambient_unbounded_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : G →ₗ.[ℂ] G} {B : G →L[ℂ] G} {a b c : ℝ}
    (V : Submodule ℂ G) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hV : DavisKahan.ReflectionIntertwines A B V)
    (hUa : ∀ x : A.domain,
      (x : G) ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
      RCLike.re ⟪A x, (x : G)⟫_ℂ ≤ a * ‖(x : G)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : G) ∈
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : G)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : G)⟫_ℂ)
    (hab : a < b) (hBmem : N.Mem B) :
    (∀ t ∈ spectrum ℝ (TauCeti.DavisKahan.Angle.angleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V),
        Real.cos (2 * t) ≠ 0) ∧
      N.Mem (TauCeti.DavisKahan.Angle.absTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) ∧
      (b - a) * N.gauge (TauCeti.DavisKahan.Angle.absTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) ≤
        2 * N.gauge B := by
  obtain ⟨hunit, hmem, hle⟩ :=
    tanTwoTheta_ambient_unbounded_blockRepresentative_derivedReflection_symmetricNorming_complex
      N V hA hBsa hB hV hUa hUb
      hab hBmem
  have hcos := DavisKahan.cos_two_ne_zero_of_isUnit_diagonalPart_reflection_sq
    (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V hunit
  have hgauge := DavisKahan.extendedGauge_unboundedReflectionTangent_complex
    (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V N hcos
  refine ⟨hcos, ?_, ?_⟩
  · unfold SymmetricNormingFunction.Mem at hmem ⊢
    rwa [← hgauge]
  · unfold SymmetricNormingFunction.gauge at hle ⊢
    rwa [← hgauge]

/-- **Davis--Kahan 1970, the ambient `tan 2Θ` theorem at the printed source scope
over `ℂ`.**

Separable ambient Hilbert space and normalized unitarily invariant norm.  The
pole-exclusion conjunct does not mention the norm and is read off the Ky Fan
norming function; the estimate goes through the Fan-dominance bridge with the
source's constant 2. -/
theorem tanTwoTheta_ambient_unbounded_normalizedUIN_complex
    
    (N : NormalizedUnitaryInvariantNorm.{0, u} ℂ)
    {A : G →ₗ.[ℂ] G} {B : G →L[ℂ] G} {a b c : ℝ}
    (V : Submodule ℂ G) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hV : DavisKahan.ReflectionIntertwines A B V)
    (hUa : ∀ x : A.domain,
      (x : G) ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
      RCLike.re ⟪A x, (x : G)⟫_ℂ ≤ a * ‖(x : G)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : G) ∈
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : G)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : G)⟫_ℂ)
    (hab : a < b) (hBmem : N.Mem B) :
    (∀ t ∈ spectrum ℝ (TauCeti.DavisKahan.Angle.angleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V),
        Real.cos (2 * t) ≠ 0) ∧
      N.Mem (TauCeti.DavisKahan.Angle.absTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) ∧
      (b - a) * N.gauge (TauCeti.DavisKahan.Angle.absTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) ≤
        2 * N.gauge B := by
  obtain ⟨hcos, -, -⟩ :=
    tanTwoTheta_ambient_unbounded_symmetricNorming_complex
      (kyFanNormingFunction 1 one_pos) V hA hBsa hB hV hUa hUb hab
      (kyFanNormingFunction_mem 1 one_pos _)
  obtain ⟨hmem, hle⟩ :=
    normalizedUnitaryInvariant_of_symmetricNorming_mul N (sub_pos.mpr hab) two_pos hBmem
      fun M hM => by
        obtain ⟨-, hm, hl⟩ :=
          tanTwoTheta_ambient_unbounded_symmetricNorming_complex M V hA hBsa hB hV
            hUa hUb hab hM
        exact ⟨hm, hl⟩
  exact ⟨hcos, hmem, hle⟩

end

section DirectedCornerCorrespondence

variable {Ea : Type*} [NormedAddCommGroup Ea] [InnerProductSpace ℂ Ea] [CompleteSpace Ea]
variable (U V : Submodule ℂ Ea) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- An orthogonally complemented subspace of a complete space is complete; the
approximation-number API for block compressions needs it on the nose. -/
local instance instCompleteSpaceCoeDirectedCorner
    (W : Submodule ℂ Ea) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

/-- **The canonical directed tangent corner IS the paper's directed corner.**

The Section 2 directed `tan 2Θ` theorems conclude on
`reflectionTangentCorner U V.reflectionOperator`, while Davis and Kahan state the
bound on the directed `tan 2Θ₀` object, whose block spelling is the `U → Uᗮ`
corner of the paper's own double-angle representative.  Hostile review asked for
registered evidence that these are the same thing rather than prose asserting
that a unitarily invariant norm cannot tell them apart.

They are not merely cospectral; they are equal.  Two facts do it:

* `unboundedReflectionTangent_reflection_eq` -- the reflection tangent is the
  paper's block representative composed with the reflection through `U`;
* `blockCompression_mul_reflectionOperator` -- a compression out of `U`
  feeds its operator only vectors of `U`, which that reflection fixes.

So the reflection is invisible to the corner, and what remains on the right is
the paper's directed corner.  Every symmetric gauge of the two therefore agrees,
which is what the source-facing bound needs. -/
theorem reflectionTangentCorner_reflection_eq_tanTwoBlockCompression
    (hinv : IsUnit ((1 : Ea →L[ℂ] Ea) - 2 *
      (projectorDifference U V * projectorDifference U V))) :
    reflectionTangentCorner U V.reflectionOperator
      = blockCompression Uᗮ U (tanTwoBlockRepresentative U V) := by
  unfold reflectionTangentCorner
  rw [TauCeti.DavisKahan.unboundedReflectionTangent_reflection_eq U V hinv,
    blockCompression_mul_reflectionOperator]

/-- **The canonical directed object and the paper's directed `tan 2Θ₀` corner
have the same approximation singular sequence.**

This is the correspondence the Section 2 directed clauses need, and it is now a
chain of equalities rather than an appeal to what a unitarily invariant norm can
or cannot distinguish:

1. the canonical object is the compressed corner of the paper's double-angle
   block representative (`reflectionTangentCorner_reflection_eq_tanTwoBlockCompression`);
2. that representative is a `diagonalPair`, whose complementary summand a
   compression out of `U` does not see
   (`blockCompression_diagonalPair`), leaving the compressed corner of
   the doubled tangent expression itself;
3. an ambient projection block and its compression have the same approximation
   singular sequence (`projectionBlock_same_compression`).

The right-hand side is the ambient block spelling the paper-facing directed
object uses, so a symmetric gauge of the two agrees and the printed norm is the
one the canonical theorems bound. -/
theorem tanTwoDirectedCornerC_sameApproximationSingularSequence_reflectionTangentCorner
    (hinv : IsUnit ((1 : Ea →L[ℂ] Ea) - 2 *
      (projectorDifference U V * projectorDifference U V))) :
    SameApproximationSingularSequence
      (projectionBlock Uᗮ U
        (2 * (projectorDifference U V * doubleSecant U V)))
      (reflectionTangentCorner U V.reflectionOperator) := by
  rw [reflectionTangentCorner_reflection_eq_tanTwoBlockCompression U V hinv,
    tanTwoBlockRepresentative, blockCompression_diagonalPair]
  exact projectionBlock_same_compression Uᗮ U _

/-- **Davis--Kahan 1970, the directed `tan 2Θ₀` bound, stated on the paper's own
object, over `ℂ`.**

Source-shaped endpoint.  The reusable directed theorems quantify over an
arbitrary self-adjoint involution `Z` and conclude on
`reflectionTangentCorner U Z`; hostile review observed that such a statement is
not an exact witness for a printed result about `tan 2Θ₀`, because nothing in
its type says the object bounded is the paper's.  This takes the actual reducing
subspace `V`, derives its reflection internally, and concludes on the `U → Uᗮ`
corner of the paper's own double-angle block representative.

The arbitrary-`Z` theorem remains as the general result; this is the spelling a
reviewer compares against Section 2. -/
theorem tanTwoTheta_directed_unboundedResidual_reducing_blockCompression_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : Ea →ₗ.[ℂ] Ea} {B : Ea →L[ℂ] Ea} {a b : ℝ}
    (hA : IsSelfAdjoint A) (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hB : TauCeti.IsOddFor U B)
    (hV : DavisKahan.ReflectionIntertwines A B V)
    (hUa : ∀ x : A.domain, (x : Ea) ∈ U →
      RCLike.re ⟪A x, (x : Ea)⟫_ℂ ≤ a * ‖(x : Ea)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : Ea) ∈ Uᗮ →
      b * ‖(x : Ea)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : Ea)⟫_ℂ)
    (hab : a < b) (hRmem : N.Mem (blockCompression Uᗮ U B)) :
    N.Mem (blockCompression Uᗮ U (tanTwoBlockRepresentative U V)) ∧
      (b - a) * N.gauge (blockCompression Uᗮ U (tanTwoBlockRepresentative U V)) ≤
        2 * N.gauge (blockCompression Uᗮ U B) := by
  have hZsa := TauCeti.DavisKahanExt.isSelfAdjoint_reflectionOperator V
  have hZ2 := TauCeti.DavisKahan.reflectionOperator_mul_self_complex V
  have hS1 : ‖U.offDiagonalPart V.reflectionOperator‖ < 1 :=
    norm_offDiagonalPart_lt_one_reducing_exact hA hred hB hZsa hZ2 hV.mapsDomain
      hV.commutes hUa hUb hab
  have hsq : ‖U.offDiagonalPart V.reflectionOperator *
      U.offDiagonalPart V.reflectionOperator‖ < 1 := by
    have h := norm_mul_le (U.offDiagonalPart V.reflectionOperator)
      (U.offDiagonalPart V.reflectionOperator)
    nlinarith [norm_nonneg (U.offDiagonalPart V.reflectionOperator)]
  have hinv := TauCeti.DavisKahan.isUnit_signedCosTwo_of_isUnit_diagonalPart_sq U V
    (isUnit_diagonalPart_sq hZ2 hsq)
  obtain ⟨-, -, hmem, hle⟩ :=
    tanTwoTheta_directed_unboundedResidual_reducing_derivedReflection_symmetricNorming_complex
      N V hA hred hB hV hUa hUb hab hRmem
  rw [← reflectionTangentCorner_reflection_eq_tanTwoBlockCompression U V hinv]
  exact ⟨hmem, hle⟩

end DirectedCornerCorrespondence

/-! ### The ambient block spelling of a directed corner

`blockCompression Ω Γ K : Γ →L Ω` and `projectionBlock Ω Γ K : E →L E` are the
same operator read in two coordinate systems, and `projectionBlock_same_compression`
says they have the same approximation singular sequence.  A symmetric norming
function sees nothing else, so the three facts below let a theorem proved in the
compressed spelling be read in the ambient spelling the paper-facing directed
objects use -- `tanTwoDirectedCornerR` is an ambient projection block. -/

section AmbientSpelling

variable {𝕜 : Type*} [RCLike 𝕜] {G : Type*} [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- The scalar-generic completeness instance for an orthogonally complemented
subspace, reinstalled because `local instance` does not propagate. -/
local instance instCompleteSpaceCoeAmbientSpelling
    (W : Submodule 𝕜 G) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

variable (Ω Γ : Submodule 𝕜 G) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]

/-- An ambient projection block and its compression have the same extended
gauge under every symmetric norming function. -/
theorem extendedGauge_projectionBlock_eq_blockCompression
    (N : SymmetricNormingFunction) (K : G →L[𝕜] G) :
    N.extendedGauge (projectionBlock Ω Γ K) = N.extendedGauge (blockCompression Ω Γ K) :=
  N.extendedGauge_eq_of_hasSameApproximationNumbers (projectionBlock_same_compression Ω Γ K)

/-- Ideal membership of an ambient projection block is that of its compression. -/
theorem mem_projectionBlock_iff_mem_blockCompression
    (N : SymmetricNormingFunction) (K : G →L[𝕜] G) :
    N.Mem (projectionBlock Ω Γ K) ↔ N.Mem (blockCompression Ω Γ K) := by
  unfold SymmetricNormingFunction.Mem
  rw [extendedGauge_projectionBlock_eq_blockCompression]

/-- The gauge of an ambient projection block is that of its compression. -/
theorem gauge_projectionBlock_eq_blockCompression
    (N : SymmetricNormingFunction) (K : G →L[𝕜] G) :
    N.gauge (projectionBlock Ω Γ K) = N.gauge (blockCompression Ω Γ K) := by
  unfold SymmetricNormingFunction.gauge
  rw [extendedGauge_projectionBlock_eq_blockCompression]

end AmbientSpelling

section DirectedSourceEndpoint

variable {Ea : Type*} [NormedAddCommGroup Ea] [InnerProductSpace ℂ Ea] [CompleteSpace Ea]
variable (U V : Submodule ℂ Ea) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- An orthogonally complemented subspace of a complete space is complete;
reinstalled for this section because `local instance` does not propagate. -/
local instance instCompleteSpaceCoeDirectedSourceEndpoint
    (W : Submodule ℂ Ea) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

/-- **The paper's directed `tan 2Θ₀` corner carries the doubled directed angles,
singular value by singular value.**

The directed object the Section 2 statement bounds is the `U → Uᗮ` projection
block of `2 (P_V − P_U) (1 − 2 (P_V − P_U)²)⁻¹`, which is how `tan 2Θ₀ =
2 sin Θ₀ cos Θ₀ / cos 2Θ₀` is spelled without choosing a branch.  This theorem is
what makes that reading a theorem rather than a convention: its `n`-th
approximation number is `tan (arcsin aₙ(sin 2Θ₀))`, with `sin 2Θ₀` the paper's
directed double-angle sine `DavisKahan.sinTwoThetaIdealBlock U V` -- whose
singular values are those of `directedSinTwoAngleOperatorC U V` by
`DavisKahan.sinTwoThetaIdealBlock_hasSameApproximationNumbers`.  Each directed
principal angle appears once, and `tan (arcsin (sin 2θ)) = |tan 2θ|` on both
sides of the quarter turn, so no branch is chosen.

The hypothesis is the pole exclusion `‖S‖ < 1` for the off-diagonal block of the
reflection through `V`; it is derived, not assumed, in
`tanTwoTheta_directed_unboundedResidual_symmetricNorming_complex`, which also
restates this identity as its second conjunct.

Chain: `reflectionTangentCorner_reflection_eq_tanTwoBlockCompression` and
`blockCompression_diagonalPair` identify the reflection tangent corner with the
compression of this block; `projectionBlock_same_compression` moves to the
ambient spelling; `approximationNumber_reflectionTangentCorner` and
`hasSameApproximationNumbers_reflectionSineCorner_sinTwoThetaIdealBlock` read
off the singular values. -/
theorem approximationNumber_tanTwoDirectedCorner
    (hS1 : ‖U.offDiagonalPart V.reflectionOperator‖ < 1) (n : ℕ) :
    (projectionBlock Uᗮ U
        (2 * (projectorDifference U V * doubleSecant U V))).approximationNumber n =
      Real.tan (Real.arcsin
        ((DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n)) := by
  have hZsa := TauCeti.DavisKahanExt.isSelfAdjoint_reflectionOperator V
  have hZ2 := TauCeti.DavisKahan.reflectionOperator_mul_self_complex V
  have hsq : ‖U.offDiagonalPart V.reflectionOperator *
      U.offDiagonalPart V.reflectionOperator‖ < 1 := by
    have h := norm_mul_le (U.offDiagonalPart V.reflectionOperator)
      (U.offDiagonalPart V.reflectionOperator)
    nlinarith [norm_nonneg (U.offDiagonalPart V.reflectionOperator)]
  have hinv := TauCeti.DavisKahan.isUnit_signedCosTwo_of_isUnit_diagonalPart_sq U V
    (isUnit_diagonalPart_sq hZ2 hsq)
  have hcorner : reflectionTangentCorner U V.reflectionOperator =
      blockCompression Uᗮ U (2 * (projectorDifference U V * doubleSecant U V)) := by
    rw [reflectionTangentCorner_reflection_eq_tanTwoBlockCompression U V hinv,
      tanTwoBlockRepresentative, blockCompression_diagonalPair]
  rw [(projectionBlock_same_compression Uᗮ U _) n, ← hcorner,
    approximationNumber_reflectionTangentCorner hZsa hZ2 hS1 n,
    hasSameApproximationNumbers_reflectionSineCorner_sinTwoThetaIdealBlock U V n]

/-- **Davis--Kahan 1970, the `tan 2Θ` theorem, directed clause, over `ℂ`:
`(b − a) N(tan 2Θ₀) ≤ 2 N(R)`.**

The source-shaped endpoint.  Its data are the paper's: a self-adjoint, possibly
unbounded `A`; a closed subspace `U` reducing `A`, with the form of `A` at most
`a` on `U` and at least `b` on `Uᗮ`, `a < b` (the ordered gap, both sides
half-infinite); a bounded self-adjoint-free perturbation `B` that is odd for the
splitting (`H₀ = H₁ = 0`); a closed subspace `V` reducing `A + B`; and a
symmetric norming function `N` in whose ideal the residual `R = P_{Uᗮ} B P_U`
lies.  Nothing else: no pole certificate, no quarter-angle branch, no spectral
placement of the perturbed blocks, no finite-dimensionality, no reflection or
involution supplied by the caller.

The conclusion is on the paper's directed object, the `U → Uᗮ` projection block
of `2 (P_V − P_U)(1 − 2(P_V − P_U)²)⁻¹`, and says four things: no directed
doubled angle is a quarter turn (the pole exclusion Section 7 derives); that block
has singular values exactly `tan (arcsin aₙ(sin 2Θ₀))`, one per directed
principal angle (`approximationNumber_tanTwoDirectedCorner`), which is what
makes it `tan 2Θ₀`; it lies in the ideal of `N`; and
`(b − a) N(tan 2Θ₀) ≤ 2 N(R)`.

The reusable theorems quantify over an arbitrary self-adjoint involution `Z` and
conclude on `reflectionTangentCorner U Z`; they remain the general result.  This
is the statement a reviewer compares against Section 2. -/
theorem tanTwoTheta_directed_unboundedResidual_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : Ea →ₗ.[ℂ] Ea} {B : Ea →L[ℂ] Ea} {a b : ℝ}
    (hA : IsSelfAdjoint A) (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hB : TauCeti.IsOddFor U B)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : Ea) ∈ U →
      RCLike.re ⟪A x, (x : Ea)⟫_ℂ ≤ a * ‖(x : Ea)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : Ea) ∈ Uᗮ →
      b * ‖(x : Ea)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : Ea)⟫_ℂ)
    (hab : a < b) (hRmem : N.Mem (projectionBlock Uᗮ U B)) :
    (∀ n : ℕ, (DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n < 1) ∧
      (∀ n : ℕ,
        (projectionBlock Uᗮ U
            (2 * (projectorDifference U V * doubleSecant U V))).approximationNumber n =
          Real.tan (Real.arcsin
            ((DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n))) ∧
      N.Mem (projectionBlock Uᗮ U (2 * (projectorDifference U V * doubleSecant U V))) ∧
      (b - a) * N.gauge
          (projectionBlock Uᗮ U (2 * (projectorDifference U V * doubleSecant U V))) ≤
        2 * N.gauge (projectionBlock Uᗮ U B) := by
  have hV' : DavisKahan.ReflectionIntertwines A B V :=
    DavisKahan.ReflectionIntertwines.ofReducesSubspace hV
  have hZsa := TauCeti.DavisKahanExt.isSelfAdjoint_reflectionOperator V
  have hZ2 := TauCeti.DavisKahan.reflectionOperator_mul_self_complex V
  have hS1 : ‖U.offDiagonalPart V.reflectionOperator‖ < 1 :=
    norm_offDiagonalPart_lt_one_reducing_exact hA hred hB hZsa hZ2 hV'.mapsDomain
      hV'.commutes hUa hUb hab
  have hsq : ‖U.offDiagonalPart V.reflectionOperator *
      U.offDiagonalPart V.reflectionOperator‖ < 1 := by
    have h := norm_mul_le (U.offDiagonalPart V.reflectionOperator)
      (U.offDiagonalPart V.reflectionOperator)
    nlinarith [norm_nonneg (U.offDiagonalPart V.reflectionOperator)]
  have hinv := TauCeti.DavisKahan.isUnit_signedCosTwo_of_isUnit_diagonalPart_sq U V
    (isUnit_diagonalPart_sq hZ2 hsq)
  have hcorner : reflectionTangentCorner U V.reflectionOperator =
      blockCompression Uᗮ U (2 * (projectorDifference U V * doubleSecant U V)) := by
    rw [reflectionTangentCorner_reflection_eq_tanTwoBlockCompression U V hinv,
      tanTwoBlockRepresentative, blockCompression_diagonalPair]
  have hRmem' : N.Mem (blockCompression Uᗮ U B) :=
    (mem_projectionBlock_iff_mem_blockCompression Uᗮ U N B).1 hRmem
  obtain ⟨hlt, -, hmem, hle⟩ :=
    tanTwoTheta_directed_unboundedResidual_reducing_derivedReflection_symmetricNorming_complex
      N V hA hred hB hV' hUa hUb hab hRmem'
  refine ⟨hlt, fun n => approximationNumber_tanTwoDirectedCorner U V hS1 n, ?_, ?_⟩
  · rw [mem_projectionBlock_iff_mem_blockCompression, ← hcorner]
    exact hmem
  · rw [gauge_projectionBlock_eq_blockCompression, gauge_projectionBlock_eq_blockCompression,
      ← hcorner]
    exact hle

/-- **Davis--Kahan 1970, the directed `tan 2Θ₀` theorem at the printed source
scope over `ℂ`.**

Separable ambient Hilbert space and normalized unitarily invariant norm.  The
two pole-exclusion conjuncts do not mention the norm, so they are read off the
Ky Fan norming function, whose ideal is everything; the estimate itself goes
through the Fan-dominance bridge. -/
theorem tanTwoTheta_directed_unboundedResidual_normalizedUIN_complex
    
    (N : NormalizedUnitaryInvariantNorm.{0, _} ℂ)
    {A : Ea →ₗ.[ℂ] Ea} {B : Ea →L[ℂ] Ea} {a b : ℝ}
    (hA : IsSelfAdjoint A) (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hB : TauCeti.IsOddFor U B)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : Ea) ∈ U →
      RCLike.re ⟪A x, (x : Ea)⟫_ℂ ≤ a * ‖(x : Ea)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : Ea) ∈ Uᗮ →
      b * ‖(x : Ea)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : Ea)⟫_ℂ)
    (hab : a < b) (hRmem : N.Mem (projectionBlock Uᗮ U B)) :
    (∀ n : ℕ, (DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n < 1) ∧
      (∀ n : ℕ,
        (projectionBlock Uᗮ U
            (2 * (projectorDifference U V * doubleSecant U V))).approximationNumber n =
          Real.tan (Real.arcsin
            ((DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n))) ∧
      N.Mem (projectionBlock Uᗮ U (2 * (projectorDifference U V * doubleSecant U V))) ∧
      (b - a) * N.gauge
          (projectionBlock Uᗮ U (2 * (projectorDifference U V * doubleSecant U V))) ≤
        2 * N.gauge (projectionBlock Uᗮ U B) := by
  obtain ⟨hpole, htan, -, -⟩ :=
    tanTwoTheta_directed_unboundedResidual_symmetricNorming_complex U V
      (kyFanNormingFunction 1 one_pos) hA hred hB hV hUa hUb hab
      (kyFanNormingFunction_mem 1 one_pos _)
  obtain ⟨hmem, hle⟩ :=
    normalizedUnitaryInvariant_of_symmetricNorming_mul N (sub_pos.mpr hab) two_pos hRmem
      fun M hM => by
        obtain ⟨-, -, hm, hl⟩ :=
          tanTwoTheta_directed_unboundedResidual_symmetricNorming_complex U V M
            hA hred hB hV hUa hUb hab hM
        exact ⟨hm, hl⟩
  exact ⟨hpole, htan, hmem, hle⟩

end DirectedSourceEndpoint


end DavisKahan1970
end TauCeti
