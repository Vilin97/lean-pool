/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.ReflectionTangentKyFan
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngle
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaAmbient
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.ReflectionBlocks
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.UnboundedPole
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SpectralOrder

/-! # Tan Two Theta Reflection Ambient -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# The branch-free ambient half of Davis--Kahan `tan 2Theta`

This file closes the remaining Section 7 ambient corner estimate without a
quarter-angle branch.  The singular family is taken for the **actual** tangent
corner.  The signed cosine blocks are kept signed and their polar isometries
absorb the side of `pi/4`; no graph-coordinate rearrangement occurs.

The sharp factor `2` is introduced once, by the two residual pairings in
Equation (7.6).  The estimate is proved first against the lower residual corner
`U -> Uᗮ`.  Only after that estimate is complete is self-adjointness of `H`
used to identify its Ky Fan gauge with the upper corner required by the ambient
Lemma-6.1 assembly.
-/

namespace TauCeti
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

omit [CompleteSpace E] in
private theorem comp_eq_mul_reflection (f g : E →L[ℂ] E) : f ∘L g = f * g := rfl

omit [CompleteSpace E] in
private theorem starProjection_idem_reflection (U : Submodule ℂ E)
    [U.HasOrthogonalProjection] : U.starProjection * U.starProjection = U.starProjection :=
  U.isIdempotentElem_starProjection


omit [CompleteSpace E] in
private theorem projectionBlock_lower_reflection
    {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    (K : E →L[ℂ] E) :
    projectionBlock Uᗮ U K =
      (1 - U.starProjection) * K * U.starProjection := by
  rw [projectionBlock, Submodule.starProjection_orthogonal',
    comp_eq_mul_reflection, comp_eq_mul_reflection, mul_assoc]

omit [CompleteSpace E] in
private theorem projectionBlock_upper_reflection
    {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    (K : E →L[ℂ] E) :
    projectionBlock Uᗮᗮ Uᗮ K =
      U.starProjection * K * (1 - U.starProjection) := by
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  rw [projectionBlock]
  simp only [hUperp, Submodule.starProjection_orthogonal', comp_eq_mul_reflection]
  rw [mul_assoc]

private theorem kyFan_lowerBlock_eq_upperBlock_reflection
    {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    (K : E →L[ℂ] E) (hK : IsSelfAdjoint K) (k : ℕ) :
    kyFanApproximationGauge k (projectionBlock Uᗮ U K) =
      kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ K) := by
  have hadj : projectionBlock Uᗮᗮ Uᗮ K =
      (projectionBlock Uᗮ U K).adjoint := by
    rw [projectionBlock_upper_reflection, projectionBlock_lower_reflection]
    change _ = star _
    simp only [star_mul, star_sub, star_one,
      (isSelfAdjoint_starProjection U).star_eq, hK.star_eq]
    noncomm_ring
  rw [hadj, kyFanApproximationGauge_adjoint]

omit [CompleteSpace E] in
private theorem projectionBlock_diagonalPair_lower_reflection
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (K : E →L[ℂ] E) :
    projectionBlock Uᗮ U (diagonalPair Uᗮ U K) =
      projectionBlock Uᗮ U K := by
  unfold projectionBlock diagonalPair
  simp only [Submodule.orthogonal_orthogonal,
    Submodule.starProjection_orthogonal', comp_eq_mul_reflection]
  have hp := starProjection_idem_reflection U
  have hqp : (1 - U.starProjection) * U.starProjection = 0 := by
    noncomm_ring [hp]
  have hqq : (1 - U.starProjection) * (1 - U.starProjection) =
      1 - U.starProjection := by
    noncomm_ring [hp]
  calc
    (1 - U.starProjection) *
          (((1 - U.starProjection) * (K * U.starProjection) +
              U.starProjection * (K * (1 - U.starProjection))) *
            U.starProjection) =
        (1 - U.starProjection) *
          (((1 - U.starProjection) * K *
              (U.starProjection * U.starProjection)) +
            U.starProjection * K *
              ((1 - U.starProjection) * U.starProjection)) := by
            noncomm_ring
    _ = (1 - U.starProjection) *
          ((1 - U.starProjection) * K * U.starProjection) := by
            rw [hp, hqp, mul_zero, add_zero]
    _ = (1 - U.starProjection) * K * U.starProjection := by
          calc
            (1 - U.starProjection) *
                ((1 - U.starProjection) * K * U.starProjection) =
                ((1 - U.starProjection) * (1 - U.starProjection)) * K *
                  U.starProjection := by
              noncomm_ring
            _ = (1 - U.starProjection) * K * U.starProjection := by rw [hqq]

section ReflectionRing

variable {A : Type*} [Ring A] {p D : A}

private theorem sq_eq_sub_reflection
    (hkey : D * p + p * D + D * D = D) :
    D * D = D - D * p - p * D := by
  have h : D * D = D - (D * p + p * D) := eq_sub_of_add_eq' hkey
  rw [h]
  abel

private theorem proj_sq_reflection (hp : p * p = p)
    (hkey : D * p + p * D + D * D = D) :
    p * (D * D) = -(p * D * p) := by
  have e1 : p * (D * p) = p * D * p := (mul_assoc p D p).symm
  have e2 : p * (p * D) = p * D := by rw [← mul_assoc, hp]
  rw [sq_eq_sub_reflection hkey, mul_sub, mul_sub, e1, e2]
  abel

private theorem sq_proj_reflection (hp : p * p = p)
    (hkey : D * p + p * D + D * D = D) :
    D * D * p = -(p * D * p) := by
  have e3 : D * p * p = D * p := by rw [mul_assoc, hp]
  rw [sq_eq_sub_reflection hkey, sub_mul, sub_mul, e3]
  abel

private theorem proj_comm_sq_reflection (hp : p * p = p)
    (hkey : D * p + p * D + D * D = D) :
    p * (D * D) = D * D * p := by
  rw [proj_sq_reflection hp hkey, sq_proj_reflection hp hkey]

private theorem inverse_comm_reflection {a x : A} (ha : IsUnit a)
    (h : x * a = a * x) :
    x * Ring.inverse a = Ring.inverse a * x := by
  have h1 : Ring.inverse a * a = 1 := Ring.inverse_mul_cancel a ha
  have h2 : a * Ring.inverse a = 1 := Ring.mul_inverse_cancel a ha
  calc
    x * Ring.inverse a = (Ring.inverse a * a) * (x * Ring.inverse a) := by
      rw [h1, one_mul]
    _ = Ring.inverse a * ((a * x) * Ring.inverse a) := by noncomm_ring
    _ = Ring.inverse a * ((x * a) * Ring.inverse a) := by rw [h]
    _ = Ring.inverse a * x * (a * Ring.inverse a) := by noncomm_ring
    _ = Ring.inverse a * x := by rw [h2, mul_one]

end ReflectionRing

/-- The signed doubled cosine `1 - 2(P_V-P_U)^2`. -/
def signedCosTwo (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  1 - 2 * (projectorDifference U V * projectorDifference U V)

omit [CompleteSpace E] in
/-- The signed doubled cosine commutes with the projection onto `U`. -/
theorem signedCosTwo_comm_starProjection
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    signedCosTwo U V * U.starProjection = U.starProjection * signedCosTwo U V := by
  have hsq := proj_comm_sq_reflection
    (starProjection_idem_reflection U)
    (projectorDifference_anticommutator (U := U) (V := V))
  unfold signedCosTwo
  rw [mul_sub, sub_mul, mul_one, one_mul]
  have htwo :
      (2 * (projectorDifference U V * projectorDifference U V)) *
          U.starProjection =
        2 * ((projectorDifference U V * projectorDifference U V) *
          U.starProjection) := by noncomm_ring
  have htwo' :
      U.starProjection *
          (2 * (projectorDifference U V * projectorDifference U V)) =
        2 * (U.starProjection *
          (projectorDifference U V * projectorDifference U V)) := by
    rw [show (2 : E →L[ℂ] E) = 1 + 1 from (one_add_one_eq_two).symm]
    noncomm_ring
  rw [htwo, htwo', hsq]

omit [CompleteSpace E] in
/-- The signed doubled cosine commutes with the projection onto `Uᗮ`. -/
theorem signedCosTwo_comm_starProjection_orthogonal
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    signedCosTwo U V * Uᗮ.starProjection = Uᗮ.starProjection * signedCosTwo U V := by
  rw [Submodule.starProjection_orthogonal']
  have h := signedCosTwo_comm_starProjection (U := U) (V := V)
  calc
    signedCosTwo U V * (1 - U.starProjection) =
        signedCosTwo U V - signedCosTwo U V * U.starProjection := by
      noncomm_ring
    _ = signedCosTwo U V - U.starProjection * signedCosTwo U V := by rw [h]
    _ = (1 - U.starProjection) * signedCosTwo U V := by
      noncomm_ring

/-- The signed doubled cosine is self-adjoint: it is `1 - 2 D²` with `D` a difference of
orthogonal projections. -/
theorem signedCosTwo_selfAdjoint
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (signedCosTwo U V) := by
  have hD := isSelfAdjoint_projectorDifference (U := U) (V := V)
  unfold signedCosTwo
  rw [IsSelfAdjoint, star_sub, star_one, star_mul, star_mul,
    star_ofNat, hD.star_eq]
  noncomm_ring

omit [CompleteSpace E] in
/-- The diagonal block of the reflection through `V`, relative to `U`, is the
reflection through `U` times the signed doubled cosine.  Squaring therefore
removes the harmless reflection factor. -/
theorem diagonalPart_reflection_eq_reflection_mul_signedCosTwo
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.diagonalPart V.reflectionOperator = U.reflectionOperator * signedCosTwo U V := by
  unfold signedCosTwo
  rw [Submodule.diagonalPart_eq,
    Submodule.reflectionOperator_eq_two_smul_sub_id U,
    Submodule.reflectionOperator_eq_two_smul_sub_id V]
  simp only [two_smul, Submodule.starProjection_orthogonal', comp_eq_mul_reflection]
  rw [projectorDifference, ← ContinuousLinearMap.one_def]
  have hp := starProjection_idem_reflection U
  have hq := starProjection_idem_reflection V
  simp only [two_mul, mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one,
    ← mul_assoc, hp, hq]
  abel

omit [CompleteSpace E] in
private theorem maps_mem_of_comm_starProjection
    {U : Submodule ℂ E} [U.HasOrthogonalProjection] (K : E →L[ℂ] E)
    (hcomm : K * U.starProjection = U.starProjection * K) {x : E} (hx : x ∈ U) :
    K x ∈ U := by
  rw [← Submodule.starProjection_eq_self_iff]
  have h := congrArg (fun T : E →L[ℂ] E => T x) hcomm
  simp only [mul_apply_eq_comp] at h
  rw [Submodule.starProjection_eq_self_iff.mpr hx] at h
  exact h.symm

omit [CompleteSpace E] in
private theorem maps_mem_orthogonal_of_comm_starProjection
    {U : Submodule ℂ E} [U.HasOrthogonalProjection] (K : E →L[ℂ] E)
    (hcomm : K * U.starProjection = U.starProjection * K) {x : E} (hx : x ∈ Uᗮ) :
    K x ∈ Uᗮ := by
  apply (U.starProjection_apply_eq_zero_iff).mp
  have h := congrArg (fun T : E →L[ℂ] E => T x) hcomm
  simp only [mul_apply_eq_comp] at h
  have hPx : U.starProjection x = 0 :=
    (U.starProjection_apply_eq_zero_iff).mpr hx
  rw [hPx, map_zero] at h
  exact h.symm

omit [CompleteSpace E] in
private theorem coe_compressOperator_apply_of_maps
    {U : Submodule ℂ E} [U.HasOrthogonalProjection] (K : E →L[ℂ] E)
    (hK : ∀ x ∈ U, K x ∈ U) (x : U) :
    ((compressOperator U K x : U) : E) = K (x : E) := by
  rw [compressOperator_eq_restrict_of_invariant K U hK]
  rfl

private theorem coe_blockCompression_apply_of_maps
    {Ω Γ : Submodule ℂ E} [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K : E →L[ℂ] E) (hK : ∀ x ∈ Γ, K x ∈ Ω) (x : Γ) :
    ((blockCompression Ω Γ K x : Ω) : E) = K (x : E) := by
  rw [blockCompression, Submodule.adjoint_subtypeL]
  exact Submodule.starProjection_eq_self_iff.mpr (hK (x : E) x.property)

private theorem blockCompression_adjoint_of_selfAdjoint
    {Ω Γ : Submodule ℂ E} [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K : E →L[ℂ] E) (hK : IsSelfAdjoint K) :
    (blockCompression Ω Γ K).adjoint = blockCompression Γ Ω K := by
  unfold blockCompression
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hK.adjoint_eq,
    ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] in
private theorem tanRep_maps_U
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : x ∈ U) : tanTwoBlockRepresentative U V x ∈ Uᗮ := by
  rw [tanTwoBlockRepresentative, diagonalPair]
  simp only [ContinuousLinearMap.comp_apply, add_apply]
  have hxU : U.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hxPerp : Uᗮ.starProjection x = 0 :=
    TauCeti.starProjection_orthogonal_eq_zero_of_mem hx
  rw [hxU, hxPerp, map_zero, map_zero, add_zero]
  exact Uᗮ.starProjection_apply_mem _

omit [CompleteSpace E] in
private theorem tanRep_maps_Uperp
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : x ∈ Uᗮ) : tanTwoBlockRepresentative U V x ∈ U := by
  rw [tanTwoBlockRepresentative, diagonalPair]
  simp only [ContinuousLinearMap.comp_apply, add_apply]
  have hxU : U.starProjection x = 0 := (U.starProjection_apply_eq_zero_iff).mpr hx
  have hxPerp : Uᗮ.starProjection x = x :=
    Submodule.starProjection_eq_self_iff.mpr hx
  rw [hxU, map_zero, map_zero, hxPerp, zero_add]
  have hUU : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  simpa only [hUU] using U.starProjection_apply_mem
    ((2 * (projectorDifference U V * doubleSecant U V)) x)

private theorem signedCosBlock_isUnit
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    IsUnit (compressOperator U (signedCosTwo U V)) := by
  let N := signedCosTwo U V
  let R := doubleSecant U V
  have hinv := isUnit_one_sub_two_mul_projectorDifference_sq_of_cos_two_ne_zero hcos
  have hNR : N * R = 1 := Ring.mul_inverse_cancel _ hinv
  have hRN : R * N = 1 := Ring.inverse_mul_cancel _ hinv
  have hNcomm := signedCosTwo_comm_starProjection (U := U) (V := V)
  have hcommBase : U.starProjection *
        (1 - 2 * (projectorDifference U V * projectorDifference U V)) =
      (1 - 2 * (projectorDifference U V * projectorDifference U V)) *
        U.starProjection := by
    simpa only [signedCosTwo] using hNcomm.symm
  have hRcomm : R * U.starProjection = U.starProjection * R := by
    simpa only [R, doubleSecant] using
      (inverse_comm_reflection hinv hcommBase).symm
  have hNU : ∀ x ∈ U, N x ∈ U := fun x hx =>
    maps_mem_of_comm_starProjection N hNcomm hx
  have hRU : ∀ x ∈ U, R x ∈ U := fun x hx =>
    maps_mem_of_comm_starProjection R hRcomm hx
  refine isUnit_iff_exists.mpr ⟨compressOperator U R, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    rw [mul_apply_eq_comp,
      coe_compressOperator_apply_of_maps N hNU,
      coe_compressOperator_apply_of_maps R hRU]
    have h := congrArg (fun T : E →L[ℂ] E => T (x : E)) hNR
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  · apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    rw [mul_apply_eq_comp,
      coe_compressOperator_apply_of_maps R hRU,
      coe_compressOperator_apply_of_maps N hNU]
    have h := congrArg (fun T : E →L[ℂ] E => T (x : E)) hRN
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

private theorem signedCosBlockOrthogonal_isUnit
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    IsUnit (compressOperator Uᗮ (signedCosTwo U V)) := by
  let N := signedCosTwo U V
  let R := doubleSecant U V
  have hinv := isUnit_one_sub_two_mul_projectorDifference_sq_of_cos_two_ne_zero hcos
  have hNR : N * R = 1 := Ring.mul_inverse_cancel _ hinv
  have hRN : R * N = 1 := Ring.inverse_mul_cancel _ hinv
  have hNcomm := signedCosTwo_comm_starProjection (U := U) (V := V)
  have hcommBase : U.starProjection *
        (1 - 2 * (projectorDifference U V * projectorDifference U V)) =
      (1 - 2 * (projectorDifference U V * projectorDifference U V)) *
        U.starProjection := by
    simpa only [signedCosTwo] using hNcomm.symm
  have hRcomm : R * U.starProjection = U.starProjection * R := by
    simpa only [R, doubleSecant] using
      (inverse_comm_reflection hinv hcommBase).symm
  have hNU : ∀ x ∈ Uᗮ, N x ∈ Uᗮ := fun x hx =>
    maps_mem_orthogonal_of_comm_starProjection N hNcomm hx
  have hRU : ∀ x ∈ Uᗮ, R x ∈ Uᗮ := fun x hx =>
    maps_mem_orthogonal_of_comm_starProjection R hRcomm hx
  refine isUnit_iff_exists.mpr ⟨compressOperator Uᗮ R, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    rw [mul_apply_eq_comp,
      coe_compressOperator_apply_of_maps N hNU,
      coe_compressOperator_apply_of_maps R hRU]
    have h := congrArg (fun T : E →L[ℂ] E => T (x : E)) hNR
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  · apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    rw [mul_apply_eq_comp,
      coe_compressOperator_apply_of_maps R hRU,
      coe_compressOperator_apply_of_maps N hNU]
    have h := congrArg (fun T : E →L[ℂ] E => T (x : E)) hRN
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

/-- The signed-cosine/tangent Pythagorean identity in the ambient algebra. -/
private theorem signedCosTwo_sq_mul_one_add_tanRep_sq
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    signedCosTwo U V * signedCosTwo U V *
        (1 + tanTwoBlockRepresentative U V * tanTwoBlockRepresentative U V) = 1 := by
  let D := projectorDifference U V
  let S := D * D
  let N := signedCosTwo U V
  let R := doubleSecant U V
  let L := tanTwoBlockRepresentative U V
  have hinv := isUnit_one_sub_two_mul_projectorDifference_sq_of_cos_two_ne_zero hcos
  have hNR : N * R = 1 := Ring.mul_inverse_cancel _ hinv
  have hN2R2 : (N * N) * (R * R) = 1 := by
    calc
      (N * N) * (R * R) = N * (N * R) * R := by noncomm_ring
      _ = N * R := by noncomm_ring [hNR]
      _ = 1 := hNR
  have hLsq := tanTwoBlockRepresentative_mul_self hinv
  have hNP : (N * N) * (S - S * S) = (S - S * S) * (N * N) := by
    dsimp [N, signedCosTwo, S]
    noncomm_ring
  have hpoly : N * N + 4 * (S - S * S) = 1 := by
    dsimp [N, signedCosTwo, S]
    rw [show (2 : E →L[ℂ] E) = 1 + 1 from (one_add_one_eq_two).symm,
      show (4 : E →L[ℂ] E) = 1 + 1 + 1 + 1 by norm_num]
    noncomm_ring
  rw [show L * L = 4 * ((S - S * S) * (R * R)) by
    simpa only [L, S, D, projectorDifference_sq] using hLsq]
  calc
    N * N * (1 + 4 * ((S - S * S) * (R * R))) =
        N * N + 4 * ((N * N) * ((S - S * S) * (R * R))) := by
      rw [mul_add, mul_one]
      noncomm_ring
    _ = N * N + 4 * ((S - S * S) * ((N * N) * (R * R))) := by
      rw [← mul_assoc (N * N) (S - S * S) (R * R), hNP,
        mul_assoc (S - S * S) (N * N) (R * R)]
    _ = N * N + 4 * (S - S * S) := by rw [hN2R2, mul_one]
    _ = 1 := hpoly

/-- Bounded pointwise form of Davis--Kahan equation (7.6).

The reflection commutation identity is projected to `Uᗮ` exactly as in the
unbounded `sylvester_offDiagonalPart_of_mem` theorem.  The signed cosine
normalization then turns the diagonal reflection block into `+N` on `U` and
`-N` on `Uᗮ`, which is the source of the two plus signs on the residual side.
-/
private theorem bounded_reflection_equation_on_U
    {A H Z N L : E →L[ℂ] E} {U : Submodule ℂ E}
    [U.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hcommZ : Z ∘L (A + H) = (A + H) ∘L Z)
    (hNL : N * L = U.offDiagonalPart Z)
    (hdiag : U.diagonalPart Z = U.reflectionOperator * N)
    (hNU : ∀ x ∈ U, N x ∈ U)
    (hNUperp : ∀ x ∈ Uᗮ, N x ∈ Uᗮ)
    (x : E) (hx : x ∈ U) :
    N (L (A x)) - A (N (L x)) = H (N x) + N (H x) := by
  let C : E →L[ℂ] E := U.diagonalPart Z
  let S : E →L[ℂ] E := U.offDiagonalPart Z
  have hAsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hAred : A.Reduces U := ContinuousLinearMap.IsSymmetric.reduces_of_invariant hAsym hAU
  have hAUperp : ∀ y ∈ Uᗮ, A y ∈ Uᗮ := hAred.2
  have hCU : C x ∈ U := by
    dsimp [C]
    exact TauCeti.diagonalPart_mem_of_mem U Z hx
  have hSU : S x ∈ Uᗮ := by
    dsimp [S]
    exact TauCeti.offDiagonalPart_mem_orthogonal_of_mem U Z hx
  have hsplit : Z x = C x + S x := by
    have h := congrArg (fun T : E →L[ℂ] E => T x)
      (TauCeti.diagonalPart_add_offDiagonalPart U Z)
    simpa only [add_apply, C, S] using h.symm
  have hAsplit : A (Z x) = A (C x) + A (S x) := by
    rw [hsplit, map_add]
  have hHsplit : H (Z x) = H (C x) + H (S x) := by
    rw [hsplit, map_add]
  have hACU : A (C x) ∈ U := hAU _ hCU
  have hASU : A (S x) ∈ Uᗮ := hAUperp _ hSU
  have hHCU : H (C x) ∈ Uᗮ := hHU _ hCU
  have hHSU : H (S x) ∈ U := hHUperp _ hSU
  have hAxU : A x ∈ U := hAU _ hx
  have hHxU : H x ∈ Uᗮ := hHU _ hx
  have hcomm := congrArg (fun T : E →L[ℂ] E => T x) hcommZ.symm
  simp only [ContinuousLinearMap.comp_apply, add_apply, map_add] at hcomm
  have hproj := congrArg Uᗮ.starProjection hcomm
  rw [map_add, map_add, hAsplit, hHsplit, map_add, map_add,
    TauCeti.starProjection_orthogonal_eq_zero_of_mem hACU,
    Submodule.starProjection_eq_self_iff.mpr hASU,
    Submodule.starProjection_eq_self_iff.mpr hHCU,
    TauCeti.starProjection_orthogonal_eq_zero_of_mem hHSU,
    ← TauCeti.offDiagonalPart_apply_of_mem U Z hAxU,
    ← TauCeti.diagonalPart_apply_of_mem_orthogonal U Z hHxU] at hproj
  have hblock : A (S x) + H (C x) = S (A x) + C (H x) := by
    simpa only [zero_add, add_zero, C, S] using hproj
  have hS (y : E) : S y = N (L y) := by
    have h := congrArg (fun T : E →L[ℂ] E => T y) hNL
    simpa only [mul_apply_eq_comp, S] using h.symm
  have hCx : C x = N x := by
    have h := congrArg (fun T : E →L[ℂ] E => T x) hdiag
    simp only [mul_apply_eq_comp] at h
    have hreflect : U.reflectionOperator (N x) = N x := by
      rw [Submodule.reflectionOperator_apply,
        Submodule.starProjection_eq_self_iff.mpr (hNU x hx)]
      module
    exact h.trans hreflect
  have hCHx : C (H x) = -N (H x) := by
    have h := congrArg (fun T : E →L[ℂ] E => T (H x)) hdiag
    simp only [mul_apply_eq_comp] at h
    have hreflect : U.reflectionOperator (N (H x)) = -N (H x) := by
      rw [Submodule.reflectionOperator_apply,
        (U.starProjection_apply_eq_zero_iff).mpr (hNUperp (H x) hHxU)]
      module
    exact h.trans hreflect
  rw [hS, hS, hCx, hCHx] at hblock
  have hblock' :
      N (L (A x)) = A (N (L x)) + H (N x) + N (H x) := by
    calc
      N (L (A x)) = (N (L (A x)) + -N (H x)) + N (H x) := by module
      _ = (A (N (L x)) + H (N x)) + N (H x) := by rw [← hblock]
  rw [hblock']
  module

private theorem reflection_block_data
    {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k
          (blockCompression Uᗮ U (tanTwoBlockRepresentative U V)) ≤
        2 * kyFanApproximationGauge k (blockCompression Uᗮ U H) := by
  let N : E →L[ℂ] E := signedCosTwo U V
  let L : E →L[ℂ] E := tanTwoBlockRepresentative U V
  let A0 : U →L[ℂ] U := compressOperator U A
  let A1 : Uᗮ →L[ℂ] Uᗮ := compressOperator Uᗮ A
  let B : U →L[ℂ] Uᗮ := blockCompression Uᗮ U H
  let T : U →L[ℂ] Uᗮ := blockCompression Uᗮ U L
  let C0 : U →L[ℂ] U := compressOperator U N
  let C1 : Uᗮ →L[ℂ] Uᗮ := compressOperator Uᗮ N
  have hNcomm := signedCosTwo_comm_starProjection (U := U) (V := V)
  have hNU : ∀ x ∈ U, N x ∈ U := fun x hx =>
    maps_mem_of_comm_starProjection N hNcomm hx
  have hNUperp : ∀ x ∈ Uᗮ, N x ∈ Uᗮ := fun x hx =>
    maps_mem_orthogonal_of_comm_starProjection N hNcomm hx
  have hLU : ∀ x ∈ U, L x ∈ Uᗮ := fun x hx => tanRep_maps_U (U := U) (V := V) hx
  have hLUperp : ∀ x ∈ Uᗮ, L x ∈ U := fun x hx => tanRep_maps_Uperp (U := U) (V := V) hx
  have hAred : A.Reduces U := by
    have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
    exact ContinuousLinearMap.IsSymmetric.reduces_of_invariant hs hAU
  have hAUperp : ∀ x ∈ Uᗮ, A x ∈ Uᗮ := hAred.2
  have hA0sa : IsSelfAdjoint A0 := by
    dsimp [A0]
    exact isSelfAdjoint_compressOperator hA U
  have hA1sa : IsSelfAdjoint A1 := by
    dsimp [A1]
    exact isSelfAdjoint_compressOperator hA Uᗮ
  have hNsa : IsSelfAdjoint N := by simpa only [N] using
    (signedCosTwo_selfAdjoint (U := U) (V := V))
  have hC0sa : IsSelfAdjoint C0 := by
    dsimp [C0]
    exact isSelfAdjoint_compressOperator hNsa U
  have hC1sa : IsSelfAdjoint C1 := by
    dsimp [C1]
    exact isSelfAdjoint_compressOperator hNsa Uᗮ
  have hC0unit : IsUnit C0 := by
    simpa only [C0, N] using signedCosBlock_isUnit (U := U) (V := V) hcos
  have hC1unit : IsUnit C1 := by
    simpa only [C1, N] using signedCosBlockOrthogonal_isUnit (U := U) (V := V) hcos
  have hA0high : ∀ x : U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A0 x, x⟫_ℂ := by
    intro x
    have h := hUhigh (x : E) x.property
    have hcoe : ((A0 x : U) : E) = A (x : E) := by
      dsimp [A0]
      exact coe_compressOperator_apply_of_maps A hAU x
    simpa [Submodule.coe_norm, Submodule.coe_inner, hcoe] using h
  have hA1low : ∀ x : Uᗮ, RCLike.re ⟪A1 x, x⟫_ℂ ≤ a * ‖x‖ ^ 2 := by
    intro x
    have h := hUperpLow (x : E) x.property
    have hcoe : ((A1 x : Uᗮ) : E) = A (x : E) := by
      dsimp [A1]
      exact coe_compressOperator_apply_of_maps A hAUperp x
    simpa [Submodule.coe_norm, Submodule.coe_inner, hcoe] using h
  have hLsa : IsSelfAdjoint L := by
    have hinv := isUnit_one_sub_two_mul_projectorDifference_sq_of_cos_two_ne_zero hcos
    simpa only [L] using isSelfAdjoint_tanTwoBlockRepresentative hinv
  have hTadj : T.adjoint = blockCompression U Uᗮ L := by
    dsimp [T]
    exact blockCompression_adjoint_of_selfAdjoint L hLsa
  have hglobal := signedCosTwo_sq_mul_one_add_tanRep_sq (U := U) (V := V) hcos
  have hgram0 : C0.adjoint ∘L C0 ∘L (1 + T.adjoint ∘L T) = 1 := by
    rw [hC0sa.adjoint_eq]
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    have hLx : L (x : E) ∈ Uᗮ := hLU (x : E) x.property
    have hLLx : L (L (x : E)) ∈ U := hLUperp _ hLx
    have happ := congrArg (fun M : E →L[ℂ] E => M (x : E)) hglobal
    simp only [mul_apply_eq_comp, add_apply, one_apply_eq_self] at happ
    have hTx : ((T x : Uᗮ) : E) = L (x : E) := by
      dsimp [T]
      exact coe_blockCompression_apply_of_maps L hLU x
    have hTTx : ((T.adjoint (T x) : U) : E) = L (L (x : E)) := by
      rw [hTadj]
      calc
        (((blockCompression U Uᗮ L) (T x) : U) : E) =
            L ((T x : Uᗮ) : E) :=
          coe_blockCompression_apply_of_maps L hLUperp (T x)
        _ = L (L (x : E)) := congrArg L hTx
    have harg : (((x + T.adjoint (T x) : U) : E)) =
        (x : E) + L (L (x : E)) := by
      change (x : E) + ((T.adjoint (T x) : U) : E) =
        (x : E) + L (L (x : E))
      rw [hTTx]
    have hinner : ((C0 (x + T.adjoint (T x)) : U) : E) =
        N ((x : E) + L (L (x : E))) := by
      calc
        ((C0 (x + T.adjoint (T x)) : U) : E) =
            N (((x + T.adjoint (T x) : U) : E)) := by
          dsimp [C0]
          exact coe_compressOperator_apply_of_maps N hNU _
        _ = N ((x : E) + L (L (x : E))) := congrArg N harg
    have houter : ((C0 (C0 (x + T.adjoint (T x))) : U) : E) =
        N (N ((x : E) + L (L (x : E)))) := by
      calc
        ((C0 (C0 (x + T.adjoint (T x))) : U) : E) =
            N ((C0 (x + T.adjoint (T x)) : U) : E) := by
          dsimp [C0]
          exact coe_compressOperator_apply_of_maps N hNU _
        _ = N (N ((x : E) + L (L (x : E)))) := congrArg N hinner
    simp only [ContinuousLinearMap.comp_apply, add_apply, one_apply_eq_self]
    exact houter.trans happ
  have hgram1 : C1.adjoint ∘L C1 ∘L (1 + T ∘L T.adjoint) = 1 := by
    rw [hC1sa.adjoint_eq]
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    have hLx : L (x : E) ∈ U := hLUperp (x : E) x.property
    have hLLx : L (L (x : E)) ∈ Uᗮ := hLU _ hLx
    have happ := congrArg (fun M : E →L[ℂ] E => M (x : E)) hglobal
    simp only [mul_apply_eq_comp, add_apply, one_apply_eq_self] at happ
    have hTadjx : ((T.adjoint x : U) : E) = L (x : E) := by
      rw [hTadj]
      exact coe_blockCompression_apply_of_maps L hLUperp x
    have hTTadjx : ((T (T.adjoint x) : Uᗮ) : E) = L (L (x : E)) := by
      calc
        ((T (T.adjoint x) : Uᗮ) : E) =
            L ((T.adjoint x : U) : E) := by
          dsimp [T]
          exact coe_blockCompression_apply_of_maps L hLU (T.adjoint x)
        _ = L (L (x : E)) := congrArg L hTadjx
    have harg : (((x + T (T.adjoint x) : Uᗮ) : E)) =
        (x : E) + L (L (x : E)) := by
      change (x : E) + ((T (T.adjoint x) : Uᗮ) : E) =
        (x : E) + L (L (x : E))
      rw [hTTadjx]
    have hinner : ((C1 (x + T (T.adjoint x)) : Uᗮ) : E) =
        N ((x : E) + L (L (x : E))) := by
      calc
        ((C1 (x + T (T.adjoint x)) : Uᗮ) : E) =
            N (((x + T (T.adjoint x) : Uᗮ) : E)) := by
          dsimp [C1]
          exact coe_compressOperator_apply_of_maps N hNUperp _
        _ = N ((x : E) + L (L (x : E))) := congrArg N harg
    have houter : ((C1 (C1 (x + T (T.adjoint x))) : Uᗮ) : E) =
        N (N ((x : E) + L (L (x : E)))) := by
      calc
        ((C1 (C1 (x + T (T.adjoint x))) : Uᗮ) : E) =
            N ((C1 (x + T (T.adjoint x)) : Uᗮ) : E) := by
          dsimp [C1]
          exact coe_compressOperator_apply_of_maps N hNUperp _
        _ = N (N ((x : E) + L (L (x : E)))) := congrArg N hinner
    simp only [ContinuousLinearMap.comp_apply, add_apply, one_apply_eq_self]
    exact houter.trans happ
  have heq76 : (C1 ∘L T) ∘L A0 - A1 ∘L (C1 ∘L T) =
      B ∘L C0 + C1 ∘L B := by
    -- Equation (7.6), obtained by projecting the reflection commutation identity.
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    have hAsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
    have hAHsa := hA.add hH
    have hAHsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAHsa
    have hVred : (A + H).Reduces V :=
      ContinuousLinearMap.IsSymmetric.reduces_of_invariant hAHsym hAplusH_V
    have hcommZ := Submodule.reflectionOperator_comm_of_reduces (A + H) V hVred
    -- Reduce the projected reflection identity to the explicit `N * L` blocks.
    have hinv := isUnit_one_sub_two_mul_projectorDifference_sq_of_cos_two_ne_zero hcos
    have hp := starProjection_idem_reflection U
    have hkey := projectorDifference_anticommutator (U := U) (V := V)
    have hQ : V.starProjection =
        projectorDifference U V + U.starProjection := by
      rw [projectorDifference]
      abel
    have hD2p :
        U.starProjection *
            (projectorDifference U V * projectorDifference U V) =
          (projectorDifference U V * projectorDifference U V) *
            U.starProjection :=
      proj_comm_sq_reflection hp hkey
    have hNR : signedCosTwo U V * doubleSecant U V = 1 := by
      unfold signedCosTwo doubleSecant
      exact Ring.mul_inverse_cancel _ hinv
    have hND : signedCosTwo U V * projectorDifference U V =
        projectorDifference U V * signedCosTwo U V := by
      unfold signedCosTwo
      noncomm_ring
    have hNP : signedCosTwo U V * U.starProjection =
        U.starProjection * signedCosTwo U V :=
      signedCosTwo_comm_starProjection (U := U) (V := V)
    have hNq : signedCosTwo U V * (1 - U.starProjection) =
        (1 - U.starProjection) * signedCosTwo U V := by
      calc
        signedCosTwo U V * (1 - U.starProjection) =
            signedCosTwo U V - signedCosTwo U V * U.starProjection := by
          noncomm_ring
        _ = signedCosTwo U V - U.starProjection * signedCosTwo U V := by rw [hNP]
        _ = (1 - U.starProjection) * signedCosTwo U V := by
          noncomm_ring
    have hXlower :
        signedCosTwo U V *
            ((1 - U.starProjection) * projectorDifference U V * U.starProjection) =
          ((1 - U.starProjection) * projectorDifference U V * U.starProjection) *
            signedCosTwo U V := by
      calc
        signedCosTwo U V *
              ((1 - U.starProjection) * projectorDifference U V * U.starProjection) =
            (signedCosTwo U V * (1 - U.starProjection)) *
              projectorDifference U V * U.starProjection := by
          noncomm_ring
        _ = ((1 - U.starProjection) * signedCosTwo U V) *
              projectorDifference U V * U.starProjection := by rw [hNq]
        _ = (1 - U.starProjection) *
              (signedCosTwo U V * projectorDifference U V) * U.starProjection := by
          noncomm_ring
        _ = (1 - U.starProjection) *
              (projectorDifference U V * signedCosTwo U V) * U.starProjection := by
          rw [hND]
        _ = (1 - U.starProjection) * projectorDifference U V *
              (signedCosTwo U V * U.starProjection) := by
          noncomm_ring
        _ = (1 - U.starProjection) * projectorDifference U V *
              (U.starProjection * signedCosTwo U V) := by rw [hNP]
        _ = ((1 - U.starProjection) * projectorDifference U V * U.starProjection) *
              signedCosTwo U V := by
          noncomm_ring
    have hXupper :
        signedCosTwo U V *
            (U.starProjection * projectorDifference U V * (1 - U.starProjection)) =
          (U.starProjection * projectorDifference U V * (1 - U.starProjection)) *
            signedCosTwo U V := by
      calc
        signedCosTwo U V *
              (U.starProjection * projectorDifference U V * (1 - U.starProjection)) =
            (signedCosTwo U V * U.starProjection) *
              projectorDifference U V * (1 - U.starProjection) := by
          noncomm_ring
        _ = (U.starProjection * signedCosTwo U V) *
              projectorDifference U V * (1 - U.starProjection) := by rw [hNP]
        _ = U.starProjection *
              (signedCosTwo U V * projectorDifference U V) * (1 - U.starProjection) := by
          noncomm_ring
        _ = U.starProjection *
              (projectorDifference U V * signedCosTwo U V) * (1 - U.starProjection) := by
          rw [hND]
        _ = U.starProjection * projectorDifference U V *
              (signedCosTwo U V * (1 - U.starProjection)) := by
          noncomm_ring
        _ = U.starProjection * projectorDifference U V *
              ((1 - U.starProjection) * signedCosTwo U V) := by rw [hNq]
        _ = (U.starProjection * projectorDifference U V * (1 - U.starProjection)) *
              signedCosTwo U V := by
          noncomm_ring
    have hXcomm :
        signedCosTwo U V *
            ((1 - U.starProjection) * projectorDifference U V * U.starProjection +
              U.starProjection * projectorDifference U V *
                (1 - U.starProjection)) =
          ((1 - U.starProjection) * projectorDifference U V * U.starProjection +
              U.starProjection * projectorDifference U V *
                (1 - U.starProjection)) * signedCosTwo U V := by
      rw [mul_add, add_mul, hXlower, hXupper]
    have hoff : U.offDiagonalPart V.reflectionOperator =
        2 * ((1 - U.starProjection) * projectorDifference U V * U.starProjection +
          U.starProjection * projectorDifference U V *
            (1 - U.starProjection)) := by
      rw [Submodule.offDiagonalPart_eq, Submodule.diagonalPart_eq,
        Submodule.reflectionOperator_eq_two_smul_sub_id V]
      simp only [two_smul, Submodule.starProjection_orthogonal', comp_eq_mul_reflection]
      rw [hQ, ← ContinuousLinearMap.one_def]
      noncomm_ring [hp]
    have hNL : N * L = U.offDiagonalPart V.reflectionOperator := by
      change signedCosTwo U V * tanTwoBlockRepresentative U V =
        U.offDiagonalPart V.reflectionOperator
      rw [tanTwoBlockRepresentative_eq hinv, hoff]
      calc
        signedCosTwo U V *
              (2 * (((1 - U.starProjection) * projectorDifference U V *
                    U.starProjection +
                  U.starProjection * projectorDifference U V *
                    (1 - U.starProjection)) * doubleSecant U V)) =
            2 * ((signedCosTwo U V *
                ((1 - U.starProjection) * projectorDifference U V *
                    U.starProjection +
                  U.starProjection * projectorDifference U V *
                    (1 - U.starProjection))) * doubleSecant U V) := by
              noncomm_ring
        _ = 2 * ((((1 - U.starProjection) * projectorDifference U V *
                    U.starProjection +
                  U.starProjection * projectorDifference U V *
                    (1 - U.starProjection)) * signedCosTwo U V) *
                  doubleSecant U V) := by rw [hXcomm]
        _ = 2 * (((1 - U.starProjection) * projectorDifference U V *
                    U.starProjection +
                  U.starProjection * projectorDifference U V *
                    (1 - U.starProjection)) *
                  (signedCosTwo U V * doubleSecant U V)) := by
              noncomm_ring
        _ = 2 * ((1 - U.starProjection) * projectorDifference U V *
                    U.starProjection +
                  U.starProjection * projectorDifference U V *
                    (1 - U.starProjection)) := by rw [hNR, mul_one]
    have hdiag : U.diagonalPart V.reflectionOperator =
        U.reflectionOperator * N := by
      simpa only [N] using
        (diagonalPart_reflection_eq_reflection_mul_signedCosTwo (U := U) (V := V))
    have hEq := bounded_reflection_equation_on_U hA hAU hHU hHUperp
      hcommZ hNL hdiag hNU hNUperp (x : E) x.property
    have h0 : ((C1 (T (A0 x)) : Uᗮ) : E) = N (L (A (x : E))) := by
      dsimp [C1, T, A0]
      rw [coe_compressOperator_apply_of_maps N hNUperp,
        coe_blockCompression_apply_of_maps L hLU,
        coe_compressOperator_apply_of_maps A hAU]
    have h1 : ((A1 (C1 (T x)) : Uᗮ) : E) = A (N (L (x : E))) := by
      dsimp [A1, C1, T]
      rw [coe_compressOperator_apply_of_maps A hAUperp,
        coe_compressOperator_apply_of_maps N hNUperp,
        coe_blockCompression_apply_of_maps L hLU]
    have h2 : ((B (C0 x) : Uᗮ) : E) = H (N (x : E)) := by
      dsimp [B, C0]
      rw [coe_blockCompression_apply_of_maps H hHU,
        coe_compressOperator_apply_of_maps N hNU]
    have h3 : ((C1 (B x) : Uᗮ) : E) = N (H (x : E)) := by
      dsimp [C1, B]
      rw [coe_compressOperator_apply_of_maps N hNUperp,
        coe_blockCompression_apply_of_maps H hHU]
    simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply]
    change ((C1 (T (A0 x)) : Uᗮ) : E) - ((A1 (C1 (T x)) : Uᗮ) : E) =
      ((B (C0 x) : Uᗮ) : E) + ((C1 (B x) : Uᗮ) : E)
    rw [h0, h1, h2, h3]
    exact hEq
  exact reflectionTangent_all_kyFan A0 A1 B T C0 C1
    hA0sa hA1sa hC0sa hC1sa hC0unit hC1unit hab hA0high hA1low
    hgram0 hgram1 heq76

/-- **Section 7 pole exclusion from the printed ordered gap.**

For a bounded self-adjoint `A`, the full-domain cutoff is simply `P_U`.  The
unbounded Section 7 pole estimate therefore applies without an auxiliary
limit construction and gives `‖offdiag_U(2P_V-1)‖ < 1`.  The reflection
Pythagorean identity makes its diagonal square invertible; after removing the
reflection through `U`, this is exactly invertibility of the signed
`cos 2Θ = 1 - 2(P_V-P_U)^2`.  Hence no principal angle is `π/4`.

This theorem is deliberately internal: the source-facing endpoint below
states the spectral hypotheses printed in Section 2 and derives these form
bounds before invoking it. -/
private theorem cos_two_ne_zero_of_ordered_form_gap_offDiagonal
    {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUlow : ∀ x ∈ U, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hUperpHigh : ∀ x ∈ Uᗮ, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0 := by
  let Ap : E →ₗ.[ℂ] E := A.toLinearMap.toPMap ⊤
  have hAred : A.Reduces U := by
    have hAsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
    exact ContinuousLinearMap.IsSymmetric.reduces_of_invariant hAsym hAU
  have hAUperp : ∀ x ∈ Uᗮ, A x ∈ Uᗮ := hAred.2
  have hred : TauCeti.LinearPMap.ReducesSubspace Ap U := by
    refine TauCeti.LinearPMap.ReducesSubspace.of_components ?_ ?_ ?_ ?_
    · intro x
      exact Submodule.mem_top
    · intro x
      exact Submodule.mem_top
    · intro x hx
      change A (x : E) ∈ U
      exact hAU _ hx
    · intro x hx
      change A (x : E) ∈ Uᗮ
      exact hAUperp _ hx
  have hBodd : TauCeti.IsOddFor U H := ⟨hHU, hHUperp⟩
  let Z : E →L[ℂ] E := V.reflectionOperator
  have hZsa : IsSelfAdjoint Z := by
    simpa only [Z] using isSelfAdjoint_reflectionOperator V
  have hZ2 : Z * Z = 1 := by
    dsimp [Z]
    rw [ContinuousLinearMap.mul_def, Submodule.reflectionOperator_involutive,
      ← ContinuousLinearMap.one_def]
  have hZdom : TauCeti.LinearPMap.MapsDomainTo Ap Ap Z := by
    intro x
    exact Submodule.mem_top
  have hAHsa : IsSelfAdjoint (A + H) := hA.add hH
  have hAHsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAHsa
  have hVred : (A + H).Reduces V :=
    ContinuousLinearMap.IsSymmetric.reduces_of_invariant hAHsym hAplusH_V
  have hcomm : V.reflectionOperator ∘L (A + H) =
      (A + H) ∘L V.reflectionOperator :=
    Submodule.reflectionOperator_comm_of_reduces (A + H) V hVred
  have hZcomm : ∀ x : Ap.domain,
      Ap ⟨Z (x : E), hZdom x⟩ + H (Z (x : E)) =
        Z (Ap x) + Z (H (x : E)) := by
    intro x
    have hx := congrArg (fun T : E →L[ℂ] E => T (x : E)) hcomm
    change A (Z (x : E)) + H (Z (x : E)) =
      Z (A (x : E)) + Z (H (x : E))
    simpa only [Z, ContinuousLinearMap.comp_apply, add_apply, map_add] using hx.symm
  have hUa : ∀ x : Ap.domain, (x : E) ∈ U →
      (⟪Ap x, (x : E)⟫_ℂ).re ≤ a * ‖(x : E)‖ ^ 2 := by
    intro x hx
    change RCLike.re ⟪A (x : E), (x : E)⟫_ℂ ≤ a * ‖(x : E)‖ ^ 2
    exact hUlow _ hx
  have hUb : ∀ x : Ap.domain, (x : E) ∈ Uᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ (⟪Ap x, (x : E)⟫_ℂ).re := by
    intro x hx
    change b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A (x : E), (x : E)⟫_ℂ
    exact hUperpHigh _ hx
  let Ω : TauCeti.BoundedCutoff Ap U ‖A‖ := {
    toProj := U.starProjection
    isSelfAdjoint := isSelfAdjoint_starProjection U
    isIdempotentElem := U.isIdempotentElem_starProjection
    mem_subspace := fun v => U.starProjection_apply_mem v
    mem_domain := fun _ => Submodule.mem_top
    norm_apply_le := fun v => by
      change ‖A (U.starProjection v)‖ ≤ ‖A‖ * ‖U.starProjection v‖
      exact A.le_opNorm _
    apply_mem_range := fun v => by
      change U.starProjection (A (U.starProjection v)) = A (U.starProjection v)
      exact Submodule.starProjection_eq_self_iff.mpr
        (hAU _ (U.starProjection_apply_mem v))
  }
  have hconv : ∀ x ∈ U,
      Filter.Tendsto (fun _ : ℕ => Ω.toProj x) Filter.atTop (nhds x) := by
    intro x hx
    have hxproj : Ω.toProj x = x := by
      change U.starProjection x = x
      exact Submodule.starProjection_eq_self_iff.mpr hx
    simpa only [hxproj] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x))
  have hS1 : ‖U.offDiagonalPart Z‖ < 1 :=
    TauCeti.norm_offDiagonalPart_lt_one_of_tendsto
      hred hBodd hZsa hZ2 hZdom hZcomm hUa hUb
      (fun _ : ℕ => ‖A‖) (fun _ => Ω) (fun _ => norm_nonneg A) hab hconv
  have hSS : ‖U.offDiagonalPart Z * U.offDiagonalPart Z‖ < 1 := by
    have hmul := norm_mul_le (U.offDiagonalPart Z) (U.offDiagonalPart Z)
    nlinarith [norm_nonneg (U.offDiagonalPart Z)]
  have hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z) := by
    have hsum := TauCeti.diagonalPart_sq_add_offDiagonalPart_sq (U := U) hZ2
    have hrewrite : U.diagonalPart Z * U.diagonalPart Z =
        1 - U.offDiagonalPart Z * U.offDiagonalPart Z := by
      rw [← hsum]
      abel
    rw [hrewrite]
    exact ⟨Units.oneSub _ hSS, rfl⟩
  let N : E →L[ℂ] E := signedCosTwo U V
  have hdiag : U.diagonalPart Z = U.reflectionOperator * N := by
    simpa only [Z, N] using
      (diagonalPart_reflection_eq_reflection_mul_signedCosTwo (U := U) (V := V))
  have hNP : N * U.starProjection = U.starProjection * N := by
    simpa only [N] using signedCosTwo_comm_starProjection (U := U) (V := V)
  have hJN : U.reflectionOperator * N = N * U.reflectionOperator := by
    rw [Submodule.reflectionOperator_eq_two_smul_sub_id U]
    simp only [two_smul]
    noncomm_ring [hNP]
  have hJ2 : U.reflectionOperator * U.reflectionOperator = 1 := by
    rw [ContinuousLinearMap.mul_def, Submodule.reflectionOperator_involutive,
      ← ContinuousLinearMap.one_def]
  have hdiagSq : U.diagonalPart Z * U.diagonalPart Z = N * N := by
    rw [hdiag]
    calc
      (U.reflectionOperator * N) * (U.reflectionOperator * N) =
          U.reflectionOperator * (N * U.reflectionOperator) * N := by
            simp only [mul_assoc]
      _ = U.reflectionOperator * (U.reflectionOperator * N) * N := by
            rw [← hJN]
      _ = (U.reflectionOperator * U.reflectionOperator) * N * N := by
            simp only [mul_assoc]
      _ = N * N := by
            rw [hJ2, one_mul]
  have hNN : IsUnit (N * N) := by
    rw [← hdiagSq]
    exact hCC
  have hN : IsUnit N := ((Commute.refl N).isUnit_mul_iff.mp hNN).1
  exact cos_two_ne_zero_of_isUnit_one_sub_two_mul_projectorDifference_sq
    (by simpa only [N, signedCosTwo] using hN)

/-- **Branch-free Section 7 directed-corner estimate, lower-residual form.** -/
theorem tanTwoTheta_directed_boundedResidual_branchFree_blockRepresentative_kyFan_complex
    {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k
          (projectionBlock Uᗮ U
            (2 * (projectorDifference U V * doubleSecant U V))) ≤
        2 * kyFanApproximationGauge k (projectionBlock Uᗮ U H) := by
  intro k
  have h := reflection_block_data hA hH hAU hAplusH_V hab hUhigh hUperpLow
    hHU hHUperp hcos k
  rw [← (projectionBlock_same_compression Uᗮ U
      (tanTwoBlockRepresentative U V)).kyFanApproximationGauge_eq k,
    tanTwoBlockRepresentative] at h
  rw [projectionBlock_diagonalPair_lower_reflection U,
    ← (projectionBlock_same_compression Uᗮ U H).kyFanApproximationGauge_eq k] at h
  exact h

/-- **Branch-free Section 7 directed-corner estimate for every source
unitarily invariant norm.**

This is the arbitrary-UI-norm upgrade of
`tanTwoTheta_directed_boundedResidual_branchFree_blockRepresentative_kyFan_complex`.  The operator on the
left is the paper's directed `tan 2Θ₀` corner representative and the operator on
the right is the directed residual corner.  Pole exclusion is still an explicit
input at this layer; the source-facing theorem below derives it from the printed
ordered spectral gap and off-diagonal hypotheses. -/
theorem tanTwoTheta_directed_boundedResidual_branchFree_blockRepresentative_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0)
    (hRmem : N.Mem (projectionBlock Uᗮ U H)) :
    N.Mem
        (projectionBlock Uᗮ U
          (2 * (projectorDifference U V * doubleSecant U V))) ∧
      (b - a) * N.gauge
          (projectionBlock Uᗮ U
            (2 * (projectorDifference U V * doubleSecant U V))) ≤
        2 * N.gauge (projectionBlock Uᗮ U H) := by
  have hhalf : (0 : ℝ) < (b - a) / 2 := by linarith
  have hscaled : ∀ k : ℕ,
      (b - a) / 2 * kyFanApproximationGauge k
          (projectionBlock Uᗮ U
            (2 * (projectorDifference U V * doubleSecant U V))) ≤
        kyFanApproximationGauge k (projectionBlock Uᗮ U H) := by
    intro k
    have h := tanTwoTheta_directed_boundedResidual_branchFree_blockRepresentative_kyFan_complex
      hA hH hAU hAplusH_V hab hUhigh hUperpLow hHU hHUperp hcos k
    linarith
  obtain ⟨hmem, hbound⟩ :=
    N.mul_gauge_le_of_all_mul_kyFan_le hhalf hRmem hscaled
  exact ⟨hmem, by linarith⟩

/-- The same branch-free corner estimate in the upper-residual orientation
consumed by the ambient Lemma-6.1 assembly.  This rewrite costs **no factor**:
it is only adjoint invariance of approximation numbers. -/
theorem tanTwoTheta_directed_boundedResidual_branchFree_blockRepresentative_kyFan_complex_upperCorner
    {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k
          (projectionBlock Uᗮ U
            (2 * (projectorDifference U V * doubleSecant U V))) ≤
        2 * kyFanApproximationGauge k (projectionBlock Uᗮᗮ Uᗮ H) := by
  intro k
  have h := tanTwoTheta_directed_boundedResidual_branchFree_blockRepresentative_kyFan_complex
    hA hH hAU hAplusH_V hab hUhigh hUperpLow hHU hHUperp hcos k
  rw [← kyFan_lowerBlock_eq_upperBlock_reflection H hH k]
  exact h

/-- **M30: branch-free ambient `tan 2Theta`, every Ky Fan gauge.**

No `IsQuarterAcute`, no graph coordinate, and no placement hypothesis on the
blocks of `A+H`.  The only angle hypothesis is the paper's own pole exclusion
`cos 2theta != 0`. -/
theorem tanTwoTheta_ambient_bounded_branchFree_orderedForm_kyFan_complex
    {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    ∀ k : ℕ,
      (b - a) * kyFanApproximationGauge k (absTanTwoAngleOperatorC U V) ≤
        2 * kyFanApproximationGauge k H := by
  exact tanTwoTheta_ambient_bounded_branchFree_kyFan_complex_of_corner hH hab hcos
    (tanTwoTheta_directed_boundedResidual_branchFree_blockRepresentative_kyFan_complex_upperCorner
      hA hH hAU hAplusH_V hab hUhigh hUperpLow hHU hHUperp hcos)

/-- **M30: source unitarily-invariant-norm form.** -/
theorem tanTwoTheta_ambient_bounded_branchFree_orderedForm_symmetricNorming_complex_of_poleExclusion
    (N : SymmetricNormingFunction)
    {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0)
    (hHmem : N.Mem H) :
    N.Mem (absTanTwoAngleOperatorC U V) ∧
      (b - a) * N.gauge (absTanTwoAngleOperatorC U V) ≤ 2 * N.gauge H := by
  exact tanTwoTheta_ambient_bounded_branchFree_symmetricNorming_complex_of_corner N hH hab hcos
    (tanTwoTheta_directed_boundedResidual_branchFree_blockRepresentative_kyFan_complex_upperCorner
      hA hH hAU hAplusH_V hab hUhigh hUperpLow hHU hHUperp hcos) hHmem

/-- **Davis--Kahan 1970, Section 2 `tan 2Θ₀`, directed residual
conclusion, exactly from its printed hypotheses.**

The source assumes `spectrum(A₀) ⊆ [β, α]`,
`spectrum(A₁) ⊆ [α + δ, ∞)`, `δ > 0`, and `H₀ = H₁ = 0`.  For every source
unitarily invariant norm it concludes

`δ ‖tan(2Θ₀)‖ ≤ 2 ‖R‖`.

Here the two displayed operators are the canonical directed projection-block
representatives of `tan(2Θ₀)` and of the residual.  They have exactly the
singular data seen by the paper's norm.  There is deliberately no caller
supplied quarter-angle branch, no `cos (2θ) ≠ 0` hypothesis, and no placement
hypothesis on the blocks of `A+H`; pole exclusion is derived internally by the
Section 7 reflection argument. -/
theorem tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {β α δ : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hRmem : N.Mem (projectionBlock Uᗮ U H)) :
    N.Mem
        (projectionBlock Uᗮ U
          (2 * (projectorDifference U V * doubleSecant U V))) ∧
      δ * N.gauge
          (projectionBlock Uᗮ U
            (2 * (projectorDifference U V * doubleSecant U V))) ≤
        2 * N.gauge (projectionBlock Uᗮ U H) := by
  have hAred : A.Reduces U := by
    have hAsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
    exact ContinuousLinearMap.IsSymmetric.reduces_of_invariant hAsym hAU
  have hAUperp : ∀ x ∈ Uᗮ, A x ∈ Uᗮ := hAred.2
  have hA0sa : IsSelfAdjoint (compressOperator U A) :=
    isSelfAdjoint_compressOperator hA U
  have hA1sa : IsSelfAdjoint (compressOperator Uᗮ A) :=
    isSelfAdjoint_compressOperator hA Uᗮ
  have hA0upper : spectrum ℝ (compressOperator U A) ⊆ Set.Iic α :=
    fun r hr => (hA0spec hr).2
  have hUlow : ∀ x ∈ U,
      RCLike.re ⟪A x, x⟫_ℂ ≤ α * ‖x‖ ^ 2 := by
    intro x hx
    let xu : U := ⟨x, hx⟩
    have h := TauCeti.SpectralOrder.re_inner_le_of_spectrum_subset_Iic
      (compressOperator U A) hA0sa hA0upper xu
    have hcoe : ((compressOperator U A xu : U) : E) = A (x : E) :=
      coe_compressOperator_apply_of_maps A hAU xu
    simpa [Submodule.coe_norm, Submodule.coe_inner, hcoe] using h
  have hUperpHigh : ∀ x ∈ Uᗮ,
      (α + δ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ := by
    intro x hx
    let xu : Uᗮ := ⟨x, hx⟩
    have h := TauCeti.SpectralOrder.le_re_inner_of_spectrum_subset_Ici
      (compressOperator Uᗮ A) hA1sa hA1spec xu
    have hcoe : ((compressOperator Uᗮ A xu : Uᗮ) : E) = A (x : E) :=
      coe_compressOperator_apply_of_maps A hAUperp xu
    simpa [Submodule.coe_norm, Submodule.coe_inner, hcoe] using h
  have hgap : α < α + δ := by linarith
  have hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V),
      Real.cos (2 * t) ≠ 0 :=
    cos_two_ne_zero_of_ordered_form_gap_offDiagonal
      hA hH hAU hAplusH_V hgap hUlow hUperpHigh hHU hHUperp
  have hAneg : IsSelfAdjoint (-A) := by
    rw [IsSelfAdjoint, star_neg, hA.star_eq]
  have hHneg : IsSelfAdjoint (-H) := by
    rw [IsSelfAdjoint, star_neg, hH.star_eq]
  have hAUneg : ∀ x ∈ U, (-A) x ∈ U := by
    intro x hx
    change -(A x) ∈ U
    exact U.neg_mem (hAU x hx)
  have hAplusH_V_neg : ∀ x ∈ V, ((-A) + (-H)) x ∈ V := by
    intro x hx
    have h := V.neg_mem (hAplusH_V x hx)
    simpa [add_apply, add_comm] using h
  have hUhighNeg : ∀ x ∈ U,
      (-α) * ‖x‖ ^ 2 ≤ RCLike.re ⟪(-A) x, x⟫_ℂ := by
    intro x hx
    calc
      (-α) * ‖x‖ ^ 2 = -(α * ‖x‖ ^ 2) := by ring
      _ ≤ -RCLike.re ⟪A x, x⟫_ℂ := neg_le_neg (hUlow x hx)
      _ = RCLike.re ⟪(-A) x, x⟫_ℂ := by simp
  have hUperpLowNeg : ∀ x ∈ Uᗮ,
      RCLike.re ⟪(-A) x, x⟫_ℂ ≤ (-(α + δ)) * ‖x‖ ^ 2 := by
    intro x hx
    calc
      RCLike.re ⟪(-A) x, x⟫_ℂ = -RCLike.re ⟪A x, x⟫_ℂ := by simp
      _ ≤ -((α + δ) * ‖x‖ ^ 2) := neg_le_neg (hUperpHigh x hx)
      _ = (-(α + δ)) * ‖x‖ ^ 2 := by ring
  have hHUNeg : ∀ x ∈ U, (-H) x ∈ Uᗮ := by
    intro x hx
    change -(H x) ∈ Uᗮ
    exact Uᗮ.neg_mem (hHU x hx)
  have hHUperpNeg : ∀ x ∈ Uᗮ, (-H) x ∈ U := by
    intro x hx
    change -(H x) ∈ U
    exact U.neg_mem (hHUperp x hx)
  have hnegGap : -(α + δ) < -α := by linarith
  have hRneg : projectionBlock Uᗮ U (-H) =
      -(projectionBlock Uᗮ U H) := by
    ext x
    simp [projectionBlock]
  have hRnegExt :
      N.extendedGauge (-(projectionBlock Uᗮ U H)) =
        N.extendedGauge (projectionBlock Uᗮ U H) := by
    have h := N.extendedGauge_smul (-1 : ℂ) (projectionBlock Uᗮ U H)
    simpa using h
  have hRnegMem : N.Mem (projectionBlock Uᗮ U (-H)) := by
    rw [hRneg]
    unfold SymmetricNormingFunction.Mem at hRmem ⊢
    rwa [hRnegExt]
  obtain ⟨hmem, hbound⟩ :=
    tanTwoTheta_directed_boundedResidual_branchFree_blockRepresentative_symmetricNorming_complex N
      (A := -A) (H := -H) (U := U) (V := V)
      (a := -(α + δ)) (b := -α)
      hAneg hHneg hAUneg hAplusH_V_neg hnegGap hUhighNeg hUperpLowNeg
      hHUNeg hHUperpNeg hcos hRnegMem
  refine ⟨hmem, ?_⟩
  have hRnegGauge :
      N.gauge (-(projectionBlock Uᗮ U H)) =
        N.gauge (projectionBlock Uᗮ U H) := by
    unfold SymmetricNormingFunction.gauge
    rw [hRnegExt]
  rw [hRneg, hRnegGauge] at hbound
  have hgapEq : (-α) - (-(α + δ)) = δ := by ring
  rwa [hgapEq] at hbound

/-- **Davis--Kahan 1970, Section 2 `tan 2Θ`, ambient conclusion, exactly from
its printed hypotheses.**

The source assumes an interval `[β, α]`, `δ > 0`,

* `spectrum(A₀) ⊆ [β, α]`,
* `spectrum(A₁) ⊆ [α + δ, ∞)`, and
* `H₀ = H₁ = 0` (expressed here as the equivalent off-diagonal mapping
  conditions).

For an arbitrary reducing subspace `V` of `A+H`, it concludes, for every
source unitarily invariant norm,

`δ ‖tan 2Θ‖ ≤ 2 ‖H‖`.

There is deliberately **no** `IsQuarterAcute`, no `cos (2θ) ≠ 0` hypothesis,
and no spectral-placement hypothesis for the `V`-blocks of `A+H`.  Pole
exclusion is derived above from the same ordered gap by the Section 7
reflection argument.  The proof uses the branch-free positive representative
internally, then the modulus identity in `TanTwoThetaWholeSpace` transfers the
result back to the paper's literal signed `tan 2Θ`. -/
theorem tanTwoTheta_ambient_bounded_spectralGap_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {β α δ : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hHmem : N.Mem H) :
    N.Mem (tanTwoAngleOperatorC U V) ∧
      δ * N.gauge (tanTwoAngleOperatorC U V) ≤ 2 * N.gauge H := by
  have hAred : A.Reduces U := by
    have hAsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
    exact ContinuousLinearMap.IsSymmetric.reduces_of_invariant hAsym hAU
  have hAUperp : ∀ x ∈ Uᗮ, A x ∈ Uᗮ := hAred.2
  have hA0sa : IsSelfAdjoint (compressOperator U A) :=
    isSelfAdjoint_compressOperator hA U
  have hA1sa : IsSelfAdjoint (compressOperator Uᗮ A) :=
    isSelfAdjoint_compressOperator hA Uᗮ
  have hA0upper : spectrum ℝ (compressOperator U A) ⊆ Set.Iic α :=
    fun r hr => (hA0spec hr).2
  have hUlow : ∀ x ∈ U,
      RCLike.re ⟪A x, x⟫_ℂ ≤ α * ‖x‖ ^ 2 := by
    intro x hx
    let xu : U := ⟨x, hx⟩
    have h := TauCeti.SpectralOrder.re_inner_le_of_spectrum_subset_Iic
      (compressOperator U A) hA0sa hA0upper xu
    have hcoe : ((compressOperator U A xu : U) : E) = A (x : E) :=
      coe_compressOperator_apply_of_maps A hAU xu
    simpa [Submodule.coe_norm, Submodule.coe_inner, hcoe] using h
  have hUperpHigh : ∀ x ∈ Uᗮ,
      (α + δ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ := by
    intro x hx
    let xu : Uᗮ := ⟨x, hx⟩
    have h := TauCeti.SpectralOrder.le_re_inner_of_spectrum_subset_Ici
      (compressOperator Uᗮ A) hA1sa hA1spec xu
    have hcoe : ((compressOperator Uᗮ A xu : Uᗮ) : E) = A (x : E) :=
      coe_compressOperator_apply_of_maps A hAUperp xu
    simpa [Submodule.coe_norm, Submodule.coe_inner, hcoe] using h
  have hgap : α < α + δ := by linarith
  have hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V),
      Real.cos (2 * t) ≠ 0 :=
    cos_two_ne_zero_of_ordered_form_gap_offDiagonal
      hA hH hAU hAplusH_V hgap hUlow hUperpHigh hHU hHUperp
  have hAneg : IsSelfAdjoint (-A) := by
    rw [IsSelfAdjoint, star_neg, hA.star_eq]
  have hHneg : IsSelfAdjoint (-H) := by
    rw [IsSelfAdjoint, star_neg, hH.star_eq]
  have hAUneg : ∀ x ∈ U, (-A) x ∈ U := by
    intro x hx
    change -(A x) ∈ U
    exact U.neg_mem (hAU x hx)
  have hAplusH_V_neg : ∀ x ∈ V, ((-A) + (-H)) x ∈ V := by
    intro x hx
    have h := V.neg_mem (hAplusH_V x hx)
    simpa [add_apply, add_comm] using h
  have hUhighNeg : ∀ x ∈ U,
      (-α) * ‖x‖ ^ 2 ≤ RCLike.re ⟪(-A) x, x⟫_ℂ := by
    intro x hx
    calc
      (-α) * ‖x‖ ^ 2 = -(α * ‖x‖ ^ 2) := by ring
      _ ≤ -RCLike.re ⟪A x, x⟫_ℂ := neg_le_neg (hUlow x hx)
      _ = RCLike.re ⟪(-A) x, x⟫_ℂ := by simp
  have hUperpLowNeg : ∀ x ∈ Uᗮ,
      RCLike.re ⟪(-A) x, x⟫_ℂ ≤ (-(α + δ)) * ‖x‖ ^ 2 := by
    intro x hx
    calc
      RCLike.re ⟪(-A) x, x⟫_ℂ = -RCLike.re ⟪A x, x⟫_ℂ := by simp
      _ ≤ -((α + δ) * ‖x‖ ^ 2) := neg_le_neg (hUperpHigh x hx)
      _ = (-(α + δ)) * ‖x‖ ^ 2 := by ring
  have hHUNeg : ∀ x ∈ U, (-H) x ∈ Uᗮ := by
    intro x hx
    change -(H x) ∈ Uᗮ
    exact Uᗮ.neg_mem (hHU x hx)
  have hHUperpNeg : ∀ x ∈ Uᗮ, (-H) x ∈ U := by
    intro x hx
    change -(H x) ∈ U
    exact U.neg_mem (hHUperp x hx)
  have hnegGap : -(α + δ) < -α := by linarith
  have hnegExt : N.extendedGauge (-H) = N.extendedGauge H := by
    have h := N.extendedGauge_smul (-1 : ℂ) H
    simpa using h
  have hnegMem : N.Mem (-H) := by
    unfold SymmetricNormingFunction.Mem at hHmem ⊢
    rwa [hnegExt]
  obtain ⟨habsMem, habsBound⟩ :=
    tanTwoTheta_ambient_bounded_branchFree_orderedForm_symmetricNorming_complex_of_poleExclusion N
      (A := -A) (H := -H) (U := U) (V := V)
      (a := -(α + δ)) (b := -α)
      hAneg hHneg hAUneg hAplusH_V_neg hnegGap hUhighNeg hUperpLowNeg
      hHUNeg hHUperpNeg hcos hnegMem
  have habsBound' :
      δ * N.gauge (absTanTwoAngleOperatorC U V) ≤ 2 * N.gauge H := by
    calc
    δ * N.gauge (absTanTwoAngleOperatorC U V) =
        ((-α) - (-(α + δ))) * N.gauge (absTanTwoAngleOperatorC U V) := by ring
    _ ≤ 2 * N.gauge (-H) := habsBound
    _ = 2 * N.gauge H := by
      unfold SymmetricNormingFunction.gauge
      rw [hnegExt]
  have habsMod : absTanTwoAngleOperatorC U V =
      (tanTwoAngleOperatorC U V).modulus :=
    absTanTwoAngleOperatorC_eq_modulus_directedTanTwoAngleOperatorC hcos
  have hext : N.extendedGauge (absTanTwoAngleOperatorC U V) =
      N.extendedGauge (tanTwoAngleOperatorC U V) := by
    calc
      N.extendedGauge (absTanTwoAngleOperatorC U V) =
          N.extendedGauge ((tanTwoAngleOperatorC U V).modulus) := by
            rw [habsMod]
      _ = N.extendedGauge (tanTwoAngleOperatorC U V) :=
        normingFunction_modulus_eq N (tanTwoAngleOperatorC U V)
  have htanMem : N.Mem (tanTwoAngleOperatorC U V) := by
    unfold SymmetricNormingFunction.Mem at habsMem ⊢
    rwa [← hext]
  have hgauge : N.gauge (absTanTwoAngleOperatorC U V) =
      N.gauge (tanTwoAngleOperatorC U V) := by
    unfold SymmetricNormingFunction.gauge
    rw [hext]
  refine ⟨htanMem, ?_⟩
  rwa [hgauge] at habsBound'

end
end DavisKahan1970
end TauCeti
