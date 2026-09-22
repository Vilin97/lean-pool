/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanThetaAmbient
import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63UnboundedInfiniteTrial
import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63UnboundedCompression
import LeanPool.DavisKahan.DavisKahan.TanTheta.RitzPair
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance

/-! # Tan Theta Unbounded Ambient -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Unbounded ambient single-angle tangent assembly

This file isolates the missing ambient half of the Section 2 `tan Theta`
theorem from the already-proved unbounded directed Theorem 6.3 estimate.

The ambient step is bounded operator geometry once a sharp lower-corner
Ky Fan estimate is available.  Two data paths supply that estimate:
`Theorem63TrialData` covers an unbounded ambient operator with bounded Ritz
compression, while `UnboundedCompressionTrialData` supplies the full Appendix
scope in which the Ritz compression itself may be unbounded.  In the latter
case the Appendix spectral truncation/release argument is consumed through
`UnboundedCompressionTrialData.all_kyFan_core`.  The upper tangent corner is the
adjoint of the lower one, and Davis--Kahan Lemmas 6.1 and 6.2 assemble the two
corners without loss.
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt

open TauCeti.DavisKahan.ExactSinTheta


open scoped InnerProductSpace BigOperators
open TauCeti.DavisKahan
open TauCeti.DavisKahan.TanTheta
open TauCeti.DavisKahan.TanTheta
open TauCeti.ApproximationNumber
open scoped TauCeti.CompleteSubspace

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- **The paper's `tan Θ` exists as a bounded operator.**

`‖P_U − P_V‖ < 1`: no principal angle of the pair reaches `π/2`.  This is the Section 1
vacuity convention made explicit for the tangent -- when it fails, `‖tan Θ‖` does not exist and
the printed statement says nothing -- and it is *not* condition (3.5), which the paper
introduces only in Section 3. -/
def HasDefinedAmbientTangent (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : Prop :=
  U.projectionGap V < 1

/-- `HasDefinedAmbientTangent` is exactly `‖sin Θ‖ < 1`; the gap and the ambient sine are the
same number by `norm_sinAngleOperatorC`. -/
theorem hasDefinedAmbientTangent_iff_norm_sinAngleOperatorC_lt_one
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    HasDefinedAmbientTangent U V ↔ ‖sinAngleOperatorC U V‖ < 1 := by
  rw [HasDefinedAmbientTangent, norm_sinAngleOperatorC U V]

omit [CompleteSpace E] in
private theorem comp_eq_mul_unboundedTanThetaAmbient
    (f g : E →L[ℂ] E) : f ∘L g = f * g := rfl

omit [CompleteSpace E] in
private theorem projectionBlock_lower_unboundedTanThetaAmbient
    {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    (K : E →L[ℂ] E) :
    projectionBlock Uᗮ U K =
      (1 - U.starProjection) * K * U.starProjection := by
  rw [projectionBlock, Submodule.starProjection_orthogonal',
    comp_eq_mul_unboundedTanThetaAmbient,
    comp_eq_mul_unboundedTanThetaAmbient, mul_assoc]

omit [CompleteSpace E] in
private theorem projectionBlock_upper_unboundedTanThetaAmbient
    {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    (K : E →L[ℂ] E) :
    projectionBlock Uᗮᗮ Uᗮ K =
      U.starProjection * K * (1 - U.starProjection) := by
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  rw [projectionBlock]
  simp only [hUperp, Submodule.starProjection_orthogonal',
    comp_eq_mul_unboundedTanThetaAmbient]
  rw [mul_assoc]

omit [CompleteSpace E] in
private theorem projectionBlock_smul_unboundedTanThetaAmbient
    (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (c : ℂ) (K : E →L[ℂ] E) :
    projectionBlock Ω Γ (c • K) = c • projectionBlock Ω Γ K := by
  ext x
  simp [projectionBlock]

private theorem subtypeL_comp_adjoint_subtypeL_unboundedTanThetaAmbient
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    U.subtypeL ∘L U.subtypeL.adjoint = U.starProjection := by
  rw [Submodule.adjoint_subtypeL]
  rfl

/-- Pure bounded-operator assembly for the ambient tangent theorem.

The hypothesis `hlower` is the only place the unbounded Theorem 6.3 argument
enters: it supplies the sharp lower-corner estimate.  Everything after that is
the same two-corner Lemma-6.1/Lemma-6.2 argument as the bounded source theorem. -/
theorem tanTheta_ambient_bounded_kyFan_complex_of_lowerCorner
    {H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hH : IsSelfAdjoint H)
    {delta : ℝ} (hdelta : 0 < delta)
    (htr : ‖sinAngleOperatorC U V‖ < 1)
    (hlower : ∀ k : ℕ,
      delta * kyFanApproximationGauge k
          (projectionBlock Uᗮ U
            (projectorDifference U V * secantSquared U V)) ≤
        kyFanApproximationGauge k (projectionBlock Uᗮ U H)) :
    ∀ k : ℕ,
      delta * kyFanApproximationGauge k (tanAngleOperatorC U V) ≤
        kyFanApproximationGauge k H := by
  intro k
  have hdeltac : ‖((delta : ℝ) : ℂ)‖ = delta := by
    simp [abs_of_pos hdelta]
  set K := projectorDifference U V * secantSquared U V
  have h₀ : ∀ j : ℕ,
      kyFanApproximationGauge j
          (projectionBlock Uᗮ U (((delta : ℝ) : ℂ) • K)) ≤
        kyFanApproximationGauge j (projectionBlock Uᗮ U H) := by
    intro j
    rw [projectionBlock_smul_unboundedTanThetaAmbient,
      kyFanApproximationGauge_smul, hdeltac]
    exact hlower j
  have h₁ : ∀ j : ℕ,
      kyFanApproximationGauge j
          (projectionBlock Uᗮᗮ Uᗮ (((delta : ℝ) : ℂ) • K)) ≤
        kyFanApproximationGauge j (projectionBlock Uᗮᗮ Uᗮ H) := by
    intro j
    have hleft :
        projectionBlock Uᗮᗮ Uᗮ (((delta : ℝ) : ℂ) • K) =
          (((delta : ℝ) : ℂ) • projectionBlock Uᗮ U K).adjoint := by
      rw [projectionBlock_smul_unboundedTanThetaAmbient,
        upperCorner_eq_adjoint_lowerCorner htr]
      change ((delta : ℝ) : ℂ) • star (projectionBlock Uᗮ U K) =
        star (((delta : ℝ) : ℂ) • projectionBlock Uᗮ U K)
      rw [star_smul, RCLike.star_def, Complex.conj_ofReal]
    have hright :
        projectionBlock Uᗮᗮ Uᗮ H =
          (projectionBlock Uᗮ U H).adjoint := by
      have hp := isSelfAdjoint_starProjection U
      rw [projectionBlock_upper_unboundedTanThetaAmbient,
        projectionBlock_lower_unboundedTanThetaAmbient]
      change _ = star _
      simp only [star_mul, star_sub, star_one, hp.star_eq, hH.star_eq]
      noncomm_ring
    rw [hleft, hright, kyFanApproximationGauge_adjoint,
      kyFanApproximationGauge_adjoint, kyFanApproximationGauge_smul, hdeltac]
    exact hlower j
  have hcombine := lemma61_all_kyFan Uᗮ U
    (((delta : ℝ) : ℂ) • K) (((delta : ℝ) : ℂ) • K) H H h₀ h₁ k
  have hsum :
      projectionBlock Uᗮ U (((delta : ℝ) : ℂ) • K) +
          projectionBlock Uᗮᗮ Uᗮ (((delta : ℝ) : ℂ) • K) =
        ((delta : ℝ) : ℂ) • tanBlockRepresentative U V := by
    rw [tanBlockRepresentative, diagonalPair,
      projectionBlock_smul_unboundedTanThetaAmbient,
      projectionBlock_smul_unboundedTanThetaAmbient, ← smul_add]
    rfl
  have hsumH :
      projectionBlock Uᗮ U H + projectionBlock Uᗮᗮ Uᗮ H =
        diagonalPair Uᗮ U H := rfl
  rw [hsum, hsumH, kyFanApproximationGauge_smul, hdeltac] at hcombine
  have hpinch := diagonalPair_all_kyFan_le Uᗮ U H k
  have hmodulus :
      kyFanApproximationGauge k (tanAngleOperatorC U V) =
        kyFanApproximationGauge k (tanBlockRepresentative U V) := by
    rw [directedTanAngleOperatorC_eq_modulus_blockRepresentative htr]
    exact (ContinuousLinearMap.modulus_hasSameApproximationNumbers
      (tanBlockRepresentative U V)).kyFanGauge_eq k
  rw [hmodulus]
  exact hcombine.trans hpinch

/-- Paper-norm form of `tanTheta_ambient_bounded_kyFan_complex_of_lowerCorner`. -/
theorem tanTheta_ambient_bounded_symmetricNorming_complex_of_lowerCorner
    (N : SymmetricNormingFunction)
    {H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hH : IsSelfAdjoint H)
    {delta : ℝ} (hdelta : 0 < delta)
    (htr : ‖sinAngleOperatorC U V‖ < 1)
    (hlower : ∀ k : ℕ,
      delta * kyFanApproximationGauge k
          (projectionBlock Uᗮ U
            (projectorDifference U V * secantSquared U V)) ≤
        kyFanApproximationGauge k (projectionBlock Uᗮ U H))
    (hMem : N.Mem H) :
    N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge H :=
  N.mul_gauge_le_of_all_mul_kyFan_le hdelta hMem
    (tanTheta_ambient_bounded_kyFan_complex_of_lowerCorner hH hdelta htr hlower)

/-- **Unbounded-data ambient `tan Theta` theorem with transversality supplied.**

This is the assembly half of `tanTheta_ambient_unboundedOperator_boundedRitzData_symmetricNorming_complex`:
everything except the derivation of `‖sin Theta‖ < 1` from the printed standing
assumption (3.5).  Separating the two lets the real-scalar counterpart consume
this half after establishing transversality natively on the real side, so the
crossed-defect condition never has to be transported across complexification.

`data` is the bounded trial-block data extracted from an unbounded self-adjoint
problem.  Its residual is assumed to be exactly the lower `U -> U-perp` block of
the bounded perturbation `H`; this is the operator form of the printed
Rayleigh--Ritz condition `H_0 = 0`. -/
theorem tanTheta_ambient_unboundedOperator_boundedRitzData_symmetricNorming_complex_of_transversality
    (N : SymmetricNormingFunction)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (data : Theorem63TrialData U V)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompression : ∀ z : U,
      RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : U,
      (alpha + delta) * ‖Vᗮ.starProjection ((z : U) : E)‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection ((z : U) : E),
          Vᗮ.starProjection (data.action z)⟫_ℂ)
    (htr : ‖sinAngleOperatorC U V‖ < 1)
    (hResidual :
      data.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge H := by
  have hblock :
      projectionBlock Uᗮ U H =
        data.residual ∘L U.subtypeL.adjoint := by
    rw [hResidual, projectionBlock]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply]
    have hproj :
        U.subtypeL ∘L U.subtypeL.adjoint = U.starProjection :=
      subtypeL_comp_adjoint_subtypeL_unboundedTanThetaAmbient U
    have happ := congrArg (fun L : E →L[ℂ] E => L x) hproj
    simpa only [ContinuousLinearMap.comp_apply] using
      (congrArg (fun y : E => Uᗮ.starProjection (H y)) happ).symm
  have hlower : ∀ k : ℕ,
      delta * kyFanApproximationGauge k
          (projectionBlock Uᗮ U
            (projectorDifference U V * secantSquared U V)) ≤
        kyFanApproximationGauge k (projectionBlock Uᗮ U H) := by
    intro k
    have hcorner := kyFan_lowerCorner_le (U := U) (V := V) htr k
    have hcore := data.all_kyFan_core_of_formBounds_infinite
      hdelta hCompression hcross k
    have hresKy :
        kyFanApproximationGauge k data.residual =
          kyFanApproximationGauge k (projectionBlock Uᗮ U H) := by
      rw [hblock]
      have hs := sameApproximationSingularValues_extendDomainByZero U data.residual
      exact (hs.kyFanApproximationGauge_eq k).symm
    calc
      delta * kyFanApproximationGauge k
          (projectionBlock Uᗮ U
            (projectorDifference U V * secantSquared U V))
          ≤ delta * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
              (approximationSingularValue n (theorem63DirectedSineBlock U V))) :=
        mul_le_mul_of_nonneg_left hcorner hdelta.le
      _ ≤ kyFanApproximationGauge k data.residual := hcore
      _ = kyFanApproximationGauge k (projectionBlock Uᗮ U H) := hresKy
  exact tanTheta_ambient_bounded_symmetricNorming_complex_of_lowerCorner N hH hdelta htr hlower hMem

/-- **Unbounded-data ambient `tan Theta` theorem, complex form.**

`data` is the bounded trial-block data extracted from an unbounded self-adjoint
problem.  Its residual is assumed to be exactly the lower `U -> U-perp` block of
the bounded perturbation `H`; this is the operator form of the printed
Rayleigh--Ritz condition `H_0 = 0`.  The form bounds are precisely the two
inputs already consumed by the unbounded arbitrary-trial Theorem 6.3 chain.

Uniform transversality is not assumed: the directed sine values are already
strictly below one under those form bounds, and the printed standing assumption
(3.5) identifies the symmetric gap with the directed one.

The conclusion is the missing sharp ambient inequality
`delta * N(tan Theta) <= N(H)` for every paper unitary-invariant norm. -/
theorem tanTheta_ambient_unboundedOperator_boundedRitzData_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (data : Theorem63TrialData U V)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompression : ∀ z : U,
      RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : U,
      (alpha + delta) * ‖Vᗮ.starProjection ((z : U) : E)‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection ((z : U) : E),
          Vᗮ.starProjection (data.action z)⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual :
      data.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    HasDefinedAmbientTangent U V ∧
      N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge H := by
  have hdirected :
      approximationSingularValue 0 (theorem63DirectedSineBlock U V) < 1 :=
    data.approximationSingularValue_sineBlock_lt_one_infiniteData
      hdelta hCompression hcross 0
  have hambient : ‖directedSineAmbient U V‖ < 1 := by
    have h := approximationNumber_directedSineAmbient_le (U := U) (V := V) 0
    rw [(directedSineAmbient U V).approximationNumber_index_zero] at h
    exact lt_of_le_of_lt h hdirected
  have htr : ‖sinAngleOperatorC U V‖ < 1 := by
    rw [norm_sinAngleOperatorC U V,
      DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent
        U V h35]
    exact hambient
  exact ⟨(hasDefinedAmbientTangent_iff_norm_sinAngleOperatorC_lt_one U V).2 htr,
    tanTheta_ambient_unboundedOperator_boundedRitzData_symmetricNorming_complex_of_transversality N data H hH
      hdelta hCompression hcross htr hResidual hMem⟩

/-! ## Appendix scope: the Ritz compression itself may be unbounded -/

/-- **Ambient `tan Theta` assembly with a genuinely unbounded Ritz compression,
with transversality supplied.**

This is the Appendix counterpart of
`tanTheta_ambient_unboundedOperator_boundedRitzData_symmetricNorming_complex_of_transversality`.  The crucial
difference is that `D.compression` is a densely defined self-adjoint closed
operator on the trial space, not a bounded continuous endomorphism.  Only the
residual is bounded.  The lower-corner estimate therefore comes from
`UnboundedCompressionTrialData.all_kyFan_core`, which performs the Appendix
spectral truncation and release argument.  Once that estimate is available, the
whole-space assembly is again purely bounded operator geometry. -/
theorem tanTheta_ambient_unboundedRitzData_symmetricNorming_complex_of_transversality
    (N : SymmetricNormingFunction)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : UnboundedCompressionTrialData U)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : U) : E))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : U) : E)),
          Vᗮ.starProjection (D.action z)⟫_ℂ)
    (htr : ‖sinAngleOperatorC U V‖ < 1)
    (hResidual :
      D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge H := by
  have hblock :
      projectionBlock Uᗮ U H =
        D.residual ∘L U.subtypeL.adjoint := by
    rw [hResidual, projectionBlock]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply]
    have hproj :
        U.subtypeL ∘L U.subtypeL.adjoint = U.starProjection :=
      subtypeL_comp_adjoint_subtypeL_unboundedTanThetaAmbient U
    have happ := congrArg (fun L : E →L[ℂ] E => L x) hproj
    simpa only [ContinuousLinearMap.comp_apply] using
      (congrArg (fun y : E => Uᗮ.starProjection (H y)) happ).symm
  have hlower : ∀ k : ℕ,
      delta * kyFanApproximationGauge k
          (projectionBlock Uᗮ U
            (projectorDifference U V * secantSquared U V)) ≤
        kyFanApproximationGauge k (projectionBlock Uᗮ U H) := by
    intro k
    have hcorner := kyFan_lowerCorner_le (U := U) (V := V) htr k
    have hcore := D.all_kyFan_core V hdelta hupper hcross k
    have hresKy :
        kyFanApproximationGauge k D.residual =
          kyFanApproximationGauge k (projectionBlock Uᗮ U H) := by
      rw [hblock]
      have hs := sameApproximationSingularValues_extendDomainByZero U D.residual
      exact (hs.kyFanApproximationGauge_eq k).symm
    calc
      delta * kyFanApproximationGauge k
          (projectionBlock Uᗮ U
            (projectorDifference U V * secantSquared U V))
          ≤ delta * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
              (approximationSingularValue n (theorem63DirectedSineBlock U V))) :=
        mul_le_mul_of_nonneg_left hcorner hdelta.le
      _ ≤ kyFanApproximationGauge k D.residual := hcore
      _ = kyFanApproximationGauge k (projectionBlock Uᗮ U H) := hresKy
  exact tanTheta_ambient_bounded_symmetricNorming_complex_of_lowerCorner N hH hdelta htr hlower hMem

/-- **Davis--Kahan's ambient `tan Theta` estimate with an unbounded Ritz
compression, complex form.**

The Appendix explicitly allows `A₀ ≤ alpha` and `Lambda₁ ≥ alpha + delta` to
*both* be unbounded.  Here `D.compression` is that unbounded self-adjoint Ritz
operator and `D.residual` is the bounded residual.  Uniform transversality is
derived from the Appendix no-pole theorem plus the paper's standing condition
(3.5), not assumed by the caller. -/
theorem tanTheta_ambient_unboundedRitzData_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : UnboundedCompressionTrialData U)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : U) : E))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : U) : E)),
          Vᗮ.starProjection (D.action z)⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual :
      D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    HasDefinedAmbientTangent U V ∧
      N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge H := by
  have hdirected :
      approximationSingularValue 0 (theorem63DirectedSineBlock U V) < 1 :=
    D.approximationSingularValue_sineBlock_lt_one V hdelta hupper hcross 0
  have hambient : ‖directedSineAmbient U V‖ < 1 := by
    have h := approximationNumber_directedSineAmbient_le (U := U) (V := V) 0
    rw [(directedSineAmbient U V).approximationNumber_index_zero] at h
    exact lt_of_le_of_lt h hdirected
  have htr : ‖sinAngleOperatorC U V‖ < 1 := by
    rw [norm_sinAngleOperatorC U V,
      DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent
        U V h35]
    exact hambient
  exact ⟨(hasDefinedAmbientTangent_iff_norm_sinAngleOperatorC_lt_one U V).2 htr,
    tanTheta_ambient_unboundedRitzData_symmetricNorming_complex_of_transversality
      N D H hH hdelta hupper hcross htr hResidual hMem⟩

/-- **Davis--Kahan 1970, Appendix-complete ambient `tan Theta` theorem.**

This is the source-shaped wrapper for the genuinely unbounded Ritz-compression
case.  The ambient self-adjoint operator and the Ritz compression may both be
unbounded; the residual and perturbation `H` are bounded.  The hypotheses
`hZA`/`haction` identify the abstract Ritz data with the ambient operator on the
Ritz domain, `hVdom`/`hVcomm` say the unwanted subspace reduces the ambient
operator, `hupper` and `hUnwanted` are the two printed form bounds, and `h35` is
the standing condition (3.5). -/
theorem tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : UnboundedCompressionTrialData U)
    (A : E →ₗ.[ℂ] E)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hZA : ∀ z : D.compression.domain, ((z : U) : E) ∈ A.domain)
    (haction : ∀ z : D.compression.domain,
      D.action z = A ⟨((z : U) : E), hZA z⟩)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : E)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : E)), hVdom x⟩)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤
        RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    HasDefinedAmbientTangent U V ∧
      N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge H := by
  refine tanTheta_ambient_unboundedRitzData_symmetricNorming_complex
    N D H hH hdelta hupper ?_ h35 hResidual hMem
  intro z
  exact D.crossed_lower_of_reducing V A hZA haction hVdom hVcomm hUnwanted z

/-- The same theorem specialized to an actual unbounded trial block and an
arbitrary chosen reducing subspace.  All domain-sensitive crossed-form work is
reused from the already-proved unbounded Theorem 6.3 implementation. -/
theorem tanTheta_ambient_unboundedOperator_boundedRitz_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℂ] E)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : BoundedCompressionTrialBlock A U)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : E)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : E)), hVdom x⟩)
    (hCompression : ∀ z : U,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤
        RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    HasDefinedAmbientTangent U V ∧
      N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge H := by
  let data := Theorem63TrialData.ofUnbounded D V
  refine tanTheta_ambient_unboundedOperator_boundedRitzData_symmetricNorming_complex N data H hH hdelta
    hCompression ?_ h35 ?_ hMem
  · intro z
    exact crossed_lower_of_reducing A D V hVdom hVcomm hUnwanted z
  · exact hResidual

/-! ### The constructor-first interface

`tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_complex` above is the most
general form, and it asks the caller for four separate facts that are not
Davis--Kahan mathematics: two saying the compression data is `A`'s Ritz pair on
`U`, and two saying `Vᗮ` reduces `A`.  `DavisKahan.UnboundedRitzPair` and
`DavisKahan.ReducingComplement` hold those, and
`UnboundedRitzPair.ofTrialBlock` builds the first from the bounded-compression
bundle a caller usually has.

What stays a hypothesis is what the theorem is about: the semiboundedness of the
compression, the coercivity on the unwanted subspace, and the crossed-defect
standing condition (3.5). -/

/-- **Uniform transversality is a consequence of the Appendix hypotheses, not an
extra assumption.**

`‖sin Θ‖ < 1` for the ambient angle, from the two printed form bounds together with the
standing condition (3.5).  The tangent theorem's proof derives this inline; exposing it is
what lets a caller read the *sequence* `tan θ₀, tan θ₁, …` off `tanAngleOperatorC`,
which needs the transversality separately from the estimate. -/
theorem norm_sinAngleOperatorC_lt_one_of_unboundedRitz
    {A : E →ₗ.[ℂ] E}
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace U]
    (D : DavisKahan.UnboundedRitzPair A U)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V) :
    ‖sinAngleOperatorC U V‖ < 1 := by
  have hcross := D.trial.crossed_lower_of_reducing V A D.mem_domain D.action_eq
    hV.mapsDomain hV.commutes hUnwanted
  have hdirected :
      approximationSingularValue 0 (theorem63DirectedSineBlock U V) < 1 :=
    D.trial.approximationSingularValue_sineBlock_lt_one V hdelta hupper hcross 0
  have hambient : ‖directedSineAmbient U V‖ < 1 := by
    have h := approximationNumber_directedSineAmbient_le (U := U) (V := V) 0
    rw [(directedSineAmbient U V).approximationNumber_index_zero] at h
    exact lt_of_le_of_lt h hdirected
  rw [norm_sinAngleOperatorC U V,
    DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent U V h35]
  exact hambient

/-- **Davis--Kahan 1970, `tan Θ`, unbounded ambient form, taking the Ritz pair and
the reducing complement as objects.**

`tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_complex` with its four
structural arguments replaced by `DavisKahan.UnboundedRitzPair A U` and
`DavisKahan.ReducingComplement A V`.  The mathematics -- semiboundedness,
coercivity on the unwanted subspace, and the crossed-defect condition (3.5) --
is unchanged and still supplied by the caller. -/
theorem tanTheta_ambient_unboundedRitz_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℂ] E}
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace U]
    (D : DavisKahan.UnboundedRitzPair A U)
    (hV : DavisKahan.ReducingComplement A V)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤
        RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    HasDefinedAmbientTangent U V ∧
      N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge H :=
  tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_complex N D.trial A H hH hdelta
    D.mem_domain D.action_eq hV.mapsDomain hV.commutes hupper hUnwanted h35
    hResidual hMem

/-! ## The printed `tan Θ` hypotheses, with the source's own vacuity convention

The Section 2 tangent theorem assumes the ordered spectral gap, `δ > 0` and `H₀ = 0`, and
nothing else.  The endpoints above additionally take `CrossedDefectsEquivalent U V`, which is
condition (3.5) -- and (3.5) is introduced in Section 3, *after* Proposition 3.2, where the
source announces it will be assumed for the **remainder** of the paper.  A convention
introduced after a theorem is not a hypothesis of it, so reading (3.5) back into Section 2 is
not the ledger-selected source witness.

What Section 1 does give, before any of this, is a semantic convention: some of the paper's
results are vacuous when a norm occurring in them fails to exist, and the source says it will
not remark on this at the individual statements.  For the tangent that case is concrete.
`tan` is unbounded at `π/2`, so `‖tan Θ‖` exists exactly when no principal angle reaches
`π/2` -- equivalently when `‖P_U − P_V‖ < 1`, since `‖sin Θ‖` is that gap and the angle
spectrum is a compact subset of `[0, π/2]`.  Mathlib's `Real.tan` is total, with
`tan (π/2) = 0`, so `cfc Real.tan Θ` is *always* a bounded operator: when an angle does reach
`π/2` that object silently is not the paper's `tan Θ`, and the printed statement is vacuous
rather than false.

`HasDefinedAmbientTangent` names that condition, and the endpoints below take it in place of
(3.5).  Nothing is lost: definedness *implies* (3.5), because an angle of `π/2` is exactly a
vector in one of the two crossed defect spaces, so a defined tangent forces both of them to be
trivial and the identification (3.5) asks for is the one between two zero spaces.

The (3.5) endpoints above are non-vacuous, and since 2026-09-05 they *say so*: each one
concludes `HasDefinedAmbientTangent U V` alongside the estimate.  That conjunct was always
proved inside those proofs -- the tangent bound needs it -- but until it was exposed a reader
had to open a proof to learn that the conclusion is not about Lean's totalised
`cfc Real.tan` at a right angle.  Finding F3.1 of the 2026-09-04 hostile review.  The
endpoints below need no such conjunct: they take the condition as a hypothesis. -/

section DefinedTangent

omit [CompleteSpace E] in
/-- **A defined tangent implies condition (3.5).**

An angle of `π/2` is a vector of `U` killed by `P_V`, or of `V` killed by `P_U`; a gap strictly
below one excludes both, so the two crossed defect spaces are trivial and the identification
(3.5) demands is the one between two zero spaces.  This is why the endpoints below lose nothing
by replacing (3.5) with definedness. -/
theorem crossedDefectsEquivalent_of_hasDefinedAmbientTangent
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : HasDefinedAmbientTangent U V) : DavisKahan.CrossedDefectsEquivalent U V :=
  DavisKahan.crossedDefectsEquivalent_of_isAcute U V (TauCeti.isAcute_of_projectionGap_lt_one h)

/-- **Under a defined tangent the angle spectrum misses `π/2`.**

This is what makes the hypothesis a *definedness* condition rather than a convenient
inequality: `Real.tan` is finite exactly on the spectrum this permits. -/
theorem spectrum_angleOperator_lt_pi_div_two_of_hasDefinedAmbientTangent
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : HasDefinedAmbientTangent U V) {t : ℝ}
    (ht : t ∈ spectrum ℝ (angleOperatorC U V)) : 0 ≤ t ∧ t < Real.pi / 2 :=
  spectrum_angleOperatorC_lt_pi_div_two U V (by rwa [norm_sinAngleOperatorC]) ht

/-- **The definedness hypothesis is exactly "no principal angle is `π/2`".**

The forward direction says the hypothesis is sufficient for `tan` to be finite on the angle
spectrum.  This is the converse, and it is what makes the modelling of Section 1's vacuity
convention two-directional rather than one: when `‖P_U − P_V‖ = 1` the gap is attained in the
spectrum -- a nonnegative operator has its norm in its spectrum -- so `arcsin 1 = π/2` is an
angle of the pair and the paper's `tan Θ` genuinely does not exist.  The printed statement is
then vacuous, and the hypothesis fails, in step.

`Nontrivial E` is what puts the norm in the spectrum; over the zero space every gap is `0` and
the hypothesis holds outright. -/
theorem hasDefinedAmbientTangent_iff_pi_div_two_notMem_spectrum
    [Nontrivial E] (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    HasDefinedAmbientTangent U V ↔
      Real.pi / 2 ∉ spectrum ℝ (angleOperatorC U V) := by
  constructor
  · intro h hmem
    have := (spectrum_angleOperator_lt_pi_div_two_of_hasDefinedAmbientTangent h hmem).2
    exact absurd this (lt_irrefl _)
  · intro h
    by_contra hgap
    -- the gap is at most one, so failing to be `< 1` pins it at `1`
    have hle : ‖sinAngleOperatorC U V‖ ≤ 1 := norm_sinAngleOperatorC_le_one U V
    have hgap' : ¬ ‖sinAngleOperatorC U V‖ < 1 := by
      rw [norm_sinAngleOperatorC]
      exact hgap
    have heq : ‖sinAngleOperatorC U V‖ = 1 := le_antisymm hle (not_lt.mp hgap')
    -- a nonnegative operator attains its norm in its spectrum
    have hone : (1 : ℝ) ∈ spectrum ℝ (sinAngleOperatorC U V) := by
      have := CStarAlgebra.norm_mem_spectrum_of_nonneg (a := sinAngleOperatorC U V)
        (sinAngleOperatorC_nonneg U V)
      rwa [heq] at this
    -- and `arcsin` carries it to `π/2` in the angle spectrum
    refine h ?_
    rw [angleOperatorC,
      cfc_map_spectrum (R := ℝ) (f := Real.arcsin) (a := sinAngleOperatorC U V)
        (isSelfAdjoint_sinAngleOperatorC U V) Real.continuous_arcsin.continuousOn]
    exact ⟨1, hone, Real.arcsin_one⟩

/-- **Under a defined tangent, `cfc Real.tan` is the paper's `tan Θ` and not Mathlib's
totalisation.**

`Real.tan` is total in Lean, with `tan (π/2) = 0`, so `tanAngleOperatorC` is a bounded operator
whether or not the paper's `tan Θ` exists.  This says that when the tangent *is* defined the
totalisation is never reached: `tan` is genuinely continuous on the angle spectrum, so the
functional calculus is applied to an honest function and the object is the printed one.

Without this the definedness hypothesis would be doing no work in the conclusion; with it, the
endpoint below is about `tan Θ` in the source's sense. -/
theorem continuousOn_tan_spectrum_of_hasDefinedAmbientTangent
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : HasDefinedAmbientTangent U V) :
    ContinuousOn Real.tan (spectrum ℝ (angleOperatorC U V)) := by
  intro t ht
  obtain ⟨ht0, ht2⟩ := spectrum_angleOperator_lt_pi_div_two_of_hasDefinedAmbientTangent h ht
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcos : Real.cos t ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith, ht2⟩)
  exact (Real.continuousAt_tan.mpr hcos).continuousWithinAt

/-- **Davis--Kahan 1970, the `tan Θ` theorem, ambient clause, over `ℂ`, at the printed
hypotheses.**

`δ N(tan Θ) ≤ N(H)` with the printed ordered gap, `δ > 0` and the Rayleigh--Ritz condition,
and with no condition (3.5): in its place is the source's own requirement that the norm
occurring in the statement exists.  When it does not, `HasDefinedAmbientTangent` fails and the
statement is vacuous, which is exactly what Section 1 says to read into it.

`tanTheta_ambient_unboundedRitz_symmetricNorming_complex` is the same conclusion under (3.5);
it is now the corollary rather than the source statement. -/
theorem tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℂ] E}
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace U]
    (D : DavisKahan.UnboundedRitzPair A U)
    (hV : DavisKahan.ReducingComplement A V)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (hdefined : HasDefinedAmbientTangent U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge H :=
  (tanTheta_ambient_unboundedRitz_symmetricNorming_complex N D hV H hH hdelta hupper hUnwanted
    (crossedDefectsEquivalent_of_hasDefinedAmbientTangent hdefined) hResidual hMem).2

/-- **Davis--Kahan 1970, the ambient `tan Θ` theorem at the printed source scope
over `ℂ`.**

Separable ambient Hilbert space and normalized unitarily invariant norm.  The
definedness hypothesis stays exactly as printed; the estimate goes through the
Fan-dominance bridge. -/
theorem tanTheta_ambient_unboundedRitz_definedTangent_normalizedUIN_complex
    
    (N : NormalizedUnitaryInvariantNorm.{0, u} ℂ)
    {A : E →ₗ.[ℂ] E}
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace U]
    (D : DavisKahan.UnboundedRitzPair A U)
    (hV : DavisKahan.ReducingComplement A V)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (hdefined : HasDefinedAmbientTangent U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge H :=
  normalizedUnitaryInvariant_of_symmetricNorming N hdelta hMem fun M hM =>
    tanTheta_ambient_unboundedRitz_definedTangent_symmetricNorming_complex M D hV H hH
      hdelta hupper hUnwanted hdefined hResidual hM

end DefinedTangent

end

end DavisKahan1970
end TauCeti
