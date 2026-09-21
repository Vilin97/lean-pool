/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamDoubleTangent
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedGramMiddle

/-!
# Section 9, the 2-norm sentence of equation (9.7)

`DavisKahan/Specialized/FreeBeam/BeamDoubleTangent.lean` proves the
bound-norm half of equation (9.7) for the genuine free beam:
`tan 2θ₁ ≤ 2‖R̂‖/(500 - α̂₂)`.  The sentence the paper prints straight after it is

> with the same right side bounding `tan 2θ₁ + tan 2θ₂` in the 2-norm

and that is what this module proves, as `beamTanTwoThetaSum_le`.

The mathematics is entirely upstream: `beamTanTwoThetaAt_le` used the *pointwise*
operator-norm estimate, and this uses the Ky Fan prefix endpoint
`DavisKahan1970.gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan` at
`k = 2`.  Everything else — the comparison operator `Â`, the off-diagonal
residual `B`, the Rayleigh--Ritz form bounds and the perturbed spectral gap — is
the data `BeamDoubleTangent` already built.

## Two things are specific to the beam

* **The residual is charged to the corner, not to the ambient operator.**  The
  ambient `B = R̂ ⊕ R̂*` carries *both* off-diagonal blocks, so its second
  approximation number is again `‖R̂‖` and the ambient endpoint
  `…_le_two_mul_kyFan_ambient` would lose a factor of two, overshooting the
  printed bound.  The directed corner `R₀ : Z → Zᗮ` is exactly the
  Rayleigh--Ritz residual, whose recentered Gram `(ε²/30)[[1,-1],[-1,1]]` is rank
  one, so `kyFanTwo_beamTrialBlock_residual_le` gives `‖R̂‖₂ = ‖R̂‖₁ = ε/√15` and
  the printed right side survives unchanged.
* **The pole exclusion is needed in operator norm.**  The endpoint's hypothesis
  is `‖sin 2Θ₀‖ < 1`, where the pointwise bound of `beamTanTwoThetaAt_le` needed
  only `‖sin 2Θ₀ x‖ ≤ c‖x‖` on the trial subspace.
  `TauCeti.norm_offDiagonalPart_lt_one_of_tendsto` upgrades the one to the other
  from the same constant cutoff, with no smallness assumption on `ε`.

This module lives under `Sources/` rather than beside `BeamDoubleTangent`
because it imports a source facade, which a generic-foundation module may not
do.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. 7 (1970), 1--46, Section 9, the sentence after equation
  (9.7).
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model

open DavisKahan1970.Section9
open TauCeti.ApproximationNumber

noncomputable section

/-! ## The 2-norm sentence of equation (9.7)

The sentence the paper prints after (9.7) is "with the same right side bounding
`tan 2θ₁ + tan 2θ₂` in the 2-norm".  `tan 2θ₁ + tan 2θ₂` is the two-term Ky Fan
gauge of the directed tangent corner `T₀ : Z → Zᗮ`, so the statement is
`DavisKahan1970.gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan`
instantiated at `k = 2`.

Two things are specific to the beam.

* **The residual is charged to the corner, not to the ambient operator.**  The
  ambient `B` carries *both* off-diagonal blocks, so its second approximation
  number is again `‖R̂‖` and the ambient endpoint would lose a factor of two.  The
  corner `R₀` is exactly the Rayleigh--Ritz residual, whose recentered Gram
  `(ε²/30)[[1,-1],[-1,1]]` is rank one, so
  `kyFanTwo_beamTrialBlock_residual_le` gives `‖R̂‖₂ = ‖R̂‖₁ = ε/√15` and the
  printed right side survives unchanged.
* **The pole exclusion is needed in operator norm.**  The endpoint's hypothesis
  is `‖sin 2Θ₀‖ < 1`, where `beamTanTwoThetaAt_le` needed only the pointwise
  bound; `TauCeti.norm_offDiagonalPart_lt_one_of_tendsto` supplies it from the
  same cutoff, with no smallness assumption on `ε`. -/



/-- The beam's cutoff family is constant and already fixes the trial subspace, so
it converges strongly to the identity there. -/
theorem beamTrialCutoff_tendsto (ε : ℝ) {x : BeamL2} (hx : x ∈ beamTrial) :
    Filter.Tendsto (fun _ : ℕ => (beamTrialCutoff ε).toProj x) Filter.atTop
      (nhds x) := by
  have hproj : (beamTrialCutoff ε).toProj = beamTrial.starProjection := rfl
  simp only [hproj, Submodule.starProjection_eq_self_iff.2 hx]
  exact tendsto_const_nhds

/-- **The pole exclusion in operator norm**, `‖sin 2Θ₀‖ < 1`, for the genuine
beam.  This is the hypothesis the Ky Fan endpoint takes and the pointwise bound
of `beamTanTwoThetaAt_le` did not need. -/
theorem norm_offDiagonalPart_beamLowReflection_lt_one (ε : ℝ) (hε : 0 < ε)
    (hε100 : ε < 100) :
    ‖beamTrial.offDiagonalPart (beamLowReflection ε)‖ < 1 := by
  have hab : ritzHigh ε < (1001 / 2 : ℝ) := by
    have h := ritzHigh_lt_five_hundred hε100
    linarith
  exact TauCeti.norm_offDiagonalPart_lt_one_of_tendsto
    (beamComparison_reduces ε) (beamRitzOffDiagonal_isOddFor ε)
    (beamLowReflection_isSelfAdjoint ε) (beamLowReflection_sq ε)
    (beamLowReflection_mapsDomain ε) (beamLowReflection_comm ε)
    (a := ritzHigh ε) (b := 1001 / 2)
    (fun z hz => beamComparison_form_le_of_mem_beamTrial ε hε.le z hz)
    (fun z hz => beamComparison_form_ge_of_mem_orthogonal ε hε.le z hz)
    (fun _ : ℕ => ‖beamPerturbation ε‖) (fun _ => beamTrialCutoff ε)
    (fun _ => norm_nonneg _) hab (fun x hx => beamTrialCutoff_tendsto ε hx)

/-- The beam's compressed cutoff is the identity: the cutoff *is* the trial
projection, so no limit is needed. -/
theorem cutoffCorner_beamTrialCutoff (ε : ℝ) :
    DavisKahan1970.cutoffCorner (beamTrialCutoff ε)
      = ContinuousLinearMap.id ℂ beamTrial := by
  refine ContinuousLinearMap.ext fun z => ?_
  refine Subtype.ext ?_
  rw [DavisKahan1970.coe_cutoffCorner_apply]
  exact Submodule.starProjection_eq_self_iff.2 z.2

/-- The constant cutoff family converges strongly to the identity. -/
theorem stronglyTendsto_cutoffCorner_beamTrialCutoff (ε : ℝ) :
    StronglyTendsto (fun _ : ℕ => DavisKahan1970.cutoffCorner (beamTrialCutoff ε))
      Filter.atTop (ContinuousLinearMap.id ℂ beamTrial) := by
  intro z
  simp only [cutoffCorner_beamTrialCutoff]
  exact tendsto_const_nhds

/-- **The directed residual corner is the Rayleigh--Ritz residual.**  On the trial
subspace the ambient off-diagonal operator is already `(1 - P_Z)(ε t)`, so its
`Z → Zᗮ` corner is the recentered residual `R̂`, whose Gram is rank one. -/
theorem reflectionResidualCorner_beamRitzOffDiagonal (ε : ℝ) :
    DavisKahan1970.reflectionResidualCorner beamTrial (beamRitzOffDiagonal ε)
      = (beamTrialᗮ.subtypeL).adjoint ∘L (beamTrialBlock ε).residual := by
  refine ContinuousLinearMap.ext fun z => ?_
  have hz : beamRitzOffDiagonal ε (z : BeamL2) = (beamTrialBlock ε).residual z := by
    rw [beamRitzOffDiagonal_apply, Submodule.starProjection_eq_self_iff.2 z.2,
      starProjection_orthogonal_eq_zero_of_mem_beamTrial z.2, map_zero, map_zero,
      add_zero, beamTrialBlock_residual_apply,
      Submodule.starProjection_orthogonal_apply]
    rfl
  show (beamTrialᗮ.subtypeL).adjoint (beamRitzOffDiagonal ε (z : BeamL2)) = _
  rw [hz]
  rfl

/-- **Both singular values of the corner residual at once**: `‖R̂‖₂ = ‖R̂‖₁`, the
paper's `ε/√15`, because the recentered residual Gram is rank one. -/
theorem kyFanTwo_reflectionResidualCorner_le (ε : ℝ) :
    kyFanApproximationGauge 2
        (DavisKahan1970.reflectionResidualCorner beamTrial (beamRitzOffDiagonal ε))
      ≤ orthogonalResidualSingularValue ε := by
  have hadj : ‖(beamTrialᗮ.subtypeL : beamTrialᗮ →L[ℂ] BeamL2).adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact beamTrialᗮ.norm_subtypeL_le
  have hid : ‖ContinuousLinearMap.id ℂ beamTrial‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hnn : 0 ≤ kyFanApproximationGauge 2 ((beamTrialBlock ε).residual) :=
    kyFanApproximationGauge_nonneg 2 _
  rw [reflectionResidualCorner_beamRitzOffDiagonal]
  calc kyFanApproximationGauge 2
        ((beamTrialᗮ.subtypeL).adjoint ∘L (beamTrialBlock ε).residual)
      = kyFanApproximationGauge 2
          ((beamTrialᗮ.subtypeL).adjoint ∘L (beamTrialBlock ε).residual ∘L
            ContinuousLinearMap.id ℂ beamTrial) := by congr 1
    _ ≤ ‖(beamTrialᗮ.subtypeL : beamTrialᗮ →L[ℂ] BeamL2).adjoint‖ *
          kyFanApproximationGauge 2 ((beamTrialBlock ε).residual) *
          ‖ContinuousLinearMap.id ℂ beamTrial‖ :=
        kyFanApproximationGauge_comp_le _ _ _ _
    _ ≤ kyFanApproximationGauge 2 ((beamTrialBlock ε).residual) := by
        have h1 := mul_le_mul_of_nonneg_right hadj hnn
        have h2 := mul_le_mul_of_nonneg_left hid
          (mul_nonneg (norm_nonneg
            ((beamTrialᗮ.subtypeL : beamTrialᗮ →L[ℂ] BeamL2).adjoint)) hnn)
        linarith
    _ ≤ orthogonalResidualSingularValue ε := kyFanTwo_beamTrialBlock_residual_le ε

/-- **The two-term Ky Fan sum of the double-angle tangents** between the affine
trial subspace and the perturbed beam's low spectral subspace: the paper's
`tan 2θ₁ + tan 2θ₂`. -/
def beamTanTwoThetaSum (ε : ℝ) : ℝ :=
  kyFanApproximationGauge 2
    (DavisKahan1970.reflectionTangentCorner beamTrial (beamLowReflection ε))

/-- **Davis--Kahan 1970, the 2-norm sentence of equation (9.7), for the genuine
free-beam operator.**

`tan 2θ₁ + tan 2θ₂ ≤ tangentTwoThetaExactBound ε` — the same right side as the
bound-norm half, exactly as the paper says.  The comparison operator, the
residual and the gap are the ones (9.7) already used; what is new is that the
residual is charged at the two-term Ky Fan gauge, where the rank-one recentered
Gram makes it cost no more than at the operator norm. -/
theorem beamTanTwoThetaSum_le (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTwoThetaSum ε ≤ tangentTwoThetaExactBound ε := by
  have hritz : ritzHigh ε < 500 := ritzHigh_lt_five_hundred hε100
  have hgapPos : (0 : ℝ) < 500 - ritzHigh ε := by linarith
  have hab : ritzHigh ε < (1001 / 2 : ℝ) := by linarith
  have hσ0 : (0 : ℝ) ≤ orthogonalResidualSingularValue ε := by
    unfold orthogonalResidualSingularValue; positivity
  have hden : (1 : ℝ) - ritzHighCoefficient / 500 * ε ≠ 0 := by
    have h : ritzHigh ε = ε * ritzHighCoefficient := rfl
    rw [h] at hritz
    intro hzero
    apply absurd hritz
    push Not
    nlinarith [hzero]
  have hbound : tangentTwoThetaExactBound ε
      = 2 * orthogonalResidualSingularValue ε / (500 - ritzHigh ε) := by
    unfold tangentTwoThetaExactBound orthogonalResidualSingularValue
    rw [abs_of_pos hε, show ritzHigh ε = ε * ritzHighCoefficient from rfl,
      div_eq_div_iff hden (by
        rw [show ritzHigh ε = ε * ritzHighCoefficient from rfl] at hgapPos
        exact ne_of_gt hgapPos)]
    ring
  have hmain := DavisKahan1970.gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan
    (beamComparison_reduces ε) (beamRitzOffDiagonal_isOddFor ε)
    (beamLowReflection_isSelfAdjoint ε) (beamLowReflection_sq ε)
    (beamLowReflection_mapsDomain ε) (beamLowReflection_comm ε)
    (a := ritzHigh ε) (b := 1001 / 2)
    (fun z hz => beamComparison_form_le_of_mem_beamTrial ε hε.le z hz)
    (fun z hz => beamComparison_form_ge_of_mem_orthogonal ε hε.le z hz)
    hab (norm_offDiagonalPart_beamLowReflection_lt_one ε hε hε100)
    (σ := fun _ : ℕ => ‖beamPerturbation ε‖) (fun _ => norm_nonneg _)
    (fun _ => beamTrialCutoff ε)
    (stronglyTendsto_cutoffCorner_beamTrialCutoff ε) 2
  have hres := kyFanTwo_reflectionResidualCorner_le ε
  have hnn : 0 ≤ beamTanTwoThetaSum ε := kyFanApproximationGauge_nonneg 2 _
  rw [hbound, le_div_iff₀ hgapPos]
  have hchain : ((1001 : ℝ) / 2 - ritzHigh ε) * beamTanTwoThetaSum ε
      ≤ 2 * orthogonalResidualSingularValue ε := by
    refine le_trans hmain ?_
    linarith
  nlinarith [hchain, hnn, hgapPos]

/-- **The 2-norm sentence of equation (9.7) as printed**: the same right side as
the bound-norm half. -/
theorem beamTanTwoThetaSum_lt_printed (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTwoThetaSum ε
      < ((1291 : ℝ) / 1250000 * ε) / (1 - (7887 : ℝ) / 5000000 * ε) :=
  equation_9_7 ε (beamTanTwoThetaSum ε) hε hε100 (beamTanTwoThetaSum_le ε hε hε100)

end

end Model
end FreeBeam
end DavisKahan
end TauCeti
