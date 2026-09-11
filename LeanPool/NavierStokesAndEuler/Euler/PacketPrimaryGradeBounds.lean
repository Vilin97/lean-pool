/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimarySourceRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalInitialData
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketLinearCostAbsorption
import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalEnvelope
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryCorrector
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketNormalBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradientBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryBudget
import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlWeight
import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialWeight
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradientWeight
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevScaling
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderPressureWeight
import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardCoefficientGevrey
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryPaths
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryHomogeneity
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing
import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointUnitBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardBounds

/-! The actual primary closes the first packet grade.  Its terminal scalar
amplitude is canceled against the actual time profile, and only fixed source
costs are absorbed into the radius. -/

section

/-! Same-radius estimates for the actual corrector, divided by the prescribed time profile. -/

section

/-!
Unit-terminal-data estimates for the actual joined primary. The same
external radius controls its history, actual trace, and weighted future.
-/

@[expose] public section

noncomputable section

namespace EulerTransversePacketPrimary.Budget

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerGevrey EulerParameterWordGevrey EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerContinuousTimeWeight EulerTimeIntervalRestriction
  EulerElapsedTimePathGluing EulerFixedEvolutionSobolev
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {ι : Type*} [Fintype ι] {q : ℕ}
  {L : EulerTransversePacketJoin.Budget D τ hτ hτT B ι q}
  (H : Budget L) (Y : InitialData P D)
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1)
  (d : ℕ)
  (hYb : ∀ n, block directions q (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤
    majorant L.R d n)

include H hdir hYb

theorem terminal_bound (n : ℕ) :
    block directions q (fun a => translate P a
      ((forwardInitial τ hτ hτT B Y).value : CylinderL2 P U)) n 0 ≤
        H.endpointBudget.coordinateCost*majorant L.R (d+2) n :=
  (trace_block_le P directions q
    (B.coefficients.endpointCoordinate P (Y.value : CylinderL2 P U))
    (EulerTransversePacketEndpoint.coordinatePath_orbit B (endpointData τ hτ hτT Y))
    ⟨τ,hτ.le,le_rfl⟩ n 0).trans
      (H.endpointBudget.coordinate_unit_bound P directions hdir Y.value Y.orbit d hYb n)

theorem past_velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a (pastVelocity τ hτ hτT B Y)) n 0 ≤
      H.endpointBudget.velocityCost*majorant L.R (d+2) n :=
  H.endpointBudget.velocity_unit_bound P directions hdir Y.value Y.orbit d hYb n

theorem past_derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a (pastDerivative τ hτ hτT B Y)) n 0 ≤
      H.endpointBudget.derivativeCost*majorant L.R (d+3) n :=
  H.endpointBudget.derivative_unit_bound P directions hdir Y.value Y.orbit d hYb n

theorem future_velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (futureVelocity τ hτ hτT B Y))) n 0 ≤
        (3*sobolevCoefficientAmplitude ι q L.Rc L.C₀)*majorant L.R (d+3) n := by
  have hf (j : ℕ) : block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath (zeroForcing (P := P) (D.tail τ hτ.le
          hτT)))))
        j 0 ≤ 0*majorant L.R (d+2) j := by
    simp only [HistoryData.forcingPath,zeroForcing,map_zero,zero_mul]
    erw [map_zero]
    simp only [map_zero,block_zero_function,le_refl]
  dsimp only [futureVelocity]
  rw [show d+3=d+2+1 by omega]
  exact
    (zeroForcing (D.tail τ hτ.le hτT)).source_velocity_normalized_bound (forwardInitial τ hτ hτT B
        Y)
      L.g L.positive directions hdir q L.neighborhood L.neighborhood_measurable L.neighborhood_open
      L.support_subset L.neighborhood_halfball L.initial_one
      L.C H.endpointBudget.coordinateCost 0 L.Rc L.C₀ L.C₁ L.Ri L.R
      L.C_nonneg H.endpointBudget.coordinateCost_nonneg le_rfl L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg
      L.forward_inverse
      (fun j t x => L.frame_bound j (tailInclusion D.T τ hτ.le t) x)
      (fun j t x => L.frameDerivative_bound j (tailInclusion D.T τ hτ.le t) x)
      L.forcing_radius H.forward_radius L.propagator (d+2) hf
      (H.terminal_bound Y directions hdir d hYb) L.radius_bounds.2 n

theorem future_derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (futureDerivative τ hτ hτT B Y))) n 0 ≤
        EulerSourceCylinderTimeBounds.physicalCost ι q L.Ri L.C₀ L.C₁ 0 1*majorant L.R (d+3) n := by
  have hf (j : ℕ) : block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath (zeroForcing (P := P) (D.tail τ hτ.le
          hτT)))))
        j 0 ≤ 0*majorant L.R (d+2) j := by
    simp only [HistoryData.forcingPath,zeroForcing,map_zero,zero_mul]
    erw [map_zero]
    simp only [map_zero,block_zero_function,le_refl]
  dsimp only [futureDerivative]
  rw [show d+3=d+2+1 by omega]
  exact
    (zeroForcing (D.tail τ hτ.le hτT)).source_derivative_normalized_bound (forwardInitial τ hτ hτT
        B Y)
      L.g L.positive directions hdir q L.neighborhood L.neighborhood_measurable L.neighborhood_open
      L.support_subset L.neighborhood_halfball L.initial_one
      L.C H.endpointBudget.coordinateCost 0 L.Rc L.C₀ L.C₁ L.Ri L.R
      L.C_nonneg H.endpointBudget.coordinateCost_nonneg le_rfl L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg
      L.forward_inverse
      (fun j t x => L.frame_bound j (tailInclusion D.T τ hτ.le t) x)
      (fun j t x => L.frameDerivative_bound j (tailInclusion D.T τ hτ.le t) x)
      L.forcing_radius H.forward_radius L.propagator (d+2) hf
      (H.terminal_bound Y directions hdir d hYb) L.radius_bounds.1 n

theorem velocity_unit_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B Y))) n 0 ≤
        H.velocityCost*majorant L.R (d+3) n := by
  have hb := normalized_join_block P D.T τ hτ.le hτT.le L.g L.positive L.initial_one
    (pastVelocity τ hτ hτT B Y) (futureVelocity τ hτ hτT B Y) (velocity_match τ hτ hτT B Y)
    (pastVelocity_orbit τ hτ hτT B Y) (futureVelocity_orbit τ hτ hτT B Y) directions q n 0
  have hC : 0 ≤ H.endpointBudget.velocityCost :=
    mul_nonneg (mul_nonneg (by norm_num)
      (sobolevCoefficientAmplitude_nonneg q L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg))
      H.endpointBudget.coordinateCost_nonneg
  have hp := (H.past_velocity_bound Y directions hdir d hYb n).trans
    (mul_le_mul_of_nonneg_left (majorant_mono_shift L.R L.radius_bounds.1 (d+2) (d+3) n (by
        omega)) hC)
  exact hb.trans (by
    simpa only [velocityCost,add_mul] using
      add_le_add hp (H.future_velocity_bound Y directions hdir d hYb n))

theorem derivative_unit_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (derivativePath τ hτ hτT B Y))) n 0 ≤
        H.derivativeCost*majorant L.R (d+3) n := by
  have hb := normalized_join_block P D.T τ hτ.le hτT.le L.g L.positive L.initial_one
    (pastDerivative τ hτ hτT B Y) (futureDerivative τ hτ hτT B Y) (derivative_match τ hτ hτT B Y)
    (pastDerivative_orbit τ hτ hτT B Y) (futureDerivative_orbit τ hτ hτT B Y) directions q n 0
  exact hb.trans (by
    simpa only [derivativeCost,add_mul] using
      add_le_add (H.past_derivative_bound Y directions hdir d hYb n)
        (H.future_derivative_bound Y directions hdir d hYb n))

end EulerTransversePacketPrimary.Budget

end
end

end

section

/-! Unit-data estimates extend to arbitrary actual terminal amplitudes at the same radius. -/

@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerContinuousTimeWeight EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {D : Data U} {ι : Type*} [Fintype ι]

theorem initial_amplitude_bound
    (S : InitialData P D → C(Icc (0 : ℝ) D.T, CylinderL2 P V))
    (hs : ∀ Y, ContDiff ℝ ∞ (fun a => pathTranslate P a (S Y)))
    (hm : ∀ Y Z (a : ℝ), Z.value = a • Y.value → S Z = a • S Y)
    (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t)
    (directions : ι → LiftTangent) (q : ℕ) (R C : ℝ) (d e : ℕ)
    (hunit : ∀ Y : InitialData P D,
      (∀ n, block directions q (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤ majorant R
          d n) →
      ∀ n, block directions q (fun a => pathTranslate P a (normalize g hg (S Y))) n 0 ≤ C*majorant
          R e n)
    (Y : InitialData P D) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ n, block directions q (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤
        A*majorant R d n)
    (n : ℕ) :
    block directions q (fun a => pathTranslate P a (normalize g hg (S Y))) n 0 ≤
      (C*A)*majorant R e n := by
  by_cases hz : A = 0
  · have hv := value_zero_of_block_zero_bound directions q
      (fun a => translate P a (Y.value : CylinderL2 P U)) 0
      (by simpa only [hz,zero_mul] using hb 0)
    rw [translate_zero] at hv
    have hy : Y.value = 0 := Subtype.ext hv
    have hS : S Y = 0 := by
      have he := hm Y Y 0 (hy.trans (zero_smul ℝ Y.value).symm)
      simpa only [zero_smul] using he
    simp only [hS,map_zero,block_zero_function,hz,mul_zero,zero_mul,le_refl]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
    let Z := Y.smul A⁻¹
    have hZ (j : ℕ) : block directions q
        (fun a => translate P a (Z.value : CylinderL2 P U)) j 0 ≤ majorant R d j := by
      have he : (fun a => translate P a (Z.value : CylinderL2 P U)) =
          fun a => A⁻¹ • translate P a (Y.value : CylinderL2 P U) := by
        funext a
        exact (translate P a).map_smul A⁻¹ (Y.value : CylinderL2 P U)
      rw [he]
      simpa only [one_mul] using block_normalize_bound directions q
        (fun a => translate P a (Y.value : CylinderL2 P U)) Y.orbit
        A hApos R 1 d j 0 (by simpa only [one_mul] using hb j)
    have hrestore : S Y = A • S Z := by
      rw [hm Y Z A⁻¹ rfl,smul_smul,mul_inv_cancel₀ hz,one_smul]
    have hsZ : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (normalize g hg (S Z))) := by
      have he : (fun a : LiftTangent => pathTranslate P a (normalize g hg (S Z))) =
          fun a => normalize g hg (pathTranslate P a (S Z)) := by
        funext a
        apply ContinuousMap.ext
        intro t
        exact (translate P a).map_smul (g t)⁻¹ (S Z t)
      rw [he]
      exact (normalize (E := CylinderL2 P V) g hg).contDiff.comp (hs Z)
    have hr := block_restore_bound directions q
      (fun a => pathTranslate P a (normalize g hg (S Z)))
      (fun a => pathTranslate P a (normalize g hg (S Y)))
      hsZ A hA
      (fun a => by rw [hrestore,map_smul,map_smul]) R C e n 0 (hunit Z hZ n)
    exact hr.trans_eq (by ring)

end EulerTransversePacketProvider

end
end

end

section

/-!
The actual primary A/g and A_t/g retain one fixed mixed Sobolev radius.
The constants and guards depend only on source coefficients, the history
length and the genuine propagator bound. Arbitrary terminal amplitude is
restored by the proved exact homogeneity of the constructed solution.
-/

@[expose] public section

noncomputable section

namespace EulerTransversePacketPrimary.Budget

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerTransversePacketProvider EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {ι : Type*} [Fintype ι] {q : ℕ}
  {L : EulerTransversePacketJoin.Budget D τ hτ hτT B ι q}
  (H : Budget L) (Y : InitialData P D)
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1)
  (A : ℝ) (hA : 0 ≤ A) (d : ℕ)
  (hYb : ∀ n, block directions q (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤
    A * majorant L.R d n)

include hdir hA hYb

theorem velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B Y))) n 0 ≤
        (H.velocityCost*A)*majorant L.R (d+3) n :=
  initial_amplitude_bound (fun Z => velocityPath τ hτ hτT B Z)
    (velocityPath_orbit τ hτ hτT B) (velocityPath_eq_smul τ hτ hτT B)
    L.fullProfile L.fullProfile_pos directions q L.R H.velocityCost d (d+3)
    (fun Z hb => H.velocity_unit_bound Z directions hdir d hb) Y A hA hYb n

theorem derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (derivativePath τ hτ hτT B Y))) n 0 ≤
        (H.derivativeCost*A)*majorant L.R (d+3) n :=
  initial_amplitude_bound (fun Z => derivativePath τ hτ hτT B Z)
    (derivativePath_orbit τ hτ hτT B) (derivativePath_eq_smul τ hτ hτT B)
    L.fullProfile L.fullProfile_pos directions q L.R H.derivativeCost d (d+3)
    (fun Z hb => H.derivative_unit_bound Z directions hdir d hb) Y A hA hYb n

end EulerTransversePacketPrimary.Budget

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketPrimary

open Set EulerTransversePacketProvider EulerSmoothLimit EulerLiftedGradientSpace
    EulerMeanCoefficients EulerGevrey
  EulerPacketProfileRecursion EulerCylinderSobolev EulerParameterWordGevrey
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerContinuousTimeWeight
open scoped ContDiff

private theorem direction_norm_bound (i : Fin 4) : ‖standardDirection i‖ ≤ 1 := by
  cases i using Fin.cases <;> simp [Prod.norm_def]

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)
  (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t)
  (q : ℕ) (Rc C R A : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
  (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R) (d : ℕ)
  (hbA : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (velocityPath τ hτ hτT B Y))) n 0 ≤
      A * majorant R d n)
  (hbAt : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (derivativePath τ hτ hτT B Y))) n 0 ≤
      A * majorant R d n)
  (hbK : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialCoefficientPath) a‖ ≤
    C * majorant Rc 0 n)
  (hbKt : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialDerivative) a‖ ≤
    C * majorant Rc 0 n)
  (hbI : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤ C * majorant Rc 0
      n)
  (hbIt : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.inverseDerivative) a‖ ≤
    C * majorant Rc 0 n)

include hRc hC hA hR hbA hbK in
theorem potentialPath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (potentialPath τ hτ hτT B Y))) n 0 ≤
      (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d n :=
  EulerCylinderPotential.normalized_potentialPath_block_bound P g (velocityPath τ hτ hτT B Y)
    D.potentialCoefficientPath hg D.potentialCoefficientPath_orbit
    (EulerCylinderPotential.weighted_orbit P (reciprocal g hg) (velocityPath τ hτ hτT B Y)
        (velocityPath_orbit τ hτ hτT B Y))
    standardDirection direction_norm_bound q Rc C R A hRc hC hA hR hbK d hbA n

include hRc hC hA hR hbA hbAt hbK hbKt in
theorem potentialTimePath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (potentialTimePath τ hτ hτT B Y)))
          n 0 ≤
      (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d n :=
  EulerCylinderPotential.normalized_potentialDerivative_block_bound P D.T
    D.potentialCoefficientPath D.potentialDerivative D.potentialCoefficientPath_orbit
        D.potentialDerivative_orbit
    (velocityPath τ hτ hτT B Y) (derivativePath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y)
        (derivativePath_orbit τ hτ hτT B Y)
    g hg standardDirection direction_norm_bound q Rc C R A hRc hC hA hR hbK hbKt d hbA hbAt n

include hRc hC hA hR hbA hbK hbI in
theorem correctorPath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (correctorPath τ hτ hτT B Y))) n 0 ≤
      (27*(sobolevCoefficientAmplitude (Fin 4) q Rc C)^2*(P*A))*majorant R (d+1) n := by
  have hp : 0 ≤ P := (Fact.out : 0 < P).le
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q Rc C hRc hC
  have h := EulerCylinderSlowCurl.normalized_path_block_bound P g D.FInv.field
    (potentialPath τ hτ hτT B Y) (potentialPath_orbit τ hτ hτT B Y) hg D.FInv.translation_contDiff
    q Rc C R (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A)) hRc hC (by positivity) hR hbI d
    (potentialPath_normalized_bound τ hτ hτT B Y g hg q Rc C R A hRc hC hA hR d hbA hbK) n
  exact h.trans_eq (by ring)

include hRc hC hA hR hbA hbAt hbK hbKt hbI hbIt in
theorem correctorTimePath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (correctorTimePath τ hτ hτT B Y)))
          n 0 ≤
      (108*(sobolevCoefficientAmplitude (Fin 4) q Rc C)^2*(P*A))*majorant R (d+1) n := by
  have hp : 0 ≤ P := (Fact.out : 0 < P).le
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q Rc C hRc hC
  have hRn : 0 ≤ R := (sobolevCoefficientRadius_nonneg (ι := Fin 4) Rc hRc).trans hR
  have hQ (j : ℕ) : block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (potentialPath τ hτ hτT B Y))) j 0 ≤
        (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d j := by
    apply (potentialPath_normalized_bound τ hτ hτT B Y g hg q Rc C R A hRc hC hA hR d hbA hbK
        j).trans
    have hn := mul_nonneg
      (show 0 ≤ sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A) by positivity)
      (majorant_nonneg R hRn d j)
    nlinarith
  have h := EulerCylinderSlowCurl.normalized_derivative_block_bound P D.T g hg
    D.FInv.field D.inverseDerivative (potentialPath τ hτ hτT B Y) (potentialTimePath τ hτ hτT B Y)
    (potentialPath_orbit τ hτ hτT B Y) (potentialTimePath_orbit τ hτ hτT B Y)
        D.FInv.translation_contDiff D.inverseDerivative_orbit
    q Rc C R (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A)) hRc hC (by positivity) hR
    hbI hbIt d hQ (potentialTimePath_normalized_bound τ hτ hτT B Y g hg q Rc C R A hRc hC hA hR d
        hbA hbAt hbK hbKt) n
  exact h.trans_eq (by ring)

end EulerTransversePacketPrimary

namespace EulerTransversePacketPrimary.Budget

open Set ContinuousLinearMap EulerSmoothLimit EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight EulerCylinderSobolev
  EulerSourceNormalResidualBounds EulerMeanCoefficients EulerTimeLpGramGevrey
  EulerSourceCylinderTimeBounds EulerCylinderDirichlet.Coefficients
      EulerTransverseForwardCoefficientGevrey
open scoped ContDiff

private theorem standard_norm (i : Fin 4) : ‖standardDirection i‖ ≤ 1 := by
  cases i using Fin.cases <;> simp [Prod.norm_def]

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {q : ℕ}
  {L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) q}
  (H : Budget L) (N : EulerTransversePacketJoin.NormalBudget D q L.R)

theorem derivativeCost_nonneg : 0 ≤ H.derivativeCost := by
  have hi := (inverseRadius_bounds (D.tail τ hτ.le hτT).frameLower L.C₀ L.Rc L.Ri
    (D.tail τ hτ.le hτT).frameLower_pos L.Rc_nonneg L.forward_inverse).1
  have h0 := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg
  have h1 := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q L.Rc L.C₁ L.Rc_nonneg L.C₁_nonneg
  have hb0 := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*L.Ri) L.C₀ (by
      positivity) L.C₀_nonneg
  have hb1 := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*L.Ri) L.C₁ (by
      positivity) L.C₁_nonneg
  have hc0 := L.C₀_nonneg
  have hc1 := L.C₁_nonneg
  have hbb := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*L.Ri) (18*L.Ri*L.C₀*L.C₁)
    (by positivity) (by positivity)
  have hbf := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*L.Ri) (3*L.Ri*L.C₀)
    (by positivity) (by positivity)
  have ht := H.endpointBudget.coordinateCost_nonneg
  unfold derivativeCost EndpointBudget.derivativeCost physicalCost coordinateCost
  change 0 ≤ 3*sobolevCoefficientAmplitude (Fin 4) q L.Rc L.C₁*H.endpointBudget.coordinateCost +
    3*sobolevCoefficientAmplitude (Fin 4) q L.Rc L.C₀ +
      (3*sobolevCoefficientAmplitude (Fin 4) q (4*L.Ri) L.C₁*1 +
        3*sobolevCoefficientAmplitude (Fin 4) q (4*L.Ri) L.C₀ *
          (3*sobolevCoefficientAmplitude (Fin 4) q (4*L.Ri) (18*L.Ri*L.C₀*L.C₁)*1 +
            3*sobolevCoefficientAmplitude (Fin 4) q (4*L.Ri) (3*L.Ri*L.C₀)*0))
  positivity

/-- Common cost, given by `H.velocityCost+H.derivativeCost`. -/
def commonCost : ℝ := H.velocityCost+H.derivativeCost
/-- Pressure amplitude, given by `P*pressureCost (Fin 4) q N.Ri N.C N.C 0 H.commonCost`. -/
def pressureAmplitude : ℝ := P*pressureCost (Fin 4) q N.Ri N.C N.C 0 H.commonCost
/-- Potential amplitude, given by `3*N.blockAmplitude*(P*H.commonCost)`. -/
def potentialAmplitude : ℝ := 3*N.blockAmplitude*(P*H.commonCost)
/-- Potential time amplitude, given by `6*N.blockAmplitude*(P*H.commonCost)`. -/
def potentialTimeAmplitude : ℝ := 6*N.blockAmplitude*(P*H.commonCost)
/-- Corrector amplitude, given by `27*N.blockAmplitude^2*(P*H.commonCost)`. -/
def correctorAmplitude : ℝ := 27*N.blockAmplitude^2*(P*H.commonCost)
/-- Corrector time amplitude, given by `108*N.blockAmplitude^2*(P*H.commonCost)`. -/
def correctorTimeAmplitude : ℝ := 108*N.blockAmplitude^2*(P*H.commonCost)

theorem commonCost_nonneg : 0 ≤ H.commonCost := add_nonneg H.velocityCost_nonneg
    H.derivativeCost_nonneg
theorem velocityCost_le_common : H.velocityCost ≤ H.commonCost := le_add_of_nonneg_right
    H.derivativeCost_nonneg
theorem derivativeCost_le_common : H.derivativeCost ≤ H.commonCost := le_add_of_nonneg_left
    H.velocityCost_nonneg

theorem pressureAmplitude_nonneg : 0 ≤ H.pressureAmplitude (P := P) N := by
  have hRi := N.Ri_nonneg
  have hC := N.C_nonneg
  have hH := H.commonCost_nonneg
  have hP := (Fact.out : 0 < P).le
  have hm := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*N.Ri) (3*N.Ri*N.C)
    (by positivity) (by positivity)
  have hM := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*N.Ri) N.C (by positivity) hC
  unfold pressureAmplitude pressureCost
  positivity

theorem correctorAmplitude_nonneg : 0 ≤ H.correctorAmplitude (P := P) N := by
  have hH := H.commonCost_nonneg
  have hP := (Fact.out : 0 < P).le
  unfold correctorAmplitude
  positivity

theorem correctorTimeAmplitude_nonneg : 0 ≤ H.correctorTimeAmplitude (P := P) N := by
  have hH := H.commonCost_nonneg
  have hP := (Fact.out : 0 < P).le
  unfold correctorTimeAmplitude
  positivity

variable (Y : InitialData P D) (A : ℝ) (hA : 0 ≤ A) (d : ℕ)
  (hYb : ∀ n, block standardDirection q (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤
    A * majorant L.R d n)

include hA hYb

theorem velocity_common_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B Y))) n 0 ≤
        (H.commonCost*A)*majorant L.R (d+3) n :=
  (H.velocity_bound Y standardDirection standard_norm A hA d hYb n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right H.velocityCost_le_common hA)
      (majorant_nonneg L.R (zero_le_one.trans L.radius_bounds.1) (d+3) n))

theorem derivative_common_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (derivativePath τ hτ hτT B Y))) n 0 ≤
        (H.commonCost*A)*majorant L.R (d+3) n :=
  (H.derivative_bound Y standardDirection standard_norm A hA d hYb n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right H.derivativeCost_le_common hA)
      (majorant_nonneg L.R (zero_le_one.trans L.radius_bounds.1) (d+3) n))

theorem pressure_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (pressurePath τ hτ hτT B Y))) n 0 ≤
        (H.pressureAmplitude (P := P) N*A)*majorant L.R (d+3) n := by
  have he : normalize L.fullProfile L.fullProfile_pos (pressurePath τ hτ hτT B Y) =
      sourcePressure P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower 0
        (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B Y)) := by
    simpa only [EulerTransversePacketPrimary.pressurePath, EulerContinuousTimeWeight.normalize,
        map_zero] using
      (sourcePressure_weight P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
        (reciprocal L.fullProfile L.fullProfile_pos) 0 (velocityPath τ hτ hτT B Y)).symm
  rw [he]
  have hzero : ContDiff ℝ ∞ (fun a : LiftTangent =>
      pathTranslate P a (0 : C(Icc (0 : ℝ) D.T,LiftL2 P))) := by
    simpa only [map_zero] using (contDiff_const : ContDiff ℝ ∞
      (fun _ : LiftTangent => (0 : C(Icc (0 : ℝ) D.T,LiftL2 P))))
  have h := sourcePressure_block_bound P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    0 (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B Y))
    standardDirection standard_norm q hzero
    (normalize_orbit_contDiff P L.fullProfile L.fullProfile_pos _ (velocityPath_orbit τ hτ hτT B Y))
    N.Rc N.C N.C N.Ri L.R 0 (H.commonCost*A) N.Rc_nonneg N.C_nonneg N.C_nonneg le_rfl
    (mul_nonneg H.commonCost_nonneg hA) N.inverse_radius N.pressure_radius N.normal_bound
        N.strain_bound
    (d+3) (fun j => by simp only [map_zero,block_zero_function,zero_mul,le_refl])
    (H.velocity_common_bound Y A hA d hYb) n
  exact h.trans_eq (by unfold pressureAmplitude pressureCost; ring)

theorem pressure_gradient_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (scalarGradientField τ hτ hτT B Y).path)) n 0 ≤
        (3*H.pressureAmplitude (P := P) N*A)*majorant L.R (d+4) n := by
  change block standardDirection q (fun a => pathTranslate P a
    (normalize L.fullProfile L.fullProfile_pos
      (EulerPacketCylinderField.scalarGradientPath (pressurePath τ hτ hτT B Y)))) n 0 ≤ _
  have h := EulerPacketCylinderField.scalarGradientPath_normalized_majorant
    (pressurePath τ hτ hτT B Y) (pressurePath_orbit τ hτ hτT B Y)
    L.fullProfile L.fullProfile_pos q L.R (H.pressureAmplitude (P := P) N*A) (d+3)
    (H.pressure_bound N Y A hA d hYb) n
  simpa only [show d+3+1=d+4 by omega,mul_assoc] using h

theorem potential_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (potentialPath τ hτ hτT B Y))) n 0 ≤
        (H.potentialAmplitude (P := P) N*A)*majorant L.R (d+3) n := by
  have hc := N.coefficient_bounds
  have h := potentialPath_normalized_bound τ hτ hτT B Y L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (H.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg H.commonCost_nonneg hA) N.radius (d+3)
    (H.velocity_common_bound Y A hA d hYb) (fun j a => (hc.2.2 j a).2.2.1) n
  exact h.trans_eq (by
      unfold potentialAmplitude EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

theorem potential_time_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (potentialTimePath τ hτ hτT B Y))) n 0 ≤
        (H.potentialTimeAmplitude (P := P) N*A)*majorant L.R (d+3) n := by
  have hc := N.coefficient_bounds
  have h := potentialTimePath_normalized_bound τ hτ hτT B Y L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (H.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg H.commonCost_nonneg hA) N.radius (d+3)
    (H.velocity_common_bound Y A hA d hYb) (H.derivative_common_bound Y A hA d hYb)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).2.2.2) n
  exact h.trans_eq (by
      unfold potentialTimeAmplitude EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

theorem corrector_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (correctorPath τ hτ hτT B Y))) n 0 ≤
        (H.correctorAmplitude (P := P) N*A)*majorant L.R (d+4) n := by
  have hc := N.coefficient_bounds
  have h := correctorPath_normalized_bound τ hτ hτT B Y L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (H.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg H.commonCost_nonneg hA) N.radius (d+3)
    (H.velocity_common_bound Y A hA d hYb)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).1) n
  rw [show d+3+1=d+4 by omega] at h
  exact h.trans_eq (by
      unfold correctorAmplitude EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

theorem corrector_time_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (correctorTimePath τ hτ hτT B Y))) n 0 ≤
        (H.correctorTimeAmplitude (P := P) N*A)*majorant L.R (d+4) n := by
  have hc := N.coefficient_bounds
  have h := correctorTimePath_normalized_bound τ hτ hτT B Y L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (H.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg H.commonCost_nonneg hA) N.radius (d+3)
    (H.velocity_common_bound Y A hA d hYb) (H.derivative_common_bound Y A hA d hYb)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).2.2.2)
    (fun j a => (hc.2.2 j a).1) (fun j a => (hc.2.2 j a).2.1) n
  rw [show d+3+1=d+4 by omega] at h
  exact h.trans_eq (by
      unfold correctorTimeAmplitude EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

end EulerTransversePacketPrimary.Budget

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketPrimary.Budget

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerPacketShiftArithmetic EulerContinuousTimeWeight
  EulerParameterWordGevrey EulerGevrey EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerPacketTimeProfile EulerCylinderSobolev

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}
  {L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6}
  (H : Budget L) (N : EulerTransversePacketJoin.NormalBudget D 6 L.R) (C : ℝ)

/-- C bounds the unmultiplied terminal datum.  No guard involves the scalar
amplitude α, and the original radius is retained. -/
structure GradeGuards : Prop where
  terminal_nonneg : 0 ≤ C
  common : H.commonCost*C ≤ L.R
  corrector : H.correctorAmplitude (P := P) N*C ≤ L.R
  correctorTime : H.correctorTimeAmplitude (P := P) N*C ≤ L.R
  pressureGradient : 3*H.pressureAmplitude (P := P) N*C ≤ L.R

variable (W : GradeGuards (P := P) H N C) (Y : InitialData P D) (α : ℝ) (hα : 0 < α)
  (hYb : ∀ n, block standardDirection 6 (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤
    (α * C) * majorant L.R 0 n)

include W hYb hα

theorem grade_fields :
    ((vectorField τ hτ hτT B Y).normalized D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)).WordBound 6 L.R 1 (highShift 1) ∧
    ((vectorDerivativeField τ hτ hτT B Y).normalized D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)).WordBound 6 L.R 1 (highShift 1) ∧
    ((correctorField τ hτ hτT B Y).normalized D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)).WordBound 6 L.R 1 (highShift 1) ∧
    ((correctorDerivativeField τ hτ hτT B Y).normalized D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)).WordBound 6 L.R 1 (highShift 1) ∧
    ((scalarGradientField τ hτ hτT B Y).normalized D.T_pos.le (α • L.fullProfile)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα)).WordBound 6 L.R 1 (highShift 1) := by
  have ha := mul_nonneg hα.le W.terminal_nonneg
  have hv : ((vectorField τ hτ hτT B Y).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R ((H.commonCost*C)*α) 3 := by
    intro n
    simpa only [Field.normalized_path,vectorField,Nat.zero_add,mul_assoc,mul_left_comm,mul_comm]
        using H.velocity_common_bound Y _ ha 0 hYb n
  have ht : ((vectorDerivativeField τ hτ hτT B Y).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R ((H.commonCost*C)*α) 3 := by
    intro n
    simpa only [Field.normalized_path, vectorDerivativeField, Nat.zero_add, mul_assoc,
        mul_left_comm, mul_comm] using H.derivative_common_bound Y _ ha 0 hYb n
  have hc : ((correctorField τ hτ hτT B Y).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R ((H.correctorAmplitude (P := P) N*C)*α) 4 := by
    intro n
    simpa only [Field.normalized_path,correctorField,Nat.zero_add,mul_assoc,mul_left_comm,mul_comm]
        using H.corrector_bound N Y _ ha 0 hYb n
  have hct : ((correctorDerivativeField τ hτ hτT B Y).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R ((H.correctorTimeAmplitude (P := P) N*C)*α) 4 := by
    intro n
    simpa only [Field.normalized_path, correctorDerivativeField, Nat.zero_add, mul_assoc,
        mul_left_comm, mul_comm] using H.corrector_time_bound N Y _ ha 0 hYb n
  have hp : ((scalarGradientField τ hτ hτT B Y).normalized D.T_pos.le L.fullProfile
      L.fullProfile_pos).WordBound 6 L.R ((3*H.pressureAmplitude (P := P) N*C)*α) 4 := by
    intro n
    simpa only [Field.normalized_path,Nat.zero_add,mul_assoc,mul_left_comm,mul_comm] using
        H.pressure_gradient_bound N Y _ ha 0 hYb n
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (hv.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos α hα).absorb_amplitude_to
      L.radius_bounds.1 (mul_nonneg H.commonCost_nonneg W.terminal_nonneg) W.common (by
          norm_num [highShift])
  · exact (ht.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos α hα).absorb_amplitude_to
      L.radius_bounds.1 (mul_nonneg H.commonCost_nonneg W.terminal_nonneg) W.common (by
          norm_num [highShift])
  · exact (hc.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos α hα).absorb_amplitude_to
      L.radius_bounds.1 (mul_nonneg (H.correctorAmplitude_nonneg N) W.terminal_nonneg)
      W.corrector (by norm_num [highShift])
  · exact (hct.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos α hα).absorb_amplitude_to
      L.radius_bounds.1 (mul_nonneg (H.correctorTimeAmplitude_nonneg N) W.terminal_nonneg)
      W.correctorTime (by norm_num [highShift])
  · exact (hp.scale_profile D.T_pos.le L.fullProfile L.fullProfile_pos α hα).absorb_amplitude_to
      L.radius_bounds.1 (mul_nonneg (mul_nonneg (by
          norm_num) (H.pressureAmplitude_nonneg N)) W.terminal_nonneg)
      W.pressureGradient (by norm_num [highShift])

theorem profile_budget (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector P)
    (S : Scales (Icc (0 : ℝ) D.T)) (hgrowth : S.growth = α • L.fullProfile) :
    ProfileBudget (profileRegularity τ hτ hτT B Y O hcorrector) S L.R 1 := by
  obtain ⟨hv,ht,hc,hct,hp⟩ := H.grade_fields N C W Y α hα hYb
  have he : S.high 1 = α • L.fullProfile := by
    apply ContinuousMap.ext
    intro t
    rw [S.high_one,hgrowth]
  have hz := Field.wordBound_normalized_of_zero (Field.zero P D.T)
    (fun _ _ _ => rfl) D.T_pos.le (S.mean 1) (S.mean_pos 1) 6 L.R (meanShift 1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Field.normalized_wordBound_congr (vectorField τ hτ hτT B Y) D.T_pos.le
      (S.high 1) (α • L.fullProfile) (S.high_pos 1)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα) he 6 (highShift 1) L.R 1 hv
  · exact Field.normalized_wordBound_congr (vectorDerivativeField τ hτ hτT B Y) D.T_pos.le
      (S.high 1) (α • L.fullProfile) (S.high_pos 1)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα) he 6 (highShift 1) L.R 1 ht
  · exact hz.mono_amplitude (zero_le_one.trans L.radius_bounds.1) zero_le_one
  · exact hz.mono_amplitude (zero_le_one.trans L.radius_bounds.1) zero_le_one
  · exact Field.normalized_wordBound_congr (correctorField τ hτ hτT B Y) D.T_pos.le
      (S.high 1) (α • L.fullProfile) (S.high_pos 1)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα) he 6 (highShift 1) L.R 1 hc
  · exact Field.normalized_wordBound_congr (correctorDerivativeField τ hτ hτT B Y) D.T_pos.le
      (S.high 1) (α • L.fullProfile) (S.high_pos 1)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα) he 6 (highShift 1) L.R 1 hct
  · exact Field.normalized_wordBound_congr (scalarGradientField τ hτ hτT B Y) D.T_pos.le
      (S.high 1) (α • L.fullProfile) (S.high_pos 1)
      (smul_profile_pos L.fullProfile L.fullProfile_pos α hα) he 6 (highShift 1) L.R 1 hp

end EulerTransversePacketPrimary.Budget

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerParameterWordGevrey EulerGevrey EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerCylinderSobolev

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}
  {L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6}
  (H : EulerTransversePacketPrimary.Budget L)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (hR : wordRadius (Fin 4) δ ≤ L.R)
  (W : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H N (wordCost (Fin 4) 6 δ *
      ‖ξ‖))

include hδ1 hR hα

theorem scaled_initialData_bound (n : ℕ) :
    block standardDirection 6 (fun a => translate period a
      ((initialData D δ hδ (α • ξ) hs).value : CylinderL2 period U)) n 0 ≤
      (α*(wordCost (Fin 4) 6 δ*‖ξ‖))*majorant L.R 0 n := by
  have hh := initialData_common_radius D δ hδ (α • ξ) hs standardDirection
    (fun i => by cases i using Fin.cases <;> simp [Prod.norm_def]) 6 hδ1 L.R hR n
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hα,mul_assoc,mul_left_comm,mul_comm] using hh

include W in
/-- The literal α χ₁ fδ ξT terminal datum supplies the required primary
profile budget, with every terminal jet estimate discharged. -/
theorem primary_profile_budget (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector
    period)
    (S : Scales (Icc (0 : ℝ) D.T)) (hgrowth : S.growth = α • L.fullProfile) :
    ProfileBudget (EulerTransversePacketPrimary.profileRegularity τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs) O hcorrector) S L.R 1 :=
  H.profile_budget N _ W (initialData D δ hδ (α • ξ) hs) α hα
    (scaled_initialData_bound (L := L) δ hδ hδ1 ξ hs α hα hR) O hcorrector S hgrowth

end EulerPacketTerminalDatum
