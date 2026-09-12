/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedGradeBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketLinearCostAbsorption
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketNormalBudget
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardBudget
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistory
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPressureGradient
import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialWeight
import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift
public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalResidualBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradientWeight
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderPressureWeight
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrector
import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlWeight
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHomogeneity
import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathWeight
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevScaling
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryHomogeneity

/-! Fixed source costs close the direct-forward packet grade bounds.  The
profile's positive scalar factor cancels exactly; one spare shift pays the
fixed operator costs, with no change of external radius. -/

section

/-! The genuine direct-forward solution has amplitude-linear estimates at
one source-dependent radius, for arbitrary admissible initial data and forcing. -/

section

/-! Homogeneity restores a common arbitrary envelope for genuine forcing
and initial data, without adding either envelope to the radius guards. -/

@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerPacketProfileRecursion EulerContinuousTimeWeight
  EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} {ι : Type*} [Fintype ι]

theorem pair_amplitude_bound
    (S : ∀ {r : VectorField}, Forcing P D r → InitialData P D → C(Icc (0 : ℝ) D.T, LiftL2 P))
    (hs : ∀ {r} (G : Forcing P D r) (I : InitialData P D),
      ContDiff ℝ ∞ (fun a => pathTranslate P a (S G I)))
    (hm : ∀ {r r'} (G : Forcing P D r) (H : Forcing P D r') (I J : InitialData P D) (a : ℝ),
      H.path = a • G.path → J.value = a • I.value → S H J = a • S G I)
    (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t)
    (directions : ι → LiftTangent) (q : ℕ) (R C : ℝ) (d e : ℕ)
    (hunit : ∀ {r} (G : Forcing P D r) (I : InitialData P D),
      (∀ n, block directions q (fun a => pathTranslate P a
        (normalize g hg (HistoryData.forcingPath G))) n 0 ≤ majorant R d n) →
      (∀ n, block directions q (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ majorant R
          d n) →
      ∀ n, block directions q (fun a => pathTranslate P a (normalize g hg (S G I))) n 0 ≤
          C * majorant R e n)
    {r : VectorField} (G : Forcing P D r) (I : InitialData P D) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ n, block directions q (fun a => pathTranslate P a
      (normalize g hg (HistoryData.forcingPath G))) n 0 ≤ A * majorant R d n)
    (hi : ∀ n, block directions q (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤
        A * majorant R d n)
    (n : ℕ) :
    block directions q (fun a => pathTranslate P a (normalize g hg (S G I))) n 0 ≤
      (C*A)*majorant R e n := by
  by_cases hz : A = 0
  · have hf := value_zero_of_block_zero_bound directions q
      (fun a => pathTranslate P a (normalize g hg (HistoryData.forcingPath G))) 0
      (by simpa only [hz,zero_mul] using hb 0)
    have ht : pathTranslate P 0 (normalize g hg (HistoryData.forcingPath G)) =
        normalize g hg (HistoryData.forcingPath G) := by
      apply ContinuousMap.ext
      intro t
      exact translate_zero P _
    rw [ht] at hf
    have hfull : HistoryData.forcingPath G = 0 := by
      have he := congrArg (weight g) hf
      rw [weight_normalize,map_zero] at he
      exact he
    have hp : G.path = 0 := by
      have he := congrArg (projectPath P D.support D.support_measurable) hfull
      rw [project_include,map_zero] at he
      exact he
    have hinitial := value_zero_of_block_zero_bound directions q
      (fun a => translate P a (I.value : CylinderL2 P U)) 0
      (by simpa only [hz,zero_mul] using hi 0)
    rw [translate_zero] at hinitial
    have hv : I.value = 0 := Subtype.ext hinitial
    have hS : S G I = 0 := by
      have he := hm G G I I 0 (hp.trans (zero_smul ℝ G.path).symm)
        (hv.trans (zero_smul ℝ I.value).symm)
      simpa only [zero_smul] using he
    simp only [hS,map_zero,block_zero_function,hz,mul_zero,zero_mul,le_refl]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
    let H := G.smul A⁻¹
    let J := I.smul A⁻¹
    have hinput : HistoryData.forcingPath H = A⁻¹ • HistoryData.forcingPath G := by
      change includePath P D.support D.support_measurable (A⁻¹ • G.path) = _
      rw [map_smul]
    have hH (j : ℕ) : block directions q (fun a => pathTranslate P a
        (normalize g hg (HistoryData.forcingPath H))) j 0 ≤ majorant R d j := by
      have he : (fun a => pathTranslate P a (normalize g hg (HistoryData.forcingPath H))) =
          fun a => A⁻¹ • pathTranslate P a (normalize g hg (HistoryData.forcingPath G)) := by
        funext a
        rw [hinput,map_smul,map_smul]
      rw [he]
      simpa only [one_mul] using block_normalize_bound directions q
        (fun a => pathTranslate P a (normalize g hg (HistoryData.forcingPath G)))
        (normalize_orbit_contDiff P g hg _ G.path_orbit) A hApos R 1 d j 0
        (by simpa only [one_mul] using hb j)
    have hJ (j : ℕ) : block directions q
        (fun a => translate P a (J.value : CylinderL2 P U)) j 0 ≤ majorant R d j := by
      have he : (fun a => translate P a (J.value : CylinderL2 P U)) =
          fun a => A⁻¹ • translate P a (I.value : CylinderL2 P U) := by
        funext a
        change translate P a (A⁻¹ • (I.value : CylinderL2 P U)) = _
        rw [map_smul]
      rw [he]
      simpa only [one_mul] using block_normalize_bound directions q
        (fun a => translate P a (I.value : CylinderL2 P U)) I.orbit A hApos R 1 d j 0
        (by simpa only [one_mul] using hi j)
    have hrestore : S G I = A • S H J := by
      rw [hm G H I J A⁻¹ rfl rfl,smul_smul,mul_inv_cancel₀ hz,one_smul]
    exact (block_restore_bound directions q
      (fun a => pathTranslate P a (normalize g hg (S H J)))
      (fun a => pathTranslate P a (normalize g hg (S G I)))
      (normalize_orbit_contDiff P g hg (S H J) (hs H J)) A hA
      (fun a => by rw [hrestore,map_smul,map_smul]) R C e n 0
      (hunit H J hH hJ n)).trans_eq (by ring)

end EulerTransversePacketProvider

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketForward.Budget

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerTransversePacketProvider EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {ι : Type*} [Fintype ι] {q : ℕ} (L : Budget D ι q)
  {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1)
  (A : ℝ) (hA : 0 ≤ A) (d : ℕ)
  (hforce : ∀ n, block directions q (fun a => pathTranslate P a
    (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ A * majorant L.R d n)
  (hinitial : ∀ n, block directions q (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤
    A * majorant L.R d n)

include hdir hA hforce hinitial

theorem velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.fullVelocityPath I))) n 0 ≤
        (L.velocityCost*A)*majorant L.R (d+1) n :=
  pair_amplitude_bound (fun {r} H Y => (H : Forcing P D r).fullVelocityPath Y)
    (fun H Y => H.velocityPath_orbit Y)
    (fun H J Y Z a he hi => by
      change includePath P D.support D.support_measurable (J.velocityPath Z) =
        a • includePath P D.support D.support_measurable (H.velocityPath Y)
      rw [H.velocityPath_eq_smul J Y Z a he hi,map_smul])
    L.g L.positive directions q L.R L.velocityCost d (d+1)
    (fun H Y hf hi => L.velocity_unit_bound H Y directions hdir d hf hi)
    G I A hA hforce hinitial n

theorem derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.fullDerivativePath I))) n 0 ≤
        (L.derivativeCost*A)*majorant L.R (d+1) n :=
  pair_amplitude_bound (fun {r} H Y => (H : Forcing P D r).fullDerivativePath Y)
    (fun H Y => H.derivativePath_orbit Y)
    (fun H J Y Z a he hi => by
      change includePath P D.support D.support_measurable (J.derivativePath Z) =
        a • includePath P D.support D.support_measurable (H.derivativePath Y)
      rw [H.derivativePath_eq_smul J Y Z a he hi,map_smul])
    L.g L.positive directions q L.R L.derivativeCost d (d+1)
    (fun H Y hf hi => L.derivative_unit_bound H Y directions hdir d hf hi)
    G I A hA hforce hinitial n

theorem velocity_common_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.fullVelocityPath I))) n 0 ≤
        (L.commonCost*A)*majorant L.R (d+1) n :=
  (L.velocity_bound G I directions hdir A hA d hforce hinitial n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right L.velocityCost_le_common hA)
      (majorant_nonneg L.R (zero_le_one.trans L.radius_one) (d+1) n))

theorem derivative_common_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.fullDerivativePath I))) n 0 ≤
        (L.commonCost*A)*majorant L.R (d+1) n :=
  (L.derivative_bound G I directions hdir A hA d hforce hinitial n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right L.derivativeCost_le_common hA)
      (majorant_nonneg L.R (zero_le_one.trans L.radius_one) (d+1) n))

end EulerTransversePacketForward.Budget

end
end

end

section

/-!
All eight genuine direct-forward outputs obey one fixed mixed-word Sobolev
budget.  The input radius is retained, both data amplitudes remain outside
the solve, and at most two derivative shifts are spent.  All normalization
uses the literal positive time profile without differentiating that profile.
-/

section

/-! Same-radius estimates for the actual corrector, divided by the prescribed time profile. -/

@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider.Forcing

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients EulerGevrey
  EulerPacketProfileRecursion EulerCylinderSobolev EulerParameterWordGevrey
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerContinuousTimeWeight
open scoped ContDiff

private theorem direction_norm_bound (i : Fin 4) : ‖standardDirection i‖ ≤ 1 := by
  cases i using Fin.cases <;> simp [Prod.norm_def]

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)
  (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t)
  (q : ℕ) (Rc C R A : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
  (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R) (d : ℕ)
  (hbA : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.fullVelocityPath I))) n 0 ≤
      A * majorant R d n)
  (hbAt : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.fullDerivativePath I))) n 0 ≤
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
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.potentialPath I))) n 0 ≤
      (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d n :=
  EulerCylinderPotential.normalized_potentialPath_block_bound P g (G.fullVelocityPath I)
    D.potentialCoefficientPath hg D.potentialCoefficientPath_orbit
    (EulerCylinderPotential.weighted_orbit P (reciprocal g hg) (G.fullVelocityPath I)
        (G.velocityPath_orbit I))
    standardDirection direction_norm_bound q Rc C R A hRc hC hA hR hbK d hbA n

include hRc hC hA hR hbA hbAt hbK hbKt in
theorem potentialTimePath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.potentialTimePath I))) n 0 ≤
      (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d n :=
  EulerCylinderPotential.normalized_potentialDerivative_block_bound P D.T
    D.potentialCoefficientPath D.potentialDerivative D.potentialCoefficientPath_orbit
        D.potentialDerivative_orbit
    (G.fullVelocityPath I) (G.fullDerivativePath I) (G.velocityPath_orbit I)
        (G.derivativePath_orbit I)
    g hg standardDirection direction_norm_bound q Rc C R A hRc hC hA hR hbK hbKt d hbA hbAt n

include hRc hC hA hR hbA hbK hbI in
theorem correctorPath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.correctorPath I))) n 0 ≤
      (27*(sobolevCoefficientAmplitude (Fin 4) q Rc C)^2*(P*A))*majorant R (d+1) n := by
  have hp : 0 ≤ P := (Fact.out : 0 < P).le
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q Rc C hRc hC
  have h := EulerCylinderSlowCurl.normalized_path_block_bound P g D.FInv.field
    (G.potentialPath I) (G.potentialPath_orbit I) hg D.FInv.translation_contDiff
    q Rc C R (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A)) hRc hC (by positivity) hR hbI d
    (G.potentialPath_normalized_bound I g hg q Rc C R A hRc hC hA hR d hbA hbK) n
  exact h.trans_eq (by ring)

include hRc hC hA hR hbA hbAt hbK hbKt hbI hbIt in
theorem correctorTimePath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.correctorTimePath I))) n 0 ≤
      (108*(sobolevCoefficientAmplitude (Fin 4) q Rc C)^2*(P*A))*majorant R (d+1) n := by
  have hp : 0 ≤ P := (Fact.out : 0 < P).le
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q Rc C hRc hC
  have hRn : 0 ≤ R := (sobolevCoefficientRadius_nonneg (ι := Fin 4) Rc hRc).trans hR
  have hQ (j : ℕ) : block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.potentialPath I))) j 0 ≤
        (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d j := by
    apply (G.potentialPath_normalized_bound I g hg q Rc C R A hRc hC hA hR d hbA hbK j).trans
    have hn := mul_nonneg
      (show 0 ≤ sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A) by positivity)
      (majorant_nonneg R hRn d j)
    linarith
  have h := EulerCylinderSlowCurl.normalized_derivative_block_bound P D.T g hg
    D.FInv.field D.inverseDerivative (G.potentialPath I) (G.potentialTimePath I)
    (G.potentialPath_orbit I) (G.potentialTimePath_orbit I) D.FInv.translation_contDiff
        D.inverseDerivative_orbit
    q Rc C R (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A)) hRc hC (by positivity) hR
    hbI hbIt d hQ (G.potentialTimePath_normalized_bound I g hg q Rc C R A hRc hC hA hR d hbA hbAt
        hbK hbKt) n
  exact h.trans_eq (by ring)

end EulerTransversePacketProvider.Forcing

end
end

end

section

/-! Bounds for the actual high-pressure gradient from the normalized forcing and solved velocity. -/

@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider.Forcing

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerPacketProfileRecursion
  EulerPacketCylinderField EulerLpCylinderPaths EulerLpCylinderTranslation
  EulerCylinderSobolev EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight
  EulerSourceNormalResidualBounds EulerCylinderPotential EulerTimeLpGramGevrey

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

theorem pressurePath_normalized_eq_source (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t) :
    normalize g hg (G.pressurePath I) =
      sourcePressure P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
        (normalize g hg (includePath P D.support D.support_measurable G.path))
        (normalize g hg (includePath P D.support D.support_measurable (G.velocityPath I))) :=
  (sourcePressure_weight P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    (reciprocal g hg) (includePath P D.support D.support_measurable G.path)
    (includePath P D.support D.support_measurable (G.velocityPath I))).symm

theorem scalarGradientField_normalized_bound (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t)
    (q : ℕ) (R A : ℝ) (d : ℕ)
    (hb : ∀ n, block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.pressurePath I))) n 0 ≤
        A*majorant R d n) (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.scalarGradientField I).path)) n
          0 ≤
        (3*A)*majorant R (d+1) n :=
  scalarGradientPath_normalized_majorant (G.pressurePath I) (G.pressurePath_orbit I) g hg q R A d
      hb n

theorem source_pressure_gradient_bound (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t)
    (q : ℕ) (Rc Cm CM Ri R Af Av : ℝ)
    (hRc : 0 ≤ Rc) (hCm : 0 ≤ Cm) (hCM : 0 ≤ CM) (hAf : 0 ≤ Af) (hAv : 0 ≤ Av)
    (hRi : 2 * gramCost D.normalLower Cm 1 * (Rc + 1) ≤ Ri)
    (hR : sobolevCoefficientRadius (Fin 4) (4 * Ri) ≤ R)
    (hm : ∀ n t x, ‖iteratedFDeriv ℝ n (D.normal.field t : Space → Space) x‖ ≤ Cm * majorant Rc 0 n)
    (hM : ∀ n t x, ‖iteratedFDeriv ℝ n (D.M.field t : Space → Space →L[ℝ] Space) x‖ ≤ CM * majorant
        Rc 0 n)
    (d : ℕ)
    (hf : ∀ n, block standardDirection q
      (fun a : LiftTangent => pathTranslate P a
        (normalize g hg (includePath P D.support D.support_measurable G.path))) n 0 ≤ Af*majorant R
            d n)
    (hv : ∀ n, block standardDirection q
      (fun a : LiftTangent => pathTranslate P a
        (normalize g hg (includePath P D.support D.support_measurable (G.velocityPath I)))) n 0 ≤
          Av*majorant R d n) (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.scalarGradientField I).path)) n
          0 ≤
        (3*(P*pressureCost (Fin 4) q Ri Cm CM Af Av))*majorant R (d+1) n := by
  apply G.scalarGradientField_normalized_bound I g hg q R _ d _ n
  intro j
  rw [G.pressurePath_normalized_eq_source I g hg]
  exact sourcePressure_block_bound P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    _ _ standardDirection (fun i => by cases i using Fin.cases <;> simp [Prod.norm_def]) q
    (weighted_orbit P (reciprocal g hg) _ G.path_orbit)
    (weighted_orbit P (reciprocal g hg) _ (G.velocityPath_orbit I))
    Rc Cm CM Ri R Af Av hRc hCm hCM hAf hAv hRi hR hm hM d hf hv j

end EulerTransversePacketProvider.Forcing

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketForward.Budget

open Set EulerSmoothLimit EulerTransversePacketProvider EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight EulerCylinderSobolev
  EulerSourceNormalResidualBounds
open scoped ContDiff

private theorem standard_norm (i : Fin 4) : ‖standardDirection i‖ ≤ 1 := by
  cases i using Fin.cases <;> simp [Prod.norm_def]

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {q : ℕ} (L : Budget D (Fin 4) q)
  (N : EulerTransversePacketJoin.NormalBudget D q L.R)

/-- Pressure amplitude, given by `P*pressureCost (Fin 4) q N.Ri N.C N.C 1 L.commonCost`. -/
def pressureAmplitude : ℝ := P*pressureCost (Fin 4) q N.Ri N.C N.C 1 L.commonCost
/-- Potential amplitude, given by `3*N.blockAmplitude*(P*L.commonCost)`. -/
def potentialAmplitude : ℝ := 3*N.blockAmplitude*(P*L.commonCost)
/-- Potential time amplitude, given by `6*N.blockAmplitude*(P*L.commonCost)`. -/
def potentialTimeAmplitude : ℝ := 6*N.blockAmplitude*(P*L.commonCost)
/-- Corrector amplitude, given by `27*N.blockAmplitude^2*(P*L.commonCost)`. -/
def correctorAmplitude : ℝ := 27*N.blockAmplitude^2*(P*L.commonCost)
/-- Corrector time amplitude, given by `108*N.blockAmplitude^2*(P*L.commonCost)`. -/
def correctorTimeAmplitude : ℝ := 108*N.blockAmplitude^2*(P*L.commonCost)

variable {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)
  (A : ℝ) (hA : 0 ≤ A) (d : ℕ)
  (hforce : ∀ n, block standardDirection q (fun a => pathTranslate P a
    (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ A * majorant L.R d n)
  (hinitial : ∀ n, block standardDirection q
    (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ A * majorant L.R d n)

include hA hforce hinitial

theorem pressure_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.pressurePath I))) n 0 ≤
        (L.pressureAmplitude (P := P) N*A)*majorant L.R (d+1) n := by
  have hf (j : ℕ) : block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath G))) j 0 ≤ A*majorant L.R (d+1) j :=
    (hforce j).trans (mul_le_mul_of_nonneg_left
      (majorant_mono_shift L.R L.radius_one d (d+1) j (by omega)) hA)
  rw [G.pressurePath_normalized_eq_source I L.g L.positive]
  have h := sourcePressure_block_bound P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    _ _ standardDirection standard_norm q
    (EulerCylinderPotential.weighted_orbit P (reciprocal L.g L.positive) _ G.path_orbit)
    (EulerCylinderPotential.weighted_orbit P (reciprocal L.g L.positive) _ (G.velocityPath_orbit I))
    N.Rc N.C N.C N.Ri L.R A (L.commonCost*A) N.Rc_nonneg N.C_nonneg N.C_nonneg hA
    (mul_nonneg L.commonCost_nonneg hA) N.inverse_radius N.pressure_radius
    N.normal_bound N.strain_bound (d+1) hf
    (L.velocity_common_bound G I standardDirection standard_norm A hA d hforce hinitial) n
  exact h.trans_eq (by unfold pressureAmplitude pressureCost; ring)

theorem pressure_gradient_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.scalarGradientField I).path)) n 0 ≤
        (3*L.pressureAmplitude (P := P) N*A)*majorant L.R (d+2) n := by
  have h := G.scalarGradientField_normalized_bound I L.g L.positive q L.R
    (L.pressureAmplitude (P := P) N*A) (d+1) (L.pressure_bound N G I A hA d hforce hinitial) n
  simpa only [show d+1+1=d+2 by omega,mul_assoc] using h

theorem potential_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.potentialPath I))) n 0 ≤
        (L.potentialAmplitude (P := P) N*A)*majorant L.R (d+1) n := by
  have hc := N.coefficient_bounds
  have h := G.potentialPath_normalized_bound I L.g L.positive
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+1)
    (L.velocity_common_bound G I standardDirection standard_norm A hA d hforce hinitial)
    (fun j a => (hc.2.2 j a).2.2.1) n
  exact h.trans_eq (by
      unfold potentialAmplitude EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

theorem potential_time_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.potentialTimePath I))) n 0 ≤
        (L.potentialTimeAmplitude (P := P) N*A)*majorant L.R (d+1) n := by
  have hc := N.coefficient_bounds
  have h := G.potentialTimePath_normalized_bound I L.g L.positive
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+1)
    (L.velocity_common_bound G I standardDirection standard_norm A hA d hforce hinitial)
    (L.derivative_common_bound G I standardDirection standard_norm A hA d hforce hinitial)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).2.2.2) n
  exact h.trans_eq (by
      unfold potentialTimeAmplitude EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

theorem corrector_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.correctorPath I))) n 0 ≤
        (L.correctorAmplitude (P := P) N*A)*majorant L.R (d+2) n := by
  have hc := N.coefficient_bounds
  have h := G.correctorPath_normalized_bound I L.g L.positive
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+1)
    (L.velocity_common_bound G I standardDirection standard_norm A hA d hforce hinitial)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).1) n
  rw [show d+1+1=d+2 by omega] at h
  exact h.trans_eq (by
      unfold correctorAmplitude EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

theorem corrector_time_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.correctorTimePath I))) n 0 ≤
        (L.correctorTimeAmplitude (P := P) N*A)*majorant L.R (d+2) n := by
  have hc := N.coefficient_bounds
  have h := G.correctorTimePath_normalized_bound I L.g L.positive
    q N.coefficientRadius N.coefficientAmplitude L.R (L.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg L.commonCost_nonneg hA) N.radius (d+1)
    (L.velocity_common_bound G I standardDirection standard_norm A hA d hforce hinitial)
    (L.derivative_common_bound G I standardDirection standard_norm A hA d hforce hinitial)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).2.2.2)
    (fun j a => (hc.2.2 j a).1) (fun j a => (hc.2.2 j a).2.1) n
  rw [show d+1+1=d+2 by omega] at h
  exact h.trans_eq (by
      unfold correctorTimeAmplitude EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

end EulerTransversePacketForward.Budget

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketForward.Budget

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketCylinderField
  EulerPacketProfileRecursion EulerContinuousTimeWeight EulerParameterWordGevrey
  EulerGevrey EulerSourceNormalResidualBounds EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderSobolev

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (L : Budget D (Fin 4) 6)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)

theorem pressureAmplitude_nonneg : 0 ≤ L.pressureAmplitude (P := P) N := by
  have hi := N.Ri_nonneg
  have hc := N.C_nonneg
  have hl := L.commonCost_nonneg
  have hp := (Fact.out : 0 < P).le
  have hm := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) 6 (4*N.Ri) (3*N.Ri*N.C)
    (by positivity) (by positivity)
  have hM := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) 6 (4*N.Ri) N.C
    (by positivity) hc
  unfold pressureAmplitude pressureCost
  positivity

theorem correctorAmplitude_nonneg : 0 ≤ L.correctorAmplitude (P := P) N := by
  have hl := L.commonCost_nonneg
  have hp := (Fact.out : 0 < P).le
  unfold correctorAmplitude
  positivity

theorem correctorTimeAmplitude_nonneg : 0 ≤ L.correctorTimeAmplitude (P := P) N := by
  have hl := L.commonCost_nonneg
  have hp := (Fact.out : 0 < P).le
  unfold correctorTimeAmplitude
  positivity

/-- The unscaled data cost is fixed before the positive amplitude and grade.
It is one for forced profiles and the literal compact-wave cost for the primary. -/
structure GradeGuards (C : ℝ) : Prop where
  data_nonneg : 0 ≤ C
  common : L.commonCost*C ≤ L.R
  corrector : L.correctorAmplitude (P := P) N*C ≤ L.R
  correctorTime : L.correctorTimeAmplitude (P := P) N*C ≤ L.R
  pressureGradient : 3*L.pressureAmplitude (P := P) N*C ≤ L.R

variable (C : ℝ) (W : GradeGuards (P := P) L N C)
  {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)
  (c : ℝ) (hc : 0 < c) (d e : ℕ) (hroom : d + 3 ≤ e)
  (hforce : ∀ n, block standardDirection 6 (fun a => pathTranslate P a
    (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ (c * C) * majorant L.R d n)
  (hinitial : ∀ n, block standardDirection 6
    (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ (c * C) * majorant L.R d n)

include W hc hroom hforce hinitial

theorem grade_fields :
    ((G.vectorField I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e ∧
    ((G.vectorDerivativeField I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e ∧
    ((G.curlCorrectorField I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e ∧
    ((G.correctorDerivativeField I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e ∧
    ((G.scalarGradientField I).normalized D.T_pos.le (c • L.g)
      (smul_profile_pos L.g L.positive c hc)).WordBound 6 L.R 1 e := by
  have ha := mul_nonneg hc.le W.data_nonneg
  have hd : ∀ i : Fin 4, ‖standardDirection i‖ ≤ 1 := by
    intro i
    cases i using Fin.cases <;> simp [Prod.norm_def]
  have hv : ((G.vectorField I).normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R ((L.commonCost*C)*c) (d+1) := by
    intro n
    simpa only [Field.normalized_path,Forcing.vectorField,mul_assoc,mul_left_comm,mul_comm] using
      L.velocity_common_bound G I standardDirection hd (c*C) ha d hforce hinitial n
  have ht : ((G.vectorDerivativeField I).normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R ((L.commonCost*C)*c) (d+1) := by
    intro n
    simpa only [Field.normalized_path, Forcing.vectorDerivativeField, mul_assoc, mul_left_comm,
        mul_comm] using
      L.derivative_common_bound G I standardDirection hd (c*C) ha d hforce hinitial n
  have hC : ((G.curlCorrectorField I).normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R ((L.correctorAmplitude (P := P) N*C)*c) (d+2) := by
    intro n
    simpa only [Field.normalized_path,Forcing.curlCorrectorField,mul_assoc,mul_left_comm,mul_comm]
        using
      L.corrector_bound N G I (c*C) ha d hforce hinitial n
  have hCt : ((G.correctorDerivativeField I).normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R ((L.correctorTimeAmplitude (P := P) N*C)*c) (d+2) := by
    intro n
    simpa only [Field.normalized_path, Forcing.correctorDerivativeField, mul_assoc, mul_left_comm,
        mul_comm] using
      L.corrector_time_bound N G I (c*C) ha d hforce hinitial n
  have hπ : ((G.scalarGradientField I).normalized D.T_pos.le L.g L.positive).WordBound
      6 L.R ((3*L.pressureAmplitude (P := P) N*C)*c) (d+2) := by
    intro n
    simpa only [Field.normalized_path,mul_assoc,mul_left_comm,mul_comm] using
      L.pressure_gradient_bound N G I (c*C) ha d hforce hinitial n
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (hv.scale_profile D.T_pos.le L.g L.positive c hc).absorb_amplitude_to
      L.radius_one (mul_nonneg L.commonCost_nonneg W.data_nonneg) W.common (by omega)
  · exact (ht.scale_profile D.T_pos.le L.g L.positive c hc).absorb_amplitude_to
      L.radius_one (mul_nonneg L.commonCost_nonneg W.data_nonneg) W.common (by omega)
  · exact (hC.scale_profile D.T_pos.le L.g L.positive c hc).absorb_amplitude_to
      L.radius_one (mul_nonneg (L.correctorAmplitude_nonneg N) W.data_nonneg) W.corrector (by omega)
  · exact (hCt.scale_profile D.T_pos.le L.g L.positive c hc).absorb_amplitude_to
      L.radius_one (mul_nonneg (L.correctorTimeAmplitude_nonneg N) W.data_nonneg) W.correctorTime
          (by
          omega)
  · exact (hπ.scale_profile D.T_pos.le L.g L.positive c hc).absorb_amplitude_to
      L.radius_one (mul_nonneg (mul_nonneg (by
          norm_num) (L.pressureAmplitude_nonneg N)) W.data_nonneg)
      W.pressureGradient (by omega)

end EulerTransversePacketForward.Budget
