/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryCorrector
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketNormalBudget
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderPressureWeight
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradientWeight
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlWeight
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialTimeWeight

@[expose] public section

/-! Same-radius estimates for the actual corrector, divided by the prescribed time profile. -/

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
  (g : C(Icc (0 : ℝ) D.T,ℝ)) (hg : ∀ t, 0 < g t)
  (q : ℕ) (Rc C R A : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
  (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R) (d : ℕ)
  (hbA : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (velocityPath τ hτ hτT B Y))) n 0 ≤
      A*majorant R d n)
  (hbAt : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (derivativePath τ hτ hτT B Y))) n 0 ≤
      A*majorant R d n)
  (hbK : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialCoefficientPath) a‖ ≤
    C*majorant Rc 0 n)
  (hbKt : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialDerivative) a‖ ≤
    C*majorant Rc 0 n)
  (hbI : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤ C*majorant Rc 0 n)
  (hbIt : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.inverseDerivative) a‖ ≤
    C*majorant Rc 0 n)

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
  have hb0 := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*L.Ri) L.C₀ (by positivity)
    L.C₀_nonneg
  have hb1 := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*L.Ri) L.C₁ (by positivity)
    L.C₁_nonneg
  have hc0 := L.C₀_nonneg
  have hc1 := L.C₁_nonneg
  have hbb := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*L.Ri) (18*L.Ri*L.C₀*L.C₁)
    (by positivity) (by positivity)
  have hbf := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*L.Ri) (3*L.Ri*L.C₀)
    (by positivity) (by positivity)
  have ht := H.endpointBudget.coordinateCost_nonneg
  unfold derivativeCost EndpointBudget.derivativeCost physicalCost coordinateCost
  change 0 ≤ 3*sobolevCoefficientAmplitude (Fin 4) q L.Rc L.C₁*H.endpointBudget.coordinateCost+
    3*sobolevCoefficientAmplitude (Fin 4) q L.Rc L.C₀+
      (3*sobolevCoefficientAmplitude (Fin 4) q (4*L.Ri) L.C₁*1+
        3*sobolevCoefficientAmplitude (Fin 4) q (4*L.Ri) L.C₀*
          (3*sobolevCoefficientAmplitude (Fin 4) q (4*L.Ri) (18*L.Ri*L.C₀*L.C₁)*1+
            3*sobolevCoefficientAmplitude (Fin 4) q (4*L.Ri) (3*L.Ri*L.C₀)*0))
  positivity

def commonCost : ℝ := H.velocityCost+H.derivativeCost
def pressureAmplitude : ℝ := P*pressureCost (Fin 4) q N.Ri N.C N.C 0 H.commonCost
def potentialAmplitude : ℝ := 3*N.blockAmplitude*(P*H.commonCost)
def potentialTimeAmplitude : ℝ := 6*N.blockAmplitude*(P*H.commonCost)
def correctorAmplitude : ℝ := 27*N.blockAmplitude^2*(P*H.commonCost)
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
    A*majorant L.R d n)

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
    simpa only [EulerTransversePacketPrimary.pressurePath,EulerContinuousTimeWeight.normalize,map_zero] using
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
  exact h.trans_eq (by unfold potentialAmplitude
    EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

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
  exact h.trans_eq (by unfold potentialTimeAmplitude
    EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

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
  exact h.trans_eq (by unfold correctorAmplitude
    EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

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
  exact h.trans_eq (by unfold correctorTimeAmplitude
    EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

end EulerTransversePacketPrimary.Budget
