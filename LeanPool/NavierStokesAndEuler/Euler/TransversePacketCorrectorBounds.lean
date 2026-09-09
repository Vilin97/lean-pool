/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrector
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlWeight
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialTimeWeight

@[expose] public section

/-! Same-radius estimates for the actual corrector, divided by the prescribed time profile. -/

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
  (g : C(Icc (0 : ℝ) D.T,ℝ)) (hg : ∀ t, 0 < g t)
  (q : ℕ) (Rc C R A : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
  (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R) (d : ℕ)
  (hbA : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.fullVelocityPath I))) n 0 ≤
      A*majorant R d n)
  (hbAt : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.fullDerivativePath I))) n 0 ≤
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
    nlinarith
  have h := EulerCylinderSlowCurl.normalized_derivative_block_bound P D.T g hg
    D.FInv.field D.inverseDerivative (G.potentialPath I) (G.potentialTimePath I)
    (G.potentialPath_orbit I) (G.potentialTimePath_orbit I) D.FInv.translation_contDiff
      D.inverseDerivative_orbit
    q Rc C R (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A)) hRc hC (by positivity) hR
    hbI hbIt d hQ (G.potentialTimePath_normalized_bound I g hg q Rc C R A hRc hC hA hR d hbA hbAt
      hbK hbKt) n
  exact h.trans_eq (by ring)

end EulerTransversePacketProvider.Forcing
