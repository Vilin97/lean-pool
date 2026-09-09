/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrector
public import LeanPool.NavierStokesAndEuler.Euler.CylinderLocalSupport

@[expose] public section

/-! Compact support of the actual transverse potential, corrector, and their time derivatives. -/

noncomputable section

namespace EulerTransversePacketProvider.Forcing

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerCylinderSmoothOrbit EulerCylinderLocalSupport
    EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

theorem potentialPath_supported (t : Icc (0 : ℝ) D.T) :
    G.potentialPath I t ∈ Supported P Space D.support D.support_measurable :=
  EulerCylinderLocalSupport.potentialPath_supported P D.support D.support_measurable
    (G.fullVelocityPath I) D.potentialCoefficientPath (fun s => (G.velocityPath I s).property) t

theorem potentialTimePath_supported (t : Icc (0 : ℝ) D.T) :
    G.potentialTimePath I t ∈ Supported P Space D.support D.support_measurable := by
  apply (Supported P Space D.support D.support_measurable).add_mem
  · exact EulerCylinderLocalSupport.potentialPath_supported P D.support D.support_measurable
      (G.fullVelocityPath I) D.potentialDerivative (fun s => (G.velocityPath I s).property) t
  · exact EulerCylinderLocalSupport.potentialPath_supported P D.support D.support_measurable
      (G.fullDerivativePath I) D.potentialCoefficientPath (fun s => (G.derivativePath I
        s).property) t

theorem correctorPath_supported (t : Icc (0 : ℝ) D.T) :
    G.correctorPath I t ∈ Supported P Space D.support D.support_measurable :=
  slowCurlPath_supported P D.support D.support_measurable (G.potentialPath I)
    (G.potentialPath_orbit I) D.FInv.field D.support_compact.isClosed (G.potentialPath_supported I)
      t

theorem correctorTimePath_supported (t : Icc (0 : ℝ) D.T) :
    G.correctorTimePath I t ∈ Supported P Space D.support D.support_measurable := by
  apply (Supported P Space D.support D.support_measurable).add_mem
  · exact slowCurlPath_supported P D.support D.support_measurable (G.potentialPath I)
      (G.potentialPath_orbit I) D.inverseDerivative D.support_compact.isClosed
      (G.potentialPath_supported I) t
  · exact slowCurlPath_supported P D.support D.support_measurable (G.potentialTimePath I)
      (G.potentialTimePath_orbit I) D.FInv.field D.support_compact.isClosed
      (G.potentialTimePath_supported I) t

theorem corrector_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    G.corrector I (t,(x,θ)) = 0 :=
  pointField_zero_outside P D.support D.support_measurable (G.correctorPath I)
    (G.correctorPath_orbit I)
    D.support_compact.isClosed (G.correctorPath_supported I) (D.clamp t) (x,(θ : AddCircle P)) hx

theorem correctorDerivative_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    G.correctorDerivative I (t,(x,θ)) = 0 :=
  pointField_zero_outside P D.support D.support_measurable (G.correctorTimePath I)
    (G.correctorTimePath_orbit I) D.support_compact.isClosed
    (G.correctorTimePath_supported I) (D.clamp t) (x,(θ : AddCircle P)) hx

theorem corrector_compact (t θ : ℝ) : HasCompactSupport (fun x => G.corrector I (t,(x,θ))) := by
  apply D.support_compact.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ D.support_compact.isClosed
  intro x hx
  by_contra hn
  exact hx (G.corrector_zero_outside I t x hn θ)

theorem correctorDerivative_compact (t θ : ℝ) :
    HasCompactSupport (fun x => G.correctorDerivative I (t,(x,θ))) := by
  apply D.support_compact.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ D.support_compact.isClosed
  intro x hx
  by_contra hn
  exact hx (G.correctorDerivative_zero_outside I t x hn θ)

end EulerTransversePacketProvider.Forcing
