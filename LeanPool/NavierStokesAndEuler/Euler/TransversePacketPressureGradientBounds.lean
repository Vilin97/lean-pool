/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPressureGradient
public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalResidualBounds
import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialWeight
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradientWeight
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderPressureWeight

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
