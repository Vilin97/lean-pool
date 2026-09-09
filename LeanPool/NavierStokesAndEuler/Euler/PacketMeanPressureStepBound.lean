/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketMeanGradeBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderMeanStep
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketForcingBounds

/-! The actual recursive mean pressure retains the same grade estimate
as the mean velocity. This estimate was already proved by the source
solver but is not a field of the velocity-oriented ProfileBudget. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.ProfileBudget

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

variable {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {R : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  {O : Operators} (C : CoefficientData P M.T O) (BC : CoefficientBudget C)
  (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R) (hcost : BC.termCost ≤ R)
  (S : Scales (Icc (0 : ℝ) M.T)) {support : Set Space}
  {p : ℕ} {a : ℕ → Profile} (hp : 2 ≤ p)
  (G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le support (a i))
  (hG : ∀ i (hi : i < p), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hc₀ : (a 0).corrector = 0) (hB₁ : (a 1).mean = 0)
  (hA : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) M.T) x θ,
    inner ℝ (O.normal (t, (x, θ))) ((a i).high (t, (x, θ))) = 0)

include WM BC hmean hRc hcost hp hG hc₀ hB₁ hA in
theorem meanPressure_step_exists :
    ∃ Q : Field P M.T (pressureGradient (step O p a).meanPressure),
      (Q.normalized M.T_pos.le (S.mean p) (S.mean_pos p)).WordBound 6 R 1 (meanShift p) := by
  let F := ProfileRegularity.prefixFields G
  let V := G (p-1) (by omega)
  have hV := hG (p-1) (by omega) (by omega)
  have BF : PrefixBound F M.T_pos.le S R := {
    high := fun i hi hi1 => (hG i hi hi1).high
    mean := fun i hi hi2 => (hG i hi (by omega)).mean
    corrector := fun i hi hi1 => (hG i hi hi1).corrector
  }
  have hB : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) M.T) x θ,
      (a i).mean (t,(x,θ))=(a i).mean (t,(x,0)) := fun i hi => (G i hi).mean_angle
  let MF := F.meanForce C (by omega) M.T_pos V.correctorDerivative V.corrector_time V.pressure
  have hMF : (MF.normalized M.T_pos.le (S.mean p) (S.mean_pos p)).WordBound
      6 R 1 (meanForceShift p) :=
    BF.meanForce_bound hp M.T_pos V.correctorDerivative V.corrector_time V.pressure BC
      hV.correctorDerivative hV.pressure LM.radius_bounds.1 hRc hcost hc₀ hB₁ hA hB
  let hm : Nonempty (EulerMeanPacketProvider.Forcing M (meanForce O p a)) :=
    ⟨F.meanForcing M C (by omega) V.correctorDerivative V.corrector_time V.pressure⟩
  let GM := Classical.choice hm
  have hsolve : O.meanSolve (meanForce O p a)=(GM.vector,GM.scalar) := by
    rw [hmean,EulerMeanPacketProvider.meanSolve_of_admissible M _ hm]
  have hscalar : (step O p a).meanPressure=GM.scalar := congrArg Prod.snd hsolve
  let Q : Field P M.T (pressureGradient (step O p a).meanPressure) :=
    (GM.pressureGradientCylinderField P).congr
      (fun t x θ => congrFun (congrArg pressureGradient hscalar) (t,(x,θ)))
  refine ⟨Q,?_⟩
  exact (LM.grade_bounds WM S GM MF p hp hMF).2.2.of_path_eq _ rfl

include WM BC hmean hRc hcost hp hG hc₀ hB₁ hA in
theorem meanPressure_step_bound (Q : Field P M.T (pressureGradient (step O p a).meanPressure)) :
    (Q.normalized M.T_pos.le (S.mean p) (S.mean_pos p)).WordBound 6 R 1 (meanShift p) := by
  obtain ⟨Q₀,hQ₀⟩ := meanPressure_step_exists M LM WM C BC hmean hRc hcost S hp G hG hc₀ hB₁ hA
  exact hQ₀.normalized_of_raw_eq Q M.T_pos.le (S.mean p) (S.mean_pos p) (fun _ _ _ => rfl)

end EulerPacketCylinderField.ProfileBudget
