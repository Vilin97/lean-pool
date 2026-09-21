/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.UpperAnalytic
import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoFinalTrial.Proof

/-!
The explicit above-two trial supplied to the known-parameter upper-bound argument.
-/

namespace V7.Stage5AboveTwoLowerS5F

open V7.Stage4AboveTwoFinalTrial

theorem explicit_aboveLocalTrial (p : ℝ) (hp : 2 < p)
    (eps M D : ℝ) (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (x0 : Point d) (cached : CachedPair d) (inst : PositiveInstance p d x0)
    (hcached : cached.observation = inst.oracle.observe x0)
    (hG : eps < lpNorm (conjugateExponent p) (inst.oracle.gradient x0))
    (hDG : D ≥ lpNorm (conjugateExponent p)
      (inst.oracle.gradient x0) / M) :
    let nf := nF p eps M D
    let nd := nD p eps M D
    ∃ (report : TrialReport d) (w : AboveTrialWitness p d),
      (aboveLocalTrial p eps x0 nf nd).Executes M D cached inst.oracle report ∧
      TrialCertificate eps p M D inst.L inst.R cached inst.oracle report ∧
      AboveTrialOperationalContract p eps M D x0 cached inst.oracle report w ∧
      (report.calls : ℝ) ≤
        trialConstant p * (M * D / eps) ^ (p / (p + 2)) := by
  let nf := nF p eps M D
  let nd := nD p eps M D
  have hzero : cached.observation =
      phaseOneObs p eps M D x0 inst.oracle 0 := by
    simpa [phaseOneObs, phaseOneState, O3.PairOracle.observe] using hcached
  have hlargeZero : eps < lpNorm (conjugateExponent p)
      (phaseOneObs p eps M D x0 inst.oracle 0).gradient := by
    simpa [phaseOneObs, phaseOneState, O3.PairOracle.observe] using hG
  let report := Stage3BelowTwoS3F.Program.eval inst.oracle (phaseOneBudget nd nf)
    (phaseOneProgram p eps M D (etaF p) (etaD p eps M D) x0 nf nd 0
      (phaseOneState p eps M D x0 inst.oracle 0)
      (phaseOneObs p eps M D x0 inst.oracle 0)
      (phaseOneChecks p eps M D x0 inst.oracle 0) nf)
    (phaseOneNewTrace p eps M D x0 inst.oracle 0)
  have hshapeExists := eval_phaseOne_shape p eps M D x0 inst.oracle 0 nf
    (by simp [nf]) (by simp) hlargeZero
  change ∃ m₁ m₂,
    FullShape p eps M D x0 inst.oracle report m₁ m₂ at hshapeExists
  obtain ⟨m₁, m₂, hshape⟩ := hshapeExists
  let w := shapeWitness p eps M D x0 inst.oracle m₁ m₂
  refine ⟨report, w, ?_,
    fullShape_certificate hp heps hM hD inst hcached hshape,
    fullShape_operational_contract hp heps hM hD hcached hshape, ?_⟩
  · change (aboveLocalTrial p eps x0 nf nd).Executes M D cached inst.oracle report
    have hexec := Stage3BelowTwoS3F.programTrial_executes inst.oracle
      (fun M D cached =>
        ⟨phaseOneBudget nd nf,
          phaseOneProgram p eps M D (etaF p) (etaD p eps M D) x0 nf nd 0
            ⟨0, 0, 0⟩ cached.observation [] nf⟩) M D cached
    simpa [aboveLocalTrial, nf, nd, report, hzero, phaseOneState,
      phaseOneChecks, phaseOneNewTrace] using hexec
  · have hgradMD : lpNorm (conjugateExponent p)
        (inst.oracle.gradient x0) ≤ M * D := by
      calc
        lpNorm (conjugateExponent p) (inst.oracle.gradient x0) =
            M * (lpNorm (conjugateExponent p) (inst.oracle.gradient x0) / M) := by
          field_simp [hM.ne']
        _ ≤ M * D := mul_le_mul_of_nonneg_left hDG hM.le
    have hkappa : 1 ≤ M * D / eps := by
      rw [le_div_iff₀ heps]
      simpa using le_trans (le_of_lt hG) hgradMD
    exact calls_current_bound hp heps hM hD hkappa hshape

end V7.Stage5AboveTwoLowerS5F
