/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoFinalTrial.Bounds

namespace V7

open Stage4AboveTwoFinalTrial

theorem aboveTrial : AboveTrialStatement := by
  intro p hp
  refine ⟨trialConstant p, trialConstant_pos p hp, ?_⟩
  intro d eps M D heps hM hD x0 cached
  let nf := nF p eps M D
  let nd := nD p eps M D
  let trial := aboveLocalTrial p eps x0 nf nd
  refine ⟨trial, ?_⟩
  intro inst hcached hG hDG
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

end V7
