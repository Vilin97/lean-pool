/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.Bounds

namespace V7

open Stage3BelowTwoS3F

theorem belowTrial : BelowTrialStatement := by
  intro p hp hp2 d eps M D heps hM hD x0 cached
  let n := horizon p eps M D
  let trial := belowLocalTrial p eps x0 n
  refine ⟨trial, ?_⟩
  intro inst hcached hG hDG
  have hzero : cached.observation =
      phaseOneObs p eps M D x0 inst.oracle 0 := by
    simpa [phaseOneObs, phaseOneState, O3.PairOracle.observe] using hcached
  have hlargeZero : eps < lpNorm (conjugateExponent p)
      (phaseOneObs p eps M D x0 inst.oracle 0).gradient := by
    simpa [phaseOneObs, phaseOneState, O3.PairOracle.observe] using hG
  let report := Program.eval inst.oracle (phaseOneBudget n n)
    (phaseOneProgram p eps M D x0 n 0
      (phaseOneState p eps M D x0 inst.oracle 0)
      (phaseOneObs p eps M D x0 inst.oracle 0)
      (phaseOneChecks p eps M D x0 inst.oracle 0) n)
    (phaseOneNewTrace p eps M D x0 inst.oracle 0)
  have hshapeExists := eval_phaseOne_shape p eps M D x0 inst.oracle 0 n
    (by simp [n]) (by simp) hlargeZero
  change ∃ m₁ m₂, FullShape p eps M D x0 inst.oracle report m₁ m₂ at hshapeExists
  obtain ⟨m₁, m₂, hshape⟩ := hshapeExists
  let w := shapeWitness p eps M D x0 inst.oracle m₁ m₂
  refine ⟨report, w, ?_, fullShape_certificate hp hp2 heps hM hD inst
    hcached hshape, ?_, calls_first_bound hp heps hM hD hshape, ?_⟩
  · change (belowLocalTrial p eps x0 n).Executes M D cached inst.oracle report
    have hexec := programTrial_executes inst.oracle
      (fun M D cached =>
        ⟨phaseOneBudget n n, phaseOneProgram p eps M D x0 n 0 ⟨0, 0, 0⟩
          cached.observation [] n⟩) M D cached
    simpa [belowLocalTrial, n, report, hzero, phaseOneState, phaseOneChecks,
      phaseOneNewTrace] using hexec
  · exact fullShape_operational_contract hp heps hM hD hcached hshape
  · have hgradMD : lpNorm (conjugateExponent p) (inst.oracle.gradient x0) ≤
        M * D := by
      calc
        lpNorm (conjugateExponent p) (inst.oracle.gradient x0) =
            M * (lpNorm (conjugateExponent p) (inst.oracle.gradient x0) / M) := by
          field_simp [hM.ne']
        _ ≤ M * D := mul_le_mul_of_nonneg_left hDG hM.le
    have hkappa : 1 ≤ M * D / eps := by
      rw [le_div_iff₀ heps]
      simpa using le_trans (le_of_lt hG) hgradMD
    exact (calls_first_bound hp heps hM hD hshape).trans
      (first_to_second_bound hp heps hM hD hkappa)

end V7
