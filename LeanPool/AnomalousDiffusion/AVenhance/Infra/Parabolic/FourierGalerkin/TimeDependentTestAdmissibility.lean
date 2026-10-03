/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentTestConvergence

/-!
# Admissibility of spacetime Fourier cutoffs

For a test, each spatial Fourier cutoff remains a smooth spacetime test with the same
periodicity and terminal support.
-/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Parabolic.FourierGalerkin

theorem TimeDependentTestAdmissibility.spatialFourierCutoff_zero (N : ℕ) :
    AVenhance.Infra.Section5.testFourierCutoff (fun _ : Vec 2 => 0) N =
      fun _ => 0 := by
  funext x
  simp [AVenhance.Infra.Section5.testFourierCutoff,
    AVenhance.Infra.Ergodic.lowProjection,
    AVenhance.Infra.Ergodic.euclideanFourierCutoff,
    AVenhance.Infra.Ergodic.complexEuclideanCutoff,
    AVenhance.Infra.Torus.smoothFourierCoeff]

end AVenhance.Infra.Parabolic.FourierGalerkin

end
