/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerInput
public import LeanPool.NavierStokesAndEuler.Euler.StaticEulerForceField
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerSobolev

/-! The concrete local base evolution has actual continuous L² jets for
both velocity and pressure force. Consequently its Euler equation holds
strongly in every finite Sobolev order, including endpoint derivatives. -/

@[expose] public section


noncomputable section

namespace EulerStaticEuler

open Set EulerSmoothLimit EulerLpTranslation EulerParentPacketFrames

variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R)
  (hdiv : ∀ x, divergence u.field x = 0) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)

/-- Base sobolev data, bundling `velocity`, `force`, `velocity_match`, `force_match` and the
required compatibility proofs. -/
def baseSobolevData : SobolevData (baseEvolution P u C R hC hR hu hdiv ell hell hell1) where
  velocity t := localField P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
  force t := localForceField P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
  velocity_match t x := (localField_apply P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
      x).symm
  force_match t x := (localForceField_apply P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
      x).symm
  velocity_continuous n := (localField_jetLp_continuous P u C R hC hR hu hdiv n).comp
    (baseInclusion P C R hC hR).continuous
  force_continuous n := (localForceField_jetLp_continuous P u C R hC hR hu hdiv n).comp
    (baseInclusion P C R hC hR).continuous

end EulerStaticEuler

namespace EulerBaseDatum

open EulerParentPacketFrames

local instance instBaseEulerSobolev1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Solution sobolev data, constructed using `EulerStaticEuler.baseSobolevData`. -/
def solutionSobolevData (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) :
    SobolevData (solutionEvolution β hβ ell hell hell1) :=
  EulerStaticEuler.baseSobolevData 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1

end EulerBaseDatum
