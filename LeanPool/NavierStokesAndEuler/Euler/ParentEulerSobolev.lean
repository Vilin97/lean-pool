/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerState
public import LeanPool.NavierStokesAndEuler.Euler.SmoothEulerEvolution

@[expose] public section

/-! The actual physical velocity and pressure force in every Sobolev
order. Strong time evolution follows from their classical Euler equation
and continuous L² jets, including both endpoint derivatives. -/

noncomputable section

namespace EulerParentPacketFrames

open Set EulerSmoothLimit EulerLpTranslation EulerSmoothFieldSobolevTime
  EulerSmoothEulerEvolution EulerVolterraConvolution EulerTimeIntervalRestriction

structure SobolevData {A : Parent} (E : Evolution A) where
  velocity : Icc (0 : ℝ) A.T → SmoothL2Field Space
  force : Icc (0 : ℝ) A.T → SmoothL2Field Space
  velocity_match : ∀ (t : Icc (0 : ℝ) A.T) x, E.velocity (t,x)=(velocity t).field x
  force_match : ∀ (t : Icc (0 : ℝ) A.T) x, E.force t x=(force t).field x
  velocity_continuous : ∀ n, Continuous (fun t => (velocity t).jetLp n)
  force_continuous : ∀ n, Continuous (fun t => (force t).jetLp n)

namespace SobolevData

variable {A : Parent} {E : Evolution A} (S : SobolevData E)

theorem strong_euler (q : ℕ) (t : Icc (0 : ℝ) A.T) :
    HasDerivWithinAt (extendPath A.T A.T_pos.le
      (sobolevPath S.velocity S.velocity_continuous q))
      (sobolevPath (rhs S.velocity S.velocity_continuous S.force)
        (rhs_jet_continuous S.velocity S.velocity_continuous S.force S.force_continuous) q t)
      (Icc (0 : ℝ) A.T) t :=
  sobolev_evolution_of_classical A.T A.T_pos.le S.velocity S.force
    S.velocity_continuous S.force_continuous E.velocity E.pressure S.velocity_match
    (fun s x => (E.pressure_gradient s x).trans (S.force_match s x))
    E.velocity_differentiable E.momentum_zero q t

def restrictTime (T : ℝ) (hT : 0 < T) (hTA : T ≤ A.T) :
    SobolevData (E.restrictTime T hT hTA) where
  velocity t := S.velocity (initialInclusion A.T T hTA t)
  force t := S.force (initialInclusion A.T T hTA t)
  velocity_match t x := S.velocity_match (initialInclusion A.T T hTA t) x
  force_match t x := S.force_match (initialInclusion A.T T hTA t) x
  velocity_continuous n := (S.velocity_continuous n).comp (initialInclusion A.T T hTA).continuous
  force_continuous n := (S.force_continuous n).comp (initialInclusion A.T T hTA).continuous

end SobolevData
end EulerParentPacketFrames
