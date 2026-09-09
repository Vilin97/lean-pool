/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerState
public import LeanPool.NavierStokesAndEuler.Euler.ParentState

/-! The concrete compactly supported datum supplies the full recursive
state: the physical Euler solution, all Sobolev orders, particle labels,
and odd symmetry all refer to the same solution. -/

@[expose] public section


noncomputable section

namespace EulerBaseDatum

open EulerParentPacketFrames

/-- Initial state, bundling `evolution`, `regularity`, `labels`, `odd`. -/
def initialState (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1) :
    SmoothState (initialParent β hβ ell hell hell1) where
  evolution := initialEvolution β hβ ell hell hell1
  regularity := initialSobolevData β hβ ell hell hell1
  labels := initialLabelData β hβ ell hell hell1
  odd := initialOddData β hβ ell hell hell1

end EulerBaseDatum
