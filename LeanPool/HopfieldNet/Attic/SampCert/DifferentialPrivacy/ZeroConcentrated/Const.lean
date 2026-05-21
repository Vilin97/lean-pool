/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Generic
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.ZeroConcentrated.DP

/-!
# zCDP Constant function

This file proves a zCDP bound on the constant query
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

variable { T U : Type }
-- Could weaken these, but there's no point, since we need to establish these for the more useful queries too.
variable [MeasurableSpace U]
variable [MeasurableSingletonClass U]
variable [Countable U]

/--
Constant query satisfies zCDP Renyi divergence bound.
-/
theorem privConst_zCDPBound {u : U} : zCDPBound (privConst u : Mechanism T U) 0 := by
  simp [zCDPBound, privConst]
  intros
  refine (RenyiDivergence_aux_zero (PMF.pure u) (PMF.pure u) ?G1 fun x a => a).mp rfl
  linarith

/--
Constant query satisfies absolute continuity
-/
def privConst_AC {u : U} : ACNeighbour (privConst u : Mechanism T U) := by
  simp [ACNeighbour, AbsCts, privConst]

/--
``privComposeAdaptive`` satisfies zCDP
-/
theorem privConst_zCDP : ∀ (u : U), zCDP (privConst u : Mechanism T U) (0 : NNReal) := by
  simp [zCDP] at *
  intro u
  apply And.intro
  · apply privConst_AC
  · apply privConst_zCDPBound
end SLang
