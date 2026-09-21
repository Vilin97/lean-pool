/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.Counterexample
import LeanPool.QuadraticCarleson.QuadraticCarleson.SchwartzOperator

/-!
# The counterexample as a Schwartz function

The paper's finite wave-packet superposition is smooth and compactly
supported, hence belongs to Schwartz space.  Bundling it this way lets the
canonical distributional quadratic Hilbert transform act on it directly.
-/

open scoped ContDiff SchwartzMap

namespace QuadraticCarleson

theorem contDiff_wavePacket (s t : ℝ) : ContDiff ℝ ∞ (wavePacket s t) := by
  unfold wavePacket
  exact contDiff_const.mul
    (baseBump_smooth.comp ((contDiff_id.sub contDiff_const).div_const t))

theorem contDiff_packetSum (N : ℕ) : ContDiff ℝ ∞ (packetSum N) := by
  rw [packetSum, Finset.sum_fn]
  exact ContDiff.sum fun j _ ↦ contDiff_wavePacket (j : ℝ) (packetScale N j)

theorem contDiff_counterexampleReal (N : ℕ) :
    ContDiff ℝ ∞ (counterexampleReal N) := by
  unfold counterexampleReal
  exact contDiff_const.mul (contDiff_packetSum N)

theorem contDiff_counterexample (N : ℕ) : ContDiff ℝ ∞ (counterexample N) := by
  unfold counterexample
  exact Complex.ofRealCLM.contDiff.comp (contDiff_counterexampleReal N)

/-- The counterexample `χ_N` as a complex Schwartz function. -/
noncomputable def counterexampleSchwartz (N : ℕ) : 𝓢(ℝ, ℂ) :=
  (counterexample_hasCompactSupport N).toSchwartzMap (contDiff_counterexample N)

@[simp]
theorem counterexampleSchwartz_apply (N : ℕ) (x : ℝ) :
    counterexampleSchwartz N x = counterexample N x :=
  rfl

end QuadraticCarleson
