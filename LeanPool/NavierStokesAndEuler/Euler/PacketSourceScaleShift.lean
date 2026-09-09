/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyScales
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-! Exact reindexing of the prescribed scale sequence after finitely many
exceptional initial stages. No new choice of asymptotic scales is made. -/

@[expose] public section


noncomputable section

namespace EulerPacketSourceScaleSequence

open EulerPacketSourceScaleChoice EulerPacketUniformFrequencyScales

theorem scaleSequence_shift (J : ℕ) (X : ℝ) (r n : ℕ) :
    scaleSequence (J+r) (scaleSequence J X r) n=scaleSequence J X (r+n) := by
  induction n with
  | zero => simp only [scaleSequence_zero,Nat.add_zero]
  | succ n ih =>
    rw [scaleSequence_succ,ih,show r+(n+1)=(r+n)+1 by omega,scaleSequence_succ,Nat.add_assoc]

theorem frequency_shift (J : ℕ) (X : ℝ) (r n : ℕ) :
    frequency (J+r) (scaleSequence J X r) n=frequency J X (r+n) := by
  simp only [frequency,scaleSequence_shift,Nat.add_assoc]

theorem supportScale_shift (J : ℕ) (X : ℝ) (r n : ℕ) :
    supportScale (J+r) (scaleSequence J X r) n=supportScale J X (r+n) := by
  simp only [supportScale,scaleSequence_shift,Nat.add_assoc]

theorem spike_shift (J : ℕ) (X : ℝ) (r n : ℕ) :
    spike (J+r) (scaleSequence J X r) n=spike J X (r+n) := by
  simp only [spike,scaleSequence_shift,Nat.add_assoc]

theorem parameterEnvelope_shift (J : ℕ) (hJ : 1 ≤ J) (C c : ℝ) (p q : ℕ)
    (X : ℝ) (r n : ℕ) :
    parameterEnvelope (J+r) C c p q (scaleSequence J X r) n =
      parameterEnvelope J C c p q X (r+n) := by
  have he : J+r-1+n=J-1+(r+n) := by omega
  simp only [parameterEnvelope,scaleSequence_shift,Nat.add_assoc,he]

end EulerPacketSourceScaleSequence
