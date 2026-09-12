/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketGradeAbsorption

/-! A single spare shift absorbs every fixed linear-operator amplitude at the same radius. -/

@[expose] public section


namespace EulerGevrey

theorem amplitude_absorbed (A R : ℝ) (hA : 0 ≤ A) (hAR : A ≤ R) (d n : ℕ) :
    A*majorant R d n ≤ majorant R (d+1) n := by
  have hcount : 1 ≤ (d+1)^2 := by
    simpa only [one_pow] using Nat.pow_le_pow_left (by omega : 1 ≤ d+1) 2
  have h := finite_cost_absorbed A R hA hAR 1 (d+1) n (by omega) hcount
  simpa only [Nat.cast_one,mul_one,Nat.add_sub_cancel] using h

end EulerGevrey

namespace EulerPacketCylinderField.Field

open EulerGevrey EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} {G : Field P T raw}
  {q d e : ℕ} {R A : ℝ}

theorem WordBound.absorb_amplitude (hG : G.WordBound q R A d) (hA : 0 ≤ A) (hAR : A ≤ R) :
    G.WordBound q R 1 (d+1) := by
  intro n
  simpa only [one_mul] using (hG n).trans (amplitude_absorbed A R hA hAR d n)

theorem WordBound.absorb_amplitude_to (hG : G.WordBound q R A d)
    (hR : 1 ≤ R) (hA : 0 ≤ A) (hAR : A ≤ R) (hde : d + 1 ≤ e) : G.WordBound q R 1 e :=
  (hG.absorb_amplitude hA hAR).mono_shift hR zero_le_one hde

end EulerPacketCylinderField.Field
