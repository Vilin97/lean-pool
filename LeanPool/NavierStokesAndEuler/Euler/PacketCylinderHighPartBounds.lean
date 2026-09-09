/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear

@[expose] public section

/-! Bounds for literal high projection and for the zero fields in masked grade families. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerPacketProfileRecursion
  EulerCylinderAngleAverage

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}

@[simp] theorem highPart_path (G : Field P T raw) :
    G.highPart.path = G.path-pathAverage P G.path := by
  change G.path + -(pathAverage P G.path) = G.path-pathAverage P G.path
  rw [sub_eq_add_neg]

theorem wordBound_of_zero (G : Field P T raw)
    (hz : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(x,θ)) = 0)
    (q : ℕ) (R : ℝ) (d : ℕ) : G.WordBound q R 0 d := by
  have hp : G.path = (Field.zero P T).path :=
    G.path_eq_of_raw_eq (Field.zero P T) (fun t x θ => (hz t x θ).symm)
  exact (wordBound_zero P T q R d).of_path_eq G hp

theorem wordBound_normalized_of_zero (G : Field P T raw)
    (hz : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(x,θ)) = 0)
    (hT : 0 ≤ T) (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
    (q : ℕ) (R : ℝ) (d : ℕ) : (G.normalized hT g hg).WordBound q R 0 d := by
  apply wordBound_of_zero
  intro t x θ
  change (g (projIcc 0 T hT t))⁻¹ • raw (t,(x,θ)) = 0
  rw [hz t x θ,smul_zero]

variable {G : Field P T raw} {q d : ℕ} {R A : ℝ}

theorem WordBound.highPart (hG : G.WordBound q R A d) :
    G.highPart.WordBound q R (2*A) d := by
  have h := hG.sub hG.angleMean
  simpa only [Field.highPart,two_mul] using h

theorem WordBound.normalized_highPart (hT : 0 ≤ T)
    (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
    (hG : (G.normalized hT g hg).WordBound q R A d) :
    (G.highPart.normalized hT g hg).WordBound q R (2*A) d := by
  have h := hG.normalized_sub hT (hG.normalized_angleMean hT)
  simpa only [Field.highPart,two_mul] using h

end EulerPacketCylinderField.Field
