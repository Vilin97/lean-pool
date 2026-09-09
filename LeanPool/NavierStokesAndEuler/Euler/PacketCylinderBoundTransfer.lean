/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear

@[expose] public section

/-! Transfer quantitative bounds between genuine witnesses of the same raw field on the interval. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set EulerPacketProfileRecursion EulerContinuousTimeWeight

variable {P T : ℝ} [Fact (0 < P)] {raw raw' : VectorField}
  {G : Field P T raw} (H : Field P T raw')

theorem WordBound.of_raw_eq {q d : ℕ} {R A : ℝ} (hG : G.WordBound q R A d)
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, raw' (t,(x,θ)) = raw (t,(x,θ))) :
    H.WordBound q R A d :=
  hG.of_path_eq H (H.path_eq_of_raw_eq G (fun t x θ => (he t x θ).symm))

theorem WordBound.normalized_of_raw_eq (hT : 0 ≤ T)
    (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
    {q d : ℕ} {R A : ℝ} (hG : (G.normalized hT g hg).WordBound q R A d)
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, raw' (t,(x,θ)) = raw (t,(x,θ))) :
    (H.normalized hT g hg).WordBound q R A d := by
  apply hG.of_raw_eq
  intro t x θ
  change (g (projIcc 0 T hT t))⁻¹ • raw' (t,(x,θ)) =
    (g (projIcc 0 T hT t))⁻¹ • raw (t,(x,θ))
  rw [he t x θ]

end EulerPacketCylinderField.Field
