/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderField

import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Genuine within-time derivatives inherit the raw field's joint parity, including at the
endpoints. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.Field

open Set EulerSmoothLimit EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)] {raw raw_t : VectorField}
  (G : Field P T raw) (H : Field P T raw_t)

theorem timeDerivative_parity (hT : 0 < T) (hd : TimeDerivative hT.le G H) (c : ℝ)
    (hpar : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t, (-x, -θ)) = c • raw (t, (x, θ)))
    (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) : raw_t (t,(-x,-θ)) = c • raw_t (t,(x,θ)) := by
  have h₁ := G.raw_hasDerivWithinAt hT.le H hd t (-x) (-θ)
  have h₂ := (G.raw_hasDerivWithinAt hT.le H hd t x θ).const_smul c
  have h₂' : HasDerivWithinAt (fun r => raw (r,(-x,-θ))) (c • raw_t (t,(x,θ)))
      (Icc (0 : ℝ) T) t := h₂.congr_of_mem (fun r hr => hpar ⟨r,hr⟩ x θ) t.property
  exact (h₁.derivWithin ((uniqueDiffOn_Icc hT) _ t.property)).symm.trans
    (h₂'.derivWithin ((uniqueDiffOn_Icc hT) _ t.property))

theorem timeDerivative_odd (hT : 0 < T) (hd : TimeDerivative hT.le G H)
    (hpar : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t, (-x, -θ)) = -raw (t, (x, θ)))
    (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) : raw_t (t,(-x,-θ)) = -raw_t (t,(x,θ)) := by
  simpa only [neg_one_smul] using G.timeDerivative_parity H hT hd (-1)
    (by simpa only [neg_one_smul] using hpar) t x θ

end EulerPacketCylinderField.Field
