/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketAngularPotential
import LeanPool.NavierStokesAndEuler.Euler.AnglePrimitiveParity

/-! Jointly odd transverse profiles give the actual jointly even vector potential. -/

@[expose] public section


noncomputable section

namespace EulerPacketAngularPotential

open EulerSmoothLimit EulerPacketCrossProduct EulerAngleMeanZeroPrimitive MeasureTheory

theorem potential_joint_even (P : ℝ) (hP : P ≠ 0) (m : Space → Space)
    (A : Space → ℝ → Space) (hm : ∀ x, m (-x) = m x)
    (hA : ∀ x, Continuous (A x)) (hper : ∀ x, Function.Periodic (A x) P)
    (hmean : ∀ x, ∫ θ in 0..P, A x θ = 0)
    (hodd : ∀ x θ, A (-x) (-θ) = -A x θ) (x : Space) (θ : ℝ) :
    potential P (m (-x)) (A (-x)) (-θ)=potential P (m x) (A x) θ := by
  let f : ℝ → Space := fun s => potentialMultiplier (m x) (A x s)
  have hf : Continuous f := (potentialMultiplier (m x)).continuous.comp (hA x)
  have hp : Function.Periodic f P := fun s => congrArg (potentialMultiplier (m x)) (hper x s)
  have hz : (∫ s in 0..P, f s)=0 := by
    change (∫ s in 0..P, potentialMultiplier (m x) (A x s))=0
    rw [(potentialMultiplier (m x)).intervalIntegral_comp_comm ((hA x).intervalIntegrable 0 P),
      hmean x, map_zero]
  have he : (fun s => potentialMultiplier (m (-x)) (A (-x) s))=fun s => -f (-s) := by
    funext s
    rw [hm]
    have ha : A (-x) s=-A x (-s) := by simpa only [neg_neg] using hodd x (-s)
    rw [ha, map_neg]
  change primitive P (fun s => potentialMultiplier (m (-x)) (A (-x) s)) (-θ)=primitive P f θ
  rw [he, primitive_reflection P hP f hf hp hz]
  simp only [neg_neg]

end EulerPacketAngularPotential
