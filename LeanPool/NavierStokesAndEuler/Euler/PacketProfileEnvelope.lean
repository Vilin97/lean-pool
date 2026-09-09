/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketGevreyProfileChoice
public import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathWeight

/-! The actual grade scale is controlled by the source bound on `alpha*g`.
No reciprocal of alpha or extremum ratio of g enters this estimate. -/

@[expose] public section


noncomputable section

namespace EulerPacketTimeProfile.Scales

open Set EulerPacketCylinderField

theorem ofGrowth_H0_le {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (g : C(K, ℝ)) (hg : ∀ t, 0 < g t) (B : ℝ) (hB : 1 ≤ B)
    (hbound : ∀ t, g t ≤ B) : (ofGrowth g hg).H0 ≤ B := by
  apply max_le hB
  apply (ContinuousMap.norm_le g (zero_le_one.trans hB)).2
  intro t
  simpa only [Real.norm_eq_abs,abs_of_pos (hg t)] using hbound t

theorem ofTimeProfile_H0_le {T T' : ℝ} (g : C(Icc (0 : ℝ) T, ℝ))
    (hg : ∀ t, 0 < g t) (h : T = T') (α : ℝ) (hα : 0 < α)
    (B : ℝ) (hB : 1 ≤ B) (hbound : ∀ t, α * g t ≤ B) :
    (ofTimeProfile g hg h α hα).H0 ≤ B := by
  subst T'
  exact ofGrowth_H0_le (α • g) (fun t => mul_pos hα (hg t)) B hB hbound

end EulerPacketTimeProfile.Scales

namespace EulerElapsedTimePathGluing

open Set

theorem smul_profile_le (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (g : C(Icc (0 : ℝ) (S - τ), ℝ))
    (hg0 : g ⟨0, le_rfl, sub_nonneg.mpr hτS⟩ = 1)
    (α B : ℝ) (hα : α ≤ B) (hbound : ∀ t, α * g t ≤ B)
    (t : Icc (0 : ℝ) S) : α*profile S τ hτ0 hτS g hg0 t ≤ B := by
  by_cases ht : (t : ℝ) ≤ τ
  · rw [profile_left S τ hτ0 hτS g hg0 ⟨t,t.property.1,ht⟩,mul_one]
    exact hα
  · rw [profile_right S τ hτ0 hτS g hg0 ⟨t,(not_le.mp ht).le,t.property.2⟩]
    exact hbound _

end EulerElapsedTimePathGluing
