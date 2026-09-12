/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget

/-! Quantitative profile estimates do not depend on the particular regularity witness. -/

@[expose] public section


namespace EulerPacketCylinderField.ProfileBudget

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketTimeProfile

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {support support' : Set Space}
  {a b : Profile} {G : ProfileRegularity P T hT support a}
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} {p : ℕ}

theorem of_profile_eq (hG : ProfileBudget G S R p) (hTpos : 0 < T)
    (H : ProfileRegularity P T hT support' b) (he : a = b) : ProfileBudget H S R p := by
  subst b
  exact hG.transfer hTpos H

end EulerPacketCylinderField.ProfileBudget
