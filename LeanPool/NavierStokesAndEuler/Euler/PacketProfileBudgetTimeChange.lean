/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketBudgetTimeChange
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget

/-! Profile budgets and their actual path witnesses transport across equal time endpoints. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.ProfileBudget

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketTimeProfile

theorem changeTime {P T T' : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {support : Set Space}
    {a : Profile} {G : ProfileRegularity P T hT support a}
    {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} {p : ℕ}
    (B : ProfileBudget G S R p) (h : T = T') (hT' : 0 ≤ T') :
    ProfileBudget (G.changeTime h hT') (S.changeTime h) R p := by
  subst T'
  exact B

end EulerPacketCylinderField.ProfileBudget

namespace EulerPacketTimeProfile.Scales

open Set EulerPacketCylinderField

theorem growth_changeTime {T T' : ℝ} (S : Scales (Icc (0 : ℝ) T)) (h : T = T') :
    (S.changeTime h).growth = timeProfileChange S.growth h := by
  subst T'
  rfl

end EulerPacketTimeProfile.Scales
