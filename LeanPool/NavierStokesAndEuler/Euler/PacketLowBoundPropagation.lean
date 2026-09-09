/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketBaseGuardScales

@[expose] public section

/-! Numerical absorption in the sharp gradient and Hessian bounds,
and the common localized coercivity guard for all nested horizons. -/

noncomputable section

namespace EulerPacketLowBoundPropagation

open Real EulerPacketBaseGuardScales

theorem gradient_bound (CM hprev hchild g b e : ℝ)
    (hCM : 4 ≤ CM) (hp : 1 ≤ hprev) (hc : 1 ≤ hchild)
    (hscale : hprev^2 ≤ hchild/4) (hg : 4*g ≤ CM)
    (hbad : hchild*b+e ≤ 1) :
    CM*hprev+hchild*(g+b)+e ≤ CM*hchild := by
  have hCM0 : 0 ≤ CM := by linarith only [hCM]
  have hh : hprev ≤ hchild/4 := by nlinarith only [hp,hscale,sq_nonneg (hprev-1)]
  have ho := mul_le_mul_of_nonneg_left hh hCM0
  have hgood := mul_le_mul_of_nonneg_right hg (zero_le_one.trans hc)
  have hproduct : 4 ≤ CM*hchild := by nlinarith only [hCM,hc]
  nlinarith only [ho,hgood,hbad,hproduct]

theorem hessian_bound (CM CH hprev hold hchild g b e : ℝ)
    (hCH : 4 ≤ CH) (hp : 1 ≤ hprev) (hc : 1 ≤ hchild)
    (hhold : hold ≤ hprev) (hscale : hprev^2 ≤ hchild/4)
    (hg : 8*CM*g ≤ CH) (hbad : 2*CM*hprev*hchild*b+e ≤ 1) :
    CH*hprev*hold+2*CM*hprev*hchild*(g+b)+e ≤ CH*hchild*hprev := by
  have hCH0 : 0 ≤ CH := by linarith only [hCH]
  have hp0 := zero_le_one.trans hp
  have hc0 := zero_le_one.trans hc
  have hh := mul_le_mul_of_nonneg_left hhold (mul_nonneg hCH0 hp0)
  have hs := mul_le_mul_of_nonneg_left hscale hCH0
  have hprod : 1 ≤ hchild*hprev := one_le_mul_of_one_le_of_one_le hc hp
  have hprod0 := zero_le_one.trans hprod
  have hgood := mul_le_mul_of_nonneg_right hg hprod0
  have hmon := mul_le_mul_of_nonneg_left hp (mul_nonneg hCH0 hc0)
  have hproduct : 4 ≤ CH*(hchild*hprev) := by nlinarith only [hCH,hprod]
  nlinarith only [hh,hs,hgood,hmon,hbad,hproduct]

theorem localized_cost_le (J : ℕ) (X K Be Bc Kcap Becap CM Cboundary T : ℝ)
    (hK : 0 ≤ K) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc) (hT : 0 ≤ T)
    (hC : 0 ≤ Cboundary) (hr : 0 ≤ baseRadius X)
    (hKT : K ≤ Kcap) (hBeT : Be ≤ Becap) (hBcT : Bc ≤ CM*X^1000+2)
    (hTS : T ≤ baseHorizon J X) :
    K*(T^2/2)+Be*T+Cboundary*Bc*(baseRadius X)^3*T ≤
      baseGuardCost J Kcap Becap CM Cboundary X := by
  have hKcap0 := hK.trans hKT
  have hBecap0 := hBe.trans hBeT
  have hBccap0 := hBc.trans hBcT
  unfold baseGuardCost
  gcongr

theorem localized_guard (J : ℕ) (X K Be Bc Kcap Becap CM Cboundary T : ℝ)
    (hK : 0 ≤ K) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc) (hT : 0 ≤ T)
    (hC : 0 ≤ Cboundary) (hr : 0 ≤ baseRadius X)
    (hKT : K ≤ Kcap) (hBeT : Be ≤ Becap) (hBcT : Bc ≤ CM*X^1000+2)
    (hTS : T ≤ baseHorizon J X)
    (hbase : baseGuardCost J Kcap Becap CM Cboundary X ≤ 1/2) :
    K*(T^2/2)+Be*T+Cboundary*Bc*(baseRadius X)^3*T ≤ 1/2 :=
  (localized_cost_le J X K Be Bc Kcap Becap CM Cboundary T
    hK hBe hBc hT hC hr hKT hBeT hBcT hTS).trans hbase

end EulerPacketLowBoundPropagation
