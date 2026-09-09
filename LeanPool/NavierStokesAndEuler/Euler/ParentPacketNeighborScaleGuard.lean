/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketNeighborPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleActual

/-! The computed neighboring-label cost fits the source's monomial
majorant under fixed degree and constant guards. Thus the small support
scale discharges the literal neighbor comparison in the geometry step. -/

@[expose] public section


noncomputable section

namespace EulerParentNeighborCost

theorem polynomial_le_monomial (A K Ti H k h : ℝ) (n q c : ℕ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hTi : 0 ≤ Ti) (hH : 0 ≤ H)
    (hk : 1 ≤ k) (hh : 1 ≤ h) (hKk : K ≤ k ^ q) (hTik : Ti ≤ k ^ q) (hHh : H ≤ h)
    (hcost : A * 4 ^ n ≤ k) (hc : q * n + 1 ≤ c) (hn : n ≤ c) :
    A*(1+K+Ti+H)^n ≤ k^c*h^c := by
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hh0 : 0 ≤ h := zero_le_one.trans hh
  have hkq : 1 ≤ k^q := one_le_pow₀ hk
  have hkq0 : 0 ≤ k^q := zero_le_one.trans hkq
  have hkh : 1 ≤ k^q*h := one_le_mul_of_one_le_of_one_le hkq hh
  have hkk : k^q ≤ k^q*h := le_mul_of_one_le_right hkq0 hh
  have hhh : h ≤ k^q*h := le_mul_of_one_le_left hh0 hkq
  have hb : 1+K+Ti+H ≤ 4*k^q*h := by
    nlinarith only [hkh,hKk.trans hkk,hTik.trans hkk,hHh.trans hhh]
  calc
    _ ≤ A*(4*k^q*h)^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb n) hA
    _ = (A*4^n)*(k^(q*n)*h^n) := by simp only [mul_pow,← pow_mul]; ring
    _ ≤ k*(k^(q*n)*h^n) := mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = k^(q*n+1)*h^n := by rw [pow_succ]; ring
    _ ≤ k^c*h^c := mul_le_mul (pow_le_pow_right₀ hk hc) (pow_le_pow_right₀ hh hn)
      (pow_nonneg hh0 n) (pow_nonneg hk0 c)

end EulerParentNeighborCost

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerParentNeighborCost EulerPacketSourceScaleSequence
  EulerPacketSourceScaleActual

variable {G : Parent} (L : LabelData G)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)
  (Ti CM CH : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)
  (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (ha : 1 / 2 ≤ P.a) (hH : 1 ≤ P.shear)

include hτ1 hTi hCM hCH ha hH in
theorem neighborScaleCost_monomial (k : ℝ) (q c : ℕ)
    (hk : 1 ≤ k) (hKk : L.K ≤ k ^ q) (hTik : Ti ≤ k ^ q)
    (hcost : (EulerParentNeighborCost.boundConstant * (2 * (1 + CM + CH)) ^ degree) * 4 ^ degree
        ≤ k)
    (hc : q * degree + 1 ≤ c) (hn : degree ≤ c) :
    L.neighborScaleCost m hm R S hS H τ hτ hτT P CM CH ≤ k^c*P.shear^c := by
  have hconst := EulerParentNeighborCost.constant_pos
  exact (L.neighborScaleCost_low_polynomial m hm R S hS H τ hτ hτT P Ti CM CH
    hτ1 hTi hCM hCH ha hH).trans
      (polynomial_le_monomial
        (EulerParentNeighborCost.boundConstant * (2*(1+CM+CH))^degree)
        L.K Ti P.shear k P.shear degree q c (by positivity)
        (zero_le_one.trans L.K_one) ((inv_pos.mpr hτ).le.trans hTi)
        (zero_le_one.trans hH) hk hH hKk hTik le_rfl hcost hc hn)

include hτ1 hTi hCM hCH ha hH in
theorem neighbor_error_of_source_scales (J D : ℕ) (X ρ : ℝ) (j q c : ℕ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hshear : P.shear = previousShear J X j)
    (hk : 1 ≤ previousFrequency J D X j)
    (hKk : L.K ≤ previousFrequency J D X j ^ q) (hTik : Ti ≤ previousFrequency J D X j ^ q)
    (hcost : (EulerParentNeighborCost.boundConstant * (2 * (1 + CM + CH)) ^ degree) * 4 ^ degree
        ≤ previousFrequency J D X j)
    (hc : q * degree + 1 ≤ c) (hn : degree ≤ c)
    (hscale : G.ell ≤ supportScale J X j) :
    L.neighborScaleCost m hm R S hS H τ hτ hτT P CM CH*G.ell*ρ ≤
      neighborError J D X (c : ℝ) j := by
  have hbound := L.neighborScaleCost_monomial m hm R S hS H τ hτ hτT P Ti CM CH
    hτ1 hTi hCM hCH ha hH (previousFrequency J D X j) q c hk hKk hTik hcost hc hn
  have hmono : 0 ≤ previousFrequency J D X j^c*P.shear^c :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hk) c) (pow_nonneg (zero_le_one.trans hH) c)
  calc
    _ ≤ (previousFrequency J D X j^c*P.shear^c)*G.ell*ρ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbound G.ell_pos.le) hρ
    _ ≤ (previousFrequency J D X j^c*P.shear^c)*G.ell := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hρ1 (mul_nonneg hmono G.ell_pos.le)
    _ ≤ (previousFrequency J D X j^c*P.shear^c)*supportScale J X j :=
      mul_le_mul_of_nonneg_left hscale hmono
    _ = neighborError J D X (c : ℝ) j := by
      simp only [neighborError,Real.rpow_natCast,hshear]
      ring

end EulerParentPacketFrames.LabelData
