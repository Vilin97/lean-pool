/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketNestedHorizons
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleActual
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketNeighborPolynomial
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceParameterScales
import LeanPool.NavierStokesAndEuler.Euler.ParentHistoryFrequencyGuard
import LeanPool.NavierStokesAndEuler.Euler.ParentPacketNeighborScaleGuard

/-! Fixed coefficient thresholds for the literal neighboring-label guard.
The history reciprocal is derived from the initial geometric step, and
the only parent size input is the already constructed parent's label bound. -/

@[expose] public section


noncomputable section

namespace EulerParentNeighborThreshold

open Real EulerParentNeighborCost EulerPacketSourceScaleSequence
  EulerParentHistoryFrequency

/-- Forward threshold, given by `boundConstant*4^degree`. -/
def forwardThreshold : ℝ := boundConstant*4^degree

/-- Joined threshold, given by `(boundConstant*(2*(1+CM+CH))^degree)*4^degree`. -/
def joinedThreshold (CM CH : ℝ) : ℝ :=
  (boundConstant*(2*(1+CM+CH))^degree)*4^degree

/-- Common threshold, given by `max forwardThreshold (joinedThreshold CM CH)`. -/
def commonThreshold (CM CH : ℝ) : ℝ :=
  max forwardThreshold (joinedThreshold CM CH)

/-- Required exponent, given by `80*degree+1`. -/
def requiredExponent : ℕ := 80*degree+1

theorem degree_le_requiredExponent : degree ≤ requiredExponent := by
  unfold requiredExponent
  omega

theorem forwardThreshold_le_common (CM CH : ℝ) :
    forwardThreshold ≤ commonThreshold CM CH := le_max_left _ _

theorem joinedThreshold_le_common (CM CH : ℝ) :
    joinedThreshold CM CH ≤ commonThreshold CM CH := le_max_right _ _

theorem threshold_le_previous (J D : ℕ) (hJ : 3 ≤ J) (X : ℝ) (hX : 0 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (B : ℝ) (hB : B ≤ X ^ D)
    (n : ℕ) : B ≤ previousFrequency J D X n :=
  hB.trans (initial_frequency_le_previous J D hJ X hX hbase n)

end EulerParentNeighborThreshold

namespace EulerParentPacketFrames.LabelData

open Set Real EulerSmoothLimit EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerParentNeighborCost EulerPacketSourceScaleSequence
  EulerPacketSourceScaleActual EulerParentNeighborThreshold EulerParentHistoryFrequency
  EulerPacketNestedHorizons EulerPacketBaseGuardScales

variable {G : Parent} (L : LabelData G)

theorem strainDifferenceCost_power :
    L.strainDifferenceCost ≤ boundConstant*(1+L.K)^degree := by
  simpa only [envelope,formula,strainDifferenceCost,mul_zero,add_zero] using
    envelope_power L.K 0 0 0 0 0 (zero_le_one.trans L.K_one)
      le_rfl le_rfl le_rfl le_rfl le_rfl

theorem strainDifferenceCost_monomial (k : ℝ) (c : ℕ)
    (hk : 1 ≤ k) (hKk : L.K ≤ k ^ 80)
    (hcost : forwardThreshold ≤ k) (hc : requiredExponent ≤ c) :
    L.strainDifferenceCost ≤ k^c := by
  have hconst := constant_pos
  have hn : degree ≤ c := degree_le_requiredExponent.trans hc
  have he : 80*degree+1 ≤ c := hc
  have hb := polynomial_le_monomial boundConstant L.K 0 0 k 1 degree 80 c
    hconst.le (zero_le_one.trans L.K_one) le_rfl le_rfl hk le_rfl hKk
    (pow_nonneg (zero_le_one.trans hk) 80) zero_le_one hcost he hn
  exact L.strainDifferenceCost_power.trans (by
    simpa only [add_zero,one_pow,mul_one] using hb)

theorem forward_neighbor_error_of_source_scales (J D : ℕ) (hJ : 3 ≤ J)
    (X ρ : ℝ) (hX : 1 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n c : ℕ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hKk : L.K ≤ previousFrequency J D X n ^ 80)
    (hcost : forwardThreshold ≤ previousFrequency J D X n)
    (hc : requiredExponent ≤ c) (hscale : G.ell ≤ supportScale J X n) :
    L.strainDifferenceCost*G.ell*ρ ≤ neighborError J D X (c : ℝ) n := by
  have hk := previousFrequency_one_le J D hJ X hX hbase n
  have hh : 1 ≤ previousShear J X n := by
    cases n with
    | zero => exact one_le_pow₀ hX
    | succ n =>
      apply one_le_exp
      exact div_nonneg
        ((zero_le_one.trans hX).trans
          (EulerPacketSourceParameterScales.sequence_initial_le J (by omega) X
            (zero_le_one.trans hX) n)) (by positivity)
  have hb := L.strainDifferenceCost_monomial (previousFrequency J D X n) c hk hKk hcost hc
  have hkn : 0 ≤ previousFrequency J D X n^c := pow_nonneg (zero_le_one.trans hk) c
  have hhn : 0 ≤ previousShear J X n^c := pow_nonneg (zero_le_one.trans hh) c
  have hb' : L.strainDifferenceCost ≤ previousFrequency J D X n^c*previousShear J X n^c :=
    hb.trans (le_mul_of_one_le_right hkn (one_le_pow₀ hh))
  have hprod : 0 ≤ previousFrequency J D X n^c*previousShear J X n^c := mul_nonneg hkn hhn
  calc
    _ ≤ (previousFrequency J D X n^c*previousShear J X n^c)*G.ell*ρ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb' G.ell_pos.le) hρ
    _ ≤ (previousFrequency J D X n^c*previousShear J X n^c)*G.ell := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hρ1
        (mul_nonneg hprod G.ell_pos.le)
    _ ≤ (previousFrequency J D X n^c*previousShear J X n^c)*supportScale J X n :=
      mul_le_mul_of_nonneg_left hscale hprod
    _ = neighborError J D X (c : ℝ) n := by
      simp only [neighborError,rpow_natCast]
      ring

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)

theorem joined_neighbor_error_of_literal_scales
    (J D : ℕ) (hJ : 3 ≤ J) (hD : 2000 ≤ D) (X ρ CM CH : ℝ)
    (hX : 2 ≤ X) (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4))
    (a β : ℕ → ℝ) (ha₀ : 1 / 2 ≤ a 0) (ha₀₂ : a 0 ≤ 2)
    (hβ₀ : 1 / 2 ≤ β 0 * X ^ 2) (hβ₀₂ : β 0 * X ^ 2 ≤ 2)
    (n c : ℕ) (hn : 1 ≤ n) (hτliteral : τ = activationTime J X a β n)
    (hτ1 : τ ≤ 1) (hCM : 0 ≤ CM) (hCH : 0 ≤ CH)
    (ha : 1 / 2 ≤ P.a) (hH : 1 ≤ P.shear)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hshear : P.shear = previousShear J X n)
    (hKk : L.K ≤ previousFrequency J D X n ^ 80)
    (hcost : joinedThreshold CM CH ≤ previousFrequency J D X n)
    (hc : requiredExponent ≤ c) (hscale : G.ell ≤ supportScale J X n) :
    L.neighborScaleCost m hm R S hS H τ hτ hτT P CM CH*G.ell*ρ ≤
      neighborError J D X (c : ℝ) n := by
  have hx0 : 0 < X := by linarith only [hX]
  have hx1 : 1 ≤ X := by linarith only [hX]
  have hTi : τ⁻¹ ≤ 12/baseHorizon J X := by
    rw [hτliteral]
    exact reciprocal_activation_le_base J (by omega) X hx0 a β ha₀ ha₀₂ hβ₀ hβ₀₂ hn
  have hTik := base_inverse_le_previous_frequency_pow80 J D hJ hD X hX hbase n
  have hk := previousFrequency_one_le J D hJ X hx1 hbase n
  exact L.neighbor_error_of_source_scales m hm R S hS H τ hτ hτT P
    (12/baseHorizon J X) CM CH hτ1 hTi hCM hCH ha hH J D X ρ n 80 c
    hρ hρ1 hshear hk hKk hTik hcost hc (degree_le_requiredExponent.trans hc) hscale

end EulerParentPacketFrames.LabelData
