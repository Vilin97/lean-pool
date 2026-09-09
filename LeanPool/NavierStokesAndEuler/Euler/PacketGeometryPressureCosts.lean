/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureScaleCosts

@[expose] public section

/-! Actual geometric pressure increments are dominated by the literal
summable scale costs. The physical parent-strain bound is CM times the
previous shear, while the activation constants remain fixed low constants. -/

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set Real EulerSmoothLimit EulerPacketSourceGeometry EulerPacketGeometryLowBounds
  EulerPacketPressureScale EulerPacketSourceScaleSequence EulerPacketSourceScaleChoice
  EulerPacketSourceScales EulerScale EulerParentBadRatio

variable {G : Parent} (L : LabelData G)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)
  (A : Guards hτ hτT P (G.historyOn H m hm R S hS τ hτ hτT))
  (Ti : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)
  (J D : ℕ) (hJ : 3 ≤ J) (X Cθ CM CMn CHn c : ℝ)
  (hX : 1 ≤ X) (hCθ : 1 ≤ Cθ) (hCM : 0 ≤ CM) (hCMn : 0 ≤ CMn) (hCHn : 0 ≤ CHn) (hc : 1 ≤ c)
  (hbaseH : X^1000 ≤ exp (X/((J-1 : ℕ) : ℝ)^7))
  (hbaseK : X^D ≤ exp (X/((J-1 : ℕ) : ℝ)^4))
  (n : ℕ) (M : ℝ)
  (hK : L.K ≤ previousFrequency J D X n^c) (hTib : Ti ≤ previousShear J X n)
  (hCMb : A.CM ≤ CMn) (hCHb : A.CH ≤ CHn)
  (hTheta : P.horizon ≤ sourceTheta J Cθ (scaleSequence J X) n)
  (hSigma : P.sigma*scaleSequence J X n ≤ 2)
  (hchild : A.hchild ≤ shear J X n) (hMb : M ≤ CM*previousShear J X n)

include hτ1 hTi hJ hX hCθ hCM hCMn hCHn hc hbaseH hbaseK hK hTib hCMb hCHb hTheta hSigma hchild hMb

theorem joined_bad_pressure_cost_bound :
    2*M*A.hchild*A.badRatio ≤ badCost J Cθ CM CMn CHn c (scaleSequence J X) n := by
  have hx := quadratic_growth_one_le J (by omega) (scaleSequence J X) hX (scaleSequence_succ J X)
  have hs : 1 ≤ P.shear := by
    have hh := mul_le_mul_of_nonneg_left hτ1 A.shear_pos.le
    nlinarith only [hh,A.history_layer]
  have hi : P.shear⁻¹ ≤ 1 := (inv_le_one₀ A.shear_pos).2 hs
  have hQ := parameters_le_source_exponential J D hJ X c hX hc hbaseH hbaseK n
    L.K Ti P.shear⁻¹ A.CM A.CH CMn CHn hK hTib hi hCMb hCHb hCMn hCHn
  have ht0 := (inv_pos.mpr hτ).le.trans hTi
  have hQ0 : 0 ≤ 1+L.K+Ti+P.shear⁻¹+A.CM+A.CH := by
    positivity [L.K_one,A.shear_pos,A.CM_nonneg,A.CH_nonneg]
  have hM' := hMb.trans (mul_le_mul_of_nonneg_left
    (previousShear_le_normal J (by omega) X hbaseH n) hCM)
  exact badCost_bound J hJ Cθ CM CMn CHn c hCθ hCM hCMn hCHn (scaleSequence J X) hx n
    M A.hchild A.badRatio (1+L.K+Ti+P.shear⁻¹+A.CM+A.CH) P.horizon P.sigma
    A.child_nonneg A.badRatio_nonneg hQ0 (zero_le_one.trans A.horizon_lower) A.sigma_pos
    hM' hchild hQ hTheta hSigma
    (L.badRatio_polynomial m hm R S hS H τ hτ hτT P A Ti hτ1 hTi)

theorem joined_upper_pressure_cost_bound (hdelta : A.δ ≤ spike J X n) :
    2*M*A.hchild*(A.δ*goodRatio+A.badRatio) ≤
      2*CM*goodRatio*goodCost J (scaleSequence J X) n+
        badCost J Cθ CM CMn CHn c (scaleSequence J X) n := by
  have hb := L.joined_bad_pressure_cost_bound m hm R S hS H τ hτ hτT P A Ti hτ1 hTi
    J D hJ X Cθ CM CMn CHn c hX hCθ hCM hCMn hCHn hc hbaseH hbaseK n M
    hK hTib hCMb hCHb hTheta hSigma hchild hMb
  have hg := goodCost_bound J (by omega) X CM M A.δ A.hchild hCM A.delta_nonneg A.child_nonneg
    hbaseH n hMb hdelta hchild
  calc
    _ = 2*M*A.hchild*(A.δ*goodRatio)+2*M*A.hchild*A.badRatio := by ring
    _ ≤ _ := add_le_add hg hb

theorem joined_initial_gradient_cost_bound (hMone : 1 ≤ M) (ev : ℝ) :
    A.hchild*A.badRatio+ev ≤ badCost J Cθ CM CMn CHn c (scaleSequence J X) n+ev := by
  have hb := L.joined_bad_pressure_cost_bound m hm R S hS H τ hτ hτT P A Ti hτ1 hTi
    J D hJ X Cθ CM CMn CHn c hX hCθ hCM hCMn hCHn hc hbaseH hbaseK n M
    hK hTib hCMb hCHb hTheta hSigma hchild hMb
  have hbase : A.hchild*A.badRatio ≤ 2*M*A.hchild*A.badRatio := by
    nlinarith only [mul_nonneg (by linarith only [hMone] : 0 ≤ 2*M-1)
      (mul_nonneg A.child_nonneg A.badRatio_nonneg)]
  exact add_le_add (hbase.trans hb) le_rfl

end EulerParentPacketFrames.LabelData

namespace EulerPacketSourceGeometry.ForwardGuards

open Real EulerSmoothLimit EulerPacketGeometryLowBounds EulerParentBadRatio
  EulerPacketPressureScale EulerPacketSourceScaleSequence EulerPacketSourceScaleChoice
  EulerPacketSourceScales EulerScale

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U} {P : ParentFrame D 0} (A : ForwardGuards P)

omit [CompleteSpace U] in
theorem earlyRatio_bound :
    A.earlyRatio ≤ badConstant*1^degree*P.horizon^5*exp (-(1/(4*P.sigma))) := by
  have hh : cutoffBound*(8232*exp 9*P.horizon^5) ≤
      cutoffBound*(8232*exp 9*P.horizon^5+4*P.horizon*(boundConstant*1^degree)) := by
    apply mul_le_mul_of_nonneg_left _ cutoffBound_pos.le
    exact le_add_of_nonneg_right (by positivity [A.horizon_lower,constant_pos])
  rw [show A.earlyRatio=cutoffBound*(8232*exp 9*P.horizon^5)*exp (-(1/(4*P.sigma))) by
    unfold earlyRatio
    ring]
  apply (mul_le_mul_of_nonneg_right hh (exp_pos _).le).trans
  exact mul_le_mul_of_nonneg_right (prefactor_bound 1 P.horizon le_rfl A.horizon_lower) (exp_pos
    _).le

variable (J : ℕ) (hJ : 3 ≤ J) (X Cθ CM CMn CHn c : ℝ)
  (hX : 1 ≤ X) (hCθ : 1 ≤ Cθ) (hCM : 0 ≤ CM) (hCMn : 0 ≤ CMn) (hCHn : 0 ≤ CHn) (hc : 0 ≤ c)
  (hbaseH : X^1000 ≤ exp (X/((J-1 : ℕ) : ℝ)^7))
  (n : ℕ) (M : ℝ)
  (hTheta : P.horizon ≤ sourceTheta J Cθ (scaleSequence J X) n)
  (hSigma : P.sigma*scaleSequence J X n ≤ 2)
  (hchild : A.hchild ≤ shear J X n) (hMb : M ≤ CM*previousShear J X n)

include hJ hX hCθ hCM hCMn hCHn hc hbaseH hTheta hSigma hchild hMb

omit [CompleteSpace U] in
theorem bad_pressure_cost_bound :
    2*M*A.hchild*A.earlyRatio ≤ badCost J Cθ CM CMn CHn c (scaleSequence J X) n := by
  have hx := quadratic_growth_one_le J (by omega) (scaleSequence J X) hX (scaleSequence_succ J X)
  have hz : 0 ≤ c*(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^4) := by positivity [hx n]
  have he := one_le_exp hz
  have hQ : 1 ≤ (4+CMn+CHn)*exp (c*(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^4)) := by
    nlinarith only [he,mul_nonneg hCMn (zero_le_one.trans he),mul_nonneg hCHn (zero_le_one.trans
      he)]
  have hM' := hMb.trans (mul_le_mul_of_nonneg_left
    (previousShear_le_normal J (by omega) X hbaseH n) hCM)
  exact badCost_bound J hJ Cθ CM CMn CHn c hCθ hCM hCMn hCHn (scaleSequence J X) hx n
    M A.hchild A.earlyRatio 1 P.horizon P.sigma A.child_nonneg A.earlyRatio_nonneg zero_le_one
    (zero_le_one.trans A.horizon_lower) A.sigma_pos hM' hchild hQ hTheta hSigma A.earlyRatio_bound

omit [CompleteSpace U] in
theorem upper_pressure_cost_bound (hdelta : A.δ ≤ spike J X n) :
    2*M*A.hchild*(A.δ*goodRatio+A.earlyRatio) ≤
      2*CM*goodRatio*goodCost J (scaleSequence J X) n+
        badCost J Cθ CM CMn CHn c (scaleSequence J X) n := by
  have hb := A.bad_pressure_cost_bound J hJ X Cθ CM CMn CHn c hX hCθ hCM hCMn hCHn hc
    hbaseH n M hTheta hSigma hchild hMb
  have hg := goodCost_bound J (by omega) X CM M A.δ A.hchild hCM A.delta_nonneg A.child_nonneg
    hbaseH n hMb hdelta hchild
  calc
    _ = 2*M*A.hchild*(A.δ*goodRatio)+2*M*A.hchild*A.earlyRatio := by ring
    _ ≤ _ := add_le_add hg hb

omit [CompleteSpace U] in
theorem initial_gradient_cost_bound (hMone : 1 ≤ M) (ev : ℝ) :
    A.hchild*A.earlyRatio+ev ≤ badCost J Cθ CM CMn CHn c (scaleSequence J X) n+ev := by
  have hb := A.bad_pressure_cost_bound J hJ X Cθ CM CMn CHn c hX hCθ hCM hCMn hCHn hc
    hbaseH n M hTheta hSigma hchild hMb
  have hbase : A.hchild*A.earlyRatio ≤ 2*M*A.hchild*A.earlyRatio := by
    nlinarith only [mul_nonneg (by linarith only [hMone] : 0 ≤ 2*M-1)
      (mul_nonneg A.child_nonneg A.earlyRatio_nonneg)]
  exact add_le_add (hbase.trans hb) le_rfl

end EulerPacketSourceGeometry.ForwardGuards
