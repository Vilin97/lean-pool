/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketStageGuards
import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalScaleApplication
public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureScaleCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryLowBounds
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Scale
public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionStage
import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScaleBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketLowBoundPropagation
import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalPrefix
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryForwardChoice
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryJoinedChoice
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerChild
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardChildLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketChildLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceCenter
public import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalParameters
public import LeanPool.NavierStokesAndEuler.Euler.ParentStateGeometry
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryGuards

/-! Related estimates used together by the same construction modules. -/

section

/-! The actual stage guards satisfy the fixed pressure, initial-gradient
and frame-renewal budgets used by the induction. -/

section

/-! Actual geometric pressure increments are dominated by the literal
summable scale costs. The physical parent-strain bound is CM times the
previous shear, while the activation constants remain fixed low constants. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set Real EulerSmoothLimit EulerPacketSourceGeometry EulerPacketGeometryLowBounds
  EulerPacketPressureScale EulerPacketSourceScaleSequence EulerPacketSourceScaleChoice
  EulerPacketSourceScales EulerScale EulerParentBadRatio

variable {G : Parent} (L : LabelData G)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)
  (A : Guards hτ hτT P (G.historyOn H m hm R S hS τ hτ hτT))
  (Ti : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)
  (J D : ℕ) (hJ : 3 ≤ J) (X Cθ CM CMn CHn c : ℝ)
  (hX : 1 ≤ X) (hCθ : 1 ≤ Cθ) (hCM : 0 ≤ CM) (hCMn : 0 ≤ CMn) (hCHn : 0 ≤ CHn) (hc : 1 ≤ c)
  (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
  (hbaseK : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4))
  (n : ℕ) (M : ℝ)
  (hK : L.K ≤ previousFrequency J D X n ^ c) (hTib : Ti ≤ previousShear J X n)
  (hCMb : A.CM ≤ CMn) (hCHb : A.CH ≤ CHn)
  (hTheta : P.horizon ≤ sourceTheta J Cθ (scaleSequence J X) n)
  (hSigma : P.sigma * scaleSequence J X n ≤ 2)
  (hchild : A.hchild ≤ shear J X n) (hMb : M ≤ CM * previousShear J X n)

include hτ1 hTi hJ hX hCθ hCM hCMn hCHn hc hbaseH hbaseK hK hTib hCMb hCHb hTheta hSigma hchild hMb

theorem joined_bad_pressure_cost_bound :
    2*M*A.hchild*A.badRatio ≤ badCost J Cθ CM CMn CHn c (scaleSequence J X) n := by
  have hx := quadratic_growth_one_le J (by omega) (scaleSequence J X) hX (scaleSequence_succ J X)
  have hs : 1 ≤ P.shear := by
    have hh := mul_le_mul_of_nonneg_left hτ1 A.shear_pos.le
    linarith only [hh,A.history_layer]
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
      2*CM*goodRatio*goodCost J (scaleSequence J X) n +
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
    linarith only [mul_nonneg (by linarith only [hMone] : 0 ≤ 2*M-1)
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
  (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
  (n : ℕ) (M : ℝ)
  (hTheta : P.horizon ≤ sourceTheta J Cθ (scaleSequence J X) n)
  (hSigma : P.sigma * scaleSequence J X n ≤ 2)
  (hchild : A.hchild ≤ shear J X n) (hMb : M ≤ CM * previousShear J X n)

include hJ hX hCθ hCM hCMn hCHn hc hbaseH hTheta hSigma hchild hMb

omit [CompleteSpace U] in
theorem bad_pressure_cost_bound :
    2*M*A.hchild*A.earlyRatio ≤ badCost J Cθ CM CMn CHn c (scaleSequence J X) n := by
  have hx := quadratic_growth_one_le J (by omega) (scaleSequence J X) hX (scaleSequence_succ J X)
  have hz : 0 ≤ c*(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^4) := by positivity [hx n]
  have he := one_le_exp hz
  have hQ : 1 ≤ (4+CMn+CHn)*exp (c*(scaleSequence J X n/((J-1+n : ℕ) : ℝ)^4)) := by
    linarith only [he,mul_nonneg hCMn (zero_le_one.trans he),mul_nonneg hCHn (zero_le_one.trans
        he)]
  have hM' := hMb.trans (mul_le_mul_of_nonneg_left
    (previousShear_le_normal J (by omega) X hbaseH n) hCM)
  exact badCost_bound J hJ Cθ CM CMn CHn c hCθ hCM hCMn hCHn (scaleSequence J X) hx n
    M A.hchild A.earlyRatio 1 P.horizon P.sigma A.child_nonneg A.earlyRatio_nonneg zero_le_one
    (zero_le_one.trans A.horizon_lower) A.sigma_pos hM' hchild hQ hTheta hSigma A.earlyRatio_bound

omit [CompleteSpace U] in
theorem upper_pressure_cost_bound (hdelta : A.δ ≤ spike J X n) :
    2*M*A.hchild*(A.δ*goodRatio+A.earlyRatio) ≤
      2*CM*goodRatio*goodCost J (scaleSequence J X) n +
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
    linarith only [mul_nonneg (by linarith only [hMone] : 0 ≤ 2*M-1)
      (mul_nonneg A.child_nonneg A.earlyRatio_nonneg)]
  exact add_le_add (hbase.trans hb) le_rfl

end EulerPacketSourceGeometry.ForwardGuards

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketInduction.Stage

open Set Real EulerSmoothLimit EulerParentPacketFrames EulerPacketSourceGeometry
  EulerTransverseFrameCoordinates EulerPacketInductionScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketSourceScales
  EulerPacketLowConstants EulerPacketPressureScale EulerPacketGeometryLowBounds
  EulerParentRenewalScale EulerParentNeighborThreshold EulerPacketSupport

section Joined

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} {n : ℕ} (P : Stage S n)
  (hn : n ≠ 0) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

local notation "G" => P.joinedGuards hn hq hB
local notation "R" => LinearIsometryEquiv.refl ℝ (referencePlane (P.joinedNormal hn))

theorem joined_horizon_bound :
    (P.joinedFrame hn).horizon ≤ sourceTheta S.J 4 (scaleSequence S.J S.X) n := by
  rw [P.joinedFrame_horizon,P.restrictedFrame_horizon]
  exact P.source_stage.horizon_le_Theta

include hn in
theorem history_inverse_shear : P.time⁻¹ ≤ previousShear S.J S.X n := by
  rw [← one_div]
  exact (div_le_iff₀ (P.time_pos hn)).mpr (P.history_layer hn)

theorem joined_bad_cost :
    2*(gradientConstant*previousShear S.J S.X n)*(G).hchild*(G).badRatio ≤
      badCost S.J 4 gradientConstant gradientConstant hessianConstant 80 (scaleSequence S.J S.X) n
          :=
  P.restrictedState.labels.joined_bad_pressure_cost_bound (P.joinedNormal hn) (P.joinedNormal_unit
      hn)
    R support compact P.restrictedLow P.time (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame
        hn)
    G P.time⁻¹ P.time_one le_rfl S.J S.D S.stage_large S.X 4 gradientConstant gradientConstant
    hessianConstant 80 S.x_one (by
        norm_num) gradient_nonneg gradient_nonneg hessian_nonneg (by norm_num)
    S.actual.initial_shear S.actual.initial_frequency n (gradientConstant*previousShear S.J S.X n)
    (by
        rw [rpow_ofNat]; exact P.label_eq.le) (P.history_inverse_shear hn) (P.joinedGuards_CM hn hq
            hB).le
    (P.joinedGuards_CH hn hq hB).le (P.joined_horizon_bound hn)
    (by
        erw [P.joinedFrame_sigma]; exact P.normalized_sigma) (P.joinedGuards_shear hn hq hB).le
            le_rfl

theorem joined_initial_cost :
    (G).hchild*(G).badRatio+(frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ initialIncrement S.J S.X n := by
  have hb := P.joined_bad_cost hn hq hB
  have hm : 1 ≤ 2*(gradientConstant*previousShear S.J S.X n) := by
    have h := mul_le_mul_of_nonneg_left (S.previousShear_one n) gradient_nonneg
    linarith only [gradient_properties.1,h]
  have hn0 := mul_nonneg (G).child_nonneg (G).badRatio_nonneg
  have hh := mul_le_mul_of_nonneg_right hm hn0
  unfold initialIncrement
  linarith only [hb,hh]

theorem joined_pressure_cost :
    2*(gradientConstant*previousShear S.J S.X n)*(G).hchild*((G).δ*goodRatio+(G).badRatio) +
      (frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ pressureIncrement S.J S.X n := by
  have h := P.restrictedState.labels.joined_upper_pressure_cost_bound
    (P.joinedNormal hn) (P.joinedNormal_unit hn) R support compact P.restrictedLow P.time
    (P.time_pos hn) P.time_lt_nextHorizon (P.joinedFrame hn) G P.time⁻¹ P.time_one le_rfl
    S.J S.D S.stage_large S.X 4 gradientConstant gradientConstant hessianConstant 80 S.x_one
    (by norm_num) gradient_nonneg gradient_nonneg hessian_nonneg (by norm_num)
    S.actual.initial_shear S.actual.initial_frequency n (gradientConstant*previousShear S.J S.X n)
    (by
        rw [rpow_ofNat]; exact P.label_eq.le) (P.history_inverse_shear hn) (P.joinedGuards_CM hn hq
            hB).le
    (P.joinedGuards_CH hn hq hB).le (P.joined_horizon_bound hn)
    (by erw [P.joinedFrame_sigma]; exact P.normalized_sigma)
    (P.joinedGuards_shear hn hq hB).le le_rfl (P.joinedGuards_delta hn hq hB).le
  unfold pressureIncrement initialIncrement
  exact (add_le_add h (le_refl ((frequency S.J S.X n)^(-(1/4 : ℝ))))).trans_eq
    (add_assoc _ _ _)

theorem joined_renewal_errors :
    (P.joinedGeometry hn hq hB).couplingError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X n ∧
    (P.joinedGeometry hn hq hB).tiltError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X n := by
  exact (G).renewal_errors_on_scales (by change (1/2 : ℝ) ≤ 1; norm_num)
    S.J S.D (by have h := S.stage_large; omega) 4 (q : ℝ) frameConstant S.X P.frame.a
    (by norm_num) frame_properties.1 S.x_one P.coupling_bounds.2 n (P.joinedFrame_a hn)
    ((P.joinedFrame_shear hn).trans P.frame_shear) (P.joined_horizon_bound hn)
    ((P.joinedFrame_G hn).le.trans P.frame_bound) ((P.joinedFrame_error hn).le.trans P.frame_error)
    (P.joined_source_neighbor hn hq hB) (P.joinedGuards_y hn hq hB)
    (by erw [P.joinedFrame_sigma]; exact P.tilt_upper)

end Joined

section Forward

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : Stage S 0)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)

local notation "G" => P.forwardGuards hq hB

theorem forward_horizon_bound : P.forwardFrame.horizon ≤ sourceTheta S.J 4 (scaleSequence S.J S.X)
    0 := by
  rw [P.forwardFrame_horizon,P.restrictedFrame_horizon]
  exact P.source_stage.horizon_le_Theta

theorem forward_bad_cost :
    2*(gradientConstant*previousShear S.J S.X 0)*(G).hchild*(G).earlyRatio ≤
      badCost S.J 4 gradientConstant gradientConstant hessianConstant 80 (scaleSequence S.J S.X) 0
          := by
  apply (G).bad_pressure_cost_bound S.J S.stage_large S.X 4 gradientConstant gradientConstant
    hessianConstant 80 S.x_one (by
        norm_num) gradient_nonneg gradient_nonneg hessian_nonneg (by norm_num)
    S.actual.initial_shear 0 (gradientConstant*previousShear S.J S.X 0) P.forward_horizon_bound
    _ le_rfl le_rfl
  rw [P.forwardFrame_sigma]
  exact P.normalized_sigma

theorem forward_initial_cost :
    (G).hchild*(G).earlyRatio+(frequency S.J S.X 0)^(-(1/4 : ℝ)) ≤ initialIncrement S.J S.X 0 := by
  have hb := P.forward_bad_cost hq hB
  have hm : 1 ≤ 2*(gradientConstant*previousShear S.J S.X 0) := by
    have h := mul_le_mul_of_nonneg_left (S.previousShear_one 0) gradient_nonneg
    linarith only [gradient_properties.1,h]
  have hn0 := mul_nonneg (G).child_nonneg (G).earlyRatio_nonneg
  have hh := mul_le_mul_of_nonneg_right hm hn0
  unfold initialIncrement
  linarith only [hb,hh]

theorem forward_pressure_cost :
    2*(gradientConstant*previousShear S.J S.X 0)*(G).hchild*((G).δ*goodRatio+(G).earlyRatio) +
      (frequency S.J S.X 0)^(-(1/4 : ℝ)) ≤ pressureIncrement S.J S.X 0 := by
  have h := (G).upper_pressure_cost_bound S.J S.stage_large S.X 4 gradientConstant gradientConstant
    hessianConstant 80 S.x_one (by
        norm_num) gradient_nonneg gradient_nonneg hessian_nonneg (by norm_num)
    S.actual.initial_shear 0 (gradientConstant*previousShear S.J S.X 0) P.forward_horizon_bound
    (by rw [P.forwardFrame_sigma]; exact P.normalized_sigma) le_rfl le_rfl le_rfl
  unfold pressureIncrement initialIncrement
  linarith only [h]

theorem forward_renewal_errors :
    (P.forwardGeometry hq hB).couplingError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X 0 ∧
    (P.forwardGeometry hq hB).tiltError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X 0 := by
  exact (G).renewal_errors_on_scales (by change (1/2 : ℝ) ≤ 1; norm_num)
    S.J S.D (by have h := S.stage_large; omega) 4 (q : ℝ) frameConstant S.X P.frame.a
    (by norm_num) frame_properties.1 S.x_one P.coupling_bounds.2 0 P.forwardFrame_a
    (P.forwardFrame_shear.trans P.frame_shear) P.forward_horizon_bound
    (P.forwardFrame_G.le.trans P.frame_bound) (P.forwardFrame_error.le.trans P.frame_error)
    (P.forward_source_neighbor hq hB) rfl (by rw [P.forwardFrame_sigma]; exact P.tilt_upper)

end Forward
end EulerPacketInduction.Stage

end
end

end

section

/-! The summable scalar budgets propagate the genuine low source
guards and absorb the absolute geometric errors. -/

@[expose] public section

noncomputable section

namespace EulerPacketInduction.Stage

open Set Finset Real EulerSmoothLimit EulerParentPacketFrames
  EulerBaseDatum EulerPacketInductionScales EulerPacketLowConstants
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence EulerPacketSourceScaleActual
  EulerPacketBaseGuardScales EulerPacketPressureScale EulerPacketGeometryLowBounds
  EulerParentRenewalScale EulerParentRenewalPrefix EulerMeanHarmonic

variable {c B : ℝ} {S : Scales c B} {n : ℕ} (P : Stage S n)

theorem initial_step_bound (e : ℝ) (he : e ≤ initialIncrement S.J S.X n) :
    P.low.Be+e ≤ initialCoefficientCost+∑ i ∈ range (n+1), initialIncrement S.J S.X i ∧
    P.low.Bc+e ≤ gradientConstant*S.X^1000+∑ i ∈ range (n+1), initialIncrement S.J S.X i := by
  rw [sum_range_succ]
  constructor <;> linarith only [P.exterior_bound,P.core_bound,he]

theorem pressure_step_bound (e : ℝ) (he : e ≤ pressureIncrement S.J S.X n) :
    P.low.K+e ≤ initialCoefficientCost+literalInitialPressureCost S.D S.X +
      ∑ i ∈ range (n+1), pressureIncrement S.J S.X i := by
  rw [sum_range_succ]
  linarith only [P.pressure_bound,he]

theorem next_localized (T ei ep : ℝ) (hT : 0 ≤ T) (hTcap : T ≤ baseHorizon S.J S.X)
    (hi0 : 0 ≤ ei) (hp0 : 0 ≤ ep)
    (hi : ei ≤ initialIncrement S.J S.X n) (hp : ep ≤ pressureIncrement S.J S.X n) :
    (P.low.K+ep)*(T^2/2)+(P.low.Be+ei)*T +
      boundaryLocalizationC2*(P.low.Bc+ei)*P.low.r^3*T ≤ 1/2 := by
  have hib := P.initial_step_bound ei hi
  have hpb := P.pressure_step_bound ep hp
  have his := S.initial_partial_sum (n+1)
  have hps := S.pressure_partial_sum (n+1)
  have hd := S.delta_small
  have hb := S.first.pressure_small
  rw [P.radius_eq]
  apply S.localized_guard T (P.low.K+ep) (P.low.Be+ei) (P.low.Bc+ei) hT
    (add_nonneg P.low.K_nonneg hp0) (add_nonneg P.low.Be_nonneg hi0)
    (add_nonneg P.low.Bc_nonneg hi0)
  · linarith only [hpb,hps,hd,hb]
  · linarith only [hib.1,his,hd]
  · linarith only [hib.2,his,hd]
  · exact hTcap

theorem ratio_absorption (r : ℝ) (hr : 0 ≤ r)
    (hbad : 2 * gradientConstant * previousShear S.J S.X n * shear S.J S.X n * r ≤
      badCost S.J 4 gradientConstant gradientConstant hessianConstant 80 (scaleSequence S.J S.X) n)
          :
    gradientConstant * previousShear S.J S.X n+shear S.J S.X n*(goodRatio+r) +
        (frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ gradientConstant*shear S.J S.X n ∧
    hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n +
      2 * gradientConstant*previousShear S.J S.X n * shear S.J S.X n*(goodRatio+r) +
        (frequency S.J S.X n)^(-(1/4 : ℝ)) ≤
      hessianConstant*shear S.J S.X n*previousShear S.J S.X n := by
  have hsum : badCost S.J 4 gradientConstant gradientConstant hessianConstant 80
      (scaleSequence S.J S.X) n+(frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ 1 := by
    have h := S.initial_series.term_le n
    change initialIncrement S.J S.X n ≤ _
    exact h.trans (by linarith only [S.delta_small])
  have hM : 1 ≤ 2*gradientConstant*previousShear S.J S.X n := by
    have h := mul_le_mul_of_nonneg_left (S.previousShear_one n) gradient_nonneg
    nlinarith only [gradient_properties.1,h]
  have hgrad : shear S.J S.X n*r ≤
      2*gradientConstant*previousShear S.J S.X n*shear S.J S.X n*r := by
    have h := mul_le_mul_of_nonneg_right hM (mul_nonneg (zero_le_one.trans (S.shear_one n)) hr)
    nlinarith only [h]
  have hg : shear S.J S.X n*r+(frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ 1 := by
    linarith only [hgrad,hbad,hsum]
  have hh : 2*gradientConstant*previousShear S.J S.X n*shear S.J S.X n*r +
      (frequency S.J S.X n)^(-(1/4 : ℝ)) ≤ 1 := by linarith only [hbad,hsum]
  exact ⟨EulerPacketLowBoundPropagation.gradient_bound _ _ _ _ _ _ gradient_properties.1
      (S.previousShear_one n) (S.shear_one n) (S.shear_separation n) gradient_properties.2.2 hg,
    EulerPacketLowBoundPropagation.hessian_bound _ _ _ _ _ _ _ _ hessian_properties.1
      (S.previousShear_one n) (S.shear_one n) (S.olderShear_le n) (S.shear_separation n)
      hessian_properties.2.2 hh⟩

theorem next_frame_bounds :
    1 ≤ frameConstant*(1+previousShear S.J S.X n) ∧
    gradientConstant*previousShear S.J S.X n ≤ frameConstant*(1+previousShear S.J S.X n) ∧
    (gradientConstant*previousShear S.J S.X n)^2 +
        hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n ≤
      (frameConstant*(1+previousShear S.J S.X n))^2 := by
  have hp := S.previousShear_one n
  have hp0 := zero_le_one.trans hp
  have hf0 := zero_le_one.trans frame_properties.1
  have hold := S.olderShear_le n
  have hcf := frame_properties.2.1
  have hCH := frame_properties.2.2
  refine ⟨one_le_mul_of_one_le_of_one_le frame_properties.1 (by linarith only [hp]),?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right hcf hp0).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hf0)
  · have h1 := mul_le_mul_of_nonneg_left hold (mul_nonneg hessian_nonneg hp0)
    have h2 := mul_le_mul_of_nonneg_right hCH (sq_nonneg (previousShear S.J S.X n))
    have h3 := mul_nonneg (sq_nonneg frameConstant)
      (show 0 ≤ 1+2*previousShear S.J S.X n by positivity)
    nlinarith only [h1,h2,h3]

theorem coupling_step (a : ℝ)
    (h : |a / P.frame.a - 1| ≤ renewalCost S.J S.D 4 c frameConstant S.X n) :
    |a-1| ≤ 2*∑ i ∈ range (n+1), renewalCost S.J S.D 4 c frameConstant S.X i := by
  have he := S.renewal_series.nonneg n
  have hd := relative_step_error P.coupling_pos P.coupling_bounds.2 he h
  have ht := abs_add_le (a-P.frame.a) (P.frame.a-1)
  rw [show a-P.frame.a+(P.frame.a-1)=a-1 by ring] at ht
  rw [sum_range_succ]
  linarith only [hd,ht,P.coupling_error]

theorem tilt_step (σ : ℝ)
    (h : |(scaleSequence S.J S.X (n + 1)) ^ 2 * σ ^ 2 - 1| ≤
      renewalCost S.J S.D 4 c frameConstant S.X n) :
    1/2 ≤ σ^2*(scaleSequence S.J S.X (n+1))^2 ∧
      σ^2*(scaleSequence S.J S.X (n + 1)) ^ 2 ≤ 2 := by
  have hh := abs_le.mp h
  have he := S.renewal_series.term_le n
  constructor <;> nlinarith only [hh.1,hh.2,he]

end EulerPacketInduction.Stage

namespace EulerParentPacketFrames.RenewalAtTarget

open InnerProductSpace EulerPacketMovingFrame EulerPacketSourceGeometry EulerPacketNormalizedPrimary

theorem background_compression_of_error_le_one
    {ι V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {D : EulerTransversePacketProvider.Data V} {G : PhysicalGeometryData ι}
    {P : ParentFrame D G.targetTime} (J : RenewalAtTarget G P) (e : ℝ) (he : e ≤ 1) :
    ⟪P.B G.targetTime (unit (P.m G.targetTime)),unit (P.m G.targetTime)⟫_ℝ+e < 0 := by
  rw [J.background_compression_eq]
  have hm := G.compression_margin he
  have hc := G.nextCompression_le
  linarith only [hm,hc]

end EulerParentPacketFrames.RenewalAtTarget

end
end

end

section

/-! The same geometrically selected correction supplies the actual
child's whole-horizon physical bounds and its next localized source guard. -/

section

/-! The actual initialized packet changes the initial velocity gradient
by the exponentially small early/history size plus its correction error.
These are the costs needed to preserve the localized source guards. -/

@[expose] public section

noncomputable section

namespace EulerPacketPhysicalLowBounds

open EulerSmoothLimit EulerPeriodicProfile

theorem norm_le_of_shear_error (V : Matrix) (amp δ θ ev size : ℝ) (r w : Space)
    (hamp : 0 ≤ amp) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsize : amp * (‖r‖ * ‖w‖) ≤ δ * size)
    (herr : ‖V - shearTerm amp (deriv (profile δ) θ) r w‖ ≤ ev) : ‖V‖ ≤ size+ev := by
  have hshear : ‖shearTerm amp (deriv (profile δ) θ) r w‖ ≤ size :=
    (shearTerm_norm_le amp _ δ r w hamp (profile_deriv_abs δ hδ hδ1 θ)).trans
      ((div_le_iff₀ hδ).2 (by nlinarith only [hsize]))
  have h := norm_of_remainder V 0 (shearTerm amp (deriv (profile δ) θ) r w) ev
    (by simpa only [sub_zero] using herr)
  simp only [norm_zero,zero_add] at h
  exact h.trans (add_le_add hshear le_rfl)

end EulerPacketPhysicalLowBounds

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerPacketSourceGeometry EulerPacketMovingFrame EulerPacketGeometryLowBounds
  EulerPacketPhysicalLowBounds EulerPacketPrimaryFactorization EulerPeriodicProfile
  EulerSpatialCutoffs EulerPacketTerminalDatum
open scoped ContDiff

variable {A : Parent} (E : Evolution A)

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower period A.T}
  (B : Budget period A.T_pos (correctionData (A.transverseData m hm J support hSupport) period κ hκ
      Z R))
  (residual : ApproximationResidual period A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) period κ hκ Z R))
  (k : ℝ) (hk : k * κ = 1)

section Joined

variable {τ : ℝ} {hτ : 0 < τ} {hτT : τ < A.T}
  {F : ParentFrame (A.transverseData m hm J support hSupport) τ}
  {H : HistoryData ((A.transverseData m hm J support hSupport).initial τ hτ hτT.le)}
  (G : Guards hτ hτT F H) (hball : (1 / 2 : ℝ) ≤ G.radius)
  (hs : tsupport innerCutoff ⊆ support) (hδ : 0 < G.δ) (hδ1 : G.δ ≤ 1)

include hk hδ hδ1 in
theorem exactPacket_bad_gradient_increment
    (ev ep : ℝ) (herr : E.SourceErrors m hm J support hSupport B residual k G hball hs ev ep)
    (t : Icc (0 : ℝ) A.T) (ht : scaledTime τ F.a F.epsilon t ≤ 1) (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (t,y)) x -
      fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ G.hchild*G.badRatio+ev := by
  rw [(E.exactPacket_derivative_split m hm J support hSupport B residual k hk t
      x).1,add_sub_cancel_left]
  apply norm_le_of_shear_error _ (G.primaryAmplitude hball) G.δ
    (k*⟪m,E.inverse.normalized t (A.ell⁻¹ • x)⟫_ℝ) ev (G.hchild*G.badRatio)
    ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t (A.ell⁻¹ •
        x)))
    (canonicalVelocity τ hτ hτT H G.terminal hs t (E.inverse.normalized t (A.ell⁻¹ • x)))
    (G.primaryAmplitude_nonneg hball) hδ hδ1
  · simpa only [mul_assoc] using G.bad_primary_size hball t ht (E.inverse.normalized t (A.ell⁻¹ •
      x)) hs
  · exact (herr t (A.ell⁻¹ • x)).1

include hk hδ hδ1 in
theorem exactPacket_initial_gradient_increment
    (ev ep : ℝ) (herr : E.SourceErrors m hm J support hSupport B residual k G hball hs ev ep)
    (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (0,y)) x -
      fderiv ℝ (fun y => E.velocity (0,y)) x‖ ≤ G.hchild*G.badRatio+ev := by
  apply E.exactPacket_bad_gradient_increment m hm J support hSupport B residual k hk G hball hs hδ
      hδ1 ev ep herr A.zeroTime _ x
  change (F.a/F.epsilon)*(0-τ) ≤ 1
  have h : (F.a/F.epsilon)*(0-τ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg G.a_pos.le G.epsilon_pos.le) (by linarith only [hτ])
  linarith only [h]

end Joined

section Forward

variable {F : ParentFrame (A.transverseData m hm J support hSupport) 0}
  (G : ForwardGuards F) (hball : (1 / 2 : ℝ) ≤ G.radius)
  (hδ : 0 < G.δ) (hδ1 : G.δ ≤ 1)

include hk hδ hδ1 in
theorem exactForwardPacket_early_gradient_increment
    (ev ep : ℝ) (herr : E.ForwardSourceErrors m hm J support hSupport B residual k G hball ev ep)
    (t : Icc (0 : ℝ) A.T) (ht : scaledTime 0 F.a F.epsilon t ≤ 1) (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (t,y)) x -
      fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ G.hchild*G.earlyRatio+ev := by
  rw [(E.exactPacket_derivative_split m hm J support hSupport B residual k hk t
      x).1,add_sub_cancel_left]
  apply norm_le_of_shear_error _ (G.primaryAmplitude hball) G.δ
    (k*⟪m,E.inverse.normalized t (A.ell⁻¹ • x)⟫_ℝ) ev (G.hchild*G.earlyRatio)
    ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t (A.ell⁻¹ •
        x)))
    (EulerPacketForwardFactorization.canonicalVelocity (A.transverseData m hm J support hSupport)
        G.initialCoordinate t (E.inverse.normalized t (A.ell⁻¹ • x)))
    (G.primaryAmplitude_nonneg hball) hδ hδ1
  · simpa only [mul_assoc] using G.early_primary_size hball t ht (E.inverse.normalized t (A.ell⁻¹ •
      x))
  · exact (herr t (A.ell⁻¹ • x)).1

include hk hδ hδ1 in
theorem exactForwardPacket_initial_gradient_increment
    (ev ep : ℝ) (herr : E.ForwardSourceErrors m hm J support hSupport B residual k G hball ev ep)
    (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
        E.velocity (0,y)) x -
      fderiv ℝ (fun y => E.velocity (0,y)) x‖ ≤ G.hchild*G.earlyRatio+ev := by
  apply E.exactForwardPacket_early_gradient_increment m hm J support hSupport B residual k hk G
      hball hδ hδ1 ev ep herr A.zeroTime _ x
  change (F.a/F.epsilon)*(0-0) ≤ 1
  norm_num

end Forward

end EulerParentPacketFrames.Evolution

end
end

end

section

/-! The next packet's localized lower initial-gradient bounds and upper
pressure bound are consequences of the exact physical estimates. The
radius stays fixed, and the boundary parameter has a canonical value. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace EulerSmoothLimit EulerMeanHarmonic
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow EulerPacketTerminalDatum EulerSpatialCutoffs
  EulerPacketSourceGeometry EulerPacketGeometryLowBounds

variable {A : Parent} (E : Evolution A)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower period A.T}
  (B : Budget period A.T_pos (correctionData (A.transverseData m hm J support hSupport) period κ hκ
      Z R))
  (residual : ApproximationResidual period A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) period κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field period A.T raw) (hV : Z = V.toFieldTower)
  (G : EulerPhysicalGraphFlowBounds.Data period A.T) (hG : G.A = B.liftedPacketCoefficient period V)
  (k : ℝ) (hk : k * κ = 1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

section Joined

variable {τ : ℝ} {hτ : 0 < τ} {hτT : τ < A.T}
  {F : ParentFrame (A.transverseData m hm J support hSupport) τ}
  {D : HistoryData ((A.transverseData m hm J support hSupport).initial τ hτ hτT.le)}
  (C : Guards hτ hτT F D) (hball : (1 / 2 : ℝ) ≤ C.radius)
  (hs : tsupport EulerSpatialCutoffs.innerCutoff ⊆ support) (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1)

/-- Joined child low bounds as an element of `LowBounds (A.child G k m hgraph nextEll hnext
hnext1)`. -/
def joinedChildLowBounds (H : LowBounds A) (ev ep CM CH : ℝ)
    (herr : E.SourceErrors m hm J support hSupport B residual k C hball hs ev ep)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t, y)) x‖ ≤ CM)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hsmall : (H.K + 2 * CM * C.hchild * (C.δ * goodRatio + C.badRatio) + ep) * (A.T ^ 2 / 2) +
      (H.Be + (C.hchild * C.badRatio + ev)) * A.T +
      boundaryLocalizationC2 * (H.Bc + (C.hchild * C.badRatio + ev)) * H.r ^ 3 * A.T ≤ 1 / 2) :
    LowBounds (A.child G k m hgraph nextEll hnext hnext1) := by
  have hev : 0 ≤ ev := (norm_nonneg _).trans (herr A.zeroTime 0).1
  have hep : 0 ≤ ep := (norm_nonneg _).trans (herr A.zeroTime 0).2
  have hCM0 : 0 ≤ CM := (norm_nonneg _).trans (hCM A.zeroTime 0)
  apply E.updateLowBounds
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1)
    H (C.hchild*C.badRatio+ev) (H.K+2*CM*C.hchild*(C.δ*goodRatio+C.badRatio)+ep)
  · exact add_nonneg (mul_nonneg C.child_nonneg C.badRatio_nonneg) hev
  · positivity [H.K_nonneg,C.child_nonneg,C.delta_nonneg,goodRatio_pos,C.badRatio_nonneg]
  · intro x
    exact E.exactPacket_initial_gradient_increment m hm J support hSupport B residual k hk
      C hball hs hδ hδ1 ev ep herr x
  · intro t x z
    let EC := E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1
    rw [← EC.pressure_hessian_eq_force]
    exact (E.exactPacket_whole_horizon_low_bounds m hm J support hSupport B residual k hk
      C hball hs hδ hδ1 ev ep CM CH H.K herr hCM hCH
      (E.force_quadratic_upper_of_lowBounds H) t x).2.2 z
  · exact hsmall

end Joined

section Forward

variable {F : ParentFrame (A.transverseData m hm J support hSupport) 0}
  (C : ForwardGuards F) (hball : (1 / 2 : ℝ) ≤ C.radius)
  (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1)

/-- Forward child low bounds as an element of `LowBounds (A.child G k m hgraph nextEll hnext
hnext1)`. -/
def forwardChildLowBounds (H : LowBounds A) (ev ep CM CH : ℝ)
    (herr : E.ForwardSourceErrors m hm J support hSupport B residual k C hball ev ep)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t, y)) x‖ ≤ CM)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hsmall : (H.K + 2 * CM * C.hchild * (C.δ * goodRatio + C.earlyRatio) + ep) * (A.T ^ 2 / 2) +
      (H.Be + (C.hchild * C.earlyRatio + ev)) * A.T +
      boundaryLocalizationC2 * (H.Bc + (C.hchild * C.earlyRatio + ev)) * H.r ^ 3 * A.T ≤ 1 / 2) :
    LowBounds (A.child G k m hgraph nextEll hnext hnext1) := by
  have hev : 0 ≤ ev := (norm_nonneg _).trans (herr A.zeroTime 0).1
  have hep : 0 ≤ ep := (norm_nonneg _).trans (herr A.zeroTime 0).2
  have hCM0 : 0 ≤ CM := (norm_nonneg _).trans (hCM A.zeroTime 0)
  apply E.updateLowBounds
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1)
    H (C.hchild*C.earlyRatio+ev) (H.K+2*CM*C.hchild*(C.δ*goodRatio+C.earlyRatio)+ep)
  · exact add_nonneg (mul_nonneg C.child_nonneg C.earlyRatio_nonneg) hev
  · positivity [H.K_nonneg,C.child_nonneg,C.delta_nonneg,goodRatio_pos,C.earlyRatio_nonneg]
  · intro x
    exact E.exactForwardPacket_initial_gradient_increment m hm J support hSupport B residual k hk
      C hball hδ hδ1 ev ep herr x
  · intro t x z
    let EC := E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1
    rw [← EC.pressure_hessian_eq_force]
    exact (E.exactForwardPacket_whole_horizon_low_bounds m hm J support hSupport B residual k hk
      C hball hδ hδ1 ev ep CM CH H.K herr hCM hCH
      (E.force_quadratic_upper_of_lowBounds H) t x).2.2 z
  · exact hsmall

end Forward

end EulerParentPacketFrames.Evolution

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.GeometryForwardChoice

open Set InnerProductSpace EulerSmoothLimit EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketGeometryLowBounds EulerMeanHarmonic

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : GeometryForwardInput U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)

/-- Low bounds as an element of `LowBounds F.parent`. -/
def lowBounds (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤
        CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (hsmall : (I.low.K + 2 * CM * I.geometry.hchild * (I.geometry.δ * goodRatio +
        I.geometry.earlyRatio) + k ^ (-(1 / 4 : ℝ))) * (I.parent.T ^ 2 / 2) + (I.low.Be +
        (I.geometry.hchild * I.geometry.earlyRatio + k ^ (-(1 / 4 : ℝ)))) * I.parent.T +
        boundaryLocalizationC2 * (I.low.Bc + (I.geometry.hchild * I.geometry.earlyRatio +
        k ^ (-(1 / 4 : ℝ)))) * I.low.r ^ 3 * I.parent.T ≤ 1 / 2) : LowBounds F.parent := by
  let res := forwardInitializedApproximationResidual I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement (truncation k) F.hn k hk.four
  let V := forwardInitializedNormalizedField I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha (truncation k) k
  exact S.evolution.forwardChildLowBounds I.normal I.normal_unit I.coordinates I.support
      I.support_compact
    F.Q res V rfl F.flow F.coefficient k (mul_inv_cancel₀ hk.pos.ne') F.graph nextEll hnext hnext1
    I.geometry I.halfBall I.delta_pos I.delta_le_one I.low
    (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) CM CH F.errors hCM hCH hsmall

theorem lowBounds_values (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤
        CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (hsmall : (I.low.K + 2 * CM * I.geometry.hchild * (I.geometry.δ * goodRatio +
        I.geometry.earlyRatio) + k ^ (-(1 / 4 : ℝ))) * (I.parent.T ^ 2 / 2) + (I.low.Be +
        (I.geometry.hchild * I.geometry.earlyRatio + k ^ (-(1 / 4 : ℝ)))) * I.parent.T +
        boundaryLocalizationC2 * (I.low.Bc + (I.geometry.hchild * I.geometry.earlyRatio +
        k ^ (-(1 / 4 : ℝ)))) * I.low.r ^ 3 * I.parent.T ≤ 1 / 2) :
    (F.lowBounds CM CH hCM hCH
        hsmall).Be=I.low.Be+(I.geometry.hchild * I.geometry.earlyRatio + k^(-(1 / 4 : ℝ))) ∧
    (F.lowBounds CM CH hCM hCH
        hsmall).Bc=I.low.Bc+(I.geometry.hchild*I.geometry.earlyRatio+k^(-(1/4 : ℝ))) ∧
    (F.lowBounds CM CH hCM hCH
        hsmall).K=I.low.K+2*CM*I.geometry.hchild*(I.geometry.δ*goodRatio+I.geometry.earlyRatio) +
      k^(-(1/4 : ℝ)) ∧
    (F.lowBounds CM CH hCM hCH hsmall).r=I.low.r ∧
    (F.lowBounds CM CH hCM hCH hsmall).L =
      boundaryLocalizationC1*(F.lowBounds CM CH hCM hCH hsmall).Bc+1 :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem physical_bounds (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support) (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤
        CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (t : Icc (0 : ℝ) I.parent.T) (x : Space) :
    ‖fderiv ℝ (fun y => (state I S k hk nextEll hnext hnext1 F hSym).evolution.velocity (t,y)) x‖ ≤
      CM+I.geometry.hchild*(goodRatio+I.geometry.earlyRatio)+k^(-(1/4 : ℝ)) ∧
    ‖fderiv ℝ ((state I S k hk nextEll hnext hnext1 F hSym).evolution.force t) x‖ ≤
      CH+2*CM*I.geometry.hchild*(goodRatio+I.geometry.earlyRatio)+k^(-(1/4 : ℝ)) := by
  let res := forwardInitializedApproximationResidual I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement (truncation k) F.hn k hk.four
  have h := S.evolution.exactForwardPacket_whole_horizon_low_bounds I.normal I.normal_unit
      I.coordinates
    I.support I.support_compact F.Q res k (mul_inv_cancel₀ hk.pos.ne') I.geometry I.halfBall
    I.delta_pos I.delta_le_one (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) CM CH I.low.K
    F.errors hCM hCH (S.evolution.force_quadratic_upper_of_lowBounds I.low) t x
  refine ⟨h.1,?_⟩
  erw [← (state I S k hk nextEll hnext hnext1 F hSym).evolution.pressure_hessian_eq_force]
  exact h.2.1

end EulerParentPacketFrames.GeometryForwardChoice

namespace EulerParentPacketFrames.GeometryJoinedChoice

open Set InnerProductSpace EulerSmoothLimit EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketGeometryLowBounds EulerMeanHarmonic

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : EulerPacketInitial.Input U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)

/-- Low bounds as an element of `LowBounds F.parent`. -/
def lowBounds (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤
        CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (hsmall : (I.low.K + 2 * CM * I.geometry.hchild * (I.geometry.δ * goodRatio +
        I.geometry.badRatio) + k ^ (-(1 / 4 : ℝ))) * (I.parent.T ^ 2 / 2) + (I.low.Be +
        (I.geometry.hchild * I.geometry.badRatio + k ^ (-(1 / 4 : ℝ)))) * I.parent.T +
        boundaryLocalizationC2 * (I.low.Bc + (I.geometry.hchild * I.geometry.badRatio + k ^
        (-(1 / 4 : ℝ)))) * I.low.r ^ 3 * I.parent.T ≤ 1 / 2) : LowBounds F.parent := by
  let res := initializedApproximationResidual I.meanData I.data rfl I.historyTime I.history_pos
      I.history_lt
    I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement (truncation
        k) F.hn k hk.four
  let V := initializedNormalizedField I.meanData I.data rfl I.historyTime I.history_pos
      I.history_lt I.history
    I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha (truncation k) k
  exact S.evolution.joinedChildLowBounds I.normal I.normal_unit I.coordinates I.support
      I.support_compact
    F.Q res V rfl F.flow F.coefficient k (mul_inv_cancel₀ hk.pos.ne') F.graph nextEll hnext hnext1
    I.geometry I.halfBall I.cutoff_support I.delta_pos I.delta_le_one I.low
    (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) CM CH F.errors hCM hCH hsmall

theorem lowBounds_values (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤
        CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (hsmall : (I.low.K + 2 * CM * I.geometry.hchild * (I.geometry.δ * goodRatio +
        I.geometry.badRatio) + k ^ (-(1 / 4 : ℝ))) * (I.parent.T ^ 2 / 2) + (I.low.Be +
        (I.geometry.hchild * I.geometry.badRatio + k ^ (-(1 / 4 : ℝ)))) * I.parent.T +
        boundaryLocalizationC2 * (I.low.Bc + (I.geometry.hchild * I.geometry.badRatio + k ^
        (-(1 / 4 : ℝ)))) * I.low.r ^ 3 * I.parent.T ≤ 1 / 2) :
    (F.lowBounds CM CH hCM hCH hsmall).Be=I.low.Be+(I.geometry.hchild*I.geometry.badRatio+k^(-(1/4
        : ℝ))) ∧
    (F.lowBounds CM CH hCM hCH hsmall).Bc=I.low.Bc+(I.geometry.hchild*I.geometry.badRatio+k^(-(1/4
        : ℝ))) ∧
    (F.lowBounds CM CH hCM hCH
        hsmall).K=I.low.K+2*CM*I.geometry.hchild*(I.geometry.δ*goodRatio+I.geometry.badRatio) +
      k^(-(1/4 : ℝ)) ∧
    (F.lowBounds CM CH hCM hCH hsmall).r=I.low.r ∧
    (F.lowBounds CM CH hCM hCH hsmall).L =
      boundaryLocalizationC1*(F.lowBounds CM CH hCM hCH hsmall).Bc+1 :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem physical_bounds (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support) (CM CH : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤
        CM)
    (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
    (t : Icc (0 : ℝ) I.parent.T) (x : Space) :
    ‖fderiv ℝ (fun y => (state I S k hk nextEll hnext hnext1 F hSym).evolution.velocity (t,y)) x‖ ≤
      CM+I.geometry.hchild*(goodRatio+I.geometry.badRatio)+k^(-(1/4 : ℝ)) ∧
    ‖fderiv ℝ ((state I S k hk nextEll hnext hnext1 F hSym).evolution.force t) x‖ ≤
      CH+2*CM*I.geometry.hchild*(goodRatio+I.geometry.badRatio)+k^(-(1/4 : ℝ)) := by
  let res := initializedApproximationResidual I.meanData I.data rfl I.historyTime I.history_pos
      I.history_lt
    I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement (truncation
        k) F.hn k hk.four
  have h := S.evolution.exactPacket_whole_horizon_low_bounds I.normal I.normal_unit I.coordinates
    I.support I.support_compact F.Q res k (mul_inv_cancel₀ hk.pos.ne') I.geometry I.halfBall
        I.cutoff_support
    I.delta_pos I.delta_le_one (k^(-(1/4 : ℝ))) (k^(-(1/4 : ℝ))) CM CH I.low.K
    F.errors hCM hCH (S.evolution.force_quadratic_upper_of_lowBounds I.low) t x
  refine ⟨h.1,?_⟩
  erw [← (state I S k hk nextEll hnext hnext1 F hSym).evolution.pressure_hessian_eq_force]
  exact h.2.1

end EulerParentPacketFrames.GeometryJoinedChoice

end
end

end

section

/-! Actual frame renewal for the very correction and flow chosen by
the geometric packet factories. Center source matching is derived. -/

section

/-! The geometric target of the actual forward or joined primary is the
activation time of the next parent frame. These factories are the checked
`SmoothState` renewals with the source-selected amplitude and primary;
all target matching is proved from their definitions. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.SmoothState

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerSpatialCutoffs EulerPeriodicProfile
  EulerPacketMovingFrame EulerPacketNormalizedPrimary

variable {A N : Parent} (S : SmoothState A) (T : SmoothState N) (hTime : N.T = A.T)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (mNext : Space) (hmNext : ‖mNext‖ = 1) (JNext : V ≃ₗᵢ[ℝ] referencePlane mNext)
  (supportNext : Set Space) (hSupportNext : IsCompact supportNext)

local notation "D" => A.transverseData m hm J support hSupport
local notation "DNext" => N.transverseData mNext hmNext JNext supportNext hSupportNext

section Forward

variable {P : ParentFrame (A.transverseData m hm J support hSupport) 0} (G : ForwardGuards P)
    (hball : (1 / 2 : ℝ) ≤ G.radius)

local notation "Geo" => ForwardGuards.lowGeometry G hball
local notation "tNext" => PhysicalGeometryData.targetTime (ForwardGuards.lowGeometry G hball)

variable (CM CH K error : ℝ) (hCM : 0 ≤ CM) (hK : 1 ≤ K) (he : 0 ≤ error)
  (hMK : CM ≤ K) (hHK : CM ^ 2 + CH ≤ K ^ 2)
  (hM : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerStrain t‖ ≤ CM)
  (hH : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerCurvature t‖ ≤ CH)
  (hδ : 0 < G.δ) (k : ℝ)
  (hsource : ∀ t : Icc (0 : ℝ) A.T, (G.lowGeometry hball).targetTime ≤ (t : ℝ) →
    ‖fderiv ℝ (S.velocityIncrement T t) 0 -
      (G.primaryAmplitude hball * deriv (profile G.δ)
        (k * ⟪m, S.evolution.inverse.normalized t 0⟫_ℝ)) •
        rankOne ℝ (EulerPacketForwardFactorization.canonicalVelocity
          (A.transverseData m hm J support hSupport) G.initialCoordinate t
              (S.evolution.inverse.normalized t 0))
          ((A.transverseData m hm J support hSupport).normal.field t
              (S.evolution.inverse.normalized t 0))‖ ≤ error)

/-- The next actual frame, using exactly the forward source primary and
its target-normalized amplitude. -/
def forwardTargetRenewal : ParentFrame DNext tNext :=
  S.forwardRenewal T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext
    tNext ((G.lowGeometry hball).target_time_mem).1 CM CH K error
    hCM hK he hMK hHK hM hH G.δ hδ (G.primaryAmplitude hball) k
    G.initialCoordinate G.initialCoordinate_ne_zero hsource

local notation "Q" => forwardTargetRenewal S T hTime m hm J support hSupport
  mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
  hCM hK he hMK hHK hM hH hδ k hsource

/-- In particular, the new ray and primary are the old source's actual
physical ray and primary at the target, not freely chosen frame vectors. -/
theorem forwardTargetRenewal_matches : RenewalAtTarget Geo Q := by
  let t : Icc (0 : ℝ) A.T := ⟨tNext,(G.lowGeometry hball).target_time_mem⟩
  constructor
  · change A.centerStrain t = (D).M.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_strain_eq m hm J support hSupport t).symm
  · change A.sourceNormal m t = (D).normal.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_normal_eq m hm J support hSupport t).symm
  · rfl
  · rfl

theorem forwardTargetRenewal_shear : (Q).shear=G.hchild :=
  (forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource).shear_eq hδ

theorem forwardTargetRenewal_constants : (Q).G=K ∧ (Q).error=error := ⟨rfl,rfl⟩

include hTime hCM hK he hMK hHK hM hH hδ hsource in
theorem forwardTargetRenewal_remainder (hT : tNext ≤ N.T) :
    ‖(DNext).M.field ((DNext).clamp tNext) 0-(Geo).M (Geo).center tNext -
      G.hchild • rankOne ℝ (unit ((Geo).w (Geo).center tNext))
        (unit ((Geo).r (Geo).center tNext))‖ ≤ error := by
  have H := forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact H.target_remainder hδ hT

theorem forwardTargetRenewal_parameters (hTilt : (Geo).tiltError ≤ 1 / 2) :
    (Q).shear=G.hchild ∧ 0 < (Q).a ∧
    |(Q).a/P.a-1| ≤ (Geo).couplingError ∧
    0 < (Q).sigma ∧
    |(G.y⁻¹)^2*(Q).sigma^2-1| ≤ (Geo).tiltError ∧
    1/2 ≤ (G.y⁻¹)^2*(Q).sigma^2 ∧ (G.y⁻¹)^2*(Q).sigma^2 ≤ 3/2 := by
  have H := forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact ⟨H.shear_eq hδ,H.coupling_pos,H.coupling_error,H.sigma_pos hTilt,
    H.tilt_error hTilt,H.tilt_interval hTilt⟩

theorem forwardTargetRenewal_compression
    (ht : 0 < tNext) (hT : tNext < N.T)
    (hmargin : 3 * ((Geo).G + (Geo).d) + error < (Geo).compressionScale) :
    ⟪(DNext).M.field ⟨tNext,ht.le,hT.le⟩ 0 (unit ((Q).m tNext)),
      unit ((Q).m tNext)⟫_ℝ < 0 := by
  have H := forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact H.activation_compression ht hT hmargin

theorem forwardTargetRenewal_compression_of_error_le_one
    (hT : tNext < N.T) (herror : error ≤ 1) :
    ⟪(DNext).M.field ⟨tNext,(Geo).targetTime_pos le_rfl |>.le,hT.le⟩ 0
      (unit ((Q).m tNext)),unit ((Q).m tNext)⟫_ℝ < 0 := by
  have H := forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact H.activation_compression_of_error_le_one ((Geo).targetTime_pos le_rfl) hT herror

end Forward

section Joined

variable (s : ℝ) (hs : 0 < s) (hsT : s < A.T)
  (H : HistoryData ((A.transverseData m hm J support hSupport).initial s hs hsT.le))
  {P : ParentFrame (A.transverseData m hm J support hSupport) s}
  (G : Guards hs hsT P H) (hball : (1 / 2 : ℝ) ≤ G.radius)
  (hcut : tsupport innerCutoff ⊆ support)

local notation "Geo" => Guards.lowGeometry G hball
local notation "tNext" => PhysicalGeometryData.targetTime (Guards.lowGeometry G hball)

variable (CM CH K error : ℝ) (hCM : 0 ≤ CM) (hK : 1 ≤ K) (he : 0 ≤ error)
  (hMK : CM ≤ K) (hHK : CM ^ 2 + CH ≤ K ^ 2)
  (hM : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerStrain t‖ ≤ CM)
  (hH : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerCurvature t‖ ≤ CH)
  (hδ : 0 < G.δ) (k : ℝ)
  (hsource : ∀ t : Icc (0 : ℝ) A.T, (G.lowGeometry hball).targetTime ≤ (t : ℝ) →
    ‖fderiv ℝ (S.velocityIncrement T t) 0 -
      (G.primaryAmplitude hball * deriv (profile G.δ)
        (k * ⟪m, S.evolution.inverse.normalized t 0⟫_ℝ)) •
        rankOne ℝ (EulerPacketPrimaryFactorization.canonicalVelocity
          s hs hsT H G.terminal hcut t (S.evolution.inverse.normalized t 0))
          ((A.transverseData m hm J support hSupport).normal.field t
              (S.evolution.inverse.normalized t 0))‖ ≤ error)

/-- The joined renewal retains the activation-selected endpoint and
its actual stationary-history initial trace. -/
def joinedTargetRenewal : ParentFrame DNext tNext :=
  S.joinedRenewal T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext
    tNext (hs.le.trans ((G.lowGeometry hball).target_time_mem).1) CM CH K error
    hCM hK he hMK hHK hM hH G.δ hδ (G.primaryAmplitude hball) k
    s hs hsT H G.terminal G.terminal_properties.1 hcut hsource

local notation "Q" => joinedTargetRenewal S T hTime m hm J support hSupport
  mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
  hCM hK he hMK hHK hM hH hδ k hsource

theorem joinedTargetRenewal_matches : RenewalAtTarget Geo Q := by
  let t : Icc (0 : ℝ) A.T :=
    ⟨tNext,hs.le.trans ((G.lowGeometry hball).target_time_mem).1,
      ((G.lowGeometry hball).target_time_mem).2⟩
  constructor
  · change A.centerStrain t = (D).M.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_strain_eq m hm J support hSupport t).symm
  · change A.sourceNormal m t = (D).normal.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_normal_eq m hm J support hSupport t).symm
  · rfl
  · rfl

theorem joinedTargetRenewal_shear : (Q).shear=G.hchild :=
  (joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource).shear_eq hδ

theorem joinedTargetRenewal_constants : (Q).G=K ∧ (Q).error=error := ⟨rfl,rfl⟩

include hTime hCM hK he hMK hHK hM hH hδ hsource in
theorem joinedTargetRenewal_remainder (hT : tNext ≤ N.T) :
    ‖(DNext).M.field ((DNext).clamp tNext) 0-(Geo).M (Geo).center tNext -
      G.hchild • rankOne ℝ (unit ((Geo).w (Geo).center tNext))
        (unit ((Geo).r (Geo).center tNext))‖ ≤ error := by
  have E := joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact E.target_remainder hδ hT

theorem joinedTargetRenewal_parameters (hTilt : (Geo).tiltError ≤ 1 / 2) :
    (Q).shear=G.hchild ∧ 0 < (Q).a ∧
    |(Q).a/P.a-1| ≤ (Geo).couplingError ∧
    0 < (Q).sigma ∧
    |(G.y⁻¹)^2*(Q).sigma^2-1| ≤ (Geo).tiltError ∧
    1/2 ≤ (G.y⁻¹)^2*(Q).sigma^2 ∧ (G.y⁻¹)^2*(Q).sigma^2 ≤ 3/2 := by
  have E := joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact ⟨E.shear_eq hδ,E.coupling_pos,E.coupling_error,E.sigma_pos hTilt,
    E.tilt_error hTilt,E.tilt_interval hTilt⟩

theorem joinedTargetRenewal_compression
    (ht : 0 < tNext) (hT : tNext < N.T)
    (hmargin : 3 * ((Geo).G + (Geo).d) + error < (Geo).compressionScale) :
    ⟪(DNext).M.field ⟨tNext,ht.le,hT.le⟩ 0 (unit ((Q).m tNext)),
      unit ((Q).m tNext)⟫_ℝ < 0 := by
  have E := joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact E.activation_compression ht hT hmargin

theorem joinedTargetRenewal_compression_of_error_le_one
    (hT : tNext < N.T) (herror : error ≤ 1) :
    ⟪(DNext).M.field ⟨tNext,(Geo).targetTime_pos hs.le |>.le,hT.le⟩ 0
      (unit ((Q).m tNext)),unit ((Q).m tNext)⟫_ℝ < 0 := by
  have E := joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact E.activation_compression_of_error_le_one ((Geo).targetTime_pos hs.le) hT herror

end Joined
end EulerParentPacketFrames.SmoothState

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set EulerSmoothLimit EulerVolterraConvolution

variable {A : Parent} (E : Evolution A)

theorem centerStrain_bound (CM : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t, y)) x‖ ≤ CM)
    (t : ℝ) : ‖A.centerStrain t‖ ≤ CM := by
  change ‖A.strain.field (projIcc 0 A.T A.T_pos.le t) 0‖ ≤ CM
  rw [E.strain_eq]
  exact hCM _ _

theorem centerCurvature_bound (CH : ℝ)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (t : ℝ) : ‖A.centerCurvature t‖ ≤ CH := by
  change ‖A.curvature.field (projIcc 0 A.T A.T_pos.le t) 0‖ ≤ CH
  rw [E.curvature_eq]
  exact hCH _ _

end EulerParentPacketFrames.Evolution

namespace EulerParentPacketFrames.GeometryForwardChoice

open Set Real InnerProductSpace EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketMovingFrame EulerPacketNormalizedPrimary

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : GeometryForwardInput U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)
  (CM CH K : ℝ) (hCM0 : 0 ≤ CM) (hK : 1 ≤ K) (hMK : CM ≤ K) (hHK : CM ^ 2 + CH ≤ K ^ 2)
  (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤ CM)
  (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m : Space) (hm : ‖m‖ = 1) (R : V ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)

/-- Renewal, constructed using `S.forwardTargetRenewal`. -/
def renewal : ParentFrame (F.parent.transverseData m hm R support hSupport)
    (I.geometry.lowGeometry I.halfBall).targetTime :=
  S.forwardTargetRenewal (state I S k hk nextEll hnext hnext1 F hSym) rfl
    I.normal I.normal_unit I.coordinates I.support I.support_compact
    m hm R support hSupport I.geometry I.halfBall CM CH K (k^(-(1/4 : ℝ)))
    hCM0 hK (rpow_nonneg hk.pos.le _) hMK hHK
    (fun t _ => S.evolution.centerStrain_bound CM hCM t)
    (fun t _ => S.evolution.centerCurvature_bound CH hCH t)
    I.delta_pos k (fun t _ => center_error I S k hk nextEll hnext hnext1 F hSym t)

local notation "Pnew" => F.renewal hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport

theorem renewal_matches : RenewalAtTarget (I.geometry.lowGeometry I.halfBall) Pnew := by
  unfold renewal
  apply SmoothState.forwardTargetRenewal_matches

theorem renewal_costs : (Pnew).G=K ∧ (Pnew).error=k^(-(1/4 : ℝ)) := ⟨rfl,rfl⟩

theorem renewal_parameters (hTilt : (I.geometry.lowGeometry I.halfBall).tiltError ≤ 1 / 2) :
    (Pnew).shear=I.geometry.hchild ∧ 0 < (Pnew).a ∧
    |(Pnew).a/I.frame.a-1| ≤ (I.geometry.lowGeometry I.halfBall).couplingError ∧
    0 < (Pnew).sigma ∧
    |(I.geometry.y⁻¹)^2*(Pnew).sigma^2-1| ≤ (I.geometry.lowGeometry I.halfBall).tiltError := by
  have H := F.renewal_matches hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport
  exact ⟨H.shear_eq I.delta_pos,H.coupling_pos,H.coupling_error,H.sigma_pos hTilt,H.tilt_error
      hTilt⟩

theorem renewal_compression (e : ℝ) (he : e ≤ 1) :
    ⟪(Pnew).B (I.geometry.lowGeometry I.halfBall).targetTime
      (unit ((Pnew).m (I.geometry.lowGeometry I.halfBall).targetTime)),
      unit ((Pnew).m (I.geometry.lowGeometry I.halfBall).targetTime)⟫_ℝ+e < 0 := by
  have H := F.renewal_matches hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport
  rw [H.background_compression_eq]
  have hm := (I.geometry.lowGeometry I.halfBall).compression_margin he
  have hc := (I.geometry.lowGeometry I.halfBall).nextCompression_le
  linarith only [hm,hc]

end EulerParentPacketFrames.GeometryForwardChoice

namespace EulerParentPacketFrames.GeometryJoinedChoice

open Set Real InnerProductSpace EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketMovingFrame EulerPacketNormalizedPrimary

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : EulerPacketInitial.Input U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)
  (CM CH K : ℝ) (hCM0 : 0 ≤ CM) (hK : 1 ≤ K) (hMK : CM ≤ K) (hHK : CM ^ 2 + CH ≤ K ^ 2)
  (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t, y)) x‖ ≤ CM)
  (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m : Space) (hm : ‖m‖ = 1) (R : V ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)

/-- Renewal, constructed using `S.joinedTargetRenewal`. -/
def renewal : ParentFrame (F.parent.transverseData m hm R support hSupport)
    (I.geometry.lowGeometry I.halfBall).targetTime :=
  S.joinedTargetRenewal (state I S k hk nextEll hnext hnext1 F hSym) rfl
    I.normal I.normal_unit I.coordinates I.support I.support_compact
    m hm R support hSupport I.historyTime I.history_pos I.history_lt I.history I.geometry I.halfBall
    I.cutoff_support CM CH K (k^(-(1/4 : ℝ)))
    hCM0 hK (rpow_nonneg hk.pos.le _) hMK hHK
    (fun t _ => S.evolution.centerStrain_bound CM hCM t)
    (fun t _ => S.evolution.centerCurvature_bound CH hCH t)
    I.delta_pos k (fun t _ => center_error I S k hk nextEll hnext hnext1 F hSym t)

local notation "Pnew" => F.renewal hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport

theorem renewal_matches : RenewalAtTarget (I.geometry.lowGeometry I.halfBall) Pnew := by
  unfold renewal
  apply SmoothState.joinedTargetRenewal_matches

theorem renewal_costs : (Pnew).G=K ∧ (Pnew).error=k^(-(1/4 : ℝ)) := ⟨rfl,rfl⟩

theorem renewal_parameters (hTilt : (I.geometry.lowGeometry I.halfBall).tiltError ≤ 1 / 2) :
    (Pnew).shear=I.geometry.hchild ∧ 0 < (Pnew).a ∧
    |(Pnew).a/I.frame.a-1| ≤ (I.geometry.lowGeometry I.halfBall).couplingError ∧
    0 < (Pnew).sigma ∧
    |(I.geometry.y⁻¹)^2*(Pnew).sigma^2-1| ≤ (I.geometry.lowGeometry I.halfBall).tiltError := by
  have H := F.renewal_matches hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport
  exact ⟨H.shear_eq I.delta_pos,H.coupling_pos,H.coupling_error,H.sigma_pos hTilt,H.tilt_error
      hTilt⟩

theorem renewal_compression (e : ℝ) (he : e ≤ 1) :
    ⟪(Pnew).B (I.geometry.lowGeometry I.halfBall).targetTime
      (unit ((Pnew).m (I.geometry.lowGeometry I.halfBall).targetTime)),
      unit ((Pnew).m (I.geometry.lowGeometry I.halfBall).targetTime)⟫_ℝ+e < 0 := by
  have H := F.renewal_matches hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport
  rw [H.background_compression_eq]
  have hm := (I.geometry.lowGeometry I.halfBall).compression_margin he
  have hc := (I.geometry.lowGeometry I.halfBall).nextCompression_le
  linarith only [hm,hc]

end EulerParentPacketFrames.GeometryJoinedChoice

end
end

end
