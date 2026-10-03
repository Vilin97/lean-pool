/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowRegularityCore
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSharpEstimate

/-! Quantitative regularity of the inverse flow in the §2 time window. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Construction

theorem Section2FlowInverseBounds.spatialGradient_snorm_le_time_scaled
    (f : Vec 2 → Vec 2) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    {Rsrc Rt Rbase C τ : ℝ}
    (hRsrc : 0 < Rsrc) (hRt : 0 < Rt) (hRbase : 0 < Rbase)
    (hC : 0 ≤ C) (hτ : 0 ≤ τ)
    (hRsrcBase : Rsrc ≤ (9 / 8) * Rbase)
    (hRratio : Rsrc / Rt ≤ 1 / 8)
    (hnext : FaaDiBruno.snorm f (n + 1) Rsrc ≤
      ENNReal.ofReal (16 * C * τ)) :
    FaaDiBruno.snorm (FaaDiBruno.spatialGradientMatrix f) n Rt ≤
      ENNReal.ofReal (8 * C * Rbase * τ) := by
  have hDnext := FaaDiBruno.derivativeSup_le_of_snorm_le f hRsrc hnext
  have hDgrad := FaaDiBruno.spatialGradientMatrix_derivativeSup_le f hf n
  have hDgrad' : FaaDiBruno.derivativeSup n
      (FaaDiBruno.spatialGradientMatrix f) ≤ ENNReal.ofReal
        (16 * C * τ * (n + 1).factorial * Rsrc ^ (n + 1) /
          (n + 2 : ℝ) ^ 2) := by
    have hDnext' : FaaDiBruno.derivativeSup (n + 1) f ≤ ENNReal.ofReal
        (16 * C * τ * (n + 1).factorial * Rsrc ^ (n + 1) /
          (n + 2 : ℝ) ^ 2) := by
      convert hDnext using 1
      congr 1
      push_cast
      ring
    exact hDgrad.trans hDnext'
  let q : ℝ := Rsrc / Rt
  let qbase : ℝ := Rsrc / Rbase
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqle : q ≤ 1 / 8 := by simpa [q] using hRratio
  have hqbase : 0 ≤ qbase := by dsimp [qbase]; positivity
  have hqbasele : qbase ≤ 9 / 8 := by
    dsimp [qbase]
    exact (div_le_iff₀ hRbase).2 (by simpa [mul_comm] using hRsrcBase)
  have hpoly : (n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2 ≤ (n + 1 : ℝ) := by
    have hsq : (n + 1 : ℝ) ^ 2 ≤ (n + 2 : ℝ) ^ 2 := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      exact pow_le_pow_left₀ (by linarith only [hn0]) (by linarith only) 2
    have hfrac : (n + 1 : ℝ) ^ 2 / (n + 2 : ℝ) ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      simpa using hsq
    calc
      (n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2 =
          (n + 1 : ℝ) * ((n + 1 : ℝ) ^ 2 / (n + 2 : ℝ) ^ 2) := by ring
      _ ≤ (n + 1 : ℝ) * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = n + 1 := by ring
  have hfactor : 2 *
      ((n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2 * q ^ n * qbase) ≤ 1 := by
    by_cases hn0 : n = 0
    · subst n
      norm_num [q, qbase]
      nlinarith [hqbasele]
    · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnat : ∀ k : ℕ, (k + 1 : ℝ) ≤ 2 ^ k := by
        intro k
        induction k with
        | zero => norm_num
        | succ k ih =>
            rw [pow_succ]
            push_cast
            have hk0 : 0 ≤ (k : ℝ) := by positivity
            nlinarith [ih, hk0]
      have hqpow : q ^ n ≤ (1 / 8 : ℝ) ^ n :=
        pow_le_pow_left₀ hq hqle n
      have hnatPow : (n + 1 : ℝ) * q ^ n ≤ 1 / 4 := by
        have hprod : (n + 1 : ℝ) * q ^ n ≤
            (2 : ℝ) ^ n * (1 / 8 : ℝ) ^ n :=
          mul_le_mul (hnat n) hqpow (by positivity) (by norm_num)
        have hpowEq : (2 : ℝ) ^ n * (1 / 8 : ℝ) ^ n =
            (1 / 4 : ℝ) ^ n := by
          rw [← mul_pow]
          norm_num
        have hsmallPow : (1 / 4 : ℝ) ^ n ≤ 1 / 4 := by
          have hnEq : n = (n - 1) + 1 := by omega
          rw [hnEq, pow_succ]
          have hbasePow : (1 / 4 : ℝ) ^ (n - 1) ≤ 1 :=
            pow_le_one₀ (by norm_num) (by norm_num)
          linarith only [mul_le_mul_of_nonneg_left hbasePow (by norm_num : 0 ≤ (1 / 4 : ℝ))]
        exact hprod.trans (hpowEq ▸ hsmallPow)
      have hpolyPow := mul_le_mul_of_nonneg_right hpoly (pow_nonneg hq n)
      have hpolyQnonneg : 0 ≤ (n + 1 : ℝ) * q ^ n := by positivity
      have hprodBound :
          (n + 1 : ℝ) * q ^ n * qbase ≤ (n + 1 : ℝ) * q ^ n * (9 / 8) := by
        exact mul_le_mul_of_nonneg_left hqbasele hpolyQnonneg
      have htotal :
          ((n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2) * q ^ n * qbase ≤
            (n + 1 : ℝ) * q ^ n * (9 / 8) := by
        calc
          _ ≤ (n + 1 : ℝ) * q ^ n * qbase := by
            exact mul_le_mul_of_nonneg_right hpolyPow hqbase
          _ ≤ _ := hprodBound
      have hlast := mul_le_mul_of_nonneg_right hnatPow (by norm_num : 0 ≤ (9 / 8 : ℝ))
      linarith [htotal, hlast]
  have hfac : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * n.factorial := by
    rw [Nat.factorial_succ]
    norm_cast
  let targetCoeff : ℝ := 8 * C * Rbase * τ * Rt ^ n * n.factorial /
    (n + 1 : ℝ) ^ 2
  have htargetCoeff : 0 ≤ targetCoeff := by
    dsimp [targetCoeff]
    positivity
  have hcoeffEq :
      16 * C * τ * (n + 1).factorial * Rsrc ^ (n + 1) /
          (n + 2 : ℝ) ^ 2 =
        targetCoeff * (2 *
          ((n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2 * q ^ n * qbase)) := by
    dsimp [targetCoeff, q, qbase]
    rw [hfac, div_pow]
    field_simp [ne_of_gt hRbase, ne_of_gt hRt,
      (by positivity : (n + 1 : ℝ) ≠ 0), (by positivity : (n + 2 : ℝ) ≠ 0)]
    ring
  have hcoeff :
      16 * C * τ * (n + 1).factorial * Rsrc ^ (n + 1) /
          (n + 2 : ℝ) ^ 2 ≤ targetCoeff := by
    rw [hcoeffEq]
    exact mul_le_of_le_one_right htargetCoeff hfactor
  have hDtarget : FaaDiBruno.derivativeSup n
      (FaaDiBruno.spatialGradientMatrix f) ≤ ENNReal.ofReal targetCoeff :=
    hDgrad'.trans (ENNReal.ofReal_le_ofReal hcoeff)
  have hsnorm := FaaDiBruno.snorm_le_of_derivativeSup_le
    (FaaDiBruno.spatialGradientMatrix f) hRt hDtarget
  simpa [targetCoeff, mul_assoc, mul_left_comm, mul_comm] using hsnorm

theorem Section2FlowInverseBounds.inverseFlowJacobian_snorm_from_transport
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (m n : ℕ) (hm : 1 ≤ m)
    (hcurrent : Section2StreamInductionHypothesis (Φ := Φ) R M m)
    (s t : ℝ)
    (ht : |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) :
    flowJacobianBarNorm n (2 ^ 11 * (epsilon β I.Λ m)⁻¹)
      (fun x => constructionFlowInvJacobian hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)) ≤
      ENNReal.ofReal (2 ^ 23 * |t| * a β I.Λ m) := by
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow hseq m
  let Rm : ℝ := R m
  let Mm : ℝ := M m
  let Cf : ℝ := Mm / Rm
  let Rtarget : ℝ := 2 ^ 11 * (epsilon β I.Λ m)⁻¹
  let Rsource : ℝ := FaaDiBruno.transportShiftRadius Cf Rm |t|
  have hRm : 0 < Rm := by dsimp [Rm]; exact section2_radius_pos hscales m
  have hMm : 0 < Mm := by dsimp [Mm]; exact section2_amplitude_pos hscales m
  have he : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have ha : 0 < a β I.Λ m :=
    Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  have hCfRm : Cf * Rm = Mm := by
    dsimp [Cf, Rm, Mm]
    exact div_mul_cancel₀ _ (ne_of_gt hRm)
  have hMbound : Mm ≤ 2 ^ 19 * a β I.Λ m := by
    dsimp [Mm]
    exact full_amplitude_recurrence_bound I.one_lt_beta I.beta_lt
      I.two_pow_seven_le R M hscales.radius_zero hscales.amplitude_zero
      hscales.radius_step hscales.amplitude_step m
  have hma : Mm * (a β I.Λ m)⁻¹ ≤ 2 ^ 19 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ ha).2
    dsimp [Mm] at hMbound
    linarith only [hMbound]
  have hMtime : Mm * |t| ≤ 1 / 64 := by
    calc
      Mm * |t| ≤ Mm * (2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) :=
        mul_le_mul_of_nonneg_left ht hMm.le
      _ = 2 ^ (-25 : ℤ) * (Mm * (a β I.Λ m)⁻¹) := by ring
      _ ≤ 2 ^ (-25 : ℤ) * 2 ^ 19 :=
        mul_le_mul_of_nonneg_left hma (by positivity)
      _ = 1 / 64 := by norm_num
  have hpaperTime : |t| ≤ 1 / (8 * Cf * Rm) := by
    apply (le_div_iff₀ (by positivity)).2
    calc
      |t| * (8 * Cf * Rm) = 8 * (Cf * Rm * |t|) := by ring
      _ = 8 * (Mm * |t|) := by rw [hCfRm]
      _ ≤ 8 * (1 / 64) := mul_le_mul_of_nonneg_left hMtime (by norm_num)
      _ ≤ 1 := by norm_num
  have hRsource : 0 < Rsource := by
    dsimp [Rsource]
    unfold FaaDiBruno.transportShiftRadius
    positivity
  have hRsourceBase : Rsource ≤ (9 / 8) * Rm := by
    dsimp [Rsource]
    rw [FaaDiBruno.transportShiftRadius]
    rw [show 8 * |t| * Cf * Rm ^ 2 = 8 * (Mm * |t|) * Rm by
      rw [← hCfRm]
      ring]
    have hfactor : 1 + 8 * (Mm * |t|) ≤ 9 / 8 := by linarith only [hMtime]
    calc
      Rm + 8 * (Mm * |t|) * Rm = Rm * (1 + 8 * (Mm * |t|)) := by ring
      _ ≤ Rm * (9 / 8) := mul_le_mul_of_nonneg_left hfactor hRm.le
      _ = (9 / 8) * Rm := by ring
  have hR131 : Rm ≤ 131 * (epsilon β I.Λ m)⁻¹ := by
    dsimp [Rm]
    have hr := radius_recurrence_bound I.one_lt_beta I.beta_lt
      I.two_pow_seven_le R hscales.radius_zero hscales.radius_step (m := m) hm
    simpa only [show (3 : ℝ) + (2 : ℝ) ^ 7 = 131 by norm_num] using hr
  have hRtarget : 0 < Rtarget := by dsimp [Rtarget]; positivity
  have hRratio : Rsource / Rtarget ≤ 1 / 8 := by
    apply (div_le_iff₀ hRtarget).2
    calc
      Rsource ≤ (9 / 8) * Rm := hRsourceBase
      _ ≤ (9 / 8) * (131 * (epsilon β I.Λ m)⁻¹) :=
        mul_le_mul_of_nonneg_left hR131 (by norm_num)
      _ ≤ (1 / 8) * Rtarget := by
        dsimp [Rtarget]
        have hinv : 0 ≤ (epsilon β I.Λ m)⁻¹ := inv_nonneg.mpr he.le
        linarith only [hinv]
  let bShift : ℝ → Vec 2 → Vec 2 := fun u y => b (s + u) y
  let gShift : ℝ → Vec 2 → Vec 2 := fun u y => -bShift u y
  let XShift : ℝ → Vec 2 → ℝ → Vec 2 :=
    fun u y r => X (s + u) y (s + r)
  have hφ := streamSeq_isAdmissible hseq m
  have hb : Infra.Flow.SmoothPeriodicField b := by
    dsimp [b]
    exact smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hbShift : Infra.Flow.SmoothPeriodicField bShift := by
    refine ⟨?_, ?_⟩
    · have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (s + p.1, p.2)) := by fun_prop
      change ContDiff ℝ (⊤ : ℕ∞)
        (Function.uncurry b ∘ fun p : ℝ × Vec 2 => (s + p.1, p.2))
      exact hb.smooth.comp hmap
    · intro k ell r y
      dsimp [bShift]
      simpa [add_assoc] using hb.periodic k ell (s + r) y
  have hgShift : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry gShift) := by
    convert contDiff_neg.comp hbShift.smooth using 1
    rfl
  have hXShift : IsFlow bShift XShift := by
    simpa [bShift, XShift] using constructionFlow_shift_isFlow hX s
  have hXjoint := constructionFlow_joint_smooth hseq m
  have hXShiftSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × Vec 2) × ℝ => XShift p.1.1 p.1.2 p.2) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (ℝ × Vec 2) × ℝ =>
          (s + p.1.1, p.1.2, s + p.2)) := by fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun p : ℝ × Vec 2 × ℝ =>
        constructionFlow hseq m p.1 p.2.1 p.2.2) ∘
        (fun p : (ℝ × Vec 2) × ℝ => (s + p.1.1, p.1.2, s + p.2)))
    exact hXjoint.comp hmap
  have hBfield : ∀ u k, 1 ≤ k → k ≤ n + 1 →
      FaaDiBruno.snorm (bShift u) k Rm ≤ ENNReal.ofReal Cf := by
    intro u k hk hkn
    have hs := section2_streamVel_snorm_bound (hseq := hseq)
      (hprev := hcurrent) (m := m) (n := k) hk hRm hMm (s + u)
    simpa [bShift, b, Rm, Mm, Cf] using hs
  have hGfield : ∀ u k, 1 ≤ k → k ≤ n + 1 →
      FaaDiBruno.snorm (gShift u) k Rm ≤ ENNReal.ofReal Cf := by
    intro u k hk hkn
    have hneg := snorm_neg_eq_vec (n := k) (R := Rm) (bShift u)
    calc
      FaaDiBruno.snorm (gShift u) k Rm =
          FaaDiBruno.snorm (bShift u) k Rm := by simpa [gShift] using hneg
      _ ≤ ENNReal.ofReal Cf := hBfield u k hk hkn
  have hY := FaaDiBruno.flow_inverse_displacement_isTransportSolution_of_jointSmooth
    hbShift hXShift hXShiftSmooth
  have hnext := FaaDiBruno.transportSolution_snorm_equalRadius_all
    (N := n + 1) hY hbShift.smooth hgShift hXShift hCf hCf.le hRm
    (fun u k hk hkn => hBfield u k hk hkn)
    (fun u k hk hkn => hGfield u k hk hkn)
    (n + 1) (by omega) (by omega) t hpaperTime
  let disp : Vec 2 → Vec 2 := fun y =>
    constructionFlowInv hseq m (s + t) y s - y
  have hInvSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec 2 => constructionFlowInv hseq m (s + t) y s) := by
    have hInvJoint := constructionFlowInv_joint_smooth hseq m
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => (s + t, (y, s))) := by fun_prop
    have h := hInvJoint.comp hmap
    simpa only [Function.comp_def] using h
  have hdispSmooth : ContDiff ℝ (⊤ : ℕ∞) disp := by
    dsimp [disp]
    exact hInvSmooth.sub contDiff_id
  have hdispNext : FaaDiBruno.snorm disp (n + 1) Rsource ≤
      ENNReal.ofReal (16 * Cf * |t|) := by
    simpa [disp, Rsource, constructionFlowInv, constructionFlow,
      AVenhance.flowInv, XShift, X] using hnext
  have hgrad := Section2FlowInverseBounds.spatialGradient_snorm_le_time_scaled disp hdispSmooth n
    hRsource hRtarget hRm hCf.le (abs_nonneg t) hRsourceBase hRratio hdispNext
  have hGradSmooth : ContDiff ℝ n
      (FaaDiBruno.spatialGradientMatrix disp) := by
    unfold FaaDiBruno.spatialGradientMatrix
    apply contDiff_pi.2
    intro i
    apply contDiff_pi.2
    intro j
    have hcolumn : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => fderiv ℝ disp y (FaaDiBruno.coordinateVector 2 j)) :=
      hdispSmooth.fderiv_right (by simp) |>.clm_apply contDiff_const
    exact (contDiff_apply ℝ ℝ i).comp (hcolumn.of_le (by simp))
  have hJfun : (fun y => constructionFlowInvJacobian hseq m t s y -
      ContinuousLinearMap.id ℝ (Vec 2)) =
      (fun y => fderiv ℝ disp y) := by
    funext y
    have hsub := fderiv_sub
      (hInvSmooth.differentiable (by simp) y) (differentiable_id y)
    change fderiv ℝ (fun z : Vec 2 => constructionFlowInv hseq m (s + t) z s) y -
      ContinuousLinearMap.id ℝ (Vec 2) = fderiv ℝ disp y
    rw [show disp = (fun z : Vec 2 => constructionFlowInv hseq m (s + t) z s) - id by
      funext z
      rfl]
    simpa [fderiv_id] using hsub.symm
  rw [hJfun]
  have hbound := flowJacobianBarNorm_le_spatialGradient_snorm disp n Rtarget
    (8 * Cf * Rm * |t|) hGradSmooth hgrad
  have htarget : 8 * Cf * Rm * |t| ≤ 2 ^ 23 * |t| * a β I.Λ m := by
    have hleft : 8 * Cf * Rm * |t| = 8 * (Cf * Rm) * |t| := by ring
    rw [hleft, hCfRm]
    calc
      8 * Mm * |t| ≤ 8 * (2 ^ 19 * a β I.Λ m) * |t| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMbound (by norm_num))
          (abs_nonneg t)
      _ = 2 ^ 22 * |t| * a β I.Λ m := by ring
      _ = 2 ^ 22 * (|t| * a β I.Λ m) := by ring
      _ ≤ 2 ^ 23 * (|t| * a β I.Λ m) :=
        mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg (abs_nonneg t) (Infra.Cutoff.a_pos
            I.one_lt_beta I.beta_lt I.two_pow_seven_le).le)
      _ = 2 ^ 23 * |t| * a β I.Λ m := by ring
  exact hbound.trans (ENNReal.ofReal_le_ofReal htarget)

/-- The exact `inverse_regbounds` field consumed by §2, obtained from the
previous-scale stream induction and the corrected equal-radius transport
estimate. -/
theorem section2_flow_inverse_regbounds_from_previous
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1)) :
    ∀ s t : ℝ, |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ,
      flowJacobianBarNorm n (2 ^ 11 * (epsilon β I.Λ m)⁻¹)
        (fun x => constructionFlowInvJacobian hseq m t s x -
          ContinuousLinearMap.id ℝ (Vec 2)) ≤
        ENNReal.ofReal (2 ^ 23 * |t| * a β I.Λ m) := by
  intro s t ht n
  exact Section2FlowInverseBounds.inverseFlowJacobian_snorm_from_transport hscales m n hm
    (section2_stream_induction_step hscales happB2 m hm hprev) s t ht

end AVenhance.Infra.Construction

end
