/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowRegularityCore

/-! Pointwise all-order spatial derivative bounds for the §2 flow. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Construction

theorem Section2FlowHigherDerivative.continuous_orderedPartial
    {n : ℕ} {f : Vec 2 → Vec 2} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (J : Fin n → Fin 2) :
    Continuous (fun x => FaaDiBruno.orderedPartial n f x J) := by
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  have hlift := FaaDiBruno.contDiff_liftVecOne hfN
  have hderiv : Continuous
      (fun z : FaaDiBruno.VecOne 2 =>
        iteratedFDeriv ℝ n (FaaDiBruno.liftVecOne f) z) :=
    continuous_iff_continuousAt.mpr fun z =>
      (hlift.contDiffAt).continuousAt_iteratedFDeriv (by simp)
  have heval : Continuous
      (fun z : FaaDiBruno.VecOne 2 =>
        iteratedFDeriv ℝ n (FaaDiBruno.liftVecOne f) z
          (fun j => FaaDiBruno.coordinateVectorOne 2 (J j))) := by
    fun_prop
  have hmap : Continuous (fun x : Vec 2 => WithLp.toLp 1 x) := by fun_prop
  change Continuous
    ((fun z : FaaDiBruno.VecOne 2 =>
      iteratedFDeriv ℝ n (FaaDiBruno.liftVecOne f) z
        (fun j => FaaDiBruno.coordinateVectorOne 2 (J j))) ∘
      (fun x : Vec 2 => WithLp.toLp 1 x))
  exact heval.comp hmap

theorem Section2FlowHigherDerivative.continuous_norm_le_of_ae_le_vecVolume
    {E : Type*} [NormedAddCommGroup E] {f : Vec 2 → E} {B : ℝ} (hf : Continuous f) (hB : 0 ≤ B)
    (h : ∀ᵐ x ∂(FaaDiBruno.vecVolume 2),
      ‖f x‖ₑ ≤ ENNReal.ofReal B) : ∀ x, ‖f x‖ ≤ B := by
  have hopenPos : (FaaDiBruno.vecVolume 2).IsOpenPosMeasure := by
    unfold FaaDiBruno.vecVolume
    infer_instance
  intro x
  by_contra hx
  have hx' : B < ‖f x‖ := lt_of_not_ge hx
  let U : Set (Vec 2) := {y | B < ‖f y‖}
  have hUopen : IsOpen U := isOpen_lt continuous_const (Continuous.norm hf)
  have hUnonempty : U.Nonempty := ⟨x, hx'⟩
  have hUpos : 0 < (FaaDiBruno.vecVolume 2) U :=
    (hopenPos.open_pos U hUopen hUnonempty).bot_lt
  have hnotU : ∀ᵐ y ∂(FaaDiBruno.vecVolume 2), y ∉ U := by
    filter_upwards [h] with y hy
    intro hyU
    have hle : ENNReal.ofReal ‖f y‖ ≤ ENNReal.ofReal B := by
      simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using hy
    exact (not_lt_of_ge ((ENNReal.ofReal_le_ofReal_iff hB).mp hle)) hyU
  have hUzero : (FaaDiBruno.vecVolume 2) U = 0 := by
    simpa [ae_iff] using hnotU
  exact (ne_of_gt hUpos) hUzero

theorem Section2FlowHigherDerivative.continuousVector_norm_le_of_ae_le
    {f : Vec 2 → Vec 2} {B : ℝ} (hf : Continuous f) (hB : 0 ≤ B)
    (h : ∀ᵐ x ∂(FaaDiBruno.vecVolume 2),
      ‖f x‖ₑ ≤ ENNReal.ofReal B) : ∀ x, ‖f x‖ ≤ B := by
  have hcoord : ∀ i : Fin 2, ∀ x, ‖f x i‖ ≤ B := by
    intro i
    apply Section2FlowHigherDerivative.continuous_norm_le_of_ae_le_vecVolume
      (continuous_apply i |>.comp hf) hB
    filter_upwards [h] with x hx
    have hnorm : ‖f x i‖ ≤ ‖f x‖ := norm_le_pi_norm (f x) i
    have hcomponent : ‖f x i‖ₑ ≤ ‖f x‖ₑ := by
      simpa [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hnorm
    exact hcomponent.trans hx
  intro x
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  exact hcoord i x

theorem Section2FlowHigherDerivative.orderedPartial_pointwise_of_snorm
    {n : ℕ} {f : Vec 2 → Vec 2} {R C : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hR : 0 < R) (hC : 0 ≤ C)
    (hs : FaaDiBruno.snorm f n R ≤ ENNReal.ofReal C)
    (J : Fin n → Fin 2) (x : Vec 2) :
    ‖FaaDiBruno.orderedPartial n f x J‖ ≤
      C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 := by
  have hderiv := FaaDiBruno.derivativeSup_le_of_snorm_le f hR hs
  have hpartial : FaaDiBruno.partialSup n f J ≤ ENNReal.ofReal
      (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) :=
    (le_iSup_of_le J le_rfl).trans hderiv
  have hess : eLpNormEssSup (fun y => FaaDiBruno.orderedPartial n f y J)
      (FaaDiBruno.vecVolume 2) ≤ ENNReal.ofReal
        (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) := by
    simpa [FaaDiBruno.partialSup] using hpartial
  have hae : ∀ᵐ y ∂(FaaDiBruno.vecVolume 2),
      ‖FaaDiBruno.orderedPartial n f y J‖ₑ ≤ ENNReal.ofReal
        (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) :=
    (ae_le_eLpNormEssSup
      (f := fun y => FaaDiBruno.orderedPartial n f y J)
      (μ := FaaDiBruno.vecVolume 2)).mono fun y hy => hy.trans hess
  have hboundNonneg : 0 ≤ C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (by positivity))
      (by positivity)
  have hpoint := Section2FlowHigherDerivative.continuousVector_norm_le_of_ae_le
    (B := C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2)
    (Section2FlowHigherDerivative.continuous_orderedPartial hf J) hboundNonneg hae
  exact hpoint x

theorem Section2FlowHigherDerivative.orderedPartial_eq_iteratedFDeriv
    {n : ℕ} {f : Vec 2 → Vec 2} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : Vec 2) (J : Fin n → Fin 2) :
    FaaDiBruno.orderedPartial n f x J =
      iteratedFDeriv ℝ n f x (fun j => basisVec (J j)) := by
  unfold FaaDiBruno.orderedPartial FaaDiBruno.liftVecOne
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  change iteratedFDeriv ℝ n
      (f ∘ (FaaDiBruno.vecOneEquiv 2).toContinuousLinearMap)
      (WithLp.toLp 1 x)
      (fun j => FaaDiBruno.coordinateVectorOne 2 (J j)) = _
  rw [(FaaDiBruno.vecOneEquiv 2).toContinuousLinearMap.iteratedFDeriv_comp_right
    hfN (WithLp.toLp 1 x) le_rfl]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    FaaDiBruno.vecOneEquiv, FaaDiBruno.coordinateVectorOne,
    Homogenization.basisVec,
    PiLp.coe_continuousLinearEquiv]

private theorem section2_flow_higher_derivative_from_current_induction_branch1 :
  ∀ {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ} {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ} (m
      n : ℕ),
    1 ≤ n →
      ∀ (s t : ℝ) (x : Vec 2) (J : Fin n → Fin 2),
        let Rm : ℝ := R m;
        let Mm : ℝ := M m;
        let Cf : ℝ := Mm / Rm;
        0 < Rm →
          0 < Mm →
            let f : Vec 2 → Vec 2 := fun y => constructionFlow hseq m (s + t) y s;
            ContDiff ℝ ∞ f →
              let Rflow : ℝ := 16 * Rm * (1 + 16 * Cf * Rm * |t|);
              let Rtarget : ℝ := 2 ^ 14 * (epsilon β I.Λ m)⁻¹;
              let Cflow : ℝ := FaaDiBruno.flowHalfBinomialCoeff (n - 1) / (2 * Rm);
              FaaDiBruno.snorm f n Rflow ≤ ENNReal.ofReal Cflow →
                0 < Rflow →
                  Rflow ≤ 20 * Rm →
                    Rflow ≤ Rtarget →
                      ¬n = 1 →
                        ‖(iteratedFDeriv ℝ n (fun (y : Vec 2) => constructionFlow hseq m (s + t) y
                            s) x)
                              fun (k : Fin n) => basisVec (J k)‖ ≤
                          2 * ↑n.factorial * (2 ^ 14 * (epsilon β I.Λ m)⁻¹) ^ (n - 1)
    := by
  intro β I Φ hseq R M m n hn s t x J Rm Mm Cf hRm hMm f hf Rflow Rtarget Cflow hflowSnorm
      hRflowPositive hRflow20 hRflowTarget hn1
  have hn2 : 2 ≤ n := by omega
  have hpoint := Section2FlowHigherDerivative.orderedPartial_pointwise_of_snorm hf hRflowPositive
    (div_nonneg (FaaDiBruno.flowHalfBinomialCoeff_nonneg
      (by omega : 1 ≤ n - 1)) (by positivity)) hflowSnorm J x
  have hcoeff : FaaDiBruno.flowHalfBinomialCoeff (n - 1) ≤ 1 := by
    have hsmall := FaaDiBruno.flowHalfBinomialCoeff_le_inverse
      (n := n - 1) (by omega : 1 ≤ n - 1)
    have hnReal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hnSub : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      exact_mod_cast (show n - 1 + 1 = n by omega)
    have hsmall' : FaaDiBruno.flowHalfBinomialCoeff (n - 1) ≤
        1 / (4 * (n : ℝ)) := by
      simpa [hnSub] using hsmall
    have hfrac : (1 : ℝ) / (4 * (n : ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      linarith only [hnReal]
    exact hsmall'.trans hfrac
  have hCflowRflow : Cflow * Rflow ≤ 10 := by
    dsimp [Cflow]
    calc
      (FaaDiBruno.flowHalfBinomialCoeff (n - 1) / (2 * Rm)) * Rflow ≤
          (1 / (2 * Rm)) * Rflow := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hRflowPositive)
            exact (div_le_div_of_nonneg_right hcoeff (by positivity))
      _ = Rflow / (2 * Rm) := by ring
      _ ≤ 10 := (div_le_iff₀ (by positivity)).2 (by linarith only [hRflow20])
  have hcoefRadius : Cflow * Rflow / (n + 1 : ℝ) ^ 2 ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).2
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hden : 9 ≤ (n + 1 : ℝ) ^ 2 :=
      le_trans (by norm_num)
        (pow_le_pow_left₀ (by norm_num) (by linarith only [hnR] : (3 : ℝ) ≤ n + 1) 2)
    linarith only [hCflowRflow, hden]
  have hpow : Rflow ^ (n - 1) ≤ Rtarget ^ (n - 1) :=
    pow_le_pow_left₀ hRflowPositive.le hRflowTarget (n - 1)
  have htargetBound : Cflow * n.factorial * Rflow ^ n / (n + 1 : ℝ) ^ 2 ≤
      2 * n.factorial * Rtarget ^ (n - 1) := by
    have hpowN : Rflow ^ n = Rflow ^ (n - 1) * Rflow := by
      calc
        Rflow ^ n = Rflow ^ ((n - 1) + 1) := by congr 1; omega
        _ = Rflow ^ (n - 1) * Rflow := by rw [pow_succ]
    calc
      Cflow * n.factorial * Rflow ^ n /
          (n + 1 : ℝ) ^ 2 =
        Cflow * n.factorial * (Rflow ^ (n - 1) * Rflow) /
          (n + 1 : ℝ) ^ 2 := by rw [hpowN]
      _ = (Cflow * Rflow / (n + 1 : ℝ) ^ 2) *
          (n.factorial * Rflow ^ (n - 1)) := by ring
      _ ≤ 2 * (n.factorial * Rtarget ^ (n - 1)) := by
        apply mul_le_mul hcoefRadius
        · exact mul_le_mul_of_nonneg_left hpow (by positivity)
        · positivity
        · norm_num
      _ = 2 * n.factorial * Rtarget ^ (n - 1) := by ring
  rw [← Section2FlowHigherDerivative.orderedPartial_eq_iteratedFDeriv hf x J]
  exact hpoint.trans htargetBound

theorem Section2FlowHigherDerivative.section2_flow_higher_derivative_from_current_induction
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ} (hscales : Section2Scales I R M)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hcurrent : Section2StreamInductionHypothesis (Φ := Φ) R M m)
    (s t : ℝ) (ht : |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹)
    (x : Vec 2) (J : Fin n → Fin 2)
    (hclose : ‖constructionFlowJacobian hseq m t s x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 2 ^ 23 * |t| * a β I.Λ m ∧
      2 ^ 23 * |t| * a β I.Λ m ≤ 1 / 4) :
    ‖iteratedFDeriv ℝ n (fun y : Vec 2 =>
        constructionFlow hseq m (s + t) y s) x
        (fun k => basisVec (J k))‖ ≤
      2 * n.factorial *
        (2 ^ 14 * (epsilon β I.Λ m)⁻¹) ^ (n - 1) := by
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow hseq m
  let Rm : ℝ := R m
  let Mm : ℝ := M m
  let Cf : ℝ := Mm / Rm
  have hRm : 0 < Rm := by dsimp [Rm]; exact section2_radius_pos hscales m
  have hMm : 0 < Mm := by dsimp [Mm]; exact section2_amplitude_pos hscales m
  have he : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  have hMbound : Mm ≤ 2 ^ 19 * a β I.Λ m := by
    dsimp [Mm]
    exact full_amplitude_recurrence_bound I.one_lt_beta I.beta_lt
      I.two_pow_seven_le R M hscales.radius_zero hscales.amplitude_zero
      hscales.radius_step hscales.amplitude_step m
  have hma : Mm * (a β I.Λ m)⁻¹ ≤ 2 ^ 19 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le)).2
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
  have hCfRm : Cf * Rm = Mm := by
    dsimp [Cf, Rm, Mm]
    exact div_mul_cancel₀ _ (ne_of_gt hRm)
  have hpaperTime : |t| ≤ 1 / (8 * Cf * Rm) := by
    apply (le_div_iff₀ (by positivity)).2
    calc
      |t| * (8 * Cf * Rm) = 8 * (Cf * Rm * |t|) := by ring
      _ = 8 * (Mm * |t|) := by rw [hCfRm]
      _ ≤ 8 * (1 / 64) := mul_le_mul_of_nonneg_left hMtime (by norm_num)
      _ ≤ 1 := by norm_num
  have hφ := streamSeq_isAdmissible hseq m
  have hb : Infra.Flow.SmoothPeriodicField b := by
    dsimp [b]
    exact smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  let bShift : ℝ → Vec 2 → Vec 2 := fun u y => b (s + u) y
  let XShift : ℝ → Vec 2 → ℝ → Vec 2 :=
    fun u y r => X (s + u) y (s + r)
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
  have hBfield : ∀ u k, 1 ≤ k → k ≤ n →
      FaaDiBruno.snorm (bShift u) k Rm ≤ ENNReal.ofReal Cf := by
    intro u k hk hkn
    have hs := section2_streamVel_snorm_bound (hseq := hseq)
      (hprev := hcurrent) (m := m) (n := k) hk hRm hMm (s + u)
    simpa [bShift, b, Rm, Mm, Cf] using hs
  let f : Vec 2 → Vec 2 := fun y => constructionFlow hseq m (s + t) y s
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => (s + t, y, s)) := by fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun p : ℝ × Vec 2 × ℝ =>
        constructionFlow hseq m p.1 p.2.1 p.2.2) ∘
        (fun y : Vec 2 => (s + t, y, s)))
    exact hXjoint.comp hmap
  have hDn := FaaDiBruno.flow_spatialDn_snorm_smallTime
    (N := n) (by omega) hbShift hXShift hXShiftSmooth hCf hRm hBfield
    (t := t) hpaperTime n hn (by rfl)
  let Rflow : ℝ := 16 * Rm * (1 + 16 * Cf * Rm * |t|)
  let Rtarget : ℝ := 2 ^ 14 * (epsilon β I.Λ m)⁻¹
  let Cflow : ℝ := FaaDiBruno.flowHalfBinomialCoeff (n - 1) / (2 * Rm)
  have hRflowDef : (8 : ℝ) * 2 * Rm *
      (1 + (8 * 2 * Cf * Rm) * |t|) = Rflow := by
    dsimp [Rflow]
    ring
  have hflowSnorm : FaaDiBruno.snorm f n Rflow ≤ ENNReal.ofReal Cflow := by
    have hDnR := hDn
    rw [hRflowDef] at hDnR
    simpa [f, XShift, X, constructionFlow, Cflow] using hDnR
  have hRflowPositive : 0 < Rflow := by dsimp [Rflow]; positivity
  have hfactor : 1 + 16 * Cf * Rm * |t| ≤ 5 / 4 := by
    rw [show 16 * Cf * Rm * |t| = 16 * (Mm * |t|) by rw [← hCfRm]; ring]
    linarith only [hMtime]
  have hRflow20 : Rflow ≤ 20 * Rm := by
    dsimp [Rflow]
    calc
      16 * Rm * (1 + 16 * Cf * Rm * |t|) ≤ 16 * Rm * (5 / 4) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = 20 * Rm := by ring
  have hR131 : Rm ≤ 131 * (epsilon β I.Λ m)⁻¹ := by
    dsimp [Rm]
    have hr := radius_recurrence_bound I.one_lt_beta I.beta_lt
      I.two_pow_seven_le R hscales.radius_zero hscales.radius_step (m := m) hm
    simpa only [show (3 : ℝ) + (2 : ℝ) ^ 7 = 131 by norm_num] using hr
  have hRtargetPositive : 0 < Rtarget := by dsimp [Rtarget]; positivity
  have hRflowTarget : Rflow ≤ Rtarget := by
    dsimp [Rtarget]
    calc
      Rflow ≤ 20 * Rm := hRflow20
      _ ≤ 20 * (131 * (epsilon β I.Λ m)⁻¹) :=
        mul_le_mul_of_nonneg_left hR131 (by norm_num)
      _ = 2620 * (epsilon β I.Λ m)⁻¹ := by ring
      _ ≤ 2 ^ 14 * (epsilon β I.Λ m)⁻¹ :=
        mul_le_mul_of_nonneg_right (by norm_num)
          (inv_nonneg.mpr he.le)
  by_cases hn1 : n = 1
  · subst n
    have hdev : ‖constructionFlowJacobian hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 / 4 := hclose.1.trans hclose.2
    have hidnorm : ‖ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 := by simp
    have hJnorm : ‖constructionFlowJacobian hseq m t s x‖ ≤ 2 := by
      have hdecomp : constructionFlowJacobian hseq m t s x =
          (constructionFlowJacobian hseq m t s x -
            ContinuousLinearMap.id ℝ (Vec 2)) +
              ContinuousLinearMap.id ℝ (Vec 2) := by abel
      rw [hdecomp]
      calc
        ‖(constructionFlowJacobian hseq m t s x -
            ContinuousLinearMap.id ℝ (Vec 2)) +
              ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
            ‖constructionFlowJacobian hseq m t s x -
              ContinuousLinearMap.id ℝ (Vec 2)‖ +
                ‖ContinuousLinearMap.id ℝ (Vec 2)‖ := norm_add_le _ _
        _ ≤ 1 / 4 + 1 := add_le_add hdev hidnorm
        _ ≤ 2 := by norm_num
    have hbasis : ‖basisVec (J 0)‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonempty]
      intro i
      by_cases hi : i = J 0
      · simp [Homogenization.basisVec, hi]
      · simp [Homogenization.basisVec, hi]
    rw [iteratedFDeriv_one_apply]
    have hderiv : fderiv ℝ
        (fun y : Vec 2 => constructionFlow hseq m (s + t) y s) x =
        constructionFlowJacobian hseq m t s x := rfl
    rw [hderiv]
    calc
      ‖constructionFlowJacobian hseq m t s x (basisVec (J 0))‖ ≤
          ‖constructionFlowJacobian hseq m t s x‖ * ‖basisVec (J 0)‖ :=
        (constructionFlowJacobian hseq m t s x).le_opNorm _
      _ ≤ 2 * 1 := mul_le_mul hJnorm hbasis (norm_nonneg _) (by norm_num)
      _ = 2 * Nat.factorial 1 * Rtarget ^ (1 - 1) := by norm_num
  · exact @section2_flow_higher_derivative_from_current_induction_branch1 β I Φ hseq R M m n hn s
      t x J hRm hMm hf hflowSnorm hRflowPositive hRflow20 hRflowTarget hn1
/-- `flow_higher_derivative` in `Section2FlowBoundsAtScale`, derived from the
previous scale and the all-order signed-time `p.ODE.flow.2` estimate. -/
theorem section2_flow_higher_derivative_from_previous
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M)
    (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n)
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1))
    (s t : ℝ) (ht : |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹)
    (x : Vec 2) (J : Fin n → Fin 2) :
    ‖iteratedFDeriv ℝ n (fun y : Vec 2 =>
        constructionFlow hseq m (s + t) y s) x
        (fun k => basisVec (J k))‖ ≤
      2 * n.factorial * (2 ^ 14 * (epsilon β I.Λ m)⁻¹) ^ (n - 1) := by
  exact Section2FlowHigherDerivative.section2_flow_higher_derivative_from_current_induction
      hscales m n hm hn
    (section2_stream_induction_step hscales happB2 m hm hprev) s t ht x J
    (section2_flow_close_from_previous hscales happB2 m hm hprev s t ht x)

end AVenhance.Infra.Construction

end
