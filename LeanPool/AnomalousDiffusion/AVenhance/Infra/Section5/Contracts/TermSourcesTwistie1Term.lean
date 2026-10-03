/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1Decomp
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1Pointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsCentered

/-! # One term of the `twistie1` ergodic estimate

For `ξ_{m,k}(t) ≠ 0` and a component `j`, the centered `HDot⁻¹` norm of
`f_{k,j} · (χ_{m,k,j} ∘ X⁻¹_{m-1,l_k})` is bounded by the centered App C estimate
`centered_frozen_hMinusOneNorm_le_of_fastPeriodicProduct_flow` with
* the fast factor `g = χ_{m,k,j}` (zero mean, fast periodic at `N = ε_m⁻¹`, `|g| ≤ G_χ`),
* the slow factor `f = f_{k,j}` (`‖f‖_{L²(𝕋²)} ≤ 4 ‖∇ ∇·((K_m + s_{m-1}) ∇T)‖_{L²}`),
* the composed analyticity `se_choice1_analytic` (amplitude `C_f`, radius `r`). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section4 AVenhance.Infra.Ergodic

/-- The absolute constant of the App C estimate. -/
def seCE : ℝ := 1 + 64 * (ergodicFourierWeight 2) ^ (1 / 2 : ℝ) + 1024 * ((2 : ℝ) + 1)

theorem seCE_nonneg : 0 ≤ seCE := by
  unfold seCE
  have : 0 ≤ (ergodicFourierWeight 2) ^ (1 / 2 : ℝ) := by
    apply Real.rpow_nonneg
    rw [ergodicFourierWeight_eq_tsum]
    exact tsum_nonneg fun k => (Real.exp_pos _).le
  positivity

theorem se_seGd_continuous {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ) {T : ℝ → Vec 2 → ℝ} (t : ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x => (I.Kmat κ m t + I.sMat hΦ m κ t x) i j))
    (hT : ContDiff ℝ ∞ (T t)) : Continuous (seGd I hΦ m κ T t) := by
  refine continuous_pi fun i => ?_
  have : (fun x => seGd I hΦ m κ T t x i) =
      slowFactorGradDiv (fun y => I.Kmat κ m t + I.sMat hΦ m κ t y) (T t) i :=
    funext fun x => seGd_apply I hΦ m κ T t x i
  rw [this]
  exact (slowFactorGradDiv_smooth hB hT i).continuous

/-- Pointwise: `|f_{k,j}|² ≤ 16 |∇ ∇·(B ∇T)|²`. -/
theorem se_choice1_sq_le {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ) {t : ℝ}
    (hξ : I.xiMK m k t ≠ 0) (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1)
    (j : Fin 2) (x : Vec 2) :
    (section5SlowChoice1 I hΦ m κ T k t j x) ^ 2 ≤ 16 * vecNormSq (seGd I hΦ m κ T t x) := by
  obtain ⟨hξ0, hξ1⟩ := Infra.Section3.xiMK_mem_Icc I (by omega : 1 ≤ m) k t
  have hF : ∀ a b, |(flowGradK I hΦ m k t x) a b| ≤ 2 := fun a b =>
    RelativeError.abs_le_two_of_sub_one hsmall (fun i j => RelativeError.flowGrad_sub_one_le hΦ hm
        k hξ x i j) a b
  have hM := sc_mulVec_vecNormSq_le (seGd I hΦ m κ T t x) hF
  have hcomp : ((flowGradK I hΦ m k t x).mulVec (seGd I hΦ m κ T t x) j) ^ 2 ≤
      vecNormSq ((flowGradK I hΦ m k t x).mulVec (seGd I hΦ m κ T t x)) := by
    rw [sc_vecNormSq_eq]
    fin_cases j <;> simp <;> nlinarith [sq_nonneg ((flowGradK I hΦ m k t x).mulVec
      (seGd I hΦ m κ T t x) 0), sq_nonneg ((flowGradK I hΦ m k t x).mulVec
      (seGd I hΦ m κ T t x) 1)]
  have h1 : section5SlowChoice1 I hΦ m κ T k t j x =
      I.xiMK m k t * ((flowGradK I hΦ m k t x).mulVec (seGd I hΦ m κ T t x)) j := rfl
  rw [h1, mul_pow]
  have hξ2 : I.xiMK m k t ^ 2 ≤ 1 := by nlinarith
  calc _ ≤ 1 * ((flowGradK I hΦ m k t x).mulVec (seGd I hΦ m κ T t x) j) ^ 2 :=
        mul_le_mul_of_nonneg_right hξ2 (sq_nonneg _)
    _ ≤ 4 * 2 ^ 2 * vecNormSq (seGd I hΦ m κ T t x) := by
        rw [one_mul]; exact hcomp.trans hM
    _ = _ := by ring

theorem se_choice1_smooth {ξ : ℝ} {Q B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {T : Vec 2 → ℝ}
    (hQ : ∀ i j, ContDiff ℝ ∞ (fun x => Q x i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x => B x i j)) (hT : ContDiff ℝ ∞ T) (j : Fin 2) :
    ContDiff ℝ ∞ (slowFactorChoice1 ξ Q B T j) :=
  (slowFactor_sum_smooth Finset.univ _
    (fun i _ => (hQ j i).mul (slowFactorGradDiv_smooth hB hT i))).const_smul ξ

/-- `‖f_{k,j}‖²_{L²(𝕋²)} ≤ 16 ‖∇ ∇·(B ∇T)‖²_{L²(𝕋²)}`. -/
theorem se_cellAverage_choice1_le {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (κ : ℝ) {T : ℝ → Vec 2 → ℝ} (k : ℤ) {t : ℝ}
    (hξ : I.xiMK m k t ≠ 0) (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x => (I.Kmat κ m t + I.sMat hΦ m κ t x) i j))
    (hT : ContDiff ℝ ∞ (T t)) (j : Fin 2) :
    cellAverage (fun x => |section5SlowChoice1 I hΦ m κ T k t j x| ^ 2) ≤
      16 * gradNormSq (seGd I hΦ m κ T t) := by
  have hQ : ∀ i j, ContDiff ℝ ∞ (fun x => I.flowGrad hΦ m (lIdx β I.Λ m k) t x i j) := by
    intro i j
    exact (amnr_flowGrad_joint_contDiff_infty I hΦ m (lIdx β I.Λ m k) i j).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  have hfs : Continuous (fun x => section5SlowChoice1 I hΦ m κ T k t j x) := by
    have : (fun x => section5SlowChoice1 I hΦ m κ T k t j x) =
        slowFactorChoice1 (I.xiMK m k t) (I.flowGrad hΦ m (lIdx β I.Λ m k) t)
          (fun x => I.Kmat κ m t + I.sMat hΦ m κ t x) (T t) j :=
      section5SlowChoice1_eq I hΦ m κ T k t j
    rw [this]
    exact (se_choice1_smooth hQ hB hT j).continuous
  have hgd : Continuous (seGd I hΦ m κ T t) := se_seGd_continuous I hΦ m κ t hB hT
  rw [← LeftToShow.spaceAvg_eq_cellAverage]
  unfold AVenhance.spaceAvg gradNormSq
  rw [← integral_const_mul]
  refine integral_mono (LeftToShow.integrableOn_unitCube_of_continuous (hfs.abs.pow 2))
    ((LeftToShow.integrableOn_unitCube_of_continuous
      (LeftToShow.continuous_vecNormSq_two.comp hgd)).const_mul 16) fun x => ?_
  simp only [sq_abs]
  exact se_choice1_sq_le I hΦ hm κ T k hξ hsmall j x

/-- One term of the centered ergodic estimate. -/
theorem se_term_bound {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ} (hκm : 0 < κm)
    (Tn : ℝ → Vec 2 → ℝ) {t : ℝ} (k : ℤ) (hξ : I.xiMK m k t ≠ 0)
    (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 / 8)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x => (I.Kmat κm m t + I.sMat hΦ m κm t x) i j))
    (hBper : IsZ2Periodic (fun x => I.Kmat κm m t + I.sMat hΦ m κm t x))
    (hT : ContDiff ℝ ∞ (Tn t)) (hTper : IsZ2Periodic (Tn t))
    {CB M L : ℝ} (hCB : 0 ≤ CB) (hM : 0 ≤ M) (hL : 2 ^ 10 / epsilon β I.Λ (m - 1) ≤ L)
    (hBb : ∀ i j w x, |amnrSpaceWord w (fun y => (I.Kmat κm m t + I.sMat hΦ m κm t y) i j) x| ≤
      CB * w.length.factorial * L ^ w.length)
    (hTb : ∀ w : List (Fin 2), 0 < w.length →
      eLpNorm (amnrSpaceWord w (Tn t)) 2 (volume.restrict (Infra.Torus.unitCell 2)) ≤
        ENNReal.ofReal (M * w.length.factorial * L ^ w.length))
    (hsep : 2 ≤ ((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ)) (j : Fin 2) :
    hMinusOneNorm (centerCell (fun x => section5SlowChoice1 I hΦ m κm Tn k t j x *
        I.chiTilde hΦ m κm k t x j)) ≤
      ENNReal.ofReal (12 * ((seCE / (ergodicFrequency β I.Λ m : ℝ)) *
        (4 * Real.sqrt (gradNormSq (seGd I hΦ m κm Tn t))) *
          (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) +
        seCE * (2048 * 40 * CB * M * L ^ 3) *
          (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) *
          Real.exp (-((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ) / 4096))) := by
  have hsm1 : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 := by linarith
  set N : ℕ := ergodicFrequency β I.Λ m with hN
  have hNpos : 0 < N := ergodicFrequency_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  set X := LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k) t with hX
  set r : ℝ := (16 * L)⁻¹ / 2 ^ 11 with hr
  have hr0 : 0 < r := by positivity
  set Gχ : ℝ := epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) with hGχ
  have hεm : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have haM : 0 ≤ a β I.Λ m := (Real.rpow_pos_of_pos hεm _).le
  have hGχ0 : 0 ≤ Gχ := by rw [hGχ]; positivity
  set CF : ℝ := 2048 * 40 * CB * M * L ^ 3 with hCF
  have hCF0 : 0 ≤ CF := by rw [hCF]; positivity
  set G : ℝ := gradNormSq (seGd I hΦ m κm Tn t) with hG
  have hG0 : 0 ≤ G := by
    rw [hG]; unfold gradNormSq; exact integral_nonneg fun x => vecNormSq_nonneg _
  -- the slow factor
  have hQ : ∀ i j, ContDiff ℝ ∞ (fun x => I.flowGrad hΦ m (lIdx β I.Λ m k) t x i j) := by
    intro i j
    exact (amnr_flowGrad_joint_contDiff_infty I hΦ m (lIdx β I.Λ m k) i j).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  set f : Vec 2 → ℝ := slowFactorChoice1 (I.xiMK m k t) (I.flowGrad hΦ m (lIdx β I.Λ m k) t)
    (fun x => I.Kmat κm m t + I.sMat hΦ m κm t x) (Tn t) j with hf
  have hfs : ContDiff ℝ ∞ f := se_choice1_smooth hQ hB hT j
  have hfper : IsZPeriodic f := se_slowFactorChoice1_periodic
    (iterate_flowGrad_periodic I hΦ m (lIdx β I.Λ m k) t) hB hBper hT hTper j
  have hfeq : ∀ x, section5SlowChoice1 I hΦ m κm Tn k t j x = f x :=
    fun x => congrFun (section5SlowChoice1_eq I hΦ m κm Tn k t j) x
  set g : Vec 2 → ℝ := fun y => I.chiMK κm m k t y j with hg
  have hgc : Continuous g := se_chi_continuous I m κm k t j
  have hprod : (fun x => section5SlowChoice1 I hΦ m κm Tn k t j x * I.chiTilde hΦ m κm k t x j) =
      fun x => f x * g (X.invFun x) := by
    funext x; rw [hfeq]; rfl
  rw [hprod]
  have hana := se_choice1_analytic I hΦ hm k hξ hsm1 hB hBper hT hTper hCB hM hL hBb hTb j
  have hg2c : Continuous (fun y => |g y| ^ 2) := hgc.abs.pow 2
  have hmain := centered_frozen_hMinusOneNorm_le_of_fastPeriodicProduct_flow (N := N) hNpos X
    hfs hfper CF r hCF0 hr0 hana hgc.locallyIntegrable hg2c.locallyIntegrable
    (se_chi_fastPeriodic I m κm k t j) hsep (se_nearIdentity I hΦ hm k hξ hsmall)
    (se_chi_cellAverage I m κm k t j)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the two averages
  have hAf : cellAverage (fun x => |f x| ^ 2) ≤ 16 * G := by
    have := se_cellAverage_choice1_le I hΦ hm κm (T := Tn) k hξ hsm1 hB hT j
    simpa only [hfeq] using this
  have hAf0 : 0 ≤ cellAverage (fun x => |f x| ^ 2) := by
    rw [← LeftToShow.spaceAvg_eq_cellAverage]
    exact integral_nonneg fun x => by positivity
  have hAg : cellAverage (fun y => |g y| ^ 2) ≤ Gχ ^ 2 := by
    apply LeftToShow.cellAverage_le_of_forall_le _ hg2c
    intro y
    have h := se_chi_abs_le I (by omega : 1 ≤ m) hκm k t y j
    have := pow_le_pow_left₀ (abs_nonneg _) h 2
    exact this
  have hAg0 : 0 ≤ cellAverage (fun y => |g y| ^ 2) := by
    rw [← LeftToShow.spaceAvg_eq_cellAverage]
    exact integral_nonneg fun x => by positivity
  have hF : (cellAverage (fun x => |f x| ^ 2)) ^ (1 / 2 : ℝ) ≤ 4 * Real.sqrt G := by
    calc _ ≤ (16 * G) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hAf0 hAf (by norm_num)
      _ = Real.sqrt (16 * G) := (Real.sqrt_eq_rpow _).symm
      _ = 4 * Real.sqrt G := by
          rw [Real.sqrt_mul (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have hGg : (cellAverage (fun y => |g y| ^ 2)) ^ (1 / 2 : ℝ) ≤ Gχ := by
    calc _ ≤ (Gχ ^ 2) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hAg0 hAg (by norm_num)
      _ = Real.sqrt (Gχ ^ 2) := (Real.sqrt_eq_rpow _).symm
      _ = Gχ := Real.sqrt_sq hGχ0
  have hCE := seCE_nonneg
  have hE0 := (Real.exp_pos (-r * (N : ℝ) / 4096)).le
  have hAf1 : 0 ≤ (cellAverage (fun x => |f x| ^ 2)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hAf0 _
  have hAg1 : 0 ≤ (cellAverage (fun y => |g y| ^ 2)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hAg0 _
  have hNinv : 0 ≤ seCE / (N : ℝ) := by positivity
  have hceq : (1 + 64 * (ergodicFourierWeight 2) ^ (1 / 2 : ℝ) + 1024 * ((2 : ℝ) + 1)) = seCE := rfl
  rw [hceq]
  have h1 : seCE / (N : ℝ) * (cellAverage (fun x => |f x| ^ 2)) ^ (1 / 2 : ℝ) *
      (cellAverage (fun y => |g y| ^ 2)) ^ (1 / 2 : ℝ) ≤
      seCE / (N : ℝ) * (4 * Real.sqrt G) * Gχ := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hF hNinv) hGg hAg1 (by positivity)
  have h2 : seCE * CF * (cellAverage (fun y => |g y| ^ 2)) ^ (1 / 2 : ℝ) *
      Real.exp (-r * (N : ℝ) / 4096) ≤ seCE * CF * Gχ * Real.exp (-r * (N : ℝ) / 4096) := by
    apply mul_le_mul_of_nonneg_right _ hE0
    exact mul_le_mul_of_nonneg_left hGg (by positivity)
  nlinarith [h1, h2]

/-- **Slice estimate.**  At a time `t` where `twistie1(t)` has mean zero, its `HDot⁻¹` norm is
    bounded by
the sum over the (at most six) pairs `(k, j)` of the centered App C estimates. -/
theorem se_slice_hMinus {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ} (hκm : 0 < κm)
    (Tn : ℝ → Vec 2 → ℝ) {t : ℝ}
    (hmean : MeanZeroOn unitCube (twistie1 I hΦ m κm Tn t))
    (hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 / 8)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x => (I.Kmat κm m t + I.sMat hΦ m κm t x) i j))
    (hBper : IsZ2Periodic (fun x => I.Kmat κm m t + I.sMat hΦ m κm t x))
    (hT : ContDiff ℝ ∞ (Tn t)) (hTper : IsZ2Periodic (Tn t))
    {CB M L : ℝ} (hCB : 0 ≤ CB) (hM : 0 ≤ M) (hL : 2 ^ 10 / epsilon β I.Λ (m - 1) ≤ L)
    (hBb : ∀ i j w x, |amnrSpaceWord w (fun y => (I.Kmat κm m t + I.sMat hΦ m κm t y) i j) x| ≤
      CB * w.length.factorial * L ^ w.length)
    (hTb : ∀ w : List (Fin 2), 0 < w.length →
      eLpNorm (amnrSpaceWord w (Tn t)) 2 (volume.restrict (Infra.Torus.unitCell 2)) ≤
        ENNReal.ofReal (M * w.length.factorial * L ^ w.length))
    (hsep : 2 ≤ ((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ)) :
    hMinusOneNorm (twistie1 I hΦ m κm Tn t) ≤
      ENNReal.ofReal (72 * ((seCE / (ergodicFrequency β I.Λ m : ℝ)) *
        (4 * Real.sqrt (gradNormSq (seGd I hΦ m κm Tn t))) *
          (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) +
        seCE * (2048 * 40 * CB * M * L ^ 3) *
          (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) *
          Real.exp (-((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ) / 4096))) := by
  classical
  obtain ⟨s, hcard, hsmem, hszero⟩ := se_xi_support I m t
  rw [se_twistie1_eq_sum I hΦ m κm Tn t s hszero]
  set c : ℝ := 12 * ((seCE / (ergodicFrequency β I.Λ m : ℝ)) *
        (4 * Real.sqrt (gradNormSq (seGd I hΦ m κm Tn t))) *
          (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) +
        seCE * (2048 * 40 * CB * M * L ^ 3) *
          (epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) *
          Real.exp (-((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ) / 4096)) with hc
  have hεm : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have haM : 0 ≤ a β I.Λ m := (Real.rpow_pos_of_pos hεm _).le
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hNr : (0 : ℝ) < (ergodicFrequency β I.Λ m : ℝ) := by
    have := ergodicFrequency_pos (Λ := I.Λ) (m := m) I.one_lt_beta I.beta_lt I.two_pow_seven_le
    exact_mod_cast this
  have hc0 : 0 ≤ c := by
    have h1 := seCE_nonneg
    have h2 : 0 ≤ Real.sqrt (gradNormSq (seGd I hΦ m κm Tn t)) := Real.sqrt_nonneg _
    have h3 : 0 ≤ Real.exp (-((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ) / 4096) :=
      (Real.exp_pos _).le
    have h4 : 0 ≤ epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) := by positivity
    have h5 : 0 ≤ 2048 * 40 * CB * M * L ^ 3 := by positivity
    rw [hc]; positivity
  have hQ : ∀ i j (k : ℤ), ContDiff ℝ ∞ (fun x => I.flowGrad hΦ m (lIdx β I.Λ m k) t x i j) := by
    intro i j k
    exact (amnr_flowGrad_joint_contDiff_infty I hΦ m (lIdx β I.Λ m k) i j).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  have hcont : ∀ (q : {k : ℤ // Odd k}) (j : Fin 2), Continuous (fun x =>
      section5SlowChoice1 I hΦ m κm Tn q.1 t j x * I.chiTilde hΦ m κm q.1 t x j) := by
    intro q j
    have h1 : section5SlowChoice1 I hΦ m κm Tn q.1 t j =
        slowFactorChoice1 (I.xiMK m q.1 t) (I.flowGrad hΦ m (lIdx β I.Λ m q.1) t)
          (fun x => I.Kmat κm m t + I.sMat hΦ m κm t x) (Tn t) j :=
      section5SlowChoice1_eq I hΦ m κm Tn q.1 t j
    have h2 : Continuous (fun x => I.chiTilde hΦ m κm q.1 t x j) :=
      (se_chi_continuous I m κm q.1 t j).comp
        (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m q.1) t).contDiff_invFun.continuous
    refine Continuous.mul ?_ h2
    rw [h1]
    exact (se_choice1_smooth (hQ · · q.1) hB hT j).continuous
  set sI : Finset ({k : ℤ // Odd k} × Fin 2) := s ×ˢ (Finset.univ : Finset (Fin 2)) with hsI
  have hsum : (fun x => ∑ q ∈ s, ∑ j : Fin 2, section5SlowChoice1 I hΦ m κm Tn q.1 t j x *
      I.chiTilde hΦ m κm q.1 t x j) = fun x => ∑ i ∈ sI, section5SlowChoice1 I hΦ m κm Tn i.1.1 t
        i.2 x * I.chiTilde hΦ m κm i.1.1 t x i.2 := by
    funext x
    rw [hsI, Finset.sum_product]
  rw [hsum]
  have hcard' : sI.card ≤ 6 := by
    rw [hsI, Finset.card_product]; simp; omega
  have hfin := frozen_hMinusOneNorm_sum_le_of_centered_bounds sI
    (fun i x => section5SlowChoice1 I hΦ m κm Tn i.1.1 t i.2 x *
      I.chiTilde hΦ m κm i.1.1 t x i.2) (fun _ => ENNReal.ofReal c)
    (fun i _ => se_memL2On_of_continuous (hcont i.1 i.2))
    (fun i _ => (hcont i.1 i.2).locallyIntegrable)
    (by
      rw [← LeftToShow.spaceAvg_eq_cellAverage]
      have htw : twistie1 I hΦ m κm Tn t = fun x => ∑ i ∈ sI, section5SlowChoice1 I hΦ m κm Tn
          i.1.1 t i.2 x * I.chiTilde hΦ m κm i.1.1 t x i.2 :=
        (se_twistie1_eq_sum I hΦ m κm Tn t s hszero).trans hsum
      have h0 := hmean
      rw [htw] at h0
      exact h0)
    (fun i hi => by
      rw [hsI, Finset.mem_product] at hi
      exact se_term_bound I hΦ hm hκm Tn i.1.1 (hsmem i.1 hi.1) hsmall hB hBper hT hTper hCB hM hL
        hBb hTb hsep i.2)
  refine hfin.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  calc (sI.card : ENNReal) * ENNReal.ofReal c ≤ (6 : ENNReal) * ENNReal.ofReal c := by
        gcongr; exact_mod_cast hcard'
    _ = ENNReal.ofReal (6 * c) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
        congr 1
        exact (ENNReal.ofReal_ofNat 6).symm
    _ = _ := by
        congr 1; rw [hc]; ring

end AVenhance.Infra.Section5.Contracts
end
