/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.CutoffMemory
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.MatrixBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScales
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Quantitative slow variation of the Section 3 forcing cutoffs. -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace AVenhance.Infra.Section3

open AVenhance

/-- The product forcing cutoff has a global derivative bound at the small
cutoff scale.  The large cutoff contributes `Chat / tauP`, and `tauP ≥ tau`;
the small cutoff contributes `Czeta / tau`. -/
theorem zetaProd_deriv_abs_le {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (k : ℤ) (t : ℝ) :
    |deriv (I.zetaProd m k) t| ≤
      (I.Czeta + I.Chat) / tau β I.Λ m := by
  let l := lIdx β I.Λ m k
  let h : ℝ → ℝ := I.hatZetaML m l
  let z : ℝ → ℝ := I.zetaMK m k
  have hhsm : ContDiff ℝ (⊤ : ℕ∞) h := by
    dsimp [h]
    unfold Ingredients.hatZetaML shiftCutoff
    exact (I.hatZeta_smooth m).comp (contDiff_id.sub contDiff_const)
  have hzsm : ContDiff ℝ (⊤ : ℕ∞) z := by
    dsimp [z]
    unfold Ingredients.zetaMK scaledCutoff
    exact I.zeta_smooth.comp
      ((contDiff_id.sub contDiff_const).div_const (tau β I.Λ m))
  have hprod : I.zetaProd m k = h * z := by
    funext x
    change I.hatZetaML m (lIdx β I.Λ m k) x * I.zetaMK m k x =
      I.hatZetaML m l x * I.zetaMK m k x
    simp [l]
  have hderiv := deriv_mul
    ((ContDiff.contDiffAt (x := t) hhsm).differentiableAt (by norm_num))
    ((ContDiff.contDiffAt (x := t) hzsm).differentiableAt (by norm_num))
  have hfactor : 1 ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
    unfold Infra.Ingredients.tauCellFactor
    have hc : 0 ≤ (⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ : ℝ) :=
      Nat.cast_nonneg _
    nlinarith
  have hτ : 0 < tau β I.Λ m := I.tau_pos' m
  have hτle : tau β I.Λ m ≤ tauP β I.Λ m := by
    rw [Infra.Ingredients.tauP_eq_cellFactor_mul_tau hm]
    nlinarith
  have hhval : |h t| ≤ 1 := by
    dsimp [h]
    rw [abs_of_nonneg (hatZetaML_mem_Icc I hm l t).1]
    exact (hatZetaML_mem_Icc I hm l t).2
  have hzval : |z t| ≤ 1 := by
    dsimp [z]
    rw [abs_of_nonneg (zetaMK_mem_Icc I k t).1]
    exact (zetaMK_mem_Icc I k t).2
  have hhderiv : |deriv h t| ≤ I.Chat / tau β I.Λ m := by
    dsimp [h]
    have hNs := Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    have hb := hatZetaML_derivative_abs_le I hm l
      (j := 1) (by omega) t
    have hsmall : I.Chat / tauP β I.Λ m ≤ I.Chat / tau β I.Λ m := by
      exact div_le_div_of_nonneg_left (by linarith [I.one_le_Chat]) hτ hτle
    calc
      |deriv (I.hatZetaML m l) t| ≤ I.Chat / tauP β I.Λ m := by
        simpa only [iteratedDeriv_one, pow_one] using hb
      _ ≤ I.Chat / tau β I.Λ m := hsmall
  have hzderiv : |deriv z t| ≤ I.Czeta / tau β I.Λ m := by
    dsimp [z]
    have hNs := Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    have hb := zetaMK_derivative_abs_le I m k (j := 1) (by omega) t
    simpa only [iteratedDeriv_one, pow_one] using hb
  rw [hprod, hderiv]
  have hChat : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
  have hhnonneg : 0 ≤ I.Chat / tau β I.Λ m := div_nonneg hChat hτ.le
  calc
    |deriv h t * z t + h t * deriv z t| ≤
        |deriv h t * z t| + |h t * deriv z t| := abs_add_le _ _
    _ = |deriv h t| * |z t| + |h t| * |deriv z t| := by rw [abs_mul, abs_mul]
    _ ≤
      (I.Chat / tau β I.Λ m) * 1 + 1 * (I.Czeta / tau β I.Λ m) := by
        exact add_le_add
          (mul_le_mul hhderiv hzval (abs_nonneg _) hhnonneg)
          (mul_le_mul hhval hzderiv (abs_nonneg _) (by norm_num))
    _ = (I.Czeta + I.Chat) / tau β I.Λ m := by ring

theorem FluxEnergyCutoff.expKernel_integral_Iic {ρ t : ℝ} (hρ : 0 < ρ) :
    (∫ s in Set.Iic t, Real.exp (ρ * (s - t))) = ρ⁻¹ := by
  have hcancel : Real.exp (-ρ * t) * Real.exp (ρ * t) = 1 := by
    rw [← Real.exp_add]
    have hsum : -ρ * t + ρ * t = 0 := by ring
    rw [hsum, Real.exp_zero]
  calc
    (∫ s in Set.Iic t, Real.exp (ρ * (s - t))) =
        Real.exp (-ρ * t) * (∫ s in Set.Iic t, Real.exp (ρ * s)) := by
          rw [show (fun s : ℝ => Real.exp (ρ * (s - t))) =
            fun s => Real.exp (-ρ * t) * Real.exp (ρ * s) by
              funext s
              rw [show ρ * (s - t) = ρ * s + (-ρ * t) by ring,
                Real.exp_add]
              ring]
          rw [integral_const_mul]
    _ = Real.exp (-ρ * t) * (Real.exp (ρ * t) / ρ) := by
          rw [integral_exp_mul_Iic hρ t]
    _ = ρ⁻¹ := by
          rw [div_eq_mul_inv, ← mul_assoc, hcancel]
          simp

/-- Integration by parts in the defining memory integral: its ODE defect is
the exponentially weighted derivative of the forcing cutoff. -/
theorem FluxEnergyCutoff.corrTime_forcingError_eq_deriv_integral {β : ℝ}
    (I : Ingredients β) {m : ℕ} (κ ρ : ℝ) (k : ℤ) (t : ℝ)
    (hρ : ρ = 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) :
    I.zetaProd m k t - ρ * I.corrTime κ m k t =
      ∫ s in Set.Iic t,
        deriv (I.zetaProd m k) s * Real.exp (ρ * (s - t)) := by
  let f : ℝ → ℝ := I.zetaProd m k
  let e : ℝ → ℝ := fun s => Real.exp (ρ * (s - t))
  let g : ℝ → ℝ := f * e
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := zetaProd_contDiff I k
  have hfcompact : HasCompactSupport f := zetaProd_hasCompactSupport I k
  have he : ContDiff ℝ (⊤ : ℕ∞) e := by
    dsimp [e]
    fun_prop
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.mul he
  have hgcompact : HasCompactSupport g :=
    HasCompactSupport.mul_right (f := f) (f' := e) hfcompact
  have hfone : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hfoneDeriv : Continuous (deriv f) := hfone.continuous_deriv (by norm_num)
  have hfderivCompact : HasCompactSupport (deriv f) := hfcompact.deriv
  have hpcont : Continuous (fun s => deriv f s * e s) := hfoneDeriv.mul he.continuous
  have hpcompact : HasCompactSupport (fun s => deriv f s * e s) :=
    HasCompactSupport.mul_right (f := deriv f) (f' := e) hfderivCompact
  have hqcont : Continuous (fun s => ρ * (f s * e s)) :=
    continuous_const.mul (hf.continuous.mul he.continuous)
  have hqcompact : HasCompactSupport (fun s => ρ * (f s * e s)) := by
    have hqfun : (fun s => ρ * (f s * e s)) = (fun _ : ℝ => ρ) * (f * e) := by
      funext s
      rfl
    rw [hqfun]
    exact HasCompactSupport.mul_left hgcompact
  have hpint : IntegrableOn (fun s => deriv f s * e s) (Set.Iic t) :=
    (hpcont.integrable_of_hasCompactSupport hpcompact).integrableOn
  have hqint : IntegrableOn (fun s => ρ * (f s * e s)) (Set.Iic t) :=
    (hqcont.integrable_of_hasCompactSupport hqcompact).integrableOn
  have hderivEq : deriv g = fun s => deriv f s * e s + ρ * (f s * e s) := by
    funext s
    have hfdiff : DifferentiableAt ℝ f s :=
      (ContDiff.contDiffAt (x := s) hf).differentiableAt (by norm_num)
    have hediff : DifferentiableAt ℝ e s :=
      (ContDiff.contDiffAt (x := s) he).differentiableAt (by norm_num)
    have hmul := deriv_mul hfdiff hediff
    have hederiv : deriv e s = ρ * e s := by
      have harg : HasDerivAt (fun x : ℝ => ρ * (x - t)) ρ s := by
        simpa using (hasDerivAt_id s).sub_const t |>.const_mul ρ
      have h := harg.exp.deriv
      change deriv (fun x : ℝ => Real.exp (ρ * (x - t))) s = _
      rw [h]
      ring
    change deriv (f * e) s = _
    rw [hmul, hederiv]
    ring
  have hfund := hgcompact.integral_Iic_deriv_eq (hg.of_le (by norm_num)) t
  rw [hderivEq, integral_add hpint hqint, integral_const_mul] at hfund
  have hgval : g t = f t := by simp [g, e, f]
  rw [hgval] at hfund
  have hmemory : I.corrTime κ m k t =
      ∫ s in Set.Iic t, f s * e s := by
    unfold Ingredients.corrTime
    rw [show (fun s : ℝ => I.zetaProd m k s *
      Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t))) =
      fun s => f s * e s by
        funext s
        simp [f, e, hρ]]
  rw [← hmemory] at hfund
  dsimp [f, g, e] at hfund ⊢
  linarith

/-- The memory tracks its instantaneous forcing with error bounded by
the forcing's variation over one relaxation time.  This is the quantitative
integration-by-parts step only sketched at source lines 3399--3416. -/
theorem corrTime_forcingError_le {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (k : ℤ) (t : ℝ) :
    |I.zetaProd m k t -
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) * I.corrTime κ m k t| ≤
      ((I.Czeta + I.Chat) / (4 * Real.pi ^ 2)) *
        (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let D := (I.Czeta + I.Chat) / tau β I.Λ m
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have herror := FluxEnergyCutoff.corrTime_forcingError_eq_deriv_integral I κ ρ k t (by rfl)
  let p : ℝ → ℝ := fun s => deriv (I.zetaProd m k) s * Real.exp (ρ * (s - t))
  have hF := zetaProd_contDiff I (m := m) k
  have hF1 : ContDiff ℝ 1 (I.zetaProd m k) := hF.of_le (by norm_num)
  have hpcont : Continuous p := by
    dsimp [p]
    exact hF1.continuous_deriv (by norm_num) |>.mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const)))
  have hpsupp : HasCompactSupport p := by
    dsimp [p]
    exact HasCompactSupport.mul_right (f := deriv (I.zetaProd m k))
      (f' := fun s => Real.exp (ρ * (s - t)))
      ((zetaProd_hasCompactSupport I k).deriv)
  have hpint : IntegrableOn p (Set.Iic t) :=
    (hpcont.integrable_of_hasCompactSupport hpsupp).integrableOn
  have hkernelint : IntegrableOn (fun s : ℝ => Real.exp (ρ * (s - t)))
      (Set.Iic t) := by
    have hbase := integrableOn_exp_mul_Iic hρ t
    have heq : (fun s : ℝ => Real.exp (ρ * (s - t))) =
        fun s => Real.exp (-ρ * t) * Real.exp (ρ * s) := by
      funext s
      rw [show ρ * (s - t) = ρ * s + (-ρ * t) by ring, Real.exp_add]
      ring
    rw [heq]
    exact hbase.const_mul _
  have hmajorint : IntegrableOn
      (fun s : ℝ => D * Real.exp (ρ * (s - t))) (Set.Iic t) :=
    hkernelint.const_mul _
  have hpoint (s : ℝ) :
      |deriv (I.zetaProd m k) s| * Real.exp (ρ * (s - t)) ≤
        D * Real.exp (ρ * (s - t)) := by
    have hd := zetaProd_deriv_abs_le I hm k s
    have hExp : 0 ≤ Real.exp (ρ * (s - t)) := Real.exp_nonneg _
    exact mul_le_mul_of_nonneg_right (by simpa [D] using hd) hExp
  have hmajor := FluxEnergyCutoff.expKernel_integral_Iic (ρ := ρ) (t := t) hρ
  let pabs : ℝ → ℝ := fun s => |deriv (I.zetaProd m k) s| *
    Real.exp (ρ * (s - t))
  have hpabscont : Continuous pabs := by
    dsimp [pabs]
    exact (hF1.continuous_deriv (by norm_num)).abs.mul
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_id.sub continuous_const)))
  have hpabssupp : HasCompactSupport pabs := by
    dsimp [pabs]
    exact HasCompactSupport.mul_right (f := |deriv (I.zetaProd m k)|)
      (f' := fun s => Real.exp (ρ * (s - t)))
      ((zetaProd_hasCompactSupport I (m := m) k).deriv.abs)
  have hpabsint : IntegrableOn pabs (Set.Iic t) :=
    (hpabscont.integrable_of_hasCompactSupport hpabssupp).integrableOn
  have hpabsmajor (s : ℝ) : pabs s ≤ D * Real.exp (ρ * (s - t)) := by
    exact hpoint s
  have hmonoAbs := setIntegral_mono_on hpabsint hmajorint measurableSet_Iic
    (fun s _ => hpabsmajor s)
  have hbound :
      |∫ s in Set.Iic t, p s| ≤ D * ρ⁻¹ := by
    calc
      |∫ s in Set.Iic t, p s| ≤ ∫ s in Set.Iic t, |p s| :=
        abs_integral_le_integral_abs
      _ = ∫ s in Set.Iic t, pabs s := by
            congr 1
            funext s
            simp [pabs, p, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      _ ≤ ∫ s in Set.Iic t, D * Real.exp (ρ * (s - t)) := hmonoAbs
      _ = D * ρ⁻¹ := by rw [integral_const_mul, hmajor]
  change |I.zetaProd m k t - ρ * I.corrTime κ m k t| ≤ _
  rw [herror]
  calc
    |∫ s in Set.Iic t, p s| ≤ D * ρ⁻¹ := hbound
    _ = ((I.Czeta + I.Chat) / (4 * Real.pi ^ 2)) *
        (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
      dsimp [D, ρ]
      field_simp [ne_of_gt hκ, ne_of_gt hτ, ne_of_gt hε]
  where
    hτ : 0 < tau β I.Λ m := I.tau_pos' m

end AVenhance.Infra.Section3
