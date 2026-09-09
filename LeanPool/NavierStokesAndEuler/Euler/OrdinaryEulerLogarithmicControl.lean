/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerGradientControl
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerKineticEnergy
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryVariableGronwall

/-! The scalar part of the vorticity continuation argument. A genuine
logarithmic gradient estimate bounds the gradient integral using only
the time integral of its continuous vorticity coefficient. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Real EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerVolterraConvolution EulerContinuousTimeIntegral

/-- Log energy base, given by `exp 1+wordCount 3*sqrt (wordEnergy 3 A)`. -/
def logEnergyBase (A : SmoothL2Field Space) : ℝ :=
  exp 1+wordCount 3*sqrt (wordEnergy 3 A)

theorem logEnergyBase_pos (A : SmoothL2Field Space) : 0 < logEnergyBase A :=
  add_pos_of_pos_of_nonneg (exp_pos 1) (mul_nonneg (wordCount_nonneg 3) (sqrt_nonneg _))

/-- Logarithmic gronwall constant, given by `C*(1+‖A.toLp‖+logEnergyBase
A+gradientEnergyConstant)`. -/
def logarithmicGronwallConstant (C : ℝ) (A : SmoothL2Field Space) : ℝ :=
  C*(1+‖A.toLp‖+logEnergyBase A+gradientEnergyConstant)

theorem logarithmicGronwallConstant_nonneg (C : ℝ) (hC : 0 ≤ C) (A : SmoothL2Field Space) :
    0 ≤ logarithmicGronwallConstant C A := by
  unfold logarithmicGronwallConstant
  positivity [logEnergyBase_pos A,gradientEnergyConstant_nonneg]

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T} (U : Evolution T hT)

theorem logarithmic_h3_bound (t : Icc (0 : ℝ) T) :
    log (exp 1+tensorNorm 3 (U.velocity t)) ≤
      logEnergyBase (U.velocity ⟨0,le_rfl,hT⟩)+gradientEnergyConstant*U.gradientIntegral t := by
  let a := gradientEnergyConstant*U.gradientIntegral t
  have ha : 0 ≤ a := mul_nonneg gradientEnergyConstant_nonneg (U.gradientIntegral_nonneg t)
  have hexp : 1 ≤ exp a := one_le_exp ha
  have hs : sqrt (exp a) ≤ exp a := sqrt_le_self_iff.mpr (Or.inr hexp)
  have hE0 := wordEnergy_nonneg 3 (U.velocity ⟨0,le_rfl,hT⟩)
  have hnorm : tensorNorm 3 (U.velocity t) ≤
      (wordCount 3*sqrt (wordEnergy 3 (U.velocity ⟨0,le_rfl,hT⟩)))*exp a := by
    apply (tensorNorm_le_energy (U.velocity t) 3).trans
    calc
      wordCount 3*sqrt (wordEnergy 3 (U.velocity t)) ≤
          wordCount 3*sqrt (wordEnergy 3 (U.velocity ⟨0,le_rfl,hT⟩)*exp a) :=
        mul_le_mul_of_nonneg_left (sqrt_le_sqrt (U.h3_energy_gradientIntegral t)) (wordCount_nonneg
            3)
      _ = wordCount 3*(sqrt (wordEnergy 3 (U.velocity ⟨0,le_rfl,hT⟩))*sqrt (exp a)) := by
        rw [sqrt_mul hE0]
      _ ≤ wordCount 3*(sqrt (wordEnergy 3 (U.velocity ⟨0,le_rfl,hT⟩))*exp a) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (sqrt_nonneg _)) (wordCount_nonneg
            3)
      _ = _ := by ring
  have hexpone : exp 1 ≤ exp 1*exp a := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (exp_pos 1).le
  have harg : exp 1+tensorNorm 3 (U.velocity t) ≤
      logEnergyBase (U.velocity ⟨0,le_rfl,hT⟩)*exp a := by
    calc
      _ ≤ exp 1*exp a+(wordCount 3*sqrt (wordEnergy 3 (U.velocity ⟨0,le_rfl,hT⟩)))*exp a :=
        add_le_add hexpone hnorm
      _ = _ := by unfold logEnergyBase; ring
  calc
    _ ≤ log (logEnergyBase (U.velocity ⟨0,le_rfl,hT⟩)*exp a) :=
      log_le_log (add_pos_of_pos_of_nonneg (exp_pos 1) (tensorNorm_nonneg 3 _)) harg
    _ = log (logEnergyBase (U.velocity ⟨0,le_rfl,hT⟩))+a := by
      rw [log_mul (logEnergyBase_pos _).ne' (exp_pos a).ne',log_exp]
    _ ≤ logEnergyBase (U.velocity ⟨0,le_rfl,hT⟩)+a := by
      have h := log_le_sub_one_of_pos (logEnergyBase_pos (U.velocity ⟨0,le_rfl,hT⟩))
      linarith

variable (C : ℝ) (hC : 0 ≤ C) (W : C(Icc (0 : ℝ) T, ℝ))
  (hW : ∀ t, 0 ≤ W t)
  (hlog : ∀ t, U.gradientNormPath t ≤
    C * (1 + ‖(U.velocity t).toLp‖ + W t * log (exp 1 + tensorNorm 3 (U.velocity t))))

include hC hW hlog

theorem gradient_logarithmic_envelope (t : Icc (0 : ℝ) T) :
    U.gradientNormPath t ≤ logarithmicGronwallConstant C (U.velocity ⟨0,le_rfl,hT⟩) *
      (1+W t)*(1+U.gradientIntegral t) := by
  let b := 1+‖(U.velocity ⟨0,le_rfl,hT⟩).toLp‖
  let e := logEnergyBase (U.velocity ⟨0,le_rfl,hT⟩)
  let d := b+e+gradientEnergyConstant
  let z := 1+U.gradientIntegral t
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have he : 0 ≤ e := (logEnergyBase_pos _).le
  have hk := gradientEnergyConstant_nonneg
  have hg := U.gradientIntegral_nonneg t
  have hd : 0 ≤ d := add_nonneg (add_nonneg hb he) hk
  have hbd : b ≤ d := by dsimp [d]; linarith
  have hed : e ≤ d := by dsimp [d]; linarith
  have hkd : gradientEnergyConstant ≤ d := by dsimp [d]; linarith
  have hz : 1 ≤ z := by dsimp [z]; linarith
  have hbz : b ≤ d*z := hbd.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hd)
  have hez : e+gradientEnergyConstant*U.gradientIntegral t ≤ d*z := by
    calc
      _ ≤ d+d*U.gradientIntegral t := add_le_add hed (mul_le_mul_of_nonneg_right hkd hg)
      _ = _ := by dsimp [z]; ring
  have hfirst : U.gradientNormPath t ≤ C*(b+W t*(e+gradientEnergyConstant*U.gradientIntegral t)) :=
      by
    have h := hlog t
    rw [U.velocity_norm_conserved t] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (U.logarithmic_h3_bound t) (hW t))) hC)
  apply hfirst.trans
  change C*(b+W t*(e+gradientEnergyConstant*U.gradientIntegral t)) ≤ C*d*(1+W t)*z
  calc
    _ ≤ C*(d*z+W t*(d*z)) :=
      mul_le_mul_of_nonneg_left (add_le_add hbz (mul_le_mul_of_nonneg_left hez (hW t))) hC
    _ = _ := by ring

theorem gradientIntegral_logarithmic_bound (t : Icc (0 : ℝ) T) :
    1+U.gradientIntegral t ≤
      exp (logarithmicGronwallConstant C (U.velocity ⟨0,le_rfl,hT⟩) *
        ((t : ℝ)+realIntegral T hT W t)) := by
  let K : C(Icc (0 : ℝ) T,ℝ) := ⟨fun s => 1+W s,continuous_const.add W.continuous⟩
  let X := fun r => 1+realIntegral T hT U.gradientNormPath r
  let X' := extendPath T hT U.gradientNormPath
  have hIc : Continuous (realIntegral T hT U.gradientNormPath) :=
    (show Differentiable ℝ (realIntegral T hT U.gradientNormPath) from
      fun r => (realIntegral_hasDerivAt T hT U.gradientNormPath r).differentiableAt).continuous
  have hc : ContinuousOn X (Icc (0 : ℝ) T) := (continuous_const.add hIc).continuousOn
  have hder (r : ℝ) (_hr : r ∈ Ico 0 T) : HasDerivWithinAt X (X' r) (Icc (0 : ℝ) T) r :=
    ((realIntegral_hasDerivAt T hT U.gradientNormPath r).const_add 1).hasDerivWithinAt
  have hi (r : ℝ) (hr : r ∈ Ico 0 T) :
      X' r ≤ logarithmicGronwallConstant C (U.velocity ⟨0,le_rfl,hT⟩)*extendPath T hT K r*X r := by
    have h := U.gradient_logarithmic_envelope C hC W hW hlog ⟨r,hr.1,hr.2.le⟩
    change U.gradientNormPath (projIcc 0 T hT r) ≤
      logarithmicGronwallConstant C (U.velocity ⟨0,le_rfl,hT⟩) *
        (1+W (projIcc 0 T hT r))*(1+realIntegral T hT U.gradientNormPath r)
    simpa only [gradientIntegral,projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1,hr.2.le⟩)] using h
  have h := variable_linear_stability T hT X X'
    (logarithmicGronwallConstant C (U.velocity ⟨0,le_rfl,hT⟩)) K hc hder hi t
  have hX0 : X 0=1 := by simp only [X,realIntegral,intervalIntegral.integral_same,add_zero]
  have hK : realIntegral T hT K t=(t : ℝ)+realIntegral T hT W t := by
    change (∫ r in (0 : ℝ)..(t : ℝ), (1+extendPath T hT W r))=_
    rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable 0 t)
      ((extendPath_continuous T hT W).intervalIntegrable 0 t)]
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one]
    rfl
  rw [hX0,one_mul,hK] at h
  exact h

theorem gradientIntegral_logarithmic_uniform (Tmax G : ℝ) (hTmax : T ≤ Tmax)
    (hG : ∀ t : Icc (0 : ℝ) T, realIntegral T hT W t ≤ G) (t : Icc (0 : ℝ) T) :
    U.gradientIntegral t ≤ exp (logarithmicGronwallConstant C (U.velocity ⟨0,le_rfl,hT⟩)*(Tmax+G))
        := by
  have hb := U.gradientIntegral_logarithmic_bound C hC W hW hlog t
  have he := exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (add_le_add (t.property.2.trans hTmax) (hG t))
    (logarithmicGronwallConstant_nonneg C hC (U.velocity ⟨0,le_rfl,hT⟩)))
  linarith

end Evolution
end EulerOrdinarySobolev
