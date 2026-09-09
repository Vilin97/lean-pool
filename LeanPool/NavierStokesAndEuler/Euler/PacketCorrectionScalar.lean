/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionConstants
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! Explicit scalar choices for the actual drift-aware correction budget.
The error target is exp(-sqrt X), with X=k^ϑ in the source construction. -/

noncomputable section

namespace EulerPacketCorrectionScalar

open Set

def delta (X : ℝ) : ℝ := Real.exp (-Real.sqrt X)

def residual (k X : ℝ) : ℝ := 2*Real.exp (-(7/10)*X*Real.log k)

def initialRadius (R M Rc : ℝ) : ℝ := 1/(1+8*R+4*M*Rc+Rc)

theorem delta_pos (X : ℝ) : 0 < delta X := Real.exp_pos _

theorem delta_le_one (X : ℝ) : delta X ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg X))

theorem residual_pos (k X : ℝ) : 0 < residual k X :=
  mul_pos (by norm_num) (Real.exp_pos _)

/-- One polynomial inverse radius meets both packet-series and pressure-
inverse absorption requirements. -/
theorem initialRadius_bounds (R M Rc : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) (hRc : 0 ≤ Rc) :
    0 < initialRadius R M Rc ∧ initialRadius R M Rc*(4*R) ≤ 1/2 ∧
      4*M*(initialRadius R M Rc*Rc) ≤ 1 ∧ initialRadius R M Rc*Rc ≤ 1 := by
  have hd : 0 < 1+8*R+4*M*Rc+Rc := by positivity
  have hmc : 0 ≤ M*Rc := mul_nonneg hM hRc
  unfold initialRadius
  refine ⟨one_div_pos.mpr hd, ?_, ?_, ?_⟩
  · rw [div_mul_eq_mul_div,one_mul,div_le_iff₀ hd]
    nlinarith
  · rw [show 4*M*(1/(1+8*R+4*M*Rc+Rc)*Rc) =
        (4*M*Rc)/(1+8*R+4*M*Rc+Rc) by ring, div_le_iff₀ hd]
    nlinarith
  · rw [div_mul_eq_mul_div,one_mul,div_le_iff₀ hd]
    nlinarith

/-- The actual residual envelope wins over the Gronwall factor with an
explicit linear bound on the source growth cost. -/
theorem residual_small (C T k X : ℝ) (hX : 64 ≤ X) (hk : 1 ≤ Real.log k)
    (hgrowth : 3*C*T ≤ X/4) :
    2*residual k X*Real.exp (3*C*T) ≤ delta X/2 := by
  have hX0 : 0 ≤ X := by linarith
  have hs : Real.sqrt X ≤ X/8 :=
    (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
  have hl : Real.log 8 ≤ X/8 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)).trans (by linarith)
  have hxlog : X ≤ X*Real.log k := le_mul_of_one_le_right hX0 hk
  have he : Real.log 8 + (-(7/10)*X*Real.log k+3*C*T) ≤ -Real.sqrt X := by
    nlinarith only [hX0,hs,hl,hxlog,hgrowth]
  have hh := Real.exp_le_exp.mpr he
  rw [Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 8),Real.exp_add] at hh
  unfold residual delta
  nlinarith only [hh]

/-- The two elementary frequency guards control the radius loss caused
by the actual O(1/k) drift and the chosen error target. -/
theorem radius_decay (C T D ρ0 k X : ℝ) (hk : 0 < k)
    (hfrequency : 8*C*T*D ≤ ρ0*k)
    (herror : 8*C*T ≤ ρ0*Real.exp (Real.sqrt X)) :
    2*C*(D/k+delta X)*T ≤ ρ0/2 := by
  have hf : 8*C*T*(D/k) ≤ ρ0 := by
    calc
      _ = (8*C*T*D)/k := by ring
      _ ≤ ρ0 := (div_le_iff₀ hk).mpr hfrequency
  have he : 8*C*T*delta X ≤ ρ0 := by
    rw [delta,Real.exp_neg,← div_eq_mul_inv]
    exact (div_le_iff₀ (Real.exp_pos _)).mpr herror
  nlinarith only [hf,he]

def radius (T C D ρ0 k X : ℝ) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => ρ0-2*C*(D/k+delta X)*t.val,
    continuous_const.sub (continuous_const.mul continuous_subtype_val)⟩

theorem radius_bounds (T C D ρ0 k X : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hk : 0 < k)
    (hdecay : 2*C*(D/k+delta X)*T ≤ ρ0/2) (t : Icc (0 : ℝ) T) :
    ρ0/2 ≤ radius T C D ρ0 k X t ∧ radius T C D ρ0 k X t ≤ ρ0 := by
  have hs : 0 ≤ 2*C*(D/k+delta X) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hC)
      (add_nonneg (div_nonneg hD hk.le) (delta_pos X).le)
  have hu := mul_nonneg hs t.property.1
  have hl := (mul_le_mul_of_nonneg_left t.property.2 hs).trans hdecay
  change ρ0/2 ≤ ρ0-2*C*(D/k+delta X)*t.val ∧ ρ0-2*C*(D/k+delta X)*t.val ≤ ρ0
  constructor <;> linarith

end EulerPacketCorrectionScalar
