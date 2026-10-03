/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.SmoothStep

/-! A flatter smooth step used to tune the quadratic mass of the time partition. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Cutoff

/-- An odd polynomial reparametrization of the unit interval. -/
def cardinalArg (x : ℝ) : ℝ := 1 / 2 + 2 ^ 10 * (x - 1 / 2) ^ 11

/-- A smooth transition with a long central region. -/
def cardinalStep (x : ℝ) : ℝ := step (cardinalArg x)

@[fun_prop]
theorem cardinalStep_contDiff : ContDiff ℝ (⊤ : ℕ∞) cardinalStep := by
  unfold cardinalStep cardinalArg
  fun_prop

theorem cardinalArg_one_sub (x : ℝ) : cardinalArg (1 - x) = 1 - cardinalArg x := by
  unfold cardinalArg
  have hp : (1 - x - 1 / 2) ^ 11 = -((x - 1 / 2) ^ 11) := by
    rw [show 1 - x - 1 / 2 = -(x - 1 / 2) by ring, neg_pow]
    norm_num
  rw [hp]
  ring

theorem cardinalArg_le_zero {x : ℝ} (hx : x ≤ 0) : cardinalArg x ≤ 0 := by
  have hpow : (1 / 2 : ℝ) ^ 11 ≤ (1 / 2 - x) ^ 11 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hneg : (x - 1 / 2) ^ 11 = -((1 / 2 - x) ^ 11) := by
    rw [show x - 1 / 2 = -(1 / 2 - x) by ring, neg_pow]
    norm_num
  unfold cardinalArg
  rw [hneg]
  norm_num at hpow ⊢
  nlinarith

theorem cardinalArg_one_le {x : ℝ} (hx : 1 ≤ x) : 1 ≤ cardinalArg x := by
  have h := cardinalArg_le_zero (x := 1 - x) (by linarith)
  rw [cardinalArg_one_sub] at h
  linarith

theorem cardinalStep_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : cardinalStep x = 0 :=
  step_zero_of_nonpos (cardinalArg_le_zero hx)

theorem cardinalStep_one_of_one_le {x : ℝ} (hx : 1 ≤ x) : cardinalStep x = 1 :=
  step_one_of_one_le (cardinalArg_one_le hx)

theorem cardinalStep_one_sub (x : ℝ) : cardinalStep (1 - x) = 1 - cardinalStep x := by
  simp only [cardinalStep, cardinalArg_one_sub, step_one_sub]

theorem cardinalArg_mem_middle {x : ℝ} (hlo : 1 / 8 ≤ x) (hhi : x ≤ 7 / 8) :
    15 / 32 ≤ cardinalArg x ∧ cardinalArg x ≤ 17 / 32 := by
  unfold cardinalArg
  have habs : |x - 1 / 2| ≤ 3 / 8 := by
    rw [abs_le]
    constructor <;> linarith
  have hpow : |(x - 1 / 2) ^ 11| ≤ (3 / 8 : ℝ) ^ 11 := by
    rw [abs_pow]
    gcongr
  have hpowlo := (abs_le.mp hpow).1
  have hpowhi := (abs_le.mp hpow).2
  have hsize : 2 ^ 10 * (3 / 8 : ℝ) ^ 11 ≤ 1 / 32 := by norm_num
  constructor <;> nlinarith

theorem CardinalStep.step_ge_two_fifths_middle {x : ℝ}
    (hlo : 15 / 32 ≤ x) (hhi : x ≤ 17 / 32) : 2 / 5 ≤ step x := by
  have hmono : step (15 / 32) ≤ step x :=
    Real.smoothTransition.monotone hlo
  have hmono' : step (15 / 32) ≤ step (1 - x) := by
    apply Real.smoothTransition.monotone
    linarith
  have hbase : 2 / 5 ≤ step (15 / 32) := by
    have he : (2 / 3 : ℝ) ≤ Real.exp (-(64 / 255 : ℝ)) := by
      have h := Real.add_one_le_exp (-(64 / 255 : ℝ))
      norm_num at h ⊢
      linarith
    have hp : 0 < Real.exp (-(32 / 17 : ℝ)) := Real.exp_pos _
    have hratio : Real.exp (-(32 / 15 : ℝ)) =
        Real.exp (-(32 / 17 : ℝ)) * Real.exp (-(64 / 255 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hn : expNegInvGlue (15 / 32) = Real.exp (-(32 / 15 : ℝ)) := by
      simp [expNegInvGlue]
    have hd : expNegInvGlue (1 - 15 / 32) = Real.exp (-(32 / 17 : ℝ)) := by
      norm_num [expNegInvGlue]
    change 2 / 5 ≤ expNegInvGlue (15 / 32) /
      (expNegInvGlue (15 / 32) + expNegInvGlue (1 - 15 / 32))
    rw [hn, hd, hratio]
    have hden : 0 < Real.exp (-(32 / 17 : ℝ)) *
        Real.exp (-(64 / 255 : ℝ)) + Real.exp (-(32 / 17 : ℝ)) := by positivity
    rw [le_div_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left he hp.le]
  have hlo' : 2 / 5 ≤ step x := hbase.trans hmono
  have hhi' : step x ≤ 3 / 5 := by
    rw [step_one_sub] at hmono'
    linarith [hbase.trans hmono']
  exact hlo'

theorem cardinalStep_mem_middle {x : ℝ}
    (hlo : 1 / 8 ≤ x) (hhi : x ≤ 7 / 8) :
    2 / 5 ≤ cardinalStep x ∧ cardinalStep x ≤ 3 / 5 := by
  have harg := cardinalArg_mem_middle hlo hhi
  have hlo' := CardinalStep.step_ge_two_fifths_middle harg.1 harg.2
  have h := CardinalStep.step_ge_two_fifths_middle (x := 1 - cardinalArg x) (by linarith [harg.2])
    (by linarith [harg.1])
  rw [step_one_sub] at h
  have hupper : step (cardinalArg x) ≤ 3 / 5 := by linarith
  exact ⟨hlo', by simpa [cardinalStep] using hupper⟩

theorem cardinalStep_sq_complement_lower {x : ℝ}
    (hlo : 1 / 8 ≤ x) (hhi : x ≤ 7 / 8) :
    6 / 25 ≤ cardinalStep x * (1 - cardinalStep x) := by
  obtain ⟨hlo', hhi'⟩ := cardinalStep_mem_middle hlo hhi
  nlinarith

end AVenhance.Infra.Cutoff
