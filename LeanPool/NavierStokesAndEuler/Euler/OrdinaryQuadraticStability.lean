/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-! The scalar comparison lemma with genuine one-sided endpoint derivatives. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Real

theorem quadratic_stability_within (X X' : ℝ → ℝ) (C ε T : ℝ)
    (hC : 0 < C) (hε : 0 < ε) (_hT : 0 ≤ T)
    (hsmall : 2 * ε * exp (3 * C * T) ≤ 1 / 2)
    (hcont : ContinuousOn X (Icc 0 T)) (hinit : X 0 ≤ ε)
    (hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt X (X' t) (Icc 0 T) t)
    (hineq : ∀ t ∈ Ico 0 T, X' t ≤ C * (X t + (X t) ^ 2)) :
    ∀ t ∈ Icc 0 T, X t ≤ 2*ε*exp (3*C*T) := by
  let F : ℝ → ℝ := fun t => 2*ε*exp (3*C*t)
  have hF (t : ℝ) : HasDerivAt F (3*C*F t) t := by
    have hh := ((hasDerivAt_id t).const_mul (3*C)).exp.const_mul (2*ε)
    simp only [id_eq,mul_one] at hh
    change HasDerivAt (fun s => 2*ε*exp (3*C*s)) (3*C*(2*ε*exp (3*C*t))) t
    exact hh.congr_deriv (by ring)
  have hFp (t : ℝ) : 0 < F t := by dsimp [F]; positivity
  have hbound : ∀ t ∈ Icc 0 T, X t ≤ F t := by
    apply image_le_of_deriv_right_lt_deriv_boundary hcont
      (fun t ht => (hder t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    · simpa only [F,mul_zero,exp_zero,mul_one] using (hinit.trans (by linarith : ε ≤ 2*ε))
    · exact hF
    · intro t ht he
      have hFt : F t ≤ 1/2 := by
        calc
          F t ≤ 2*ε*exp (3*C*T) := by dsimp [F]; gcongr; exact ht.2.le
          _ ≤ _ := hsmall
      have hb := hineq t ht
      rw [he] at hb
      have hfsq : (F t)^2 ≤ F t := by nlinarith [hFp t]
      have hh := mul_le_mul_of_nonneg_left hfsq hC.le
      nlinarith [mul_pos hC (hFp t)]
  intro t ht
  apply (hbound t ht).trans
  dsimp [F]
  gcongr
  exact ht.2

end EulerOrdinarySobolev
