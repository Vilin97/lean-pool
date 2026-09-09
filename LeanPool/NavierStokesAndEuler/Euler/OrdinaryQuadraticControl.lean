/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-! A uniform short-time bound for a nonnegative genuine energy with
a quadratic differential upper bound. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set

theorem quadratic_energy_bound (T C : ℝ) (hT : 0 ≤ T)
    (X X' : ℝ → ℝ) (hX : ContinuousOn X (Icc 0 T))
    (hpos : ∀ t ∈ Icc 0 T, 0 ≤ X t)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt X (X' t) (Icc 0 T) t)
    (hb : ∀ t ∈ Icc 0 T, X' t ≤ C * (1 + X t) ^ 2)
    (hC : 0 ≤ C) (hsmall : C * T ≤ (1 + X 0)⁻¹ / 2)
    (t : ℝ) (ht : t ∈ Icc 0 T) : X t ≤ 2*X 0+1 := by
  have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl,hT⟩
  have hp (r : ℝ) (hr : r ∈ Icc 0 T) : 0 < 1+X r := by linarith [hpos r hr]
  let f (r : ℝ) := (1+X r)⁻¹+C*r
  let f' (r : ℝ) := -(X' r)/(1+X r)^2+C
  have hc : ContinuousOn f (Icc 0 T) :=
    ((continuousOn_const.add hX).inv₀ (fun r hr => (hp r hr).ne')).add
      (continuous_const.mul continuous_id).continuousOn
  have hfd (r : ℝ) (hr : r ∈ Icc 0 T) : HasDerivWithinAt f (f' r) (Icc 0 T) r := by
    have hi := ((hd r hr).const_add 1).inv (hp r hr).ne'
    have hl := ((hasDerivAt_id r).const_mul C).hasDerivWithinAt (s := Icc 0 T)
    simpa only [f,f',id_eq,mul_one,Pi.inv_apply] using hi.fun_add hl
  have hfn (r : ℝ) (hr : r ∈ Icc 0 T) : 0 ≤ f' r := by
    have hdv : X' r/(1+X r)^2 ≤ C := (div_le_iff₀ (sq_pos_of_pos (hp r hr))).mpr (by
      simpa only [mul_comm C] using hb r hr)
    dsimp [f']
    rw [neg_div]
    linarith
  have hm : MonotoneOn f (Icc 0 T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) hc
      (fun r hr => (hfd r (interior_subset hr)).mono interior_subset)
      (fun r hr => hfn r (interior_subset hr))
  have hmono := hm hz ht ht.1
  dsimp [f] at hmono
  have hCt : C*t ≤ (1+X 0)⁻¹/2 :=
    (mul_le_mul_of_nonneg_left ht.2 hC).trans hsmall
  have hi : (1 : ℝ)/(2*(1+X 0)) ≤ 1/(1+X t) := by
    have he : (1 : ℝ)/(2*(1+X 0))=(1+X 0)⁻¹/2 := by
      rw [mul_comm 2,div_mul_eq_div_div,one_div]
    rw [he,one_div]
    linarith
  have hcross := (div_le_div_iff₀ (mul_pos (by norm_num) (hp 0 hz)) (hp t ht)).mp hi
  nlinarith

end EulerOrdinarySobolev
