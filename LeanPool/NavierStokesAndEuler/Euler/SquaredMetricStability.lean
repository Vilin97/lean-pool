/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricEnergyEvolution
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Squared metric stability with a viscosity-sized source, including zero energy. -/

@[expose] public section


noncomputable section

namespace EulerSquaredMetricStability

open Set InnerProductSpace Real EulerMetricEnergyEvolution
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A literal transport-pressure-heat equation gives a squared metric differential bound without
differentiating a zero norm. -/
theorem metric_derivative_bound (K : ℝ → H →L[ℝ] H) (e : ℝ → H)
    (t ν c β h L ε M : ℝ) (K' : H →L[ℝ] H) (e' transport pressure forcing lap : H)
    (hc : 0 < c) (hν : 0 ≤ ν) (hβ : 0 ≤ β) (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hK : HasDerivAt K K' t) (he : HasDerivAt e e' t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ)
    (hcoer : c ^ 2 * ‖e t‖ ^ 2 ≤ ⟪K t (e t), e t⟫_ℝ)
    (heq : e' + transport + pressure = forcing + ν • lap)
    (hp : ⟪K t (e t), pressure⟫_ℝ = 0)
    (ht : |⟪K t (e t), transport⟫_ℝ| ≤ β * ‖e t‖ ^ 2)
    (hlap : ⟪K t (e t), lap⟫_ℝ ≤ h * ‖e t‖ ^ 2)
    (hf : ‖forcing‖ ≤ L * ‖e t‖ + ε * M) :
    deriv (fun s => ⟪K s (e s),e s⟫_ℝ) t ≤
      ((‖K'‖+2*β+2*ν*h+2*‖K t‖*L+1)/c^2)*⟪K t (e t),e t⟫_ℝ +
        (‖K t‖*M)^2*ε^2 := by
  have hd := metric_energy_evolution K e t K' e' transport pressure (forcing+ν • lap) hK he hsym
      heq hp
  rw [hd.deriv]
  have hb := energy_derivative_bound (K t) K' (e t) transport forcing β hβ ht
  have hheat := mul_le_mul_of_nonneg_left hlap (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hν)
  have hforce := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 2*‖K t‖*‖e t‖)
  have hy := sq_nonneg (‖e t‖-‖K t‖*M*ε)
  have hraw : ⟪K' (e t),e t⟫_ℝ+2*⟪K t (e t),forcing+ν • lap⟫_ℝ-2*⟪K t (e t),transport⟫_ℝ ≤
      (‖K'‖+2*β+2*ν*h+2*‖K t‖*L+1)*‖e t‖^2+(‖K t‖*M)^2*ε^2 := by
    rw [inner_add_right,real_inner_smul_right]
    nlinarith
  have hn : ‖e t‖^2 ≤ ⟪K t (e t),e t⟫_ℝ/c^2 := (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by
      nlinarith [hcoer])
  have ha : 0 ≤ ‖K'‖+2*β+2*ν*h+2*‖K t‖*L+1 := by positivity
  calc
    _ ≤ (‖K'‖+2*β+2*ν*h+2*‖K t‖*L+1)*‖e t‖^2+(‖K t‖*M)^2*ε^2 := hraw
    _ ≤ (‖K'‖+2*β+2*ν*h+2*‖K t‖*L+1)*(⟪K t (e t),e t⟫_ℝ/c^2)+(‖K t‖*M)^2*ε^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hn ha) le_rfl
    _ = _ := by ring

/-- A genuine interior differential inequality yields a finite-interval linear-growth bound,
including both endpoints. -/
theorem linear_growth_bound (E E' : ℝ → ℝ) (A B T : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hcont : ContinuousOn E (Icc 0 T)) (hzero : E 0 ≤ 0)
    (hder : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hineq : ∀ t ∈ Ioo 0 T, E' t ≤ A * E t + B) :
    ∀ t ∈ Icc 0 T, E t ≤ B*T*exp (A*T) := by
  let F := fun t : ℝ => exp (-A*t)*E t-B*t
  have hFc : ContinuousOn F (Icc 0 T) :=
    (((Real.continuous_exp.comp (show Continuous (fun t : ℝ => -A*t) from continuous_const.mul
        continuous_id)).continuousOn).mul hcont).sub
      (continuous_const.mul continuous_id).continuousOn
  have hFd (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt F (exp (-A*t)*(E' t-A*E t)-B) t := by
    have hlin : HasDerivAt (fun s : ℝ => -A*s) (-A) t := by
      simpa only [id_eq,mul_one] using (hasDerivAt_id t).const_mul (-A)
    have hlast : HasDerivAt (fun s : ℝ => B*s) B t := by
      simpa only [id_eq,mul_one] using (hasDerivAt_id t).const_mul B
    exact ((hlin.exp.mul (hder t ht)).sub hlast).congr_deriv (by ring)
  have hanti : AntitoneOn F (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hFc
    · intro t ht
      rw [interior_Icc] at ht
      exact (hFd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hFd t ht).deriv]
      have h := mul_le_mul_of_nonneg_left (hineq t ht) (exp_pos (-A*t)).le
      have hexp : exp (-A*t) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [ht.1])
      have hBexp := mul_le_mul_of_nonneg_right hexp hB
      nlinarith
  intro t ht
  have hF := hanti ⟨le_rfl,hT⟩ ht ht.1
  have hscaled : exp (-A*t)*E t ≤ B*t := by
    dsimp [F] at hF
    simp only [mul_zero,exp_zero,one_mul,sub_zero] at hF
    linarith
  have heq : exp (A*t)*exp (-A*t)=1 := by rw [← exp_add,show A*t+ -A*t=0 by ring,exp_zero]
  have hE : E t ≤ B*t*exp (A*t) := by
    have h := mul_le_mul_of_nonneg_left hscaled (exp_pos (A*t)).le
    calc
      E t = exp (A*t)*(exp (-A*t)*E t) := by rw [← mul_assoc,heq,one_mul]
      _ ≤ exp (A*t)*(B*t) := h
      _ = _ := by ring
  exact hE.trans (mul_le_mul (mul_le_mul_of_nonneg_left ht.2 hB)
    (exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hA))
    (exp_pos _).le (mul_nonneg hB hT))

end EulerSquaredMetricStability
