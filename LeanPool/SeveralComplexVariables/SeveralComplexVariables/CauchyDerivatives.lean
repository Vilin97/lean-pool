/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Complex.CauchyIntegral
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ParametricIntegral

/-!
# Cauchy's derivative formula at an arbitrary point of a disk

Mathlib's higher-derivative circle formula is stated at the center. Here the evaluation point
may be anywhere in the open disk. Differentiating the contour kernel with respect to that point
preserves the hypothesis of continuity on the boundary: no boundary derivatives of the function
are required.

These Banach-valued, one-variable results also support iterated Cauchy formulas in several
variables. The circle center and evaluation point are independent, and the derivative order is
arbitrary. The statements use Mathlib's `HasDerivAt`, `iteratedDeriv`, `DiffContOnCl`, and
circle-integral interfaces rather than introducing a separate contour or derivative theory.
Their intended Mathlib home is `Analysis.Complex.CauchyIntegral`.

## Main results

* `hasDerivAt_circleIntegral_sub_zpow_smul`: Differentiation in the evaluation point raises the
  order of the circle Cauchy kernel.
* `DiffContOnCl.iteratedDeriv_eq_circleIntegral_sub_zpow_smul`: Cauchy's formula for every
  derivative at any point inside the circle.
* `hasDerivAt_circleIntegral_sub_zpow_mul`: Differentiation in the evaluation point raises the order
  of the circle Cauchy kernel.
* `DiffContOnCl.iteratedDeriv_eq_circleIntegral_sub_zpow_mul`: Cauchy's formula for every derivative
  at any point inside the circle.
-/

open Complex MeasureTheory Metric Filter Set
open scoped Topology

public noncomputable section

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Differentiation in the evaluation point raises the order of the circle Cauchy kernel. -/
theorem hasDerivAt_circleIntegral_sub_zpow_smul
    {c w : ℂ} {R : ℝ} (hR : 0 ≤ R) (hw : w ∈ ball c R)
    {f : ℂ → E} (hf : ContinuousOn f (sphere c R)) (n : ℕ) :
    HasDerivAt (fun w => ∮ s in C(c, R), (s - w) ^ (-(n + 1 : ℤ)) • f s)
      (((n : ℂ) + 1) • ∮ s in C(c, R), (s - w) ^ (-((n + 1 : ℕ) + 1 : ℤ)) • f s) w := by
  have hkernel (k : ℕ) : ContinuousOn (fun p : ℂ × ℝ =>
      (circleMap c R p.2 - p.1) ^ (-(k + 1 : ℤ)))
      (ball c R ×ˢ Icc 0 (2 * Real.pi)) := by
    exact (((continuous_circleMap c R).comp continuous_snd).sub continuous_fst).continuousOn.zpow₀ _
      (fun p hp => Or.inl (sub_ne_zero.mpr (circleMap_ne_mem_ball hp.1 p.2)))
  have hcircle : ContinuousOn (fun p : ℂ × ℝ => deriv (circleMap c R) p.2)
      (ball c R ×ˢ Icc 0 (2 * Real.pi)) := by
    simp only [deriv_circleMap]
    fun_prop
  have hfun : ContinuousOn (fun p : ℂ × ℝ => f (circleMap c R p.2))
      (ball c R ×ˢ Icc 0 (2 * Real.pi)) :=
    hf.comp ((continuous_circleMap c R).comp continuous_snd).continuousOn
      (fun p _ => circleMap_mem_sphere c hR p.2)
  have h := hasDerivAt_integral_of_continuousOn_compact
    (μ := volume) (K := Icc 0 (2 * Real.pi))
    (F := fun w θ => deriv (circleMap c R) θ •
      ((circleMap c R θ - w) ^ (-(n + 1 : ℤ)) • f (circleMap c R θ)))
    (F' := fun w θ => ((n : ℂ) + 1) • (deriv (circleMap c R) θ •
      ((circleMap c R θ - w) ^ (-((n + 1 : ℕ) + 1 : ℤ)) • f (circleMap c R θ))))
    isCompact_Icc isOpen_ball hw
    (hcircle.smul ((hkernel n).smul hfun))
    (continuousOn_const.smul (hcircle.smul ((hkernel (n + 1)).smul hfun))) ?_
  · simpa only [circleIntegral_def_Icc, integral_smul] using h
  intro x hx θ _
  have hd := (hasDerivAt_zpow (-(n + 1 : ℤ)) (circleMap c R θ - x)
    (Or.inl (sub_ne_zero.mpr (circleMap_ne_mem_ball hx θ)))).comp x
      ((hasDerivAt_id x).const_sub (circleMap c R θ))
  have hexp : -(n + 1 : ℤ) - 1 = -((n + 1 : ℕ) + 1 : ℤ) := by omega
  have hd' : HasDerivAt (fun w => (circleMap c R θ - w) ^ (-(n + 1 : ℤ)))
      (((n : ℂ) + 1) * (circleMap c R θ - x) ^ (-((n + 1 : ℕ) + 1 : ℤ))) x := by
    simpa only [Function.comp_def, id_eq, hexp, Int.cast_neg, Int.cast_add,
      Int.cast_natCast, Int.cast_one, mul_neg_one, neg_mul, neg_neg] using hd
  convert (hd'.smul_const (f (circleMap c R θ))).const_smul (deriv (circleMap c R) θ) using 1
  simp only [smul_smul]
  congr 1
  ring

variable [CompleteSpace E]

/-- Cauchy's formula for every derivative at any point inside the circle. The function need only be
holomorphic in the open disk and continuous on its closure. -/
theorem DiffContOnCl.iteratedDeriv_eq_circleIntegral_sub_zpow_smul
    {c : ℂ} {R : ℝ} {f : ℂ → E} (hf : DiffContOnCl ℂ f (ball c R))
    (hR : 0 < R) (n : ℕ) {w : ℂ} (hw : w ∈ ball c R) :
    iteratedDeriv n f w = ((n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹) •
      ∮ s in C(c, R), (s - w) ^ (-(n + 1 : ℤ)) • f s := by
  induction n generalizing w with
  | zero =>
    simpa using
      (hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw).symm
  | succ n ih =>
    have heq : (iteratedDeriv n f) =ᶠ[nhds w]
        (fun w => ((n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹) •
          ∮ s in C(c, R), (s - w) ^ (-(n + 1 : ℤ)) • f s) := by
      filter_upwards [isOpen_ball.mem_nhds hw] with v hv
      exact ih hv
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hd := ((hasDerivAt_circleIntegral_sub_zpow_smul hR.le hw
      (hf.continuousOn_ball.mono sphere_subset_closedBall) n).const_smul
      ((n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹)).deriv
    apply hd.trans
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, smul_smul]
    congr 1
    ring

end Banach

/-- Differentiation in the evaluation point raises the order of the circle Cauchy kernel. -/
theorem hasDerivAt_circleIntegral_sub_zpow_mul
    {c w : ℂ} {R : ℝ} (hR : 0 ≤ R) (hw : w ∈ ball c R)
    {f : ℂ → ℂ} (hf : ContinuousOn f (sphere c R)) (n : ℕ) :
    HasDerivAt (fun w => ∮ s in C(c, R), (s - w) ^ (-(n + 1 : ℤ)) * f s)
      (((n : ℂ) + 1) * ∮ s in C(c, R), (s - w) ^ (-((n + 1 : ℕ) + 1 : ℤ)) * f s) w := by
  simpa only [smul_eq_mul] using hasDerivAt_circleIntegral_sub_zpow_smul hR hw hf n

/-- Cauchy's formula for every derivative at any point inside the circle. The function need only be
holomorphic in the open disk and continuous on its closure. -/
theorem DiffContOnCl.iteratedDeriv_eq_circleIntegral_sub_zpow_mul
    {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f (ball c R))
    (hR : 0 < R) (n : ℕ) {w : ℂ} (hw : w ∈ ball c R) :
    iteratedDeriv n f w = (n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹ *
      ∮ s in C(c, R), (s - w) ^ (-(n + 1 : ℤ)) * f s := by
  simpa only [smul_eq_mul] using hf.iteratedDeriv_eq_circleIntegral_sub_zpow_smul hR n hw

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
