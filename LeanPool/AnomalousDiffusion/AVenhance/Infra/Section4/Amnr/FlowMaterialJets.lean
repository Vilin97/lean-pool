/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowMaterial

/-! Higher material differentiation of the actual pulled-back Jacobian.
The coefficients below are derived from its evolution equation. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Coefficients of the repeated material derivative of a transported row.
The order of indices agrees with `amnr_flowGrad_material_equation`. -/
def amnrFlowMaterialCoefficient (b : AmnrSpace → Vec 2) :
    ℕ → Fin 2 → Fin 2 → AmnrSpace → ℝ
  | 0, q, p => fun _ => if q = p then 1 else 0
  | n + 1, q, p => fun z =>
      amnrOp b none (amnrFlowMaterialCoefficient b n q p) z +
        ∑ a : Fin 2, amnrVelocityGradient b a q z *
          amnrFlowMaterialCoefficient b n a p z

/-- Coefficients of every finite material order are smooth because the
velocity is smooth; no high regularity of the flow is used here. -/
theorem amnrFlowMaterialCoefficient_contDiff {b : AmnrSpace → Vec 2}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (n : ℕ) (q p : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrFlowMaterialCoefficient b n q p) := by
  induction n generalizing q p with
  | zero => exact contDiff_const
  | succ n ih =>
    apply contDiffOn_univ.mp
    exact (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn
      (ih q p).contDiffOn [none]).add (ContDiffOn.sum (fun a _ =>
        (amnrVelocityGradient_contDiffOn_infty isOpen_univ hb.contDiffOn a q).mul
          (ih a p).contDiffOn))

/-- Repeated material derivatives are explicit finite combinations of the
original row and the derived coefficients. Joint C¹ of the row suffices. -/
theorem amnrWord_material_transport {b : AmnrSpace → Vec 2}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (G : Fin 2 → AmnrSpace → ℝ)
    (hG : ∀ p, ContDiff ℝ 1 (G p))
    (heq : ∀ p z, amnrOp b none (G p) z =
      ∑ q : Fin 2, G q z * amnrVelocityGradient b p q z)
    (n : ℕ) (p : Fin 2) :
    amnrWord b (List.replicate n none) (G p) =
      fun z => ∑ q : Fin 2, G q z * amnrFlowMaterialCoefficient b n q p z := by
  induction n generalizing p with
  | zero =>
    funext z
    simp [amnrWord, amnrFlowMaterialCoefficient]
  | succ n ih =>
    rw [List.replicate_succ]
    change amnrOp b none (amnrWord b (List.replicate n none) (G p)) = _
    rw [ih]
    funext z
    have hc (q p : Fin 2) := amnrFlowMaterialCoefficient_contDiff hb n q p
    have hdG (q : Fin 2) := (hG q).differentiable (by norm_num) z
    have hdC (q p : Fin 2) := (hc q p).differentiable (by simp) z
    have hext : (fun z => ∑ q : Fin 2, G q z * amnrFlowMaterialCoefficient b n q p z) =
        ∑ q : Fin 2, G q * amnrFlowMaterialCoefficient b n q p := by
      funext y
      simp only [Finset.sum_apply, Pi.mul_apply]
    rw [hext, amnrOp_sum]
    · simp_rw [amnrOp_mul none (hdG _) (hdC _ p), heq, Finset.sum_mul]
      rw [Finset.sum_add_distrib]
      conv_lhs => lhs; rw [Finset.sum_comm]
      simp only [amnrFlowMaterialCoefficient, Finset.mul_sum, mul_add,
        Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro a _
      ring
    · intro q _
      exact (hdG q).mul (hdC q p)

end AVenhance.Infra.Section4
