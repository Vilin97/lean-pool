/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialSmoothness

/-! Actual higher derivatives of primitive fields acting on trajectories. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- Each actual trajectory-space derivative is the pointwise state
derivative of the primitive field. There is no additional norm cost from
the curve-space representation. -/
theorem amnrCurveJointCompose_iteratedFDeriv_eval {K E F : Type}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hbound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖iteratedFDeriv ℝ j f z‖ ≤ C)
    (η : C(K, ℝ)) (n : ℕ) (u : C(K, E)) (v : Fin n → C(K, E)) (t : K) :
    iteratedFDeriv ℝ n (amnrCurveJointCompose f hf.continuous η) u v t =
      iteratedFDeriv ℝ n (fun x => f (η t, x)) (u t) (fun j => v j t) := by
  let P := ContinuousMap.evalCLM ℝ (M := F) t
  let R := ContinuousMap.evalCLM ℝ (M := E) t
  let N := amnrCurveJointCompose f hf.continuous η
  have hN := amnrCurveJointCompose_contDiff_infty hf hbound η
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => f (η t, x)) := hf.comp (contDiff_const.prodMk contDiff_id)
  have heq : P ∘ N = (fun x => f (η t, x)) ∘ R := rfl
  have hl := P.iteratedFDeriv_comp_left (hN.contDiffAt (x := u)) (i := n) (by simp)
  have hr := R.iteratedFDeriv_comp_right hs u (i := n) (by simp)
  rw [heq, hr] at hl
  exact (congrArg (fun L => L v) hl).symm

/-- A uniform actual state-derivative bound gives exactly the same bound
for the corresponding operator on continuous trajectories. -/
theorem amnrCurveJointCompose_iteratedFDeriv_norm_le {K E F : Type}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hbound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖iteratedFDeriv ℝ j f z‖ ≤ C)
    (η : C(K, ℝ)) (n : ℕ) (u : C(K, E)) {B : ℝ} (hB : 0 ≤ B)
    (hstate : ∀ t x, ‖iteratedFDeriv ℝ n (fun y => f (η t, y)) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (amnrCurveJointCompose f hf.continuous η) u‖ ≤ B := by
  apply ContinuousMultilinearMap.opNorm_le_bound hB
  intro v
  have hprod : 0 ≤ ∏ j : Fin n, ‖v j‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  apply (ContinuousMap.norm_le _ (mul_nonneg hB hprod)).mpr
  intro t
  rw [amnrCurveJointCompose_iteratedFDeriv_eval hf hbound]
  have hh := (iteratedFDeriv ℝ n (fun y => f (η t, y)) (u t)).le_opNorm (fun j => v j t)
  refine hh.trans ?_
  apply mul_le_mul (hstate t (u t)) ?_ (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hB
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => (v j).norm_coe_le_norm t)

end AVenhance.Infra.Section4
