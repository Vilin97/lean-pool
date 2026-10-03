/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.LinearWindowBounds
public import Mathlib.Analysis.ODE.ExistUnique

/-! Continuous linear dependence on initial data for finite-window linear ODEs. -/

@[expose] public section

open Set
open scoped NNReal Topology

namespace AVenhance.Infra.Flow

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A global flow of a linear system is a continuous linear map in its initial
state at each fixed pair of times. The operator norm is controlled by the
finite-window Grönwall estimate. -/
theorem linearFlow_continuousLinearMap_on_window
    (A : ℝ → E →L[ℝ] E) {V : ℝ → E → ℝ → E}
    (hV : IsFlowOn (fun r z => A r z) V)
    {a d s t M : ℝ} (hs : s ∈ Ioo a d) (ht : t ∈ Icc a d)
    (hM0 : 0 ≤ M) (hM : ∀ r, r ∈ Icc a d → ‖A r‖ ≤ M) :
    ∃ J : E →L[ℝ] E, ∀ v, J v = V t v s := by
  let K : ℝ≥0 := ⟨M, hM0⟩
  have hK : (K : ℝ) = M := rfl
  have hLip (r : ℝ) (hr : r ∈ Ioo a d) :
      LipschitzWith K (fun v : E => A r v) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    rw [hK]
    calc
      ‖A r (u - v)‖ ≤ ‖A r‖ * ‖u - v‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right
        (hM r (Ioo_subset_Icc_self hr)) (norm_nonneg _)
  have hadd (v w : E) : V t (v + w) s = V t v s + V t w s := by
    let f : ℝ → E := fun r => V r (v + w) s
    let g : ℝ → E := fun r => V r v s + V r w s
    have hf' (r : ℝ) : HasDerivAt f (A r (f r)) r := hV.2 (v + w) s r
    have hg' (r : ℝ) : HasDerivAt g (A r (g r)) r := by
      have hsum := (hV.2 v s r).add (hV.2 w s r)
      convert hsum using 1
      simp [g, map_add]
    have hf : ContinuousOn f (Icc a d) :=
      HasDerivAt.continuousOn (fun r _ => hf' r)
    have hg : ContinuousOn g (Icc a d) :=
      HasDerivAt.continuousOn (fun r _ => hg' r)
    have hinit : f s = g s := by simp [f, g, hV.1]
    have huniq := ODE_solution_unique_of_mem_Icc
      (v := fun r z => A r z) (s := fun _ => (Set.univ : Set E))
      (K := K) (f := f) (g := g) (a := a) (b := d) (t₀ := s)
      (fun r hr => (hLip r hr).lipschitzOnWith) hs hf
      (fun r _ => hf' r) (fun _ _ => Set.mem_univ _)
      hg (fun r _ => hg' r) (fun _ _ => Set.mem_univ _) hinit
    have hEq := huniq ht
    simpa [f, g] using hEq
  have hsmul (c : ℝ) (v : E) : V t (c • v) s = c • V t v s := by
    let f : ℝ → E := fun r => V r (c • v) s
    let g : ℝ → E := fun r => c • V r v s
    have hf' (r : ℝ) : HasDerivAt f (A r (f r)) r := hV.2 (c • v) s r
    have hg' (r : ℝ) : HasDerivAt g (A r (g r)) r := by
      have hscale := (hV.2 v s r).const_smul c
      convert hscale using 1
      simp [g, map_smul]
    have hf : ContinuousOn f (Icc a d) :=
      HasDerivAt.continuousOn (fun r _ => hf' r)
    have hg : ContinuousOn g (Icc a d) :=
      HasDerivAt.continuousOn (fun r _ => hg' r)
    have hinit : f s = g s := by simp [f, g, hV.1]
    have huniq := ODE_solution_unique_of_mem_Icc
      (v := fun r z => A r z) (s := fun _ => (Set.univ : Set E))
      (K := K) (f := f) (g := g) (a := a) (b := d) (t₀ := s)
      (fun r hr => (hLip r hr).lipschitzOnWith) hs hf
      (fun r _ => hf' r) (fun _ _ => Set.mem_univ _)
      hg (fun r _ => hg' r) (fun _ _ => Set.mem_univ _) hinit
    have hEq := huniq ht
    simpa [f, g] using hEq
  let L : E →ₗ[ℝ] E :=
    { toFun := fun v => V t v s
      map_add' := hadd
      map_smul' := hsmul }
  have hbound : ∀ v, ‖L v‖ ≤ Real.exp (M * |t - s|) * ‖v‖ := by
    intro v
    have h := linearFlow_norm_bound_on_window hV
      (Ioo_subset_Icc_self hs) (fun r hr => hM r hr) v t ht
    simpa [L] using h
  refine ⟨L.mkContinuous (Real.exp (M * |t - s|)) hbound, ?_⟩
  intro v
  rfl

end

end AVenhance.Infra.Flow
