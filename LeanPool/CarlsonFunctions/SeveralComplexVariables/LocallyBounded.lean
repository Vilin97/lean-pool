/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.SeveralComplexVariables.CauchyEstimates
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Locally bounded separate holomorphy

Coordinate Cauchy estimates give joint local Lipschitz bounds for locally bounded,
separately holomorphic functions. This supplies the continuity hypothesis of Osgood's
theorem and the equicontinuity estimate used in Montel's theorem.
-/

public section

open Complex Filter Function Metric Set
open scoped Classical NNReal Topology

namespace SeveralComplexVariables

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [NormedSpace ℂ F] in
/-- Coordinate variation bounds telescope to a joint bound on a product set. This also
includes the empty product, where every function is constant. -/
theorem norm_sub_le_sum_of_update {s : ι → Set ℂ} {f : (ι → ℂ) → F} {C : ℝ}
    (hf : ∀ z ∈ Set.pi univ s, ∀ i, ∀ w ∈ s i,
      ‖f (update z i w) - f z‖ ≤ C * ‖w - z i‖)
    {x y : ι → ℂ} (hx : x ∈ Set.pi univ s) (hy : y ∈ Set.pi univ s) :
    ‖f y - f x‖ ≤ ∑ i, C * ‖y i - x i‖ := by
  have hmem (t : Finset ι) : (fun i => if i ∈ t then y i else x i) ∈ Set.pi univ s := by
    intro i hi
    dsimp only
    split_ifs <;> [exact hy i hi; exact hx i hi]
  have hstep (t : Finset ι) :
      ‖f (fun i => if i ∈ t then y i else x i) - f x‖ ≤ ∑ i ∈ t, C * ‖y i - x i‖ := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      have heq : (fun j => if j ∈ insert i t then y j else x j) =
          update (fun j => if j ∈ t then y j else x j) i (y i) := by
        funext j
        by_cases hji : j = i <;> simp [hji]
      rw [heq, Finset.sum_insert hi]
      refine (norm_sub_le_norm_sub_add_norm_sub _ (f (fun j => if j ∈ t then y j else x j)) _).trans
        (add_le_add ?_ ih)
      simpa [hi] using hf _ (hmem t) i (y i) (hy i (mem_univ i))
  simpa using hstep Finset.univ

/-- Updating a coordinate within its disc preserves a closed sup-norm ball. -/
theorem update_mem_closedBall_of_mem {c z : ι → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hz : z ∈ closedBall c r) (i : ι) {w : ℂ} (hw : w ∈ closedBall (c i) r) :
    update z i w ∈ closedBall c r := by
  rw [mem_closedBall, dist_pi_le_iff hr] at hz ⊢
  intro j
  by_cases hji : j = i
  · simpa [hji] using hw
  · simpa [hji] using hz j

/-- A bounded separately holomorphic map is jointly Lipschitz on a smaller polydisc.
The constant is explicit and uniform over families with the same bound. -/
theorem norm_sub_le_of_separately_analytic_bounded {f : (ι → ℂ) → F}
    {c : ι → ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : ∀ z ∈ closedBall c (2 * r), ∀ i,
      AnalyticAt ℂ (fun w => f (update z i w)) (z i))
    (hM : ∀ z ∈ closedBall c (2 * r), ‖f z‖ ≤ M)
    {x y : ι → ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    ‖f y - f x‖ ≤ (Fintype.card ι : ℝ) * (M / r) * ‖y - x‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans (hM c (mem_closedBall_self (by positivity)))
  have hsmall : closedBall c r ⊆ closedBall c (2 * r) := closedBall_subset_closedBall (by linarith)
  have hdiff (z : ι → ℂ) (i : ι) (w : ℂ) (hw : update z i w ∈ closedBall c (2 * r)) :
      DifferentiableAt ℂ (fun v => f (update z i v)) w := by
    simpa only [update_idem, update_self] using (hf _ hw i).differentiableAt
  have hcoord (z : ι → ℂ) (hz : z ∈ closedBall c r) (i : ι) (w : ℂ)
      (hw : w ∈ closedBall (c i) r) :
      ‖f (update z i w) - f z‖ ≤ (M / r) * ‖w - z i‖ := by
    have hder (v : ℂ) (hv : v ∈ closedBall (c i) r) :
        ‖deriv (fun a => f (update z i a)) v‖ ≤ M / r := by
      have hp := update_mem_closedBall_of_mem hr.le hz i hv
      have hball : closedBall (update z i v) r ⊆ closedBall c (2 * r) :=
        closedBall_subset_closedBall' (by linarith [mem_closedBall.mp hp])
      have hslice := norm_partialDeriv_le_of_slice (f := f) (z := update z i v) i hr
        (fun a ha => (hdiff (update z i v) i a
          (hball (update_mem_closedBall hr.le ha))).differentiableWithinAt)
        (fun a ha => hM _ (hball (update_mem_closedBall hr.le (sphere_subset_closedBall ha))))
      simpa only [partialDeriv, update_idem, update_self] using hslice
    have hzi : z i ∈ closedBall (c i) r := (dist_pi_le_iff hr.le).mp (mem_closedBall.mp hz) i
    simpa only [update_eq_self] using
      (convex_closedBall (c i) r).norm_image_sub_le_of_norm_deriv_le
        (fun v hv => hdiff z i v (hsmall (update_mem_closedBall_of_mem hr.le hz i hv)))
        hder hzi hw
  have hprod : closedBall c r = Set.pi univ (fun i => closedBall (c i) r) := closedBall_pi c hr.le
  have hsum := norm_sub_le_sum_of_update (C := M / r)
    (fun z hz i w hw => hcoord z (hprod.symm ▸ hz) i w hw) (hprod ▸ hx) (hprod ▸ hy)
  refine hsum.trans ?_
  calc
    ∑ i, (M / r) * ‖y i - x i‖ ≤ ∑ i : ι, (M / r) * ‖y - x‖ :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm (y - x) i)
        (div_nonneg hM0 hr.le))
    _ = _ := by simp [mul_assoc]

/-- Local bounds and separate holomorphy give a Lipschitz neighborhood of each point. -/
theorem exists_lipschitzOnWith_of_separately_analytic_locally_bounded
    {U : Set (ι → ℂ)} {f : (ι → ℂ) → F} (hU : IsOpen U)
    (hf : ∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i))
    {c : ι → ℂ} (hc : c ∈ U) (hb : ∃ M : ℝ, ∀ᶠ z in 𝓝 c, ‖f z‖ ≤ M) :
    ∃ r > 0, ∃ C : ℝ≥0, LipschitzOnWith C f (closedBall c r) := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨R, hR, hball⟩ := nhds_basis_closedBall.mem_iff.mp (inter_mem (hU.mem_nhds hc) hM)
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans
    (hball (mem_closedBall_self hR.le)).2
  have hr : 0 < R / 2 := by positivity
  have htwo : 2 * (R / 2) = R := by ring
  have hfa : ∀ z ∈ closedBall c (2 * (R / 2)), ∀ i,
      AnalyticAt ℂ (fun w => f (update z i w)) (z i) := by
    intro z hz
    exact hf z (hball (by simpa only [htwo] using hz)).1
  have hbound : ∀ z ∈ closedBall c (2 * (R / 2)), ‖f z‖ ≤ M := by
    intro z hz
    exact (hball (by simpa only [htwo] using hz)).2
  refine ⟨R / 2, hr, ⟨(Fintype.card ι : ℝ) * (M / (R / 2)), by positivity⟩, ?_⟩
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro x hx y hy
  exact norm_sub_le_of_separately_analytic_bounded hr hfa hbound hy hx

variable [CompleteSpace F]

/-- **Locally bounded Osgood theorem.** Joint continuity need not be assumed when a
separately holomorphic map is locally bounded on its open domain. -/
theorem analyticOnNhd_of_separately_analytic_locally_bounded
    {U : Set (ι → ℂ)} {f : (ι → ℂ) → F} (hU : IsOpen U)
    (hf : ∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (update z i w)) (z i))
    (hb : ∀ c ∈ U, ∃ M : ℝ, ∀ᶠ z in 𝓝 c, ‖f z‖ ≤ M) : AnalyticOnNhd ℂ f U := by
  apply analyticOnNhd_pi_of_analyticOnNhd_update hU _ hf
  apply continuousOn_of_forall_continuousAt
  intro c hc
  obtain ⟨r, hr, C, hC⟩ := exists_lipschitzOnWith_of_separately_analytic_locally_bounded
    hU hf hc (hb c hc)
  exact hC.continuousOn.continuousAt (closedBall_mem_nhds _ hr)

end SeveralComplexVariables

end
