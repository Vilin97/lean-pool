/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.PeriodicSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.VariationalEquation
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Second-order Taylor control for smooth periodic vector fields. -/

@[expose] public section

open Homogenization
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

/-- A fixed-time spatial slice of a smooth periodic field has a globally
bounded second derivative, with a bound independent of the chosen time. -/
theorem exists_global_spatialSecondFDeriv_bound
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x,
      ‖iteratedFDeriv ℝ 2 (fun y => b t y) x‖ ≤ C := by
  obtain ⟨C₀, _, h₀⟩ := exists_global_iteratedFDeriv_bound hb 0
  obtain ⟨C₁, _, h₁⟩ := exists_global_iteratedFDeriv_bound hb 1
  obtain ⟨C₂, _, h₂⟩ := exists_global_iteratedFDeriv_bound hb 2
  let C : ℝ := max C₀ (max C₁ C₂)
  refine ⟨2 * C, by positivity, ?_⟩
  intro t x
  let F : ℝ × Vec 2 → Vec 2 := Function.uncurry b
  let g : Vec 2 → ℝ × Vec 2 := fun y => (t, y)
  have hF : ContDiff ℝ ∞ F := hb.smooth
  have hg : ContDiff ℝ ∞ g := by fun_prop
  have hC : ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i F (g x)‖ ≤ C := by
    intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi' with rfl | rfl | rfl
    · change ‖iteratedFDeriv ℝ 0 (Function.uncurry b) (t, x)‖ ≤ C
      exact (h₀ (t, x)).trans (le_max_left _ _)
    · change ‖iteratedFDeriv ℝ 1 (Function.uncurry b) (t, x)‖ ≤ C
      exact (h₁ (t, x)).trans <| le_trans (le_max_left _ _) (le_max_right _ _)
    · change ‖iteratedFDeriv ℝ 2 (Function.uncurry b) (t, x)‖ ≤ C
      exact (h₂ (t, x)).trans <| le_trans (le_max_right _ _) (le_max_right _ _)
  have hgD : ∀ y, fderiv ℝ g y = ContinuousLinearMap.inr ℝ ℝ (Vec 2) := by
    intro y
    exact (hasFDerivAt_prodMk_right t y).fderiv
  have hD : ∀ i, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i g x‖ ≤ (1 : ℝ) ^ i := by
    intro i hi₁ hi₂
    have hi' : i = 1 ∨ i = 2 := by omega
    rcases hi' with rfl | rfl
    · rw [norm_iteratedFDeriv_one, hgD]
      simpa using (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ) (E := ℝ) (F := Vec 2))
    · have hzero : iteratedFDeriv ℝ 2 g x = 0 := by
        rw [iteratedFDeriv_succ_eq_comp_right]
        rw [show (fun y => fderiv ℝ g y) =
          fun _ => ContinuousLinearMap.inr ℝ ℝ (Vec 2) from funext hgD]
        rw [iteratedFDeriv_const_of_ne (by norm_num : (1 : ℕ) ≠ 0)]
        exact (continuousMultilinearCurryRightEquiv' ℝ 1 (Vec 2) (ℝ × Vec 2)).symm.map_zero
      rw [hzero]
      norm_num
  have hcomp := norm_iteratedFDeriv_comp_le hF hg (by norm_num) x hC hD
  have hfg : F ∘ g = fun y => b t y := by
    funext y
    rfl
  rw [hfg] at hcomp
  simpa [C, Nat.factorial] using hcomp

/-- A fixed-time spatial slice of a smooth periodic field has a globally
bounded third derivative, with a bound independent of the chosen time. -/
theorem exists_global_spatialThirdFDeriv_bound
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x,
      ‖iteratedFDeriv ℝ 3 (fun y => b t y) x‖ ≤ C := by
  obtain ⟨C₀, _, h₀⟩ := exists_global_iteratedFDeriv_bound hb 0
  obtain ⟨C₁, _, h₁⟩ := exists_global_iteratedFDeriv_bound hb 1
  obtain ⟨C₂, _, h₂⟩ := exists_global_iteratedFDeriv_bound hb 2
  obtain ⟨C₃, _, h₃⟩ := exists_global_iteratedFDeriv_bound hb 3
  let C : ℝ := max C₀ (max C₁ (max C₂ C₃))
  refine ⟨6 * C, by positivity, ?_⟩
  have hC₀' : C₀ ≤ C := by dsimp [C]; exact le_max_left _ _
  have hC₁' : C₁ ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left C₁ (max C₂ C₃))
      (le_max_right C₀ (max C₁ (max C₂ C₃)))
  have hC₂' : C₂ ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left C₂ C₃) <| le_trans
      (le_max_right C₁ (max C₂ C₃)) (le_max_right C₀ (max C₁ (max C₂ C₃)))
  have hC₃' : C₃ ≤ C := by
    dsimp [C]
    exact le_trans (le_max_right C₂ C₃) <| le_trans
      (le_max_right C₁ (max C₂ C₃)) (le_max_right C₀ (max C₁ (max C₂ C₃)))
  intro t x
  let F : ℝ × Vec 2 → Vec 2 := Function.uncurry b
  let g : Vec 2 → ℝ × Vec 2 := fun y => (t, y)
  have hF : ContDiff ℝ ∞ F := hb.smooth
  have hg : ContDiff ℝ ∞ g := by fun_prop
  have hC : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i F (g x)‖ ≤ C := by
    intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi' with rfl | rfl | rfl | rfl
    · change ‖iteratedFDeriv ℝ 0 (Function.uncurry b) (t, x)‖ ≤ C
      exact (h₀ (t, x)).trans hC₀'
    · change ‖iteratedFDeriv ℝ 1 (Function.uncurry b) (t, x)‖ ≤ C
      exact (h₁ (t, x)).trans hC₁'
    · change ‖iteratedFDeriv ℝ 2 (Function.uncurry b) (t, x)‖ ≤ C
      exact (h₂ (t, x)).trans hC₂'
    · change ‖iteratedFDeriv ℝ 3 (Function.uncurry b) (t, x)‖ ≤ C
      exact (h₃ (t, x)).trans hC₃'
  have hgD : ∀ y, fderiv ℝ g y = ContinuousLinearMap.inr ℝ ℝ (Vec 2) := by
    intro y
    exact (hasFDerivAt_prodMk_right t y).fderiv
  have hD : ∀ i, 1 ≤ i → i ≤ 3 →
      ‖iteratedFDeriv ℝ i g x‖ ≤ (1 : ℝ) ^ i := by
    intro i hi₁ hi₃
    have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi' with rfl | rfl | rfl
    · rw [norm_iteratedFDeriv_one, hgD]
      simpa using (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ)
        (E := ℝ) (F := Vec 2))
    · have hzero : iteratedFDeriv ℝ 2 g x = 0 := by
        rw [iteratedFDeriv_succ_eq_comp_right]
        rw [show (fun y => fderiv ℝ g y) =
          fun _ => ContinuousLinearMap.inr ℝ ℝ (Vec 2) from funext hgD]
        rw [iteratedFDeriv_const_of_ne (by norm_num : (1 : ℕ) ≠ 0)]
        exact (continuousMultilinearCurryRightEquiv' ℝ 1 (Vec 2)
          (ℝ × Vec 2)).symm.map_zero
      rw [hzero]
      norm_num
    · have hzero : iteratedFDeriv ℝ 3 g x = 0 := by
        rw [iteratedFDeriv_succ_eq_comp_right]
        rw [show (fun y => fderiv ℝ g y) =
          fun _ => ContinuousLinearMap.inr ℝ ℝ (Vec 2) from funext hgD]
        rw [iteratedFDeriv_const_of_ne (by norm_num : (2 : ℕ) ≠ 0)]
        exact (continuousMultilinearCurryRightEquiv' ℝ 2 (Vec 2)
          (ℝ × Vec 2)).symm.map_zero
      rw [hzero]
      norm_num
  have hcomp := norm_iteratedFDeriv_comp_le hF hg (by norm_num) x hC hD
  have hfg : F ∘ g = fun y => b t y := by
    funext y
    rfl
  rw [hfg] at hcomp
  simpa [C, Nat.factorial] using hcomp

/-- After fixing the direction acted on by the Jacobian, its first-order
Taylor remainder is quadratic, uniformly in time and base point. -/
theorem exists_global_spatialFDeriv_apply_taylor_remainder
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x y v,
      ‖jointSpatialFDeriv b t y v - jointSpatialFDeriv b t x v -
        fderiv ℝ (fun z => jointSpatialFDeriv b t z v) x (y - x)‖ ≤
          C * ‖v‖ * ‖y - x‖ * ‖y - x‖ := by
  obtain ⟨C, hC₀, hC⟩ := exists_global_spatialThirdFDeriv_bound hb
  refine ⟨C, hC₀, ?_⟩
  intro t x y v
  let g : Vec 2 → Vec 2 := fun z => b t z
  let A : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun z => fderiv ℝ g z
  let f : Vec 2 → Vec 2 := fun z => A z v
  have hg : ContDiff ℝ ∞ g := by
    have hmap : ContDiff ℝ ∞ (fun z : Vec 2 => (t, z)) :=
      contDiff_const.prodMk contDiff_id
    exact hb.smooth.comp hmap
  have hA : ContDiff ℝ 2 A := by
    change ContDiff ℝ 2 (fderiv ℝ g)
    exact hg.fderiv_right (m := 2) (by norm_num)
  have hf : ContDiff ℝ 2 f := by
    let evalV : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] Vec 2 :=
      (ContinuousLinearMap.apply ℝ (Vec 2)) v
    change ContDiff ℝ 2 (evalV ∘ A)
    exact evalV.contDiff.comp hA
  have hsecond : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ ‖v‖ * C := by
    intro z
    have happly := norm_iteratedFDeriv_clm_apply_const
      (f := A) (c := v) (x := z) (N := 2) (n := 2)
      hA.contDiffAt (by norm_num)
    have hAthird : ‖iteratedFDeriv ℝ 2 A z‖ =
        ‖iteratedFDeriv ℝ 3 g z‖ := by
      change ‖iteratedFDeriv ℝ 2 (fderiv ℝ g) z‖ = _
      rw [norm_iteratedFDeriv_fderiv]
    calc
      ‖iteratedFDeriv ℝ 2 f z‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ 2 A z‖ := by
        simpa [f] using happly
      _ ≤ ‖v‖ * C := by
        rw [hAthird]
        exact mul_le_mul_of_nonneg_left (hC t z) (norm_nonneg v)
  have hdf : Differentiable ℝ (fderiv ℝ f) := by
    exact (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdfderiv : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C * ‖v‖ := by
    intro z
    calc
      ‖fderiv ℝ (fderiv ℝ f) z‖ =
          ‖iteratedFDeriv ℝ 2 f z‖ := by
            rw [← norm_iteratedFDeriv_one (fderiv ℝ f), norm_iteratedFDeriv_fderiv]
      _ ≤ ‖v‖ * C := hsecond z
      _ = C * ‖v‖ := by ring
  have hLip : ∀ z, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤
      (C * ‖v‖) * ‖z - x‖ := by
    intro z
    exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hdf z) (fun z _ => hdfderiv z) (Set.mem_univ _) (Set.mem_univ _)
  let S : Set (Vec 2) := Metric.closedBall x ‖y - x‖
  have hS : Convex ℝ S := convex_closedBall _ _
  have hxS : x ∈ S := by simp [S, Metric.mem_closedBall]
  have hyS : y ∈ S := by
    simp [S, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
  have hLipOn : ∀ z ∈ S, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤
      (C * ‖v‖) * ‖y - x‖ := by
    intro z hz
    have hz' : ‖z - x‖ ≤ ‖y - x‖ := by
      simpa [S, Metric.mem_closedBall, dist_eq_norm] using hz
    exact (hLip z).trans (mul_le_mul_of_nonneg_left hz' (by positivity))
  have hTaylor := hS.norm_image_sub_le_of_norm_fderiv_le'
    (f := f) (φ := fderiv ℝ f x)
    (fun z _ => hf.differentiable (by norm_num) z)
    hLipOn hxS hyS
  have hslice (z : Vec 2) : jointSpatialFDeriv b t z = A z :=
    jointSpatialFDeriv_eq_slice hb t z
  simpa [hslice, f, mul_assoc, mul_comm, mul_left_comm] using hTaylor

/-- A globally quadratic remainder estimate for the first-order Taylor
approximation of a smooth periodic vector field in space. -/
theorem exists_global_smoothPeriodicField_taylor_remainder
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x y,
      ‖b t y - b t x - fderiv ℝ (fun z => b t z) x (y - x)‖ ≤
        C * ‖y - x‖ * ‖y - x‖ := by
  obtain ⟨C, hC₀, hC⟩ := exists_global_spatialSecondFDeriv_bound hb
  refine ⟨C, hC₀, ?_⟩
  intro t x y
  let f : Vec 2 → Vec 2 := fun z => b t z
  have hg : ContDiff ℝ ∞ (fun z : Vec 2 => (t, z)) :=
    contDiff_const.prodMk contDiff_id
  have hf : ContDiff ℝ ∞ f := by
    exact hb.smooth.comp hg
  have hdf : Differentiable ℝ (fderiv ℝ f) := by
    exact (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdfderiv : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C := by
    intro z
    rw [← norm_iteratedFDeriv_one (fderiv ℝ f), norm_iteratedFDeriv_fderiv]
    exact hC t z
  have hLip : ∀ z, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * ‖z - x‖ := by
    intro z
    exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hdf z) (fun z _ => hdfderiv z) (Set.mem_univ _) (Set.mem_univ _)
  let S : Set (Vec 2) := Metric.closedBall x ‖y - x‖
  have hS : Convex ℝ S := convex_closedBall _ _
  have hxS : x ∈ S := by simp [S, Metric.mem_closedBall]
  have hyS : y ∈ S := by
    simp [S, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
  have hLipOn : ∀ z ∈ S, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * ‖y - x‖ := by
    intro z hz
    have hz' : ‖z - x‖ ≤ ‖y - x‖ := by
      simpa [S, Metric.mem_closedBall, dist_eq_norm] using hz
    exact (hLip z).trans (mul_le_mul_of_nonneg_left hz' hC₀)
  have hTaylor := hS.norm_image_sub_le_of_norm_fderiv_le'
    (f := f) (φ := fderiv ℝ f x)
    (fun z _ => hf.differentiable (by norm_num) z)
    hLipOn hxS hyS
  simpa [f, mul_assoc, mul_comm, mul_left_comm] using hTaylor

/-- The spatial derivative of a smooth periodic field is globally Lipschitz
in space, uniformly in time. -/
theorem exists_global_spatialFDeriv_lipschitz
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x y,
      ‖jointSpatialFDeriv b t x - jointSpatialFDeriv b t y‖ ≤ C * ‖x - y‖ := by
  obtain ⟨C, hC₀, hC⟩ := exists_global_spatialSecondFDeriv_bound hb
  refine ⟨C, hC₀, ?_⟩
  intro t x y
  let f : Vec 2 → Vec 2 := fun z => b t z
  have hf : ContDiff ℝ ∞ f := by
    have hmap : ContDiff ℝ ∞ (fun z : Vec 2 => (t, z)) :=
      contDiff_const.prodMk contDiff_id
    exact hb.smooth.comp hmap
  have hdf : Differentiable ℝ (fderiv ℝ f) := by
    exact (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdfderiv : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C := by
    intro z
    rw [← norm_iteratedFDeriv_one (fderiv ℝ f), norm_iteratedFDeriv_fderiv]
    exact hC t z
  have hLip : ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x - y‖ := by
    exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hdf z) (fun z _ => hdfderiv z) (Set.mem_univ _) (Set.mem_univ _)
  rw [jointSpatialFDeriv_eq_slice hb t x, jointSpatialFDeriv_eq_slice hb t y]
  exact hLip

end AVenhance.Infra.Flow
