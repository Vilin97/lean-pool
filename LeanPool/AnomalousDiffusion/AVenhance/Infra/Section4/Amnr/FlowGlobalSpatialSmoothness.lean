/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.LocalSpatialWords

/-! Extend actual short-time spatial smoothness by the proved flow group law. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- Every fixed-time map of the actual flow is spatially smooth. A finite
subdivision and the actual group law extend the proved short-time result. -/
theorem amnr_flow_spatial_contDiff_infty_global {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {M : ℝ} (hM : 0 ≤ M) (hstate : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    (s t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun x => X t x s) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|t - s| * M + 1)
  have hNpos : 0 < (N : ℝ) := by have := mul_nonneg (abs_nonneg (t - s)) hM; linarith
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  let d := (t - s) / (N : ℝ)
  have hd : |d| * M < 1 := by
    dsimp [d]
    rw [abs_div, abs_of_pos hNpos, div_mul_eq_mul_div, div_lt_iff₀ hNpos, one_mul]
    linarith
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  have hLip : ∃ L : ℝ, ∀ u x y, ‖b u x - b u y‖ ≤ L * ‖x - y‖ := ⟨L, hL⟩
  have hmaps (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun x => X (s + (j : ℝ) * d) x s) := by
    induction j with
    | zero =>
      have he : (fun x => X (s + (0 : ℝ) * d) x s) = id := by
        funext x
        simpa using hX.1 x s
      simp only [Nat.cast_zero]
      rw [he]
      exact contDiff_id
    | succ j ih =>
      let u := s + (j : ℝ) * d
      let v := s + ((j + 1 : ℕ) : ℝ) * d
      have hvu : v - u = d := by dsimp [v, u]; push_cast; ring
      have hsmall : (max u v - min u v) * M < 1 := by rw [max_sub_min_eq_abs, hvu]; exact hd
      have hstep := amnr_flow_spatial_contDiff_infty_of_short hb hX hM hstate
        (s := u) (t := v) min_le_max ⟨min_le_left _ _, le_max_left _ _⟩
        ⟨min_le_right _ _, le_max_right _ _⟩ hsmall
      have hh := hstep.comp ih
      have he : (fun x => X v x u) ∘ (fun x => X u x s) = fun x => X v x s := by
        funext x
        exact flow_group_law b hLip hX x s u v
      rw [he] at hh
      exact hh
  have hfinish : s + (N : ℝ) * d = t := by dsimp [d]; field_simp; ring
  simpa only [hfinish] using hmaps N

/-- The actual flow is jointly smooth in target time and initial point at
all times, using a fixed intermediate time for the local joint argument. -/
theorem amnr_flow_joint_contDiff_infty_global {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {M : ℝ} (hM : 0 ≤ M) (hstate : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    (s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => X z.1 z.2 s) := by
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  have hLip : ∃ L : ℝ, ∀ u x y, ‖b u x - b u y‖ ≤ L * ‖x - y‖ := ⟨L, hL⟩
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have hslice := amnr_flow_spatial_contDiff_infty_global hb hX hM hstate s z.1
  have hR : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ℝ × Vec 2 => (y.1, X z.1 y.2 s)) z :=
    contDiffAt_fst.prodMk (hslice.contDiffAt.comp z contDiffAt_snd)
  have hF := amnr_flow_contDiffAt_joint_of_short hb hX hM hstate z.1 z.1
    (X z.1 z.2 s) (by simp)
  have hh := hF.comp z hR
  have he : (fun y : ℝ × Vec 2 => X y.1 y.2 z.1) ∘
      (fun y : ℝ × Vec 2 => (y.1, X z.1 y.2 s)) = fun y : ℝ × Vec 2 => X y.1 y.2 s := by
    funext y
    exact flow_group_law b hLip hX y.2 s z.1 y.1
  rwa [he] at hh

end AVenhance.Infra.Section4
