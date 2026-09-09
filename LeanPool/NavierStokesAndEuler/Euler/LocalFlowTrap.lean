/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-! Short-time confinement uses a velocity bound only inside the trapping ball. -/

@[expose] public section


noncomputable section

namespace EulerComparatorLocalFlow

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The mean-value bound up to both endpoints, with derivatives required only in the interior. -/
theorem norm_sub_le_mul_of_hasDerivAt_Ioo (X X' : ℝ → E) {T M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hX : ContinuousOn X (Icc 0 T))
    (hderiv : ∀ s ∈ Ioo 0 T, HasDerivAt X (X' s) s)
    (hbound : ∀ s ∈ Ioo 0 T, ‖X' s‖ ≤ M) :
    ‖X T - X 0‖ ≤ M * T := by
  have hlip : LipschitzOnWith ⟨M, hM⟩ X (Ioo 0 T) :=
    (convex_Ioo (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun s hs => (hderiv s hs).hasDerivWithinAt) (fun s hs => hbound s hs)
  have hcl : closure (Ioo (0 : ℝ) T) = Icc 0 T := closure_Ioo hT.ne
  have hlipclosed : LipschitzOnWith ⟨M, hM⟩ X (Icc 0 T) := by
    rw [← hcl]
    exact LipschitzOnWith.closure (by simpa only [hcl] using hX) hlip
  have h := lipschitzOnWith_iff_dist_le_mul.mp hlipclosed
    T (right_mem_Icc.mpr hT.le) 0 (left_mem_Icc.mpr hT.le)
  change dist (X T) (X 0) ≤ M * dist T 0 at h
  simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos hT] using h

/-- A trajectory cannot first leave the ball before the local speed budget is exhausted.
No bound on the velocity outside `‖x‖ ≤ B` is used. -/
theorem norm_lt_of_local_speed_bound (X : ℝ → E) (V : ℝ → E → E)
    {δ A B M : ℝ} (hM : 0 ≤ M) (hAB : A < B) (hsmall : δ * M < B - A)
    (hX : ContinuousOn X (Icc 0 δ))
    (hderiv : ∀ s ∈ Ioo 0 δ, HasDerivAt X (V s (X s)) s)
    (hinitial : ‖X 0‖ ≤ A)
    (hbound : ∀ s ∈ Icc 0 δ, ∀ x : E, ‖x‖ ≤ B → ‖V s x‖ ≤ M) :
    ∀ t ∈ Icc 0 δ, ‖X t‖ < B := by
  intro t ht
  by_contra hnot
  let S : Set ℝ := {s ∈ Icc 0 δ | B ≤ ‖X s‖}
  have hSc : IsCompact S :=
    isCompact_Icc.of_isClosed_subset
      (isClosed_Icc.isClosed_le continuousOn_const hX.norm) (fun _ h => h.1)
  have hSn : S.Nonempty := ⟨t, ht, le_of_not_gt hnot⟩
  obtain ⟨s, hs⟩ := hSc.exists_isLeast hSn
  have hsI : s ∈ Icc 0 δ := hs.1.1
  have hsbound : B ≤ ‖X s‖ := hs.1.2
  have hspos : 0 < s := by
    have hsne : s ≠ 0 := by
      intro h
      rw [h] at hsbound
      exact (not_le_of_gt hAB) (hsbound.trans hinitial)
    exact lt_of_le_of_ne hsI.1 hsne.symm
  have hinside : ∀ r ∈ Ioo 0 s, ‖X r‖ < B := by
    intro r hr
    by_contra hn
    have hrS : r ∈ S := ⟨⟨hr.1.le, hr.2.le.trans hsI.2⟩, le_of_not_gt hn⟩
    exact (not_le_of_gt hr.2) (hs.2 hrS)
  have hdisplacement : ‖X s - X 0‖ ≤ M * s :=
    norm_sub_le_mul_of_hasDerivAt_Ioo X (fun r => V r (X r)) hspos hM
      (hX.mono (fun _ hr => ⟨hr.1, hr.2.trans hsI.2⟩))
      (fun r hr => hderiv r ⟨hr.1, hr.2.trans_le hsI.2⟩)
      (fun r hr => hbound r ⟨hr.1.le, hr.2.le.trans hsI.2⟩ (X r) (hinside r hr).le)
  have hnorm : ‖X s‖ ≤ M * s + A := by
    calc
      ‖X s‖ = ‖(X s - X 0) + X 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖X s - X 0‖ + ‖X 0‖ := norm_add_le _ _
      _ ≤ M * s + A := add_le_add hdisplacement hinitial
  have hbudget : M * s ≤ M * δ := mul_le_mul_of_nonneg_left hsI.2 hM
  nlinarith

omit [NormedSpace ℝ E] in
/-- Compactness supplies a common speed bound and positive time budget on a fixed ball. -/
theorem exists_local_speed_budget [ProperSpace E] (u : ℝ → E → E) {A B : ℝ}
    (hAB : A < B)
    (hu : ContinuousOn (Function.uncurry u)
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : E) B)) :
    ∃ δ M : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < M ∧ δ * M < B - A ∧
      ∀ s ∈ Icc 0 δ, ∀ x : E, ‖x‖ ≤ B → ‖u s x‖ ≤ M := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : E) B)).exists_bound_of_continuousOn hu
  let M : ℝ := max C 0 + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let δ : ℝ := min 1 ((B - A) / (2 * M))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos (sub_pos.mpr hAB) (by positivity))
  have hδone : δ ≤ 1 := min_le_left _ _
  have hsmall : δ * M < B - A := by
    have hb : δ * M ≤ (B - A) / 2 := by
      calc
        δ * M ≤ ((B - A) / (2 * M)) * M :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hM.le
        _ = (B - A) / 2 := by field_simp
    linarith
  refine ⟨δ, M, hδ, hδone, hM, hsmall, ?_⟩
  intro s hs x hx
  have hxball : x ∈ Metric.closedBall (0 : E) B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hc := hC (s, x) ⟨⟨hs.1, hs.2.trans hδone⟩, hxball⟩
  have hCM : C ≤ M := (le_max_left C 0).trans (by dsimp [M]; linarith)
  exact hc.trans hCM

end EulerComparatorLocalFlow
