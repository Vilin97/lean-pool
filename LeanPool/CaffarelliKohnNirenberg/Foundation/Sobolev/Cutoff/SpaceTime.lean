/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Space-time cutoffs

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent module combines the ball cutoff with a smooth
one-dimensional time cutoff in the `CKN` namespace.

## Main definitions

* `timeCutoff`: a smooth cutoff equal to one on the backward time interval
  `[t₀ - r², t₀]`.
* `spaceTimeCutoff`: the product `η(x) χ(t)`.

## Main results

* `timeCutoff_smooth`, `timeCutoff_eq_one_on`, and
  `timeCutoff_support_subset` give the temporal cutoff properties.
* `timeCutoff_abs_deriv_le` gives the explicit bound
  `32 / (R² - r²)`.
* `spaceTimeCutoff_smooth`, `spaceTimeCutoff_eq_one_on`, and
  `spaceTimeCutoff_support_subset` give the product cutoff properties.
-/

public section

open Set

noncomputable section

namespace CKN

/-- Gap between the squared inner and outer radii in the temporal cutoff. -/
def timeGap (r R : ℝ) : ℝ :=
  R ^ 2 - r ^ 2

private theorem timeGap_pos {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) :
    0 < timeGap r R := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hprod :
      0 < (R - r) * (R + r) :=
    mul_pos (sub_pos.mpr hrR) (add_pos_of_pos_of_nonneg hR hr)
  dsimp [timeGap]
  nlinarith only [hprod]

/-- Rising temporal cutoff at the backward end of the cylinder. -/
def timeCutoffLeft
    (t₀ r R t : ℝ) : ℝ :=
  smoothTransitionProfile
    ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
      (timeGap r R / 2))

/-- Falling temporal cutoff extending slightly beyond the cylinder's terminal time. -/
def timeCutoffRight
    (t₀ r R t : ℝ) : ℝ :=
  smoothTransitionProfile
    ((t₀ + timeGap r R / 2 - t) /
      (timeGap r R / 2))

/-- A smooth temporal cutoff with an interior support collar. -/
def timeCutoff
    (t₀ r R t : ℝ) : ℝ :=
  timeCutoffLeft t₀ r R t * timeCutoffRight t₀ r R t

private theorem timeCutoffLeft_smooth
    {t₀ r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    ContDiff ℝ (⊤ : ℕ∞) (timeCutoffLeft t₀ r R) := by
  have hgap : 0 < timeGap r R := timeGap_pos hr hrR
  apply smoothTransitionProfile.smooth.comp
  simpa [timeCutoffLeft] using
    ((contDiff_id.sub
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : ℝ => t₀ - R ^ 2 + timeGap r R / 2))).div_const
      (timeGap r R / 2))

private theorem timeCutoffRight_smooth
    {t₀ r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    ContDiff ℝ (⊤ : ℕ∞) (timeCutoffRight t₀ r R) := by
  have hgap : 0 < timeGap r R := timeGap_pos hr hrR
  apply smoothTransitionProfile.smooth.comp
  simpa [timeCutoffRight] using
    ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : ℝ => t₀ + timeGap r R / 2)).sub contDiff_id).div_const
      (timeGap r R / 2)

/-- The temporal cutoff is smooth to every order. -/
theorem timeCutoff_smooth
    {t₀ r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    ContDiff ℝ (⊤ : ℕ∞) (timeCutoff t₀ r R) := by
  exact (timeCutoffLeft_smooth hr hrR).mul
    (timeCutoffRight_smooth hr hrR)

/-- The temporal cutoff is nonnegative. -/
theorem timeCutoff_nonneg
    (t₀ r R t : ℝ) :
    0 ≤ timeCutoff t₀ r R t := by
  apply mul_nonneg
  · exact smoothTransitionProfile.nonneg _
  · exact smoothTransitionProfile.nonneg _

/-- The temporal cutoff is at most one. -/
theorem timeCutoff_le_one
    (t₀ r R t : ℝ) :
    timeCutoff t₀ r R t ≤ 1 := by
  calc
    timeCutoff t₀ r R t ≤
        1 * smoothTransitionProfile
          ((t₀ + timeGap r R / 2 - t) / (timeGap r R / 2)) :=
      mul_le_mul_of_nonneg_right
        (smoothTransitionProfile.le_one _) (smoothTransitionProfile.nonneg _)
    _ ≤ 1 * 1 :=
      mul_le_mul_of_nonneg_left (smoothTransitionProfile.le_one _)
        (by norm_num)
    _ = 1 := by norm_num

private theorem timeCutoffLeft_eq_one
    {t₀ r R t : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (ht : t₀ - r ^ 2 ≤ t) :
    timeCutoffLeft t₀ r R t = 1 := by
  apply smoothTransitionProfile.one_of_one_le
  have hgap : 0 < timeGap r R := timeGap_pos hr hrR
  have hgap' : 0 < R ^ 2 - r ^ 2 := by simpa [timeGap] using hgap
  have hden : 0 < (R ^ 2 - r ^ 2) / 2 := by linarith only [hgap']
  dsimp [timeCutoffLeft, timeGap]
  apply (le_div_iff₀ hden).2
  nlinarith only [ht, hgap']

private theorem timeCutoffRight_eq_one
    {t₀ r R t : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (ht : t ≤ t₀) :
    timeCutoffRight t₀ r R t = 1 := by
  apply smoothTransitionProfile.one_of_one_le
  have hgap : 0 < timeGap r R := timeGap_pos hr hrR
  have hgap' : 0 < R ^ 2 - r ^ 2 := by simpa [timeGap] using hgap
  have hden : 0 < (R ^ 2 - r ^ 2) / 2 := by linarith only [hgap']
  dsimp [timeCutoffRight, timeGap]
  apply (le_div_iff₀ hden).2
  nlinarith only [ht, hgap']

/-- The temporal cutoff equals one on `[t₀ - r², t₀]`. -/
theorem timeCutoff_eq_one_on
    {t₀ r R t : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (ht : t ∈ Icc (t₀ - r ^ 2) t₀) :
    timeCutoff t₀ r R t = 1 := by
  rw [timeCutoff, timeCutoffLeft_eq_one hr hrR ht.1,
    timeCutoffRight_eq_one hr hrR ht.2]
  norm_num

private theorem timeCutoffLeft_eq_zero_of_le
    {t₀ r R t : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (ht : t ≤ t₀ - R ^ 2 + timeGap r R / 2) :
    timeCutoffLeft t₀ r R t = 0 := by
  apply smoothTransitionProfile.zero_of_nonpos
  have hgap : 0 < timeGap r R := timeGap_pos hr hrR
  have hden : 0 < timeGap r R / 2 := by linarith only [hgap]
  rw [div_nonpos_iff]
  exact Or.inr ⟨by linarith only [ht], hden.le⟩

private theorem timeCutoffRight_eq_zero_of_ge
    {t₀ r R t : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (ht : t₀ + timeGap r R / 2 ≤ t) :
    timeCutoffRight t₀ r R t = 0 := by
  apply smoothTransitionProfile.zero_of_nonpos
  have hgap : 0 < timeGap r R := timeGap_pos hr hrR
  have hden : 0 < timeGap r R / 2 := by linarith only [hgap]
  rw [div_nonpos_iff]
  exact Or.inr ⟨by linarith only [ht], hden.le⟩

private theorem timeCutoff_support_subset_Icc
    {t₀ r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    Function.support (timeCutoff t₀ r R) ⊆
      Icc (t₀ - R ^ 2 + timeGap r R / 2)
        (t₀ + timeGap r R / 2) := by
  intro t ht
  constructor
  · by_contra hleft
    have hzero := timeCutoffLeft_eq_zero_of_le hr hrR
      (le_of_lt (lt_of_not_ge hleft))
    exact ht (by simp [timeCutoff, hzero])
  · by_contra hright
    have hzero := timeCutoffRight_eq_zero_of_ge hr hrR
      (le_of_lt (lt_of_not_ge hright))
    exact ht (by simp [timeCutoff, hzero])

/-- The temporal support lies strictly inside the prescribed time interval. -/
theorem timeCutoff_support_subset
    {t₀ r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    Function.support (timeCutoff t₀ r R) ⊆
      Ioo (t₀ - R ^ 2) (t₀ + (R ^ 2 - r ^ 2)) := by
  intro t ht
  have hgap : 0 < timeGap r R := timeGap_pos hr hrR
  have hclosed := timeCutoff_support_subset_Icc hr hrR ht
  have hgap' : 0 < R ^ 2 - r ^ 2 := by
    simpa [timeGap] using hgap
  constructor
  · linarith only [hclosed.1, hgap]
  · dsimp [timeGap] at hclosed ⊢
    linarith only [hclosed.2, hgap']

private theorem timeCutoffLeft_hasDerivAt
    {t₀ r R t : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    HasDerivAt (timeCutoffLeft t₀ r R) (
        deriv smoothTransitionProfile
            ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
              (timeGap r R / 2)) /
          (timeGap r R / 2)) t := by
  have hgap : 0 < timeGap r R := timeGap_pos hr hrR
  have hprofile :=
    (smoothTransitionProfile.smooth.differentiable (by simp)
      ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
        (timeGap r R / 2))).hasDerivAt
  have harg :=
    ((hasDerivAt_id t).sub_const
      (t₀ - R ^ 2 + timeGap r R / 2)).div_const
        (timeGap r R / 2)
  convert hprofile.comp t harg using 1
  · funext x
    rfl
  · ring

private theorem timeCutoffRight_hasDerivAt
    {t₀ r R t : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    HasDerivAt (timeCutoffRight t₀ r R) (-
        deriv smoothTransitionProfile
            ((t₀ + timeGap r R / 2 - t) /
              (timeGap r R / 2)) /
          (timeGap r R / 2)) t := by
  have hgap : 0 < timeGap r R := timeGap_pos hr hrR
  have hprofile :=
    (smoothTransitionProfile.smooth.differentiable (by simp)
      ((t₀ + timeGap r R / 2 - t) /
        (timeGap r R / 2))).hasDerivAt
  have harg :=
    ((hasDerivAt_const t (t₀ + timeGap r R / 2)).sub
      (hasDerivAt_id t)).div_const
        (timeGap r R / 2)
  convert hprofile.comp t harg using 1
  · funext x
    rfl
  · ring

private theorem timeCutoff_hasDerivAt
    {t₀ r R t : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    HasDerivAt (timeCutoff t₀ r R)
      ((deriv smoothTransitionProfile
          ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
            (timeGap r R / 2)) /
          (timeGap r R / 2)) *
        smoothTransitionProfile
          ((t₀ + timeGap r R / 2 - t) /
            (timeGap r R / 2)) +
      smoothTransitionProfile
          ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
            (timeGap r R / 2)) *
        (-deriv smoothTransitionProfile
          ((t₀ + timeGap r R / 2 - t) /
            (timeGap r R / 2)) /
          (timeGap r R / 2))) t := by
  change HasDerivAt
    (fun x => timeCutoffLeft t₀ r R x * timeCutoffRight t₀ r R x) _ t
  convert (timeCutoffLeft_hasDerivAt hr hrR).mul
      (timeCutoffRight_hasDerivAt hr hrR) using 1
  all_goals simp only [timeCutoffLeft, timeCutoffRight]

private theorem timeCutoffLeft_abs_deriv_le
    {t₀ r R t : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    |deriv (timeCutoffLeft t₀ r R) t| ≤
      16 / timeGap r R := by
  have hgap : 0 < timeGap r R := timeGap_pos hr hrR
  have hden : 0 < timeGap r R / 2 := by linarith only [hgap]
  rw [(timeCutoffLeft_hasDerivAt hr hrR).deriv, abs_div,
    abs_of_pos hden]
  calc
    |deriv smoothTransitionProfile
          ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
            (timeGap r R / 2))| / (timeGap r R / 2) ≤
        8 / (timeGap r R / 2) :=
      div_le_div_of_nonneg_right
        (smoothTransitionProfile.abs_deriv_le_eight _) hden.le
    _ = 16 / timeGap r R := by field_simp [hgap.ne']; ring

private theorem timeCutoffRight_abs_deriv_le
    {t₀ r R t : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    |deriv (timeCutoffRight t₀ r R) t| ≤
      16 / timeGap r R := by
  have hgap : 0 < timeGap r R := timeGap_pos hr hrR
  have hden : 0 < timeGap r R / 2 := by linarith only [hgap]
  rw [(timeCutoffRight_hasDerivAt hr hrR).deriv, abs_div, abs_neg,
    abs_of_pos hden]
  calc
    |deriv smoothTransitionProfile
          ((t₀ + timeGap r R / 2 - t) /
            (timeGap r R / 2))| / (timeGap r R / 2) ≤
        8 / (timeGap r R / 2) :=
      div_le_div_of_nonneg_right
        (smoothTransitionProfile.abs_deriv_le_eight _) hden.le
    _ = 16 / timeGap r R := by field_simp [hgap.ne']; ring

/-- The temporal derivative obeys `|χ'| ≤ 32 / (R² - r²)`. -/
theorem timeCutoff_abs_deriv_le
    {t₀ r R t : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    |deriv (timeCutoff t₀ r R) t| ≤
      32 / (R ^ 2 - r ^ 2) := by
  have hgap : 0 < timeGap r R := timeGap_pos hr hrR
  rw [(timeCutoff_hasDerivAt hr hrR).deriv]
  calc
    |(deriv smoothTransitionProfile
          ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
            (timeGap r R / 2)) /
          (timeGap r R / 2)) *
        smoothTransitionProfile
          ((t₀ + timeGap r R / 2 - t) /
            (timeGap r R / 2)) +
      smoothTransitionProfile
          ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
            (timeGap r R / 2)) *
        (-deriv smoothTransitionProfile
          ((t₀ + timeGap r R / 2 - t) /
            (timeGap r R / 2)) /
          (timeGap r R / 2))| ≤
        |(deriv smoothTransitionProfile
            ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
              (timeGap r R / 2)) /
            (timeGap r R / 2)) *
          smoothTransitionProfile
            ((t₀ + timeGap r R / 2 - t) /
              (timeGap r R / 2))| +
          |smoothTransitionProfile
            ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
              (timeGap r R / 2)) *
            (-deriv smoothTransitionProfile
              ((t₀ + timeGap r R / 2 - t) /
                (timeGap r R / 2)) /
              (timeGap r R / 2))| := by
      exact abs_add_le _ _
    _ =
        |deriv smoothTransitionProfile
            ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
              (timeGap r R / 2)) /
            (timeGap r R / 2)| *
          |smoothTransitionProfile
            ((t₀ + timeGap r R / 2 - t) /
              (timeGap r R / 2))| +
        |smoothTransitionProfile
            ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
              (timeGap r R / 2))| *
          |-deriv smoothTransitionProfile
            ((t₀ + timeGap r R / 2 - t) /
              (timeGap r R / 2)) /
            (timeGap r R / 2)| := by
      rw [abs_mul, abs_mul]
    _ ≤
        |deriv smoothTransitionProfile
            ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
              (timeGap r R / 2)) /
            (timeGap r R / 2)| +
          |-deriv smoothTransitionProfile
            ((t₀ + timeGap r R / 2 - t) /
              (timeGap r R / 2)) /
            (timeGap r R / 2)| := by
      have hleft :
          |smoothTransitionProfile
              ((t₀ + timeGap r R / 2 - t) /
                (timeGap r R / 2))| ≤ 1 := by
        rw [abs_of_nonneg (smoothTransitionProfile.nonneg _)]
        exact smoothTransitionProfile.le_one _
      have hright :
          |smoothTransitionProfile
              ((t - (t₀ - R ^ 2 + timeGap r R / 2)) /
                (timeGap r R / 2))| ≤ 1 := by
        rw [abs_of_nonneg (smoothTransitionProfile.nonneg _)]
        exact smoothTransitionProfile.le_one _
      exact add_le_add
        (by
          simpa using
            (mul_le_mul_of_nonneg_left hleft (abs_nonneg _)))
        (by
          simpa using
            (mul_le_mul_of_nonneg_right hright (abs_nonneg _)))
    _ = |deriv (timeCutoffLeft t₀ r R) t| +
          |deriv (timeCutoffRight t₀ r R) t| := by
      rw [(timeCutoffLeft_hasDerivAt hr hrR).deriv,
        (timeCutoffRight_hasDerivAt hr hrR).deriv]
    _ ≤ 16 / timeGap r R + 16 / timeGap r R :=
      add_le_add (timeCutoffLeft_abs_deriv_le hr hrR)
        (timeCutoffRight_abs_deriv_le hr hrR)
    _ = 32 / (R ^ 2 - r ^ 2) := by
      dsimp [timeGap]
      ring

/-- The product of the spatial and temporal cutoffs. -/
def spaceTimeCutoff {d : ℕ}
    (x₀ : Vec d) (t₀ r R : ℝ) (z : Vec d × ℝ) : ℝ :=
  canonicalBallCutoff x₀ r R z.1 * timeCutoff t₀ r R z.2

/-- The space-time cutoff is smooth to every order. -/
theorem spaceTimeCutoff_smooth {d : ℕ}
    (x₀ : Vec d) (t₀ r R : ℝ) (hr : 0 ≤ r) (hrR : r < R) :
    ContDiff ℝ (⊤ : ℕ∞) (spaceTimeCutoff x₀ t₀ r R) := by
  apply (canonicalBallCutoff_smooth x₀ hr hrR).comp contDiff_fst |>.mul
  exact (timeCutoff_smooth hr hrR).comp contDiff_snd

/-- The space-time cutoff equals one on the spatial-temporal plateau. -/
theorem spaceTimeCutoff_eq_one_on {d : ℕ}
    {x₀ : Vec d} {t₀ r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {z : Vec d × ℝ}
    (hx : z.1 ∈ euclideanBall x₀ r)
    (ht : z.2 ∈ Icc (t₀ - r ^ 2) t₀) :
    spaceTimeCutoff x₀ t₀ r R z = 1 := by
  rw [spaceTimeCutoff, canonicalBallCutoff_eq_one_on_inner hr hrR hx,
    timeCutoff_eq_one_on hr hrR ht]
  norm_num

/-- The support lies in the spatial outer ball and the open time interval. -/
theorem spaceTimeCutoff_support_subset {d : ℕ}
    {x₀ : Vec d} {t₀ r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    Function.support (spaceTimeCutoff x₀ t₀ r R) ⊆
      euclideanBall x₀ R ×ˢ
        Ioo (t₀ - R ^ 2) (t₀ + (R ^ 2 - r ^ 2)) := by
  rintro ⟨x, t⟩ hzt
  constructor
  · apply canonicalBallCutoff_tsupport_subset_outer hr hrR
    apply subset_tsupport
    intro hzero
    apply hzt
    simp [spaceTimeCutoff, hzero]
  · apply timeCutoff_support_subset hr hrR
    intro hzero
    apply hzt
    simp [spaceTimeCutoff, hzero]

end CKN
