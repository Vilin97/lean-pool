/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.OscillationLin34

/-!
# CZStart Bridge Source

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- For a nonnegative real `t`, the `3/2`-power of `t ^ 2` is `t ^ 3`. This is
the exponent identity that turns the pointwise bound `|g| ≤ |v| ^ 2` into the
`L^{3/2}` control by `|v| ^ 3` in the pressure oscillation estimate `eq:Chat`. -/
private lemma sq_rpow_three_halves (t : ℝ) (ht : 0 ≤ t) :
    (t ^ (2 : ℕ)) ^ (3 / 2 : ℝ) = t ^ (3 : ℕ) := by
  rw [(Real.rpow_natCast_mul ht 2 (3 / 2)).symm,
    show ((2 : ℕ) : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

/-- The explicit Euclidean ball `euclideanBall x₀ ρ` is Borel measurable, being
the sublevel set of the continuous function `euclideanSqDist · x₀`. -/
private lemma euclideanBall_measurable_source (x₀ : Vec3) (ρ : ℝ) :
    MeasurableSet (euclideanBall x₀ ρ) := by
  have hopen : IsOpen (euclideanBall x₀ ρ) := by
    change IsOpen {y : Vec3 | euclideanSqDist y x₀ < ρ ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  exact hopen.measurableSet

/-- Pointwise majorant behind the `L^{3/2}` pressure bound. If `g` vanishes off
the ball `B(x₀,ρ)` and `|g| ≤ |v| ^ 2` there, then `|g| ^ (3/2)` is dominated by
the indicator of the ball times `|v| ^ 3`, the `L^3` velocity density of
`eq:Chat`. -/
private lemma abs_rpow_three_halves_le_indicator
    {g : Vec3 → ℝ} {v : Vec3 → Vec3} {x₀ : Vec3} {ρ : ℝ}
    (hzero : ∀ y, y ∉ euclideanBall x₀ ρ → g y = 0)
    (hbound : ∀ y, |g y| ≤ vec3EuclideanNorm (v y) ^ (2 : ℕ)) :
    ∀ y, |g y| ^ (3 / 2 : ℝ) ≤
      (euclideanBall x₀ ρ).indicator
        (fun y => vec3EuclideanNorm (v y) ^ (3 : ℕ)) y := by
  intro y
  by_cases hy : y ∈ euclideanBall x₀ ρ
  · rw [Set.indicator_of_mem hy]
    calc
      |g y| ^ (3 / 2 : ℝ) ≤
          (vec3EuclideanNorm (v y) ^ (2 : ℕ)) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) (hbound y) (by norm_num)
      _ = vec3EuclideanNorm (v y) ^ (3 : ℕ) :=
        sq_rpow_three_halves _ (vec3EuclideanNorm_nonneg (v y))
  · rw [Set.indicator_of_notMem hy]
    have hz : |g y| ^ (3 / 2 : ℝ) = 0 := by
      rw [hzero y hy, abs_zero,
        Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    rw [hz]

/-- Integrability of `|g| ^ (3/2)`: a function vanishing off the ball
`B(x₀,ρ)` with `|g| ≤ |v| ^ 2` there is in `L^{3/2}`, because `|v| ^ 3` is
integrable on that ball. This is the measure-theoretic content of the
scale-invariant `L^{3/2}` pressure energy of `eq:Chat`. -/
private lemma integrable_abs_rpow_three_halves_of_velocity_square_bound
    {g : Vec3 → ℝ} {v : Vec3 → Vec3} {x₀ : Vec3} {ρ : ℝ}
    (hg : AEStronglyMeasurable g volume)
    (hv : IntegrableOn (fun y => vec3EuclideanNorm (v y) ^ (3 : ℕ))
      (euclideanBall x₀ ρ) volume)
    (hzero : ∀ y, y ∉ euclideanBall x₀ ρ → g y = 0)
    (hbound : ∀ y, |g y| ≤ vec3EuclideanNorm (v y) ^ (2 : ℕ)) :
    Integrable (fun y => |g y| ^ (3 / 2 : ℝ)) volume := by
  have hA : MeasurableSet (euclideanBall x₀ ρ) :=
    euclideanBall_measurable_source x₀ ρ
  have hWint : Integrable
      ((euclideanBall x₀ ρ).indicator
        (fun y => vec3EuclideanNorm (v y) ^ (3 : ℕ))) volume :=
    hv.integrable_indicator hA
  have hmeas : AEStronglyMeasurable (fun y => |g y| ^ (3 / 2 : ℝ)) volume :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp_aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hg.norm)
  refine hWint.mono' hmeas (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact abs_rpow_three_halves_le_indicator hzero hbound y

/-- A function `g` that vanishes off the ball `B(x₀,ρ)` and satisfies
`|g| ≤ |v| ^ 2` there lies in `L^{3/2}` whenever the velocity cube
`|v| ^ 3` is integrable on that ball. This is the exponent bookkeeping for the
`L^{3/2}` pressure energy in the oscillation estimate `eq:Chat`. -/
theorem memLp_three_halves_of_velocity_square_bound
    {g : Vec3 → ℝ} {v : Vec3 → Vec3} {x₀ : Vec3} {ρ : ℝ}
    (hg : AEStronglyMeasurable g volume)
    (hv : IntegrableOn (fun y => vec3EuclideanNorm (v y) ^ (3 : ℕ))
      (euclideanBall x₀ ρ) volume)
    (hzero : ∀ y, y ∉ euclideanBall x₀ ρ → g y = 0)
    (hbound : ∀ y, |g y| ≤ vec3EuclideanNorm (v y) ^ (2 : ℕ)) :
    MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
  have hp0 : ENNReal.ofReal (3 / 2 : ℝ) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    norm_num
  have hpTop : ENNReal.ofReal (3 / 2 : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
  have hInt :=
    integrable_abs_rpow_three_halves_of_velocity_square_bound hg hv hzero hbound
  refine (integrable_norm_rpow_iff hg hp0 hpTop).1 ?_
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
    Real.norm_eq_abs] using hInt

/-- Quantitative `L^{3/2}` pressure bound: if `g` vanishes off the ball
`B(x₀,ρ)` and `|g| ≤ |v| ^ 2` there, then the `L^{3/2}` norm of `g` is at most
`(∫_{B(x₀,ρ)} |v| ^ 3) ^ (2/3)`. This is the scale-invariant form in which the
velocity enters the pressure oscillation estimate `eq:Chat`. -/
theorem lpNorm_three_halves_le_of_velocity_square_bound
    {g : Vec3 → ℝ} {v : Vec3 → Vec3} {x₀ : Vec3} {ρ : ℝ}
    (hg : AEStronglyMeasurable g volume)
    (hv : IntegrableOn (fun y => vec3EuclideanNorm (v y) ^ (3 : ℕ))
      (euclideanBall x₀ ρ) volume)
    (hzero : ∀ y, y ∉ euclideanBall x₀ ρ → g y = 0)
    (hbound : ∀ y, |g y| ≤ vec3EuclideanNorm (v y) ^ (2 : ℕ)) :
    lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      (∫ y in euclideanBall x₀ ρ, vec3EuclideanNorm (v y) ^ (3 : ℕ)) ^ (2 / 3 : ℝ) := by
  have hp0 : ENNReal.ofReal (3 / 2 : ℝ) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    norm_num
  have hpTop : ENNReal.ofReal (3 / 2 : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
  have hgmem : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    memLp_three_halves_of_velocity_square_bound hg hv hzero hbound
  have hA : MeasurableSet (euclideanBall x₀ ρ) :=
    euclideanBall_measurable_source x₀ ρ
  have hWint : Integrable
      ((euclideanBall x₀ ρ).indicator
        (fun y => vec3EuclideanNorm (v y) ^ (3 : ℕ))) volume :=
    hv.integrable_indicator hA
  have hInt :=
    integrable_abs_rpow_three_halves_of_velocity_square_bound hg hv hzero hbound
  have hEq : (∫ y, |g y| ^ (3 / 2 : ℝ)) =
      lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume ^ (3 / 2 : ℝ) := by
    have h := integral_rpow_norm_eq_lpNorm_rpow
      (p := ENNReal.ofReal (3 / 2 : ℝ)) (μ := volume) hp0 hpTop hgmem
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
      Real.norm_eq_abs] using h
  have hb : (∫ y, |g y| ^ (3 / 2 : ℝ)) ≤
      ∫ y in euclideanBall x₀ ρ, vec3EuclideanNorm (v y) ^ (3 : ℕ) := by
    calc
      (∫ y, |g y| ^ (3 / 2 : ℝ)) ≤
          ∫ y, (euclideanBall x₀ ρ).indicator
            (fun y => vec3EuclideanNorm (v y) ^ (3 : ℕ)) y :=
        integral_mono hInt hWint (abs_rpow_three_halves_le_indicator hzero hbound)
      _ = ∫ y in euclideanBall x₀ ρ, vec3EuclideanNorm (v y) ^ (3 : ℕ) :=
        integral_indicator hA
  have hkey : lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume ^ (3 / 2 : ℝ) ≤
      ∫ y in euclideanBall x₀ ρ, vec3EuclideanNorm (v y) ^ (3 : ℕ) := by
    rw [← hEq]
    exact hb
  have hfinal : lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume =
      (lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume ^ (3 / 2 : ℝ)) ^
        (2 / 3 : ℝ) := by
    rw [← Real.rpow_mul (lpNorm_nonneg (f := g)
        (p := ENNReal.ofReal (3 / 2 : ℝ)) (μ := volume)) (3 / 2 : ℝ) (2 / 3 : ℝ),
      show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one]
  calc
    lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume =
        (lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume ^ (3 / 2 : ℝ)) ^
          (2 / 3 : ℝ) := hfinal
    _ ≤ (∫ y in euclideanBall x₀ ρ, vec3EuclideanNorm (v y) ^ (3 : ℕ)) ^
          (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (lpNorm_nonneg (f := g)
        (p := ENNReal.ofReal (3 / 2 : ℝ)) (μ := volume)) _) hkey (by norm_num)

end CKN
