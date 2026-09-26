/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPHarmonicCells
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedMarginGeometry
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszSourceQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTCentredSourceCorrection
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Support bounds for centred cutoff corrections

The pressure-gradient construction uses a centred cutoff and its spatial
derivatives.  This file records the pointwise support and correction estimates
needed when the cutoff and its derivatives are contained in the source ball.
The displayed bounds keep the centred velocity tensor and the velocity-gradient
centring term explicit, so they can be consumed by the source estimates.

## Main results
- `centredRawSourceCorrection_abs_le_of_support`: a pointwise triangle bound
  for the centred raw-source correction under support hypotheses.
- `mollifiedBallCutoff_eq_zero_outside_source_ball`: the centred cutoff
  vanishes outside the source ball under the gap condition.
- `spatialDeriv_mollifiedBallCutoff_eq_zero_outside_source_ball`: every spatial
  derivative of that cutoff vanishes there under the same condition.
-/

public section

section

/-!
# Pressure Gradient Origin KPHarmonic Small Cells

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4
/-- The source collar is never smaller than one quarter, while its half-ball
contains the tested small cell. -/
def originHarmonicCellRadius (r : ℝ) : ℝ := max (1/4) (2*r)

end CKN.Core.Step4
end

end

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open CKN CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4
-- The support estimates are grouped immediately after their private arithmetic
-- helper.
/-- A three-term triangle inequality with explicit majorants. -/
private theorem abs_add_sub_le_three {a b c A B C : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a + b - c| ≤ A + B + C := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  rw [abs_le]
  constructor <;> linarith only [ha'.1, ha'.2, hb'.1, hb'.2, hc'.1, hc'.2]

/-- **The correction under the support containment.**  If the cutoff and its
spatial derivatives vanish outside `vec3Ball 0 R₀` and the cutoff takes values in
`[0,1]`, then the raw-source correction is dominated pointwise by the raw
divergence source, the centred velocity tensor and the velocity-gradient centring
term, each restricted to `vec3Ball 0 R₀`, with the cutoff-gradient size as the only
coefficient.  Every majorant on the right is supported where the A binder's Morrey
bounds `KU`, `KD` apply. -/
theorem centredRawSourceCorrection_abs_le_of_support
    {R₀ Kη : ℝ} {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (hsupp : ∀ x, x ∉ vec3Ball (0 : Vec3) R₀ → η x = 0)
    (hdη : ∀ k x, |dη k x| ≤ Kη)
    (hdsupp : ∀ k x, x ∉ vec3Ball (0 : Vec3) R₀ → dη k x = 0)
    (u f : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (c : Vec3) (j : Fin 3) (x : Vec3) :
    |centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) η dη u f Du c j x| ≤
      |(vec3Ball (0 : Vec3) R₀).indicator
          (fun y => (∑ k, Du y j k * u y k) - f y j) x| +
        Kη * ∑ k, |(vec3Ball (0 : Vec3) R₀).indicator
          (fun y => u y j * (u y k - c k)) x| +
        ∑ k, |(vec3Ball (0 : Vec3) R₀).indicator (fun y => Du y j k * c k) x| := by
  unfold centredRawSourceCorrection
  by_cases hx : x ∈ vec3Ball (0 : Vec3) R₀
  · simp only [Set.indicator_of_mem hx]
    have h1 : |(η x - 1) * ((∑ k, Du x j k * u x k) - f x j)| ≤
        |(∑ k, Du x j k * u x k) - f x j| := by
      rw [abs_mul]
      refine mul_le_of_le_one_left (abs_nonneg _) ?_
      rw [abs_le]
      constructor <;> linarith only [hη0 x, hη1 x]
    have h2 : |∑ k, dη k x * u x j * (u x k - c k)| ≤
        Kη * ∑ k, |u x j * (u x k - c k)| := by
      calc |∑ k, dη k x * u x j * (u x k - c k)| ≤
          ∑ k, |dη k x * u x j * (u x k - c k)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k, Kη * |u x j * (u x k - c k)| := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [mul_assoc, abs_mul]
            exact mul_le_mul_of_nonneg_right (hdη k x) (abs_nonneg _)
        _ = _ := by rw [Finset.mul_sum]
    have h3 : |η x * ∑ k, Du x j k * c k| ≤ ∑ k, |Du x j k * c k| := by
      rw [abs_mul, abs_of_nonneg (hη0 x)]
      calc η x * |∑ k, Du x j k * c k| ≤ 1 * |∑ k, Du x j k * c k| :=
            mul_le_mul_of_nonneg_right (hη1 x) (abs_nonneg _)
        _ = |∑ k, Du x j k * c k| := one_mul _
        _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    exact abs_add_sub_le_three h1 h2 h3
  · have hsum : (∑ k, dη k x * u x j * (u x k - c k)) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hdsupp k x hx]
      ring
    have hz : (η x - (vec3Ball (0 : Vec3) R₀).indicator (fun _ => (1 : ℝ)) x) *
        ((∑ k, Du x j k * u x k) - f x j) +
        (∑ k, dη k x * u x j * (u x k - c k)) -
        η x * ∑ k, Du x j k * c k = 0 := by
      rw [hsupp x hx, Set.indicator_of_notMem hx, hsum]
      ring
    rw [hz, abs_zero]
    simp only [Set.indicator_of_notMem hx, abs_zero, Finset.sum_const_zero,
      mul_zero, add_zero]
    norm_num

/-- **The gap condition that makes the containment true.**  If the collar radius
satisfies `R₁ + 3ρ/4 ≤ R₀` then, for every centre in the closure of the carrier of
radius `R₁`, the centred cutoff vanishes outside the source ball. -/
theorem mollifiedBallCutoff_eq_zero_outside_source_ball
    {ρ R₁ R₀ : ℝ} (hρ : 0 < ρ) (hR₁ : 0 < R₁)
    {z : ParabolicPoint} (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁))
    (hgap : R₁ + 3 * ρ / 4 ≤ R₀) :
    ∀ x, x ∉ vec3Ball (0 : Vec3) R₀ → mollifiedBallCutoff z.1 hρ x = 0 := by
  intro x hx
  have hzx : vec3EuclideanNorm z.1 ≤ R₁ := by
    rw [closure_parabolicCylinder hR₁] at hz
    have h := hz.1
    change vec3EuclideanNorm (z.1 - (0 : Vec3)) ≤ R₁ at h
    simpa only [sub_zero] using h
  have hxn : R₀ ≤ vec3EuclideanNorm (x - (0 : Vec3)) := by
    rw [mem_vec3Ball] at hx
    exact not_lt.mp hx
  have hxn' : R₀ ≤ vec3EuclideanNorm x := by simpa only [sub_zero] using hxn
  have htri : vec3EuclideanNorm x ≤
      vec3EuclideanNorm (x - z.1) + vec3EuclideanNorm z.1 := by
    calc vec3EuclideanNorm x = vec3EuclideanNorm ((x - z.1) + z.1) := by abel_nf
      _ ≤ _ := vec3EuclideanNorm_add_le _ _
  have hfar : 3 * ρ / 4 ≤ vec3EuclideanNorm (x - z.1) := by
    linarith only [hxn', htri, hzx, hgap]
  have hnot : x ∉ tsupport (mollifiedBallCutoff z.1 hρ) := by
    intro hmem
    have hball := mollifiedBallCutoff_tsupport_subset_outer z.1 hρ hmem
    rw [euclideanBall_eq_vec3Ball (by positivity : (0 : ℝ) < 3 * ρ / 4),
      mem_vec3Ball] at hball
    linarith only [hball, hfar]
  exact image_eq_zero_of_notMem_tsupport hnot

/-- Under the same gap condition every first spatial derivative of the centred
cutoff vanishes outside the source ball. -/
theorem spatialDeriv_mollifiedBallCutoff_eq_zero_outside_source_ball
    {ρ R₁ R₀ : ℝ} (hρ : 0 < ρ) (hR₁ : 0 < R₁)
    {z : ParabolicPoint} (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁))
    (hgap : R₁ + 3 * ρ / 4 ≤ R₀) :
    ∀ (k : Fin 3), ∀ x, x ∉ vec3Ball (0 : Vec3) R₀ →
      spatialDeriv (mollifiedBallCutoff z.1 hρ) k x = 0 := by
  intro k x hx
  have hzx : vec3EuclideanNorm z.1 ≤ R₁ := by
    rw [closure_parabolicCylinder hR₁] at hz
    have h := hz.1
    change vec3EuclideanNorm (z.1 - (0 : Vec3)) ≤ R₁ at h
    simpa only [sub_zero] using h
  have hxn : R₀ ≤ vec3EuclideanNorm (x - (0 : Vec3)) := by
    rw [mem_vec3Ball] at hx
    exact not_lt.mp hx
  have hxn' : R₀ ≤ vec3EuclideanNorm x := by simpa only [sub_zero] using hxn
  have htri : vec3EuclideanNorm x ≤
      vec3EuclideanNorm (x - z.1) + vec3EuclideanNorm z.1 := by
    calc vec3EuclideanNorm x = vec3EuclideanNorm ((x - z.1) + z.1) := by abel_nf
      _ ≤ _ := vec3EuclideanNorm_add_le _ _
  have hfar : 3 * ρ / 4 ≤ vec3EuclideanNorm (x - z.1) := by
    linarith only [hxn', htri, hzx, hgap]
  refine (pressure_cutoff_derivatives_vanish z.1 hρ ?_).1 k
  intro hmem
  have hball := hmem.1
  rw [euclideanBall_eq_vec3Ball (by positivity : (0 : ℝ) < 3 * ρ / 4),
    mem_vec3Ball] at hball
  linarith only [hball, hfar]

end CKN.Core.Step4
