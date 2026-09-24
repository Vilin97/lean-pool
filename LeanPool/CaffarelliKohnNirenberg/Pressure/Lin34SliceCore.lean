/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SliceHolder
public import LeanPool.CaffarelliKohnNirenberg.Pressure.OscillationLin34Solution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorEstimatesBasic

/-!
# Lin34 Slice Core

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

/-!
# The centred pressure decomposition on one time slice

This file runs the local pressure decomposition of `prop:pressure-decomposition`
(`paper/ckn.tex`) with the doubly centred nonlinearity `eq:Uhat` of
`lem:delta-p-centred` in place of the raw one, which is the form the oscillation
estimate `prop:lin34` uses: the velocity then enters only through the mean-free
field `u - ⨍_{B_ρ} u` of `eq:Chat`.
-/

/-- The mean-free velocity field `w = u - ⨍_{B_ρ} u` of `eq:Uhat` in
`paper/ckn.tex`, seen as a field on space-time. -/
def lin34CentredVelocity (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ : ℝ) :
    ParabolicPoint → Vec3 := fun w => meanFreeVec u x₀ ρ w.2 w.1

/-- The centred tensor `Û_{ij} = -(u_i - ⨍u_i)(u_j - ⨍u_j)` of `eq:Uhat` is the
tensor of the decomposition run with the mean-free field and a zero average. -/
theorem lin34_pressureUTensor_centred
    (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ s : ℝ) (y : Vec3) (i j : Fin 3) :
    pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j =
      -(meanFreeVec u x₀ ρ s y i) * (meanFreeVec u x₀ ρ s y j) := by
  simp [pressureUTensor, lin34CentredVelocity]

/-- The pointwise norm of the centred tensor is the square of the mean-free
velocity, which is the identity `|Û| ≤ |w|²` of `prop:lin34` in equality form. -/
theorem lin34_pressureUTensorNorm_centred
    (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ s : ℝ) (y : Vec3) :
    pressureUTensorNorm (lin34CentredVelocity u x₀ ρ) 0 s y =
      vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) := by
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3,
      (pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j) ^
        (2 : ℕ)) =
      (∑ i : Fin 3, (meanFreeVec u x₀ ρ s y i) ^ (2 : ℕ)) *
        (∑ j : Fin 3, (meanFreeVec u x₀ ρ s y j) ^ (2 : ℕ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [lin34_pressureUTensor_centred]
    ring
  unfold pressureUTensorNorm
  rw [hsum]
  have hnonneg : 0 ≤ ∑ i : Fin 3, (meanFreeVec u x₀ ρ s y i) ^ (2 : ℕ) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [Real.sqrt_mul_self hnonneg, vec3EuclideanNorm]
  rw [Real.sq_sqrt hnonneg]

/-- The mean-free field of a time slice is the slice minus a constant vector. -/
theorem lin34_centredVelocity_slice_eq
    (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ s : ℝ) :
    (fun y : Vec3 => lin34CentredVelocity u x₀ ρ (y, s)) =
      (fun y : Vec3 => u (y, s)) -
        (fun _ : Vec3 => fun j : Fin 3 => MeasureTheory.average
          (volume.restrict (vec3Ball x₀ ρ)) (fun w : Vec3 => u (w, s) j)) := by
  funext y
  funext j
  rfl

private lemma lin34_isFiniteMeasure_ball {x₀ : Vec3} {ρ : ℝ} :
    IsFiniteMeasure (volume.restrict (vec3Ball x₀ ρ)) := by
  refine isFiniteMeasure_restrict.mpr ?_
  rw [volume_vec3Ball_eq]
  exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    ENNReal.ofReal_lt_top).ne

/-- The mean-free slice inherits the square integrability of the velocity slice. -/
theorem lin34_centredVelocity_memLp
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ s : ℝ}
    (hu : MemLp (fun y : Vec3 => u (y, s)) 2 (volume.restrict (vec3Ball x₀ ρ))) :
    MemLp (fun y : Vec3 => lin34CentredVelocity u x₀ ρ (y, s)) 2
      (volume.restrict (vec3Ball x₀ ρ)) := by
  haveI : IsFiniteMeasure (volume.restrict (vec3Ball x₀ ρ)) :=
    lin34_isFiniteMeasure_ball
  rw [lin34_centredVelocity_slice_eq]
  exact hu.sub (memLp_const _)

/-- The far-field bound of `lem:pk-bounds`(b) for the centred potentials
`p₂, p₃, p₄` of `prop:lin34`: on the inner ball they are dominated by the
`L¹` norm of the centred tensor `eq:Uhat`. -/
theorem lin34_centred_P234_sup_bound
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ r s : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hu : MemLp (fun y : Vec3 => u (y, s)) 2 (volume.restrict (vec3Ball x₀ ρ)))
    (_ : AEMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ))) :
    ∀ x ∈ vec3Ball x₀ r,
      |pressureP2 (mollifiedBallCutoff x₀ hρ)
          (lin34CentredVelocity u x₀ ρ) 0 s x| +
        |pressureP3 (mollifiedBallCutoff x₀ hρ)
          (lin34CentredVelocity u x₀ ρ) 0 s x| +
        |pressureP4 (mollifiedBallCutoff x₀ hρ)
          (lin34CentredVelocity u x₀ ρ) 0 s x| ≤
      (18 * cutoffSecondDerivativeConstant + 720 * cutoffGradientConstant) /
          ρ ^ 3 *
        ∫ y in vec3Ball x₀ ρ,
          vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) := by
  have hcu : MemLp (fun y : Vec3 => lin34CentredVelocity u x₀ ρ (y, s)) 2
      (volume.restrict (vec3Ball x₀ ρ)) := lin34_centredVelocity_memLp hu
  have hcumeas : AEMeasurable (fun y : Vec3 => lin34CentredVelocity u x₀ ρ (y, s))
      (volume.restrict (vec3Ball x₀ ρ)) := hcu.aestronglyMeasurable.aemeasurable
  have hU : Integrable
      (pressureUTensorNorm (lin34CentredVelocity u x₀ ρ) 0 s)
      (volume.restrict (vec3Ball x₀ ρ)) :=
    pressure_utensor_integrable_on_ball hρ hcumeas hcu
  have hfixed := pressureP234_fixed_bound hρ hr hhalf
    cutoffGradientConstant_nonneg_global cutoffSecondDerivativeConstant_nonneg_global
    (η := mollifiedBallCutoff x₀ hρ) (u := lin34CentredVelocity u x₀ ρ) (c := 0)
    (hηeq := rfl) (mollifiedBallCutoff_smooth x₀ hρ)
    (mollifiedBallCutoff_hasCompactSupport x₀ hρ)
    (pressure_cutoff_support_subset_ball x₀ hρ)
    (fun y hy => hy) hcu hcumeas hU
  simpa only [lin34_pressureUTensorNorm_centred] using hfixed

/-- The far-field bound of `lem:pk-bounds`(c) for `p₅, p₆` on the inner ball,
in the form used by `prop:lin34`. -/
theorem lin34_P56_sup_bound
    {p : ParabolicPoint → ℝ} {x₀ : Vec3} {ρ r s : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hp : Integrable (fun y : Vec3 => |p (y, s)|)
      (volume.restrict (vec3Ball x₀ ρ)))
    (hpm : AEStronglyMeasurable (fun y : Vec3 => p (y, s))
      (volume.restrict (vec3Ball x₀ ρ))) :
    ∀ x ∈ vec3Ball x₀ r,
      |pressureP5 (mollifiedBallCutoff x₀ hρ) p s x| +
        |pressureP6 (mollifiedBallCutoff x₀ hρ) p s x| ≤
      (18 * cutoffSecondDerivativeConstant + 240 * cutoffGradientConstant) /
          ρ ^ 3 * ∫ y in vec3Ball x₀ ρ, |p (y, s)| :=
  pressureP56_fixed_bound hρ hr hhalf hp hpm rfl
    (mollifiedBallCutoff_smooth x₀ hρ)
    (mollifiedBallCutoff_hasCompactSupport x₀ hρ)
    (pressure_cutoff_support_subset_ball x₀ hρ)

/-- The constant of the far-field potential bounds of `lem:pk-bounds`(b)--(c)
used in `prop:lin34`. -/
def lin34CutoffConstant : ℝ :=
  18 * cutoffSecondDerivativeConstant + 720 * cutoffGradientConstant

theorem lin34CutoffConstant_nonneg : 0 ≤ lin34CutoffConstant := by
  have h₁ := cutoffGradientConstant_nonneg_global
  have h₂ := cutoffSecondDerivativeConstant_nonneg_global
  unfold lin34CutoffConstant
  linarith only [h₁, h₂]

private lemma lin34_P56Constant_le :
    18 * cutoffSecondDerivativeConstant + 240 * cutoffGradientConstant ≤
      lin34CutoffConstant := by
  have h₁ := cutoffGradientConstant_nonneg_global
  unfold lin34CutoffConstant
  linarith only [h₁]

private lemma lin34_rpow_add_three_halves {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ (3 / 2 : ℝ) ≤
      Real.sqrt 2 * (a ^ (3 / 2 : ℝ) + b ^ (3 / 2 : ℝ)) := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow
    (s := (Finset.univ : Finset (Fin 2)))
    (f := ![a, b]) (p := (3 / 2 : ℝ)) (by norm_num)
  have h' : (|a| + |b|) ^ (3 / 2 : ℝ) ≤
      2 ^ ((3 / 2 : ℝ) - 1) * (|a| ^ (3 / 2 : ℝ) + |b| ^ (3 / 2 : ℝ)) := by
    simpa using h
  rw [abs_of_nonneg ha, abs_of_nonneg hb] at h'
  convert h' using 1; norm_num [Real.sqrt_eq_rpow]

private lemma lin34_rpow_two_thirds_cancel {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = x := by
  rw [← Real.rpow_mul hx]
  norm_num

private lemma lin34_rpow_one_third_half {y : ℝ} (hy : 0 ≤ y) :
    (y ^ (1 / 3 : ℝ)) ^ (3 / 2 : ℝ) = y ^ (1 / 2 : ℝ) := by
  rw [← Real.rpow_mul hy]
  norm_num

private lemma lin34_rpow_inv_sq {ρ : ℝ} (hρ : 0 < ρ) :
    ((ρ ^ 2)⁻¹) ^ (3 / 2 : ℝ) = (ρ ^ 3)⁻¹ := by
  rw [Real.inv_rpow (by positivity)]
  congr 1
  rw [show (ρ ^ 2 : ℝ) = ρ ^ (2 : ℝ) by
    rw [← Real.rpow_natCast ρ 2]; norm_num, ← Real.rpow_mul hρ.le]
  rw [show (2 : ℝ) * (3 / 2) = 3 by norm_num, ← Real.rpow_natCast ρ 3]
  norm_num

/-- The group `p₂ + p₃ + p₄ + p₅ + p₆` of the decomposition
`prop:pressure-decomposition`, run with the centred tensor `eq:Uhat`: this is
the part of the pressure that carries the factor `r/ρ` in
`eq:lin34-pointwise`. -/
def lin34CentredRemainder (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (x₀ : Vec3) (ρ : ℝ) (hρ : 0 < ρ) (s : ℝ) : Vec3 → ℝ :=
  pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s +
    pressureP3 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s +
    pressureP4 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s +
    pressureP5 (mollifiedBallCutoff x₀ hρ) p s +
    pressureP6 (mollifiedBallCutoff x₀ hρ) p s

/-- The far-field bounds of `lem:pk-bounds`(b)--(c) combined: on the half ball
the group `p₂ + ⋯ + p₆` is bounded by `ρ⁻³` times the `L¹` norms of the centred
tensor and of the pressure. -/
theorem lin34_centred_remainder_sup_bound
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {x₀ : Vec3} {ρ s : ℝ}
    (hρ : 0 < ρ)
    (hu : MemLp (fun y : Vec3 => u (y, s)) 2 (volume.restrict (vec3Ball x₀ ρ)))
    (humeas : AEMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hpint : Integrable (fun y : Vec3 => |p (y, s)|)
      (volume.restrict (vec3Ball x₀ ρ)))
    (hpm : AEStronglyMeasurable (fun y : Vec3 => p (y, s))
      (volume.restrict (vec3Ball x₀ ρ))) :
    ∀ x ∈ vec3Ball x₀ (ρ / 2),
      |lin34CentredRemainder u p x₀ ρ hρ s x| ≤
        lin34CutoffConstant / ρ ^ 3 *
          ((∫ y in vec3Ball x₀ ρ,
              vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ)) +
            ∫ y in vec3Ball x₀ ρ, |p (y, s)|) := by
  have hhalfpos : (0 : ℝ) < ρ / 2 := by positivity
  have hhalfle : ρ / 2 ≤ ρ / 2 := le_rfl
  have h234 := lin34_centred_P234_sup_bound hρ hhalfpos hhalfle hu humeas
  have h56 := lin34_P56_sup_bound hρ hhalfpos hhalfle hpint hpm
  intro x hx
  have hV : 0 ≤ ∫ y in vec3Ball x₀ ρ,
      vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) :=
    integral_nonneg (fun y => by positivity)
  have hP : 0 ≤ ∫ y in vec3Ball x₀ ρ, |p (y, s)| :=
    integral_nonneg (fun y => abs_nonneg _)
  have hsplit : |lin34CentredRemainder u p x₀ ρ hρ s x| ≤
      (|pressureP2 (mollifiedBallCutoff x₀ hρ)
          (lin34CentredVelocity u x₀ ρ) 0 s x| +
        |pressureP3 (mollifiedBallCutoff x₀ hρ)
          (lin34CentredVelocity u x₀ ρ) 0 s x| +
        |pressureP4 (mollifiedBallCutoff x₀ hρ)
          (lin34CentredVelocity u x₀ ρ) 0 s x|) +
      (|pressureP5 (mollifiedBallCutoff x₀ hρ) p s x| +
        |pressureP6 (mollifiedBallCutoff x₀ hρ) p s x|) := by
    have hpt : lin34CentredRemainder u p x₀ ρ hρ s x =
        (pressureP2 (mollifiedBallCutoff x₀ hρ)
            (lin34CentredVelocity u x₀ ρ) 0 s x +
          pressureP3 (mollifiedBallCutoff x₀ hρ)
            (lin34CentredVelocity u x₀ ρ) 0 s x +
          pressureP4 (mollifiedBallCutoff x₀ hρ)
            (lin34CentredVelocity u x₀ ρ) 0 s x) +
        (pressureP5 (mollifiedBallCutoff x₀ hρ) p s x +
          pressureP6 (mollifiedBallCutoff x₀ hρ) p s x) := by
      simp only [lin34CentredRemainder, Pi.add_apply]
      ring
    rw [hpt]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    · exact abs_add_le _ _
  have hK56 : (18 * cutoffSecondDerivativeConstant +
      240 * cutoffGradientConstant) / ρ ^ 3 *
      (∫ y in vec3Ball x₀ ρ, |p (y, s)|) ≤
      lin34CutoffConstant / ρ ^ 3 * ∫ y in vec3Ball x₀ ρ, |p (y, s)| := by
    have hdiv : (18 * cutoffSecondDerivativeConstant +
        240 * cutoffGradientConstant) / ρ ^ 3 ≤ lin34CutoffConstant / ρ ^ 3 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right lin34_P56Constant_le (by positivity)
    exact mul_le_mul_of_nonneg_right hdiv hP
  refine hsplit.trans ?_
  calc
    _ ≤ lin34CutoffConstant / ρ ^ 3 *
        (∫ y in vec3Ball x₀ ρ,
          vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ)) +
        (18 * cutoffSecondDerivativeConstant +
          240 * cutoffGradientConstant) / ρ ^ 3 *
          ∫ y in vec3Ball x₀ ρ, |p (y, s)| :=
      add_le_add (h234 x hx) (h56 x hx)
    _ ≤ lin34CutoffConstant / ρ ^ 3 *
        (∫ y in vec3Ball x₀ ρ,
          vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ)) +
        lin34CutoffConstant / ρ ^ 3 *
          ∫ y in vec3Ball x₀ ρ, |p (y, s)| := add_le_add le_rfl hK56
    _ = _ := by ring

private lemma lin34_sq_rpow_three_halves {a : ℝ} (ha : 0 ≤ a) :
    (a ^ (2 : ℕ)) ^ (3 / 2 : ℝ) = a ^ (3 : ℕ) := by
  rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha]
  rw [show ((2 : ℕ) : ℝ) * (3 / 2 : ℝ) = ((3 : ℕ) : ℝ) by norm_num]
  rw [Real.rpow_natCast]

private lemma lin34_continuous_vec3EuclideanNorm :
    Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
  unfold vec3EuclideanNorm
  fun_prop

/-- The far-field bound of `lem:pk-bounds`(b)--(c) after the Hölder step of
`prop:lin34`: the group `p₂ + ⋯ + p₆` is bounded on the half ball by
`ρ⁻²` times the oscillation and pressure quantities of `eq:Chat`. -/
theorem lin34_centred_remainder_sup_bound_rpow
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {x₀ : Vec3} {ρ s : ℝ}
    (hρ : 0 < ρ)
    (hu : MemLp (fun y : Vec3 => u (y, s)) 2 (volume.restrict (vec3Ball x₀ ρ)))
    (humeas : AEMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hpint : Integrable (fun y : Vec3 => |p (y, s)|)
      (volume.restrict (vec3Ball x₀ ρ)))
    (hpm : AEStronglyMeasurable (fun y : Vec3 => p (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hVint : Integrable (fun y : Vec3 =>
      vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hPint : Integrable (fun y : Vec3 => |p (y, s)| ^ (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ ρ))) :
    ∀ x ∈ vec3Ball x₀ (ρ / 2),
      |lin34CentredRemainder u p x₀ ρ hρ s x| ≤
        (4 * Real.pi / 3) ^ (1 / 3 : ℝ) * lin34CutoffConstant * (ρ ^ 2)⁻¹ *
          ((∫ y in vec3Ball x₀ ρ,
              vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ)) ^ (2 / 3 : ℝ) +
            (∫ y in vec3Ball x₀ ρ, |p (y, s)| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) := by
  have hwmeas : AEMeasurable
      (fun y : Vec3 => vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ))
      (volume.restrict (vec3Ball x₀ ρ)) := by
    have hc : AEMeasurable (fun y : Vec3 => lin34CentredVelocity u x₀ ρ (y, s))
        (volume.restrict (vec3Ball x₀ ρ)) :=
      (lin34_centredVelocity_memLp hu).aestronglyMeasurable.aemeasurable
    exact ((lin34_continuous_vec3EuclideanNorm.measurable.comp_aemeasurable
      hc).pow_const 2)
  have hVpow : Integrable (fun y : Vec3 =>
      (vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ)) ^ (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ ρ)) := by
    refine hVint.congr (Filter.Eventually.of_forall (fun y => ?_))
    exact (lin34_sq_rpow_three_halves (vec3EuclideanNorm_nonneg _)).symm
  have hV := lin34_ball_integral_le_rpow_three_halves hρ hwmeas
    (fun y => by positivity) hVpow
  have hVeq : (∫ y in vec3Ball x₀ ρ,
      (vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ)) ^ (3 / 2 : ℝ)) =
      ∫ y in vec3Ball x₀ ρ,
        vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    exact lin34_sq_rpow_three_halves (vec3EuclideanNorm_nonneg _)
  rw [hVeq] at hV
  have hpabsmeas : AEMeasurable (fun y : Vec3 => |p (y, s)|)
      (volume.restrict (vec3Ball x₀ ρ)) :=
    (continuous_abs.comp_aestronglyMeasurable hpm).aemeasurable
  have hPpow : Integrable (fun y : Vec3 => |p (y, s)| ^ (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ ρ)) := hPint
  have hP := lin34_ball_integral_le_rpow_three_halves hρ hpabsmeas
    (fun y => abs_nonneg _) hPpow
  intro x hx
  have hbase := lin34_centred_remainder_sup_bound hρ hu humeas hpint hpm x hx
  have hKnonneg : 0 ≤ lin34CutoffConstant / ρ ^ 3 := by
    have := lin34CutoffConstant_nonneg
    positivity
  refine hbase.trans ?_
  have hstep : lin34CutoffConstant / ρ ^ 3 *
      ((∫ y in vec3Ball x₀ ρ,
          vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ)) +
        ∫ y in vec3Ball x₀ ρ, |p (y, s)|) ≤
      lin34CutoffConstant / ρ ^ 3 *
        ((4 * Real.pi / 3) ^ (1 / 3 : ℝ) * ρ *
            (∫ y in vec3Ball x₀ ρ,
              vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ)) ^ (2 / 3 : ℝ) +
          (4 * Real.pi / 3) ^ (1 / 3 : ℝ) * ρ *
            (∫ y in vec3Ball x₀ ρ, |p (y, s)| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) :=
    mul_le_mul_of_nonneg_left (add_le_add hV hP) hKnonneg
  refine hstep.trans_eq ?_
  field_simp

private lemma lin34_euclideanBall_eq_vec3Ball {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

private lemma lin34_volume_euclideanBall_toReal {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    (volume (euclideanBall x₀ r)).toReal = (4 * Real.pi / 3) * r ^ (3 : ℕ) := by
  rw [lin34_euclideanBall_eq_vec3Ball hr, pressure_volume_ball hr,
    ENNReal.toReal_ofReal (by positivity)]

private lemma lin34_sup_constant_rpow {K ρ X : ℝ}
    (hK : 0 ≤ K) (hρ : 0 < ρ) (hX : 0 ≤ X) :
    ((4 * Real.pi / 3) ^ (1 / 3 : ℝ) * K * (ρ ^ 2)⁻¹ * X) ^ (3 / 2 : ℝ) =
      (4 * Real.pi / 3) ^ (1 / 2 : ℝ) * K ^ (3 / 2 : ℝ) * (ρ ^ 3)⁻¹ *
        X ^ (3 / 2 : ℝ) := by
  have hpi : (0 : ℝ) ≤ (4 * Real.pi / 3) ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hinv : (0 : ℝ) ≤ (ρ ^ 2)⁻¹ := by positivity
  rw [Real.mul_rpow (by positivity) hX, Real.mul_rpow (by positivity) hinv,
    Real.mul_rpow hpi hK, lin34_rpow_one_third_half (by positivity),
    lin34_rpow_inv_sq hρ]

private lemma lin34_sum_two_thirds_rpow {V P : ℝ} (hV : 0 ≤ V) (hP : 0 ≤ P) :
    (V ^ (2 / 3 : ℝ) + P ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) ≤
      Real.sqrt 2 * (V + P) := by
  have h := lin34_rpow_add_three_halves
    (Real.rpow_nonneg hV (2 / 3 : ℝ)) (Real.rpow_nonneg hP (2 / 3 : ℝ))
  rwa [lin34_rpow_two_thirds_cancel hV, lin34_rpow_two_thirds_cancel hP] at h

/-- The constant of the `r/ρ` group in `eq:lin34-pointwise`. -/
def lin34RemainderConstant : ℝ :=
  Real.sqrt 2 * (4 * Real.pi / 3) * (4 * Real.pi / 3) ^ (1 / 2 : ℝ) *
    lin34CutoffConstant ^ (3 / 2 : ℝ)

theorem lin34RemainderConstant_nonneg : 0 ≤ lin34RemainderConstant := by
  have hK : (0 : ℝ) ≤ lin34CutoffConstant ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg lin34CutoffConstant_nonneg _
  unfold lin34RemainderConstant
  positivity

/-- The `L^{3/2}` bound on the inner ball for the group `p₂ + ⋯ + p₆`: this is
the second term of `eq:lin34-pointwise`, with its decay factor `(r/ρ)³`. -/
theorem lin34_centred_remainder_integral_bound
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {x₀ : Vec3}
    {ρ r s : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hu : MemLp (fun y : Vec3 => u (y, s)) 2 (volume.restrict (vec3Ball x₀ ρ)))
    (humeas : AEMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hpint : Integrable (fun y : Vec3 => |p (y, s)|)
      (volume.restrict (vec3Ball x₀ ρ)))
    (hpm : AEStronglyMeasurable (fun y : Vec3 => p (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hVint : Integrable (fun y : Vec3 =>
      vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hPint : Integrable (fun y : Vec3 => |p (y, s)| ^ (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hHmem : MemLp (lin34CentredRemainder u p x₀ ρ hρ s)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r))) :
    ∫ x in euclideanBall x₀ r,
        |lin34CentredRemainder u p x₀ ρ hρ s x| ^ (3 / 2 : ℝ) ≤
      lin34RemainderConstant * (r / ρ) ^ (3 : ℕ) *
        ((∫ y in vec3Ball x₀ ρ,
            vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ)) +
          ∫ y in vec3Ball x₀ ρ, |p (y, s)| ^ (3 / 2 : ℝ)) := by
  set V : ℝ := ∫ y in vec3Ball x₀ ρ,
    vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ) with hVdef
  set P : ℝ := ∫ y in vec3Ball x₀ ρ, |p (y, s)| ^ (3 / 2 : ℝ) with hPdef
  have hV0 : 0 ≤ V := by
    rw [hVdef]
    exact integral_nonneg (fun y => pow_nonneg (vec3EuclideanNorm_nonneg _) 3)
  have hP0 : 0 ≤ P := by
    rw [hPdef]; exact integral_nonneg (fun y => by positivity)
  set X : ℝ := V ^ (2 / 3 : ℝ) + P ^ (2 / 3 : ℝ) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]; positivity
  set A : ℝ := (4 * Real.pi / 3) ^ (1 / 3 : ℝ) * lin34CutoffConstant *
    (ρ ^ 2)⁻¹ * X with hAdef
  have hA0 : 0 ≤ A := by
    have hpi : (0 : ℝ) ≤ (4 * Real.pi / 3) ^ (1 / 3 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    have hinv : (0 : ℝ) ≤ (ρ ^ 2)⁻¹ := by positivity
    rw [hAdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg hpi lin34CutoffConstant_nonneg)
      hinv) hX0
  have hsup : ∀ x ∈ euclideanBall x₀ (ρ / 2),
      |lin34CentredRemainder u p x₀ ρ hρ s x| ≤ A := by
    intro x hx
    rw [lin34_euclideanBall_eq_vec3Ball (by positivity : (0:ℝ) < ρ / 2)] at hx
    exact lin34_centred_remainder_sup_bound_rpow hρ hu humeas hpint hpm
      hVint hPint x hx
  have hraw := pressure_harmonic_inner_integral_bound hρ hr hhalf hA0 hHmem hsup
  have hvol := lin34_volume_euclideanBall_toReal (x₀ := x₀) hr
  have hArpow : A ^ (3 / 2 : ℝ) =
      (4 * Real.pi / 3) ^ (1 / 2 : ℝ) * lin34CutoffConstant ^ (3 / 2 : ℝ) *
        (ρ ^ 3)⁻¹ * X ^ (3 / 2 : ℝ) :=
    lin34_sup_constant_rpow lin34CutoffConstant_nonneg hρ hX0
  have hXbound : X ^ (3 / 2 : ℝ) ≤ Real.sqrt 2 * (V + P) :=
    lin34_sum_two_thirds_rpow hV0 hP0
  refine hraw.trans ?_
  rw [hvol, hArpow]
  have hcoef : (0 : ℝ) ≤ (4 * Real.pi / 3) * r ^ (3 : ℕ) *
      ((4 * Real.pi / 3) ^ (1 / 2 : ℝ) * lin34CutoffConstant ^ (3 / 2 : ℝ) *
        (ρ ^ 3)⁻¹) := by
    have hK : (0 : ℝ) ≤ lin34CutoffConstant ^ (3 / 2 : ℝ) :=
      Real.rpow_nonneg lin34CutoffConstant_nonneg _
    have hpi : (0 : ℝ) ≤ (4 * Real.pi / 3) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    have hr3 : (0 : ℝ) ≤ (4 * Real.pi / 3) * r ^ (3 : ℕ) := by positivity
    have hinv : (0 : ℝ) ≤ (ρ ^ 3)⁻¹ := by positivity
    exact mul_nonneg hr3 (mul_nonneg (mul_nonneg hpi hK) hinv)
  calc
    (4 * Real.pi / 3) * r ^ (3 : ℕ) *
        ((4 * Real.pi / 3) ^ (1 / 2 : ℝ) * lin34CutoffConstant ^ (3 / 2 : ℝ) *
          (ρ ^ 3)⁻¹ * X ^ (3 / 2 : ℝ)) =
        ((4 * Real.pi / 3) * r ^ (3 : ℕ) *
          ((4 * Real.pi / 3) ^ (1 / 2 : ℝ) *
            lin34CutoffConstant ^ (3 / 2 : ℝ) * (ρ ^ 3)⁻¹)) *
          X ^ (3 / 2 : ℝ) := by ring
    _ ≤ ((4 * Real.pi / 3) * r ^ (3 : ℕ) *
          ((4 * Real.pi / 3) ^ (1 / 2 : ℝ) *
            lin34CutoffConstant ^ (3 / 2 : ℝ) * (ρ ^ 3)⁻¹)) *
          (Real.sqrt 2 * (V + P)) :=
      mul_le_mul_of_nonneg_left hXbound hcoef
    _ = lin34RemainderConstant * (r / ρ) ^ (3 : ℕ) * (V + P) := by
      unfold lin34RemainderConstant
      rw [div_pow]
      field_simp

/-- The Calderón--Zygmund part `p₁` of `prop:pressure-decomposition`, run with
the centred tensor `eq:Uhat`.  This is the object the external input
`ext:CZ` bounds in the proof of `prop:lin34`. -/
def lin34CentredP1 (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ : ℝ) (hρ : 0 < ρ) (s : ℝ) :
    Vec3 → ℝ :=
  pressureP1 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 p f s

/-- The force group `p₇ + p₈` of `prop:pressure-decomposition`. -/
def lin34ForcePart (f : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ : ℝ)
    (hρ : 0 < ρ) (s : ℝ) : Vec3 → ℝ :=
  pressureP7 (mollifiedBallCutoff x₀ hρ) f s +
    pressureP8 (mollifiedBallCutoff x₀ hρ) f s

/-- On the inner ball `B_{13ρ/20}` the pressure splits as
`p = p₁ + (p₂ + ⋯ + p₆) + (p₇ + p₈)`; this is
`prop:pressure-decomposition` with the cutoff equal to one. -/
theorem lin34_centred_decomposition_on_inner
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ s : ℝ} (hρ : 0 < ρ) :
    (fun x : Vec3 => p (x, s)) =ᵐ[
        volume.restrict (euclideanBall x₀ (13 * ρ / 20))]
      (lin34CentredP1 u p f x₀ ρ hρ s + lin34CentredRemainder u p x₀ ρ hρ s +
        lin34ForcePart f x₀ ρ hρ s) := by
  have hrem := pressure_remainder_eq_on_inner
    (u := lin34CentredVelocity u x₀ ρ) (c := 0) (p := p) (f := f)
    (x₀ := x₀) (s := s) hρ
  filter_upwards [hrem] with x hx
  have hx' : lin34CentredRemainder u p x₀ ρ hρ s x =
      p (x, s) - lin34CentredP1 u p f x₀ ρ hρ s x -
        lin34ForcePart f x₀ ρ hρ s x := hx
  change p (x, s) = lin34CentredP1 u p f x₀ ρ hρ s x +
    lin34CentredRemainder u p x₀ ρ hρ s x + lin34ForcePart f x₀ ρ hρ s x
  rw [hx']
  ring

end CKN
