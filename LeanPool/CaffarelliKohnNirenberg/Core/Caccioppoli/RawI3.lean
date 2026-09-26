/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.I3
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Covering

/-!
# Raw I3

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat


noncomputable section

namespace CKN

theorem caccioppoli_heat_cutoff_gradient_sum_bound
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (_ : r ≤ ρ / 2) {z : ParabolicPoint}
    (hz : z ∈ parabolicCylinder x₀ t₀ ρ) :
    ∑ i, |spatialPartial (fun w : ParabolicPoint =>
      backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i z| ≤
      3 * ((cutoffGradientConstant / ρ) * (1000 / r) +
        300000 * r ^ 2 / r ^ 4) := by
  have htime : z.2 - t₀ < r ^ 2 := by
    have hupper := (mem_parabolicCylinder.mp hz).2.2
    linarith only [hupper, sq_pos_of_pos hr]
  have hη : ContDiff ℝ (⊤ : ℕ∞)
      (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) :=
    caccioppoli_heat_cutoff_smooth x₀ t₀ ρ ε hρ hε
  have hz' : (z.1 - x₀, z.2 - t₀) ∈ parabolicCylinder 0 0 ρ := by
    rw [mem_parabolicCylinder]
    rcases mem_parabolicCylinder.mp hz with ⟨hx, ht₁, ht₂⟩
    exact ⟨by simpa only [sub_zero] using hx, by linarith only [ht₁],
      by linarith only [ht₂]⟩
  have hψ := backwardHeatTestFunction_upper_on_cylinder hr hρ hz'
  have hψ0 := backwardHeatTestFunction_nonneg
    (x := z.1 - x₀) (t := z.2 - t₀) hr htime
  have hgrad := backwardHeatTestGradient_upper_on_cylinder hr hρ hz'
  have hC : 0 ≤ cutoffGradientConstant := by
    by_contra hC'
    have hneg : cutoffGradientConstant / ρ < 0 :=
      div_neg_of_neg_of_pos (lt_of_not_ge hC') hρ
    have hbound := caccioppoli_spatial_cutoff_gradient_bound x₀ ρ hρ 0
    have hnorm : 0 ≤ vecEuclideanNorm (classicalGradient
        (mollifiedBallCutoff x₀ hρ) 0) := by
      unfold vecEuclideanNorm
      positivity
    exact (not_lt_of_ge hnorm) (hbound.trans_lt hneg)
  have hCρ : 0 ≤ cutoffGradientConstant / ρ := div_nonneg hC hρ.le
  have hcoord : ∀ i : Fin 3,
      |heatKernelSpaceDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) i| ≤
        heatKernelGradientNorm (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) := by
    intro i
    exact Finset.single_le_sum (f := fun j =>
      |heatKernelSpaceDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀)) j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have hD : ∀ i : Fin 3,
      |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) i| ≤
        300000 * r ^ 2 / r ^ 4 := by
    intro i
    rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
    calc
      r ^ 2 * |heatKernelSpaceDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) i| ≤
          r ^ 2 * heatKernelGradientNorm (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) := by
        exact mul_le_mul_of_nonneg_left (hcoord i) (sq_nonneg r)
      _ = backwardHeatTestGradientNorm r (z.1 - x₀) (z.2 - t₀) := rfl
      _ ≤ 300000 / r ^ 2 := hgrad
      _ = 300000 * r ^ 2 / r ^ 4 := by
        field_simp [hr.ne']
  calc
    ∑ i, |spatialPartial (fun w : ParabolicPoint =>
        backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i z| ≤
      ∑ i, ((cutoffGradientConstant / ρ) * (1000 / r) +
        |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) i|) := by
      apply Finset.sum_le_sum
      intro i hi
      have hformula := caccioppoli_cutoff_heat_spatialPartial
        (η := caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε)
        (x₀ := x₀) (t₀ := t₀) (r := r) (z := z) hη htime i
      have hηi := caccioppoli_heat_cutoff_spatial_partial_bound
        x₀ t₀ ρ ε hρ hε z i
      have hη0 := caccioppoli_heat_cutoff_nonneg x₀ t₀ ρ ε hρ hε z
      have hη1 := caccioppoli_heat_cutoff_le_one x₀ t₀ ρ ε hρ hε z
      rw [hformula]
      calc
        |spatialPartial (fun w : ParabolicPoint =>
            caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i z *
              backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
            caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε z *
              (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
                (r ^ 2 - (z.2 - t₀)) i)| ≤
          |spatialPartial (fun w : ParabolicPoint =>
            caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i z *
              backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀)| +
            |caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε z *
              (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
                (r ^ 2 - (z.2 - t₀)) i)| := abs_add_le _ _
        _ = |spatialPartial (fun w : ParabolicPoint =>
            caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i z| *
              backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
            caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε z *
              |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
                (r ^ 2 - (z.2 - t₀)) i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hψ0, abs_of_nonneg hη0]
        _ ≤ (cutoffGradientConstant / ρ) * (1000 / r) +
            |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
              (r ^ 2 - (z.2 - t₀)) i| := by
          exact add_le_add
            (mul_le_mul hηi hψ hψ0 hCρ)
            (by
              simpa only [one_mul] using
                (mul_le_mul_of_nonneg_right hη1 (abs_nonneg
                  (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
                    (r ^ 2 - (z.2 - t₀)) i))))
    _ ≤ ∑ i, ((cutoffGradientConstant / ρ) * (1000 / r) +
        300000 * r ^ 2 / r ^ 4) := by
      apply Finset.sum_le_sum
      intro i hi
      exact add_le_add (le_refl _) (hD i)
    _ = 3 * ((cutoffGradientConstant / ρ) * (1000 / r) +
        300000 * r ^ 2 / r ^ 4) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      norm_num

end CKN
