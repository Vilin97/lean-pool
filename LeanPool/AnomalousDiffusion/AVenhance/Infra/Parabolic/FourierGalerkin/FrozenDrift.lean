/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ODE
public import LeanPool.AnomalousDiffusion.Homogenization.Ambient.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.UnitCube
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Drift estimates from the boundedness hypothesis

The weak-wellposedness root assumes a pointwise bound on the ambient drift. Since `Vec 2`
uses the product sup norm while the spatial gradient energy is Euclidean, the dimension-two bridge
below records the harmless factor `sqrt 2`. No divergence-free assumption is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- The product-measurability hypothesis restricts to the physical space-time cell. -/
theorem frozenDrift_aestronglyMeasurable_cell (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ AVenhance.unitCube)) := by
  apply hb_meas.mono_set
  intro p hp
  exact ⟨hp.1, Set.mem_univ _⟩

/-- Fubini turns cellwise a.e. strong measurability into a measurable time-dependent spatial
integral. The domain measure is exactly the product of restricted time and space measures. -/
theorem aestronglyMeasurable_timeIntegral_of_cell {f : ℝ × Vec 2 → ℝ}
    (hf : AEStronglyMeasurable f
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ AVenhance.unitCube))) :
    AEStronglyMeasurable
      (fun t => ∫ x, f (t, x) ∂(volume.restrict AVenhance.unitCube))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hfprod : AEStronglyMeasurable f
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (Vec 2)]
    exact hf
  exact hfprod.integral_prod_right'

/-- Multiplying the drift by a spatial vector field and scalar test mode preserves a.e.
strong measurability on the space-time cell. -/
theorem frozenDrift_weightedCell_aestronglyMeasurable
    (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (grad : Vec 2 → Vec 2) (hgrad : AEStronglyMeasurable grad
      (volume.restrict AVenhance.unitCube))
    (weight : Vec 2 → ℝ) (hweight : AEStronglyMeasurable weight
      (volume.restrict AVenhance.unitCube)) :
    AEStronglyMeasurable
      (fun p : ℝ × Vec 2 =>
        Homogenization.vecDot (b p.1 p.2) (grad p.2) * weight p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ AVenhance.unitCube)) := by
  let μ := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod
    (volume.restrict AVenhance.unitCube)
  have hbCell := frozenDrift_aestronglyMeasurable_cell b hb_meas
  have hbProd : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2) μ := by
    change AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube))
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (Vec 2)]
    exact hbCell
  have hgradProd : AEStronglyMeasurable (fun p : ℝ × Vec 2 => grad p.2) μ := by
    exact hgrad.comp_snd
  have hweightProd : AEStronglyMeasurable (fun p : ℝ × Vec 2 => weight p.2) μ := by
    exact hweight.comp_snd
  have hbCoord (i : Fin 2) : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2 i) μ := by
    simpa using (continuous_apply i).comp_aestronglyMeasurable hbProd
  have hgradCoord (i : Fin 2) : AEStronglyMeasurable (fun p : ℝ × Vec 2 => grad p.2 i) μ := by
    simpa using (continuous_apply i).comp_aestronglyMeasurable hgradProd
  have hsum : AEStronglyMeasurable
      (fun p : ℝ × Vec 2 =>
        (b p.1 p.2 0 * grad p.2 0 * weight p.2) +
          (b p.1 p.2 1 * grad p.2 1 * weight p.2)) μ := by
    exact ((hbCoord 0).mul (hgradCoord 0)).mul hweightProd |>.add
      (((hbCoord 1).mul (hgradCoord 1)).mul hweightProd)
  have hsum' : AEStronglyMeasurable
      (fun p : ℝ × Vec 2 =>
        Homogenization.vecDot (b p.1 p.2) (grad p.2) * weight p.2) μ := by
    have heq : (fun p : ℝ × Vec 2 =>
        Homogenization.vecDot (b p.1 p.2) (grad p.2) * weight p.2) =
      (fun p =>
        (b p.1 p.2 0 * grad p.2 0 + b p.1 p.2 1 * grad p.2 1) * weight p.2) := by
      funext p
      simp [Homogenization.vecDot, Fin.sum_univ_succ]
    have heq' : (fun p : ℝ × Vec 2 =>
        (b p.1 p.2 0 * grad p.2 0 + b p.1 p.2 1 * grad p.2 1) * weight p.2) =
      (fun p => b p.1 p.2 0 * grad p.2 0 * weight p.2 +
        b p.1 p.2 1 * grad p.2 1 * weight p.2) := by
      funext p
      ring
    rw [heq, heq']
    exact hsum
  change AEStronglyMeasurable
    (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (b p.1 p.2) (grad p.2) * weight p.2)
    (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ AVenhance.unitCube))
  rw [Measure.volume_eq_prod ℝ (Vec 2), ← Measure.prod_restrict]
  exact hsum'

/-- Each drift weak-form matrix entry against spatially measurable modes is measurable in
time. This is the time-coefficient measurability bridge from the product hypothesis. -/
theorem frozenDrift_weakEntry_time_aestronglyMeasurable
    (b : ℝ → Vec 2 → Vec 2)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (grad : Vec 2 → Vec 2) (hgrad : AEStronglyMeasurable grad
      (volume.restrict AVenhance.unitCube))
    (weight : Vec 2 → ℝ) (hweight : AEStronglyMeasurable weight
      (volume.restrict AVenhance.unitCube)) :
    AEStronglyMeasurable
      (fun t => ∫ x in AVenhance.unitCube,
        Homogenization.vecDot (b t x) (grad x) * weight x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  let f : ℝ × Vec 2 → ℝ := fun p =>
    Homogenization.vecDot (b p.1 p.2) (grad p.2) * weight p.2
  have hf := frozenDrift_weightedCell_aestronglyMeasurable b hb_meas grad hgrad weight hweight
  simpa [f] using aestronglyMeasurable_timeIntegral_of_cell (f := f) hf

/-- The Euclidean norm associated with the squared vector norm used by the carriers. -/
def euclideanVecNorm (v : Vec 2) : ℝ := Real.sqrt (Homogenization.vecNormSq v)

theorem euclideanVecNorm_nonneg (v : Vec 2) : 0 ≤ euclideanVecNorm v :=
  Real.sqrt_nonneg _

theorem euclideanVecNorm_sq (v : Vec 2) : euclideanVecNorm v ^ 2 =
    Homogenization.vecNormSq v :=
  Real.sq_sqrt (Homogenization.vecNormSq_nonneg v)

/-- The pointwise bound controls the Euclidean dot product, with the conversion from the
product sup norm to the Euclidean norm made explicit. -/
theorem vecDot_le_of_supNorm_le {b v : Vec 2} {C : ℝ}
    (hC : 0 ≤ C) (hb : ‖b‖ ≤ C) :
    |Homogenization.vecDot b v| ≤ (Real.sqrt 2 * C) * euclideanVecNorm v := by
  have hbcoord (i : Fin 2) : |b i| ≤ C := by
    have h := (pi_norm_le_iff_of_nonempty b).1 hb i
    simpa [Real.norm_eq_abs] using h
  have hbsq (i : Fin 2) : b i ^ 2 ≤ C ^ 2 := by
    have hlow : -C ≤ b i := (abs_le.mp (hbcoord i)).1
    have hupp : b i ≤ C := (abs_le.mp (hbcoord i)).2
    have hprod : 0 ≤ (C - b i) * (C + b i) :=
      mul_nonneg (sub_nonneg.mpr hupp) (by linarith)
    nlinarith
  have hbEuclidean : Homogenization.vecNormSq b ≤ 2 * C ^ 2 := by
    have hsum : Homogenization.vecNormSq b = b 0 ^ 2 + b 1 ^ 2 := by
      simp [Homogenization.vecNormSq, Homogenization.vecDot]
      ring
    rw [hsum]
    nlinarith [hbsq 0, hbsq 1]
  have hvEuclidean : 0 ≤ Homogenization.vecNormSq v :=
    Homogenization.vecNormSq_nonneg v
  have hcs := Homogenization.sq_vecDot_le_vecNormSq_mul_vecNormSq b v
  have htarget :
      (Real.sqrt 2 * C * euclideanVecNorm v) ^ 2 =
        2 * C ^ 2 * Homogenization.vecNormSq v := by
    calc
      (Real.sqrt 2 * C * euclideanVecNorm v) ^ 2 =
          (Real.sqrt 2) ^ 2 * C ^ 2 * euclideanVecNorm v ^ 2 := by ring
      _ = 2 * C ^ 2 * Homogenization.vecNormSq v := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), euclideanVecNorm_sq]
  have hdotSq : |Homogenization.vecDot b v| ^ 2 ≤
      (Real.sqrt 2 * C * euclideanVecNorm v) ^ 2 := by
    calc
      |Homogenization.vecDot b v| ^ 2 = Homogenization.vecDot b v ^ 2 := by rw [sq_abs]
      _ ≤ Homogenization.vecNormSq b * Homogenization.vecNormSq v := hcs
      _ ≤ 2 * C ^ 2 * Homogenization.vecNormSq v :=
        mul_le_mul_of_nonneg_right hbEuclidean hvEuclidean
      _ = (Real.sqrt 2 * C * euclideanVecNorm v) ^ 2 := htarget.symm
  have htarget_nonneg : 0 ≤ Real.sqrt 2 * C * euclideanVecNorm v :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC) (euclideanVecNorm_nonneg v)
  exact (sq_le_sq₀ (abs_nonneg _) htarget_nonneg).mp hdotSq

/-- A bounded drift gives a dimension-explicit bound on every spatial dot product. -/
theorem frozenDrift_vecDot_bound (b : ℝ → Vec 2 → Vec 2)
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x v,
      |Homogenization.vecDot (b t x) v| ≤ B * euclideanVecNorm v := by
  obtain ⟨C, hC⟩ := hb_bdd
  have hC_nonneg : 0 ≤ C := by
    have h := hC (1 / 2) (by norm_num) 0
    exact (norm_nonneg _).trans h
  refine ⟨Real.sqrt 2 * C, mul_nonneg (Real.sqrt_nonneg _) hC_nonneg, ?_⟩
  intro t ht x v
  exact vecDot_le_of_supNorm_le hC_nonneg (hC t ht x)

/-- Hölder controls the space-time-cell drift form from the two scalar `L²` bounds.

The vector estimate is supplied separately by `frozenDrift_vecDot_bound`; this lemma is the
integral step used to obtain the `drift_bound` field of a Galerkin system. -/
theorem driftIntegral_bound_of_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g u : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hpoint : ∀ᵐ x ∂μ, |f x| ≤ B * (|g x| * |u x|))
    (hg : MemLp g 2 μ) (hu : MemLp u 2 μ)
    (hf : Integrable f μ) :
    |∫ x, f x ∂μ| ≤
      B * (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ x, ‖u x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := by
  have htriple : ENNReal.HolderTriple 2 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  have hprod : Integrable (fun x => |g x| * |u x|) μ := by
    have h := @MemLp.integrable_mul α _ μ ℝ _ 2 2
      (fun x => ‖g x‖) (fun x => ‖u x‖) hg.norm hu.norm htriple
    convert h using 1
  have hmajor : Integrable (fun x => B * (|g x| * |u x|)) μ := hprod.const_mul B
  have hmajor' : ∫ x, |f x| ∂μ ≤ ∫ x, B * (|g x| * |u x|) ∂μ :=
    integral_mono_ae hf.abs hmajor hpoint
  calc
    |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, B * (|g x| * |u x|) ∂μ := hmajor'
    _ = B * ∫ x, |g x| * |u x| ∂μ := by rw [integral_const_mul]
    _ ≤ B * ((∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ x, ‖u x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)) := by
      have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
      have hu' : MemLp u (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hu
      have hholder := integral_mul_norm_le_Lp_mul_Lq
        Real.HolderConjugate.two_two hg' hu'
      simpa [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using
        (mul_le_mul_of_nonneg_left hholder hB)
    _ = _ := by ring

/-- The same `L²` drift estimate holds without a measurability premise on the integrand: if the
Bochner integral is undefined, Mathlib's integral convention assigns it zero. This form is useful
for pointwise matrix bounds when the product-measurability hypothesis controls slices only
for almost every time. -/
theorem driftIntegral_bound_of_L2_or_not {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g u : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hpoint : ∀ᵐ x ∂μ, |f x| ≤ B * (|g x| * |u x|))
    (hg : MemLp g 2 μ) (hu : MemLp u 2 μ) :
    |∫ x, f x ∂μ| ≤
      B * (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ x, ‖u x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := by
  by_cases hf : Integrable f μ
  · exact driftIntegral_bound_of_L2 f g u B hB hpoint hg hu hf
  · have hzero : ∫ x, f x ∂μ = 0 := by
      simp [MeasureTheory.integral, hf]
    rw [hzero, abs_zero]
    have hgint : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ :=
      integral_nonneg_of_ae (ae_of_all _ fun x => by positivity)
    have huit : 0 ≤ ∫ x, ‖u x‖ ^ (2 : ℝ) ∂μ :=
      integral_nonneg_of_ae (ae_of_all _ fun x => by positivity)
    exact mul_nonneg
      (mul_nonneg hB (Real.rpow_nonneg hgint _)) (Real.rpow_nonneg huit _)

end AVenhance.Infra.Parabolic.FourierGalerkin

end
