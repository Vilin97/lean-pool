/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearFlow

/-!
# Local energy data for the viscous shear

The velocity and its gradient are bounded by one on the positive time
interval. Compact local boxes therefore have finite energy and slice bounds.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic


namespace CKN

private theorem amplitude_bound (s a : ℝ) (hs : 0 ≤ s) (ha : |a| ≤ 1) :
    ‖Real.exp (-s) * a‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)
  calc
    Real.exp (-s) * |a| ≤ 1 * 1 := mul_le_mul he ha (abs_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

/-- Uniform velocity bound in nonnegative time. -/
theorem shearFlow_norm_le_one (x : Vec3) (s : ℝ) (hs : 0 ≤ s) :
    ‖shearFlow (x, s)‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  by_cases hi : i = 0
  · simpa only [shearFlow, hi, ite_true] using
      amplitude_bound s (Real.sin (x 1)) hs (Real.abs_sin_le_one _)
  · simp [shearFlow, hi]

/-- Uniform explicit-gradient bound in nonnegative time. -/
theorem shearFlowGrad_norm_le_one (x : Vec3) (s : ℝ) (hs : 0 ≤ s) :
    ‖shearFlowGrad (x, s)‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro j
  by_cases hij : i = 0 ∧ j = 1
  · simp only [shearFlowGrad, hij]
    exact amplitude_bound s (Real.cos (x 1)) hs (Real.abs_cos_le_one _)
  · simp only [shearFlowGrad, hij, ite_false, norm_zero, zero_le_one]

private theorem enorm_sq_le_one {E : Type*} [NormedAddCommGroup E]
    (v : E) (hv : ‖v‖ ≤ 1) : ‖v‖ₑ ^ (2 : ℝ) ≤ 1 := by
  have he : ‖v‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact_mod_cast hv
  calc
    ‖v‖ₑ ^ (2 : ℝ) ≤ (1 : ℝ≥0∞) ^ (2 : ℝ) :=
      ENNReal.rpow_le_rpow he (by norm_num)
    _ = 1 := by simp

/-- All local measurability, finite-energy, and weak-gradient clauses. -/
theorem shearFlow_localData (Ω' : Set Vec3) (J : Set ℝ)
    (hbox : localBox Set.univ (Ioo 0 1) Ω' J) :
    AEStronglyMeasurable shearFlow (volume.restrict (spaceTimeSet Ω' J)) ∧
    AEStronglyMeasurable shearFlowGrad (volume.restrict (spaceTimeSet Ω' J)) ∧
    AEStronglyMeasurable (fun _ : ParabolicPoint => (0 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)) ∧
    AEStronglyMeasurable (fun _ : ParabolicPoint => (0 : Vec3))
      (volume.restrict (spaceTimeSet Ω' J)) ∧
    essSup (fun s => ∫⁻ x in Ω', ‖shearFlow (x, s)‖ₑ ^ (2 : ℝ))
      (volume.restrict J) < ⊤ ∧
    (∫⁻ z in spaceTimeSet Ω' J,
      ‖shearFlow z‖ₑ ^ (2 : ℝ) + ‖shearFlowGrad z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
    MemLp (fun _ : ParabolicPoint => (0 : ℝ)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)) ∧
    MemLp (fun _ : ParabolicPoint => (0 : Vec3)) (ENNReal.ofReal (3 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)) ∧
    ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
      HasWeakGradientOn Ω' (fun x => shearFlow (x, s) i)
        (fun x => shearFlowGrad (x, s) i) := by
  have hJ : MeasurableSet J := hbox.2.2.2.1.measurableSet
  have htime : ∀ s ∈ J, 0 ≤ s := fun s hs =>
    (hbox.2.2.2.2.2 (subset_closure hs)).1.le
  have hvolx : volume Ω' < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.1.measure_lt_top
  have hvolt : volume J < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top
  have hvol : volume (spaceTimeSet Ω' J) < ∞ := by
    change volume (Ω' ×ˢ J) < ∞
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top hvolx hvolt
  have hslices : ∀ᵐ s ∂volume.restrict J,
      (∫⁻ x in Ω', ‖shearFlow (x, s)‖ₑ ^ (2 : ℝ)) ≤ volume Ω' := by
    filter_upwards [ae_restrict_mem hJ] with s hs
    calc
      _ ≤ ∫⁻ _x in Ω', (1 : ℝ≥0∞) := lintegral_mono fun x =>
        enorm_sq_le_one _ (shearFlow_norm_le_one x s (htime s hs))
      _ = volume Ω' := by simp
  have hmeas : MeasurableSet (spaceTimeSet Ω' J) := hbox.1.measurableSet.prod hJ
  have henergy : (∫⁻ z in spaceTimeSet Ω' J,
      ‖shearFlow z‖ₑ ^ (2 : ℝ) + ‖shearFlowGrad z‖ₑ ^ (2 : ℝ)) < ∞ := by
    have hb : ∀ᵐ z ∂volume.restrict (spaceTimeSet Ω' J),
        ‖shearFlow z‖ₑ ^ (2 : ℝ) + ‖shearFlowGrad z‖ₑ ^ (2 : ℝ) ≤ 2 := by
      filter_upwards [ae_restrict_mem hmeas] with z hz
      have hs := htime z.2 hz.2
      exact (add_le_add (enorm_sq_le_one _ (shearFlow_norm_le_one z.1 z.2 hs))
        (enorm_sq_le_one _ (shearFlowGrad_norm_le_one z.1 z.2 hs))).trans_eq (by norm_num)
    calc
      _ ≤ ∫⁻ _z in spaceTimeSet Ω' J, (2 : ℝ≥0∞) := lintegral_mono_ae hb
      _ < ∞ := by simpa using ENNReal.mul_lt_top (by norm_num : (2 : ℝ≥0∞) < ∞) hvol
  refine ⟨shearFlow_smooth.continuous.measurable.aestronglyMeasurable,
    shearFlowGrad_smooth.continuous.measurable.aestronglyMeasurable,
    aestronglyMeasurable_const, aestronglyMeasurable_const,
    (essSup_le_of_ae_le _ hslices).trans_lt hvolx, henergy,
    MemLp.zero, MemLp.zero, ?_⟩
  intro i
  exact ae_of_all _ fun s => shearFlow_weakGradient Ω' s i

end CKN
