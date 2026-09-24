/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientInputsCentred

/-! # Temporal bounds for the centring velocity

The local kinetic-energy essential supremum controls the spatial velocity
mean. Thus centring the tensor introduces bounded temporal coefficients,
not an additional assumption on the suitable solution.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- A component mean is bounded by the volume plus the kinetic energy,
with the exact normalization factor of the spatial average. -/
theorem pressure_source_mean_enorm_bound
    (v : Vec3 → Vec3) (B : Set Vec3) (i : Fin 3) :
    ‖average (volume.restrict B) (fun y => v y i)‖ₑ ≤
      ENNReal.ofReal (((volume B).toReal)⁻¹) *
        (volume B + ∫⁻ y in B, ‖v y‖ₑ ^ (2 : ℝ)) := by
  have hpoint : ∀ y : Vec3, ‖v y i‖ₑ ≤ 1 + ‖v y‖ₑ ^ (2 : ℝ) := by
    intro y
    have hcomp : |v y i| ≤ ‖v y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (v y) i
    have hs : ‖v y‖ ≤ 1 + ‖v y‖ ^ 2 := by nlinarith only [sq_nonneg (‖v y‖ - 1 / 2)]
    rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm]
    rw [ENNReal.rpow_ofNat, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hcomp.trans hs)
  rw [average_eq, smul_eq_mul, enorm_mul, Real.enorm_eq_ofReal_abs,
    abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg), measureReal_def,
    Measure.restrict_apply_univ]
  apply mul_le_mul_right
  calc
    _ ≤ ∫⁻ y in B, ‖v y i‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y in B, 1 + ‖v y‖ₑ ^ (2 : ℝ) := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_add_left measurable_const, lintegral_const,
        Measure.restrict_apply_univ, one_mul]

/-- Suitable weak solutions supply a finite temporal bound for each
component of the mean on every relatively compact spatial box. -/
theorem pressure_source_mean_ae_bounded_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {B : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I B J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ s ∂(volume.restrict J), ∀ i : Fin 3,
      |average (volume.restrict B) (fun y : Vec3 => u (y, s) i)| ≤ C := by
  let E : ℝ≥0∞ := essSup (fun s => ∫⁻ y in B, ‖u (y, s)‖ₑ ^ (2 : ℝ)) (volume.restrict J)
  have hE : E < ⊤ := (hsol.2.2.2.2.2.1 B J hbox).2.2.2.2.1
  have hB : volume B < ⊤ := (measure_mono subset_closure).trans_lt hbox.2.1.measure_lt_top
  let K : ℝ≥0∞ := ENNReal.ofReal (((volume B).toReal)⁻¹) * (volume B + E)
  have hK : K < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨hB, hE⟩)
  refine ⟨K.toReal, ENNReal.toReal_nonneg, ?_⟩
  filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict J)
    (fun s : ℝ => ∫⁻ y in B, ‖u (y, s)‖ₑ ^ (2 : ℝ))] with s hs
  intro i
  have h := (pressure_source_mean_enorm_bound (fun y => u (y, s)) B i).trans
    (mul_le_mul_right (add_le_add_right hs (volume B)) _)
  rw [Real.enorm_eq_ofReal_abs] at h
  exact (ENNReal.ofReal_le_iff_le_toReal hK.ne).mp h

/-- The centring mean is measurable in time on each suitable-solution box. -/
theorem pressure_source_mean_aemeasurable_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {B : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I B J) (i : Fin 3) :
    AEMeasurable (fun s : ℝ => average (volume.restrict B)
      (fun y : Vec3 => u (y, s) i)) (volume.restrict J) := by
  have hu := (hsol.2.2.2.2.2.1 B J hbox).1
  have hcomp : AEStronglyMeasurable (fun z : ParabolicPoint => u z i)
      (volume.restrict (B ×ˢ J)) :=
    ((measurable_pi_apply i).comp_aemeasurable hu.aemeasurable).aestronglyMeasurable
  have hprod : AEStronglyMeasurable (fun z : Vec3 × ℝ => u z i)
      ((volume.restrict B).prod (volume.restrict J)) := by
    have hμ : (volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ J) =
        (volume.restrict B).prod (volume.restrict J) := by
      rw [Measure.volume_eq_prod, Measure.prod_restrict]
    exact hμ ▸ hcomp
  have hm := hprod.prod_swap.integral_prod_right'.aemeasurable
  simp_rw [average_eq, smul_eq_mul]
  exact hm.const_mul _

end CKN.Core.Step4
