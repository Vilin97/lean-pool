/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMorrey

/-!
# One-sided transfer with carrier-centred cells

The cells that the one-sided transfer actually consumes are the ones centred
in the carrier cylinder itself: each small cylinder meeting the carrier has a
truncated centre that already lies in the carrier, so the growth input can be,
and here is, restricted to the carrier's own centres rather than to a larger
fixed cylinder. The transfer still covers every cell, because cells whose
centre is not met by the carrier contribute nothing, and cells at or above the
fixed scale are handled by the total integral on the carrier.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- Any cylinder meeting the carrier cylinder has a truncated centre inside the
carrier whose doubled-radius cylinder covers the cylinder's whole portion below
time zero. -/
theorem exists_one_sided_covering_cylinder_on_carrier
    {a : ℝ} {w : ParabolicPoint} {ρ : ℝ}
    (hmeet : (parabolicCylinder w.1 w.2 ρ ∩
      parabolicCylinder (0 : Vec3) 0 a).Nonempty) :
    ∃ c : ParabolicPoint, c ∈ parabolicCylinder (0 : Vec3) 0 a ∧
      parabolicCylinder w.1 w.2 ρ ∩ {z : ParabolicPoint | z.2 ≤ 0} ⊆
        parabolicCylinder c.1 c.2 (2 * ρ) := by
  obtain ⟨w', hw'⟩ := hmeet
  exact ⟨truncatedCylinderCenter w w' ρ 0,
    truncatedCylinderCenter_mem hw'.1 hw'.2,
    parabolicCylinder_inter_le_subset_truncated hw'.1⟩

/-- The power integral of an indicator is the integral of the power of the
function over the cylinder intersected with the underlying set. -/
theorem cylinderPowerIntegral_indicator_inter
    {P : ℝ} (hP : 0 < P) {S : Set ParabolicPoint} (hS : MeasurableSet S)
    (g : ParabolicPoint → ℝ) (z : ParabolicPoint) (r : ℝ) :
    cylinderPowerIntegral P (S.indicator g) z r =
      ∫⁻ w in parabolicCylinder z.1 z.2 r ∩ S, ENNReal.ofReal |g w| ^ P := by
  have heq : (fun w => ENNReal.ofReal |S.indicator g w| ^ P) =
      S.indicator (fun w => ENNReal.ofReal |g w| ^ P) := by
    funext w
    by_cases hw : w ∈ S
    · simp only [indicator_of_mem hw]
    · simp only [indicator_of_notMem hw, abs_zero, ENNReal.ofReal_zero,
        ENNReal.zero_rpow_of_pos hP]
  rw [cylinderPowerIntegral, heq, lintegral_indicator hS,
    Measure.restrict_restrict hS, inter_comm S]

private theorem cylinder_morrey_cell_le'
    {P τ : ℝ} {K : ℝ≥0∞} {g : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r : ℝ} (hP : 0 < P) (hr : 0 < r)
    (hI : cylinderPowerIntegral P g z r ≤
      K * ENNReal.ofReal (r ^ (5 * (1 - P / τ)))) :
    morreyCell P τ g z r ≤ K ^ (1 / P : ℝ) := by
  exact _root_.CKN.Core.Endgame.cylinder_morrey_cell_le hP hr hI

/-- Small-scale cylinder estimates at carrier centres and a total integral
bound on the carrier imply an explicit Morrey estimate for the one-sided
indicator of the carrier, with no upper bound on the carrier radius. -/
theorem morreyNorm_one_sided_indicator_le_of_carrier_cells
    (a P τ ρ₀ : ℝ) (A B : ℝ≥0∞)
    (hP : 1 ≤ P) (hPτ : P ≤ τ) (hρ₀ : 0 < ρ₀)
    (g : ParabolicPoint → ℝ)
    (hsmall : ∀ c ∈ parabolicCylinder (0 : Vec3) 0 a,
      ∀ r : ℝ, 0 < r → r ≤ ρ₀ → cylinderPowerIntegral P g c r ≤
        A * ENNReal.ofReal (r ^ (5 * (1 - P / τ))))
    (hglobal : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 a,
      ENNReal.ofReal |g w| ^ P) ≤ B) :
    morreyNorm P τ ((parabolicCylinder (0 : Vec3) 0 a).indicator g) ≤
      oneSidedMorreyBound P τ ρ₀ A B := by
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hτpos : 0 < τ := hPpos.trans_le hPτ
  have hexponent : 0 ≤ 5 * (1 - P / τ) := mul_nonneg (by norm_num)
    (sub_nonneg.mpr ((div_le_one hτpos).mpr hPτ))
  let S : Set ParabolicPoint := parabolicCylinder (0 : Vec3) 0 a
  have hS : MeasurableSet S :=
    (vec3Ball_measurable (0 : Vec3) a).prod measurableSet_Ioc
  have hrepr := cylinderPowerIntegral_indicator_inter hPpos hS g
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  change morreyCell P τ (S.indicator g) z r.1 ≤ oneSidedMorreyBound P τ ρ₀ A B
  by_cases hsmallr : r.1 ≤ ρ₀ / 2
  · have hI : cylinderPowerIntegral P (S.indicator g) z r.1 ≤
        (A * ENNReal.ofReal ((2 : ℝ) ^ (5 * (1 - P / τ)))) *
          ENNReal.ofReal (r.1 ^ (5 * (1 - P / τ))) := by
      rw [hrepr]
      by_cases hmeet : (parabolicCylinder z.1 z.2 r.1 ∩ S).Nonempty
      · obtain ⟨c, hcenter, hcover⟩ :=
          exists_one_sided_covering_cylinder_on_carrier hmeet
        have hsub : parabolicCylinder z.1 z.2 r.1 ∩ S ⊆
            parabolicCylinder c.1 c.2 (2 * r.1) := by
          intro w hw
          exact hcover ⟨hw.1, hw.2.2.2⟩
        calc
          _ ≤ cylinderPowerIntegral P g c (2 * r.1) := lintegral_mono_set hsub
          _ ≤ A * ENNReal.ofReal ((2 * r.1) ^ (5 * (1 - P / τ))) :=
            hsmall c hcenter _ (mul_pos (by norm_num) r.2)
              (by linarith only [hsmallr])
          _ = _ := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) r.2.le,
              ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), mul_assoc]
      · rw [Set.not_nonempty_iff_eq_empty.mp hmeet, Measure.restrict_empty,
          lintegral_zero_measure]
        exact bot_le
    exact (cylinder_morrey_cell_le' hPpos r.2 hI).trans
      (le_add_right le_rfl)
  · have hI : cylinderPowerIntegral P (S.indicator g) z r.1 ≤ B := by
      rw [hrepr]
      exact (lintegral_mono_set inter_subset_right).trans hglobal
    have hscale : (ENNReal.ofReal r.1) ^ (-(5 * (1 - P / τ) / P)) ≤
        ENNReal.ofReal ((ρ₀ / 2) ^ (-(5 * (1 - P / τ) / P))) := by
      rw [ENNReal.ofReal_rpow_of_pos r.2]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos
        (by positivity : 0 < ρ₀ / 2) (le_of_not_ge hsmallr)
        (neg_nonpos.mpr (div_nonneg hexponent hPpos.le)))
    rw [morreyCell_eq]
    exact (mul_le_mul' hscale
      (ENNReal.rpow_le_rpow hI (one_div_nonneg.mpr hPpos.le))).trans
        (le_add_left le_rfl)

end CKN.Core.Step4
