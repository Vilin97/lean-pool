/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOneSidedCell

/-!
# The backward carrier and the time windows that can contribute to it

The one-sided pressure-gradient estimate of `prop:bootstrap` measures the
selected gradient only through the indicator of the backward cylinder
`parabolicCylinder 0 0 R₁`.  Every cell of that indicator therefore sees the
gradient only on the intersection of the cell with that cylinder, and the time
factor of the intersection is contained in `(-R₁ ^ 2, 0]`, whatever the cell
centre and radius are.

This module records that geometry.  The product decomposition of the
intersection separates the spatial and temporal factors; the window inclusion
says that the contributing times of a cell always lie in the time factor
`(-1, 0]` of the unit cylinder, so a cell bound stated for the intersection
never refers to times outside the region controlled by the data hypothesis of
`thm:A`.  The last theorem is the composition with the one-sided Morrey
transfer: cell bounds for the gradient *restricted to the backward carrier*
give the Morrey cell output the estimate consumes.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame


noncomputable section

namespace CKN.Core.Step4

/-- The backward cylinder at the origin as a space-time product. -/
theorem parabolicCylinder_origin_eq_prod (R : ℝ) :
    parabolicCylinder (0 : Vec3) 0 R = vec3Ball (0 : Vec3) R ×ˢ Ioc (-(R ^ 2)) 0 := by
  rw [parabolicCylinder, zero_sub]

/-- A cell meets the backward carrier in the product of the intersected
spatial balls with the intersected time windows. -/
theorem parabolicCylinder_inter_origin_eq_prod (x : Vec3) (t r R : ℝ) :
    parabolicCylinder x t r ∩ parabolicCylinder (0 : Vec3) 0 R =
      (vec3Ball x r ∩ vec3Ball (0 : Vec3) R) ×ˢ
        (Ioc (t - r ^ 2) t ∩ Ioc (-(R ^ 2)) 0) := by
  ext w
  constructor
  · rintro ⟨h1, h2⟩
    rw [parabolicCylinder_origin_eq_prod] at h2
    exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  · rintro ⟨hx, ht⟩
    refine ⟨⟨hx.1, ht.1⟩, ?_⟩
    rw [parabolicCylinder_origin_eq_prod]
    exact ⟨hx.2, ht.2⟩

/-- Whatever the cell centre and radius, the times of the cell that can
contribute to the backward carrier lie in the time factor of the unit
cylinder.  No restriction on `R` beyond `R ≤ 1` is needed, and in particular
none beyond the range `0 < R₁ < R₀ < 3/4` of `prop:bootstrap`. -/
theorem originClauseWindow_subset_unitTime {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 1) (t r : ℝ) :
    Ioc (t - r ^ 2) t ∩ Ioc (-(R ^ 2)) 0 ⊆ Ioc (-1 : ℝ) 0 := by
  intro s hs
  have hRsq : R ^ 2 ≤ 1 := by nlinarith only [hR0, hR]
  exact ⟨by linarith only [hs.2.1, hRsq], hs.2.2⟩

/-- Under the domain hypothesis of `thm:A` the contributing times of every
cell lie in the solution interval. -/
theorem originClauseWindow_subset_of_unitTime {I : Set ℝ} {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ 1) (hI : Icc (-1 : ℝ) 0 ⊆ I) (t r : ℝ) :
    Ioc (t - r ^ 2) t ∩ Ioc (-(R ^ 2)) 0 ⊆ I :=
  (originClauseWindow_subset_unitTime hR0 hR t r).trans
    (fun _ hs => hI ⟨hs.1.le, hs.2⟩)





/-- The power integral of a function cut off outside a measurable set is the
power integral of the function over the intersection. -/
theorem cylinderPowerIntegral_carrier_eq
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

/-- The backward carrier is measurable. -/
theorem measurableSet_parabolicCylinder_origin (R : ℝ) :
    MeasurableSet (parabolicCylinder (0 : Vec3) 0 R) :=
  (vec3Ball_measurable (0 : Vec3) R).prod measurableSet_Ioc

/-- Cell bounds for the gradient **restricted to the backward carrier**, at
admissible centres and radii, together with the total integral on the carrier,
give the Morrey cell output of `prop:bootstrap`.  This is the one-sided
transfer `morreyNorm_one_sided_indicator_le_on_cylinder` applied to the cut-off
field, so it needs no hypothesis about the gradient at times outside
`(-R₁ ^ 2, 0]`. -/
theorem originCellOutput_of_carrier_cell_bounds
    {R₁ κ : ℝ} {A B : ℝ≥0∞} {Dp : ParabolicPoint → Vec3}
    (hR₁ : 0 < R₁) (hR₁34 : R₁ < 3 / 4) (hκ : 6 / 5 ≤ κ)
    (hsmall : ∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
      ∀ r : ℝ, 0 < r → r ≤ R₁ →
      (∫⁻ w in parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R₁,
        ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
        A * ENNReal.ofReal (r ^ (5 * (1 - (6 / 5 : ℝ) / κ))))
    (hglobal : ∀ i : Fin 3,
      (∫⁻ w in parabolicCylinder (0 : Vec3) 0 R₁,
        ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤ B) :
    oneSidedPressureGradientOriginCellOutput R₁ κ
      (oneSidedMorreyBound (6 / 5) κ R₁ A B) Dp := by
  intro i z r
  set S : Set ParabolicPoint := parabolicCylinder (0 : Vec3) 0 R₁ with hS
  have hSmeas : MeasurableSet S := measurableSet_parabolicCylinder_origin R₁
  have key := morreyNorm_one_sided_indicator_le_on_cylinder R₁ (6 / 5 : ℝ) κ R₁ A B
    hR₁ hR₁34 (by norm_num) hκ hR₁ (S.indicator (fun w => Dp w i)) ?_ ?_
  · have hidem : S.indicator (S.indicator (fun w => Dp w i))
        = S.indicator (fun w => Dp w i) := by
      rw [Set.indicator_indicator, Set.inter_self]
    rw [hidem] at key
    refine le_trans ?_ key
    exact le_iSup₂ (f := fun (z : ParabolicPoint) (r : {r : ℝ // 0 < r}) =>
      morreyCell (6 / 5 : ℝ) κ (S.indicator (fun w => Dp w i)) z r.1) z r
  · intro w hw ρ hρ hρR
    rw [cylinderPowerIntegral_carrier_eq (by norm_num : (0 : ℝ) < 6 / 5) hSmeas]
    exact hsmall i w hw ρ hρ hρR
  · refine le_trans (le_of_eq ?_) (hglobal i)
    refine setLIntegral_congr_fun hSmeas ?_
    intro w hw
    have hval : S.indicator (fun w => Dp w i) w = Dp w i := Set.indicator_of_mem hw _
    simp only [hval]

end CKN.Core.Step4
