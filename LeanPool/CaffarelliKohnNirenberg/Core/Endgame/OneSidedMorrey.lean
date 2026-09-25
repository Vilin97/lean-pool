/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedGeometry
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic

/-!
# One-sided transfer of scalar Morrey estimates

This is Step 2 of the proof of `thm:A`, isolated as a statement about one
scalar function. The manuscript's Step 2 replaces the centre shift of
`lem:step2-morrey-balls`, which moves a centre forward in time by the square
of the radius, by a truncated shift that stops at the top face `t = 0`; see
`truncatedCylinderCenter`. Small cylinders are then covered by a cylinder of
twice the radius about an admissible centre, and the decay hypothesis
`eq:thmA-morrey` applies there. Large cylinders are paid for by the total
integral on the fixed intermediate cylinder, which is the manuscript's
unchanged large-radius case.

`oneSidedMorreyBound P τ ρ₀ A B` is the resulting constant. `A` is the
small-cell growth coefficient and `B` the total integral; the two enter
through the two regimes just described.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey


noncomputable section

namespace CKN.Core.Endgame

private theorem cylinderPowerIntegral_indicator_eq
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

theorem cylinder_morrey_cell_le
    {P τ : ℝ} {K : ℝ≥0∞} {g : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r : ℝ} (hP : 0 < P) (hr : 0 < r)
    (hI : cylinderPowerIntegral P g z r ≤
      K * ENNReal.ofReal (r ^ (5 * (1 - P / τ)))) :
    morreyCell P τ g z r ≤ K ^ (1 / P : ℝ) := by
  have hroot := ENNReal.rpow_le_rpow hI (one_div_nonneg.mpr hP.le)
  have hroot' : (cylinderPowerIntegral P g z r) ^ (1 / P : ℝ) ≤
      K ^ (1 / P : ℝ) * (ENNReal.ofReal r) ^ (5 * (1 - P / τ) / P) := by
    calc
      _ ≤ (K * ENNReal.ofReal (r ^ (5 * (1 - P / τ)))) ^ (1 / P : ℝ) := hroot
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hP.le),
          ← ENNReal.ofReal_rpow_of_pos hr, ← ENNReal.rpow_mul]
        congr 2
        ring
  have hcancel : (ENNReal.ofReal r) ^ (-(5 * (1 - P / τ) / P)) *
      (ENNReal.ofReal r) ^ (5 * (1 - P / τ) / P) = 1 := by
    rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hr).ne'
      ENNReal.ofReal_ne_top, neg_add_cancel, ENNReal.rpow_zero]
  rw [morreyCell_eq]
  calc
    _ ≤ (ENNReal.ofReal r) ^ (-(5 * (1 - P / τ) / P)) *
        (K ^ (1 / P : ℝ) * (ENNReal.ofReal r) ^ (5 * (1 - P / τ) / P)) :=
      mul_le_mul_of_nonneg_left hroot' (by positivity)
    _ = K ^ (1 / P : ℝ) := by
      rw [← mul_left_comm, hcancel, mul_one]

/-- The explicit small-scale plus large-scale constant for the one-sided
Morrey transfer. -/
def oneSidedMorreyBound (P τ ρ₀ : ℝ) (A B : ℝ≥0∞) : ℝ≥0∞ :=
  (A * ENNReal.ofReal ((2 : ℝ) ^ (5 * (1 - P / τ)))) ^ (1 / P : ℝ) +
    ENNReal.ofReal ((ρ₀ / 2) ^ (-(5 * (1 - P / τ) / P))) * B ^ (1 / P : ℝ)

/-- Finite integral constants give a finite transfer constant. -/
theorem oneSidedMorreyBound_lt_top
    {P τ ρ₀ : ℝ} {A B : ℝ≥0∞}
    (hP : 0 < P) (hA : A < ⊤) (hB : B < ⊤) :
    oneSidedMorreyBound P τ ρ₀ A B < ⊤ := by
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hP.le)
      (ENNReal.mul_ne_top hA.ne ENNReal.ofReal_ne_top)
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hP.le) hB.ne)

/-- Small-scale cylinder estimates at admissible centers and a total
integral bound imply an explicit Morrey estimate on the one-sided
intermediate cylinder. No measurability of the scalar function is needed
for this upper-integral estimate. -/
theorem morreyNorm_one_sided_indicator_le_on_cylinder
    (a P τ ρ₀ : ℝ) (A B : ℝ≥0∞)
    (ha : 0 < a) (ha34 : a < 3 / 4)
    (hP : 1 ≤ P) (hPτ : P ≤ τ) (hρ₀ : 0 < ρ₀)
    (g : ParabolicPoint → ℝ)
    (hsmall : ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
      ∀ r : ℝ, 0 < r → r ≤ ρ₀ → cylinderPowerIntegral P g z r ≤
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
  have hrepr := cylinderPowerIntegral_indicator_eq hPpos hS g
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  change morreyCell P τ (S.indicator g) z r.1 ≤ oneSidedMorreyBound P τ ρ₀ A B
  by_cases hsmallr : r.1 ≤ ρ₀ / 2
  · have hI : cylinderPowerIntegral P (S.indicator g) z r.1 ≤
        (A * ENNReal.ofReal ((2 : ℝ) ^ (5 * (1 - P / τ)))) *
          ENNReal.ofReal (r.1 ^ (5 * (1 - P / τ))) := by
      rw [hrepr]
      by_cases hmeet : (parabolicCylinder z.1 z.2 r.1 ∩ S).Nonempty
      · obtain ⟨w', _hw', hcenter, hcover⟩ :=
          exists_one_sided_covering_cylinder_on_cylinder ha ha34 hmeet
        have hsub : parabolicCylinder z.1 z.2 r.1 ∩ S ⊆
            parabolicCylinder (truncatedCylinderCenter z w' r.1 0).1
              (truncatedCylinderCenter z w' r.1 0).2 (2 * r.1) := by
          intro w hw
          exact hcover ⟨hw.1, hw.2.2.2⟩
        calc
          _ ≤ cylinderPowerIntegral P g (truncatedCylinderCenter z w' r.1 0)
              (2 * r.1) := lintegral_mono_set hsub
          _ ≤ A * ENNReal.ofReal ((2 * r.1) ^ (5 * (1 - P / τ))) :=
            hsmall _ hcenter _ (mul_pos (by norm_num) r.2) (by linarith only [hsmallr])
          _ = _ := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) r.2.le,
              ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), mul_assoc]
      · rw [Set.not_nonempty_iff_eq_empty.mp hmeet, Measure.restrict_empty, lintegral_zero_measure]
        exact bot_le
    exact (cylinder_morrey_cell_le hPpos r.2 hI).trans
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

/-- Specialization of the quantitative transfer to the fixed intermediate cylinder. -/
theorem morreyNorm_one_sided_indicator_le
    (P τ ρ₀ : ℝ) (A B : ℝ≥0∞)
    (hP : 1 ≤ P) (hPτ : P ≤ τ) (hρ₀ : 0 < ρ₀)
    (g : ParabolicPoint → ℝ)
    (hsmall : ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
      ∀ r : ℝ, 0 < r → r ≤ ρ₀ → cylinderPowerIntegral P g z r ≤
        A * ENNReal.ofReal (r ^ (5 * (1 - P / τ))))
    (hglobal : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 (5 / 8),
      ENNReal.ofReal |g w| ^ P) ≤ B) :
    morreyNorm P τ ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator g) ≤
      oneSidedMorreyBound P τ ρ₀ A B :=
  morreyNorm_one_sided_indicator_le_on_cylinder (5 / 8) P τ ρ₀ A B
    (by norm_num) (by norm_num) hP hPτ hρ₀ g hsmall hglobal

end CKN.Core.Endgame
