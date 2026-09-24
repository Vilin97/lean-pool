/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotLargeCellsGeometry

/-! # An absolute lattice cover for thin pressure collars

The doubled cells have radius `1/512`, below both prescribed half-collars.
The existing shifted-centre construction keeps every centre in the carrier.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- The lattice indices that a cell of radius `1/1024` can carry while
meeting the origin carrier of radius `R < 3/4`. -/
def originASlotThinCoverBox : Finset ((Fin 3 → ℤ) × ℤ) :=
  (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1538 : ℤ) 1538)) ×ˢ
    (Finset.Icc (-1179648 : ℤ) 2)

/-- The index box has `3077³ · 1179651` members. -/
theorem originASlotThinCoverBox_card : originASlotThinCoverBox.card = 34366557335620983 := by
  have hp := Finset.card_product
    (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1538 : ℤ) 1538))
    (Finset.Icc (-1179648 : ℤ) 2)
  have hpi := Fintype.card_piFinset (fun _ : Fin 3 => Finset.Icc (-1538 : ℤ) 1538)
  rw [hpi] at hp
  have hc₁ : (Finset.Icc (-1538 : ℤ) 1538).card = 3077 := by
    rw [Int.card_Icc]
    rfl
  have hc₂ : (Finset.Icc (-1179648 : ℤ) 2).card = 1179651 := by
    rw [Int.card_Icc]
    rfl
  simp only [hc₁, hc₂, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  rw [originASlotThinCoverBox, hp]
  norm_num

/-- A lattice cell of radius `1/1024` that meets the carrier of radius `R`
has its index in the absolute box. -/
theorem originASlotThinCoverBox_mem {R a : ℝ} (hR : 0 < R) (hRlt : R < 3 / 4)
    (ha : a = 1 / 1024) {k : (Fin 3 → ℤ) × ℤ} {w : ParabolicPoint}
    (hcell : w ∈ parabolicCylinder (originLatticeCentre a k).1
      (originLatticeCentre a k).2 a)
    (hcarrier : w ∈ parabolicCylinder (0 : Vec3) 0 R) :
    k ∈ originASlotThinCoverBox := by
  have hapos : 0 < a := by rw [ha]; norm_num
  have hmargin : R ≤ 768 * a := by rw [ha]; linarith only [hRlt]
  have hspace : ∀ i : Fin 3, |w.1 i - a / 2 * (k.1 i : ℝ)| < a := by
    intro i
    have h := (abs_apply_le_vec3EuclideanNorm
      (w.1 - (originLatticeCentre a k).1) i).trans_lt hcell.1
    simpa only [originLatticeCentre, Pi.sub_apply] using h
  have hcar : ∀ i : Fin 3, |w.1 i| < R := by
    intro i
    have h := (abs_apply_le_vec3EuclideanNorm (w.1 - (0 : Vec3)) i).trans_lt hcarrier.1
    simpa only [sub_zero] using h
  have hindex : ∀ i : Fin 3, k.1 i ∈ Finset.Icc (-1538 : ℤ) 1538 := by
    intro i
    obtain ⟨h₁, h₂⟩ := abs_lt.mp (hspace i)
    obtain ⟨h₃, h₄⟩ := abs_lt.mp (hcar i)
    have hb : |a / 2 * (k.1 i : ℝ)| < R + a :=
      abs_lt.mpr ⟨by linarith only [h₂, h₃], by linarith only [h₁, h₄]⟩
    have hsplit : |a / 2 * (k.1 i : ℝ)| = a / 2 * |(k.1 i : ℝ)| := by
      rw [abs_mul, abs_of_pos (by linarith only [hapos] : (0 : ℝ) < a / 2)]
    rw [hsplit] at hb
    have hmul : a / 2 * |(k.1 i : ℝ)| < a / 2 * 1538 := by
      have : R + a ≤ a / 2 * 1538 := by linarith only [hmargin]
      linarith only [hb, this]
    have hlt : |(k.1 i : ℝ)| < 1538 :=
      lt_of_mul_lt_mul_left hmul (by linarith only [hapos])
    obtain ⟨h₅, h₆⟩ := abs_lt.mp hlt
    have h₇ : (-1538 : ℤ) < k.1 i := by exact_mod_cast h₅
    have h₈ : k.1 i < (1538 : ℤ) := by exact_mod_cast h₆
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have htime : k.2 ∈ Finset.Icc (-1179648 : ℤ) 2 := by
    have hupper : w.2 ≤ a ^ 2 / 2 * (k.2 : ℝ) := hcell.2.2
    have hlower : a ^ 2 / 2 * (k.2 : ℝ) - a ^ 2 < w.2 := hcell.2.1
    have hcarlow : (0 : ℝ) - R ^ 2 < w.2 := hcarrier.2.1
    have hcarhigh : w.2 ≤ 0 := hcarrier.2.2
    have hasq : 0 < a ^ 2 / 2 := by positivity
    have hRsq : R ^ 2 ≤ 589824 * a ^ 2 := by
      have h : R ≤ 768 * a := hmargin
      nlinarith only [h, hR, hapos]
    have hbig : a ^ 2 / 2 * (-1179648 : ℝ) < a ^ 2 / 2 * (k.2 : ℝ) := by
      have : a ^ 2 / 2 * (-1179648 : ℝ) = -(589824 * a ^ 2) := by ring
      rw [this]
      linarith only [hupper, hcarlow, hRsq]
    have hsmallidx : a ^ 2 / 2 * (k.2 : ℝ) < a ^ 2 / 2 * 2 := by
      have : a ^ 2 / 2 * (2 : ℝ) = a ^ 2 := by ring
      rw [this]
      linarith only [hlower, hcarhigh]
    have h₁ : (-1179648 : ℝ) < (k.2 : ℝ) := lt_of_mul_lt_mul_left hbig hasq.le
    have h₂ : (k.2 : ℝ) < 2 := lt_of_mul_lt_mul_left hsmallidx hasq.le
    have h₃ : (-1179648 : ℤ) < k.2 := by exact_mod_cast h₁
    have h₄ : k.2 < (2 : ℤ) := by exact_mod_cast h₂
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  simp only [originASlotThinCoverBox, Finset.mem_product, Fintype.mem_piFinset]
  exact ⟨hindex, htime⟩

-- The index box is used only through its cardinality and its membership
-- criterion, never through its normal form.
attribute [irreducible] originASlotThinCoverBox

/-- The origin carrier is covered by the doubled margin cells attached to the
lattice indices of the absolute box.  Every centre used lies in the carrier and
every radius used is `1/512`. -/
theorem originASlot_carrier_subset_thin_cells {R a : ℝ} (hR : 0 < R) (hRlt : R < 3 / 4)
    (ha : a = 1 / 1024) :
    parabolicCylinder (0 : Vec3) 0 R ⊆
      ⋃ k ∈ originASlotThinCoverBox,
        parabolicCylinder
          (originASlotShiftedCentre R (originLatticeCentre a k) a).1
          (originASlotShiftedCentre R (originLatticeCentre a k) a).2 (2 * a) := by
  have hapos : 0 < a := by rw [ha]; norm_num
  intro w hw
  obtain ⟨k, hk⟩ := originLattice_covers a hapos w
  have hmem : k ∈ originASlotThinCoverBox := originASlotThinCoverBox_mem hR hRlt ha hk hw
  refine Set.mem_iUnion₂.mpr ⟨k, Finset.mem_coe.mpr hmem, ?_⟩
  exact originASlotShiftedCentre_subset hapos (originLatticeCentre a k) ⟨hk, hw⟩


end CKN.Core.Step4
