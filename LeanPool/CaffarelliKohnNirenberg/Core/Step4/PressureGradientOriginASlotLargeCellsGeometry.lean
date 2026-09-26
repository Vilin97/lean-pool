/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.KappaCapArithmetic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPAffineSlot
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginLatticeCover
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.OffCentreInclusion

/-! # Margin cells for the origin pressure-gradient budget of `prop:bootstrap`

A clipped cell of the origin carrier may have its centre anywhere, and its
radius may exceed the margin `(1 - R₁)/4` on which the small-cell estimate of
`prop:bootstrap` is available.  Two elementary devices repair both defects.

* A cell clipped to the carrier is contained in a cell of twice the radius
  whose centre lies in the carrier itself: take the space coordinate of any
  point of the clipped cell and the smaller of the cell's final time and `0`.
* The carrier is covered by finitely many lattice cells of radius
  `(1 - R₁)/16`.  Since `R₁ < 3/4` the lattice indices that can occur lie in
  one absolute box, so the number of cells used is an absolute constant.

Together they reduce every clipped cell to margin cells centred in the carrier,
at the cost of one absolute multiplicative constant.
-/

public section

section

/-!
# Growth Exponent Arithmetic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

noncomputable section

namespace CKN.Core.Step4

/-- Lower bound `59/25` for the growth exponent when `q > 5/2` and `τ ≥ 25/3`. -/
theorem growth_exponent_lower {q τ : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) :
    59 / 25 ≤ 5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) := by
  set κ := min ((1 / τ + 8 / 25)⁻¹) q
  have hkappa_ge : 25 / 11 ≤ κ := by
    have hbase : min (25 / 11 : ℝ) q = 25 / 11 := min_twentyFive_div_eleven_q hq
    have hle : min (25 / 11 : ℝ) q ≤ min ((1 / τ + 8 / 25)⁻¹) q := min_kappa_base_le hτ
    linarith only [hbase, hle]
  have hτpos : 0 < τ := by
    have hpos : 0 < (25 : ℝ) / 3 := by norm_num
    linarith only [hpos, hτ]
  have hqpos : 0 < q := by linarith only [hq]
  have hkappa_pos : 0 < κ := min_kappa_pos hτpos hqpos
  have hone_div : 1 / κ ≤ 11 / 25 := by
    have hpos_25_11 : 0 < (25 / 11 : ℝ) := by norm_num
    have h := one_div_le_one_div_of_le hpos_25_11 hkappa_ge
    simpa [div_div] using h
  have hdiv : 6 / κ ≤ 66 / 25 := by
    calc
      6 / κ = 6 * (1 / κ) := by ring
      _ ≤ 6 * (11 / 25) := by
        nlinarith only [hone_div]
      _ = 66 / 25 := by norm_num
  have htarget : 5 * (1 - (6 / 5 : ℝ) / κ) = 5 - 6 / κ := by ring
  rw [htarget]
  nlinarith only [hdiv]

/-- Positivity of the growth exponent when `q > 5/2` and `τ ≥ 25/3`. -/
theorem growth_exponent_pos {q τ : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) :
    0 < 5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) := by
  have h := growth_exponent_lower hq hτ
  linarith only [h]

/-- Upper bound `71/25` for the growth exponent when `0 < τ ≤ 25` and `q > 0`. -/
theorem growth_exponent_upper {q τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 25) (hq : 0 < q) :
    5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) ≤ 71 / 25 := by
  set κ := min ((1 / τ + 8 / 25)⁻¹) q
  have hkappa_pos : 0 < κ := min_kappa_pos hτ hq
  have hkappa_le_inv : κ ≤ (1 / τ + 8 / 25)⁻¹ := min_le_left _ _
  have hinv_le_25_9 : (1 / τ + 8 / 25)⁻¹ ≤ 25 / 9 := by
    have hsum : 9 / 25 ≤ 1 / τ + 8 / 25 := by
      have hone_div : 1 / 25 ≤ 1 / τ := one_div_le_one_div_of_le hτ hτ'
      linarith only [hone_div]
    have hpos_sum : 0 < 1 / τ + 8 / 25 := by positivity
    have hpos_9_25 : 0 < (9 : ℝ) / 25 := by norm_num
    have h := ((inv_le_inv₀ hpos_sum hpos_9_25).mpr hsum)
    simpa [div_div] using h
  have hkappa_le : κ ≤ 25 / 9 := le_trans hkappa_le_inv hinv_le_25_9
  have hone_div_ge : 9 / 25 ≤ 1 / κ := by
    have h := one_div_le_one_div_of_le hkappa_pos hkappa_le
    simpa [div_div] using h
  have hdiv : 54 / 25 ≤ 6 / κ := by
    calc
      54 / 25 = 6 * (9 / 25) := by norm_num
      _ ≤ 6 * (1 / κ) := by
        nlinarith only [hone_div_ge]
      _ = 6 / κ := by ring
  have htarget : 5 * (1 - (6 / 5 : ℝ) / κ) = 5 - 6 / κ := by ring
  rw [htarget]
  nlinarith only [hdiv]

/-- Monotonicity of `r ^ (growth exponent)` in the base when the exponent is positive. -/
theorem rpow_growth_exponent_mono {q τ r R : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ)
    (hr : 0 ≤ r) (hrR : r ≤ R) :
    r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) ≤
      R ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) := by
  have hexp_pos : 0 < 5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) :=
    growth_exponent_pos hq hτ
  exact Real.rpow_le_rpow hr hrR hexp_pos.le

end CKN.Core.Step4
end

end

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-! ### The doubled cell centred in the carrier -/

open scoped Classical in
/-- A centre in the carrier for the cell `parabolicCylinder z.1 z.2 r` clipped to
the carrier of radius `R`: the space coordinate of a point of the clipped cell,
and the final time of the cell capped at `0`.  The default value is the carrier
centre, which lies in the carrier whenever `R` is positive. -/
def originASlotShiftedCentre (R : ℝ) (z : ParabolicPoint) (r : ℝ) : ParabolicPoint :=
  if h : (parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R).Nonempty then
    (h.choose.1, min z.2 0)
  else ((0 : Vec3), (0 : ℝ))

/-- The shifted centre is the space coordinate of a point of the clipped cell,
paired with the capped final time. -/
private theorem originASlotShiftedCentre_of_nonempty {R : ℝ} {z : ParabolicPoint} {r : ℝ}
    (h : (parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R).Nonempty) :
    originASlotShiftedCentre R z r = (h.choose.1, min z.2 0) :=
  dite_eq_left h

/-- On an empty clipped cell the shifted centre is the carrier centre. -/
private theorem originASlotShiftedCentre_of_empty {R : ℝ} {z : ParabolicPoint} {r : ℝ}
    (h : ¬ (parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R).Nonempty) :
    originASlotShiftedCentre R z r = ((0 : Vec3), (0 : ℝ)) :=
  dite_eq_right h

/-- The shifted centre lies in the carrier. -/
theorem originASlotShiftedCentre_mem {R : ℝ} (hR : 0 < R) (z : ParabolicPoint) (r : ℝ) :
    originASlotShiftedCentre R z r ∈ parabolicCylinder (0 : Vec3) 0 R := by
  by_cases h : (parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R).Nonempty
  · rw [originASlotShiftedCentre_of_nonempty h]
    obtain ⟨hcell, hcar⟩ := h.choose_spec
    refine ⟨hcar.1, ?_, ?_⟩
    · have hw : (0 : ℝ) - R ^ 2 < h.choose.2 := hcar.2.1
      have hz : h.choose.2 ≤ z.2 := hcell.2.2
      have hzero : h.choose.2 ≤ 0 := hcar.2.2
      have : h.choose.2 ≤ min z.2 0 := le_min hz hzero
      linarith only [hw, this]
    · exact min_le_right _ _
  · rw [originASlotShiftedCentre_of_empty h]
    refine ⟨?_, ?_, le_rfl⟩
    · have : vec3EuclideanNorm ((0 : Vec3) - 0) = 0 := by
        simp only [sub_zero]
        exact vec3EuclideanNorm_zero
      rw [mem_vec3Ball, this]
      exact hR
    · have : 0 < R ^ 2 := by positivity
      linarith only [this]

/-- The clipped cell sits inside the cell of twice the radius about the shifted
centre. -/
theorem originASlotShiftedCentre_subset {R r : ℝ} (hr : 0 < r) (z : ParabolicPoint) :
    parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R ⊆
      parabolicCylinder (originASlotShiftedCentre R z r).1
        (originASlotShiftedCentre R z r).2 (2 * r) := by
  by_cases h : (parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R).Nonempty
  · intro y hy
    obtain ⟨hcell, _hcar⟩ := h.choose_spec
    rw [originASlotShiftedCentre_of_nonempty h]
    have hspace : vec3EuclideanNorm (y.1 - h.choose.1) < 2 * r := by
      have h₁ : vec3EuclideanNorm (y.1 - z.1) < r := hy.1.1
      have h₂ : vec3EuclideanNorm (h.choose.1 - z.1) < r := hcell.1
      have h₃ : vec3EuclideanNorm (z.1 - h.choose.1) = vec3EuclideanNorm (h.choose.1 - z.1) := by
        rw [← vec3EuclideanNorm_neg (z.1 - h.choose.1), neg_sub]
      have h₄ : vec3EuclideanNorm (y.1 - h.choose.1) ≤
          vec3EuclideanNorm (y.1 - z.1) + vec3EuclideanNorm (z.1 - h.choose.1) :=
        vec3EuclideanNorm_sub_le_add_sub y.1 z.1 h.choose.1
      rw [h₃] at h₄
      linarith only [h₁, h₂, h₄]
    refine ⟨hspace, ?_, ?_⟩
    · have h₁ : z.2 - r ^ 2 < y.2 := hy.1.2.1
      have h₂ : min z.2 0 ≤ z.2 := min_le_left _ _
      have h₃ : 0 < r ^ 2 := by positivity
      have h₄ : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
      rw [h₄]
      linarith only [h₁, h₂, h₃]
    · exact le_min hy.1.2.2 hy.2.2.2
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h]
    exact Set.empty_subset _

/-! ### The absolute index box of the lattice cover -/

/-- The lattice indices that a cell of radius `(1 - R)/16` can carry while
meeting the origin carrier of radius `R < 3/4`. -/
def originASlotCoverBox : Finset ((Fin 3 → ℤ) × ℤ) :=
  (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-98 : ℤ) 98)) ×ˢ
    (Finset.Icc (-4608 : ℤ) 2)

/-- The index box has `197³ · 4611` members. -/
theorem originASlotCoverBox_card : originASlotCoverBox.card = 35252814903 := by
  have hp := Finset.card_product
    (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-98 : ℤ) 98))
    (Finset.Icc (-4608 : ℤ) 2)
  have hpi := Fintype.card_piFinset (fun _ : Fin 3 => Finset.Icc (-98 : ℤ) 98)
  rw [hpi] at hp
  have hc₁ : (Finset.Icc (-98 : ℤ) 98).card = 197 := by
    rw [Int.card_Icc]
    rfl
  have hc₂ : (Finset.Icc (-4608 : ℤ) 2).card = 4611 := by
    rw [Int.card_Icc]
    rfl
  simp only [hc₁, hc₂, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  rw [originASlotCoverBox, hp]
  norm_num

/-- A lattice cell of radius `(1 - R)/16` that meets the carrier of radius `R`
has its index in the absolute box. -/
theorem originASlotCoverBox_mem {R a : ℝ} (hR : 0 < R) (hRlt : R < 3 / 4)
    (ha : a = (1 - R) / 16) {k : (Fin 3 → ℤ) × ℤ} {w : ParabolicPoint}
    (hcell : w ∈ parabolicCylinder (originLatticeCentre a k).1
      (originLatticeCentre a k).2 a)
    (hcarrier : w ∈ parabolicCylinder (0 : Vec3) 0 R) :
    k ∈ originASlotCoverBox := by
  have hapos : 0 < a := by rw [ha]; linarith only [hRlt]
  have hmargin : R ≤ 48 * a := by rw [ha]; linarith only [hRlt]
  have hspace : ∀ i : Fin 3, |w.1 i - a / 2 * (k.1 i : ℝ)| < a := by
    intro i
    have h := (abs_apply_le_vec3EuclideanNorm
      (w.1 - (originLatticeCentre a k).1) i).trans_lt hcell.1
    simpa only [originLatticeCentre, Pi.sub_apply] using h
  have hcar : ∀ i : Fin 3, |w.1 i| < R := by
    intro i
    have h := (abs_apply_le_vec3EuclideanNorm (w.1 - (0 : Vec3)) i).trans_lt hcarrier.1
    simpa only [sub_zero] using h
  have hindex : ∀ i : Fin 3, k.1 i ∈ Finset.Icc (-98 : ℤ) 98 := by
    intro i
    obtain ⟨h₁, h₂⟩ := abs_lt.mp (hspace i)
    obtain ⟨h₃, h₄⟩ := abs_lt.mp (hcar i)
    have hb : |a / 2 * (k.1 i : ℝ)| < R + a :=
      abs_lt.mpr ⟨by linarith only [h₂, h₃], by linarith only [h₁, h₄]⟩
    have hsplit : |a / 2 * (k.1 i : ℝ)| = a / 2 * |(k.1 i : ℝ)| := by
      rw [abs_mul, abs_of_pos (by linarith only [hapos] : (0 : ℝ) < a / 2)]
    rw [hsplit] at hb
    have hmul : a / 2 * |(k.1 i : ℝ)| < a / 2 * 98 := by
      have : R + a ≤ a / 2 * 98 := by linarith only [hmargin]
      linarith only [hb, this]
    have hlt : |(k.1 i : ℝ)| < 98 :=
      lt_of_mul_lt_mul_left hmul (by linarith only [hapos])
    obtain ⟨h₅, h₆⟩ := abs_lt.mp hlt
    have h₇ : (-98 : ℤ) < k.1 i := by exact_mod_cast h₅
    have h₈ : k.1 i < (98 : ℤ) := by exact_mod_cast h₆
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have htime : k.2 ∈ Finset.Icc (-4608 : ℤ) 2 := by
    have hupper : w.2 ≤ a ^ 2 / 2 * (k.2 : ℝ) := hcell.2.2
    have hlower : a ^ 2 / 2 * (k.2 : ℝ) - a ^ 2 < w.2 := hcell.2.1
    have hcarlow : (0 : ℝ) - R ^ 2 < w.2 := hcarrier.2.1
    have hcarhigh : w.2 ≤ 0 := hcarrier.2.2
    have hasq : 0 < a ^ 2 / 2 := by positivity
    have hRsq : R ^ 2 ≤ 2304 * a ^ 2 := by
      have h : R ≤ 48 * a := hmargin
      nlinarith only [h, hR, hapos]
    have hbig : a ^ 2 / 2 * (-4608 : ℝ) < a ^ 2 / 2 * (k.2 : ℝ) := by
      have : a ^ 2 / 2 * (-4608 : ℝ) = -(2304 * a ^ 2) := by ring
      rw [this]
      linarith only [hupper, hcarlow, hRsq]
    have hsmallidx : a ^ 2 / 2 * (k.2 : ℝ) < a ^ 2 / 2 * 2 := by
      have : a ^ 2 / 2 * (2 : ℝ) = a ^ 2 := by ring
      rw [this]
      linarith only [hlower, hcarhigh]
    have h₁ : (-4608 : ℝ) < (k.2 : ℝ) := lt_of_mul_lt_mul_left hbig hasq.le
    have h₂ : (k.2 : ℝ) < 2 := lt_of_mul_lt_mul_left hsmallidx hasq.le
    have h₃ : (-4608 : ℤ) < k.2 := by exact_mod_cast h₁
    have h₄ : k.2 < (2 : ℤ) := by exact_mod_cast h₂
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  simp only [originASlotCoverBox, Finset.mem_product, Fintype.mem_piFinset]
  exact ⟨hindex, htime⟩

-- The index box is used only through its cardinality and its membership
-- criterion, never through its normal form.
attribute [irreducible] originASlotCoverBox

/-- The origin carrier is covered by the doubled margin cells attached to the
lattice indices of the absolute box.  Every centre used lies in the carrier and
every radius used is `(1 - R)/8`. -/
theorem originASlot_carrier_subset_shifted_cells {R a : ℝ} (hR : 0 < R) (hRlt : R < 3 / 4)
    (ha : a = (1 - R) / 16) :
    parabolicCylinder (0 : Vec3) 0 R ⊆
      ⋃ k ∈ originASlotCoverBox,
        parabolicCylinder
          (originASlotShiftedCentre R (originLatticeCentre a k) a).1
          (originASlotShiftedCentre R (originLatticeCentre a k) a).2 (2 * a) := by
  have hapos : 0 < a := by rw [ha]; linarith only [hRlt]
  intro w hw
  obtain ⟨k, hk⟩ := originLattice_covers a hapos w
  have hmem : k ∈ originASlotCoverBox := originASlotCoverBox_mem hR hRlt ha hk hw
  refine Set.mem_iUnion₂.mpr ⟨k, Finset.mem_coe.mpr hmem, ?_⟩
  exact originASlotShiftedCentre_subset hapos (originLatticeCentre a k) ⟨hk, hw⟩

/-! ### Two scale inequalities for the growth exponent -/

/-- Doubling the radius costs at most the factor `8`, because the growth
exponent of `prop:bootstrap` is at most `71/25`. -/
theorem originASlot_ofReal_two_mul_rpow_le {q τ r : ℝ} (hq : 5 / 2 < q)
    (hτ : 25 / 3 ≤ τ) (hτhi : τ ≤ 25) (hr : 0 < r) :
    ENNReal.ofReal ((2 * r) ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) ≤
      8 * ENNReal.ofReal (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
  have hτpos : 0 < τ := by linarith only [hτ]
  have hqpos : 0 < q := by linarith only [hq]
  have hθpos : 0 < 5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) :=
    growth_exponent_pos hq hτ
  have hθle : 5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q) ≤ 71 / 25 :=
    growth_exponent_upper hτpos hτhi hqpos
  have hsplit : (2 * r) ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) =
      2 ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) *
        r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) :=
    Real.mul_rpow (by norm_num) hr.le
  have htwo : (2 : ℝ) ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) ≤ 8 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (le_trans hθle (by norm_num : (71 : ℝ) / 25 ≤ 3))
    have h3 : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num
    rw [h3] at h
    exact h
  have hrpos : (0 : ℝ) ≤ r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) :=
    Real.rpow_nonneg hr.le _
  rw [hsplit, ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  refine mul_le_mul' ?_ le_rfl
  have h8 : ENNReal.ofReal (8 : ℝ) = 8 := by simp
  rw [← h8]
  exact ENNReal.ofReal_le_ofReal htwo

/-- The growth factor is monotone in the radius. -/
theorem originASlot_ofReal_rpow_mono {q τ a r : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ)
    (ha : 0 ≤ a) (har : a ≤ r) :
    ENNReal.ofReal (a ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) ≤
      ENNReal.ofReal (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) :=
  ENNReal.ofReal_le_ofReal (rpow_growth_exponent_mono hq hτ ha har)

/-! ### The Calderón–Zygmund threshold absorbs an absolute factor -/

/-- The affine slot is superhomogeneous in `|C| + 1`: an absolute factor `n ≥ 1`
is absorbed by enlarging the Calderón–Zygmund constant by the factor `n`. -/
theorem originKPAffineASlot_const_mul_le {q ε : ℝ} {KU KD n : ℝ≥0∞} {C₀ C : ℝ}
    (hn : 1 ≤ n)
    (h : n * ENNReal.ofReal (|C₀| + 1) ≤ ENNReal.ofReal (|C| + 1)) :
    n * originKPAffineASlot q C₀ ε KU KD ≤ originKPAffineASlot q C ε KU KD := by
  set X : ℝ≥0∞ := 3 * (3 * KU * KD + forceSourceMorreyBound q ε) with hX
  have hpow : n * (ENNReal.ofReal (|C₀| + 1) * X) ^ (6 / 5 : ℝ) ≤
      (ENNReal.ofReal (|C| + 1) * X) ^ (6 / 5 : ℝ) := by
    have hn' : n ≤ n ^ (6 / 5 : ℝ) := by
      calc n = n ^ (1 : ℝ) := (ENNReal.rpow_one n).symm
        _ ≤ n ^ (6 / 5 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hn (by norm_num)
    calc n * (ENNReal.ofReal (|C₀| + 1) * X) ^ (6 / 5 : ℝ)
        ≤ n ^ (6 / 5 : ℝ) * (ENNReal.ofReal (|C₀| + 1) * X) ^ (6 / 5 : ℝ) :=
          mul_le_mul' hn' le_rfl
      _ = (n * (ENNReal.ofReal (|C₀| + 1) * X)) ^ (6 / 5 : ℝ) :=
          (ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)).symm
      _ = ((n * ENNReal.ofReal (|C₀| + 1)) * X) ^ (6 / 5 : ℝ) := by rw [mul_assoc]
      _ ≤ (ENNReal.ofReal (|C| + 1) * X) ^ (6 / 5 : ℝ) :=
          ENNReal.rpow_le_rpow (mul_le_mul' h le_rfl) (by norm_num)
  have hlin : n * (ENNReal.ofReal (|C₀| + 1) * X) ≤ ENNReal.ofReal (|C| + 1) * X := by
    rw [← mul_assoc]
    exact mul_le_mul' h le_rfl
  have hmass : n * (ENNReal.ofReal (|C₀| + 1) * (128 * ENNReal.ofReal ε ^ (4 / 5 : ℝ))) ≤
      ENNReal.ofReal (|C| + 1) * (128 * ENNReal.ofReal ε ^ (4 / 5 : ℝ)) := by
    rw [← mul_assoc]
    exact mul_le_mul' h le_rfl
  unfold originKPAffineASlot
  rw [← hX, mul_add, mul_add]
  exact add_le_add (add_le_add hlin hpow) hmass

end CKN.Core.Step4
