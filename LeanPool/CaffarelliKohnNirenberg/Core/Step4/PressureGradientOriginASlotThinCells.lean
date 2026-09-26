/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotLargeCellsGeometry
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTimeIntegrals

/-! # From the common half-collar scale to every clipped cell

Bounds at closed carrier centres for radii at most `1/256` imply the
unrestricted clipped-cell bound. The explicit cover count is absorbed once
into the affine pressure coefficient.
-/

public section

section

/-! # An absolute lattice cover for thin pressure collars

The doubled cells have radius `1/512`, below both prescribed half-collars.
The existing shifted-centre construction keeps every centre in the carrier.
-/

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
end

end

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- The Calderón–Zygmund threshold at which every clipped cell of the origin
carrier inherits the thin-cell A slot: the number of thin cells used to
cover the carrier, times the constant of the thin-cell estimate. -/
def originASlotThinCellThreshold (Cbase : ℝ) : ℝ :=
  34366557335620983 * (|Cbase| + 1)

/-- The threshold multiplies the affine slot by the cover count. -/
theorem originKPAffineASlot_thin_cover_count_mul_le {q ε Cbase C_CZ : ℝ} {KU KD : ℝ≥0∞}
    (hthreshold : originASlotThinCellThreshold Cbase ≤ C_CZ) :
    (34366557335620983 : ℝ≥0∞) * originKPAffineASlot q Cbase ε KU KD ≤
      originKPAffineASlot q C_CZ ε KU KD := by
  refine originKPAffineASlot_const_mul_le (by norm_num) ?_
  have hcast : (34366557335620983 : ℝ≥0∞) = ENNReal.ofReal (34366557335620983 : ℝ) := by
    rw [ENNReal.ofReal]
    norm_num
  rw [hcast, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have habs : C_CZ ≤ |C_CZ| := le_abs_self C_CZ
  have hth : 34366557335620983 * (|Cbase| + 1) ≤ C_CZ := hthreshold
  linarith only [habs, hth]

/-- Thin cells control every cell.  Given the clipped A-slot estimate of
`prop:bootstrap` on thin cells at the constant `Cbase`, every clipped cell —
any centre, any positive radius — obeys the same estimate at any constant above
`originASlotThinCellThreshold Cbase`. -/
theorem originASlot_clipped_cell_of_thin_cells
    {q τ R₁ ε Cbase C_CZ : ℝ} {KU KD : ℝ≥0∞}
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hτhi : τ ≤ 25)
    (hR₁ : 0 < R₁) (hR₁lt : R₁ < 3 / 4)
    (hthreshold : originASlotThinCellThreshold Cbase ≤ C_CZ)
    {Dp : ParabolicPoint → Vec3} (hDp : Measurable Dp) (i : Fin 3)
    (hmargin : ∀ w ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 / 256 →
      (∫⁻ s in Ioc (w.2 - ρ ^ 2) w.2 ∩ Ioc (-(R₁ ^ 2)) 0,
        eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball w.1 ρ ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
        originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
          (ρ ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))))
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
      eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
      originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
        (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
  have hS : MeasurableSet (parabolicCylinder (0 : Vec3) 0 R₁) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioc
  have hmeas : Measurable (fun w : ParabolicPoint => Dp w i) :=
    (measurable_pi_apply i).comp hDp
  have key : ∀ (x : Vec3) (t ρ : ℝ),
      (∫⁻ s in Ioc (t - ρ ^ 2) t ∩ Ioc (-(R₁ ^ 2)) 0,
        eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball x ρ ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) =
      ∫⁻ w in parabolicCylinder x t ρ ∩ parabolicCylinder (0 : Vec3) 0 R₁,
        ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ) := by
    intro x t ρ
    rw [origin_clipped_slice_norm_power_eq (P := (6 / 5 : ℝ)) (by norm_num) R₁
      hmeas.aemeasurable x t ρ]
    exact cylinderPowerIntegral_indicator (by norm_num) hS (fun w => Dp w i) (x, t) ρ
  have hslot : (34366557335620983 : ℝ≥0∞) * originKPAffineASlot q Cbase ε KU KD ≤
      originKPAffineASlot q C_CZ ε KU KD :=
    originKPAffineASlot_thin_cover_count_mul_le hthreshold
  rw [key z.1 z.2 r]
  rcases le_or_gt r (1 / 512) with hsplit | hsplit
  · -- A small cell is doubled onto a margin cell centred in the carrier.
    have hshift := originASlotShiftedCentre_mem hR₁ z r
    have hsub : parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R₁ ⊆
        parabolicCylinder (originASlotShiftedCentre R₁ z r).1
          (originASlotShiftedCentre R₁ z r).2 (2 * r) ∩
          parabolicCylinder (0 : Vec3) 0 R₁ :=
      Set.subset_inter (originASlotShiftedCentre_subset hr z) inter_subset_right
    calc
      (∫⁻ w in parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R₁,
          ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ))
          ≤ ∫⁻ w in parabolicCylinder (originASlotShiftedCentre R₁ z r).1
              (originASlotShiftedCentre R₁ z r).2 (2 * r) ∩
              parabolicCylinder (0 : Vec3) 0 R₁,
              ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ) := lintegral_mono_set hsub
      _ ≤ originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
            ((2 * r) ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
          rw [← key (originASlotShiftedCentre R₁ z r).1
            (originASlotShiftedCentre R₁ z r).2 (2 * r)]
          exact hmargin (originASlotShiftedCentre R₁ z r) (subset_closure hshift) (2 * r)
            (by linarith only [hr]) (by linarith only [hsplit])
      _ ≤ originKPAffineASlot q Cbase ε KU KD *
            (8 * ENNReal.ofReal
              (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) :=
          mul_le_mul' le_rfl (originASlot_ofReal_two_mul_rpow_le hq hτ hτhi hr)
      _ = (8 : ℝ≥0∞) * originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
          ring
      _ ≤ (34366557335620983 : ℝ≥0∞) * originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) :=
          mul_le_mul' (mul_le_mul' (by norm_num) le_rfl) le_rfl
      _ ≤ originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) :=
          mul_le_mul' hslot le_rfl
  · -- A large cell is bounded by the whole clipped carrier mass.
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / 1024 := ⟨_, rfl⟩
    have hapos : 0 < a := by rw [ha]; norm_num
    have hmarginfit : 2 * a ≤ 1 / 256 := by rw [ha]; norm_num
    have hcellsmall : 2 * a ≤ r := by rw [ha]; linarith only [hsplit]
    set V : {k : (Fin 3 → ℤ) × ℤ // k ∈ originASlotThinCoverBox} → Set ParabolicPoint :=
      fun k => parabolicCylinder
        (originASlotShiftedCentre R₁ (originLatticeCentre a k.1) a).1
        (originASlotShiftedCentre R₁ (originLatticeCentre a k.1) a).2 (2 * a) ∩
        parabolicCylinder (0 : Vec3) 0 R₁ with hV
    have hcover : parabolicCylinder (0 : Vec3) 0 R₁ ⊆ ⋃ k, V k := by
      intro w hw
      obtain ⟨k, hk, hwk⟩ :=
        Set.mem_iUnion₂.mp (originASlot_carrier_subset_thin_cells hR₁ hR₁lt ha hw)
      exact Set.mem_iUnion.mpr ⟨⟨k, Finset.mem_coe.mp hk⟩, hwk, hw⟩
    have hterm : ∀ k : {k : (Fin 3 → ℤ) × ℤ // k ∈ originASlotThinCoverBox},
        (∫⁻ w in V k, ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
          originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
      intro k
      have hcentre := originASlotShiftedCentre_mem hR₁ (originLatticeCentre a k.1) a
      calc
        (∫⁻ w in V k, ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ))
            ≤ originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
                ((2 * a) ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
              rw [hV, ← key
                (originASlotShiftedCentre R₁ (originLatticeCentre a k.1) a).1
                (originASlotShiftedCentre R₁ (originLatticeCentre a k.1) a).2 (2 * a)]
              exact hmargin _ (subset_closure hcentre) (2 * a)
                (by linarith only [hapos]) hmarginfit
        _ ≤ originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
              (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) :=
            mul_le_mul' le_rfl (originASlot_ofReal_rpow_mono hq hτ
              (by linarith only [hapos]) hcellsmall)
    calc
      (∫⁻ w in parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R₁,
          ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ))
          ≤ ∫⁻ w in parabolicCylinder (0 : Vec3) 0 R₁,
              ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ) :=
            lintegral_mono_set inter_subset_right
      _ ≤ ∫⁻ w in ⋃ k, V k, ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ) :=
            lintegral_mono_set hcover
      _ ≤ ∑' k, ∫⁻ w in V k, ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ) :=
            lintegral_iUnion_le _ _
      _ = ∑ k : {k : (Fin 3 → ℤ) × ℤ // k ∈ originASlotThinCoverBox},
              ∫⁻ w in V k, ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ) := tsum_fintype _
      _ ≤ (Finset.univ : Finset {k : (Fin 3 → ℤ) × ℤ // k ∈ originASlotThinCoverBox}).card •
            (originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
              (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) :=
            Finset.sum_le_card_nsmul _ _ _ (fun k _ => hterm k)
      _ = (34366557335620983 : ℝ≥0∞) * (originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
              (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) := by
            rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_coe, originASlotThinCoverBox_card]
            norm_num
      _ = (34366557335620983 : ℝ≥0∞) * originKPAffineASlot q Cbase ε KU KD * ENNReal.ofReal
              (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
            rw [mul_assoc]
      _ ≤ originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
              (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) :=
            mul_le_mul' hslot le_rfl


end CKN.Core.Step4
