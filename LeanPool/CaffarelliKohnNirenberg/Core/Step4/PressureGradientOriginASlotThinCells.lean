/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotThinCellsGeometry
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTimeIntegrals

/-! # From the common half-collar scale to every clipped cell

Bounds at closed carrier centres for radii at most `1/256` imply the
unrestricted clipped-cell bound. The explicit cover count is absorbed once
into the affine pressure coefficient.
-/

@[expose] public section

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
