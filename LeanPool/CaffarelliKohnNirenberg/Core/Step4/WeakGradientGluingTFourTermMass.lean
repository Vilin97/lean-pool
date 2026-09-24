/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotLargeCells

/-! # Four-term pressure mass and affine absorption -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN.Core.Step4

/-- A balanced four-term split has a uniform six-fifths power cost. -/
theorem four_term_six_fifths (a b c d : ℝ≥0∞) :
    (a+b+c+d)^(6/5 : ℝ) ≤
      16*(a^(6/5 : ℝ)+b^(6/5 : ℝ)+c^(6/5 : ℝ)+d^(6/5 : ℝ)) := by
  have htwo : (2 : ℝ≥0∞)^(6/5 : ℝ) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ≥0∞)^(2 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  have h (x y : ℝ≥0∞) : (x+y)^(6/5 : ℝ) ≤
      4*(x^(6/5 : ℝ)+y^(6/5 : ℝ)) :=
    (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow x y (by norm_num)).trans
      (mul_le_mul' htwo le_rfl)
  calc
    _ = ((a+b)+(c+d))^(6/5 : ℝ) := by simp only [add_assoc]
    _ ≤ 4*((a+b)^(6/5 : ℝ)+(c+d)^(6/5 : ℝ)) := h _ _
    _ ≤ 4*(4*(a^(6/5 : ℝ)+b^(6/5 : ℝ))+
        4*(c^(6/5 : ℝ)+d^(6/5 : ℝ))) :=
      mul_le_mul' le_rfl (add_le_add (h _ _) (h _ _))
    _ = _ := by ring

/-- The signed four-term identity controls each spatial slice norm. -/
theorem four_term_slice_mass_le {μ : Measure Vec3} {D A B C E : Vec3 → ℝ}
    (hid : D =ᵐ[μ] (fun x => -A x+B x+C x-E x)) :
    eLpNorm D (ENNReal.ofReal (6/5 : ℝ)) μ^(6/5 : ℝ) ≤
      16*(eLpNorm A (ENNReal.ofReal (6/5 : ℝ)) μ^(6/5 : ℝ)+
        eLpNorm B (ENNReal.ofReal (6/5 : ℝ)) μ^(6/5 : ℝ)+
        eLpNorm C (ENNReal.ofReal (6/5 : ℝ)) μ^(6/5 : ℝ)+
        eLpNorm E (ENNReal.ofReal (6/5 : ℝ)) μ^(6/5 : ℝ)) := by
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (6/5 : ℝ) := by norm_num
  rw [eLpNorm_congr_ae hid]
  have h := (eLpNorm_add_le (f := fun x => -A x+B x+C x)
    (g := -E) (μ := μ) hp).trans
    (add_le_add (eLpNorm_add_le (f := fun x => -A x+B x) (g := C) hp) le_rfl)
  have hh := h.trans (add_le_add
    (add_le_add (eLpNorm_add_le (f := -A) (g := B) hp) le_rfl) le_rfl)
  simp only [eLpNorm_neg] at hh
  exact (ENNReal.rpow_le_rpow hh (by norm_num)).trans (four_term_six_fifths _ _ _ _)

/-- The absolute enlargement pays the triangle cost and all four component budgets. -/
def fourTermAffineThreshold (Cbase : ℝ) : ℝ := 64*(|Cbase|+1)

/-- Four component bounds at the base constant fit the enlarged affine slot. -/
theorem four_term_affine_cost_absorbed {q ε Cbase C_CZ : ℝ} {KU KD : ℝ≥0∞}
    (hthreshold : fourTermAffineThreshold Cbase ≤ C_CZ) :
    (64 : ℝ≥0∞)*originKPAffineASlot q Cbase ε KU KD ≤
      originKPAffineASlot q C_CZ ε KU KD := by
  refine originKPAffineASlot_const_mul_le (by norm_num) ?_
  have hc : (64 : ℝ≥0∞) = ENNReal.ofReal (64 : ℝ) := by norm_num
  rw [hc, ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have ha := le_abs_self C_CZ
  unfold fourTermAffineThreshold at hthreshold
  linarith only [ha,hthreshold]

/-- Integration preserves the four-term cost for measurable slice masses. -/
theorem four_term_time_mass_le {ν : Measure ℝ} {D A B C E : ℝ → ℝ≥0∞}
    (hA : AEMeasurable A ν) (hB : AEMeasurable B ν) (hC : AEMeasurable C ν)
    (hbound : ∀ᵐ s ∂ν, D s ≤ 16*(A s+B s+C s+E s)) :
    (∫⁻ s, D s ∂ν) ≤ 16*((∫⁻ s, A s ∂ν)+(∫⁻ s, B s ∂ν)+
      (∫⁻ s, C s ∂ν)+(∫⁻ s, E s ∂ν)) := by
  calc
    _ ≤ ∫⁻ s, 16*(A s+B s+C s+E s) ∂ν := lintegral_mono_ae hbound
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left' (show AEMeasurable (fun s => A s+B s+C s) ν from (hA.add hB).add hC),
        lintegral_add_left' (show AEMeasurable (fun s => A s+B s) ν from hA.add hB), lintegral_add_left' hA]

/-- Four slice-mass budgets combine into one enlarged affine budget. -/
theorem four_term_time_mass_affine {ν : Measure ℝ} {D A B C E : ℝ → ℝ≥0∞}
    {q ε Cbase C_CZ : ℝ} {KU KD L : ℝ≥0∞}
    (hthreshold : fourTermAffineThreshold Cbase ≤ C_CZ)
    (hA : AEMeasurable A ν) (hB : AEMeasurable B ν) (hC : AEMeasurable C ν)
    (hbound : ∀ᵐ s ∂ν, D s ≤ 16*(A s+B s+C s+E s))
    (hAm : (∫⁻ s, A s ∂ν) ≤ originKPAffineASlot q Cbase ε KU KD*L)
    (hBm : (∫⁻ s, B s ∂ν) ≤ originKPAffineASlot q Cbase ε KU KD*L)
    (hCm : (∫⁻ s, C s ∂ν) ≤ originKPAffineASlot q Cbase ε KU KD*L)
    (hEm : (∫⁻ s, E s ∂ν) ≤ originKPAffineASlot q Cbase ε KU KD*L) :
    (∫⁻ s, D s ∂ν) ≤ originKPAffineASlot q C_CZ ε KU KD*L := by
  calc
    _ ≤ 16*((∫⁻ s, A s ∂ν)+(∫⁻ s, B s ∂ν)+
        (∫⁻ s, C s ∂ν)+(∫⁻ s, E s ∂ν)) := four_term_time_mass_le hA hB hC hbound
    _ ≤ 16*(originKPAffineASlot q Cbase ε KU KD*L+
        originKPAffineASlot q Cbase ε KU KD*L+
        originKPAffineASlot q Cbase ε KU KD*L+
        originKPAffineASlot q Cbase ε KU KD*L) :=
      mul_le_mul' le_rfl (add_le_add (add_le_add (add_le_add hAm hBm) hCm) hEm)
    _ = (64*originKPAffineASlot q Cbase ε KU KD)*L := by ring
    _ ≤ _ := mul_le_mul' (four_term_affine_cost_absorbed hthreshold) le_rfl

end CKN.Core.Step4
