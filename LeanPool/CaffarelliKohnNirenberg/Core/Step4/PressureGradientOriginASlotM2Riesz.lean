/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotSourceCorrectionSupport
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTCentredSourceCorrection
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszSourceQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszSelection
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGaugeMajorantExponents

/-! # From a Morrey majorant to the A-slot estimate for the correction

The actual Riesz fields of the centred source correction, not merely a
measurable selection of them, satisfy the clipped-cell affine estimate as
soon as the carrier-restricted sources carry a common Morrey majorant.  The
carrier restriction is invisible on the collar time window because the
correction vanishes off the source ball.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Foundation.Euclidean
open CKN.Foundation.Heat CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- Outside the source ball the centred correction vanishes. -/
theorem originASlot_correction_zero_outside
    {R₀ : ℝ} {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    (hη : ∀ x, x ∉ vec3Ball (0 : Vec3) R₀ → η x = 0)
    (hdη : ∀ k x, x ∉ vec3Ball (0 : Vec3) R₀ → dη k x = 0)
    (u f : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (c : Vec3) (j : Fin 3)
    {x : Vec3} (hx : x ∉ vec3Ball (0 : Vec3) R₀) :
    centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) η dη u f Du c j x = 0 := by
  unfold centredRawSourceCorrection
  rw [hη x hx, Set.indicator_of_notMem hx]
  simp only [hdη _ x hx, zero_mul, Finset.sum_const_zero, sub_zero, zero_add]

/-- On the collar time window the carrier restriction does not change the
centred correction slices. -/
theorem originASlot_correction_slice_eq
    {R₀ ρ : ℝ} {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    (hη : ∀ x, x ∉ vec3Ball (0 : Vec3) R₀ → η x = 0)
    (hdη : ∀ k x, x ∉ vec3Ball (0 : Vec3) R₀ → dη k x = 0)
    {c : ℝ → Vec3}
    (u' : ParabolicPoint → Vec3) (f' : ParabolicPoint → Vec3)
    (Du' : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) (j : Fin 3) {s : ℝ}
    (hs : s ∈ Ioc (z.2 - ρ ^ 2) z.2) :
    (fun x => (vec3Ball (0 : Vec3) R₀ ×ˢ Ioc (z.2 - ρ ^ 2) z.2).indicator
      (fun w : ParabolicPoint => centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) η dη
        (fun y => u' (y, w.2)) (fun y => f' (y, w.2)) (fun y => Du' (y, w.2)) (c w.2) j w.1)
      (x, s)) =
      fun x => centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) η dη
        (fun y => u' (y, s)) (fun y => f' (y, s)) (fun y => Du' (y, s)) (c s) j x := by
  funext x
  by_cases hx : x ∈ vec3Ball (0 : Vec3) R₀
  · exact Set.indicator_of_mem (show ((x, s) : ParabolicPoint) ∈
      vec3Ball (0 : Vec3) R₀ ×ˢ Ioc (z.2 - ρ ^ 2) z.2 from ⟨hx, hs⟩) _
  · refine (Set.indicator_of_notMem (show ((x, s) : ParabolicPoint) ∉
      vec3Ball (0 : Vec3) R₀ ×ˢ Ioc (z.2 - ρ ^ 2) z.2 from fun hc => hx hc.1) _).trans ?_
    exact (originASlot_correction_zero_outside hη hdη (fun y => u' (y, s)) (fun y => f' (y, s))
      (fun y => Du' (y, s)) (c s) j hx).symm

/-- The actual Riesz fields of three sources with a common Morrey majorant
satisfy the affine clipped-cell estimate above the matching threshold. -/
theorem originASlot_literal_riesz_sum_clipped_le_slot
    (q τ C_CZ ε : ℝ) (KU KD Cbig : ℝ≥0∞)
    (hq : 5/2 < q) (hτ : 25/3 ≤ τ) (hτhi : τ ≤ 25)
    (hcoef : pressureRieszMorreyConstant (25/9) * Cbig ≤ ENNReal.ofReal (|C_CZ| + 1))
    (i : Fin 3) {F : Fin 3 → ParabolicPoint → ℝ}
    (hF : ∀ j, AEMeasurable (F j) volume)
    (hFs : ∀ j, ∀ᵐ s ∂volume, MemLp (fun y => F j (y, s))
      (ENNReal.ofReal (6/5 : ℝ)) volume)
    {K : Set Vec3} (hK : IsCompact K)
    (hsupport : ∀ j y s, y ∉ K → F j (y, s) = 0)
    (hN : ∀ j, morreyNorm (6/5 : ℝ) (min ((1/τ+8/25)⁻¹) q) (F j) ≤
      Cbig * (3*KU*KD + forceSourceMorreyBound q ε))
    (B : Set Vec3) (J : Set ℝ) (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ J,
      eLpNorm (fun y => ∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i) (fun x => F j (x, s)) y)
        (ENNReal.ofReal (6/5 : ℝ)) (volume.restrict (vec3Ball z.1 r ∩ B)) ^ (6/5 : ℝ)) ≤
      originKPAffineASlot q C_CZ ε KU KD *
        ENNReal.ofReal (r ^ (5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q))) := by
  classical
  set κ : ℝ := min ((1/τ+8/25)⁻¹) q with hκdef
  set X : ℝ≥0∞ := 3*KU*KD + forceSourceMorreyBound q ε with hXdef
  have hκ : 0 < κ := lt_of_lt_of_le (by norm_num) (endgame_kappa_ge hτ hq)
  have hκhi : κ ≤ 25/9 := endgame_kappa_le (by linarith only [hτ]) hτhi
  have ht : ∀ j : Fin 3, ∃ T : ParabolicPoint → ℝ, Measurable T ∧
      ∀ᵐ s ∂volume, (fun y => T (y, s)) =ᵐ[volume]
        rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
          (rieszSecondL2_weak_type j i) (fun y => F j (y, s)) :=
    fun j => exists_measurable_riesz_extension_field_of_aemeasurable j i (hF j) hK
      (fun y s hy => hsupport j y s hy) (hFs j)
  choose T hTm hTi using ht
  obtain ⟨L, hL⟩ := hK.isBounded.exists_norm_le
  have hsupL : ∀ j, ∀ (y : Vec3) (s : ℝ), L < ‖y‖ → F j (y, s) = 0 :=
    fun j y s hy => hsupport j y s (fun hKy => (not_le.mpr hy) (hL y hKy))
  have hn : ∀ j : Fin 3, morreyNorm (6/5 : ℝ) κ (T j) ≤
      pressureRieszMorreyConstant κ * (Cbig * X) := fun j =>
    (pressure_riesz_morreyNorm_bound j i hκ hκhi (hF j) (hFs j) (hsupL j)
      (hTm j).aemeasurable (hTi j)).trans (mul_le_mul' le_rfl (hN j))
  have hsum : morreyNorm (6/5 : ℝ) κ (fun w => ∑ j, T j w) ≤
      3 * (pressureRieszMorreyConstant κ * (Cbig * X)) := by
    have h12 := (morrey_norm_add_le (by norm_num : (1 : ℝ) ≤ 6/5)
      (hTm 1).aemeasurable (hTm 2).aemeasurable).trans (add_le_add (hn 1) (hn 2))
    have h012 := (morrey_norm_add_le (by norm_num : (1 : ℝ) ≤ 6/5)
      (hTm 0).aemeasurable ((hTm 1).aemeasurable.add (hTm 2).aemeasurable)).trans
      (add_le_add (hn 0) h12)
    simpa [Fin.sum_univ_succ,
      show (3 : ℝ≥0∞) * (pressureRieszMorreyConstant κ * (Cbig * X)) =
        pressureRieszMorreyConstant κ * (Cbig * X) +
          (pressureRieszMorreyConstant κ * (Cbig * X) +
            pressureRieszMorreyConstant κ * (Cbig * X)) by ring] using h012
  have hle : 3 * (pressureRieszMorreyConstant κ * (Cbig * X)) ≤
      ENNReal.ofReal (|C_CZ| + 1) * (3 * X) := by
    have hstep : pressureRieszMorreyConstant κ * Cbig ≤ ENNReal.ofReal (|C_CZ| + 1) :=
      (mul_le_mul' (pressureRieszMorreyConstant_le_endpoint hκ hκhi) le_rfl).trans hcoef
    calc
      3 * (pressureRieszMorreyConstant κ * (Cbig * X))
          = (pressureRieszMorreyConstant κ * Cbig) * (3 * X) := by ring
      _ ≤ ENNReal.ofReal (|C_CZ| + 1) * (3 * X) := mul_le_mul' hstep le_rfl
  have hm : AEMeasurable (fun w => ∑ j, T j w) volume :=
    Finset.aemeasurable_fun_sum _ (fun j _ => (hTm j).aemeasurable)
  have hbound := (glued_clipped_slice_time_bound (κ := κ) hm B J z hr).2
  have hA := rpow_le_originKPAffineASlot_of_le q C_CZ ε KU KD _ (hsum.trans hle)
  have hmain : (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ J,
      eLpNorm (fun y => ∑ j, T j (y, s)) (ENNReal.ofReal (6/5 : ℝ))
        (volume.restrict (vec3Ball z.1 r ∩ B)) ^ (6/5 : ℝ)) ≤
      originKPAffineASlot q C_CZ ε KU KD *
        ENNReal.ofReal (r ^ (5*(1-(6/5 : ℝ)/κ))) := by
    apply hbound.trans
    rw [mul_comm, ← ENNReal.ofReal_rpow_of_pos hr]
    exact mul_le_mul' hA le_rfl
  refine le_trans (le_of_eq ?_) hmain
  refine lintegral_congr_ae ?_
  have hall : ∀ᵐ s ∂volume, ∀ j : Fin 3, (fun y => T j (y, s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i) (fun y => F j (y, s)) := by
    rw [ae_all_iff]
    exact hTi
  filter_upwards [ae_restrict_of_ae hall] with s hs
  have hsumeq : (fun y => ∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) (fun x => F j (x, s)) y) =ᵐ[volume]
      (fun y => ∑ j, T j (y, s)) := by
    filter_upwards [hs 0, hs 1, hs 2] with y h0 h1 h2
    simp only [Fin.sum_univ_three, h0, h1, h2]
  congr 1
  exact eLpNorm_congr_ae (ae_restrict_of_ae hsumeq)

/-- Given the Morrey majorant for the carrier-restricted correction sources,
the clipped-cell time mass of the actual correction Riesz fields satisfies the
affine A-slot estimate. -/
theorem originASlot_correction_mass_of_morrey_bound
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD Cbig : ℝ≥0∞)
    (hq : 5/2 < q) (hτ : 25/3 ≤ τ) (hτhi : τ ≤ 25)
    (hcoef : pressureRieszMorreyConstant (25/9) * Cbig ≤ ENNReal.ofReal (|C_CZ| + 1))
    (hR₁ : 0 < R₁) (hgap : R₁ < R₀)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {f : ParabolicPoint → Vec3}
    (z : ParabolicPoint) (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁))
    (i : Fin 3) (r : ℝ) (hr : 0 < r) (hcell : r ≤ (R₀-R₁)/4)
    (hρ : 0 < (R₀-R₁)/2)
    (G : Fin 3 → ParabolicPoint → ℝ)
    (hG : ∀ j : Fin 3, G j =
      (vec3Ball (0 : Vec3) R₀ ×ˢ Ioc (z.2 - ((R₀-R₁)/2) ^ 2) z.2).indicator
        (fun w : ParabolicPoint => centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀)
          (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
          (fun y => u (y, w.2)) (fun y => f (y, w.2)) (fun y => Du (y, w.2))
          (sourceSliceCentredMean z.1 ((R₀-R₁)/2) u w.2) j w.1))
    (hF : ∀ j : Fin 3, AEMeasurable (G j) volume)
    (hFs : ∀ j : Fin 3, ∀ᵐ s ∂volume, MemLp (fun y => G j (y, s))
      (ENNReal.ofReal (6/5 : ℝ)) volume)
    (hN : ∀ j : Fin 3, morreyNorm (6/5 : ℝ) (min ((1/τ+8/25)⁻¹) q) (G j) ≤
      Cbig * (3*KU*KD + forceSourceMorreyBound q ε)) :
    (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
      eLpNorm (fun x => ∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i)
        (centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) (mollifiedBallCutoff z.1 hρ)
          (spatialDeriv (mollifiedBallCutoff z.1 hρ))
          (fun y => u (y, s)) (fun y => f (y, s)) (fun y => Du (y, s))
          (sourceSliceCentredMean z.1 ((R₀-R₁)/2) u s) j) x) (ENNReal.ofReal (6/5 : ℝ))
        (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6/5 : ℝ)) ≤
      originKPAffineASlot q C_CZ ε KU KD *
        ENNReal.ofReal (r ^ (5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q))) := by
  classical
  have hgapη : R₁ + 3 * ((R₀-R₁)/2) / 4 ≤ R₀ := by linarith only [hgap]
  have hη0 : ∀ x, x ∉ vec3Ball (0 : Vec3) R₀ → mollifiedBallCutoff z.1 hρ x = 0 :=
    mollifiedBallCutoff_eq_zero_outside_source_ball hρ hR₁ hz hgapη
  have hdη0 : ∀ (k : Fin 3), ∀ x, x ∉ vec3Ball (0 : Vec3) R₀ →
      spatialDeriv (mollifiedBallCutoff z.1 hρ) k x = 0 :=
    spatialDeriv_mollifiedBallCutoff_eq_zero_outside_source_ball hρ hR₁ hz hgapη
  have hR₀pos : 0 < R₀ := hR₁.trans hgap
  have hK : IsCompact (closure (vec3Ball (0 : Vec3) R₀)) :=
    isCompact_closure_vec3Ball hR₀pos
  have hsupp : ∀ (j : Fin 3) (y : Vec3) (s : ℝ),
      y ∉ closure (vec3Ball (0 : Vec3) R₀) → G j (y, s) = 0 := by
    intro j y s hy
    rw [hG j]
    exact Set.indicator_of_notMem (fun hc => hy (subset_closure hc.1)) _
  have hmain := originASlot_literal_riesz_sum_clipped_le_slot q τ C_CZ ε KU KD Cbig hq hτ hτhi hcoef
    i hF hFs hK hsupp hN (vec3Ball (0 : Vec3) R₁) (Ioc (-(R₁ ^ 2)) 0) z hr
  refine le_trans (le_of_eq ?_) hmain
  refine setLIntegral_congr_fun (measurableSet_Ioc.inter measurableSet_Ioc) ?_
  intro s hs
  beta_reduce
  have hsρ : s ∈ Ioc (z.2 - ((R₀-R₁)/2) ^ 2) z.2 := by
    refine ⟨?_, hs.1.2⟩
    have hrρ : r ≤ (R₀-R₁)/2 := by linarith only [hcell, hgap]
    have hsq : r ^ 2 ≤ ((R₀-R₁)/2) ^ 2 := by nlinarith only [hr, hrρ]
    linarith only [hs.1.1, hsq]
  have heq : ∀ j : Fin 3, (fun x => G j (x, s)) =
      fun x => centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀)
        (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
        (fun y => u (y, s)) (fun y => f (y, s)) (fun y => Du (y, s))
        (sourceSliceCentredMean z.1 ((R₀-R₁)/2) u s) j x := by
    intro j
    rw [hG j]
    exact originASlot_correction_slice_eq hη0 hdη0 u f Du z j hsρ
  have hfun : (fun x => ∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i)
      (centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) (mollifiedBallCutoff z.1 hρ)
        (spatialDeriv (mollifiedBallCutoff z.1 hρ))
        (fun y => u (y, s)) (fun y => f (y, s)) (fun y => Du (y, s))
        (sourceSliceCentredMean z.1 ((R₀-R₁)/2) u s) j) x) =
      (fun y => ∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i) (fun x => G j (x, s)) y) := by
    funext y
    refine Finset.sum_congr rfl fun j _ => ?_
    exact congrArg (fun g => rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) g y) (heq j).symm
  rw [hfun]

end CKN.Core.Step4
