/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaStopping
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalWeightedTail

/-! # Stopping Energy Transfer -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

private theorem closedBallL2Energy_nonneg {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] (u : Vec d → F) (x : Vec d) {r : ℝ} (hr : 0 < r) :
    0 ≤ closedBallL2Energy u x r := by
  unfold closedBallL2Energy closedBallAverage
  apply mul_nonneg
  · positivity
  · exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _

private theorem combined_energy_mass_identity {d : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : Vec d → F) (g : Vec d → G) {ε level r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hf : Integrable (fun y => ‖f y‖ ^ (2 : ℕ)) volume)
    (hg : Integrable (fun y => ‖g y‖ ^ (2 : ℕ)) volume)
    (x : Vec d) (hstop : goodLambdaCombinedEnergy f g ε x r = level) :
    ∫ y in Metric.closedBall x r,
        (‖f y‖ ^ (2 : ℕ) + (ε⁻¹) ^ (2 : ℕ) * ‖g y‖ ^ (2 : ℕ)) ∂volume =
      level ^ (2 : ℕ) * (2 * r) ^ d := by
  let D : ℝ := (2 * r) ^ d
  let If : ℝ := ∫ y in Metric.closedBall x r, ‖f y‖ ^ (2 : ℕ) ∂volume
  let Ig : ℝ := ∫ y in Metric.closedBall x r, ‖g y‖ ^ (2 : ℕ) ∂volume
  have hf_nonneg : 0 ≤ closedBallL2Energy f x r :=
    closedBallL2Energy_nonneg f x hr
  have hg_nonneg : 0 ≤ closedBallL2Energy g x r :=
    closedBallL2Energy_nonneg g x hr
  have hsum_nonneg : 0 ≤ closedBallL2Energy f x r +
      (ε⁻¹) ^ (2 : ℕ) * closedBallL2Energy g x r := by
    exact add_nonneg hf_nonneg (mul_nonneg (sq_nonneg _) hg_nonneg)
  have hsum : closedBallL2Energy f x r +
      (ε⁻¹) ^ (2 : ℕ) * closedBallL2Energy g x r = level ^ (2 : ℕ) := by
    have hsquare := congrArg (fun z : ℝ => z ^ (2 : ℕ)) hstop
    simpa only [goodLambdaCombinedEnergy, Real.sq_sqrt hsum_nonneg] using hsquare
  have hD_pos : 0 < D := by
    dsimp [D]
    exact pow_pos (by linarith) _
  have haverage : D⁻¹ * (If + (ε⁻¹) ^ (2 : ℕ) * Ig) = level ^ (2 : ℕ) := by
    calc
      D⁻¹ * (If + (ε⁻¹) ^ (2 : ℕ) * Ig) =
          closedBallL2Energy f x r +
            (ε⁻¹) ^ (2 : ℕ) * closedBallL2Energy g x r := by
              simp only [closedBallL2Energy, closedBallAverage, D, If, Ig]
              ring
      _ = level ^ (2 : ℕ) := hsum
  have hcombined : If + (ε⁻¹) ^ (2 : ℕ) * Ig = level ^ (2 : ℕ) * D := by
    calc
      If + (ε⁻¹) ^ (2 : ℕ) * Ig = D * (D⁻¹ * (If + (ε⁻¹) ^ (2 : ℕ) * Ig)) := by
        field_simp [hD_pos.ne']
      _ = D * level ^ (2 : ℕ) := by rw [haverage]
      _ = level ^ (2 : ℕ) * D := by ring
  calc
    ∫ y in Metric.closedBall x r,
        (‖f y‖ ^ (2 : ℕ) + (ε⁻¹) ^ (2 : ℕ) * ‖g y‖ ^ (2 : ℕ)) ∂volume =
        If + (ε⁻¹) ^ (2 : ℕ) * Ig := by
          have hfB : Integrable (fun y => ‖f y‖ ^ (2 : ℕ))
              (volume.restrict (Metric.closedBall x r)) := hf.integrableOn
          have hgB : Integrable (fun y => (ε⁻¹) ^ (2 : ℕ) * ‖g y‖ ^ (2 : ℕ))
              (volume.restrict (Metric.closedBall x r)) :=
            hg.integrableOn.const_mul ((ε⁻¹) ^ (2 : ℕ))
          have hadd : ∫ y, ((ε⁻¹) ^ (2 : ℕ) * ‖g y‖ ^ (2 : ℕ) + ‖f y‖ ^ (2 : ℕ)) ∂
              volume.restrict (Metric.closedBall x r) =
              (∫ y, (ε⁻¹) ^ (2 : ℕ) * ‖g y‖ ^ (2 : ℕ) ∂volume.restrict (Metric.closedBall x r)) +
                ∫ y, ‖f y‖ ^ (2 : ℕ) ∂volume.restrict (Metric.closedBall x r) :=
            MeasureTheory.integral_add hgB hfB
          calc
            ∫ y in Metric.closedBall x r,
                (‖f y‖ ^ (2 : ℕ) + (ε⁻¹) ^ (2 : ℕ) * ‖g y‖ ^ (2 : ℕ)) ∂volume =
                ∫ y in Metric.closedBall x r,
                  ((ε⁻¹) ^ (2 : ℕ) * ‖g y‖ ^ (2 : ℕ) + ‖f y‖ ^ (2 : ℕ)) ∂volume := by
                    apply MeasureTheory.integral_congr_ae
                    filter_upwards [] with y
                    ring
            _ = ∫ y in Metric.closedBall x r, (ε⁻¹) ^ (2 : ℕ) * ‖g y‖ ^ (2 : ℕ) ∂volume +
                  ∫ y in Metric.closedBall x r, ‖f y‖ ^ (2 : ℕ) ∂volume := hadd
            _ = If + (ε⁻¹) ^ (2 : ℕ) * Ig := by
              simp only [If, Ig, MeasureTheory.integral_const_mul]
              ring
    _ = level ^ (2 : ℕ) * D := hcombined
    _ = level ^ (2 : ℕ) * (2 * r) ^ d := by rfl

private theorem combined_sq_le_tail_split {a b ε level : ℝ}
    (hε : 0 < ε) (hlevel : 0 ≤ level) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ (2 : ℕ) + (ε⁻¹) ^ (2 : ℕ) * b ^ (2 : ℕ) ≤
      (if level / 2 < a then a ^ (2 : ℕ) else 0) +
        (ε⁻¹) ^ (2 : ℕ) * (if ε * level / 2 < b then b ^ (2 : ℕ) else 0) +
          level ^ (2 : ℕ) / 2 := by
  have hεinv : ε * ε⁻¹ = 1 := by field_simp [hε.ne']
  have hinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  have hf_small (hfa : a ≤ level / 2) : a ^ (2 : ℕ) ≤ level ^ (2 : ℕ) / 4 := by
    nlinarith [sq_nonneg (a - level / 2)]
  have hg_small (hgb : b ≤ ε * level / 2) :
      (ε⁻¹) ^ (2 : ℕ) * b ^ (2 : ℕ) ≤ level ^ (2 : ℕ) / 4 := by
    have hscaled := mul_le_mul_of_nonneg_left hgb hinv_nonneg
    have hright : ε⁻¹ * (ε * level / 2) = level / 2 := by
      calc
        ε⁻¹ * (ε * level / 2) = (ε * ε⁻¹) * level / 2 := by ring
        _ = level / 2 := by rw [hεinv, one_mul]
    rw [hright] at hscaled
    have hscaled_nonneg : 0 ≤ ε⁻¹ * b := mul_nonneg hinv_nonneg hb
    have hsq : (ε⁻¹ * b) ^ (2 : ℕ) ≤ (level / 2) ^ (2 : ℕ) :=
      (sq_le_sq₀ hscaled_nonneg (by linarith)).2 hscaled
    nlinarith [hsq]
  by_cases hfa : level / 2 < a
  · rw [if_pos hfa]
    by_cases hgb : ε * level / 2 < b
    · rw [if_pos hgb]
      nlinarith [sq_nonneg level]
    · rw [if_neg hgb]
      nlinarith [hg_small (le_of_not_gt hgb)]
  · rw [if_neg hfa]
    by_cases hgb : ε * level / 2 < b
    · rw [if_pos hgb]
      nlinarith [hf_small (le_of_not_gt hfa)]
    · rw [if_neg hgb]
      nlinarith [hf_small (le_of_not_gt hfa), hg_small (le_of_not_gt hgb)]

/-- At an exact combined stopping radius, the normalized energy is forced into
the two corresponding weighted superlevel tails. -/
theorem goodLambdaCombinedEnergy_eq_tail_transfer
    {d : ℕ} {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : Vec d → F) (g : Vec d → G) {ε level r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume)
    (hfi : Integrable (fun y => ‖f y‖ ^ (2 : ℕ)) volume)
    (hgi : Integrable (fun y => ‖g y‖ ^ (2 : ℕ)) volume)
    (x : Vec d) (hstop : goodLambdaCombinedEnergy f g ε x r = level) :
    ENNReal.ofReal (level ^ (2 : ℕ)) * volume (Metric.closedBall x r) ≤
      2 * sqWeightedMeasure f volume
          ({y | level / 2 < ‖f y‖} ∩ Metric.closedBall x r) +
        2 * ENNReal.ofReal ((ε⁻¹) ^ (2 : ℕ)) * sqWeightedMeasure g volume
          ({y | ε * level / 2 < ‖g y‖} ∩ Metric.closedBall x r) := by
  let B : Set (Vec d) := Metric.closedBall x r
  let A : Set (Vec d) := {y | level / 2 < ‖f y‖}
  let C : Set (Vec d) := {y | ε * level / 2 < ‖g y‖}
  let D : ℝ := (2 * r) ^ d
  have hB : MeasurableSet B := measurableSet_closedBall
  have hA : NullMeasurableSet A volume := by
    simpa only [A] using aestronglyMeasurable_const.nullMeasurableSet_lt hf.norm
  have hC : NullMeasurableSet C volume := by
    simpa only [C] using aestronglyMeasurable_const.nullMeasurableSet_lt hg.norm
  have hAB : NullMeasurableSet (A ∩ B) volume := hA.inter hB.nullMeasurableSet
  have hCB : NullMeasurableSet (C ∩ B) volume := hC.inter hB.nullMeasurableSet
  have hlevel : 0 ≤ level := by
    rw [← hstop]
    exact goodLambdaCombinedEnergy_nonneg f g ε x r
  have hpoint : B.indicator (fun y =>
      ‖f y‖ ^ (2 : ℕ) + (ε⁻¹) ^ (2 : ℕ) * ‖g y‖ ^ (2 : ℕ)) ≤
      (A ∩ B).indicator (fun y => ‖f y‖ ^ (2 : ℕ)) +
        (fun y => (ε⁻¹) ^ (2 : ℕ) *
          (C ∩ B).indicator (fun y => ‖g y‖ ^ (2 : ℕ)) y) +
          B.indicator (fun _ => level ^ (2 : ℕ) / 2) := by
    intro y
    change B.indicator (fun y =>
      ‖f y‖ ^ (2 : ℕ) + (ε⁻¹) ^ (2 : ℕ) * ‖g y‖ ^ (2 : ℕ)) y ≤
      (A ∩ B).indicator (fun y => ‖f y‖ ^ (2 : ℕ)) y +
        (ε⁻¹) ^ (2 : ℕ) * (C ∩ B).indicator (fun y => ‖g y‖ ^ (2 : ℕ)) y +
          B.indicator (fun _ => level ^ (2 : ℕ) / 2) y
    by_cases hyB : y ∈ B
    · rw [Set.indicator_of_mem hyB]
      by_cases hyA : y ∈ A
      · have hyA' : level / 2 < ‖f y‖ := by simpa only [A] using! hyA
        have hyAB : y ∈ A ∩ B := ⟨hyA, hyB⟩
        rw [Set.indicator_of_mem hyAB]
        by_cases hyC : y ∈ C
        · have hyC' : ε * level / 2 < ‖g y‖ := by simpa only [C] using! hyC
          have hyCB : y ∈ C ∩ B := ⟨hyC, hyB⟩
          rw [Set.indicator_of_mem hyCB, Set.indicator_of_mem hyB]
          simpa only [if_pos hyA', if_pos hyC'] using
            (combined_sq_le_tail_split (a := ‖f y‖) (b := ‖g y‖) hε hlevel
              (norm_nonneg _) (norm_nonneg _))
        · have hyC' : ¬ ε * level / 2 < ‖g y‖ := by simpa only [C] using! hyC
          rw [Set.indicator_of_notMem (fun h : y ∈ C ∩ B => hyC h.1),
            Set.indicator_of_mem hyB]
          simpa only [if_pos hyA', if_neg hyC'] using
            (combined_sq_le_tail_split (a := ‖f y‖) (b := ‖g y‖) hε hlevel
              (norm_nonneg _) (norm_nonneg _))
      · have hyA' : ¬ level / 2 < ‖f y‖ := by simpa only [A] using! hyA
        rw [Set.indicator_of_notMem (fun h : y ∈ A ∩ B => hyA h.1)]
        by_cases hyC : y ∈ C
        · have hyC' : ε * level / 2 < ‖g y‖ := by simpa only [C] using! hyC
          have hyCB : y ∈ C ∩ B := ⟨hyC, hyB⟩
          rw [Set.indicator_of_mem hyCB, Set.indicator_of_mem hyB]
          simpa only [if_neg hyA', if_pos hyC'] using
            (combined_sq_le_tail_split (a := ‖f y‖) (b := ‖g y‖) hε hlevel
              (norm_nonneg _) (norm_nonneg _))
        · have hyC' : ¬ ε * level / 2 < ‖g y‖ := by simpa only [C] using! hyC
          rw [Set.indicator_of_notMem (fun h : y ∈ C ∩ B => hyC h.1),
            Set.indicator_of_mem hyB]
          simpa only [if_neg hyA', if_neg hyC'] using
            (combined_sq_le_tail_split (a := ‖f y‖) (b := ‖g y‖) hε hlevel
              (norm_nonneg _) (norm_nonneg _))
    · rw [Set.indicator_of_notMem hyB, Set.indicator_of_notMem (fun h => hyB h.2),
        Set.indicator_of_notMem (fun h => hyB h.2), Set.indicator_of_notMem hyB]
      positivity
  have hfTail : Integrable ((A ∩ B).indicator (fun y => ‖f y‖ ^ (2 : ℕ))) volume :=
    hfi.integrableOn.integrable_indicator₀ hAB
  have hgTail : Integrable ((C ∩ B).indicator (fun y => ‖g y‖ ^ (2 : ℕ))) volume :=
    hgi.integrableOn.integrable_indicator₀ hCB
  have hconstOn : IntegrableOn (fun _ : Vec d => level ^ (2 : ℕ) / 2) B volume :=
    integrableOn_const (measure_closedBall_lt_top.ne)
  have hconst : Integrable (B.indicator (fun _ : Vec d => level ^ (2 : ℕ) / 2)) volume :=
    hconstOn.integrable_indicator hB
  have hfB : Integrable (fun y => ‖f y‖ ^ (2 : ℕ)) (volume.restrict B) :=
    hfi.integrableOn
  have hgB : Integrable (fun y => ‖g y‖ ^ (2 : ℕ)) (volume.restrict B) :=
    hgi.integrableOn
  have hleft : Integrable (B.indicator (fun y =>
      ‖f y‖ ^ (2 : ℕ) + (ε⁻¹) ^ (2 : ℕ) * ‖g y‖ ^ (2 : ℕ))) volume := by
    have hsumB : Integrable (fun y =>
        ‖f y‖ ^ (2 : ℕ) + (ε⁻¹) ^ (2 : ℕ) * ‖g y‖ ^ (2 : ℕ))
        (volume.restrict B) := hfB.add (hgB.const_mul _)
    rw [MeasureTheory.integrable_indicator_iff hB]
    exact hsumB
  have hright : Integrable ((A ∩ B).indicator (fun y => ‖f y‖ ^ (2 : ℕ)) +
      (fun y => (ε⁻¹) ^ (2 : ℕ) *
        (C ∩ B).indicator (fun y => ‖g y‖ ^ (2 : ℕ)) y) +
        B.indicator (fun _ => level ^ (2 : ℕ) / 2)) volume :=
    (hfTail.add ((hgi.integrableOn.integrable_indicator₀ hCB).const_mul _)).add hconst
  have hintegral := MeasureTheory.integral_mono_ae hleft hright
    (ae_of_all volume hpoint)
  have hvol : ∫ y in B, (level ^ (2 : ℕ) / 2) ∂volume =
      (level ^ (2 : ℕ) / 2) * D := by
    rw [MeasureTheory.integral_const, MeasureTheory.measureReal_restrict_apply_univ,
      MeasureTheory.measureReal_def,
      Real.volume_pi_closedBall x hr.le, ENNReal.toReal_ofReal]
    · simp only [D, Fintype.card_fin, smul_eq_mul]
      ring
    · exact pow_nonneg (by linarith) _
  have htail_real : level ^ (2 : ℕ) * D ≤
      2 * (∫ y in A ∩ B, ‖f y‖ ^ (2 : ℕ) ∂volume) +
        2 * (ε⁻¹) ^ (2 : ℕ) * (∫ y in C ∩ B, ‖g y‖ ^ (2 : ℕ) ∂volume) := by
    have hmass := combined_energy_mass_identity f g hε hr hfi hgi x hstop
    have hintegral' : ∫ y in B,
        (‖f y‖ ^ (2 : ℕ) + (ε⁻¹) ^ (2 : ℕ) * ‖g y‖ ^ (2 : ℕ)) ∂volume ≤
        (∫ y in A ∩ B, ‖f y‖ ^ (2 : ℕ) ∂volume) +
          (ε⁻¹) ^ (2 : ℕ) * (∫ y in C ∩ B, ‖g y‖ ^ (2 : ℕ) ∂volume) +
            ∫ y in B, (level ^ (2 : ℕ) / 2) ∂volume := by
      rw [MeasureTheory.integral_indicator hB] at hintegral
      have hfirst : Integrable ((A ∩ B).indicator (fun y => ‖f y‖ ^ (2 : ℕ)) +
          (fun y => (ε⁻¹) ^ (2 : ℕ) *
            (C ∩ B).indicator (fun y => ‖g y‖ ^ (2 : ℕ)) y)) volume :=
        hfTail.add (hgTail.const_mul _)
      rw [MeasureTheory.integral_add' hfirst hconst, MeasureTheory.integral_add'
        hfTail (hgTail.const_mul _),
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_indicator₀ hAB, MeasureTheory.integral_indicator₀ hCB] at hintegral
      rw [MeasureTheory.integral_indicator hB] at hintegral
      exact hintegral
    dsimp only [B] at hmass hvol hintegral'
    rw [hvol] at hintegral'
    nlinarith [hmass, hintegral']
  have hleft_volume : ENNReal.ofReal (level ^ (2 : ℕ)) * volume B =
      ENNReal.ofReal (level ^ (2 : ℕ) * D) := by
    rw [Real.volume_pi_closedBall x hr.le, ENNReal.ofReal_mul]
    · simp only [D, Fintype.card_fin]
    · exact pow_nonneg (by linarith) _
  rw [hleft_volume]
  have htail_nonneg_f : 0 ≤ ∫ y in A ∩ B, ‖f y‖ ^ (2 : ℕ) ∂volume :=
    MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have htail_nonneg_g : 0 ≤ ∫ y in C ∩ B, ‖g y‖ ^ (2 : ℕ) ∂volume :=
    MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hENN := ENNReal.ofReal_le_ofReal htail_real
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfi.integrableOn.mono_set
      (Set.inter_subset_right)) (ae_of_all _ fun _ => sq_nonneg _),
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hgi.integrableOn.mono_set
      (Set.inter_subset_right)) (ae_of_all _ fun _ => sq_nonneg _),
    ← sqWeightedMeasure_apply₀ f hAB, ← sqWeightedMeasure_apply₀ g hCB] at hENN
  calc
    ENNReal.ofReal (level ^ (2 : ℕ) * D) =
        ENNReal.ofReal (level ^ (2 : ℕ)) * ENNReal.ofReal D :=
      ENNReal.ofReal_mul (sq_nonneg level)
    _ ≤ ENNReal.ofReal 2 * sqWeightedMeasure f volume (A ∩ B) +
        ENNReal.ofReal (2 * (ε⁻¹) ^ (2 : ℕ)) * sqWeightedMeasure g volume (C ∩ B) := hENN
    _ = 2 * sqWeightedMeasure f volume
          ({y | level / 2 < ‖f y‖} ∩ Metric.closedBall x r) +
        2 * ENNReal.ofReal ((ε⁻¹) ^ (2 : ℕ)) * sqWeightedMeasure g volume
          ({y | ε * level / 2 < ‖g y‖} ∩ Metric.closedBall x r) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [A, B, C]

/-- A combined good-`λ` energy bound controls each component at the same
radius. -/
theorem closedBallL2Energy_sqrt_bounds_of_goodLambdaCombinedEnergy_le
    {d : ℕ} {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : Vec d → F) (g : Vec d → G) {ε level r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (x : Vec d) (h : goodLambdaCombinedEnergy f g ε x r ≤ level) :
    Real.sqrt (closedBallL2Energy f x r) ≤ level ∧
      Real.sqrt (closedBallL2Energy g x r) ≤ ε * level := by
  have hf_nonneg : 0 ≤ closedBallL2Energy f x r :=
    closedBallL2Energy_nonneg f x hr
  have hg_nonneg : 0 ≤ closedBallL2Energy g x r :=
    closedBallL2Energy_nonneg g x hr
  have hfirst : Real.sqrt (closedBallL2Energy f x r) ≤ level := by
    calc
      Real.sqrt (closedBallL2Energy f x r) ≤
          Real.sqrt (closedBallL2Energy f x r +
            (ε⁻¹) ^ (2 : ℕ) * closedBallL2Energy g x r) := by
              apply Real.sqrt_le_sqrt
              exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hg_nonneg)
      _ = goodLambdaCombinedEnergy f g ε x r := rfl
      _ ≤ level := h
  have hsecond_scaled : ε⁻¹ * Real.sqrt (closedBallL2Energy g x r) ≤ level := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (closedBallL2Energy g x r) := Real.sqrt_nonneg _
    have hsquare : (ε⁻¹) ^ (2 : ℕ) * closedBallL2Energy g x r =
        (ε⁻¹ * Real.sqrt (closedBallL2Energy g x r)) ^ (2 : ℕ) := by
      rw [mul_pow]
      norm_num [Real.sq_sqrt hg_nonneg]
    have hroot : ε⁻¹ * Real.sqrt (closedBallL2Energy g x r) ≤
        goodLambdaCombinedEnergy f g ε x r := by
      rw [goodLambdaCombinedEnergy]
      have hsum_nonneg : 0 ≤ closedBallL2Energy f x r +
          (ε⁻¹ * Real.sqrt (closedBallL2Energy g x r)) ^ (2 : ℕ) := by positivity
      calc
        ε⁻¹ * Real.sqrt (closedBallL2Energy g x r) =
            Real.sqrt ((ε⁻¹ * Real.sqrt (closedBallL2Energy g x r)) ^ (2 : ℕ)) := by
              rw [Real.sqrt_sq_eq_abs]
              exact (abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hε.le) hsqrt_nonneg)).symm
        _ ≤ Real.sqrt (closedBallL2Energy f x r +
            (ε⁻¹ * Real.sqrt (closedBallL2Energy g x r)) ^ (2 : ℕ)) := by
              apply Real.sqrt_le_sqrt
              exact le_add_of_nonneg_left hf_nonneg
        _ = Real.sqrt (closedBallL2Energy f x r +
            (ε⁻¹) ^ (2 : ℕ) * closedBallL2Energy g x r) := by rw [hsquare]
    exact hroot.trans h
  constructor
  · exact hfirst
  · have hεinv : ε * ε⁻¹ = 1 := by field_simp [hε.ne']
    have hmul := mul_le_mul_of_nonneg_left hsecond_scaled hε.le
    calc
      Real.sqrt (closedBallL2Energy g x r) =
          (ε * ε⁻¹) * Real.sqrt (closedBallL2Energy g x r) := by rw [hεinv, one_mul]
      _ = ε * (ε⁻¹ * Real.sqrt (closedBallL2Energy g x r)) := by ring
      _ ≤ ε * level := hmul

end CubeCalderonZygmund

end

end Homogenization
