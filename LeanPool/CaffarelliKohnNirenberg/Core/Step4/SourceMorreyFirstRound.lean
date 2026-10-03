/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CarrierRestriction
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyFirstRoundCutoff
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyFirstRoundNorms

/-!
# The first-round source data on an arbitrary parabolic ball

`prop:bootstrap` improves `u ∈ M^{3,25/3}` to `u ∈ M^{3,25}` in one
round.  The round localizes `eq:local-equation` by a cutoff adapted to the
parabolic ball `𝔅_R(z₀)` and reads the two sources of the heat representation
at the exponents `1/κ₂ = 1/τ + 1/τ₃ = 3/25 + 8/25 = 11/25`: the heat slot in
`M^{6/5,25/11}` and the derivative slot in `M^{3,25/6}`.

The statement below is the complete data of that localization — the cutoff,
its compactly interior product box, the measurability and compact support of
both sources, the two source Morrey norms certified finite, and the vanishing
of both sources outside the half ball.  The centre and radius are arbitrary
and the carrier is the symmetric parabolic ball, not a one-sided cylinder.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3
open CKN.Core.Endgame

noncomputable section

namespace CKN.Core.Step4

/-- The first-round localized source data of `eq:local-equation` on the
parabolic ball `𝔅_R(z₀)`, at the paper's first-round exponents
`(6/5, 25/11)` for the heat slot and `(3, 25/6)` for the derivative slot. -/
theorem first_round_source_package_of_sws :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
      Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
      morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ R) u →
      (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
        (Metric.ball z₀ R) (fun z => Du z i)) →
      ∀ {Dp : ParabolicPoint → Vec3},
      (∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
        (volume.restrict (Metric.ball z₀ (R / 2)))) →
      morreyVecMem (6 / 5 : ℝ) (min q (25 / 11 : ℝ))
        (Metric.ball z₀ (R / 2)) Dp →
      ∃ (φ : Vec3 × ℝ → ℝ) (U : Set Vec3) (J : Set ℝ)
        (KF KG : ℝ≥0∞),
        φ ∈ spaceTimeTestFunction (V := ℝ) Ω I ∧
        localBox Ω I U J ∧
        tsupport φ ⊆ U ×ˢ J ∧
        (U ×ˢ J) ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (R / 2) ∧
        (∀ z ∈ Metric.ball z₀ (R / 4), φ (z.1, z.2) = 1) ∧
        (∀ i : Fin 3, Integrable (fun z => Dp z i)
          (volume.restrict (spaceTimeSet U J))) ∧
        (∀ i : Fin 3, AEMeasurable
          (fun z => localizedGradientSourceG φ u Du f Dp z i) volume) ∧
        (∀ j i : Fin 3, AEMeasurable
          (fun z => localizedGradientSourceH φ u j z i) volume) ∧
        (∀ i : Fin 3, HasCompactSupport
          (fun z => localizedGradientSourceG φ u Du f Dp z i)) ∧
        (∀ j i : Fin 3, HasCompactSupport
          (fun z => localizedGradientSourceH φ u j z i)) ∧
        KF < ⊤ ∧ KG < ⊤ ∧
        (∀ i : Fin 3, morreyNorm (6 / 5 : ℝ) (25 / 11)
          (fun z => localizedGradientSourceG φ u Du f Dp z i) ≤ KF) ∧
        (∀ j i : Fin 3, morreyNorm 3 (25 / 6)
          (fun z => localizedGradientSourceH φ u j z i) ≤ KG) ∧
        (∀ z ∉ Metric.ball z₀ (R / 2),
          localizedGradientSourceG φ u Du f Dp z = 0) ∧
        (∀ j z, z ∉ Metric.ball z₀ (R / 2) →
          localizedGradientSourceH φ u j z = 0) := by
  intro Ω I q u Du p f hsol z₀ R hR hdom hu hDu Dp hDpAE hDpN
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have hρ : (0 : ℝ) < R / 2 := by positivity
  obtain ⟨φ, hφ, _hφrange, hφone, hφsupp, hbox, hφbox⟩ :=
    exists_first_round_cutoff hR hdom
  have hboxeq : spaceTimeSet (vec3Ball z₀.1 (R / 2))
      (Set.Ioo (z₀.2 - (R / 2) ^ 2) (z₀.2 + (R / 2) ^ 2)) =
      Metric.ball z₀ (R / 2) := parabolic_box_eq_ball z₀ (R / 2)
  have hφcarrier : tsupport φ ⊆
      parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (R / 2) :=
    hφsupp.trans (Set.preimage_mono
      (Metric.ball_subset_ball (by linarith only [hR])))
  have hDpN' : morreyVecMem (6 / 5 : ℝ) (25 / 11 : ℝ)
      (Metric.ball z₀ (R / 2)) Dp := by
    rwa [min_eq_right (by linarith only [hq] : (25 / 11 : ℝ) ≤ q)] at hDpN
  have hu' : morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ (R / 2)) u :=
    CKN.Core.Endgame.morreyVecMem_mono_carrier (by norm_num)
      (Metric.ball_subset_ball (by linarith only [hR])) hu
  have hDu' : ∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
      (Metric.ball z₀ (R / 2)) (fun z => Du z i) := fun i =>
    CKN.Core.Endgame.morreyVecMem_mono_carrier (by norm_num)
      (Metric.ball_subset_ball (by linarith only [hR])) (hDu i)
  have hDpInt : ∀ i : Fin 3, Integrable (fun z => Dp z i)
      (volume.restrict (spaceTimeSet (vec3Ball z₀.1 (R / 2))
        (Set.Ioo (z₀.2 - (R / 2) ^ 2) (z₀.2 + (R / 2) ^ 2)))) := by
    intro i
    rw [hboxeq]
    exact integrableOn_ball_of_morreyBallNorm (P := (6 / 5 : ℝ))
      (τ := (25 / 11 : ℝ)) (by norm_num) (by norm_num) hρ (hDpAE i) (hDpN' i)
  obtain ⟨hGae, hHnegae⟩ := localized_gradient_source_aemeasurable_of_sws
    hsol hφ hbox hφbox (fun i => (hDpInt i).aemeasurable)
  obtain ⟨_hGint, _hHint, hGc, hHnegc⟩ :=
    localized_gradient_source_data_of_sws hsol hφ hbox hφbox hDpInt
  obtain ⟨hGN, hHN⟩ := first_round_gradient_source_morrey_of_sws hsol hφ
    hbox hφbox z₀ (R / 2) hρ hφcarrier hu' hDu' hDpAE hDpN'
  have hHneg (j i : Fin 3) : (fun z => localizedGradientSourceH φ u j z i) =
      -(fun z => -localizedGradientSourceH φ u j z i) := by
    funext z
    simp only [Pi.neg_apply, neg_neg]
  have hHae : ∀ j i : Fin 3, AEMeasurable
      (fun z => localizedGradientSourceH φ u j z i) volume := by
    intro j i
    rw [hHneg j i]
    exact (hHnegae j i).neg
  have hHc : ∀ j i : Fin 3, HasCompactSupport
      (fun z => localizedGradientSourceH φ u j z i) := by
    intro j i
    rw [hHneg j i]
    exact (hHnegc j i).neg
  have hnot : ∀ (z : ParabolicPoint), z ∉ Metric.ball z₀ (R / 2) →
      (z.1, z.2) ∉ tsupport φ := by
    intro z hz hm
    apply hz
    have hm' : parabolicHomeomorph.symm (z.1, z.2) ∈
      Metric.ball z₀ (R / 2) := hφcarrier hm
    exact hm'
  have hφzero : ∀ (z : ParabolicPoint), z ∉ Metric.ball z₀ (R / 2) →
      (show ParabolicPoint → ℝ from φ) z = 0 := by
    intro z hz
    change φ (z.1, z.2) = 0
    exact image_eq_zero_of_notMem_tsupport (hnot z hz)
  have htimezero : ∀ (z : ParabolicPoint), z ∉ Metric.ball z₀ (R / 2) →
      timePartial φ z = 0 := fun z hz =>
    timePartial_zero_of_not_mem_tsupport_public hφ.1 (hnot z hz)
  have hspzero : ∀ (j : Fin 3) (z : ParabolicPoint),
      z ∉ Metric.ball z₀ (R / 2) → spatialPartial φ j z = 0 := fun j z hz =>
    spatialPartial_zero_of_not_mem_tsupport_public hφ.1 (hnot z hz) j
  have hlapzero : ∀ (z : ParabolicPoint), z ∉ Metric.ball z₀ (R / 2) →
      spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0 := by
    intro z hz
    change (∑ j : Fin 3, spatialSecondPartial
      (show ParabolicPoint → ℝ from φ) j j z) = 0
    exact Finset.sum_eq_zero (fun j _ =>
      spatialSecondPartial_zero_of_not_mem_tsupport_public hφ.1
        (hnot z hz) j j)
  have hGzero : ∀ z ∉ Metric.ball z₀ (R / 2),
      localizedGradientSourceG φ u Du f Dp z = 0 := by
    intro z hz
    funext i
    dsimp only [localizedGradientSourceG, localizedEquationG, Pi.zero_apply]
    rw [hφzero z hz, htimezero z hz, hlapzero z hz]
    ring
  have hHzero : ∀ (j : Fin 3) (z : ParabolicPoint),
      z ∉ Metric.ball z₀ (R / 2) →
      localizedGradientSourceH φ u j z = 0 := by
    intro j z hz
    funext i
    simp only [localizedGradientSourceH, localizedEquationH, hspzero j z hz,
      mul_zero, zero_smul, Pi.zero_apply]
  refine ⟨φ, vec3Ball z₀.1 (R / 2),
    Set.Ioo (z₀.2 - (R / 2) ^ 2) (z₀.2 + (R / 2) ^ 2),
    ∑ i : Fin 3, morreyNorm (6 / 5 : ℝ) (25 / 11)
      (fun z => localizedGradientSourceG φ u Du f Dp z i),
    ∑ j : Fin 3, ∑ i : Fin 3, morreyNorm 3 (25 / 6)
      (fun z => localizedGradientSourceH φ u j z i),
    hφ, hbox, hφbox, parabolic_box_subset_ball_preimage z₀ (R / 2), hφone,
    hDpInt, hGae, hHae, hGc, hHc, ?_, ?_, ?_, ?_, hGzero, hHzero⟩
  · exact ENNReal.sum_lt_top.mpr (fun i _ => hGN i)
  · refine ENNReal.sum_lt_top.mpr (fun j _ => ?_)
    exact ENNReal.sum_lt_top.mpr (fun i _ => hHN j i)
  · intro i
    exact Finset.single_le_sum
      (f := fun i : Fin 3 => morreyNorm (6 / 5 : ℝ) (25 / 11)
        (fun z => localizedGradientSourceG φ u Du f Dp z i))
      (fun _ _ => by simp) (Finset.mem_univ i)
  · intro j i
    refine le_trans (Finset.single_le_sum
      (f := fun i : Fin 3 => morreyNorm 3 (25 / 6)
        (fun z => localizedGradientSourceH φ u j z i))
      (fun _ _ => by simp) (Finset.mem_univ i)) ?_
    exact Finset.single_le_sum
      (f := fun j : Fin 3 => ∑ i : Fin 3, morreyNorm 3 (25 / 6)
        (fun z => localizedGradientSourceH φ u j z i))
      (fun _ _ => by simp) (Finset.mem_univ j)

end CKN.Core.Step4
