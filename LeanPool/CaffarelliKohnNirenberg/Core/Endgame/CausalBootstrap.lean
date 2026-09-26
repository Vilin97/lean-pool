/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BootstrapBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Causality
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradient

/-! # Quantitative bootstrap from past-time sources

The global bootstrap is applied to the truncated potential itself. Its
agreement with velocity is needed only on the target cylinder. Consequently
no bound or representation for the truncated velocity at future times is used.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- Past component bounds and a local literal heat representation imply
the improved velocity bound on the target cylinder. -/
theorem causal_bootstrap_morrey_le_of_local_representation
    (KF KG : ℝ≥0∞) (hKF : KF < ⊤) (hKG : KG < ⊤)
    {u F : ParabolicPoint → Vec3} {H : Fin 3 → ParabolicPoint → Vec3}
    (hF : ∀ i, AEMeasurable
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => F z i)) volume)
    (hH : ∀ j i, AEMeasurable
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => H j z i)) volume)
    (hNF : ∀ i, morreyNorm (6 / 5) (25 / 11)
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => F z i)) ≤ KF)
    (hNH : ∀ j i, morreyNorm 3 (25 / 6)
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => H j z i)) ≤ KG)
    (hFsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (21 / 32) → F z = 0)
    (hHsupp : ∀ j z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (21 / 32) →
      H j z = 0)
    (hrep : u =ᵐ[volume.restrict (parabolicCylinder (0 : Vec3) 0 (5 / 8))]
      vectorHeatPotential F H) :
    ∀ i, morreyNorm 3 25 ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) ≤ bootstrapSourceMorreyBound (3 * KF) (3 * KG) := by
  let g : ParabolicPoint → Vec3 := fun z i =>
    {w : ParabolicPoint | w.2 ≤ 0}.indicator (fun w => F w i) z
  let h : Fin 3 → ParabolicPoint → Vec3 := fun j z i =>
    -({w : ParabolicPoint | w.2 ≤ 0}.indicator (fun w => H j w i) z)
  have hg : ∀ i, AEMeasurable (fun z => g z i) volume := hF
  have hh : ∀ j i, AEMeasurable (fun z => h j z i) volume := fun j i => (hH j i).neg
  have hhN : ∀ j i, morreyNorm 3 (25 / 6) (fun z => h j z i) ≤ KG := by
    intro j i
    simpa only [h, morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg] using hNH j i
  have hgs : ∀ z ∉ parabolicCylinder (0 : Vec3) 0 (21 / 32), g z = 0 := by
    intro z hz
    funext i
    by_cases ht : z.2 ≤ 0
    · change {w : ParabolicPoint | w.2 ≤ 0}.indicator (fun w => F w i) z = 0
      rw [indicator_of_mem (show z ∈ {w : ParabolicPoint | w.2 ≤ 0} from ht)]
      exact congrFun (hFsupp z ht hz) i
    · exact indicator_of_notMem (show z ∉ {w : ParabolicPoint | w.2 ≤ 0} from ht) _
  have hhs : ∀ j z, z ∉ parabolicCylinder (0 : Vec3) 0 (21 / 32) → h j z = 0 := by
    intro j z hz
    funext i
    by_cases ht : z.2 ≤ 0
    · change -({w : ParabolicPoint | w.2 ≤ 0}.indicator (fun w => H j w i) z) = 0
      rw [indicator_of_mem (show z ∈ {w : ParabolicPoint | w.2 ≤ 0} from ht)]
      rw [show H j z i = 0 from congrFun (hHsupp j z ht hz) i, neg_zero]
    · simp only [h, indicator_of_notMem
        (show z ∉ {w : ParabolicPoint | w.2 ≤ 0} from ht), neg_zero, Pi.zero_apply]
  have hbound := bootstrap_morrey_le_of_component_sources KF KG hKF hKG
    (v := duhamelPotential g h) (z₀ := (0, 0)) (R := 21 / 32)
    (by norm_num) hg hh hNF hhN hgs hhs Filter.EventuallyEq.rfl
  have hQ : MeasurableSet (parabolicCylinder (0 : Vec3) 0 (5 / 8)) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioc
  have hlocal : u =ᵐ[volume.restrict (parabolicCylinder (0 : Vec3) 0 (5 / 8))]
      duhamelPotential g h := by
    filter_upwards [hrep, ae_restrict_mem hQ] with z hz hzQ
    rw [hz]
    have hsign := vectorHeatPotential_eq_duhamelPotential_neg
      (F := g) (G := fun j w i =>
        {v : ParabolicPoint | v.2 ≤ 0}.indicator (fun v => H j v i) w) z
    have heqh : (fun j w => -(fun i =>
        {v : ParabolicPoint | v.2 ≤ 0}.indicator (fun v => H j v i) w)) = h := by
      funext j w i
      rfl
    rw [heqh] at hsign
    rw [← hsign]
    funext i
    exact (heatPotential_time_truncation (fun w => F w i)
      (fun j w => H j w i) hzQ.2.2).symm
  intro i
  have hcomp : (fun z => u z i) =ᵐ[volume.restrict (parabolicCylinder (0 : Vec3) 0 (5 / 8))]
      (fun z => duhamelPotential g h z i) := hlocal.fun_comp (fun v => v i)
  rw [morrey_norm_congr_ae ((ae_eq_restrict_iff_indicator_ae_eq hQ).mp hcomp)]
  apply le_trans (morreyNorm_indicator_le (by norm_num) _ _)
  apply le_trans (morreyNorm_mono (by norm_num) ?_) hbound
  intro z
  rw [abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
  simpa only [CKN.vecEuclideanNorm, CKN.vecNormSq, CKN.vecDot, vec3EuclideanNorm, pow_two] using
    CKN.abs_apply_le_vecEuclideanNorm (duhamelPotential g h z) i

/-- A global literal representation of the localized velocity supplies
the restricted representation required by the causal bootstrap. -/
theorem localizedVelocity_heat_representation_on_plateau
    {φ : ParabolicPoint → ℝ} {u F : ParabolicPoint → Vec3}
    {H : Fin 3 → ParabolicPoint → Vec3} {S : Set ParabolicPoint}
    (hS : MeasurableSet S) (hφ : ∀ z ∈ S, φ z = 1)
    (hrep : localizedVelocity φ u =ᵐ[volume] vectorHeatPotential F H) :
    u =ᵐ[volume.restrict S] vectorHeatPotential F H := by
  filter_upwards [hrep.filter_mono (ae_mono Measure.restrict_le_self), ae_restrict_mem hS]
    with z hz hzS
  simpa only [localizedVelocity, hφ z hzS, one_smul] using hz

/-- A cutoff plateau and its global literal heat representation give the
quantitative improvement using only the past source bounds. -/
theorem causal_bootstrap_morrey_le_of_localized_representation
    (KF KG : ℝ≥0∞) (hKF : KF < ⊤) (hKG : KG < ⊤)
    {φ : ParabolicPoint → ℝ} {u F : ParabolicPoint → Vec3}
    {H : Fin 3 → ParabolicPoint → Vec3}
    (hF : ∀ i, AEMeasurable
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => F z i)) volume)
    (hH : ∀ j i, AEMeasurable
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => H j z i)) volume)
    (hNF : ∀ i, morreyNorm (6 / 5) (25 / 11)
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => F z i)) ≤ KF)
    (hNH : ∀ j i, morreyNorm 3 (25 / 6)
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => H j z i)) ≤ KG)
    (hFsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (21 / 32) → F z = 0)
    (hHsupp : ∀ j z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (21 / 32) →
      H j z = 0)
    (hφ : ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8), φ z = 1)
    (hrep : localizedVelocity φ u =ᵐ[volume] vectorHeatPotential F H) :
    ∀ i, morreyNorm 3 25 ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) ≤ bootstrapSourceMorreyBound (3 * KF) (3 * KG) :=
  causal_bootstrap_morrey_le_of_local_representation KF KG hKF hKG hF hH hNF hNH
    hFsupp hHsupp (localizedVelocity_heat_representation_on_plateau
      ((vec3Ball_measurable _ _).prod measurableSet_Ioc) hφ hrep)

end CKN.Core.Endgame
