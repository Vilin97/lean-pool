/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Causality
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.UniformHalfCylinder

/-! # Closed-cylinder control using only past-time source bounds

The smooth localization may depend on the future boundary of the domain.
Only its sources at times at most zero contribute on the target cylinder.
Consequently the numerical bounds below concern the truncated sources only.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Core.HeatPotential

noncomputable section

namespace CKN.Core.Endgame

/-- The uniform half-cylinder estimate needs no bound on future-time sources.
The source representation is retained before truncation, and causality proves
the required representation after truncation. -/
theorem uniform_halfCylinder_representative_of_past_source_bounds
    (q ε₀ : ℝ) (KF KG : ℝ≥0∞)
    (hq : 5 / 2 < q) (hε₀ : 0 ≤ ε₀) (hKF : KF < ⊤) (hKG : KG < ⊤)
    {Ω : Set Vec3} {I : Set ℝ}
    {u F : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {G : Fin 3 → ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ z in parabolicCylinder 0 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (hF : ∀ i, AEMeasurable
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => F z i)) volume)
    (hG : ∀ j i, AEMeasurable
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => G j z i)) volume)
    (hNF : ∀ i, morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => F z i)) ≤ KF)
    (hNG : ∀ j i, morreyNorm (6 / 5) (25 / 3)
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => G j z i)) ≤ KG)
    (hFsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 1 → F z = 0)
    (hGsupp : ∀ j z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 1 → G j z = 0)
    (hrep : u =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))]
      (fun z i => heatPotential (fun w => F w i) (fun j w => G j w i) z)) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
      ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
        w (stepGamma₀ q) (uniformHalfCylinderHolderBound q ε₀ KF KG) ∧
      ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
        IsRegularPoint Ω I u z := by
  let Fpast : ParabolicPoint → Vec3 := fun z i =>
    {w : ParabolicPoint | w.2 ≤ 0}.indicator (fun w => F w i) z
  let Gpast : Fin 3 → ParabolicPoint → Vec3 := fun j z i =>
    {w : ParabolicPoint | w.2 ≤ 0}.indicator (fun w => G j w i) z
  have hFp : ∀ i, AEMeasurable (fun z => Fpast z i) volume :=
    hF
  have hGp : ∀ j i, AEMeasurable (fun z => Gpast j z i) volume :=
    hG
  have hFpSupport : ∀ z ∉ parabolicCylinder (0 : Vec3) 0 1, Fpast z = 0 := by
    intro z hz
    funext i
    by_cases ht : z.2 ≤ 0
    · change {w : ParabolicPoint | w.2 ≤ 0}.indicator (fun w => F w i) z = 0
      rw [Set.indicator_of_mem (show z ∈ {w : ParabolicPoint | w.2 ≤ 0} from ht)]
      exact congrFun (hFsupp z ht hz) i
    · exact Set.indicator_of_notMem
        (show z ∉ {w : ParabolicPoint | w.2 ≤ 0} from ht) _
  have hGpSupport : ∀ j z, z ∉ parabolicCylinder (0 : Vec3) 0 1 → Gpast j z = 0 := by
    intro j z hz
    funext i
    by_cases ht : z.2 ≤ 0
    · change {w : ParabolicPoint | w.2 ≤ 0}.indicator (fun w => G j w i) z = 0
      rw [Set.indicator_of_mem (show z ∈ {w : ParabolicPoint | w.2 ≤ 0} from ht)]
      exact congrFun (hGsupp j z ht hz) i
    · exact Set.indicator_of_notMem
        (show z ∉ {w : ParabolicPoint | w.2 ≤ 0} from ht) _
  have hrepPast : u =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))]
      (fun z i => heatPotential (fun w => Fpast w i) (fun j w => Gpast j w i) z) := by
    have hQ : MeasurableSet (parabolicCylinder (0 : Vec3) 0 (1 / 2)) :=
      (vec3Ball_measurable _ _).prod measurableSet_Ioc
    filter_upwards [hrep, ae_restrict_mem hQ] with z hz hzQ
    rw [hz]
    funext i
    exact (heatPotential_time_truncation (fun w => F w i)
      (fun j w => G j w i) hzQ.2.2).symm
  exact uniform_halfCylinder_representative_of_paper_source_bounds q ε₀ KF KG
    hq hε₀ hKF hKG hsol hdom hsmall hFp hGp hNF hNG
    (fun i z hz => congrFun (hFpSupport z hz) i)
    (fun j i z hz => congrFun (hGpSupport j z hz) i) hrepPast

end CKN.Core.Endgame
