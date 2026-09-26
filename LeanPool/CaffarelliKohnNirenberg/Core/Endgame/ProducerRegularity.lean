/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.HeatRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.HolderGluing
public import LeanPool.CaffarelliKohnNirenberg.Core.Parameters
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Localization
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceExponents
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.PotentialFiniteness
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientBase
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradient
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# Local regularity from pressure-gradient and localized-source estimates

The velocity improvement and pressure-gradient construction are used on
nested balls before localizing the equation and applying the heat estimate.
-/

public section

section

/-! # Local regularity from actual heat-potential sources

An almost-everywhere heat representation transfers the quantitative estimate
for compactly supported Morrey sources to the represented velocity.
-/

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- Genuine Morrey sources and an almost-everywhere heat representation give
a bounded Hölder representative and regularity at the center of the ball. -/
theorem regular_point_of_heat_sources
    {Ω : Set Vec3} {I : Set ℝ} {u F : ParabolicPoint → Vec3}
    {G : Fin 3 → ParabolicPoint → Vec3} {z : ParabolicPoint} {R γ θ₀ θ₁ P : ℝ}
    (hR : 0 < R) (hball : Metric.ball z R ⊆ spaceTimeSet Ω I)
    (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5) (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : ∀ i, AEMeasurable (fun x => F x i) volume)
    (hG : ∀ j i, AEMeasurable (fun x => G j x i) volume)
    (hNF : ∀ i, morreyNorm P θ₀ (fun x => F x i) < ∞)
    (hNG : ∀ j i, morreyNorm P θ₁ (fun x => G j x i) < ∞)
    (hSupportF : ∀ i, HasCompactSupport (fun x => F x i))
    (hSupportG : ∀ j i, HasCompactSupport (fun x => G j x i))
    (hrep : u =ᵐ[volume.restrict (Metric.ball z R)]
      (fun x i => heatPotential (fun y => F y i) (fun j y => G j y i) x)) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (Metric.ball z R)] u ∧
      ParabolicHolderVecNormLE (Metric.ball z R) w γ
        (vectorHeatValueBound F G γ θ₀ θ₁ P z R +
          vectorHeatHolderCoefficient F G γ θ₀ θ₁ P) ∧
      IsRegularPoint Ω I u z := by
  obtain ⟨w, hw, hnorm⟩ := vector_heat_representative_of_morrey
    hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ hF hG hNF hNG hSupportF hSupportG
  have hwlocal : w =ᵐ[volume.restrict (Metric.ball z R)]
      (fun x i => heatPotential (fun y => F y i) (fun j y => G j y i) x) :=
    ae_restrict_of_ae hw
  have hwu : w =ᵐ[volume.restrict (Metric.ball z R)] u := hwlocal.trans hrep.symm
  refine ⟨w, hwu, hnorm z R hR, ?_⟩
  exact regular_point_of_holder_norm Metric.isOpen_ball (Metric.mem_ball_self hR)
    (Subset.refl _) hball hγ hγ1.le hwu (hnorm z R hR)

/-- The standing exponent choices discharge all numerical conditions of the
heat regularity estimate at integrability exponent `6/5`. -/
theorem regular_point_of_heat_sources_at_step_parameters
    {Ω : Set Vec3} {I : Set ℝ} {u F : ParabolicPoint → Vec3}
    {G : Fin 3 → ParabolicPoint → Vec3} {z : ParabolicPoint} {R q : ℝ}
    (hq : (5 : ℝ) / 2 < q)
    (hR : 0 < R) (hball : Metric.ball z R ⊆ spaceTimeSet Ω I)
    (hF : ∀ i, AEMeasurable (fun x => F x i) volume)
    (hG : ∀ j i, AEMeasurable (fun x => G j x i) volume)
    (hNF : ∀ i, morreyNorm (6 / 5) (stepTheta₀ (stepGamma₀ q))
      (fun x => F x i) < ∞)
    (hNG : ∀ j i, morreyNorm (6 / 5) (stepTheta₁ (stepGamma₀ q))
      (fun x => G j x i) < ∞)
    (hSupportF : ∀ i, HasCompactSupport (fun x => F x i))
    (hSupportG : ∀ j i, HasCompactSupport (fun x => G j x i))
    (hrep : u =ᵐ[volume.restrict (Metric.ball z R)]
      (fun x i => heatPotential (fun y => F y i) (fun j y => G j y i) x)) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (Metric.ball z R)] u ∧
      ParabolicHolderVecNormLE (Metric.ball z R) w (stepGamma₀ q)
        (vectorHeatValueBound F G (stepGamma₀ q) (stepTheta₀ (stepGamma₀ q))
          (stepTheta₁ (stepGamma₀ q)) (6 / 5) z R +
          vectorHeatHolderCoefficient F G (stepGamma₀ q) (stepTheta₀ (stepGamma₀ q))
            (stepTheta₁ (stepGamma₀ q)) (6 / 5)) ∧
      IsRegularPoint Ω I u z := by
  have hγ := stepGamma₀_pos hq
  have hγ1 := stepGamma₀_lt_one q
  have hθ₀ := stepTheta₀_gt_half hγ hγ1
  have hθ₁ := stepTheta₁_gt_five hγ hγ1
  exact regular_point_of_heat_sources hR hball hγ hγ1
    (stepTheta₀_inv _) (stepTheta₁_inv _) (by norm_num)
    (by linarith only [hθ₀]) (by linarith only [hθ₁])
    hF hG hNF hNG hSupportF hSupportG hrep

end CKN.Core.Endgame
end

end

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4 CKN.Core.HeatPotential


noncomputable section

namespace CKN.Core.Endgame

private theorem morreyVecMem_mono_set {P τ : ℝ} (hP : 0 ≤ P)
    {S T : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    (hST : S ⊆ T) (hu : morreyVecMem P τ T u) : morreyVecMem P τ S u := by
  intro i
  apply lt_of_le_of_lt _ (hu i)
  apply morreyBallNorm_mono hP
  intro z
  by_cases hz : z ∈ S
  · simp only [indicator_of_mem hz, indicator_of_mem (hST hz), le_refl]
  · simp only [indicator_of_notMem hz, abs_zero]
    exact abs_nonneg _

private theorem localization_box_subset_ball {z : ParabolicPoint} {r : ℝ}
    :
    spaceTimeSet (vec3Ball z.1 r) (Ioo (z.2 - r ^ 2) (z.2 + r ^ 2)) ⊆
      Metric.ball z r := by
  intro w hw
  rw [metricBall_eq_parabolicBall]
  exact hw

private theorem integrableOn_ball_of_morrey
    {P τ r : ℝ} {z : ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hP : 1 ≤ P) (hPτ : P ≤ τ) (hr : 0 < r)
    (hf : AEMeasurable f (volume.restrict (Metric.ball z r)))
    (hN : morreyBallNorm P τ ((Metric.ball z r).indicator f) < ∞) :
    IntegrableOn f (Metric.ball z r) := by
  have hfi : AEMeasurable ((Metric.ball z r).indicator f) volume :=
    (aemeasurable_indicator_iff Metric.isOpen_ball.measurableSet).mpr hf
  have hc := (morreyNorm_le_morreyBallNorm (by linarith only [hP]) hPτ _).trans_lt hN
  have hl := morreyNorm_lower_integrability (p' := (1 : ℝ)) (by norm_num) hP hPτ hfi
  have hfinite : morreyNorm 1 τ ((Metric.ball z r).indicator f) < ∞ :=
    hl.trans_lt (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg
        (by simpa only [div_one] using
          sub_nonneg.mpr (one_div_le_one_div_of_le zero_lt_one hP))
        Integration.volume_parabolicCylinder_lt_top.ne) hc)
  have hi := source_power_integral_lt_top (P := (1 : ℝ)) (by norm_num)
    (R := 2 * r) (z₀ := (z.1, z.2 + r ^ 2)) (by positivity) hfi hfinite
    (fun w hw => indicator_of_notMem
      (fun hm => hw (metricBall_subset_parabolicCylinder_doubled z hr hm)) f)
  simp only [ENNReal.rpow_one] at hi
  have hi' : Integrable ((Metric.ball z r).indicator f) volume := by
    have ht := integrableOn_of_abs_integrable (S := Set.univ) hfi
      (by simpa only [Measure.restrict_univ] using hi)
    simpa only [IntegrableOn, Measure.restrict_univ] using ht
  exact (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mp hi'

/-- The localized equation and source estimates give a representative
on a fixed smaller ball with the standing Hölder exponent. -/
theorem holder_representative_of_local_producers
    (q : ℝ) (hq : 5 / 2 < q)
    (hG : ∀ q τ : ℝ, 5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
        Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
        morreyVecMem 3 τ (Metric.ball z₀ R) u →
        (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
          (Metric.ball z₀ R) (fun z => Du z i)) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
            (volume.restrict (Metric.ball z₀ (R / 2)))) ∧
          (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (R / 2) →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          morreyVecMem (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
            (Metric.ball z₀ (R / 2)) Dp)
    (hB : ∀ q : ℝ, 5 / 2 < q →
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
        Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
        morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ R) u →
        (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
          (Metric.ball z₀ R) (fun z => Du z i)) →
        morreyVecMem 3 25 (Metric.ball z₀ (R / 4)) u)
    (hL : ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {φ : Vec3 × ℝ → ℝ}, φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
        ∀ {Ω' : Set Vec3} {J : Set ℝ}, localBox Ω I Ω' J →
        tsupport φ ⊆ Ω' ×ˢ J →
        ∀ {Dp : ParabolicPoint → Vec3},
        (∀ i, Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet Ω' J))) →
        (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
          ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
          tsupport ψ ⊆ Ω' ×ˢ J →
          (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
            -(∫ z : ParabolicPoint, Dp z i * ψ z)) →
        localizedVelocity φ u =ᵐ[volume]
          (fun z i => heatPotential
            (fun w => localizedGradientSourceG φ u Du f Dp w i)
            (fun j w => localizedGradientSourceH φ u j w i) z))
    (hS : ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {φ : Vec3 × ℝ → ℝ}, φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
        ∀ {Ω' : Set Vec3} {J : Set ℝ}, localBox Ω I Ω' J →
        tsupport φ ⊆ Ω' ×ˢ J →
        ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R → 5 / 2 < q →
        Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
        tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ R →
        morreyVecMem 3 25 (Metric.ball z₀ R) u →
        (∀ i, morreyVecMem 2 (25 / 8 : ℝ) (Metric.ball z₀ R) (fun z => Du z i)) →
        ∀ {Dp : ParabolicPoint → Vec3},
        (∀ i, AEMeasurable (fun z => Dp z i) (volume.restrict (Metric.ball z₀ R))) →
        morreyVecMem (6 / 5 : ℝ) (min q (25 / 9 : ℝ)) (Metric.ball z₀ R) Dp →
        (∀ i, AEMeasurable (fun z => localizedGradientSourceG φ u Du f Dp z i) volume) ∧
        (∀ j i, AEMeasurable (fun z => localizedGradientSourceH φ u j z i) volume) ∧
        (∀ i, HasCompactSupport (fun z => localizedGradientSourceG φ u Du f Dp z i)) ∧
        (∀ j i, HasCompactSupport (fun z => localizedGradientSourceH φ u j z i)) ∧
        (∀ i, morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
          (fun z => localizedGradientSourceG φ u Du f Dp z i) < ∞) ∧
        (∀ j i, morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
          (fun z => localizedGradientSourceH φ u j z i) < ∞))
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) (R : ℝ) (hR : 0 < R)
    (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I)
    (hu : morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ R) u)
    (hDu : ∀ i, morreyVecMem 2 (25 / 8 : ℝ) (Metric.ball z₀ R) (fun z => Du z i)) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (Metric.ball z₀ (R / 16 / 8))] u ∧
      ParabolicHolderVecOn (Metric.ball z₀ (R / 16 / 8)) w (stepGamma₀ q) := by
  have hU := hB q hq hsol z₀ R hR hdom hu hDu
  have hDquarter : ∀ i, morreyVecMem 2 (25 / 8 : ℝ)
      (Metric.ball z₀ (R / 4)) (fun z => Du z i) := fun i =>
    morreyVecMem_mono_set (by norm_num)
      (Metric.ball_subset_ball (by linarith only [hR])) (hDu i)
  obtain ⟨Dp, hDpAE, hDpweak, hDpN⟩ := hG q 25 hq (by norm_num)
    (by norm_num) hsol z₀ (R / 4) (by positivity)
    ((Metric.ball_subset_ball (by linarith only [hR])).trans hdom) hU hDquarter
  have hhalfquarter : R / 4 / 2 = R / 8 := by ring
  rw [hhalfquarter] at hDpAE hDpweak hDpN
  have hDpN' : morreyVecMem (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (Metric.ball z₀ (R / 8)) Dp := by
    norm_num only [show ((1 / (25 : ℝ) + 8 / 25)⁻¹) = 25 / 9 by norm_num] at hDpN
    simpa only [min_comm] using hDpN
  obtain ⟨φ, hφ, _hφrange, hφone, hφsupp, hbox, hφbox⟩ :=
    exists_localization_cutoff (r := R / 16) (by positivity)
      ((Metric.ball_subset_ball (by linarith only [hR])).trans hdom)
  have hboxsub : spaceTimeSet (vec3Ball z₀.1 (R / 16))
      (Ioo (z₀.2 - (R / 16) ^ 2) (z₀.2 + (R / 16) ^ 2)) ⊆
      Metric.ball z₀ (R / 8) :=
    localization_box_subset_ball.trans (Metric.ball_subset_ball (by linarith only [hR]))
  have hDpInt : ∀ i, Integrable (fun z => Dp z i)
      (volume.restrict (spaceTimeSet (vec3Ball z₀.1 (R / 16))
        (Ioo (z₀.2 - (R / 16) ^ 2) (z₀.2 + (R / 16) ^ 2)))) := by
    intro i
    exact (integrableOn_ball_of_morrey (by norm_num)
      (le_min (by linarith only [hq]) (by norm_num)) (by positivity)
      (hDpAE i) (hDpN' i)).mono_set hboxsub
  have hrep := hL hsol hφ hbox hφbox hDpInt (fun i ψ hψ hs =>
    hDpweak i ψ hψ (fun z hz => hboxsub (hs hz)))
  have hφcarrier : tsupport φ ⊆
      parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (R / 8) :=
    hφsupp.trans (preimage_mono (Metric.ball_subset_ball (by linarith only [hR])))
  obtain ⟨hF, hH, hFc, hHc, hFN, hHN⟩ :=
    hS hsol hφ hbox hφbox z₀ (R / 8) (by positivity) hq
      ((Metric.ball_subset_ball (by linarith only [hR])).trans hdom) hφcarrier
      (morreyVecMem_mono_set (by norm_num)
        (Metric.ball_subset_ball (by linarith only [hR])) hU)
      (fun i => morreyVecMem_mono_set (by norm_num)
        (Metric.ball_subset_ball (by linarith only [hR])) (hDu i))
      hDpAE hDpN'
  have hHs : ∀ j i, ∀ z ∉ parabolicCylinder z₀.1
      (z₀.2 + (R / 8) ^ 2) (2 * (R / 8)),
      localizedGradientSourceH φ u j z i = 0 := by
    intro j i z hz
    have hnot : (z.1, z.2) ∉ tsupport φ := fun hm =>
      hz (metricBall_subset_parabolicCylinder_doubled z₀ (by positivity) (hφcarrier hm))
    have hd := spatialPartial_zero_of_not_mem_tsupport_public hφ.1 hnot j
    change spatialPartial φ j z = 0 at hd
    simp only [localizedGradientSourceH, localizedEquationH, hd, mul_zero, zero_smul,
      Pi.zero_apply]
  obtain ⟨hFN', hHN'⟩ := source_norms_at_holder_exponents hq
    (z₀ := (z₀.1, z₀.2 + (R / 8) ^ 2)) (by positivity) hFN hHN hHs
  have hrepLocal : u =ᵐ[volume.restrict (Metric.ball z₀ (R / 16 / 8))]
      (fun z i => heatPotential
        (fun w => localizedGradientSourceG φ u Du f Dp w i)
        (fun j w => localizedGradientSourceH φ u j w i) z) := by
    filter_upwards [ae_restrict_of_ae hrep,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hzmem
    have hone := hφone z (Metric.ball_subset_closedBall hzmem)
    change φ z = 1 at hone
    simpa only [localizedVelocity, hone, one_smul] using hz
  obtain ⟨w, hw, hnorm, _⟩ := regular_point_of_heat_sources_at_step_parameters hq
    (by positivity) ((Metric.ball_subset_ball (by linarith only [hR])).trans hdom)
    hF hH hFN' hHN' hFc hHc hrepLocal
  exact ⟨w, hw, holder_on_of_norm hnorm⟩

/-- The explicit local analytic estimates imply regularity at the center. -/
theorem regular_point_of_local_producers
    (q : ℝ) (hq : 5 / 2 < q)
    (hG : ∀ q τ : ℝ, 5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
        Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
        morreyVecMem 3 τ (Metric.ball z₀ R) u →
        (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
          (Metric.ball z₀ R) (fun z => Du z i)) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i : Fin 3, AEMeasurable (fun z => Dp z i)
            (volume.restrict (Metric.ball z₀ (R / 2)))) ∧
          (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (R / 2) →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          morreyVecMem (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
            (Metric.ball z₀ (R / 2)) Dp)
    (hB : ∀ q : ℝ, 5 / 2 < q →
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R →
        Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
        morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ R) u →
        (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
          (Metric.ball z₀ R) (fun z => Du z i)) →
        morreyVecMem 3 25 (Metric.ball z₀ (R / 4)) u)
    (hL : ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {φ : Vec3 × ℝ → ℝ}, φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
        ∀ {Ω' : Set Vec3} {J : Set ℝ}, localBox Ω I Ω' J →
        tsupport φ ⊆ Ω' ×ˢ J →
        ∀ {Dp : ParabolicPoint → Vec3},
        (∀ i, Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet Ω' J))) →
        (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
          ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
          tsupport ψ ⊆ Ω' ×ˢ J →
          (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
            -(∫ z : ParabolicPoint, Dp z i * ψ z)) →
        localizedVelocity φ u =ᵐ[volume]
          (fun z i => heatPotential
            (fun w => localizedGradientSourceG φ u Du f Dp w i)
            (fun j w => localizedGradientSourceH φ u j w i) z))
    (hS : ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {φ : Vec3 × ℝ → ℝ}, φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
        ∀ {Ω' : Set Vec3} {J : Set ℝ}, localBox Ω I Ω' J →
        tsupport φ ⊆ Ω' ×ˢ J →
        ∀ (z₀ : ParabolicPoint) (R : ℝ), 0 < R → 5 / 2 < q →
        Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I →
        tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ R →
        morreyVecMem 3 25 (Metric.ball z₀ R) u →
        (∀ i, morreyVecMem 2 (25 / 8 : ℝ) (Metric.ball z₀ R) (fun z => Du z i)) →
        ∀ {Dp : ParabolicPoint → Vec3},
        (∀ i, AEMeasurable (fun z => Dp z i) (volume.restrict (Metric.ball z₀ R))) →
        morreyVecMem (6 / 5 : ℝ) (min q (25 / 9 : ℝ)) (Metric.ball z₀ R) Dp →
        (∀ i, AEMeasurable (fun z => localizedGradientSourceG φ u Du f Dp z i) volume) ∧
        (∀ j i, AEMeasurable (fun z => localizedGradientSourceH φ u j z i) volume) ∧
        (∀ i, HasCompactSupport (fun z => localizedGradientSourceG φ u Du f Dp z i)) ∧
        (∀ j i, HasCompactSupport (fun z => localizedGradientSourceH φ u j z i)) ∧
        (∀ i, morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
          (fun z => localizedGradientSourceG φ u Du f Dp z i) < ∞) ∧
        (∀ j i, morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
          (fun z => localizedGradientSourceH φ u j z i) < ∞))
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) (R : ℝ) (hR : 0 < R)
    (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I)
    (hu : morreyVecMem 3 (25 / 3 : ℝ) (Metric.ball z₀ R) u)
    (hDu : ∀ i, morreyVecMem 2 (25 / 8 : ℝ) (Metric.ball z₀ R) (fun z => Du z i)) :
    IsRegularPoint Ω I u z₀ := by
  obtain ⟨w, hw, hholder⟩ := holder_representative_of_local_producers
    q hq hG hB hL hS hsol z₀ R hR hdom hu hDu
  exact regular_point_of_holder_on_open Metric.isOpen_ball (Metric.mem_ball_self (by positivity))
    ((Metric.ball_subset_ball (by linarith only [hR])).trans hdom)
    (stepGamma₀_pos hq) (stepGamma₀_lt_one q).le hw hholder


end CKN.Core.Endgame
