/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicPartBoundsAE

/-! # Interior regularity of the harmonic pressure part on a slice

The harmonic summand `p₂ + p₃ + p₄ + p₅ + p₆` of the local pressure
decomposition `eq:pk` is a Newtonian potential whose density is carried by the
cutoff annulus `B_{3ρ/4}(x₀) \ B_{13ρ/20}(x₀)`.  On the inner ball
`B_{ρ/2}(x₀)` the kernel is therefore smooth in the evaluation point, and the
potential inherits every finite order of differentiability (`eq:har-Ck`).

This file records the order-one consequence in the almost-every-time form that
display (3.5) of the pressure-gradient section consumes: for a suitable weak
solution and almost every time of the one-sided interval `J_ρ`, the harmonic
pressure part is `C¹` on `B_{ρ/2}(x₀)`, so its weak gradient there is its
classical gradient.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

private lemma euclideanBall_eq_vec3Ball_regularity {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change (x ∈ euclideanBall x₀ r) ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

/-- The five annular potentials of the local pressure decomposition are each
`C¹` on the inner ball, hence so is their sum. -/
theorem contDiffOn_harmonicPressurePart_of_terms
    {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {p : ParabolicPoint → ℝ} {s : ℝ} {B : Set Vec3}
    (h2 : ContDiffOn ℝ (1 : ℕ∞) (pressureP2 η u c s) B)
    (h3 : ContDiffOn ℝ (1 : ℕ∞) (pressureP3 η u c s) B)
    (h4 : ContDiffOn ℝ (1 : ℕ∞) (pressureP4 η u c s) B)
    (h5 : ContDiffOn ℝ (1 : ℕ∞) (pressureP5 η p s) B)
    (h6 : ContDiffOn ℝ (1 : ℕ∞) (pressureP6 η p s) B) :
    ContDiffOn ℝ (1 : ℕ∞) (harmonicPressurePart η u c p s) B := by
  show ContDiffOn ℝ (1 : ℕ∞) (fun x => pressureP2 η u c s x + pressureP3 η u c s x +
    pressureP4 η u c s x + pressureP5 η p s x + pressureP6 η p s x) B
  exact (((h2.add h3).add h4).add h5).add h6

/-- Almost every slice of the harmonic pressure part of a suitable weak
solution is `C¹` on the inner ball `B_{ρ/2}(x₀)`.  This is `eq:har-Ck` at
order one, in the shape display (3.5) consumes. -/
theorem slice_harmonic_part_contDiffOn_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ContDiffOn ℝ (1 : ℕ∞)
        (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p s)
        (euclideanBall z.1 (ρ / 2)) := by
  classical
  obtain ⟨_cN, _cD, _κ, _hcN, _hcD, _hκ, hterm⟩ :=
    harmonicPressurePart_term_bounds 1
  set c : ℝ → Vec3 := fun t j =>
    average (volume.restrict (vec3Ball z.1 ρ)) (fun y : Vec3 => u (y, t) j) with hc
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hslices := ae_restrict_of_ae_restrict_of_subset htime
    (slice_memLp_ae_of_sws hsol hbox)
  have hdata := pressure_harmonic_potential_data_ae_of_sws_inner hsol hρ hsub
  have hp := sws_pressure_memLp_slice_ae hsol hρ hsub
  have hinner : euclideanBall z.1 (ρ / 2) = vec3Ball z.1 (ρ / 2) :=
    euclideanBall_eq_vec3Ball_regularity (by positivity)
  have hcentre : z.1 ∈ vec3Ball z.1 (ρ / 2) := by
    rw [mem_vec3Ball]
    simpa [vec3EuclideanNorm_zero] using (by positivity : (0 : ℝ) < ρ / 2)
  filter_upwards [hslices, hdata, hp] with s hs hdat hps
  -- the slice data required by the annular potential bounds
  have hu : MemLp (fun y : Vec3 => u (y, s)) 2
      (volume.restrict (vec3Ball z.1 ρ)) :=
    hs.1.mono_measure (Measure.restrict_mono_set volume hball)
  have humeas : AEMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball z.1 ρ)) := hu.aestronglyMeasurable.aemeasurable
  have hUint : Integrable (pressureUTensorNorm u c s)
      (volume.restrict (vec3Ball z.1 ρ)) :=
    pressure_utensor_integrable_on_ball (c := c) hρ humeas hu
  have hfin : IsFiniteMeasure (volume.restrict (vec3Ball z.1 ρ)) := by
    refine ⟨?_⟩
    simpa only [Measure.restrict_apply_univ] using
      (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top
        (x := z.1) (r := ρ))
  have hpInt : Integrable (fun y : Vec3 => |p (y, s)|)
      (volume.restrict (vec3Ball z.1 ρ)) := (hps.integrable (by norm_num)).norm
  have hdat' : PressureHarmonicPotentialData
      (vec3Ball z.1 (13 * ρ / 20)) (mollifiedBallCutoff z.1 hρ) u c p s := by
    have heq : euclideanBall z.1 (13 * ρ / 20) = vec3Ball z.1 (13 * ρ / 20) :=
      euclideanBall_eq_vec3Ball_regularity (by positivity)
    rw [heq] at hdat
    simpa [hc] using hdat
  -- the normalizing constants of the annular bounds, chosen so that the two
  -- size hypotheses hold by construction
  set A : ℝ := (∫ y in vec3Ball z.1 ρ, pressureUTensorNorm u c s y) / (2 * ρ)
    with hA
  set B : ℝ := (∫ y in vec3Ball z.1 ρ, |p (y, s)|) /
    ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ) with hB
  have hUnonneg : 0 ≤ ∫ y in vec3Ball z.1 ρ, pressureUTensorNorm u c s y :=
    integral_nonneg_of_ae (Eventually.of_forall fun y => Real.sqrt_nonneg _)
  have hPnonneg : 0 ≤ ∫ y in vec3Ball z.1 ρ, |p (y, s)| :=
    integral_nonneg_of_ae (Eventually.of_forall fun y => abs_nonneg _)
  have hAnonneg : 0 ≤ A := by
    rw [hA]
    exact div_nonneg hUnonneg (by positivity)
  have hBnonneg : 0 ≤ B := by
    rw [hB]
    exact div_nonneg hPnonneg (by positivity)
  have hUbound : (∫ y in vec3Ball z.1 ρ, pressureUTensorNorm u c s y) ≤
      2 * ρ * A := by
    rw [hA, mul_div_cancel₀ _ (by positivity : (2 : ℝ) * ρ ≠ 0)]
  have hPbound : (∫ y in vec3Ball z.1 ρ, |p (y, s)|) ≤
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ * B := by
    rw [hB, mul_div_cancel₀ _
      (by positivity : (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ≠ 0)]
  have hzero : ∀ y, y ∉ pressureAnnulus z.1 ρ →
      (∀ i, spatialDeriv (mollifiedBallCutoff z.1 hρ) i y = 0) ∧
        (∀ i j, mixedSecond (mollifiedBallCutoff z.1 hρ) i j y = 0) ∧
        spatialLaplacian (mollifiedBallCutoff z.1 hρ) y = 0 := by
    intro y hy
    have houter : euclideanBall z.1 (3 * ρ / 4) = vec3Ball z.1 (3 * ρ / 4) :=
      euclideanBall_eq_vec3Ball_regularity (by positivity)
    have hin : euclideanBall z.1 (13 * ρ / 20) = vec3Ball z.1 (13 * ρ / 20) :=
      euclideanBall_eq_vec3Ball_regularity (by positivity)
    have hyann : y ∉ euclideanBall z.1 (3 * ρ / 4) \
        euclideanClosedBall z.1 (13 * ρ / 20) := by
      intro hyann
      refine hy ⟨by rw [← houter]; exact hyann.1, fun hyinner => hyann.2 ?_⟩
      refine (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2 ?_
      have hyinner' : y ∈ euclideanBall z.1 (13 * ρ / 20) := by
        rw [hin]; exact hyinner
      exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1
        hyinner').le
    have hzz := pressure_cutoff_derivatives_vanish z.1 hρ hyann
    refine ⟨hzz.1, hzz.2, ?_⟩
    simp only [spatialLaplacian]
    exact Finset.sum_eq_zero fun i _ => hzz.2 i i
  have hpoint := hterm (η := mollifiedBallCutoff z.1 hρ) (u := u) (c := c)
    (p := p) (s := s) (x₀ := z.1) (ρ := ρ) hρ hdat' rfl hzero hUint hpInt
    A B hAnonneg hBnonneg hUbound hPbound z.1 hcentre
  have hone : ((1 : ℕ) : WithTop ℕ∞) = ((1 : ℕ∞) : WithTop ℕ∞) := by norm_cast
  rw [hinner]
  refine contDiffOn_harmonicPressurePart_of_terms ?_ ?_ ?_ ?_ ?_
  · exact hone ▸ hpoint.1
  · exact hone ▸ hpoint.2.1
  · exact hone ▸ hpoint.2.2.1
  · exact hone ▸ hpoint.2.2.2.1
  · exact hone ▸ hpoint.2.2.2.2.1

end CKN.Core.Step4
