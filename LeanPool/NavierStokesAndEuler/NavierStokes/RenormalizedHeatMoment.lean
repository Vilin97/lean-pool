/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricHeatTail
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricRephase
public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityProfile
public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingDilation
public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatedOutgoing
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# The renormalized angular moment and physical axial viscosity

The nonintegrable reference power is independent of physical axial position.
It is subtracted before integration. Local constancy of the exterior heat
carrier supplies compact support for every axial derivative of the difference.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.RenormalizedHeatMoment

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

/-! ## Smooth integrals of locally uniformly supported differences -/

noncomputable def parameterJet (F : ℝ × ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  iteratedDeriv n (fun z => F (z, p.2)) p.1

theorem parameterJet_continuous {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    Continuous (parameterJet F n) := by
  have hj : ContDiff ℝ ∞ (ParametricRephase.parameterJet F n) := by
    simpa only [univ_prod_univ, contDiffOn_univ] using
      ParametricRephase.parameterJet_contDiffOn F univ isOpen_univ hF.contDiffOn n
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin n) ℝ).symm.continuous.comp hj.continuous

theorem iteratedDeriv_zero_function (n : ℕ) :
    iteratedDeriv n (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact deriv_const x 0

/-- Only the positive integration half-line needs a common support radius. -/
def LocallyUniformSupport (F : ℝ × ℝ → ℝ) : Prop :=
  ∀ z : ℝ, ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
    ∀ y ∈ Metric.ball z ε, ∀ r : ℝ, B ≤ r → F (y, r) = 0

theorem parameterJet_zero_of_support {F : ℝ × ℝ → ℝ} {z ε B y r : ℝ}
    (hs : ∀ x ∈ Metric.ball z ε, ∀ r : ℝ, B ≤ r → F (x, r) = 0)
    (hy : y ∈ Metric.ball z ε) (hr : B ≤ r) (n : ℕ) : parameterJet F n (y, r) = 0 := by
  have he : (fun x => F (x, r)) =ᶠ[𝓝 y] (fun _ => 0) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with x hx
    exact hs x hx r hr
  simpa only [parameterJet, iteratedDeriv_zero_function] using he.iteratedDeriv_eq n

theorem supported_locally_dominated {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : LocallyUniformSupport F) :
    SmoothParameterIntegral.LocallyDominatedDeriv (fun z r => F (z, r))
      (volume.restrict (Ioi 0)) := by
  intro n z
  obtain ⟨ε, B, hε, hB, hsupport⟩ := hs z
  have hc : IsCompact (Metric.closedBall z (ε / 2) ×ˢ Icc (0 : ℝ) B) :=
    (isCompact_closedBall z (ε / 2)).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (parameterJet_continuous hF n).continuousOn
  let bound : ℝ → ℝ := (Icc (0 : ℝ) B).indicator (fun _ => max C 0)
  have hb : Integrable bound (volume.restrict (Ioi 0)) := by
    have hc : IntegrableOn (fun _ : ℝ => max C 0) (Icc (0 : ℝ) B) :=
      continuous_const.integrableOn_Icc
    exact (hc.integrable_indicator measurableSet_Icc).restrict
  refine ⟨ε / 2, by linarith, bound, hb, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  intro y hy
  by_cases hrB : r ≤ B
  · have hp : r ∈ Icc (0 : ℝ) B := ⟨hr.le, hrB⟩
    rw [show bound r = max C 0 by exact indicator_of_mem hp _]
    exact (hC (y, r) ⟨Metric.ball_subset_closedBall hy, hp⟩).trans (le_max_left _ _)
  · have hy' : y ∈ Metric.ball z ε := Metric.ball_subset_ball (by linarith) hy
    have hj := parameterJet_zero_of_support hsupport hy' (le_of_not_ge hrB) n
    change ‖parameterJet F n (y, r)‖ ≤ bound r
    rw [hj, norm_zero]
    exact indicator_nonneg (fun _ _ => le_max_right C 0) r

theorem parameterJet_measurable {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ) (z : ℝ) :
    AEStronglyMeasurable (fun r => parameterJet F n (z, r)) (volume.restrict (Ioi 0)) :=
  ((parameterJet_continuous hF n).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

theorem parameterJet_integrable {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : LocallyUniformSupport F) (n : ℕ) (z : ℝ) :
    IntegrableOn (fun r => parameterJet F n (z, r)) (Ioi 0) := by
  obtain ⟨ε, hε, b, hb, hbound⟩ := supported_locally_dominated hF hs n z
  exact hb.mono' (parameterJet_measurable hF n z)
    (hbound.mono fun r hr => hr z (Metric.mem_ball_self hε))

theorem iteratedDeriv_integral_supported {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : LocallyUniformSupport F) (n : ℕ) (z : ℝ) :
    iteratedDeriv n (fun y => ∫ r in Ioi (0 : ℝ), F (y, r)) z =
      ∫ r in Ioi (0 : ℝ), parameterJet F n (z, r) := by
  exact SmoothParameterIntegral.iteratedDeriv_integral
    (Eventually.of_forall fun r => hF.comp (contDiff_id.prodMk contDiff_const))
    (parameterJet_measurable hF) (supported_locally_dominated hF hs) n z

noncomputable def centered (u : ℝ × ℝ → ℝ) (z0 : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.2 ^ 2 * (u p - u (z0, p.2))

noncomputable def renormalizedMoment (u : ℝ × ℝ → ℝ) (reference : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), r ^ 2 * (u (z, r) - reference r)

theorem centered_contDiff {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (z0 : ℝ) :
    ContDiff ℝ ∞ (centered u z0) :=
  (contDiff_snd.pow 2).mul (hu.sub (hu.comp (contDiff_const.prodMk contDiff_snd)))

/-- A locally common exterior carrier is independent of the axial parameter. -/
def CommonExterior (u : ℝ × ℝ → ℝ) (tail : ℝ → ℝ) : Prop :=
  ∀ z : ℝ, ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
    ∀ y ∈ Metric.ball z ε, ∀ r : ℝ, B ≤ r → u (y, r) = tail r

theorem centered_support {u : ℝ × ℝ → ℝ} {tail : ℝ → ℝ}
    (he : CommonExterior u tail) (z0 : ℝ) : LocallyUniformSupport (centered u z0) := by
  obtain ⟨ε0, B0, hε0, hB0, he0⟩ := he z0
  intro z
  obtain ⟨ε, B, hε, hB, hz⟩ := he z
  refine ⟨ε, max B B0, hε, hB.trans_le (le_max_left _ _), ?_⟩
  intro y hy r hr
  simp only [centered, hz y hy r ((le_max_left _ _).trans hr),
    he0 z0 (Metric.mem_ball_self hε0) r ((le_max_right _ _).trans hr), sub_self, mul_zero]

theorem centered_jet {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (z0 : ℝ)
    (n : ℕ) (hn : 0 < n) (z r : ℝ) :
    parameterJet (centered u z0) n (z, r) =
      r ^ 2 * iteratedDeriv n (fun y => u (y, r)) z := by
  have hc : ContDiff ℝ ∞ (fun y => u (y, r)) := hu.comp (contDiff_id.prodMk contDiff_const)
  change iteratedDeriv n (fun y => r ^ 2 * (u (y, r) - u (z0, r))) z = _
  rw [iteratedDeriv_const_mul _ ((hc.sub contDiff_const).contDiffAt.of_le (nat_le_infty n))]
  congr 1
  have he : (fun y => u (y, r) - u (z0, r)) = fun y => -u (z0, r) + u (y, r) := by
    funext y
    ring
  rw [he, iteratedDeriv_const_add hn]

/-- Differentiation of the actual renormalized improper moment. The tail is
subtracted before integration, and all positive-order integrands are proved
integrable by local compact support. -/
theorem renormalized_moment_derivative {u : ℝ × ℝ → ℝ} {reference tail : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (he : CommonExterior u tail)
    (hi : ∀ z, IntegrableOn (fun r => r ^ 2 * (u (z, r) - reference r)) (Ioi 0))
    (n : ℕ) (hn : 0 < n) (z : ℝ) :
    IntegrableOn (fun r => r ^ 2 * iteratedDeriv n (fun y => u (y, r)) z) (Ioi 0) ∧
      iteratedDeriv n (renormalizedMoment u reference) z =
        ∫ r in Ioi (0 : ℝ), r ^ 2 * iteratedDeriv n (fun y => u (y, r)) z := by
  have hc := centered_contDiff hu (0 : ℝ)
  have hs := centered_support he (0 : ℝ)
  have hj : (fun r => parameterJet (centered u 0) n (z, r)) =
      (fun r => r ^ 2 * iteratedDeriv n (fun y => u (y, r)) z) :=
    funext fun r => centered_jet hu 0 n hn z r
  refine ⟨by rw [← hj]; exact parameterJet_integrable hc hs n z, ?_⟩
  have hm : renormalizedMoment u reference = fun y =>
      renormalizedMoment u reference 0 + ∫ r in Ioi (0 : ℝ), centered u 0 (y, r) := by
    funext y
    have hdiff : (fun r => centered u 0 (y, r)) = fun r =>
        r ^ 2 * (u (y, r) - reference r) - r ^ 2 * (u (0, r) - reference r) := by
      funext r
      unfold centered
      ring
    rw [hdiff, integral_sub (hi y) (hi 0)]
    unfold renormalizedMoment
    ring
  rw [hm, iteratedDeriv_const_add hn,
    iteratedDeriv_integral_supported hc hs n z, hj]

theorem axial_viscosity_moment_zero {u : ℝ × ℝ → ℝ} {reference tail : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (he : CommonExterior u tail)
    (hi : ∀ z, IntegrableOn (fun r => r ^ 2 * (u (z, r) - reference r)) (Ioi 0))
    (hm : ∀ z, renormalizedMoment u reference z = 0) (z : ℝ) :
    IntegrableOn (fun r => r ^ 2 * iteratedDeriv 2 (fun y => u (y, r)) z) (Ioi 0) ∧
      (∫ r in Ioi (0 : ℝ), r ^ 2 * iteratedDeriv 2 (fun y => u (y, r)) z) = 0 := by
  obtain ⟨hI, hd⟩ := renormalized_moment_derivative hu he hi 2 (by norm_num) z
  refine ⟨hI, hd.symm.trans ?_⟩
  rw [show renormalizedMoment u reference = (fun _ => 0) from funext hm,
    iteratedDeriv_zero_function]

/-! ## The actual implicit physical coordinates -/

noncomputable def A (h : ℝ) : ℝ := 1 / 2 + h
noncomputable def Q (h τ z : ℝ) : ℝ := SimilarityCoordinates.coordinateQ (2 * h) (τ, z)
noncomputable def eta (h τ z : ℝ) : ℝ := SimilarityCoordinates.coordinateEta (2 * h) (τ, z)

noncomputable def referencePower (h C r : ℝ) : ℝ := C * (r ^ 2 / 2) ^ (-A h)

noncomputable def heatCarrier (h C τ r : ℝ) : ℝ :=
  C * RadialHeatProfile.radialProfile (1 + h) τ r

/-- `F` is the signed radial angular profile, with parameter second. -/
noncomputable def velocity (h τ : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Q h τ p.1 ^ (-A h) * F (p.2 / Real.sqrt (Q h τ p.1), eta h τ p.1)

theorem Q_pos {h τ : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hτ : 0 < τ) (z : ℝ) :
    0 < Q h τ z :=
  (SimilarityCoordinates.coordinateQ_spec (by linarith) (by linarith) (p := (τ, z)) hτ).1

theorem Q_implicit {h τ : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hτ : 0 < τ) (z : ℝ) :
    Q h τ z - z ^ 2 * Q h τ z ^ (2 * h) = τ :=
  (SimilarityCoordinates.coordinateQ_spec (by linarith) (by linarith) (p := (τ, z)) hτ).2

theorem eta_mem {h τ : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hτ : 0 < τ) (z : ℝ) :
    eta h τ z ∈ Ioo (-1 : ℝ) 1 :=
  abs_lt.mp (SimilarityCoordinates.coordinateEta_abs_lt_one
    (by linarith) (by linarith) (p := (τ, z)) hτ)

theorem diffusion_identity {h τ : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hτ : 0 < τ) (z : ℝ) : 1 - eta h τ z ^ 2 = τ / Q h τ z := by
  have he := SimilarityCoordinates.tau_coordinate_identity
    (by linarith : 0 < 2 * h) (by linarith : 2 * h < 1) (p := (τ, z)) hτ
  apply (eq_div_iff (Q_pos hh hh1 hτ z).ne').mpr
  simpa only [Q, eta, mul_comm] using he.symm

/-- Every interior profile parameter is realized at a physical point with
`q=1`, namely `t=eta^2` and `z=eta`. -/
theorem normalized_coordinates {h e : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (he : e ∈ Ioo (-1 : ℝ) 1) :
    e ^ 2 < 1 ∧ Q h (1 - e ^ 2) e = 1 ∧ eta h (1 - e ^ 2) e = e := by
  have hτ : 0 < 1 - e ^ 2 := by
    have hp := mul_pos (show 0 < 1 - e by linarith [he.2])
      (show 0 < 1 + e by linarith [he.1])
    nlinarith
  have hq : Q h (1 - e ^ 2) e = 1 :=
    (SimilarityCoordinates.eq_coordinateQ (by linarith : 0 < 2 * h)
      (by linarith : 2 * h < 1) (p := (1 - e ^ 2, e)) hτ zero_lt_one
      (by simp [SimilarityCoordinates.forwardScalar])).symm
  refine ⟨by linarith, hq, ?_⟩
  change e / Q h (1 - e ^ 2) e ^ ((1 - 2 * h) / 2) = e
  rw [hq, Real.one_rpow, div_one]

theorem Q_contDiff {h τ : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hτ : 0 < τ) :
    ContDiff ℝ ∞ (Q h τ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (SimilarityCoordinates.coordinateQ_smooth (by linarith) (by linarith)
    (p := (τ, z)) hτ).comp z (contDiffAt_const.prodMk contDiffAt_id)

theorem eta_contDiff {h τ : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hτ : 0 < τ) :
    ContDiff ℝ ∞ (eta h τ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (SimilarityCoordinates.coordinateEta_smooth (by linarith) (by linarith)
    (p := (τ, z)) hτ).comp z (contDiffAt_const.prodMk contDiffAt_id)

theorem velocity_contDiff {h τ : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hτ : 0 < τ)
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ioo (-1 : ℝ) 1)) :
    ContDiff ℝ ∞ (velocity h τ F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hq := ((Q_contDiff hh hh1 hτ).comp contDiff_fst).contDiffAt (x := p)
  have hη := ((eta_contDiff hh hh1 hτ).comp contDiff_fst).contDiffAt (x := p)
  have hR : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => p.2 / Real.sqrt (Q h τ p.1)) p :=
    contDiffAt_snd.div (hq.sqrt (Q_pos hh hh1 hτ p.1).ne')
      (Real.sqrt_pos.mpr (Q_pos hh hh1 hτ p.1)).ne'
  exact (hq.rpow_const_of_ne (Q_pos hh hh1 hτ p.1).ne').mul
    ((hF.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      ⟨mem_univ _, eta_mem hh hh1 hτ p.1⟩)).comp p (hR.prodMk hη))

theorem referencePower_scaling (h C : ℝ) {q : ℝ} (hq : 0 < q) (r : ℝ) :
    q ^ (-A h) * referencePower h C (r / Real.sqrt q) = referencePower h C r := by
  have hp : (r / Real.sqrt q) ^ 2 / 2 = (r ^ 2 / 2) / q := by
    rw [div_pow, Real.sq_sqrt hq.le]
    ring
  rw [referencePower, referencePower, hp,
    Real.div_rpow (by positivity) hq.le]
  field_simp [(Real.rpow_pos_of_pos hq (-A h)).ne']

theorem heatCarrier_scaling (h C : ℝ) {q τ ν r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hν : ν = τ / q) :
    q ^ (-A h) * heatCarrier h C ν (r / Real.sqrt q) = heatCarrier h C τ r := by
  have hp : (r / Real.sqrt q) ^ 2 / 2 = (r ^ 2 / 2) / q := by
    rw [div_pow, Real.sq_sqrt hq.le]
    ring
  have hexp : RadialHeatProfile.spatialExponent (1 + h) = -A h := by
    unfold RadialHeatProfile.spatialExponent A
    ring
  have hs : 0 < r ^ 2 / 2 := by positivity
  simp only [heatCarrier, RadialHeatProfile.radialProfile,
    RadialHeatProfile.spatialProfile, hexp, hp, hν,
    ParametricHeatTail.heat_ratio_physical hq hs]
  rw [Real.div_rpow hs.le hq.le]
  field_simp [(Real.rpow_pos_of_pos hq (-A h)).ne']

theorem velocity_commonExterior {h τ C B : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hτ : 0 < τ) (hB : 0 < B)
    {F : ℝ × ℝ → ℝ}
    (he : ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ R : ℝ, B ≤ R →
      F (R, eta) = heatCarrier h C (1 - eta ^ 2) R) :
    CommonExterior (velocity h τ F) (heatCarrier h C τ) := by
  intro z
  let Bz := B * Real.sqrt (Q h τ z) + 1
  have hBz : 0 < Bz := by dsimp [Bz]; positivity
  have hc : Continuous (fun y => B * Real.sqrt (Q h τ y)) :=
    continuous_const.mul (Real.continuous_sqrt.comp (Q_contDiff hh hh1 hτ).continuous)
  have hev : ∀ᶠ y in 𝓝 z, B * Real.sqrt (Q h τ y) < Bz :=
    hc.continuousAt.eventually (gt_mem_nhds (by dsimp [Bz]; linarith))
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ε, Bz, hε, hBz, ?_⟩
  intro y hy r hr
  have hq := Q_pos hh hh1 hτ y
  have hR : B ≤ r / Real.sqrt (Q h τ y) := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hq)).mpr
    exact (hεs hy).le.trans hr
  rw [velocity, he _ (eta_mem hh hh1 hτ y) _ hR]
  exact heatCarrier_scaling h C hq (hBz.trans_le hr) (diffusion_identity hh hh1 hτ y)

noncomputable def radialDifference (h C : ℝ) (F : ℝ × ℝ → ℝ) (eta r : ℝ) : ℝ :=
  r ^ 2 * (F (r, eta) - referencePower h C r)

noncomputable def profileMoment (h C : ℝ) (F : ℝ × ℝ → ℝ) (eta : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), radialDifference h C F eta r

theorem physical_difference_scaling {h τ : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hτ : 0 < τ) (C : ℝ) (F : ℝ × ℝ → ℝ) (z r : ℝ) :
    r ^ 2 * (velocity h τ F (z, r) - referencePower h C r) =
      (Q h τ z * Q h τ z ^ (-A h)) *
        radialDifference h C F (eta h τ z) (r / Real.sqrt (Q h τ z)) := by
  have hq := Q_pos hh hh1 hτ z
  rw [← referencePower_scaling h C hq r]
  simp only [velocity, radialDifference, div_pow, Real.sq_sqrt hq.le]
  field_simp [hq.ne']

theorem profileMoment_integrable_physical {h τ C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hτ : 0 < τ) {F : ℝ × ℝ → ℝ}
    (hi : ∀ eta ∈ Ioo (-1 : ℝ) 1, IntegrableOn (radialDifference h C F eta) (Ioi 0))
    (z : ℝ) :
    IntegrableOn (fun r => r ^ 2 * (velocity h τ F (z, r) - referencePower h C r)) (Ioi 0) := by
  have hq := Q_pos hh hh1 hτ z
  have hc : IntegrableOn (fun r => radialDifference h C F (eta h τ z)
      (r / Real.sqrt (Q h τ z))) (Ioi 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using
      (integrableOn_Ioi_comp_mul_right_iff (radialDifference h C F (eta h τ z)) 0
        (inv_pos.mpr (Real.sqrt_pos.mpr hq))).mpr (by simpa only [zero_mul] using hi _ (eta_mem hh
          hh1 hτ z))
  apply (hc.const_mul (Q h τ z * Q h τ z ^ (-A h))).congr
  filter_upwards with r
  exact (physical_difference_scaling hh hh1 hτ C F z r).symm

theorem physical_moment_scaling {h τ : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hτ : 0 < τ) (C : ℝ) (F : ℝ × ℝ → ℝ) (z : ℝ) :
    renormalizedMoment (velocity h τ F) (referencePower h C) z =
      Q h τ z ^ (1 - h) * profileMoment h C F (eta h τ z) := by
  have hq := Q_pos hh hh1 hτ z
  have he : (fun r => r ^ 2 * (velocity h τ F (z, r) - referencePower h C r)) =
      (fun r => (Q h τ z * Q h τ z ^ (-A h)) *
        radialDifference h C F (eta h τ z) (r / Real.sqrt (Q h τ z))) :=
    funext (physical_difference_scaling hh hh1 hτ C F z)
  rw [renormalizedMoment, he, integral_const_mul]
  have hscale := integral_comp_mul_right_Ioi (radialDifference h C F (eta h τ z)) 0
    (inv_pos.mpr (Real.sqrt_pos.mpr hq))
  simp only [inv_inv, smul_eq_mul, ← div_eq_mul_inv, zero_div] at hscale
  rw [hscale]
  have hp : Q h τ z * Q h τ z ^ (-A h) * Real.sqrt (Q h τ z) = Q h τ z ^ (1 - h) := by
    calc
      _ = Q h τ z ^ (1 : ℝ) * Q h τ z ^ (-A h) * Q h τ z ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = Q h τ z ^ ((1 + -A h) + 1 / 2) := by rw [Real.rpow_add hq, Real.rpow_add hq]
      _ = _ := by congr 1; unfold A; ring
  rw [← mul_assoc, hp]
  rfl

/-! ## Integrability at the axis and at infinity -/

theorem weighted_referencePower (h C : ℝ) {r : ℝ} (hr : 0 < r) :
    r ^ 2 * referencePower h C r = C * (2 : ℝ) ^ A h * r ^ (1 - 2 * h) := by
  unfold referencePower
  rw [Real.div_rpow (sq_nonneg r) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    div_inv_eq_mul, ← Real.rpow_natCast_mul hr.le]
  calc
    _ = C * (2 : ℝ) ^ A h * (r ^ (2 : ℝ) * r ^ ((2 : ℕ) * -A h)) := by
      rw [Real.rpow_two]
      ring
    _ = _ := by
      rw [← Real.rpow_add hr]
      congr 2
      unfold A
      norm_num
      ring

theorem weighted_referencePower_nonneg_radius {h : ℝ} (hh1 : h < 1 / 2)
    (C : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ 2 * referencePower h C r = C * (2 : ℝ) ^ A h * r ^ (1 - 2 * h) := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp [referencePower, Real.zero_rpow (by linarith : 1 - 2 * h ≠ 0)]
  · exact weighted_referencePower h C hr

theorem radialDifference_continuousOn {h C : ℝ} {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ioo (-1 : ℝ) 1)) {eta : ℝ}
    (hη : eta ∈ Ioo (-1 : ℝ) 1) :
    ContinuousOn (radialDifference h C F eta) (Ioi 0) := by
  have hf : Continuous (fun r => F (r, eta)) := by
    exact hF.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
      (fun _ => ⟨mem_univ _, hη⟩)
  intro r hr
  have hrp : 0 < r := hr
  have hp : ContinuousAt (referencePower h C) r :=
    continuousAt_const.mul (((continuousAt_id.pow 2).div_const 2).rpow_const
      (Or.inl (by positivity : r ^ 2 / 2 ≠ 0)))
  exact ((continuousAt_id.pow 2).mul (hf.continuousAt.sub hp)).continuousWithinAt

theorem radialDifference_integrable_near_axis {h C B : ℝ} (hh1 : h < 1 / 2)
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ioo (-1 : ℝ) 1))
    {eta : ℝ} (hη : eta ∈ Ioo (-1 : ℝ) 1) :
    IntegrableOn (radialDifference h C F eta) (Icc 0 B) := by
  have hf : Continuous (fun r => F (r, eta)) :=
    hF.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
      (fun _ => ⟨mem_univ _, hη⟩)
  have hp : ContinuousOn (fun r : ℝ => C * (2 : ℝ) ^ A h * r ^ (1 - 2 * h)) (Icc 0 B) :=
    continuousOn_const.mul (continuousOn_id.rpow_const (fun _ _ => Or.inr (by linarith)))
  have hc : IntegrableOn
      (fun r : ℝ => r ^ 2 * F (r, eta) - C * (2 : ℝ) ^ A h * r ^ (1 - 2 * h)) (Icc 0 B) :=
    (((continuous_id.pow 2).mul hf).continuousOn.sub hp).integrableOn_Icc
  apply hc.congr_fun _ measurableSet_Icc
  intro r hr
  change r ^ 2 * F (r, eta) - C * (2 : ℝ) ^ A h * r ^ (1 - 2 * h) = _
  rw [← weighted_referencePower_nonneg_radius hh1 C hr.1]
  unfold radialDifference
  ring

theorem weighted_heat_difference_bound {h ν r : ℝ} (hh : 0 < h) (hν : ν ∈ Icc (0 : ℝ) 1)
    (hr : 0 < r) (C : ℝ) :
    |r ^ 2 * (heatCarrier h C ν r - referencePower h C r)| ≤
      (4 * |C| * (2 : ℝ) ^ A h * h * (1 + h)) * r ^ (-1 - 2 * h) := by
  have hs : 0 < r ^ 2 / 2 := by positivity
  have hν0 : 0 ≤ ν := hν.1
  have hz : 0 ≤ 2 * ν / (r ^ 2 / 2) := by positivity
  have hH := RadialHeatProfile.profile_h_sub_one_bound hh hz
  have he : r ^ 2 * (heatCarrier h C ν r - referencePower h C r) =
      (r ^ 2 * referencePower h C r) *
        (RadialHeatProfile.profile (1 + h) (2 * ν / (r ^ 2 / 2)) - 1) := by
    have hexp : RadialHeatProfile.spatialExponent (1 + h) = -A h := by
      unfold RadialHeatProfile.spatialExponent A
      ring
    simp only [heatCarrier, RadialHeatProfile.radialProfile,
      RadialHeatProfile.spatialProfile, hexp, referencePower]
    ring
  rw [he, weighted_referencePower h C hr, abs_mul, abs_mul, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _),
    abs_of_pos (Real.rpow_pos_of_pos hr _)]
  calc
    _ ≤ |C| * (2 : ℝ) ^ A h * r ^ (1 - 2 * h) *
        (h * (1 + h) * (2 * ν / (r ^ 2 / 2))) :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ |C| * (2 : ℝ) ^ A h * r ^ (1 - 2 * h) *
        (h * (1 + h) * (2 * 1 / (r ^ 2 / 2))) := by gcongr; exact hν.2
    _ = (4 * |C| * (2 : ℝ) ^ A h * h * (1 + h)) * (r ^ (1 - 2 * h) / r ^ 2) := by ring
    _ = _ := by
      rw [← Real.rpow_two, ← Real.rpow_sub hr]
      congr 2
      ring

theorem radialDifference_integrable {h C B : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hB : 0 < B) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ioo (-1 : ℝ) 1))
    (he : ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ R : ℝ, B ≤ R →
      F (R, eta) = heatCarrier h C (1 - eta ^ 2) R)
    {eta : ℝ} (hη : eta ∈ Ioo (-1 : ℝ) 1) :
    IntegrableOn (radialDifference h C F eta) (Ioi 0) := by
  have hν : 1 - eta ^ 2 ∈ Icc (0 : ℝ) 1 := by
    exact ParametricHeatTail.diffusion_mem ⟨hη.1.le, hη.2.le⟩
  have hout : IntegrableOn (radialDifference h C F eta) (Ioi B) := by
    apply ((integrableOn_Ioi_rpow_of_lt (a := -1 - 2 * h) (by linarith) hB).const_mul
      (4 * |C| * (2 : ℝ) ^ A h * h * (1 + h))).mono'
        (((radialDifference_continuousOn hF hη).mono (Ioi_subset_Ioi hB.le)).aestronglyMeasurable
          measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, radialDifference, he eta hη r hr.le]
    exact weighted_heat_difference_bound hh hν (hB.trans hr) C
  apply ((radialDifference_integrable_near_axis hh1 hF hη).union hout).mono_set
  intro r hr
  by_cases hb : r ≤ B
  · exact Or.inl ⟨hr.le, hb⟩
  · exact Or.inr (lt_of_not_ge hb)

theorem physical_axial_viscosity_moment_zero {h τ C B : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hτ : 0 < τ) (hB : 0 < B)
    {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ioo (-1 : ℝ) 1))
    (he : ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ R : ℝ, B ≤ R →
      F (R, eta) = heatCarrier h C (1 - eta ^ 2) R)
    (hm : ∀ eta ∈ Ioo (-1 : ℝ) 1, profileMoment h C F eta = 0) (z : ℝ) :
    IntegrableOn (fun r => r ^ 2 * iteratedDeriv 2 (fun y => velocity h τ F (y, r)) z) (Ioi 0) ∧
      (∫ r in Ioi (0 : ℝ), r ^ 2 * iteratedDeriv 2 (fun y => velocity h τ F (y, r)) z) = 0 := by
  apply axial_viscosity_moment_zero (reference := referencePower h C)
    (velocity_contDiff hh hh1 hτ hF) (velocity_commonExterior hh hh1 hτ hB he)
  · exact profileMoment_integrable_physical hh hh1 hτ
      (fun eta hη => radialDifference_integrable hh hh1 hB hF he hη)
  · intro y
    rw [physical_moment_scaling hh hh1 hτ C F y, hm _ (eta_mem hh hh1 hτ y), mul_zero]

/-! ## The nominal `X`-moment and the literal physical velocity -/

theorem squareHalf_image : (fun r : ℝ => r ^ 2 / 2) '' Ioi 0 = Ioi 0 := by
  ext X
  constructor
  · rintro ⟨r, hr, rfl⟩
    change 0 < r ^ 2 / 2
    exact div_pos (sq_pos_of_pos hr) (by norm_num)
  · intro hX
    refine ⟨Real.sqrt (2 * X), Real.sqrt_pos.mpr (mul_pos (by norm_num) hX), ?_⟩
    dsimp only
    rw [Real.sq_sqrt (show 0 ≤ 2 * X from mul_nonneg (by norm_num) hX.le)]
    ring

theorem squareHalf_injective : InjOn (fun r : ℝ => r ^ 2 / 2) (Ioi 0) := by
  intro r hr s hs h
  apply (sq_eq_sq₀ hr.le hs.le).mp
  linarith

theorem squareHalf_derivative (r : ℝ) : HasDerivAt (fun r : ℝ => r ^ 2 / 2) r r := by
  convert! ((hasDerivAt_id r).pow 2).div_const 2 using 1 ; simp

theorem profileMoment_eq_X_integral (h C : ℝ) (F : ℝ × ℝ → ℝ) (eta : ℝ) :
    profileMoment h C F eta =
      ∫ X in Ioi (0 : ℝ), Real.sqrt (2 * X) *
        (F (Real.sqrt (2 * X), eta) - C * X ^ (-A h)) := by
  have hc := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun r (_ : r ∈ Ioi (0 : ℝ)) => (squareHalf_derivative r).hasDerivWithinAt)
    squareHalf_injective
    (fun X => Real.sqrt (2 * X) * (F (Real.sqrt (2 * X), eta) - C * X ^ (-A h)))
  rw [squareHalf_image] at hc
  rw [hc]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [abs_of_pos hr, smul_eq_mul, show 2 * (r ^ 2 / 2) = r ^ 2 by ring,
    Real.sqrt_sq hr.le]
  unfold radialDifference referencePower
  ring

noncomputable def xMoment (h C : ℝ) (E : ℝ × ℝ → ℝ) (eta : ℝ) : ℝ :=
  ∫ X in Ioi (0 : ℝ), Real.sqrt (2 * X) * (E (X, eta) - C * X ^ (-A h))

theorem profileMoment_eq_xMoment (h C : ℝ) {F E : ℝ × ℝ → ℝ}
    (hFE : ∀ R : ℝ, 0 < R → ∀ eta ∈ Ioo (-1 : ℝ) 1,
      F (R, eta) = E (R ^ 2 / 2, eta)) {eta : ℝ} (hη : eta ∈ Ioo (-1 : ℝ) 1) :
    profileMoment h C F eta = xMoment h C E eta := by
  rw [profileMoment_eq_X_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  dsimp only
  rw [hFE _ (Real.sqrt_pos.mpr (mul_pos (by norm_num) hX)) eta hη,
    Real.sq_sqrt (show 0 ≤ 2 * X from mul_nonneg (by norm_num) hX.le), show 2 * X / 2 = X by ring]

noncomputable def profileVelocity (h τ : ℝ) (E : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Q h τ p.1 ^ (-A h) * E (p.2 ^ 2 / (2 * Q h τ p.1), eta h τ p.1)

noncomputable def uTheta (h : ℝ) (E : ℝ × ℝ → ℝ) (t r z : ℝ) : ℝ :=
  profileVelocity h (1 - t) E (z, r)

theorem velocity_eq_profileVelocity {h τ : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hτ : 0 < τ) {F E : ℝ × ℝ → ℝ}
    (hFE : ∀ R : ℝ, 0 < R → ∀ eta ∈ Ioo (-1 : ℝ) 1,
      F (R, eta) = E (R ^ 2 / 2, eta)) {r : ℝ} (hr : 0 < r) (z : ℝ) :
    velocity h τ F (z, r) = profileVelocity h τ E (z, r) := by
  have hq := Q_pos hh hh1 hτ z
  have hp : (r / Real.sqrt (Q h τ z)) ^ 2 / 2 = r ^ 2 / (2 * Q h τ z) := by
    rw [div_pow, Real.sq_sqrt hq.le]
    ring
  rw [velocity, hFE _ (div_pos hr (Real.sqrt_pos.mpr hq)) _ (eta_mem hh hh1 hτ z), hp]
  rfl

theorem radial_exterior_of_X_exterior {h C T : ℝ} (hT : 0 < T) {F E : ℝ × ℝ → ℝ}
    (hFE : ∀ R : ℝ, 0 < R → ∀ eta ∈ Ioo (-1 : ℝ) 1,
      F (R, eta) = E (R ^ 2 / 2, eta))
    (he : ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ X : ℝ, T ≤ X →
      E (X, eta) = C * X ^ (-A h) *
        RadialHeatProfile.profile (1 + h) (2 * (1 - eta ^ 2) / X)) :
    ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ R : ℝ, Real.sqrt (2 * T) ≤ R →
      F (R, eta) = heatCarrier h C (1 - eta ^ 2) R := by
  intro eta hη R hR
  have hRp : 0 < R := (Real.sqrt_pos.mpr (mul_pos (by norm_num) hT)).trans_le hR
  have hXT : T ≤ R ^ 2 / 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * T from mul_nonneg (by norm_num) hT.le)
    have hsq := sq_le_sq₀ (Real.sqrt_nonneg (2 * T)) hRp.le
    nlinarith [(hsq.mpr hR)]
  rw [hFE R hRp eta hη, he eta hη _ hXT]
  have hexp : RadialHeatProfile.spatialExponent (1 + h) = -A h := by
    unfold RadialHeatProfile.spatialExponent A
    ring
  simp only [heatCarrier, RadialHeatProfile.radialProfile, RadialHeatProfile.spatialProfile, hexp]
  ring

/-- The only nominal input involving an integral is the original renormalized
moment itself. Its differentiated moment is derived, not assumed. -/
theorem physical_axial_viscosity_zero_of_X_profile {h τ C T : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hτ : 0 < τ) (hT : 0 < T)
    {F E : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ioo (-1 : ℝ) 1))
    (hFE : ∀ R : ℝ, 0 < R → ∀ eta ∈ Ioo (-1 : ℝ) 1,
      F (R, eta) = E (R ^ 2 / 2, eta))
    (he : ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ X : ℝ, T ≤ X →
      E (X, eta) = C * X ^ (-A h) *
        RadialHeatProfile.profile (1 + h) (2 * (1 - eta ^ 2) / X))
    (hm : ∀ eta ∈ Ioo (-1 : ℝ) 1, xMoment h C E eta = 0) (z : ℝ) :
    IntegrableOn (fun r => r ^ 2 * iteratedDeriv 2 (fun y => profileVelocity h τ E (y, r)) z) (Ioi
      0) ∧
      (∫ r in Ioi (0 : ℝ), r ^ 2 * iteratedDeriv 2 (fun y => profileVelocity h τ E (y, r)) z) = 0
        := by
  have hrad := radial_exterior_of_X_exterior hT hFE he
  have hmF : ∀ eta ∈ Ioo (-1 : ℝ) 1, profileMoment h C F eta = 0 := by
    intro eta hη
    rw [profileMoment_eq_xMoment h C hFE hη, hm eta hη]
  obtain ⟨hi, hz⟩ := physical_axial_viscosity_moment_zero hh hh1 hτ
    (Real.sqrt_pos.mpr (mul_pos (by norm_num) hT)) hF hrad hmF z
  have hfg : (fun r => r ^ 2 * iteratedDeriv 2 (fun y => velocity h τ F (y, r)) z) =ᵐ[
      volume.restrict (Ioi 0)]
      (fun r => r ^ 2 * iteratedDeriv 2 (fun y => profileVelocity h τ E (y, r)) z) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hf : (fun y => velocity h τ F (y, r)) = fun y => profileVelocity h τ E (y, r) :=
      funext (velocity_eq_profileVelocity hh hh1 hτ hFE hr)
    rw [hf]
  exact ⟨hi.congr hfg, (integral_congr_ae hfg).symm.trans hz⟩

theorem uTheta_axial_viscosity_integral {h t C T : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1) (hT : 0 < T)
    {F E : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ioo (-1 : ℝ) 1))
    (hFE : ∀ R : ℝ, 0 < R → ∀ eta ∈ Ioo (-1 : ℝ) 1,
      F (R, eta) = E (R ^ 2 / 2, eta))
    (he : ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ X : ℝ, T ≤ X →
      E (X, eta) = C * X ^ (-A h) *
        RadialHeatProfile.profile (1 + h) (2 * (1 - eta ^ 2) / X))
    (hm : ∀ eta ∈ Ioo (-1 : ℝ) 1, xMoment h C E eta = 0) (z : ℝ) :
    (∫ r in Ioi (0 : ℝ), r ^ 2 * deriv (deriv (uTheta h E t r)) z) = 0 := by
  unfold uTheta
  simpa only [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero]
    using
    (physical_axial_viscosity_zero_of_X_profile hh hh1 (sub_pos.mpr ht) hT hF hFE he hm z).2

theorem uTheta_eq_similarity_pullback (h : ℝ) (E : ℝ × ℝ → ℝ) (t r z : ℝ) :
    uTheta h E t r z = SimilarityProfile.pullback h (-A h) E (t, (r ^ 2 / 2, z)) := by
  unfold uTheta profileVelocity SimilarityProfile.pullback SimilarityProfile.inner
    SimilarityProfile.X SimilarityProfile.q SimilarityProfile.eta Q eta
  have he : r ^ 2 / (2 * SimilarityCoordinates.coordinateQ (2 * h) (1 - t, z)) =
      (r ^ 2 / 2) / SimilarityCoordinates.coordinateQ (2 * h) (1 - t, z) := by ring
  rw [he]

/-- The scaling used to transfer the physical order-one viscosity moment to
the radial profile moment: `r = sqrt(q) R` contributes `q^(3/2)`. -/
theorem integral_weighted_radial_scale (b : ℝ) {q : ℝ} (hq : 0 < q) (g : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), r ^ 2 * (q ^ b * g (r / Real.sqrt q))) =
      q ^ (b + 3 / 2) * ∫ R in Ioi (0 : ℝ), R ^ 2 * g R := by
  have hf : (fun r => r ^ 2 * (q ^ b * g (r / Real.sqrt q))) =
      fun r => (q * q ^ b) * ((r / Real.sqrt q) ^ 2 * g (r / Real.sqrt q)) := by
    funext r
    rw [div_pow, Real.sq_sqrt hq.le]
    field_simp [hq.ne']
  rw [hf, integral_const_mul]
  have hs := integral_comp_mul_right_Ioi (fun R => R ^ 2 * g R) 0
    (inv_pos.mpr (Real.sqrt_pos.mpr hq))
  simp only [inv_inv, smul_eq_mul, ← div_eq_mul_inv, zero_div] at hs
  rw [hs, ← mul_assoc]
  have hp : q * q ^ b * Real.sqrt q = q ^ (b + 3 / 2) := by
    calc
      _ = q ^ (1 : ℝ) * q ^ b * q ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = q ^ ((1 + b) + 1 / 2) := by rw [Real.rpow_add hq, Real.rpow_add hq]
      _ = _ := by congr 1; ring
  rw [hp]

theorem integral_axial_scale (h : ℝ) {q : ℝ} (hq : 0 < q) (g : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), r ^ 2 *
      (q ^ (-A h - 2 * CoordinateAlgebra.D h) * g (r / Real.sqrt q))) =
        q ^ h * ∫ R in Ioi (0 : ℝ), R ^ 2 * g R := by
  rw [integral_weighted_radial_scale _ hq]
  congr 2
  unfold A CoordinateAlgebra.D
  ring

theorem exterior_second_derivative_zero {u : ℝ × ℝ → ℝ} {tail : ℝ → ℝ}
    (he : CommonExterior u tail) (z : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, B ≤ r → iteratedDeriv 2 (fun y => u (y, r)) z = 0 := by
  obtain ⟨ε, B, hε, hB, htail⟩ := he z
  refine ⟨B, hB, ?_⟩
  intro r hr
  have hfun : (fun y => u (y, r)) =ᶠ[𝓝 z] (fun _ => tail r) := by
    filter_upwards [Metric.ball_mem_nhds z hε] with y hy
    exact htail y hy r hr
  rw [hfun.iteratedDeriv_eq 2]
  simp only [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
  have hc : deriv (fun _ : ℝ => tail r) = fun _ => 0 := funext fun y => deriv_const y (tail r)
  rw [hc]
  exact deriv_const z 0

/-! ## The reference normalization of the constructed outgoing schedule -/

noncomputable def outgoingPowerAmplitude (P : OutgoingProfile.Profile) (XR : ℝ) : ℝ :=
  OutgoingTail.powerConstant P.data * XR ^ A P.data.h

theorem outgoing_powerH (P : OutgoingProfile.Profile) {XR X : ℝ}
    (hXR : 0 < XR) (hX : 0 < X) :
    OutgoingDilation.powerH P XR X =
      Real.sqrt (2 * X) * (outgoingPowerAmplitude P XR * X ^ (-A P.data.h)) := by
  rw [OutgoingDilation.powerH, OutgoingDilation.powerE_coefficient P XR X hXR hX]
  rfl

theorem outgoing_amplitude_eq_heat (P : OutgoingProfile.Profile) {XR : ℝ} (hXR : 0 < XR) :
    outgoingPowerAmplitude P XR =
      OutgoingDilation.carrierAmplitude P *
        OutgoingDilation.switchRadius P XR ^ HeatTailEdit.exponent P.data.h := by
  change OutgoingTail.powerConstant P.data * XR ^ A P.data.h =
    (OutgoingTail.powerConstant P.data * Real.exp (-A P.data.h * HeatTailEdit.switchStart P.data)) *
      (XR * Real.exp (HeatTailEdit.switchStart P.data)) ^ A P.data.h
  rw [Real.mul_rpow hXR.le (Real.exp_pos _).le, ← Real.exp_mul]
  have he : Real.exp (-A P.data.h * HeatTailEdit.switchStart P.data) *
      Real.exp (HeatTailEdit.switchStart P.data * A P.data.h) = 1 := by
    rw [← Real.exp_add, show -A P.data.h * HeatTailEdit.switchStart P.data +
      HeatTailEdit.switchStart P.data * A P.data.h = 0 by ring, Real.exp_zero]
  calc
    _ = (OutgoingTail.powerConstant P.data * XR ^ A P.data.h) * 1 := by ring
    _ = _ := by rw [← he]; ring

theorem xMoment_eq_outgoing_reference (P : OutgoingProfile.Profile) {XR : ℝ} (hXR : 0 < XR)
    (E : ℝ × ℝ → ℝ) (eta : ℝ) :
    xMoment P.data.h (outgoingPowerAmplitude P XR) E eta =
      ∫ X in Ioi (0 : ℝ), Real.sqrt (2 * X) * E (X, eta) - OutgoingDilation.powerH P XR X := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  dsimp only
  rw [outgoing_powerH P hXR hX]
  ring

noncomputable def heatThreshold (P : OutgoingProfile.Profile) (XR : ℝ) : ℝ :=
  OutgoingDilation.switchRadius P XR * Real.exp 3

theorem heatThreshold_pos (P : OutgoingProfile.Profile) {XR : ℝ} (hXR : 0 < XR) :
    0 < heatThreshold P XR :=
  mul_pos (OutgoingDilation.switchRadius_pos P XR hXR) (Real.exp_pos _)

theorem heated_exterior (P : OutgoingProfile.Profile) {XR : ℝ} (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) (eta : ℝ) {X : ℝ} (hX : heatThreshold P XR ≤ X) :
    HeatedOutgoing.E P XR c (X, eta) =
      outgoingPowerAmplitude P XR * X ^ (-A P.data.h) *
        RadialHeatProfile.profile (1 + P.data.h) (2 * (1 - eta ^ 2) / X) := by
  have hK := OutgoingDilation.switchRadius_pos P XR hXR
  have hXp := (heatThreshold_pos P hXR).trans_le hX
  have hdiv : Real.exp 3 ≤ X / OutgoingDilation.switchRadius P XR := by
    apply (le_div_iff₀ hK).mpr
    simpa only [heatThreshold, mul_comm] using hX
  have hlog : 3 ≤ Real.log (X / OutgoingDilation.switchRadius P XR) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 3) hdiv
  have he := HeatedOutgoing.E_eventual_heat P XR c eta X hXR hXp (by linarith)
  rw [← outgoing_amplitude_eq_heat P hXR] at he
  have hexp : RadialHeatProfile.spatialExponent (1 + P.data.h) = -A P.data.h := by
    unfold RadialHeatProfile.spatialExponent A
    ring
  rw [he]
  simp only [RadialHeatProfile.spatialProfile, hexp, ParametricHeatTail.diffusion]
  ring

/-- Specialization to the actual heated and compensated outgoing witness.
The remaining upstream conditions are precisely the nominal axis gluing and
its original reset moment, not an axial-viscosity moment or derivative bound. -/
theorem heated_nominal_axial_viscosity (P : OutgoingProfile.Profile)
    {XR cost t : ℝ} (w : HeatedOutgoing.CompensationWitness P XR cost)
    (hh1 : P.data.h < 1 / 2) (ht : t < 1) (L : ℝ)
    {F E : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ioo (-1 : ℝ) 1))
    (hFE : ∀ R : ℝ, 0 < R → ∀ eta ∈ Ioo (-1 : ℝ) 1,
      F (R, eta) = E (R ^ 2 / 2, eta))
    (hmatch : ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ X : ℝ, L ≤ X →
      E (X, eta) = HeatedOutgoing.E P XR w.coefficients (X, eta))
    (hreset : ∀ eta ∈ Ioo (-1 : ℝ) 1,
      (∫ X in Ioi (0 : ℝ), Real.sqrt (2 * X) * E (X, eta) - OutgoingDilation.powerH P XR X) =
      ∫ X in Ioi (0 : ℝ), HeatedOutgoing.H P XR w.coefficients (X, eta) -
        OutgoingDilation.powerH P XR X) (z : ℝ) :
    IntegrableOn (fun r => r ^ 2 * deriv (deriv (uTheta P.data.h E t r)) z) (Ioi 0) ∧
      (∫ r in Ioi (0 : ℝ), r ^ 2 * deriv (deriv (uTheta P.data.h E t r)) z) = 0 := by
  let T := max L (heatThreshold P XR)
  have hT : 0 < T := (heatThreshold_pos P w.radius_pos).trans_le (le_max_right _ _)
  have he : ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ X : ℝ, T ≤ X →
      E (X, eta) = outgoingPowerAmplitude P XR * X ^ (-A P.data.h) *
        RadialHeatProfile.profile (1 + P.data.h) (2 * (1 - eta ^ 2) / X) := by
    intro eta hη X hX
    rw [hmatch eta hη X ((le_max_left _ _).trans hX)]
    exact heated_exterior P w.radius_pos w.coefficients eta ((le_max_right _ _).trans hX)
  have hm : ∀ eta ∈ Ioo (-1 : ℝ) 1, xMoment P.data.h (outgoingPowerAmplitude P XR) E eta = 0 := by
    intro eta hη
    rw [xMoment_eq_outgoing_reference P w.radius_pos, hreset eta hη]
    exact w.renormalized_zero eta ⟨hη.1.le, hη.2.le⟩
  unfold uTheta
  simpa only [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero]
    using
    physical_axial_viscosity_zero_of_X_profile P.data.h_pos hh1 (sub_pos.mpr ht)
      hT hF hFE he hm z

end NavierStokes.RenormalizedHeatMoment
