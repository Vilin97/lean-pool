/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyDrift

/-!
# The difference of two weak solutions as a forced path

If `θ` and `θ_M` are weak solutions with the same datum and diffusivity but different
drifts, the difference `w = θ - θ_M` satisfies the forced mode-path equation for the drift of
`θ`, with transport density `b·Dw` and any flux `F` representing `(b - b_M)·Dθ_M` against smooth
periodic tests.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Parabolic.WeakUniqueness

local instance differenceFiniteUnitCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  unfold AVenhance.unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance differenceFiniteTimeCube :
    IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [forced_timeCube_measure_eq_product]
  infer_instance

/-- Pairing of a weak solution's mode density with a smooth periodic mode is integrable on
the time cell. -/
theorem weak_modeDensity_integrable {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : AVenhance.IsWeakSolutionGrad b κ g θ Dθ) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Integrable (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2) * ψ p.2 +
        κ * Homogenization.vecDot (Dθ p.1 p.2) (AVenhance.spaceGrad ψ p.2))
      (volume.restrict AVenhance.timeCube) := by
  have hψone : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hgrad : Continuous (fun x : Vec 2 => AVenhance.spaceGrad ψ x) := by
    apply continuous_pi
    intro i
    exact (hψone.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := forced_continuous_bound hψ.continuous
  have h1 := hθ.2.2.2.2.2.1.mul_bdd
    (hψ.continuous.comp continuous_snd).measurable.aestronglyMeasurable hC
  exact h1.add ((forced_vecDot_integrable hθ.2.2.2.1 hgrad).const_mul κ)

/-- The difference of two weak solutions with the same datum and diffusivity satisfies the
forced mode-path equation, provided the cross transport `(b - b_M)·Dθ_M` is represented by the
flux `F` against every smooth periodic mode. -/
theorem difference_forcedModePath
    {b bM : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {θ θM : ℝ → Vec 2 → ℝ} {Dθ DM : ℝ → Vec 2 → Vec 2}
    (hθ : AVenhance.IsWeakSolutionGrad b κ g θ Dθ)
    (hM : AVenhance.IsWeakSolutionGrad bM κ g θM DM)
    (hg : MemL2On AVenhance.unitCube g)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    {F : ℝ × Vec 2 → Vec 2}
    (hF : ∀ i : Fin 2, MemLp (fun p => F p i) 2 (volume.restrict AVenhance.timeCube))
    (hflux : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      AVenhance.IsZ2Periodic ψ →
      Integrable (fun x => Homogenization.vecDot (b s x - bM s x) (DM s x) * ψ x)
        (volume.restrict AVenhance.unitCube) ∧
      ∫ x in AVenhance.unitCube,
          Homogenization.vecDot (b s x - bM s x) (DM s x) * ψ x =
        ∫ x in AVenhance.unitCube,
          Homogenization.vecDot (F (s, x)) (AVenhance.spaceGrad ψ x)) :
    ForcedModePath κ (fun _ => 0) (fun t x => θ t x - θM t x)
      (fun t x => Dθ t x - DM t x)
      (fun p => Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2)) F := by
  have hDw (i : Fin 2) : MemLp (fun p : ℝ × Vec 2 => (Dθ p.1 p.2 - DM p.1 p.2) i) 2
      (volume.restrict AVenhance.timeCube) :=
    (hθ.2.2.2.1 i).sub (hM.2.2.2.1 i)
  have hGmem : MemLp (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2)) 2
      (volume.restrict AVenhance.timeCube) :=
    forced_drift_memLp_two (b := b) (Dw := fun t x => Dθ t x - DM t x) hDw hb_meas hb_bdd
  refine ⟨fun t ht => (hθ.1 t ht).2.sub (hM.1 t ht).2, hθ.2.2.1.sub hM.2.2.1, hDw, hGmem, hF,
    ?_, ?_⟩
  · intro ψ hψ hψp
    have hψmem := weak_continuous_memL2On hψ.continuous
    refine ((hθ.2.2.2.2.2.2.1 ψ hψ hψp).sub (hM.2.2.2.2.2.2.1 ψ hψ hψp)).congr ?_
    intro t ht
    simp only [sub_mul]
    exact integral_sub (weak_product_integrable_cell (hθ.1 t ht).2 hψmem)
      (weak_product_integrable_cell (hM.1 t ht).2 hψmem)
  · intro ψ hψ hψp t ht
    have hpθ := weak_solution_mode_integral_path hθ hg hψ hψp t ht
    have hpM := weak_solution_mode_integral_path hM hg hψ hψp t ht
    have hψmem := weak_continuous_memL2On hψ.continuous
    have hqθ := weak_solution_mode_forcing_intervalIntegrable hθ hψ
    have hqM := weak_solution_mode_forcing_intervalIntegrable hM hψ
    have hψone : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have hgrad : Continuous (fun x : Vec 2 => AVenhance.spaceGrad ψ x) := by
      apply continuous_pi
      intro i
      exact (hψone.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hP := weak_modeDensity_integrable hθ hψ
    have hQ := weak_modeDensity_integrable hM hψ
    have hI := forcedModeIntegrand_integrable (κ := κ) (Du := fun t x => Dθ t x - DM t x)
      (G := fun p => Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2))
      hDw hGmem hF hψ
    have hFψ := forced_vecDot_integrable hF hgrad
    have slice {f : ℝ × Vec 2 → ℝ} (hf : Integrable f (volume.restrict AVenhance.timeCube)) :
        ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
          Integrable (fun x => f (s, x)) (volume.restrict AVenhance.unitCube) := by
      rw [forced_timeCube_measure_eq_product] at hf
      exact hf.prod_right_ae
    have hforce : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        forcedModeForcing κ (fun t x => Dθ t x - DM t x)
          (fun p => Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2)) F ψ s =
          weakModeForcing b κ Dθ ψ s - weakModeForcing bM κ DM ψ s := by
      filter_upwards [slice hP, slice hQ, slice hI, slice hFψ,
        ae_restrict_mem measurableSet_Ioo] with s hPs hQs hIs hFs hs
      obtain ⟨hRint, hReq⟩ := hflux s ⟨hs.1.le, hs.2.le⟩ ψ hψ hψp
      have hpt : ∀ x, (Homogenization.vecDot (b s x) (Dθ s x) * ψ x +
            κ * Homogenization.vecDot (Dθ s x) (AVenhance.spaceGrad ψ x)) -
          (Homogenization.vecDot (bM s x) (DM s x) * ψ x +
            κ * Homogenization.vecDot (DM s x) (AVenhance.spaceGrad ψ x)) =
          forcedModeIntegrand κ (fun t x => Dθ t x - DM t x)
            (fun p => Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2)) F ψ (s, x) +
          (Homogenization.vecDot (b s x - bM s x) (DM s x) * ψ x -
            Homogenization.vecDot (F (s, x)) (AVenhance.spaceGrad ψ x)) := by
        intro x
        unfold forcedModeIntegrand
        simp only [Homogenization.vecDot, Fin.sum_univ_two, Pi.sub_apply]
        ring
      have hsub := integral_sub hPs hQs
      have hcalc : ∫ x in AVenhance.unitCube,
          ((Homogenization.vecDot (b s x) (Dθ s x) * ψ x +
            κ * Homogenization.vecDot (Dθ s x) (AVenhance.spaceGrad ψ x)) -
          (Homogenization.vecDot (bM s x) (DM s x) * ψ x +
            κ * Homogenization.vecDot (DM s x) (AVenhance.spaceGrad ψ x))) =
          (∫ x in AVenhance.unitCube, forcedModeIntegrand κ (fun t x => Dθ t x - DM t x)
            (fun p => Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2)) F ψ (s, x)) +
          ((∫ x in AVenhance.unitCube,
              Homogenization.vecDot (b s x - bM s x) (DM s x) * ψ x) -
            ∫ x in AVenhance.unitCube,
              Homogenization.vecDot (F (s, x)) (AVenhance.spaceGrad ψ x)) := by
        have h1 : ∫ x in AVenhance.unitCube,
              (Homogenization.vecDot (b s x - bM s x) (DM s x) * ψ x -
                Homogenization.vecDot (F (s, x)) (AVenhance.spaceGrad ψ x)) =
            (∫ x in AVenhance.unitCube,
              Homogenization.vecDot (b s x - bM s x) (DM s x) * ψ x) -
            ∫ x in AVenhance.unitCube,
              Homogenization.vecDot (F (s, x)) (AVenhance.spaceGrad ψ x) :=
          integral_sub hRint hFs
        have hRF : Integrable (fun x =>
            Homogenization.vecDot (b s x - bM s x) (DM s x) * ψ x -
              Homogenization.vecDot (F (s, x)) (AVenhance.spaceGrad ψ x))
            (volume.restrict AVenhance.unitCube) := hRint.sub hFs
        have h2 : ∫ x in AVenhance.unitCube,
              (forcedModeIntegrand κ (fun t x => Dθ t x - DM t x)
                (fun p => Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2)) F ψ (s, x) +
              (Homogenization.vecDot (b s x - bM s x) (DM s x) * ψ x -
                Homogenization.vecDot (F (s, x)) (AVenhance.spaceGrad ψ x))) =
            (∫ x in AVenhance.unitCube, forcedModeIntegrand κ (fun t x => Dθ t x - DM t x)
                (fun p => Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2)) F ψ (s, x)) +
            ∫ x in AVenhance.unitCube,
              (Homogenization.vecDot (b s x - bM s x) (DM s x) * ψ x -
                Homogenization.vecDot (F (s, x)) (AVenhance.spaceGrad ψ x)) :=
          integral_add hIs hRF
        rw [integral_congr_ae (Eventually.of_forall hpt), h2, h1]
      unfold forcedModeForcing weakModeForcing
      rw [← hsub, hcalc, hReq]
      ring
    have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
      rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num)]
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({1} : Set ℝ) :=
      (Set.countable_singleton (1 : ℝ)).ae_notMem volume
    rw [ae_restrict_iff' measurableSet_Ioo] at hforce
    have e2 : ∫ s in (0 : ℝ)..t, forcedModeForcing κ (fun t x => Dθ t x - DM t x)
          (fun p => Homogenization.vecDot (b p.1 p.2) (Dθ p.1 p.2 - DM p.1 p.2)) F ψ s =
        (∫ s in (0 : ℝ)..t, weakModeForcing b κ Dθ ψ s) -
          ∫ s in (0 : ℝ)..t, weakModeForcing bM κ DM ψ s := by
      rw [← intervalIntegral.integral_sub (hqθ.mono_set hsub) (hqM.mono_set hsub)]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hforce, hne] with s hs hs1 hmem
      rw [uIoc_of_le ht.1] at hmem
      exact hs ⟨hmem.1, lt_of_le_of_ne (hmem.2.trans ht.2) (fun h => hs1 (by simp [h]))⟩
    have e1 : ∫ x in AVenhance.unitCube, (θ t x - θM t x) * ψ x =
        weakModePairing θ ψ t - weakModePairing θM ψ t := by
      simp only [weakModePairing, sub_mul]
      exact integral_sub (weak_product_integrable_cell (hθ.1 t ht).2 hψmem)
        (weak_product_integrable_cell (hM.1 t ht).2 hψmem)
    change ∫ x in AVenhance.unitCube, (θ t x - θM t x) * ψ x =
      (∫ x in AVenhance.unitCube, (fun _ : Vec 2 => (0 : ℝ)) x * ψ x) - _
    rw [e2, e1, hpθ, hpM]
    simp

/-- Squeeze for the square of a difference of two `L²`-null sequences. -/
theorem tendsto_integral_sq_sub {μ : Measure (ℝ × Vec 2)} {a c : ℕ → ℝ × Vec 2 → ℝ}
    (ha : ∀ N, MemLp (a N) 2 μ) (hc : ∀ N, MemLp (c N) 2 μ)
    (h1 : Tendsto (fun N => ∫ p, (a N p) ^ 2 ∂μ) atTop (𝓝 0))
    (h2 : Tendsto (fun N => ∫ p, (c N p) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun N => ∫ p, (a N p - c N p) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hint (N : ℕ) : Integrable (fun p => (a N p) ^ 2) μ :=
    (memLp_two_iff_integrable_sq (ha N).aestronglyMeasurable).1 (ha N)
  have hint' (N : ℕ) : Integrable (fun p => (c N p) ^ 2) μ :=
    (memLp_two_iff_integrable_sq (hc N).aestronglyMeasurable).1 (hc N)
  have hsub (N : ℕ) : MemLp (fun p => a N p - c N p) 2 μ := (ha N).sub (hc N)
  have hintd (N : ℕ) : Integrable (fun p => (a N p - c N p) ^ 2) μ :=
    (memLp_two_iff_integrable_sq (hsub N).aestronglyMeasurable).1 (hsub N)
  have hupper : Tendsto (fun N => 2 * ∫ p, (a N p) ^ 2 ∂μ + 2 * ∫ p, (c N p) ^ 2 ∂μ)
      atTop (𝓝 0) := by
    simpa using (h1.const_mul 2).add (h2.const_mul 2)
  refine squeeze_zero (fun N => integral_nonneg fun p => sq_nonneg _) (fun N => ?_) hupper
  calc ∫ p, (a N p - c N p) ^ 2 ∂μ ≤ ∫ p, (2 * (a N p) ^ 2 + 2 * (c N p) ^ 2) ∂μ :=
        integral_mono (hintd N) (((hint N).const_mul 2).add ((hint' N).const_mul 2))
          (fun p => by nlinarith [sq_nonneg (a N p + c N p)])
    _ = 2 * ∫ p, (a N p) ^ 2 ∂μ + 2 * ∫ p, (c N p) ^ 2 ∂μ := by
        rw [integral_add ((hint N).const_mul 2) ((hint' N).const_mul 2), integral_const_mul,
          integral_const_mul]

/-- The Fourier coefficients of a difference are the differences of the coefficients. -/
theorem weakModePairing_sub {θ θM : ℝ → Vec 2 → ℝ} {ψ : Vec 2 → ℝ} {t : ℝ}
    (hθ : MemL2On AVenhance.unitCube (θ t)) (hM : MemL2On AVenhance.unitCube (θM t))
    (hψ : MemL2On AVenhance.unitCube ψ) :
    weakModePairing (fun t x => θ t x - θM t x) ψ t =
      weakModePairing θ ψ t - weakModePairing θM ψ t := by
  simp only [weakModePairing, sub_mul]
  exact integral_sub (weak_product_integrable_cell hθ hψ) (weak_product_integrable_cell hM hψ)

theorem forcedMode_memL2 (N : ℕ) (i : Fin (RealFourierDimension N)) :
    MemL2On AVenhance.unitCube (forcedMode N i) :=
  weak_continuous_memL2On (forcedMode_smooth N i).continuous

theorem projection_sub_apply {θ θM : ℝ → Vec 2 → ℝ} {t : ℝ} (N : ℕ)
    (hθ : MemL2On AVenhance.unitCube (θ t)) (hM : MemL2On AVenhance.unitCube (θM t)) (x : Vec 2) :
    weakFourierModeProjection N (fun t x => θ t x - θM t x) t x =
      weakFourierModeProjection N θ t x - weakFourierModeProjection N θM t x := by
  rw [forced_projection_expansion, forced_projection_expansion, forced_projection_expansion,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [weakModePairing_sub hθ hM (forcedMode_memL2 N i)]
  ring

theorem projection_grad_sub_apply {θ θM : ℝ → Vec 2 → ℝ} {t : ℝ} (N : ℕ)
    (hθ : MemL2On AVenhance.unitCube (θ t)) (hM : MemL2On AVenhance.unitCube (θM t))
    (x : Vec 2) (j : Fin 2) :
    AVenhance.spaceGrad (weakFourierModeProjection N (fun t x => θ t x - θM t x) t) x j =
      AVenhance.spaceGrad (weakFourierModeProjection N θ t) x j -
        AVenhance.spaceGrad (weakFourierModeProjection N θM t) x j := by
  rw [forced_projection_grad_expansion, forced_projection_grad_expansion,
    forced_projection_grad_expansion, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [weakModePairing_sub hθ hM (forcedMode_memL2 N i)]
  ring

/-- Spacetime `L²` convergence of the Fourier projections of a difference of weak solutions. -/
theorem difference_projection_tendsto
    {b bM : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {θ θM : ℝ → Vec 2 → ℝ} {Dθ DM : ℝ → Vec 2 → Vec 2}
    (hθ : AVenhance.IsWeakSolutionGrad b κ g θ Dθ)
    (hM : AVenhance.IsWeakSolutionGrad bM κ g θM DM) :
    Tendsto (fun N => ∫ p in AVenhance.timeCube,
      ((θ p.1 p.2 - θM p.1 p.2) -
        weakFourierModeProjection N (fun t x => θ t x - θM t x) p.1 p.2) ^ 2)
      atTop (𝓝 0) ∧
    ∀ i : Fin 2, Tendsto (fun N => ∫ p in AVenhance.timeCube,
      ((Dθ p.1 p.2 - DM p.1 p.2) i -
        AVenhance.spaceGrad
          (weakFourierModeProjection N (fun t x => θ t x - θM t x) p.1) p.2 i) ^ 2)
      atTop (𝓝 0) := by
  have hae : ∀ᵐ p ∂(volume.restrict AVenhance.timeCube), p.1 ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem forced_timeCube_measurable] with p hp
    exact ⟨hp.1.1.le, hp.1.2.le⟩
  refine ⟨?_, fun i => ?_⟩
  · have key := tendsto_integral_sq_sub (μ := volume.restrict AVenhance.timeCube)
      (a := fun N p => θ p.1 p.2 - weakFourierModeProjection N θ p.1 p.2)
      (c := fun N p => θM p.1 p.2 - weakFourierModeProjection N θM p.1 p.2)
      (fun N => hθ.2.2.1.sub (weakEnergyProjection_memLp hθ N))
      (fun N => hM.2.2.1.sub (weakEnergyProjection_memLp hM N))
      (weakFourierProjection_scalar_spacetime_L2_tendsto hθ)
      (weakFourierProjection_scalar_spacetime_L2_tendsto hM)
    refine key.congr fun N => integral_congr_ae ?_
    filter_upwards [hae] with p hp
    simp only [projection_sub_apply N (hθ.1 _ hp).2 (hM.1 _ hp).2 p.2]
    ring
  · have key := tendsto_integral_sq_sub (μ := volume.restrict AVenhance.timeCube)
      (a := fun N p => Dθ p.1 p.2 i -
        AVenhance.spaceGrad (weakFourierModeProjection N θ p.1) p.2 i)
      (c := fun N p => DM p.1 p.2 i -
        AVenhance.spaceGrad (weakFourierModeProjection N θM p.1) p.2 i)
      (fun N => (hθ.2.2.2.1 i).sub (weakEnergyGradient_memLp hθ N i))
      (fun N => (hM.2.2.2.1 i).sub (weakEnergyGradient_memLp hM N i))
      (weakFourierProjection_gradient_spacetime_L2_tendsto hθ i)
      (weakFourierProjection_gradient_spacetime_L2_tendsto hM i)
    refine key.congr fun N => integral_congr_ae ?_
    filter_upwards [hae] with p hp
    simp only [projection_grad_sub_apply N (hθ.1 _ hp).2 (hM.1 _ hp).2 p.2 i, Pi.sub_apply]
    ring

end AVenhance.Infra.Section5.RelativeError

end
