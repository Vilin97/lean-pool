/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyStream
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyClassical
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Drift

/-!
# RelativeError item 12: the stream-difference estimate

A weak solution `θ` for the limit drift `b = σ∇φ` and the classical solution `θ_M` for a smooth
stream `Ψ`, with the same datum and diffusivity, have `η/κ`-close dissipation whenever
`|φ - Ψ| ≤ η`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Parabolic.WeakUniqueness

local instance streamDiffFiniteUnitCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  unfold AVenhance.unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance streamDiffFiniteTimeCube :
    IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [forced_timeCube_measure_eq_product]
  infer_instance

/-- The skew rotation of a classical gradient field is coordinatewise `L²`. -/
theorem sigma_gradient_memLp {θM : ℝ → Vec 2 → ℝ}
    (hDM : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (θM p.1) p.2 i) 2
      (volume.restrict AVenhance.timeCube)) (i : Fin 2) :
    MemLp (fun p : ℝ × Vec 2 =>
      AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (θM p.1) p.2) i) 2
      (volume.restrict AVenhance.timeCube) := by
  fin_cases i
  · have : (fun p : ℝ × Vec 2 => AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (θM p.1) p.2) 0) =
        fun p => -(AVenhance.spaceGrad (θM p.1) p.2 1) :=
      funext fun p => sigmaMat_mulVec_apply_zero _
    change MemLp (fun p : ℝ × Vec 2 =>
      AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (θM p.1) p.2) 0) 2 _
    rw [this]
    exact (hDM 1).neg
  · have : (fun p : ℝ × Vec 2 => AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (θM p.1) p.2) 1) =
        fun p => AVenhance.spaceGrad (θM p.1) p.2 0 :=
      funext fun p => sigmaMat_mulVec_apply_one _
    change MemLp (fun p : ℝ × Vec 2 =>
      AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (θM p.1) p.2) 1) 2 _
    rw [this]
    exact hDM 0

/-- RelativeError item 12 (stream form, 9294–9330): a weak solution for the limit drift `b = σ∇φ`
    and the
classical solution for a smooth stream `Ψ` with the same datum and diffusivity are `η/κ`-close in
dissipation whenever `|φ − Ψ| ≤ η` on the spacetime cell. -/
theorem stream_difference_energy {b : ℝ → Vec 2 → Vec 2}
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (b t))
    (hdiv : AVenhance.IsDivFree b)
    {φ : ℝ → Vec 2 → ℝ}
    (hφ_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => φ p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hφ_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (φ t))
    (hφ_diff : ∀ t ∈ Set.Icc (0 : ℝ) 1, Differentiable ℝ (φ t))
    (hbφ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, b t x = AVenhance.streamVel φ t x)
    {Ψ : ℝ → Vec 2 → ℝ} (hΨ : AVenhance.IsAdmissibleStream Ψ) {κ : ℝ} (hκ : 0 < κ)
    {g : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (_hgp : AVenhance.IsZ2Periodic g)
    {θM : ℝ → Vec 2 → ℝ}
    (hθM : AVenhance.IsClassicalSol (AVenhance.streamVel Ψ) κ (fun _ _ => 0) g θM)
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : AVenhance.IsWeakSolutionGrad b κ g θ Dθ)
    {η : ℝ} (hη : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, |φ t x - Ψ t x| ≤ η) :
    Real.sqrt κ * Real.sqrt (AVenhance.spaceTimeGradNormSq
        (fun t x => Dθ t x - AVenhance.spaceGrad (θM t) x)) ≤
      (η / κ) * (Real.sqrt κ * Real.sqrt (AVenhance.spaceTimeGradNormSq
        (fun t x => AVenhance.spaceGrad (θM t) x))) := by
  classical
  have hbM : Continuous (fun p : ℝ × Vec 2 => AVenhance.streamVel Ψ p.1 p.2) :=
    (AVenhance.Infra.Classical.streamVel_smoothPeriodic Ψ hΨ).smooth.continuous
  have hM := classical_isWeakSolutionGrad hbM hθM
  have hg2 : MemL2On AVenhance.unitCube g := weak_continuous_memL2On hg.continuous
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 0 ⟨le_rfl, zero_le_one⟩ 0)
  have hDM : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (θM p.1) p.2 i) 2
      (volume.restrict AVenhance.timeCube) := hM.2.2.2.1
  -- the flux `F = (φ - Ψ) σ ∇θ_M`
  let F : ℝ × Vec 2 → Vec 2 := fun p i => (φ p.1 p.2 - Ψ p.1 p.2) *
    AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (θM p.1) p.2) i
  have hmeasξ : AEStronglyMeasurable (fun p : ℝ × Vec 2 => φ p.1 p.2 - Ψ p.1 p.2)
      (volume.restrict AVenhance.timeCube) := by
    have hsub : AVenhance.timeCube ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ :=
      fun p hp => ⟨⟨hp.1.1.le, hp.1.2.le⟩, trivial⟩
    have h1 := hφ_meas.mono_measure (Measure.restrict_mono hsub le_rfl)
    have h2 : Continuous (fun p : ℝ × Vec 2 => Ψ p.1 p.2) := hΨ.1.continuous
    exact h1.sub h2.aestronglyMeasurable
  have hξae : ∀ᵐ p ∂(volume.restrict AVenhance.timeCube), |φ p.1 p.2 - Ψ p.1 p.2| ≤ η := by
    filter_upwards [ae_restrict_mem forced_timeCube_measurable] with p hp
    exact hη p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2
  have hF : ∀ i : Fin 2, MemLp (fun p => F p i) 2 (volume.restrict AVenhance.timeCube) := by
    intro i
    have hσ := sigma_gradient_memLp hDM i
    refine MemLp.of_le_mul (c := η) hσ (hmeasξ.mul hσ.aestronglyMeasurable) ?_
    filter_upwards [hξae] with p hp
    change ‖(φ p.1 p.2 - Ψ p.1 p.2) *
      AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (θM p.1) p.2) i‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)
  have hflux : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      AVenhance.IsZ2Periodic ψ →
      Integrable (fun x => vecDot (b s x - AVenhance.streamVel Ψ s x)
        (AVenhance.spaceGrad (θM s) x) * ψ x) (volume.restrict AVenhance.unitCube) ∧
      ∫ x in AVenhance.unitCube,
          vecDot (b s x - AVenhance.streamVel Ψ s x) (AVenhance.spaceGrad (θM s) x) * ψ x =
        ∫ x in AVenhance.unitCube, vecDot (F (s, x)) (AVenhance.spaceGrad ψ x) := by
    intro s hs ψ hψ hψp
    obtain ⟨C, hC⟩ := hb_bdd
    have hCs : ∀ x, ‖AVenhance.streamVel φ s x‖ ≤ C := fun x => by
      rw [← hbφ s hs x]
      exact hC s hs x
    have hbs : ∀ x, b s x = AVenhance.streamVel φ s x := hbφ s hs
    have key := stream_flux_slice (Ψ := Ψ) (hφ_diff s hs) (hφ_per s hs) hCs hΨ
      (AVenhance.Infra.Section5.classicalSol_space_contDiff_of_nonneg hθM hs.1)
      (hθM.2.1 s hs.1) hψ hψp
    simp only [hbs]
    exact key
  have hid : AVenhance.l2NormSq (fun x => θ 1 x - θM 1 x) +
      2 * κ * (∫ p in AVenhance.timeCube,
        vecDot (Dθ p.1 p.2 - AVenhance.spaceGrad (θM p.1) p.2)
          (Dθ p.1 p.2 - AVenhance.spaceGrad (θM p.1) p.2)) =
      -2 * ∫ p in AVenhance.timeCube,
        vecDot (F p) (Dθ p.1 p.2 - AVenhance.spaceGrad (θM p.1) p.2) :=
    difference_energy_identity (DM := fun t x => AVenhance.spaceGrad (θM t) x) hθ hM hg2
      hb_meas hb_bdd hb_per hdiv hF hflux (t := 1) ⟨zero_le_one, le_rfl⟩
  -- integrability
  set Dw : ℝ × Vec 2 → Vec 2 := fun p => Dθ p.1 p.2 - AVenhance.spaceGrad (θM p.1) p.2 with hDw
  have hDwL : ∀ i : Fin 2, MemLp (fun p => Dw p i) 2 (volume.restrict AVenhance.timeCube) :=
    fun i => (hθ.2.2.2.1 i).sub (hDM i)
  have hDMp : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (θM p.1) p.2 i) 2
      (volume.restrict AVenhance.timeCube) := hDM
  have hFF := forced_vecDot_integrable_fields (Y := F) (Z := F) hF hF
  have hFD := forced_vecDot_integrable_fields (Y := F) (Z := Dw) hF hDwL
  have hDD := forced_vecDot_integrable_fields (Y := Dw) (Z := Dw) hDwL hDwL
  have hMM := forced_vecDot_integrable_fields
    (Y := fun p : ℝ × Vec 2 => AVenhance.spaceGrad (θM p.1) p.2)
    (Z := fun p : ℝ × Vec 2 => AVenhance.spaceGrad (θM p.1) p.2) hDMp hDMp
  -- Cauchy–Schwarz
  have hcs := sq_integral_le_of_quadratic_nonneg hFF hFD hDD (Filter.Eventually.of_forall fun p l
      => by
    simp only [vecDot, Fin.sum_univ_two]
    nlinarith [sq_nonneg (l * F p 0 + Dw p 0), sq_nonneg (l * F p 1 + Dw p 1)])
  -- the flux is controlled by `η ∇θ_M`
  have hE : (∫ p in AVenhance.timeCube, vecDot (F p) (F p)) ≤
      η ^ 2 * ∫ p in AVenhance.timeCube, vecDot (AVenhance.spaceGrad (θM p.1) p.2)
        (AVenhance.spaceGrad (θM p.1) p.2) := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => ?_) (hMM.const_mul _) ?_
    · simp only [vecDot, Fin.sum_univ_two, Pi.zero_apply]
      exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    · filter_upwards [hξae] with p hp
      have hsq : (φ p.1 p.2 - Ψ p.1 p.2) ^ 2 ≤ η ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hp 2
      simp only [F, vecDot, Fin.sum_univ_two, sigmaMat_mulVec_apply_zero,
        sigmaMat_mulVec_apply_one]
      nlinarith [mul_le_mul_of_nonneg_right hsq
        (add_nonneg (sq_nonneg (AVenhance.spaceGrad (θM p.1) p.2 0))
          (sq_nonneg (AVenhance.spaceGrad (θM p.1) p.2 1)))]
  have hA : 0 ≤ ∫ p in AVenhance.timeCube, vecDot (Dw p) (Dw p) :=
    integral_nonneg fun p => by
      simp only [vecDot, Fin.sum_univ_two, Pi.zero_apply]
      exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hl : 0 ≤ AVenhance.l2NormSq (fun x => θ 1 x - θM 1 x) :=
    integral_nonneg fun x => sq_nonneg _
  exact stream_final_real hκ hη0 hA hl hid hcs hE

end AVenhance.Infra.Section5.RelativeError

end
