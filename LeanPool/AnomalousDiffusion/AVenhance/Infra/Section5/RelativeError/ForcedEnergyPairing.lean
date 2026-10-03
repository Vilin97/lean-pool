/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyFinite

/-!
# Space-time pairing of the finite Fourier projection with forcing

The scalar identity for each Fourier mode is summed and rewritten as one space-time integral
against the finite Fourier projection.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Parabolic.WeakUniqueness

local instance forcedPairingFiniteUnitCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  unfold AVenhance.unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance forcedPairingFiniteTimeCube :
    IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [forced_timeCube_measure_eq_product]
  infer_instance

/-- Clamp of a real time into `[0,1]`. -/
def forcedClamp (t : ℝ) : ℝ := max 0 (min t 1)

theorem forcedClamp_mem (t : ℝ) : forcedClamp t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem forcedClamp_eq {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : forcedClamp t = t := by
  simp [forcedClamp, max_eq_right ht.1, min_eq_left ht.2]

theorem forcedClamp_continuous : Continuous forcedClamp :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The projection of a path is the Fourier polynomial with the coefficient path. -/
theorem forced_projection_expansion (N : ℕ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    weakFourierModeProjection N u t x =
      ∑ i : Fin (RealFourierDimension N), weakModePairing u (forcedMode N i) t *
        forcedMode N i x := by
  simp [weakFourierModeProjection, AVenhance.Infra.Classical.realFourierModeAmbientExpansion,
    weakFourierCoefficientPath, forcedMode]

/-- The projection of a path as a function of space is a finite sum. -/
theorem forced_projection_eq_sum (N : ℕ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) :
    weakFourierModeProjection N u t =
      fun x => ∑ i : Fin (RealFourierDimension N),
        weakModePairing u (forcedMode N i) t * forcedMode N i x := by
  funext x
  exact forced_projection_expansion N u t x

theorem forcedMode_differentiable (N : ℕ) (i : Fin (RealFourierDimension N)) :
    Differentiable ℝ (forcedMode N i) :=
  (forcedMode_smooth N i).differentiable (by simp)

/-- Spatial gradient of the projection. -/
theorem forced_projection_grad_expansion (N : ℕ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2)
    (j : Fin 2) :
    AVenhance.spaceGrad (weakFourierModeProjection N u t) x j =
      ∑ i : Fin (RealFourierDimension N), weakModePairing u (forcedMode N i) t *
        AVenhance.spaceGrad (forcedMode N i) x j := by
  rw [forced_projection_eq_sum]
  unfold AVenhance.spaceGrad
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin (RealFourierDimension N))),
      DifferentiableAt ℝ (fun x => weakModePairing u (forcedMode N i) t * forcedMode N i x) x :=
    fun i _ => ((forcedMode_differentiable N i) x).const_mul _
  rw [fderiv_fun_sum hd]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_const_mul (forcedMode_differentiable N i x)]
  rfl

/-- Continuity of `x ↦ ∂_j ψ` for a smooth `ψ`. -/
theorem forced_spaceGrad_component_continuous {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (j : Fin 2) :
    Continuous (fun x => AVenhance.spaceGrad ψ x j) := by
  have hψone : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  exact ((hψone.continuous_fderiv (by norm_num)).clm_apply continuous_const)

/-- Time-clamped coefficient of a mode is continuous. -/
theorem forced_coeff_clamp_continuous
    {κ : ℝ} {f : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    {G : ℝ × Vec 2 → ℝ} {F : ℝ × Vec 2 → Vec 2}
    (h : ForcedModePath κ f u Du G F) (N : ℕ) (i : Fin (RealFourierDimension N)) :
    Continuous (fun s => weakModePairing u (forcedMode N i) (forcedClamp s)) := by
  have hc := h.weak_cont _ (forcedMode_smooth N i) (forcedMode_periodic N i)
  exact hc.comp_continuous forcedClamp_continuous forcedClamp_mem

/-- The Fourier projection of a forced path is in spacetime `L²`. -/
theorem forced_projection_memLp
    {κ : ℝ} {f : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    {G : ℝ × Vec 2 → ℝ} {F : ℝ × Vec 2 → Vec 2}
    (h : ForcedModePath κ f u Du G F) (N : ℕ) :
    MemLp (fun p : ℝ × Vec 2 => weakFourierModeProjection N u p.1 p.2) 2
      (volume.restrict AVenhance.timeCube) := by
  have hcont : Continuous (fun p : ℝ × Vec 2 =>
      ∑ i : Fin (RealFourierDimension N),
        weakModePairing u (forcedMode N i) (forcedClamp p.1) * forcedMode N i p.2) := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((forced_coeff_clamp_continuous h N i).comp continuous_fst).mul
      ((forcedMode_smooth N i).continuous.comp continuous_snd)
  have hmem := weak_continuous_memLp_two_timeCube hcont
  refine hmem.ae_eq ?_
  filter_upwards [ae_restrict_mem forced_timeCube_measurable] with p hp
  rw [forced_projection_expansion, forcedClamp_eq ⟨hp.1.1.le, hp.1.2.le⟩]

/-- The projected gradient components of a forced path are in spacetime `L²`. -/
theorem forced_projection_grad_memLp
    {κ : ℝ} {f : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    {G : ℝ × Vec 2 → ℝ} {F : ℝ × Vec 2 → Vec 2}
    (h : ForcedModePath κ f u Du G F) (N : ℕ) (j : Fin 2) :
    MemLp (fun p : ℝ × Vec 2 =>
      AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 j) 2
      (volume.restrict AVenhance.timeCube) := by
  have hcont : Continuous (fun p : ℝ × Vec 2 =>
      ∑ i : Fin (RealFourierDimension N),
        weakModePairing u (forcedMode N i) (forcedClamp p.1) *
          AVenhance.spaceGrad (forcedMode N i) p.2 j) := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((forced_coeff_clamp_continuous h N i).comp continuous_fst).mul
      ((forced_spaceGrad_component_continuous (forcedMode_smooth N i) j).comp continuous_snd)
  have hmem := weak_continuous_memLp_two_timeCube hcont
  refine hmem.ae_eq ?_
  filter_upwards [ae_restrict_mem forced_timeCube_measurable] with p hp
  rw [forced_projection_grad_expansion, forcedClamp_eq ⟨hp.1.1.le, hp.1.2.le⟩]

/-- Pointwise mode-sum identity. -/
theorem forced_modeSum_eq (κ : ℝ) (Du : ℝ → Vec 2 → Vec 2) (G : ℝ × Vec 2 → ℝ)
    (F : ℝ × Vec 2 → Vec 2) (u : ℝ → Vec 2 → ℝ) (N : ℕ) (t : ℝ) (x : Vec 2) :
    ∑ i : Fin (RealFourierDimension N), weakModePairing u (forcedMode N i) t *
        forcedModeIntegrand κ Du G F (forcedMode N i) (t, x) =
      G (t, x) * weakFourierModeProjection N u t x +
        κ * Homogenization.vecDot (Du t x)
          (AVenhance.spaceGrad (weakFourierModeProjection N u t) x) +
        Homogenization.vecDot (F (t, x))
          (AVenhance.spaceGrad (weakFourierModeProjection N u t) x) := by
  have hgrad : AVenhance.spaceGrad (weakFourierModeProjection N u t) x =
      fun j => ∑ i : Fin (RealFourierDimension N),
        weakModePairing u (forcedMode N i) t * AVenhance.spaceGrad (forcedMode N i) x j := by
    funext j
    exact forced_projection_grad_expansion N u t x j
  have hdot (Y : Vec 2) : Homogenization.vecDot Y
      (AVenhance.spaceGrad (weakFourierModeProjection N u t) x) =
      ∑ i : Fin (RealFourierDimension N), weakModePairing u (forcedMode N i) t *
        Homogenization.vecDot Y (AVenhance.spaceGrad (forcedMode N i) x) := by
    rw [hgrad]
    simp only [Homogenization.vecDot, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hdot (Du t x), hdot (F (t, x)), forced_projection_expansion, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold forcedModeIntegrand
  ring

/-- The integrand of the space-time pairing against the projection. -/
def forcedProjectionPairing (κ : ℝ) (Du : ℝ → Vec 2 → Vec 2) (G : ℝ × Vec 2 → ℝ)
    (F : ℝ × Vec 2 → Vec 2) (u : ℝ → Vec 2 → ℝ) (N : ℕ) (p : ℝ × Vec 2) : ℝ :=
  G p * weakFourierModeProjection N u p.1 p.2 +
    κ * Homogenization.vecDot (Du p.1 p.2)
      (AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2) +
    Homogenization.vecDot (F p) (AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2)

theorem forcedProjectionPairing_integrable
    {κ : ℝ} {f : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    {G : ℝ × Vec 2 → ℝ} {F : ℝ × Vec 2 → Vec 2}
    (h : ForcedModePath κ f u Du G F) (N : ℕ) :
    Integrable (forcedProjectionPairing κ Du G F u N) (volume.restrict AVenhance.timeCube) := by
  have h1 : Integrable (fun p : ℝ × Vec 2 => G p * weakFourierModeProjection N u p.1 p.2)
      (volume.restrict AVenhance.timeCube) :=
    weak_product_integrable_timeCube h.G_memLp (forced_projection_memLp h N)
  have hdot (Y : ℝ × Vec 2 → Vec 2)
      (hY : ∀ i : Fin 2, MemLp (fun p => Y p i) 2 (volume.restrict AVenhance.timeCube)) :
      Integrable (fun p : ℝ × Vec 2 => Homogenization.vecDot (Y p)
        (AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2))
        (volume.restrict AVenhance.timeCube) := by
    have hterm (j : Fin 2) : Integrable (fun p : ℝ × Vec 2 => Y p j *
        AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 j)
        (volume.restrict AVenhance.timeCube) :=
      weak_product_integrable_timeCube (hY j) (forced_projection_grad_memLp h N j)
    simpa only [Homogenization.vecDot] using integrable_finsetSum Finset.univ (fun j _ => hterm j)
  exact (h1.add ((hdot (fun p => Du p.1 p.2) h.grad_memLp).const_mul κ)).add
    (hdot F h.F_memLp)

/-- Summing the mode energy integrals gives the space-time pairing with the projection. -/
theorem forced_pairing
    {κ : ℝ} {f : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    {G : ℝ × Vec 2 → ℝ} {F : ℝ × Vec 2 → Vec 2}
    (h : ForcedModePath κ f u Du G F) (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ s in (0 : ℝ)..t,
      2 * ∑ i : Fin (RealFourierDimension N),
        weakModePairing u (forcedMode N i) s *
          forcedModeForcing κ Du G F (forcedMode N i) s =
    ∫ p in weakEnergyRegion t, 2 * forcedProjectionPairing κ Du G F u N p := by
  have hint := forcedProjectionPairing_integrable h N
  rw [integral_const_mul, weakEnergy_region_integral_eq_interval hint ht,
    ← intervalIntegral.integral_const_mul]
  -- slice integrability of each mode density, almost everywhere in time
  have hmode (i : Fin (RealFourierDimension N)) :
      Integrable (forcedModeIntegrand κ Du G F (forcedMode N i))
        ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume.restrict AVenhance.unitCube)) := by
    rw [← forced_timeCube_measure_eq_product]
    exact forcedModeIntegrand_integrable h.grad_memLp h.G_memLp h.F_memLp (forcedMode_smooth N i)
  have hslices : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), ∀ i : Fin (RealFourierDimension N),
      Integrable (fun x => forcedModeIntegrand κ Du G F (forcedMode N i) (s, x))
        (volume.restrict AVenhance.unitCube) := by
    rw [ae_all_iff]
    intro i
    exact (hmode i).prod_right_ae
  have hslicesT : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) t)),
      ∀ i : Fin (RealFourierDimension N),
      Integrable (fun x => forcedModeIntegrand κ Du G F (forcedMode N i) (s, x))
        (volume.restrict AVenhance.unitCube) :=
    ae_mono (Measure.restrict_mono (Set.Ioo_subset_Ioo_right ht.2) le_rfl) hslices
  rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine integral_congr_ae ?_
  filter_upwards [hslicesT] with s hs
  congr 1
  have hsum : ∫ x in AVenhance.unitCube, forcedProjectionPairing κ Du G F u N (s, x) =
      ∫ x in AVenhance.unitCube, ∑ i : Fin (RealFourierDimension N),
        weakModePairing u (forcedMode N i) s *
          forcedModeIntegrand κ Du G F (forcedMode N i) (s, x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact (forced_modeSum_eq κ Du G F u N s x).symm
  rw [hsum, integral_finsetSum _ fun i _ => (hs i).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  rfl

end AVenhance.Infra.Section5.RelativeError

end
