/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyPairing

/-!
# Forced energy identity from the mode-path form

If a path satisfies the Fourier mode-path form of the forced weak equation and its finite Fourier
projections converge in spacetime `H¹`, the exact forced energy identity holds at every time.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Parabolic.WeakUniqueness

local instance forcedIdentityFiniteUnitCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  unfold AVenhance.unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance forcedIdentityFiniteTimeCube :
    IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [forced_timeCube_measure_eq_product]
  infer_instance

/-- Energy of the finite Fourier projection of an `L²` slice tends to the slice energy. -/
theorem forced_coefficient_normSq_tendsto {u : ℝ → Vec 2 → ℝ} {t : ℝ}
    (hu : MemL2On AVenhance.unitCube (u t)) :
    Tendsto (fun N => ‖weakFourierCoefficientPath N u t‖ ^ 2) atTop
      (𝓝 (AVenhance.l2NormSq (u t))) := by
  have hprojection := weakFourierProjectionL2_tendsto hu
  have hnorm := (continuous_norm.pow 2).continuousAt.tendsto.comp hprojection
  have hlimit := weakProjection_scalarTransfer_normSq hu
  change Tendsto (fun N => ‖weakFourierProjectionL2 N u t‖ ^ 2) atTop
    (𝓝 (‖(weakProjection_realCellToTorus_memLp hu).toLp
      (AVenhance.Infra.Torus.periodicToTorus (u t))‖ ^ 2)) at hnorm
  rw [hlimit] at hnorm
  refine hnorm.congr fun N => ?_
  rw [weakFourierProjectionL2, realFourierScalarMap_norm]

/-- The initial Fourier coefficients of a forced path are those of its datum. -/
theorem forced_initial_coefficients
    {κ : ℝ} {f : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    {G : ℝ × Vec 2 → ℝ} {F : ℝ × Vec 2 → Vec 2}
    (h : ForcedModePath κ f u Du G F) (N : ℕ) :
    weakFourierCoefficientPath N u 0 = weakFourierCoefficientPath N (fun _ x => f x) 0 := by
  ext i
  have := h.path _ (forcedMode_smooth N i) (forcedMode_periodic N i) 0 ⟨le_rfl, by norm_num⟩
  simpa [weakFourierCoefficientPath, weakModePairing, forcedMode] using this

/-- Exact forced energy identity for a path with forced mode paths whose finite Fourier
projections converge in spacetime `H¹`. -/
theorem forced_energy_of_mode_path
    {κ : ℝ} {f : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    {G : ℝ × Vec 2 → ℝ} {F : ℝ × Vec 2 → Vec 2}
    (h : ForcedModePath κ f u Du G F) (hf : MemL2On AVenhance.unitCube f)
    (hproj : Tendsto (fun N => ∫ p in AVenhance.timeCube,
      (u p.1 p.2 - weakFourierModeProjection N u p.1 p.2) ^ 2) atTop (𝓝 0))
    (hprojGrad : ∀ i : Fin 2, Tendsto (fun N => ∫ p in AVenhance.timeCube,
      (Du p.1 p.2 i - AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 i) ^ 2)
      atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AVenhance.l2NormSq (u t) + 2 * (∫ p in weakEnergyRegion t,
      (G p * u p.1 p.2 + κ * Homogenization.vecDot (Du p.1 p.2) (Du p.1 p.2) +
        Homogenization.vecDot (F p) (Du p.1 p.2))) = AVenhance.l2NormSq f := by
  let hregion : weakEnergyRegion t ⊆ AVenhance.timeCube := weakEnergy_region_subset_timeCube ht
  have hμ : volume.restrict (weakEnergyRegion t) ≤ volume.restrict AVenhance.timeCube :=
    Measure.restrict_mono hregion le_rfl
  -- limiting integrand
  let Φ : ℝ × Vec 2 → ℝ := fun p => G p * u p.1 p.2 +
    κ * Homogenization.vecDot (Du p.1 p.2) (Du p.1 p.2) +
      Homogenization.vecDot (F p) (Du p.1 p.2)
  -- errors
  let e0 : ℕ → ℝ × Vec 2 → ℝ := fun N p => u p.1 p.2 - weakFourierModeProjection N u p.1 p.2
  let e1 : ℕ → Fin 2 → ℝ × Vec 2 → ℝ := fun N j p =>
    Du p.1 p.2 j - AVenhance.spaceGrad (weakFourierModeProjection N u p.1) p.2 j
  have he0 (N : ℕ) : MemLp (e0 N) 2 (volume.restrict AVenhance.timeCube) :=
    h.memLp.sub (forced_projection_memLp h N)
  have he1 (N : ℕ) (j : Fin 2) : MemLp (e1 N j) 2 (volume.restrict AVenhance.timeCube) :=
    (h.grad_memLp j).sub (forced_projection_grad_memLp h N j)
  have hint (a b : ℝ × Vec 2 → ℝ) (ha : MemLp a 2 (volume.restrict AVenhance.timeCube))
      (hb : MemLp b 2 (volume.restrict AVenhance.timeCube)) :
      Integrable (fun p => a p * b p) (volume.restrict (weakEnergyRegion t)) :=
    (weak_product_integrable_timeCube ha hb).mono_measure hμ
  -- the three kinds of products tend to zero
  have hG0 : Tendsto (fun N => ∫ p in weakEnergyRegion t, G p * e0 N p) atTop (𝓝 0) :=
    weakEnergy_pairing_error_tendsto_on_region h.G_memLp e0 he0 hproj ht
  have hDu0 (j : Fin 2) : Tendsto (fun N => ∫ p in weakEnergyRegion t,
      Du p.1 p.2 j * e1 N j p) atTop (𝓝 0) :=
    weakEnergy_pairing_error_tendsto_on_region (h.grad_memLp j) (fun N => e1 N j)
      (fun N => he1 N j) (hprojGrad j) ht
  have hF0 (j : Fin 2) : Tendsto (fun N => ∫ p in weakEnergyRegion t,
      F p j * e1 N j p) atTop (𝓝 0) :=
    weakEnergy_pairing_error_tendsto_on_region (h.F_memLp j) (fun N => e1 N j)
      (fun N => he1 N j) (hprojGrad j) ht
  -- error integrand
  let E : ℕ → ℝ × Vec 2 → ℝ := fun N p => G p * e0 N p +
    κ * ∑ j : Fin 2, Du p.1 p.2 j * e1 N j p + ∑ j : Fin 2, F p j * e1 N j p
  have hEint (N : ℕ) : ∫ p in weakEnergyRegion t, E N p =
      (∫ p in weakEnergyRegion t, G p * e0 N p) +
        κ * ∑ j : Fin 2, (∫ p in weakEnergyRegion t, Du p.1 p.2 j * e1 N j p) +
        ∑ j : Fin 2, ∫ p in weakEnergyRegion t, F p j * e1 N j p := by
    have h1 := hint G (e0 N) h.G_memLp (he0 N)
    have h2 (j : Fin 2) := hint (fun p => Du p.1 p.2 j) (e1 N j) (h.grad_memLp j) (he1 N j)
    have h3 (j : Fin 2) := hint (fun p => F p j) (e1 N j) (h.F_memLp j) (he1 N j)
    have hA := (integrable_finsetSum (s := (Finset.univ : Finset (Fin 2)))
      fun j _ => h2 j).const_mul κ
    have hB := integrable_finsetSum (s := (Finset.univ : Finset (Fin 2))) fun j _ => h3 j
    have step1 : ∫ p in weakEnergyRegion t, E N p =
        (∫ p in weakEnergyRegion t, (G p * e0 N p +
          κ * ∑ j : Fin 2, Du p.1 p.2 j * e1 N j p)) +
          ∫ p in weakEnergyRegion t, ∑ j : Fin 2, F p j * e1 N j p :=
      integral_add (h1.add hA) hB
    have step2 : ∫ p in weakEnergyRegion t, (G p * e0 N p +
          κ * ∑ j : Fin 2, Du p.1 p.2 j * e1 N j p) =
        (∫ p in weakEnergyRegion t, G p * e0 N p) +
          ∫ p in weakEnergyRegion t, κ * ∑ j : Fin 2, Du p.1 p.2 j * e1 N j p :=
      integral_add h1 hA
    rw [step1, step2, integral_const_mul, integral_finsetSum _ fun j _ => h2 j,
      integral_finsetSum _ fun j _ => h3 j]
  have hEtendsto : Tendsto (fun N => ∫ p in weakEnergyRegion t, E N p) atTop (𝓝 0) := by
    have := (hG0.add ((tendsto_finsetSum (Finset.univ : Finset (Fin 2))
      fun j _ => hDu0 j).const_mul κ)).add
      (tendsto_finsetSum (Finset.univ : Finset (Fin 2)) fun j _ => hF0 j)
    simp only [Finset.sum_const_zero, mul_zero, add_zero] at this
    exact this.congr fun N => (hEint N).symm
  -- limiting integrand integrable on the region
  have hΦint : Integrable Φ (volume.restrict (weakEnergyRegion t)) := by
    have h1 := hint G (fun p => u p.1 p.2) h.G_memLp h.memLp
    have hdot (Y : ℝ × Vec 2 → Vec 2)
        (hY : ∀ i : Fin 2, MemLp (fun p => Y p i) 2 (volume.restrict AVenhance.timeCube)) :
        Integrable (fun p => Homogenization.vecDot (Y p) (Du p.1 p.2))
          (volume.restrict (weakEnergyRegion t)) := by
      have := integrable_finsetSum (s := (Finset.univ : Finset (Fin 2))) fun j _ =>
        hint (fun p => Y p j) (fun p => Du p.1 p.2 j) (hY j) (h.grad_memLp j)
      simpa only [Homogenization.vecDot] using this
    exact (h1.add ((hdot (fun p => Du p.1 p.2) h.grad_memLp).const_mul κ)).add
      (hdot F h.F_memLp)
  have hΦNint (N : ℕ) : Integrable (forcedProjectionPairing κ Du G F u N) (volume.restrict
      (weakEnergyRegion t)) :=
    (forcedProjectionPairing_integrable h N).mono_measure hμ
  -- Φ - Φ_N = E_N
  have hΦsub (N : ℕ) : ∀ p, Φ p - forcedProjectionPairing κ Du G F u N p = E N p := by
    intro p
    simp only [Φ, E, e0, e1, forcedProjectionPairing, Homogenization.vecDot, Fin.sum_univ_two]
    ring
  have hΦNlim : Tendsto (fun N => ∫ p in weakEnergyRegion t,
      forcedProjectionPairing κ Du G F u N p) atTop (𝓝 (∫ p in weakEnergyRegion t, Φ p)) := by
    have hEq (N : ℕ) : ∫ p in weakEnergyRegion t, forcedProjectionPairing κ Du G F u N p =
        (∫ p in weakEnergyRegion t, Φ p) - ∫ p in weakEnergyRegion t, E N p := by
      have hs : ∫ p in weakEnergyRegion t, (Φ p - forcedProjectionPairing κ Du G F u N p) =
          (∫ p in weakEnergyRegion t, Φ p) -
            ∫ p in weakEnergyRegion t, forcedProjectionPairing κ Du G F u N p :=
        integral_sub hΦint (hΦNint N)
      have hE : ∫ p in weakEnergyRegion t, (Φ p - forcedProjectionPairing κ Du G F u N p) =
          ∫ p in weakEnergyRegion t, E N p :=
        integral_congr_ae (Eventually.of_forall fun p => hΦsub N p)
      linarith
    have := (tendsto_const_nhds (x := ∫ p in weakEnergyRegion t, Φ p)).sub hEtendsto
    simp only [sub_zero] at this
    exact this.congr fun N => (hEq N).symm
  -- finite identities
  have hfinite (N : ℕ) : ‖weakFourierCoefficientPath N u t‖ ^ 2 +
      2 * ∫ p in weakEnergyRegion t, forcedProjectionPairing κ Du G F u N p =
      ‖weakFourierCoefficientPath N u 0‖ ^ 2 := by
    have h1 := forced_finite_fourier_energy h N ht
    rw [forced_pairing h N ht, integral_const_mul] at h1
    exact h1
  have hLHS : Tendsto (fun N => ‖weakFourierCoefficientPath N u t‖ ^ 2 +
      2 * ∫ p in weakEnergyRegion t, forcedProjectionPairing κ Du G F u N p) atTop
      (𝓝 (AVenhance.l2NormSq (u t) + 2 * ∫ p in weakEnergyRegion t, Φ p)) :=
    (forced_coefficient_normSq_tendsto (h.slice_mem t ht)).add (hΦNlim.const_mul 2)
  have hRHS : Tendsto (fun N => ‖weakFourierCoefficientPath N u 0‖ ^ 2) atTop
      (𝓝 (AVenhance.l2NormSq f)) := by
    have := forced_coefficient_normSq_tendsto (u := fun _ x => f x) (t := 0) hf
    refine this.congr fun N => ?_
    rw [forced_initial_coefficients h N]
  have := tendsto_nhds_unique (hLHS.congr hfinite) hRHS
  exact this

end AVenhance.Infra.Section5.RelativeError

end
