/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.TransportLimit.DriftData
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra

/-!
# Weak solutions satisfy the divergence-form transport identity up to the viscous term

For `θ` a weak solution of the advection-diffusion equation with divergence-free drift `b` and
every test function `φ`,
`∫∫ (-θ ∂ₜφ - θ b·∇φ) = ∫ θ₀ φ(0) - κ ∫∫ Dθ·∇φ`.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

noncomputable section

namespace AVenhance.Infra.FullTheorem.TransportLimit

open AVenhance.Infra.Parabolic.WeakUniqueness

local instance solutionFiniteUnitCube : IsFiniteMeasure (volume.restrict unitCube) := by
  refine ⟨?_⟩
  unfold unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

theorem openCylinder_measure_eq :
    (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec 2)))) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume : Measure (Vec 2)) := by
  have h := Measure.restrict_prod_eq_prod_univ
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Vec 2))) (s := Set.Ioo (0 : ℝ) 1)
  rw [← Measure.volume_eq_prod ℝ (Vec 2)] at h
  exact h.symm

/-- A.e. in time, the drift slice is measurable. -/
theorem DriftHyp.slice_meas {b : ℝ → Vec 2 → Vec 2} (h : DriftHyp b) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      AEStronglyMeasurable (fun x => b t x) volume := by
  have hopen : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec 2)))) :=
    h.meas.mono_measure (Measure.restrict_mono
      (Set.prod_mono Set.Ioo_subset_Icc_self (subset_rfl)) le_rfl)
  rw [openCylinder_measure_eq] at hopen
  exact hopen.prodMk_left

/-- The `b·Dθ φ` pairing integrates to minus the `θ b·∇φ` pairing. -/
theorem drift_pairing_swap {b : ℝ → Vec 2 → Vec 2} (h : DriftHyp b)
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hH1 : ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), IsPeriodicH1With (θ t) (Dθ t))
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsTestFunction φ)
    (iB : Integrable (fun p : ℝ × Vec 2 => vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2)
      (volume.restrict timeCube))
    (iT : Integrable (fun p : ℝ × Vec 2 =>
      θ p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2)) (volume.restrict timeCube)) :
    ∫ p in timeCube, vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2 =
      -∫ p in timeCube, θ p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2) := by
  rw [← integral_neg]
  have iB' := iB
  have iT' := iT
  rw [weakEnergy_timeCube_measure_eq_product] at iB' iT' ⊢
  rw [integral_prod _ iB']
  have iT'' : Integrable (fun p : ℝ × Vec 2 =>
      -(θ p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2)))
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume.restrict unitCube)) := iT'.neg
  rw [integral_prod _ iT'']
  refine integral_congr_ae ?_
  filter_upwards [h.slice_meas, hH1, ae_restrict_mem measurableSet_Ioo] with t hbs hH1t ht
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  obtain ⟨B, hB⟩ := h.bdd
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t htI 0)
  have hφt : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ t x) :=
    hφ.1.comp (contDiff_const.prodMk contDiff_id)
  have := slice_transport_identity hbs ⟨B, hB0, hB t htI⟩ (h.per t htI)
    (fun ψ hψ hc => h.div t htI ψ hψ hc) hH1t hφt (hφ.2.1 t)
  rw [integral_neg]
  exact this

/-- Boundedness of a test function on the space-time cell. -/
theorem test_bound {φ : ℝ → Vec 2 → ℝ} (hφ : IsTestFunction φ) :
    ∃ C : ℝ, ∀ p ∈ timeCube, |φ p.1 p.2| ≤ C := by
  obtain ⟨C, -, hC⟩ := weak_continuous_timeCube_bound hφ.1.continuous
  exact ⟨C, fun p hp => by simpa [Real.norm_eq_abs] using hC p hp⟩

theorem time_derivative_continuous {φ : ℝ → Vec 2 → ℝ} (hφ : IsTestFunction φ) :
    Continuous (fun p : ℝ × Vec 2 => deriv (fun s => φ s p.2) p.1) :=
  (AVenhance.Infra.Parabolic.FourierGalerkin.spacetimeTestTimeDerivative_contDiff
    hφ.1).continuous

/-- The divergence-form identity for a weak solution, with the viscous remainder. -/
theorem solution_transport_form {b : ℝ → Vec 2 → Vec 2} (h : DriftHyp b)
    {κ : ℝ} {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hu : IsWeakSolutionGrad b κ θ₀ θ Dθ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsTestFunction φ) :
    ∫ p in timeCube,
      (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        - θ p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2)) =
      (∫ x in unitCube, θ₀ x * φ 0 x) -
        κ * ∫ p in timeCube, vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2) := by
  have hθ : MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2 (volume.restrict timeCube) := hu.2.2.1
  have hDθ := hu.2.2.2.1
  have hDrift := hu.2.2.2.2.2.1
  have hweak := hu.2.2.2.2.2.2.2 φ hφ
  have hq := time_derivative_continuous hφ
  have hgc := spaceGrad_spacetime_continuous hφ.1
  obtain ⟨Cφ, hCφ⟩ := test_bound hφ
  obtain ⟨Gb, hGm, hGb⟩ := transport_grad_term h hφ
  -- integrability of the pieces
  have iT : Integrable (fun p : ℝ × Vec 2 =>
      θ p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2)) (volume.restrict timeCube) :=
    integrable_mul_bdd_timeCube hθ hGm hGb
  have iA' : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * deriv (fun s => φ s p.2) p.1)
      (volume.restrict timeCube) :=
    weak_product_integrable_timeCube hθ (weak_continuous_memLp_two_timeCube hq)
  have iA : Integrable (fun p : ℝ × Vec 2 => -(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1)
      (volume.restrict timeCube) := by
    simpa [neg_mul] using iA'.neg
  have iB : Integrable (fun p : ℝ × Vec 2 =>
      vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2) (volume.restrict timeCube) := by
    refine hDrift.mul_bdd hφ.1.continuous.measurable.aestronglyMeasurable (c := Cφ) ?_
    filter_upwards [ae_restrict_mem timeCube_measurableSet'] with p hp
    simpa [Real.norm_eq_abs] using hCφ p hp
  have iC : Integrable (fun p : ℝ × Vec 2 => vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2))
      (volume.restrict timeCube) := by
    have hterm (i : Fin 2) : Integrable (fun p : ℝ × Vec 2 =>
        Dθ p.1 p.2 i * spaceGrad (φ p.1) p.2 i) (volume.restrict timeCube) :=
      weak_product_integrable_timeCube (hDθ i)
        (weak_continuous_memLp_two_timeCube ((continuous_apply i).comp hgc))
    exact integrable_finsetSum Finset.univ (fun i _ => hterm i)
  -- split the weak form
  have hs1 := integral_add (μ := volume.restrict timeCube) iA iB
  have hs2 := integral_add (μ := volume.restrict timeCube) (iA.add iB) (iC.const_mul κ)
  have hs3 := integral_const_mul (μ := volume.restrict timeCube) κ
    (fun p : ℝ × Vec 2 => vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2))
  have hswap := drift_pairing_swap h hu.2.2.2.2.1 hφ iB iT
  have hlhs : ∫ p in timeCube,
      (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        - θ p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2)) =
      (∫ p in timeCube, -(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1) -
        ∫ p in timeCube, θ p.1 p.2 * vecDot (b p.1 p.2) (spaceGrad (φ p.1) p.2) :=
    integral_sub iA iT
  rw [hlhs]
  simp only [Pi.add_apply] at hs2
  have hw : ∫ p in timeCube,
      (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
        + κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2)) =
      (∫ p in timeCube, -(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1) +
        (∫ p in timeCube, vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2) +
        κ * ∫ p in timeCube, vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2) := by
    rw [hs2, hs1, hs3]
  rw [hw] at hweak
  linarith

end AVenhance.Infra.FullTheorem.TransportLimit
