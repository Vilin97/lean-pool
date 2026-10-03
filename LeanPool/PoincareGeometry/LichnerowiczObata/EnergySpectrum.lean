/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.CompactEnergy
public import LeanPool.PoincareGeometry.LichnerowiczObata.CompactSpectral
public import LeanPool.PoincareGeometry.LichnerowiczObata.NontrivialEnergy
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyL2Injectivity
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyGreen
public import LeanPool.PoincareGeometry.LichnerowiczObata.BochnerBound

/-! # The compact Gram operator of the manifold energy realization -/

@[expose] public noncomputable section
open Bundle Set MeasureTheory AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [Nonempty M] [LindelofSpace M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace M := borel M
local instance : BorelSpace M := ⟨rfl⟩

local notation "W" => (EnergyCompletion (I := I) (M := M))
local notation "J" => (energyCompletionToL2 (I := I) (M := M))

/-- The Gram operator uses the actual volume realization and the actual
completed Dirichlet inner product. -/
def energyGram : W →L[ℝ] W := (J).adjoint.comp J

theorem energyGram_inner (u v : W) :
    inner ℝ (energyGram u) v = inner ℝ (J u) (J v) :=
  ContinuousLinearMap.adjoint_inner_left J v (J u)

theorem energyGram_symmetric : (energyGram (I := I) (M := M)).IsSymmetric := by
  intro u v
  change inner ℝ (energyGram u) v = inner ℝ u (energyGram v)
  rw [energyGram_inner]
  exact (ContinuousLinearMap.adjoint_inner_right J u (J v)).symm

theorem energyGram_nonneg (u : W) : 0 ≤ inner ℝ u (energyGram u) := by
  rw [real_inner_comm, energyGram_inner]
  exact real_inner_self_nonneg

theorem energyGram_compact : IsCompactOperator (energyGram (I := I) (M := M)) :=
  compact_energy_realization.clm_comp (J).adjoint

theorem energyGram_injective : Function.Injective (energyGram (I := I) (M := M)) :=
  (J).adjoint_comp_self_injective_iff.mpr energyCompletionToL2_injective

/-- Spectral attainment for the actual manifold Gram operator once the
mean-zero energy space is nontrivial. Smooth regularity remains separate. -/
theorem exists_largest_energy_eigenvalue (hd : 0 < Module.finrank ℝ E) :
    ∃ r : ℝ, 0 < r ∧ Module.End.HasEigenvalue
      (energyGram (I := I) (M := M)).toLinearMap r ∧
      ∀ s : ℝ, Module.End.HasEigenvalue
        (energyGram (I := I) (M := M)).toLinearMap s → s ≤ r := by
  let : Nontrivial W := nontrivial_energyCompletion (I := I) hd
  apply exists_largest_positive_eigenvalue _ energyGram_compact
    energyGram_symmetric energyGram_nonneg
  intro hz
  have hinj := energyGram_injective (I := I) (M := M)
  have hall : ∀ u : W, u = 0 := by
    intro u
    apply hinj
    rw [hz]
    rfl
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  exact hu (hall u)

/-- A nonzero variational eigenfunction exists in the actual energy completion.
Its positive eigenvalue is the reciprocal of the largest Gram eigenvalue. -/
theorem exists_positive_variational_eigenpair (hd : 0 < Module.finrank ℝ E) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ u : W, J u ≠ 0 ∧
      ∀ v : W, inner ℝ u v = μ * inner ℝ (J u) (J v) := by
  obtain ⟨r, hr, heig, _⟩ := exists_largest_energy_eigenvalue (I := I) (M := M) hd
  obtain ⟨u, hu, hu0⟩ := heig.exists_hasEigenvector
  have heq : energyGram u = r • u := by
    simpa only [Module.End.mem_genEigenspace_one, ContinuousLinearMap.coe_coe] using hu
  refine ⟨r⁻¹, inv_pos.mpr hr, u, ?_, ?_⟩
  · intro hz
    apply hu0
    apply energyCompletionToL2_injective (I := I) (M := M)
    simpa using hz
  · intro v
    have hi := energyGram_inner u v
    rw [heq, real_inner_smul_left] at hi
    rw [← hi]
    field_simp

/-- Any positive variational eigenvalue corresponds to a reciprocal Gram eigenvalue. -/
theorem gram_eigenvalue_of_variational {μ : ℝ} (hμ : 0 < μ)
    {u : W} (hu : J u ≠ 0)
    (hvar : ∀ v : W, inner ℝ u v = μ * inner ℝ (J u) (J v)) :
    Module.End.HasEigenvalue (energyGram (I := I) (M := M)).toLinearMap μ⁻¹ := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := u)
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_genEigenspace_one]
    change energyGram u = μ⁻¹ • u
    apply ext_inner_right ℝ
    intro v
    rw [energyGram_inner, real_inner_smul_left, hvar]
    field_simp
  · intro h
    apply hu
    simp [h]

/-- The first positive variational eigenvalue is attained. This is stated
on the actual energy completion; a classical smooth representative is not
yet part of this theorem. -/
theorem exists_first_variational_eigenpair (hd : 0 < Module.finrank ℝ E) :
    ∃ μ : ℝ, 0 < μ ∧
      (∃ u : W, J u ≠ 0 ∧ ∀ v : W, inner ℝ u v = μ * inner ℝ (J u) (J v)) ∧
      ∀ s : ℝ, 0 < s →
        (∃ u : W, J u ≠ 0 ∧ ∀ v : W, inner ℝ u v = s * inner ℝ (J u) (J v)) →
        μ ≤ s := by
  obtain ⟨r, hr, heig, hmax⟩ := exists_largest_energy_eigenvalue (I := I) (M := M) hd
  obtain ⟨u, hu, hu0⟩ := heig.exists_hasEigenvector
  have heq : energyGram u = r • u := by
    simpa only [Module.End.mem_genEigenspace_one, ContinuousLinearMap.coe_coe] using hu
  refine ⟨r⁻¹, inv_pos.mpr hr, ⟨u, ?_, ?_⟩, ?_⟩
  · intro hz
    apply hu0
    apply energyCompletionToL2_injective (I := I) (M := M)
    simpa using hz
  · intro v
    have hi := energyGram_inner u v
    rw [heq, real_inner_smul_left] at hi
    rw [← hi]
    field_simp
  · intro s hs hv
    obtain ⟨w, hw, hvar⟩ := hv
    have hle := hmax s⁻¹ (gram_eigenvalue_of_variational hs hw hvar)
    exact (inv_le_comm₀ hr hs).mpr hle

/-- The L² realization pairs with a mean-corrected smooth test exactly as
with the original test, since it has zero integral. -/
theorem realization_inner_meanCorrected (u : W) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    inner ℝ (J u) (J (energyToCompletion (meanCorrectedEnergyTest f hf))) =
      ∫ x, J u x * f x ∂riemannianVolume (I := I) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, J u x * (meanCorrectedEnergyTest f hf).val x
        ∂riemannianVolume (I := I) := by
      apply integral_congr_ae
      filter_upwards [energyCompletionToL2_core_ae_eq (meanCorrectedEnergyTest f hf)] with x hx
      simp only [RCLike.inner_apply, conj_trivial, hx, mul_comm]
    _ = _ := integral_forcing_meanCorrectedEnergyTest (J u)
      (integral_energyCompletionToL2 u) f hf

/-- Identify an energy eigenvector with the existing variational Poisson
solution. The forcing is initially L², not assumed smooth. -/
theorem variational_eq_weakPoisson {μ : ℝ} {u : W}
    (hvar : ∀ v : W, inner ℝ u v = μ * inner ℝ (J u) (J v)) :
    u = weakPoissonSolution (-μ • J u) := by
  apply ext_inner_right ℝ
  intro v
  rw [weakPoissonSolution_inner, real_inner_smul_left, hvar]
  ring

/-- Every variational eigenvector solves the transposed geometric equation. -/
theorem variational_laplacian_test {μ : ℝ} {u : W}
    (hvar : ∀ v : W, inner ℝ u v = μ * inner ℝ (J u) (J v))
    (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ, ℝ) 2 φ) :
    (∫ x, J u x * laplacian (leviCivitaConnection (I := I)) φ x
      ∂riemannianVolume (I := I)) =
      -μ * (∫ x, J u x * φ x ∂riemannianVolume (I := I)) := by
  have hg := integral_energyCompletionToL2_mul_laplacian (leviCivitaConnection (I := I))
    leviCivitaConnection_metricCompatible leviCivitaConnection_torsion u φ hφ
  rw [hvar, realization_inner_meanCorrected] at hg
  simpa only [neg_mul] using hg

/-- Genuine nonzero mean-zero L² eigenfunction existence for the constructed
Laplace--Beltrami operator, expressed on all C² test functions. -/
theorem exists_weak_laplacian_eigenfunction (hd : 0 < Module.finrank ℝ E) :
    ∃ μ : ℝ, 0 < μ ∧
      ∃ f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)),
        f ≠ 0 ∧ (∫ x, f x ∂riemannianVolume (I := I)) = 0 ∧
        ∀ φ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) 2 φ →
          (∫ x, f x * laplacian (leviCivitaConnection (I := I)) φ x
            ∂riemannianVolume (I := I)) =
          -μ * (∫ x, f x * φ x ∂riemannianVolume (I := I)) := by
  obtain ⟨μ, hμ, ⟨u, hu, hvar⟩, _⟩ := exists_first_variational_eigenpair (I := I) (M := M) hd
  refine ⟨μ, hμ, J u, hu, integral_energyCompletionToL2 u, ?_⟩
  exact variational_laplacian_test hvar

end LichnerowiczObata
