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

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyL2Completion
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyCompactness

/-! # Compactness of the completed energy realization

Factor the genuine energy completion through the chart H¹ graph. The bound
on the core is proved from localization and Poincaré, and the factorization
on the completion follows by density.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory AlmostSchur
open scoped Manifold ContDiff Topology
open RellichKondrachov.Geometry.Manifold.Sobolev FiniteChartData

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
local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)
local instance : IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

local notation "ν" => (riemannianVolume (I := I) (M := M))

/-- Forget the mean-zero constraint without changing the underlying function. -/
def energyCoreToC1 : EnergySpace (I := I) (M := M) →ₗ[ℝ] ↥(C1 (I := I) (M := M)) where
  toFun f := ⟨f.val, f.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual core graph map, before using its energy-norm bound. -/
def energyCoreToH1Linear (d : FiniteChartData (H := H) (M := M) I) :
    EnergySpace (I := I) (M := M) →ₗ[ℝ] ↥(h1 (d := d) ν) :=
  (c1ToH1 (d := d) ν).comp energyCoreToC1

theorem exists_energyCoreToH1_bound (d : FiniteChartData (H := H) (M := M) I) :
    ∃ C : ℝ, ∀ f : EnergySpace (I := I) (M := M),
      ‖energyCoreToH1Linear d f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hb⟩ := exists_norm_c1ToH1_le_energy_toLp d
  refine ⟨C * (energyL2Constant (I := I) (M := M) + 1), fun f => ?_⟩
  have h := hb (energyCoreToC1 f) (memLp_c1_riemannianVolume f.property.1)
  change ‖energyCoreToH1Linear d f‖ ≤ C * (‖energyToL2Linear f‖ +
    Real.sqrt (dirichletForm (I := I) f.val f.val)) at h
  rw [← energySpace_norm f] at h
  have hL := energyToL2Linear_norm_le f
  nlinarith

/-- Bounded map from the energy core to the actual chart graph. -/
def energyCoreToH1 (d : FiniteChartData (H := H) (M := M) I) :
    EnergySpace (I := I) (M := M) →L[ℝ] ↥(h1 (d := d) ν) :=
  (energyCoreToH1Linear d).mkContinuous (exists_energyCoreToH1_bound d).choose
    (exists_energyCoreToH1_bound d).choose_spec

/-- Extend the graph map to the Hilbert energy completion. -/
def energyCompletionToH1 (d : FiniteChartData (H := H) (M := M) I) :
    EnergyCompletion (I := I) (M := M) →L[ℝ] ↥(h1 (d := d) ν) :=
  (energyCoreToH1 d).extend (energyToCompletion (I := I) (M := M)).toContinuousLinearMap

theorem energyCompletionToH1_core (d : FiniteChartData (H := H) (M := M) I)
    (f : EnergySpace (I := I) (M := M)) :
    energyCompletionToH1 d (energyToCompletion f) = energyCoreToH1Linear d f := by
  exact (energyCoreToH1 d).extend_eq
    (e := (energyToCompletion (I := I) (M := M)).toContinuousLinearMap)
    denseRange_energyToCompletion (energyToCompletion (I := I)).isometry.isUniformInducing f

/-- Reconstruction of the extended graph is exactly the existing L² realization. -/
theorem energyCompletionToL2_factorization (d : FiniteChartData (H := H) (M := M) I) :
    (h1ToL2 (d := d) ν).comp (energyCompletionToH1 d) =
      energyCompletionToL2 (I := I) (M := M) := by
  apply ContinuousLinearMap.ext
  intro u
  refine (denseRange_energyToCompletion (I := I) (M := M)).induction_on
    (p := fun u => h1ToL2 (d := d) ν (energyCompletionToH1 d u) =
      energyCompletionToL2 u) u ?_ ?_
  · exact isClosed_eq ((h1ToL2 (d := d) ν).continuous.comp
      (energyCompletionToH1 d).continuous) energyCompletionToL2.continuous
  · intro f
    rw [energyCompletionToH1_core, energyCompletionToL2_core]
    apply Lp.ext
    exact (h1ToL2_c1ToH1_ae_eq d ν (energyCoreToC1 f)).trans
      (energyToL2Linear_ae_eq f).symm

/-- Rellich compactness now holds on the genuine completed energy space. -/
theorem isCompactOperator_energyCompletionToL2
    (d : FiniteChartData (H := H) (M := M) I) :
    IsCompactOperator (energyCompletionToL2 (I := I) (M := M)) := by
  rw [← energyCompletionToL2_factorization d]
  exact (isCompactOperator_sobolevH1ToL2 d).comp_clm (energyCompletionToH1 d)

/-- Compactness requires no supplied atlas: compactness provides the finite chart data. -/
theorem compact_energy_realization :
    IsCompactOperator (energyCompletionToL2 (I := I) (M := M)) := by
  obtain ⟨d⟩ := exists_finiteChartData_chartAt (I := I) (M := M)
  exact isCompactOperator_energyCompletionToL2 d

end LichnerowiczObata
