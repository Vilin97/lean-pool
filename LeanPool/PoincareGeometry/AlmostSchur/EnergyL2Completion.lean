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

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyL2
public import LeanPool.PoincareGeometry.AlmostSchur.Poincare
public import Mathlib.Analysis.Normed.Operator.Extend

/-! # Bounded L² realization of the energy completion

Poincaré bounds the actual core map, which extends uniquely to complete L².
No injectivity of the completed map is asserted.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

/-- The actual core L² map has a positive uniform energy-norm bound. -/
theorem exists_energyToL2_bound : ∃ C : ℝ, 0 < C ∧
    ∀ f : EnergySpace (I := I) (M := M), ‖energyToL2Linear f‖ ≤ C * ‖f‖ := by
  cases (BorelSpace.measurable_eq (α := E))
  cases (BorelSpace.measurable_eq (α := M))
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨C, hC, hb⟩ := exists_poincare_constant (I := I) (M := M)
  refine ⟨C, hC, fun f => ?_⟩
  change ‖(memLp_c1_riemannianVolume f.property.1).toLp f.val‖ ≤ _
  rw [Lp.norm_toLp, toReal_eLpNorm, energySpace_norm]
  exact hb f.val f.property.1 f.property.2

/-- A chosen proved Poincaré bound for the actual core realization. -/
def energyL2Constant : ℝ := (exists_energyToL2_bound (I := I) (M := M)).choose

theorem energyL2Constant_pos : 0 < energyL2Constant (I := I) (M := M) :=
  (exists_energyToL2_bound (I := I) (M := M)).choose_spec.1

theorem energyToL2Linear_norm_le (f : EnergySpace (I := I) (M := M)) :
    ‖energyToL2Linear f‖ ≤ energyL2Constant (I := I) (M := M) * ‖f‖ :=
  (exists_energyToL2_bound (I := I) (M := M)).choose_spec.2 f

/-- The actual core map, now bundled as a bounded linear map. -/
def energyToL2 : EnergySpace (I := I) (M := M) →L[ℝ]
    Lp ℝ 2 (riemannianVolume (I := I) (M := M)) :=
  (energyToL2Linear (I := I) (M := M)).mkContinuous
    (energyL2Constant (I := I) (M := M)) energyToL2Linear_norm_le

theorem norm_energyToL2_le : ‖energyToL2 (I := I) (M := M)‖ ≤
    energyL2Constant (I := I) (M := M) :=
  LinearMap.mkContinuous_norm_le _ (energyL2Constant_pos (I := I) (M := M)).le _

/-- The bounded extension to the Hilbert energy completion; injectivity is not claimed. -/
def energyCompletionToL2 : EnergyCompletion (I := I) (M := M) →L[ℝ]
    Lp ℝ 2 (riemannianVolume (I := I) (M := M)) :=
  (energyToL2 (I := I) (M := M)).extend
    (energyToCompletion (I := I) (M := M)).toContinuousLinearMap

/-- The extension agrees with the original algebraic map on the core. -/
theorem energyCompletionToL2_core (f : EnergySpace (I := I) (M := M)) :
    energyCompletionToL2 (energyToCompletion f) = energyToL2Linear f := by
  exact (energyToL2 (I := I) (M := M)).extend_eq (e := (energyToCompletion (I := I) (M := M)).toContinuousLinearMap)
    (denseRange_energyToCompletion (I := I) (M := M))
    (energyToCompletion (I := I)).isometry.isUniformInducing f

/-- In particular, core elements retain their actual almost-everywhere representatives. -/
theorem energyCompletionToL2_core_ae_eq (f : EnergySpace (I := I) (M := M)) :
    (energyCompletionToL2 (energyToCompletion f) : M → ℝ) =ᵐ[riemannianVolume (I := I)] f.val := by
  rw [energyCompletionToL2_core]
  exact energyToL2Linear_ae_eq f

/-- Extension along the energy isometry does not increase the operator norm. -/
theorem norm_energyCompletionToL2_le : ‖energyCompletionToL2 (I := I) (M := M)‖ ≤
    energyL2Constant (I := I) (M := M) := by
  have h := (energyToL2 (I := I) (M := M)).opNorm_extend_le (N := 1)
    (e := (energyToCompletion (I := I) (M := M)).toContinuousLinearMap)
    (denseRange_energyToCompletion (I := I) (M := M))
    (fun x => by simp)
  have h' : ‖energyCompletionToL2 (I := I) (M := M)‖ ≤ ‖energyToL2 (I := I) (M := M)‖ := by
    simpa [energyCompletionToL2] using h
  exact h'.trans norm_energyToL2_le

end AlmostSchur
