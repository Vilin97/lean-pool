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

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyPairingReconstruction
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyChartKernel

/-! # Injectivity of the actual L² realization of completed energy

Zero realization gives zero local weak derivatives in compact chart interiors.
The finite-chart pairing formula then annihilates the dense C¹ energy core.
No reverse norm estimate or density of C² functions in energy is assumed.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators
open RellichKondrachov.Geometry.Manifold.Sobolev FiniteChartData

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

/-- A zero realization annihilates every reconstruction coefficient. Its
support is strictly inside the compact set, so no boundary vanishing is used. -/
theorem inner_energyChartDerivative_coeff_eq_zero
    (d : FiniteChartData (H := H) (M := M) I) (i : d.ι)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I (d.center i)).target)
    (hcover : rhoSupportImage (d := d) i ⊆ interior K)
    (u : EnergyCompletion (I := I) (M := M)) (hu : energyCompletionToL2 u = 0)
    (g : EnergySpace (I := I) (M := M)) (v : E) :
    inner ℝ (energyChartDerivative (d.center i) hK hKt v u)
      (energyPairingCoeffL2 d i g.property.1 v K) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [energyChartDerivative_ae_eq_zero_of_realization_eq_zero
    (d.center i) hK hKt v u hu, energyPairingCoeffL2_ae_eq d i g.property.1 v K]
    with z hz hq
  by_cases hs : z ∈ tsupport (energyPairingCoeff d i g.val v)
  · have hd := hz (hcover (tsupport_energyPairingCoeff_subset d i g.val v hs))
    simp only [hd, inner_zero_left, Pi.zero_apply]
  · have hq0 := image_eq_zero_of_notMem_tsupport hs
    simp only [hq, hq0, inner_zero_right, Pi.zero_apply]

/-- The completed energy-to-L² map has trivial kernel. All finite chart
neighborhoods are constructed, and orthogonality is tested against the full
dense C¹ core, not a smoother unproved-dense subspace. -/
theorem energyCompletion_eq_zero_of_toL2_eq_zero
    (u : EnergyCompletion (I := I) (M := M)) (hu : energyCompletionToL2 u = 0) : u = 0 := by
  classical
  obtain ⟨d⟩ := exists_finiteChartData_chartAt (I := I) (M := M)
  choose K hK hcover hKt using fun i : d.ι =>
    exists_compact_between (isCompact_rhoSupportImage (d := d) i)
      (isOpen_extChartAt_target (I := I) (d.center i)) (rhoSupportImage_subset_target (d := d) i)
  have hcore (g : EnergySpace (I := I) (M := M)) : inner ℝ u (energyToCompletion g) = 0 := by
    rw [energyCompletion_inner_eq_sum_chartPairings d K hK hKt
      (fun i => (hcover i).trans interior_subset)]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    exact inner_energyChartDerivative_coeff_eq_zero d i (hK i) (hKt i) (hcover i) u hu g _
  have hall (w : EnergyCompletion (I := I) (M := M)) : inner ℝ u w = 0 := by
    refine (denseRange_energyToCompletion (I := I) (M := M)).induction_on w ?_ hcore
    exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
  exact inner_self_eq_zero.mp (hall u)

/-- Completed intrinsic energy has a faithful actual-volume L² realization. -/
theorem energyCompletionToL2_injective :
    Function.Injective (energyCompletionToL2 (I := I) (M := M)) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply energyCompletion_eq_zero_of_toL2_eq_zero
  rw [map_sub, huv, sub_self]

end AlmostSchur
