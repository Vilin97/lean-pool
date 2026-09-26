/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatGeometricRegularity
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.SecondOrderCutoff
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianLeibniz

/-!
# Coordinate form of the geometric tensor-heat cutoff commutator

This file identifies the genuine connection-Laplacian cutoff commutator with
the canonical first-plus-zeroth-order operator obtained from the first two
Fréchet derivatives of the scalar cutoff in a fixed manifold chart.
-/

@[expose] public section

@[expose] public noncomputable section
open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff

namespace RicciFlow
namespace AnalyticPDE

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [I.Boundaryless]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "W" => (ι × ι → ℝ)

@[reducible] local instance cutoffCommutatorWNormedAddCommGroup :
    NormedAddCommGroup W := Pi.normedAddCommGroup
@[reducible] local instance cutoffCommutatorWNormedSpace :
    NormedSpace ℝ W := Pi.normedSpace
@[reducible] local instance cutoffCommutatorFirstNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance cutoffCommutatorFirstNormedSpace :
    NormedSpace ℝ (E →L[ℝ] W) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance cutoffCommutatorSecondNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance cutoffCommutatorSecondNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance cutoffCommutatorTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance cutoffCommutatorTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x
@[reducible] local instance cutoffCommutatorThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance cutoffCommutatorThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance cutoffCommutatorThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance cutoffCommutatorThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance cutoffCommutatorThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance cutoffCommutatorThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance cutoffCommutatorThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- Tensor-frame coordinates commute exactly with scalar multiplication. -/
theorem localTensorCoordinates_smul_function
    (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (g : M → ℝ) (h : ∀ x : M, T₂ x) :
    localTensorCoordinates (I := I) chartCenter e b (g • h) =
      fun z => writtenInExtChartAt I 𝓘(ℝ) chartCenter g z •
        localTensorCoordinates (I := I) chartCenter e b h z := by
  funext z out
  simp [localTensorCoordinates, localTwoTensorComponentInChart,
    localTwoTensorComponent, writtenInExtChartAt,
    Function.comp_def, PartialEquiv.refl_coe, chartAt_self_eq]

/-- **The genuine geometric cutoff commutator is first-plus-zeroth order in
fixed tensor-frame coordinates.**  In particular, no second derivative of
the tensor field occurs on the right-hand side. -/
theorem connectionLaplacianCutoffCommutator_apply_eq_secondOrderCutoff
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {g : M → ℝ} {h : ∀ x : M, T₂ x}
    (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (hh : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x (h x)))
    {x : M} (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I chartCenter).source)
    (p q : ι) :
    let z := (extChartAt I chartCenter) x
    let χ := writtenInExtChartAt I 𝓘(ℝ) chartCenter g
    let u := localTensorCoordinates (I := I) chartCenter e b h
    let dχ := fderivWithin ℝ χ (Set.range I) z
    let ddχ := fderivWithin ℝ
      (fun w => fderivWithin ℝ χ (Set.range I) w) (Set.range I) z
    (connectionLaplacianCutoffCommutator cov g h x)
        (e.localFrame b p x) (e.localFrame b q x) =
      (secondOrderCutoffFirstCoefficient
          (localTensorHeatPrincipalCoefficient (I := I)
            chartCenter e b z) dχ
          (localTensorCoordinateDerivative (I := I) chartCenter e b h z) +
        secondOrderCutoffZeroCoefficient
          (localTensorHeatPrincipalCoefficient (I := I)
            chartCenter e b z)
          (localTensorHeatFirstCoefficient (I := I)
            cov chartCenter e b z) dχ ddχ (u z)) (q, p) := by
  dsimp only
  let z : E := (extChartAt I chartCenter) x
  let χ : E → ℝ := writtenInExtChartAt I 𝓘(ℝ) chartCenter g
  let u : E → W := localTensorCoordinates (I := I) chartCenter e b h
  let s : Set E := (extChartAt I chartCenter).target ∩
    (extChartAt I chartCenter).symm ⁻¹' e.baseSet
  have hz : z ∈ s := by
    refine ⟨(extChartAt I chartCenter).map_source hxChart, ?_⟩
    change (extChartAt I chartCenter).symm
      ((extChartAt I chartCenter) x) ∈ e.baseSet
    rw [(extChartAt I chartCenter).left_inv hxChart]
    exact hxFrame
  have hsOpen : IsOpen s :=
    (continuousOn_extChartAt_symm (I := I) chartCenter).isOpen_inter_preimage
      (isOpen_extChartAt_target chartCenter) e.open_baseSet
  have hsRange : s ⊆ Set.range I :=
    Set.Subset.trans Set.inter_subset_left
      (extChartAt_target_subset_range chartCenter)
  have htargetNhds : (extChartAt I chartCenter).target ∈ nhds z :=
    (isOpen_extChartAt_target chartCenter).mem_nhds hz.1
  have hrangeNhds : Set.range I ∈ nhds z :=
    mem_of_superset htargetNhds (extChartAt_target_subset_range chartCenter)
  have hχOn : ContDiffOn ℝ 2 χ s := by
    have hχTarget : ContDiffOn ℝ 2 χ
        (extChartAt I chartCenter).target := by
      apply contDiffOn_writtenInExtChartAt_of_contMDiffOn
        (I := I) (p := chartCenter) hg.contMDiffOn
      · exact Set.Subset.rfl
      intro w hw
      exact Set.mem_univ _
    exact hχTarget.mono Set.inter_subset_left
  have huOn : ContDiffOn ℝ 2 u s := by
    simpa [u, s] using
      contDiffOn_localTensorCoordinates_of_contMDiff_two
        (I := I) chartCenter e b hh
  have hχAt : ContDiffAt ℝ 2 χ z :=
    (hχOn z hz).contDiffAt (hsOpen.mem_nhds hz)
  have huAt : ContDiffAt ℝ 2 u z :=
    (huOn z hz).contDiffAt (hsOpen.mem_nhds hz)
  have hjet := secondOrder_cutoff_product_jet_at hχAt huAt
  have hfirstχ : fderivWithin ℝ χ (Set.range I) z =
      fderiv ℝ χ z := fderivWithin_of_mem_nhds hrangeNhds
  have hfirstu : localTensorCoordinateDerivative (I := I)
      chartCenter e b h z = fderiv ℝ u z := by
    simp only [localTensorCoordinateDerivative, u]
    exact fderivWithin_of_mem_nhds hrangeNhds
  have hDχEventually :
      (fun w => fderivWithin ℝ χ (Set.range I) w) =ᶠ[nhds z]
        fun w => fderiv ℝ χ w := by
    filter_upwards [htargetNhds] with w hw
    exact fderivWithin_of_mem_nhds
      (mem_of_superset
        ((isOpen_extChartAt_target chartCenter).mem_nhds hw)
        (extChartAt_target_subset_range chartCenter))
  have hDuEventually :
      localTensorCoordinateDerivative (I := I) chartCenter e b h =ᶠ[nhds z]
        fun w => fderiv ℝ u w := by
    filter_upwards [htargetNhds] with w hw
    simp only [localTensorCoordinateDerivative, u]
    exact fderivWithin_of_mem_nhds
      (mem_of_superset
        ((isOpen_extChartAt_target chartCenter).mem_nhds hw)
        (extChartAt_target_subset_range chartCenter))
  have hsecondχ : fderivWithin ℝ
      (fun w => fderivWithin ℝ χ (Set.range I) w)
        (Set.range I) z = fderiv ℝ (fderiv ℝ χ) z := by
    rw [fderivWithin_of_mem_nhds hrangeNhds]
    exact hDχEventually.fderiv_eq
  have hsecondu : localTensorCoordinateSecondDerivative (I := I)
      chartCenter e b h z = fderiv ℝ (fderiv ℝ u) z := by
    simp only [localTensorCoordinateSecondDerivative]
    rw [fderivWithin_of_mem_nhds hrangeNhds]
    exact hDuEventually.fderiv_eq
  have hcoord := localTensorCoordinates_smul_function
    (I := I) chartCenter e b g h
  have hprodFirstEventually :
      localTensorCoordinateDerivative (I := I) chartCenter e b (g • h) =ᶠ[nhds z]
        fun w => fderiv ℝ (fun y => χ y • u y) w := by
    filter_upwards [htargetNhds] with w hw
    simp only [localTensorCoordinateDerivative, hcoord, χ, u]
    exact fderivWithin_of_mem_nhds
      (mem_of_superset
        ((isOpen_extChartAt_target chartCenter).mem_nhds hw)
        (extChartAt_target_subset_range chartCenter))
  have hprodFirst : localTensorCoordinateDerivative (I := I)
      chartCenter e b (g • h) z =
        χ z • fderiv ℝ u z +
          cutoffGradientValueL (fderiv ℝ χ z) (u z) := by
    rw [hprodFirstEventually.self_of_nhds]
    exact hjet.1
  have hprodSecond : localTensorCoordinateSecondDerivative (I := I)
      chartCenter e b (g • h) z =
        χ z • fderiv ℝ (fderiv ℝ u) z +
          cutoffGradientCrossL (fderiv ℝ χ z) (fderiv ℝ u z) +
          cutoffHessianValueL (fderiv ℝ (fderiv ℝ χ) z) (u z) := by
    simp only [localTensorCoordinateSecondDerivative]
    rw [fderivWithin_of_mem_nhds hrangeNhds]
    rw [hprodFirstEventually.fderiv_eq]
    exact hjet.2
  have hmul : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y ((g • h) y)) :=
    hg.smul_section hh
  have hlapProd :=
    connectionLaplacian_apply_eq_localTensorHeatSecondOrder_of_contMDiff_two
      (I := I) cov chartCenter e b hmul hxFrame hxChart p q
  have hlap :=
    connectionLaplacian_apply_eq_localTensorHeatSecondOrder_of_contMDiff_two
      (I := I) cov chartCenter e b hh hxFrame hxChart p q
  have hcomm := connectionLaplacian_smul_function_of_contMDiff_two
    (I := I) cov hg hh x
  have hcommComponent := congrArg
    (fun F : T₂ x => F (e.localFrame b p x) (e.localFrame b q x)) hcomm
  have hχValue : χ z = g x := by
    simp only [χ, z, writtenInExtChartAt, Function.comp_apply,
      extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      id_eq]
    rw [(extChartAt I chartCenter).left_inv hxChart]
  have hrawValue : writtenInExtChartAt I 𝓘(ℝ) chartCenter g
      ((extChartAt I chartCenter) x) = g x := by
    simpa only [χ, z] using hχValue
  let P := localTensorHeatPrincipalCoefficient (I := I) chartCenter e b z
  let B := localTensorHeatFirstCoefficient (I := I) cov chartCenter e b z
  let C := localTensorHeatZeroCoefficient (I := I) cov chartCenter e b z
  have hexp := secondOrder_cutoff_expansion P B C
    (χ z) (fderiv ℝ χ z) (fderiv ℝ (fderiv ℝ χ) z)
    (u z) (fderiv ℝ u z) (fderiv ℝ (fderiv ℝ u) z)
  have hexpComponent := congrFun hexp (q, p)
  rw [hlapProd] at hcommComponent
  simp only [add_apply, smul_apply, smul_eq_mul] at hcommComponent
  rw [hlap] at hcommComponent
  rw [hprodFirst, hprodSecond, hcoord] at hcommComponent
  rw [hχValue] at hexpComponent
  simp only [hχValue, hrawValue] at hcommComponent
  rw [hfirstu, hsecondu] at hcommComponent
  rw [hfirstχ, hsecondχ]
  rw [hfirstu]
  dsimp only [P, B, C, z, χ, u] at hexpComponent hcommComponent ⊢
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hexpComponent hcommComponent ⊢
  linear_combination hexpComponent - hcommComponent

/-- The cutoff commutator vanishes off the topological support of the
cutoff.  This is the germ-local support statement needed to glue its chart
representatives without artifacts. -/
theorem connectionLaplacianCutoffCommutator_eq_zero_of_notMem_tsupport
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (b : Module.Basis ι ℝ E) {g : M → ℝ} {h : ∀ x : M, T₂ x}
    (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (hh : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x (h x)))
    {x : M} (hx : x ∉ tsupport g) :
    connectionLaplacianCutoffCommutator cov g h x = 0 := by
  let e := trivializationAt E TM x
  let z := (extChartAt I x) x
  let χ := writtenInExtChartAt I 𝓘(ℝ) x g
  have hxFrame : x ∈ e.baseSet := by
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hxChart : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hg0 : g =ᶠ[nhds x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hx
  have hsymm : Tendsto (extChartAt I x).symm (nhds z) (nhds x) := by
    have ht := continuousAt_extChartAt_symm' hxChart
    change Tendsto (extChartAt I x).symm
      (nhds ((extChartAt I x) x))
      (nhds ((extChartAt I x).symm ((extChartAt I x) x))) at ht
    rw [(extChartAt I x).left_inv hxChart] at ht
    exact ht
  have hpull : (fun w => g ((extChartAt I x).symm w)) =ᶠ[nhds z] 0 :=
    hsymm.eventually hg0
  have hχ0 : χ =ᶠ[nhds z] 0 := by
    simpa [χ, writtenInExtChartAt, extChartAt_model_space_eq_id,
      Function.comp_def, PartialEquiv.refl_coe, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, chartAt_self_eq,
      OpenPartialHomeomorph.refl_apply,
      OpenPartialHomeomorph.coe_toPartialEquiv] using hpull
  have hzTarget : z ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxChart
  have hrange : Set.range I ∈ nhds z :=
    mem_of_superset ((isOpen_extChartAt_target x).mem_nhds hzTarget)
      (extChartAt_target_subset_range x)
  have hdχ : fderivWithin ℝ χ (Set.range I) z = 0 := by
    rw [fderivWithin_of_mem_nhds hrange, hχ0.fderiv_eq]
    simp
  have hdχev :
      (fun w => fderivWithin ℝ χ (Set.range I) w) =ᶠ[nhds z] 0 := by
    have htarget : (extChartAt I x).target ∈ nhds z :=
      (isOpen_extChartAt_target x).mem_nhds hzTarget
    have hdf := hχ0.fderiv (𝕜 := ℝ)
    filter_upwards [htarget, hdf] with w hw hfw
    rw [fderivWithin_of_mem_nhds
      (mem_of_superset ((isOpen_extChartAt_target x).mem_nhds hw)
        (extChartAt_target_subset_range x))]
    simpa using hfw
  have hddχ : fderivWithin ℝ
      (fun w => fderivWithin ℝ χ (Set.range I) w)
        (Set.range I) z = 0 := by
    rw [fderivWithin_of_mem_nhds hrange, hdχev.fderiv_eq]
    simp
  apply ContinuousLinearMap.coe_injective
  refine (e.basisAt b hxFrame).ext (fun p => ?_)
  apply ContinuousLinearMap.coe_injective
  refine (e.basisAt b hxFrame).ext (fun q => ?_)
  rw [← Bundle.Trivialization.localFrame_apply_of_mem_baseSet
      (e := e) (b := b) hxFrame,
    ← Bundle.Trivialization.localFrame_apply_of_mem_baseSet
      (e := e) (b := b) hxFrame]
  change connectionLaplacianCutoffCommutator cov g h x
      (e.localFrame b p x) (e.localFrame b q x) = 0
  rw [connectionLaplacianCutoffCommutator_apply_eq_secondOrderCutoff
    cov x e b hg hh hxFrame hxChart p q]
  change
    (secondOrderCutoffFirstCoefficient
        (localTensorHeatPrincipalCoefficient (I := I) x e b z)
        (fderivWithin ℝ χ (Set.range I) z)
        (localTensorCoordinateDerivative (I := I) x e b h z) +
      secondOrderCutoffZeroCoefficient
        (localTensorHeatPrincipalCoefficient (I := I) x e b z)
        (localTensorHeatFirstCoefficient (I := I) cov x e b z)
        (fderivWithin ℝ χ (Set.range I) z)
        (fderivWithin ℝ
          (fun w => fderivWithin ℝ χ (Set.range I) w)
          (Set.range I) z)
        (localTensorCoordinates (I := I) x e b h z)) (q, p) = 0
  rw [hdχ, hddχ]
  simp [secondOrderCutoffFirstCoefficient, secondOrderCutoffZeroCoefficient,
    cutoffGradientCrossL, cutoffHessianValueL, cutoffGradientValueL]

end AnalyticPDE
end RicciFlow
