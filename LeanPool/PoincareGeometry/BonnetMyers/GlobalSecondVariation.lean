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

public import LeanPool.PoincareGeometry.BonnetMyers.BrokenVariationIntegral
public import LeanPool.PoincareGeometry.BonnetMyers.ManifoldSineTest
public import LeanPool.PoincareGeometry.BonnetMyers.CurvatureRegularity
public import LeanPool.PoincareGeometry.BonnetMyers.GlobalIntrinsicGeodesic

/-! # Global Second Variation -/

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology Interval RealInnerProductSpace

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace IntrinsicGeodesic.GlobalGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

theorem coordinateFrameCombination_total_continuousAt
    {X : Type*} [TopologicalSpace X] {q : X}
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {y : X → M} {u : X → E}
    (hy : ContinuousAt y q) (hu : ContinuousAt u q)
    (hsource : y q ∈ (extChartAt I c).source) :
    ContinuousAt (fun x ↦
      (⟨y x, LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis (u x) (y x)⟩ :
        Bundle.TotalSpace E TM)) q := by
  let e := trivializationAt E TM c
  have hbase : y q ∈ e.baseSet := by
    dsimp [e]
    rw [← extChartAt_source (I := I) c]
    exact hsource
  have hpair : ContinuousAt (fun x ↦ (y x, u x)) q := hy.prodMk hu
  have hsymmAt : ContinuousAt
      (fun z : M × E ↦ TotalSpace.mk' E z.1 (e.symm z.1 z.2))
      (y q, u q) :=
    (e.continuousOn_symm.continuousAt
      ((e.open_baseSet.prod isOpen_univ).mem_nhds ⟨hbase, mem_univ _⟩))
  have hsymm : ContinuousAt
      (fun x ↦ TotalSpace.mk' E (y x) (e.symm (y x) (u x))) q :=
    hsymmAt.comp_of_eq hpair rfl
  apply hsymm.congr_of_eventuallyEq
  have hnear : ∀ᶠ x in nhds q, y x ∈ (extChartAt I c).source :=
    hy.preimage_mem_nhds ((isOpen_extChartAt_source (I := I) c).mem_nhds hsource)
  filter_upwards [hnear] with x hx
  have hxchart : y x ∈ (chartAt H c).source := by
    rwa [← extChartAt_source (I := I) c]
  have hxbase : y x ∈ e.baseSet := by
    dsimp [e]
    rw [← extChartAt_source (I := I) c]
    exact hx
  rw [LocalGeodesicData.coordinateFrameCombination_eq_symmL
    (I := I) (M := M) c basis hxchart]
  change TotalSpace.mk' E (y x) ((e.symmL ℝ (y x)) (u x)) =
    TotalSpace.mk' E (y x) (e.symm (y x) (u x))
  rw [e.symmL_apply hxbase]

theorem coordinateFrameCombination_inner_continuousAt
    [IsContinuousRiemannianBundle E TM]
    {X : Type*} [TopologicalSpace X] {q : X}
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {y : X → M} {u v : X → E}
    (hy : ContinuousAt y q) (hu : ContinuousAt u q)
    (hv : ContinuousAt v q)
    (hsource : y q ∈ (extChartAt I c).source) :
    ContinuousAt (fun x ↦ inner ℝ
      (LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c) basis (u x) (y x))
      (LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c) basis (v x) (y x))) q := by
  exact (coordinateFrameCombination_total_continuousAt
      (I := I) (M := M) c basis hy hu hsource).inner_bundle
    (coordinateFrameCombination_total_continuousAt
      (I := I) (M := M) c basis hy hv hsource)

theorem LocalGeodesicData.coordinateEnergyDensity_continuousAt
    [IsContinuousRiemannianBundle E TM]
    {X : Type*} [TopologicalSpace X] {q : X}
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {Q V : X → E} (hQ : ContinuousAt Q q) (hV : ContinuousAt V q)
    (htarget : Q q ∈ (extChartAt I c).target) :
    ContinuousAt (fun x ↦ (2 : ℝ)⁻¹ * inner ℝ
      (LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c) basis (V x)
          ((extChartAt I c).symm (Q x)))
      (LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c) basis (V x)
          ((extChartAt I c).symm (Q x)))) q := by
  have hy : ContinuousAt (fun x ↦ (extChartAt I c).symm (Q x)) q :=
    (continuousAt_extChartAt_symm'' htarget).comp_of_eq hQ rfl
  have hsource : (extChartAt I c).symm (Q q) ∈ (extChartAt I c).source :=
    (extChartAt I c).map_target htarget
  exact continuousAt_const.mul
    (coordinateFrameCombination_inner_continuousAt
      (I := I) (M := M) c basis hy hV hV hsource)

/-- The coordinate Christoffel expression is jointly continuous in its base
coordinate and both vector arguments wherever the base lies in the chart
target. -/
theorem LocalGeodesicData.coordinateParallelOperator_apply_continuousAt
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {X : Type*} [TopologicalSpace X] {q : X}
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {Q U W : X → E}
    (hQ : ContinuousAt Q q) (hU : ContinuousAt U q)
    (hW : ContinuousAt W q)
    (htarget : Q q ∈ (extChartAt I c).target) :
    ContinuousAt (fun x ↦
      LocalGeodesicData.coordinateParallelOperator
        (I := I) (M := M) (E := E) cov c basis
          (Q x) (U x) (W x)) q := by
  rw [show (fun x ↦ LocalGeodesicData.coordinateParallelOperator
      (I := I) (M := M) (E := E) cov c basis
        (Q x) (U x) (W x)) = fun x ↦ ∑ i, ∑ j, ∑ k,
      ((basis.repr (W x) j) * (basis.repr (U x) k) *
        LocalGeodesicData.connectionCoefficient
          (I := I) (M := M) (E := E) cov c basis i j k
            ((extChartAt I c).symm (Q x))) • basis i by
    funext x
    exact LocalGeodesicData.coordinateParallelOperator_apply
      cov c basis (Q x) (U x) (W x)]
  apply tendsto_finsetSum Finset.univ
  intro i hi
  apply tendsto_finsetSum Finset.univ
  intro j hj
  apply tendsto_finsetSum Finset.univ
  intro k hk
  have hWcoord : ContinuousAt (fun x ↦ basis.repr (W x) j) q :=
    (basis.coord j).toContinuousLinearMap.continuous.continuousAt.comp_of_eq hW rfl
  have hUcoord : ContinuousAt (fun x ↦ basis.repr (U x) k) q :=
    (basis.coord k).toContinuousLinearMap.continuous.continuousAt.comp_of_eq hU rfl
  have hcoeff : ContinuousAt (fun x ↦
      LocalGeodesicData.connectionCoefficient
        (I := I) (M := M) (E := E) cov c basis i j k
          ((extChartAt I c).symm (Q x))) q := by
    exact (LocalGeodesicData.connectionCoefficient_comp_extChartAt_symm_contDiffAt_of_mem_target
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := c) (b := basis)
      i j k htarget).continuousAt.comp_of_eq hQ rfl
  exact ((hWcoord.mul hUcoord).mul hcoeff).smul continuousAt_const

/-- The same Christoffel expression, viewed as a function of all three
coordinate arguments, is `C¹` on the chart target. -/
theorem LocalGeodesicData.coordinateParallelOperator_apply_contDiffAt
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {q : E × E × E} (htarget : q.1 ∈ (extChartAt I c).target) :
    ContDiffAt ℝ 1 (fun x : E × E × E ↦
      LocalGeodesicData.coordinateParallelOperator
        (I := I) (M := M) (E := E) cov c basis
          x.1 x.2.1 x.2.2) q := by
  rw [show (fun x : E × E × E ↦
      LocalGeodesicData.coordinateParallelOperator
        (I := I) (M := M) (E := E) cov c basis
          x.1 x.2.1 x.2.2) = fun x ↦ ∑ i, ∑ j, ∑ k,
      ((basis.repr x.2.2 j) * (basis.repr x.2.1 k) *
        LocalGeodesicData.connectionCoefficient
          (I := I) (M := M) (E := E) cov c basis i j k
            ((extChartAt I c).symm x.1)) • basis i by
    funext x
    exact LocalGeodesicData.coordinateParallelOperator_apply
      cov c basis x.1 x.2.1 x.2.2]
  apply ContDiffAt.sum
  intro i hi
  apply ContDiffAt.sum
  intro j hj
  apply ContDiffAt.sum
  intro k hk
  have hW : ContDiffAt ℝ 1 (fun x : E × E × E ↦ basis.repr x.2.2 j) q :=
    (basis.coord j).toContinuousLinearMap.contDiff.contDiffAt.comp q
      contDiffAt_snd.snd
  have hU : ContDiffAt ℝ 1 (fun x : E × E × E ↦ basis.repr x.2.1 k) q :=
    (basis.coord k).toContinuousLinearMap.contDiff.contDiffAt.comp q
      contDiffAt_snd.fst
  have hcoeff : ContDiffAt ℝ 1 (fun x : E × E × E ↦
      LocalGeodesicData.connectionCoefficient
        (I := I) (M := M) (E := E) cov c basis i j k
          ((extChartAt I c).symm x.1)) q :=
    (LocalGeodesicData.connectionCoefficient_comp_extChartAt_symm_contDiffAt_of_mem_target
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := c) (b := basis)
      i j k htarget).comp q contDiffAt_fst
  exact ((hW.mul hU).mul hcoeff).smul_const (basis i)

/-- The base derivative of the coordinate Christoffel expression, applied to
a direction, depends continuously on the base, both vector slots, and the
direction. -/
theorem LocalGeodesicData.coordinateParallelOperator_baseFderiv_apply_continuousAt
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {X : Type*} [TopologicalSpace X] {q : X}
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {Q U W V : X → E}
    (hQ : ContinuousAt Q q) (hU : ContinuousAt U q)
    (hW : ContinuousAt W q) (hV : ContinuousAt V q)
    (htarget : Q q ∈ (extChartAt I c).target) :
    ContinuousAt (fun x ↦
      fderiv ℝ (fun z ↦ LocalGeodesicData.coordinateParallelOperator
        (I := I) (M := M) (E := E) cov c basis z (U x) (W x))
          (Q x) (V x)) q := by
  let A := (E × E) × (E × E)
  let xq : A := ((Q q, U q), (W q, V q))
  let f : A → E → E := fun x z ↦
    LocalGeodesicData.coordinateParallelOperator
      (I := I) (M := M) (E := E) cov c basis z x.1.2 x.2.1
  let g : A → E := fun x ↦ x.1.1
  let k : A → E := fun x ↦ x.2.2
  have hP := LocalGeodesicData.coordinateParallelOperator_apply_contDiffAt
    (I := I) (M := M) (cov := cov) c basis
      (q := (Q q, U q, W q)) htarget
  have hfg : ContDiffAt ℝ 1 (Function.uncurry f) (xq, g xq) := by
    have hmap : ContDiffAt ℝ 1
        (fun r : A × E ↦ (r.2, r.1.1.2, r.1.2.1)) (xq, g xq) := by
      dsimp only [A]
      fun_prop
    have hcomp := hP.comp (xq, g xq) hmap
    convert hcomp using 1 <;> rfl
  have hfd : ContDiffAt ℝ 0
      (fun x ↦ fderiv ℝ (f x) (g x)) xq := by
    exact hfg.fderiv (by dsimp only [g, A]; fun_prop) (by norm_num)
  have happ : ContDiffAt ℝ 0
      (fun x ↦ fderiv ℝ (f x) (g x) (k x)) xq := by
    exact hfd.clm_apply (by dsimp only [k, A]; fun_prop)
  have htuple : ContinuousAt (fun x ↦
      (((Q x, U x), (W x, V x)) : A)) q :=
    (hQ.prodMk hU).prodMk (hW.prodMk hV)
  have hcomp := happ.continuousAt.comp_of_eq htuple rfl
  convert hcomp using 1 <;> rfl

theorem LocalGeodesicData.coordinateCurvatureOperator_continuousAt
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {X : Type*} [TopologicalSpace X] {q : X}
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {Q U V W : X → E}
    (hQ : ContinuousAt Q q) (hU : ContinuousAt U q)
    (hV : ContinuousAt V q) (hW : ContinuousAt W q)
    (htarget : Q q ∈ (extChartAt I c).target) :
    ContinuousAt (fun x ↦ LocalGeodesicData.coordinateCurvatureOperator
      (I := I) (M := M) cov c basis (Q x) (U x) (V x) (W x)) q := by
  have hdVU :=
    LocalGeodesicData.coordinateParallelOperator_baseFderiv_apply_continuousAt
      (I := I) (M := M) (cov := cov) c basis hQ hV hW hU htarget
  have hdUV :=
    LocalGeodesicData.coordinateParallelOperator_baseFderiv_apply_continuousAt
      (I := I) (M := M) (cov := cov) c basis hQ hU hW hV htarget
  have hPVW := LocalGeodesicData.coordinateParallelOperator_apply_continuousAt
    (I := I) (M := M) (cov := cov) c basis hQ hV hW htarget
  have hPUW := LocalGeodesicData.coordinateParallelOperator_apply_continuousAt
    (I := I) (M := M) (cov := cov) c basis hQ hU hW htarget
  have hUPVW := LocalGeodesicData.coordinateParallelOperator_apply_continuousAt
    (I := I) (M := M) (cov := cov) c basis hQ hU hPVW htarget
  have hVPUW := LocalGeodesicData.coordinateParallelOperator_apply_continuousAt
    (I := I) (M := M) (cov := cov) c basis hQ hV hPUW htarget
  unfold LocalGeodesicData.coordinateCurvatureOperator
  exact ((hdVU.sub hdUV).add hUPVW).sub hVPUW

/-- A curvature pairing written in a fixed coordinate frame is continuous
while the base and all four coordinate vectors vary inside an open frame
agreement region. -/
theorem LocalGeodesicData.coordinateCurvaturePairing_continuousAt
    [IsContinuousRiemannianBundle E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (htorsion : cov.torsion = 0)
    {X : Type*} [TopologicalSpace X] {q : X}
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {Q A U V W : X → E}
    (hQ : ContinuousAt Q q) (hA : ContinuousAt A q)
    (hU : ContinuousAt U q) (hV : ContinuousAt V q)
    (hW : ContinuousAt W q)
    (htarget : Q q ∈ (extChartAt I c).target)
    {O : Set M} (hOopen : IsOpen O)
    (hO : (extChartAt I c).symm (Q q) ∈ O)
    (hOframe : ∀ y ∈ O, ∀ k : Fin (Module.finrank ℝ E),
      LocalGeodesicData.smoothFrame
        (I := I) (M := M) (E := E) c basis k y =
        (trivializationAt E TM c).localFrame basis k y) :
    ContinuousAt (fun x ↦
      let y := (extChartAt I c).symm (Q x)
      inner ℝ
        (LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis (A x) y)
        (curvature (cov := cov) y
          (LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := c) basis (U x) y)
          (LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := c) basis (V x) y)
          (LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := c) basis (W x) y))) q := by
  let y : X → M := fun x ↦ (extChartAt I c).symm (Q x)
  let R : X → E := fun x ↦ LocalGeodesicData.coordinateCurvatureOperator
    (I := I) (M := M) cov c basis (Q x) (U x) (V x) (W x)
  have hy : ContinuousAt y q :=
    (continuousAt_extChartAt_symm'' htarget).comp_of_eq hQ rfl
  have hR : ContinuousAt R q := by
    exact LocalGeodesicData.coordinateCurvatureOperator_continuousAt
      (I := I) (M := M) (cov := cov) c basis hQ hU hV hW htarget
  have hsource : y q ∈ (extChartAt I c).source :=
    (extChartAt I c).map_target htarget
  have hcoord : ContinuousAt (fun x ↦ inner ℝ
      (LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c) basis (A x) (y x))
      (LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c) basis (R x) (y x))) q :=
    coordinateFrameCombination_inner_continuousAt
      (I := I) (M := M) c basis hy hA hR hsource
  apply hcoord.congr_of_eventuallyEq
  have htargetNear : ∀ᶠ x in nhds q, Q x ∈ (extChartAt I c).target :=
    hQ.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := I) c).mem_nhds htarget)
  have hONear : ∀ᶠ x in nhds q, y x ∈ O :=
    hy.preimage_mem_nhds (hOopen.mem_nhds hO)
  filter_upwards [htargetNear, hONear] with x hxTarget hxO
  have hxSource : y x ∈ (extChartAt I c).source :=
    (extChartAt I c).map_target hxTarget
  have hxFrame : ∀ k : Fin (Module.finrank ℝ E),
      LocalGeodesicData.smoothFrame
        (I := I) (M := M) (E := E) c basis k =ᶠ[nhds (y x)]
        (trivializationAt E TM c).localFrame basis k := by
    intro k
    filter_upwards [hOopen.mem_nhds hxO] with z hz
    exact hOframe z hz k
  have hcurv := LocalGeodesicData.coordinateFrameCombination_coordinateCurvatureOperator
    (I := I) (M := M) (E := E) cov c basis hxSource htorsion hxFrame
      (U x) (V x) (W x)
  have hright : extChartAt I c (y x) = Q x :=
    (extChartAt I c).right_inv hxTarget
  rw [hright] at hcurv
  exact congrArg (fun v ↦ inner ℝ
    (LocalGeodesicData.coordinateFrameCombination
      (I := I) (M := M) (x₀ := c) basis (A x) (y x)) v) hcurv.symm

theorem LocalGeodesicData.CoordinateBrokenVariationData.position_continuousAt
    (d : LocalGeodesicData.CoordinateBrokenVariationData E) {q : ℝ × ℝ}
    (hz : ContinuousAt d.z q.2) (hJ : ContinuousAt d.J q.2)
    (hleft : ContinuousAt d.leftNode q.1)
    (hright : ContinuousAt d.rightNode q.1) :
    ContinuousAt (fun x : ℝ × ℝ ↦ d.position x.1 x.2) q := by
  unfold LocalGeodesicData.CoordinateBrokenVariationData.position
    LocalGeodesicData.coordinateBrokenVariationPiece
    LocalGeodesicData.brokenVariationNodeResidual
    LocalGeodesicData.brokenVariationLeftWeight
    LocalGeodesicData.brokenVariationRightWeight
  fun_prop

theorem LocalGeodesicData.CoordinateBrokenVariationData.velocity_continuousAt
    (d : LocalGeodesicData.CoordinateBrokenVariationData E) {q : ℝ × ℝ}
    (hdz : ContinuousAt d.dz q.2) (hdJ : ContinuousAt d.dJ q.2)
    (hz : ContinuousAt d.z q.2) (hJ : ContinuousAt d.J q.2)
    (hleft : ContinuousAt d.leftNode q.1)
    (hright : ContinuousAt d.rightNode q.1) :
    ContinuousAt (fun x : ℝ × ℝ ↦ d.velocity x.1 x.2) q := by
  unfold LocalGeodesicData.CoordinateBrokenVariationData.velocity
    LocalGeodesicData.coordinateBrokenVariationVelocity
    LocalGeodesicData.brokenVariationNodeResidual
  fun_prop

theorem LocalGeodesicData.CoordinateBrokenVariationData.field_continuousAt
    (d : LocalGeodesicData.CoordinateBrokenVariationData E) {q : ℝ × ℝ}
    (hJ : ContinuousAt d.J q.2)
    (hleft : ContinuousAt d.leftVelocity q.1)
    (hright : ContinuousAt d.rightVelocity q.1) :
    ContinuousAt (fun x : ℝ × ℝ ↦ d.field x.1 x.2) q := by
  unfold LocalGeodesicData.CoordinateBrokenVariationData.field
    LocalGeodesicData.coordinateBrokenVariationField
    LocalGeodesicData.brokenVariationLeftWeight
    LocalGeodesicData.brokenVariationRightWeight
  fun_prop

theorem LocalGeodesicData.CoordinateBrokenVariationData.mixed_continuousAt
    (d : LocalGeodesicData.CoordinateBrokenVariationData E) {q : ℝ × ℝ}
    (hdJ : ContinuousAt d.dJ q.2) (hJ : ContinuousAt d.J q.2)
    (hleft : ContinuousAt d.leftVelocity q.1)
    (hright : ContinuousAt d.rightVelocity q.1) :
    ContinuousAt (fun x : ℝ × ℝ ↦ d.mixed x.1 x.2) q := by
  unfold LocalGeodesicData.CoordinateBrokenVariationData.mixed
    LocalGeodesicData.coordinateBrokenVariationMixed
  fun_prop

theorem LocalGeodesicData.CoordinateBrokenVariationData.secondField_continuousAt
    (d : LocalGeodesicData.CoordinateBrokenVariationData E) {q : ℝ × ℝ}
    (hleft : ContinuousAt d.leftAcceleration q.1)
    (hright : ContinuousAt d.rightAcceleration q.1) :
    ContinuousAt (fun x : ℝ × ℝ ↦ d.secondField x.1 x.2) q := by
  unfold LocalGeodesicData.CoordinateBrokenVariationData.secondField
    LocalGeodesicData.coordinateBrokenVariationSecondField
    LocalGeodesicData.brokenVariationLeftWeight
    LocalGeodesicData.brokenVariationRightWeight
  fun_prop

theorem LocalGeodesicData.CoordinateBrokenVariationData.secondMixed_continuousAt
    (d : LocalGeodesicData.CoordinateBrokenVariationData E) {q : ℝ × ℝ}
    (hleft : ContinuousAt d.leftAcceleration q.1)
    (hright : ContinuousAt d.rightAcceleration q.1) :
    ContinuousAt (fun x : ℝ × ℝ ↦ d.secondMixed x.1) q := by
  unfold LocalGeodesicData.CoordinateBrokenVariationData.secondMixed
    LocalGeodesicData.coordinateBrokenVariationSecondMixed
  fun_prop

theorem LocalGeodesicData.coordinateCovariantFieldDerivative_continuousAt
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {X : Type*} [TopologicalSpace X] {q : X}
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {Q U W dW : X → E}
    (hQ : ContinuousAt Q q) (hU : ContinuousAt U q)
    (hW : ContinuousAt W q) (hdW : ContinuousAt dW q)
    (htarget : Q q ∈ (extChartAt I c).target) :
    ContinuousAt (fun x ↦
      LocalGeodesicData.coordinateCovariantFieldDerivative
        (I := I) (M := M) cov c basis
          (Q x) (U x) (W x) (dW x)) q := by
  unfold LocalGeodesicData.coordinateCovariantFieldDerivative
  exact hdW.add
    (LocalGeodesicData.coordinateParallelOperator_apply_continuousAt
      (I := I) (M := M) (cov := cov) c basis hQ hU hW htarget)

theorem LocalGeodesicData.CoordinateBrokenVariationData.energyDensity_continuousAt
    [IsContinuousRiemannianBundle E TM]
    (d : LocalGeodesicData.CoordinateBrokenVariationData E)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {q : ℝ × ℝ}
    (hz : ContinuousAt d.z q.2) (hdz : ContinuousAt d.dz q.2)
    (hJ : ContinuousAt d.J q.2) (hdJ : ContinuousAt d.dJ q.2)
    (hleft : ContinuousAt d.leftNode q.1)
    (hright : ContinuousAt d.rightNode q.1)
    (htarget : d.position q.1 q.2 ∈ (extChartAt I c).target) :
    ContinuousAt (fun x : ℝ × ℝ ↦
      d.energyDensity (I := I) (M := M) c basis x.1 x.2) q := by
  apply LocalGeodesicData.coordinateEnergyDensity_continuousAt
    (I := I) (M := M) c basis
  · exact LocalGeodesicData.CoordinateBrokenVariationData.position_continuousAt
      d hz hJ hleft hright
  · exact LocalGeodesicData.CoordinateBrokenVariationData.velocity_continuousAt
      d hdz hdJ hz hJ hleft hright
  · exact htarget

theorem LocalGeodesicData.CoordinateBrokenVariationData.firstVariationDensity_continuousAt
    [IsContinuousRiemannianBundle E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (d : LocalGeodesicData.CoordinateBrokenVariationData E)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {q : ℝ × ℝ}
    (hz : ContinuousAt d.z q.2) (hdz : ContinuousAt d.dz q.2)
    (hJ : ContinuousAt d.J q.2) (hdJ : ContinuousAt d.dJ q.2)
    (hleftNode : ContinuousAt d.leftNode q.1)
    (hrightNode : ContinuousAt d.rightNode q.1)
    (hleftVelocity : ContinuousAt d.leftVelocity q.1)
    (hrightVelocity : ContinuousAt d.rightVelocity q.1)
    (htarget : d.position q.1 q.2 ∈ (extChartAt I c).target) :
    ContinuousAt (fun x : ℝ × ℝ ↦
      d.firstVariationDensity (I := I) (M := M) cov c basis x.1 x.2) q := by
  have hQ := LocalGeodesicData.CoordinateBrokenVariationData.position_continuousAt
    d hz hJ hleftNode hrightNode
  have hW := LocalGeodesicData.CoordinateBrokenVariationData.field_continuousAt
    d hJ hleftVelocity hrightVelocity
  have hV := LocalGeodesicData.CoordinateBrokenVariationData.velocity_continuousAt
    d hdz hdJ hz hJ hleftNode hrightNode
  have hdV := LocalGeodesicData.CoordinateBrokenVariationData.mixed_continuousAt
    d hdJ hJ hleftVelocity hrightVelocity
  have hB := LocalGeodesicData.coordinateCovariantFieldDerivative_continuousAt
    (I := I) (M := M) (cov := cov) c basis hQ hW hV hdV htarget
  unfold LocalGeodesicData.CoordinateBrokenVariationData.firstVariationDensity
    LocalGeodesicData.coordinateFirstVariationDensity
    LocalGeodesicData.coordinateFirstVariationCovariantField
  exact coordinateFrameCombination_inner_continuousAt
    (I := I) (M := M) c basis
      ((continuousAt_extChartAt_symm'' htarget).comp_of_eq hQ rfl)
      hB hV ((extChartAt I c).map_target htarget)

theorem LocalGeodesicData.CoordinateBrokenVariationData.secondVariationDensityAt_continuousAt
    [IsContinuousRiemannianBundle E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (d : LocalGeodesicData.CoordinateBrokenVariationData E)
    (htorsion : cov.torsion = 0)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {q : ℝ × ℝ}
    (hz : ContinuousAt d.z q.2) (hdz : ContinuousAt d.dz q.2)
    (hJ : ContinuousAt d.J q.2) (hdJ : ContinuousAt d.dJ q.2)
    (hleftNode : ContinuousAt d.leftNode q.1)
    (hrightNode : ContinuousAt d.rightNode q.1)
    (hleftVelocity : ContinuousAt d.leftVelocity q.1)
    (hrightVelocity : ContinuousAt d.rightVelocity q.1)
    (hleftAcceleration : ContinuousAt d.leftAcceleration q.1)
    (hrightAcceleration : ContinuousAt d.rightAcceleration q.1)
    (htarget : d.position q.1 q.2 ∈ (extChartAt I c).target)
    {O : Set M} (hOopen : IsOpen O)
    (hO : (extChartAt I c).symm (d.position q.1 q.2) ∈ O)
    (hOframe : ∀ y ∈ O, ∀ k : Fin (Module.finrank ℝ E),
      LocalGeodesicData.smoothFrame
        (I := I) (M := M) (E := E) c basis k y =
        (trivializationAt E TM c).localFrame basis k y) :
    ContinuousAt (fun x : ℝ × ℝ ↦
      d.secondVariationDensityAt (I := I) (M := M)
        cov c basis x.1 x.2) q := by
  let Q : ℝ × ℝ → E := fun x ↦ d.position x.1 x.2
  let W : ℝ × ℝ → E := fun x ↦ d.field x.1 x.2
  let V : ℝ × ℝ → E := fun x ↦ d.velocity x.1 x.2
  let dV : ℝ × ℝ → E := fun x ↦ d.mixed x.1 x.2
  let C₀ : ℝ × ℝ → E := fun x ↦ d.secondField x.1 x.2
  let dC₀ : ℝ × ℝ → E := fun x ↦ d.secondMixed x.1
  have hQ : ContinuousAt Q q :=
    LocalGeodesicData.CoordinateBrokenVariationData.position_continuousAt
      d hz hJ hleftNode hrightNode
  have hW : ContinuousAt W q :=
    LocalGeodesicData.CoordinateBrokenVariationData.field_continuousAt
      d hJ hleftVelocity hrightVelocity
  have hV : ContinuousAt V q :=
    LocalGeodesicData.CoordinateBrokenVariationData.velocity_continuousAt
      d hdz hdJ hz hJ hleftNode hrightNode
  have hdV : ContinuousAt dV q :=
    LocalGeodesicData.CoordinateBrokenVariationData.mixed_continuousAt
      d hdJ hJ hleftVelocity hrightVelocity
  have hC₀ : ContinuousAt C₀ q :=
    LocalGeodesicData.CoordinateBrokenVariationData.secondField_continuousAt
      d hleftAcceleration hrightAcceleration
  have hdC₀ : ContinuousAt dC₀ q :=
    LocalGeodesicData.CoordinateBrokenVariationData.secondMixed_continuousAt
      d hleftAcceleration hrightAcceleration
  have hB : ContinuousAt (fun x ↦
      LocalGeodesicData.coordinateCovariantFieldDerivative
        (I := I) (M := M) cov c basis (Q x) (V x) (W x) (dV x)) q :=
    LocalGeodesicData.coordinateCovariantFieldDerivative_continuousAt
      (I := I) (M := M) (cov := cov) c basis hQ hV hW hdV htarget
  have hPWW := LocalGeodesicData.coordinateParallelOperator_apply_continuousAt
    (I := I) (M := M) (cov := cov) c basis hQ hW hW htarget
  let C : ℝ × ℝ → E := fun x ↦ C₀ x +
    LocalGeodesicData.coordinateParallelOperator
      (I := I) (M := M) (E := E) cov c basis (Q x) (W x) (W x)
  have hC : ContinuousAt C q := hC₀.add hPWW
  have hbase :=
    LocalGeodesicData.coordinateParallelOperator_baseFderiv_apply_continuousAt
      (I := I) (M := M) (cov := cov) c basis hQ hW hW hV htarget
  have hPdVW := LocalGeodesicData.coordinateParallelOperator_apply_continuousAt
    (I := I) (M := M) (cov := cov) c basis hQ hdV hW htarget
  have hPWdV := LocalGeodesicData.coordinateParallelOperator_apply_continuousAt
    (I := I) (M := M) (cov := cov) c basis hQ hW hdV htarget
  let dC : ℝ × ℝ → E := fun x ↦ dC₀ x +
    fderiv ℝ (fun z ↦ LocalGeodesicData.coordinateParallelOperator
      (I := I) (M := M) (E := E) cov c basis z (W x) (W x))
        (Q x) (V x) +
    LocalGeodesicData.coordinateParallelOperator
      (I := I) (M := M) (E := E) cov c basis (Q x) (dV x) (W x) +
    LocalGeodesicData.coordinateParallelOperator
      (I := I) (M := M) (E := E) cov c basis (Q x) (W x) (dV x)
  have hdC : ContinuousAt dC q := ((hdC₀.add hbase).add hPdVW).add hPWdV
  have hDtC : ContinuousAt (fun x ↦
      LocalGeodesicData.coordinateCovariantFieldDerivative
        (I := I) (M := M) cov c basis (Q x) (V x) (C x) (dC x)) q :=
    LocalGeodesicData.coordinateCovariantFieldDerivative_continuousAt
      (I := I) (M := M) (cov := cov) c basis hQ hV hC hdC htarget
  have hy : ContinuousAt (fun x ↦ (extChartAt I c).symm (Q x)) q :=
    (continuousAt_extChartAt_symm'' htarget).comp_of_eq hQ rfl
  have hBB := coordinateFrameCombination_inner_continuousAt
    (I := I) (M := M) c basis hy hB hB
      ((extChartAt I c).map_target htarget)
  have hcurv := LocalGeodesicData.coordinateCurvaturePairing_continuousAt
    (I := I) (M := M) (cov := cov) htorsion c basis
      hQ hW hW hV hV htarget hOopen hO hOframe
  have hDtCV := coordinateFrameCombination_inner_continuousAt
    (I := I) (M := M) c basis hy hDtC hV
      ((extChartAt I c).map_target htarget)
  unfold LocalGeodesicData.CoordinateBrokenVariationData.secondVariationDensityAt
  change ContinuousAt (fun x ↦
    inner ℝ
        (LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis
            (LocalGeodesicData.coordinateCovariantFieldDerivative
              (I := I) (M := M) cov c basis (Q x) (V x) (W x) (dV x))
            ((extChartAt I c).symm (Q x)))
        (LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis
            (LocalGeodesicData.coordinateCovariantFieldDerivative
              (I := I) (M := M) cov c basis (Q x) (V x) (W x) (dV x))
            ((extChartAt I c).symm (Q x))) -
      inner ℝ
        (LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis (W x)
            ((extChartAt I c).symm (Q x)))
        (curvature (cov := cov) ((extChartAt I c).symm (Q x))
          (LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := c) basis (W x)
              ((extChartAt I c).symm (Q x)))
          (LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := c) basis (V x)
              ((extChartAt I c).symm (Q x)))
          (LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := c) basis (V x)
              ((extChartAt I c).symm (Q x)))) +
      inner ℝ
        (LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis
            (LocalGeodesicData.coordinateCovariantFieldDerivative
              (I := I) (M := M) cov c basis (Q x) (V x) (C x) (dC x))
            ((extChartAt I c).symm (Q x)))
        (LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis (V x)
            ((extChartAt I c).symm (Q x)))) q
  exact (hBB.sub hcurv).add hDtCV

/-- Position of a global geodesic in one fixed extended chart. -/
def fixedChartPosition
    (G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (c : M) (t : ℝ) : E :=
  extChartAt I c (curve G t)

/-- Velocity of a global geodesic read in the same fixed tangent
trivialization. -/
def fixedChartVelocity
    (G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (c : M) (t : ℝ) : E :=
  (trivializationAt E TM c).continuousLinearMapAt ℝ
    (curve G t) (velocity G t)

/-- A global parallel field read in a fixed tangent trivialization. -/
def GlobalParallelField.fixedChartCoordinates
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (c : M) (t : ℝ) : E :=
  (trivializationAt E TM c).continuousLinearMapAt ℝ
    (curve (shift G t₀) t) (p.field t)

/-- Coordinate representation of the sine-scaled parallel test field. -/
def GlobalParallelField.fixedChartSineField
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (c : M) (L t : ℝ) : E :=
  sineTest L t • p.fixedChartCoordinates c t

/-- Ordinary coordinate derivative of the sine-scaled parallel field. -/
def GlobalParallelField.fixedChartSineFieldDerivative
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (c : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (L t : ℝ) : E :=
  sineTestDeriv L t • p.fixedChartCoordinates c t -
    sineTest L t • LocalGeodesicData.coordinateParallelOperator
      (I := I) (M := M) (E := E) cov c basis
      (fixedChartPosition (shift G t₀) c t)
      (fixedChartVelocity (shift G t₀) c t)
      (p.fixedChartCoordinates c t)

theorem fixedChartPosition_hasDerivAt
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent) (t : ℝ)
    (hframe : IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) c basis ∈ nhds (curve G t)) :
    HasDerivAt (fixedChartPosition (E := E) G c)
      (fixedChartVelocity (E := E) G c t) t := by
  have h := G.hasDerivAt_fixedChartState c basis hmetric t hframe
  have hfst := h.hasFDerivAt.fst.hasDerivAt
  unfold fixedChartPosition fixedChartVelocity
  simpa [secondOrderSystem] using hfst

theorem fixedChartVelocity_hasDerivAt
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent) (t : ℝ)
    (hframe : IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) c basis ∈ nhds (curve G t)) :
    HasDerivAt (fixedChartVelocity (E := E) G c)
      (LocalGeodesicData.coordinateAcceleration
        (I := I) (M := M) cov c basis
        (fixedChartPosition (E := E) G c t)
        (fixedChartVelocity (E := E) G c t)) t := by
  have h := G.hasDerivAt_fixedChartState c basis hmetric t hframe
  have hsnd := h.hasFDerivAt.snd.hasDerivAt
  unfold fixedChartPosition fixedChartVelocity
  simpa [secondOrderSystem] using hsnd

theorem GlobalParallelField.fixedChartCoordinates_hasDerivAt'
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (t : ℝ)
    (hmem : curve (shift G t₀) t ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c basis)
    (hframe : ∀ i : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 (curve (shift G t₀) t),
        LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) c basis i z =
          (trivializationAt E TM c).localFrame basis i z) :
    HasDerivAt (p.fixedChartCoordinates c)
      (-LocalGeodesicData.coordinateParallelOperator
        (I := I) (M := M) (E := E) cov c basis
          (fixedChartPosition (E := E) (shift G t₀) c t)
          (fixedChartVelocity (E := E) (shift G t₀) c t)
          (p.fixedChartCoordinates c t)) t := by
  unfold GlobalParallelField.fixedChartCoordinates
  simpa [fixedChartPosition, fixedChartVelocity] using
    p.fixedChartCoordinates_hasDerivAt hmetric t c basis hmem hframe

theorem GlobalParallelField.fixedChartSineField_hasDerivAt
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (L t : ℝ)
    (hmem : curve (shift G t₀) t ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c basis)
    (hframe : ∀ i : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 (curve (shift G t₀) t),
        LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) c basis i z =
          (trivializationAt E TM c).localFrame basis i z) :
    HasDerivAt (p.fixedChartSineField c L)
      (p.fixedChartSineFieldDerivative c basis L t) t := by
  have hp := p.fixedChartCoordinates_hasDerivAt'
    hmetric c basis t hmem hframe
  have h := (hasDerivAt_sineTest L t).smul hp
  unfold GlobalParallelField.fixedChartSineField
    GlobalParallelField.fixedChartSineFieldDerivative
  convert h using 1
  · funext s
    rfl
  · module

theorem GlobalParallelField.coordinateCovariantFieldDerivative_fixedChartSineField
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (L t : ℝ) :
    LocalGeodesicData.coordinateCovariantFieldDerivative
        (I := I) (M := M) cov c basis
        (fixedChartPosition (E := E) (shift G t₀) c t)
        (fixedChartVelocity (E := E) (shift G t₀) c t)
        (p.fixedChartSineField c L t)
        (p.fixedChartSineFieldDerivative c basis L t) =
      sineTestDeriv L t • p.fixedChartCoordinates c t := by
  unfold LocalGeodesicData.coordinateCovariantFieldDerivative
    GlobalParallelField.fixedChartSineField
    GlobalParallelField.fixedChartSineFieldDerivative
  rw [map_smul]
  module

theorem coordinateFrameCombination_fixedChartReadout
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {y : M} (hy : y ∈ (extChartAt I c).source) (v : TM y) :
    LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c) basis
        ((trivializationAt E TM c).continuousLinearMapAt ℝ y v) y = v := by
  have hchart : y ∈ (chartAt H c).source := by
    rwa [← extChartAt_source (I := I) c]
  have hbase : y ∈ (trivializationAt E TM c).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (I := I) (E := E) c,
      ← extChartAt_source (I := I) c]
    exact hy
  rw [LocalGeodesicData.coordinateFrameCombination_eq_symmL
    (I := I) (M := M) c basis hchart]
  exact ((trivializationAt E (TangentSpace I : M → Type _) c)
    |>.symmL_continuousLinearMapAt (R := ℝ) hbase v)

theorem GlobalParallelField.coordinateFrameCombination_fixedChartSineField
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (L t : ℝ) (hsource : curve (shift G t₀) t ∈ (extChartAt I c).source) :
    LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c) basis
        (p.fixedChartSineField c L t) (curve (shift G t₀) t) =
      p.sineTestField L t := by
  unfold GlobalParallelField.fixedChartSineField
    GlobalParallelField.sineTestField
  rw [LocalGeodesicData.coordinateFrameCombination_smul]
  have hread :
      LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis
          (p.fixedChartCoordinates c t) (curve (shift G t₀) t) = p.field t := by
    unfold GlobalParallelField.fixedChartCoordinates
    exact coordinateFrameCombination_fixedChartReadout
      (I := I) (M := M) c basis hsource (p.field t)
  rw [hread]

theorem GlobalParallelField.coordinateFrameCombination_fixedChartSineDerivative
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (L t : ℝ) (hsource : curve (shift G t₀) t ∈ (extChartAt I c).source) :
    LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c) basis
        (LocalGeodesicData.coordinateCovariantFieldDerivative
          (I := I) (M := M) cov c basis
          (fixedChartPosition (E := E) (shift G t₀) c t)
          (fixedChartVelocity (E := E) (shift G t₀) c t)
          (p.fixedChartSineField c L t)
          (p.fixedChartSineFieldDerivative c basis L t))
        (curve (shift G t₀) t) =
      p.sineTestDerivativeField L t := by
  rw [p.coordinateCovariantFieldDerivative_fixedChartSineField c basis L t]
  unfold GlobalParallelField.sineTestDerivativeField
  rw [LocalGeodesicData.coordinateFrameCombination_smul]
  have hread :
      LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis
          (p.fixedChartCoordinates c t) (curve (shift G t₀) t) = p.field t := by
    unfold GlobalParallelField.fixedChartCoordinates
    exact coordinateFrameCombination_fixedChartReadout
      (I := I) (M := M) c basis hsource (p.field t)
  rw [hread]

/-- The coordinate index density of a sine-scaled global parallel field is
the intrinsic index-form integrand. -/
theorem LocalGeodesicData.CoordinateBrokenVariationData.indexDensity_eq_globalSine
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (d : LocalGeodesicData.CoordinateBrokenVariationData E)
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (L t : ℝ)
    (hz : d.z t = fixedChartPosition (E := E) (shift G t₀) c t)
    (hdz : d.dz t = fixedChartVelocity (E := E) (shift G t₀) c t)
    (hJ : d.J t = p.fixedChartSineField c L t)
    (hdJ : d.dJ t = p.fixedChartSineFieldDerivative c basis L t)
    (hsource : curve (shift G t₀) t ∈ (extChartAt I c).source) :
    d.indexDensity (I := I) (M := M) cov c basis t =
      inner ℝ (p.sineTestDerivativeField L t)
          (p.sineTestDerivativeField L t) -
        inner ℝ (p.sineTestField L t)
          (curvature (cov := cov) (curve (shift G t₀) t)
            (p.sineTestField L t)
            (velocity (shift G t₀) t)
            (velocity (shift G t₀) t)) := by
  have hy : (extChartAt I c).symm
      (fixedChartPosition (E := E) (shift G t₀) c t) =
        curve (shift G t₀) t := by
    unfold fixedChartPosition
    exact (extChartAt I c).left_inv hsource
  have hDJ := p.coordinateFrameCombination_fixedChartSineDerivative
    c basis L t hsource
  have hfield := p.coordinateFrameCombination_fixedChartSineField
    c basis L t hsource
  have hvel :
      LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c) basis
          (fixedChartVelocity (E := E) (shift G t₀) c t)
          (curve (shift G t₀) t) = velocity (shift G t₀) t := by
    unfold fixedChartVelocity
    exact coordinateFrameCombination_fixedChartReadout
      (I := I) (M := M) c basis hsource (velocity (shift G t₀) t)
  unfold LocalGeodesicData.CoordinateBrokenVariationData.indexDensity
  dsimp only
  rw [hz, hdz, hJ, hdJ, hy, hDJ, hfield, hvel]

/-- A compact time interval admits a monotone finite subdivision such that
each closed piece lies in one open fixed-frame agreement neighbourhood. -/
theorem exists_smoothFrameAgreementPartition
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    {L : ℝ} (hL : 0 ≤ L) :
    ∃ τ : ℕ → Icc (0 : ℝ) L,
      τ 0 = ⟨0, le_rfl, hL⟩ ∧ Monotone τ ∧
      (∃ m, ∀ n ≥ m, τ n = ⟨L, hL, le_rfl⟩) ∧
      ∀ n, ∃ c : M, ∃ O : Set M,
        IsOpen O ∧
        O ⊆ IntrinsicAcceleration.smoothFrameAgreementSet
          (I := I) (M := M) c (Module.finBasis ℝ E) ∧
        ∀ s : Icc (0 : ℝ) L, s ∈ Icc (τ n) (τ (n + 1)) →
          curve G s.1 ∈ O := by
  classical
  have hstate : Continuous G.state :=
    continuous_iff_continuousAt.2 (fun t ↦ G.continuousAt_state t)
  have hcurve : Continuous (curve G) := by
    exact (FiberBundle.continuous_proj E TM).comp hstate
  have hopen : ∀ q : Icc (0 : ℝ) L, ∃ O : Set M,
      IsOpen O ∧ curve G q.1 ∈ O ∧
      O ⊆ IntrinsicAcceleration.smoothFrameAgreementSet
        (I := I) (M := M) (curve G q.1) (Module.finBasis ℝ E) := by
    intro q
    obtain ⟨O, hOsub, hOopen, hqO⟩ := mem_nhds_iff.mp
      (IntrinsicAcceleration.smoothFrameAgreementSet_mem_nhds
        (I := I) (M := M) (curve G q.1) (Module.finBasis ℝ E))
    exact ⟨O, hOopen, hqO, hOsub⟩
  choose O hOopen hcenter hOsub using hopen
  let U : Icc (0 : ℝ) L → Set (Icc (0 : ℝ) L) := fun q ↦
    {s | curve G s.1 ∈ O q}
  have hUopen : ∀ q, IsOpen (U q) := by
    intro q
    exact (hOopen q).preimage (hcurve.comp continuous_subtype_val)
  have hUcover : (Set.univ : Set (Icc (0 : ℝ) L)) ⊆ ⋃ q, U q := by
    intro s _hs
    exact mem_iUnion.2 ⟨s, hcenter s⟩
  obtain ⟨τ, hτ0, hτmono, hτevent, hτpiece⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hL hUopen hUcover
  have hτ0' : τ 0 = ⟨0, le_rfl, hL⟩ := Subtype.ext hτ0
  obtain ⟨m, hm⟩ := hτevent
  have hτevent' : ∃ m, ∀ n ≥ m, τ n = ⟨L, hL, le_rfl⟩ := by
    refine ⟨m, fun n hn ↦ Subtype.ext (hm n hn)⟩
  refine ⟨τ, hτ0', hτmono, hτevent', ?_⟩
  intro n
  obtain ⟨q, hq⟩ := hτpiece n
  refine ⟨curve G q.1, O q, hOopen q, hOsub q, ?_⟩
  intro s hs
  exact hq hs

/-- Coordinate data for one broken sine variation piece.  The two endpoint
node curves are genuine global geodesics; adjacent pieces can therefore use
the same node curve while reading it in different charts. -/
def GlobalParallelField.sineBrokenChartData
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (L : ℝ) {a b : ℝ}
    (Nleft : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) a) (p.sineTestField L a))
    (Nright : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) b) (p.sineTestField L b))
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    LocalGeodesicData.CoordinateBrokenVariationData E where
  a := a
  b := b
  z := fixedChartPosition (E := E) (shift G t₀) c
  dz := fixedChartVelocity (E := E) (shift G t₀) c
  ddz := fun t ↦ LocalGeodesicData.coordinateAcceleration
    (I := I) (M := M) cov c basis
      (fixedChartPosition (E := E) (shift G t₀) c t)
      (fixedChartVelocity (E := E) (shift G t₀) c t)
  J := p.fixedChartSineField c L
  dJ := p.fixedChartSineFieldDerivative c basis L
  leftNode := fixedChartPosition (E := E) Nleft c
  rightNode := fixedChartPosition (E := E) Nright c
  leftVelocity := fixedChartVelocity (E := E) Nleft c
  rightVelocity := fixedChartVelocity (E := E) Nright c
  leftAcceleration := fun e ↦ LocalGeodesicData.coordinateAcceleration
    (I := I) (M := M) cov c basis
      (fixedChartPosition (E := E) Nleft c e)
      (fixedChartVelocity (E := E) Nleft c e)
  rightAcceleration := fun e ↦ LocalGeodesicData.coordinateAcceleration
    (I := I) (M := M) cov c basis
      (fixedChartPosition (E := E) Nright c e)
      (fixedChartVelocity (E := E) Nright c e)

@[simp] theorem GlobalParallelField.sineBrokenChartData_a
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (L : ℝ) {a b : ℝ}
    (Nleft : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) a) (p.sineTestField L a))
    (Nright : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) b) (p.sineTestField L b))
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    (p.sineBrokenChartData L Nleft Nright c basis).a = a := rfl

@[simp] theorem GlobalParallelField.sineBrokenChartData_b
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (L : ℝ) {a b : ℝ}
    (Nleft : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) a) (p.sineTestField L a))
    (Nright : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) b) (p.sineTestField L b))
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    (p.sineBrokenChartData L Nleft Nright c basis).b = b := rfl

theorem GlobalParallelField.sineBrokenChartData_indexDensity
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (L : ℝ) {a b : ℝ}
    (Nleft : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) a) (p.sineTestField L a))
    (Nright : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) b) (p.sineTestField L b))
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (t : ℝ)
    (hsource : curve (shift G t₀) t ∈ (extChartAt I c).source) :
    (p.sineBrokenChartData L Nleft Nright c basis).indexDensity
        (I := I) (M := M) cov c basis t =
      inner ℝ (p.sineTestDerivativeField L t)
          (p.sineTestDerivativeField L t) -
        inner ℝ (p.sineTestField L t)
          (curvature (cov := cov) (curve (shift G t₀) t)
            (p.sineTestField L t)
            (velocity (shift G t₀) t)
            (velocity (shift G t₀) t)) := by
  apply LocalGeodesicData.CoordinateBrokenVariationData.indexDensity_eq_globalSine
    (p := p) (L := L) (t := t) (c := c) (basis := basis)
      (hsource := hsource) <;> rfl

theorem GlobalParallelField.sineBrokenChartData_node_initial_data
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (L : ℝ) {a b : ℝ}
    (Nleft : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) a) (p.sineTestField L a))
    (Nright : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) b) (p.sineTestField L b))
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    let d := p.sineBrokenChartData L Nleft Nright c basis
    d.leftNode 0 = d.z d.a ∧
    d.rightNode 0 = d.z d.b ∧
    d.leftVelocity 0 = d.J d.a ∧
    d.rightVelocity 0 = d.J d.b ∧
    d.leftAcceleration 0 =
      -LocalGeodesicData.coordinateParallelOperator
        (I := I) (M := M) (E := E) cov c basis
          (d.z d.a) (d.J d.a) (d.J d.a) ∧
    d.rightAcceleration 0 =
      -LocalGeodesicData.coordinateParallelOperator
        (I := I) (M := M) (E := E) cov c basis
          (d.z d.b) (d.J d.b) (d.J d.b) := by
  dsimp only
  have hcurveLeft := Nleft.curve_initial
  have hcurveRight := Nright.curve_initial
  have hvelocityLeft := Nleft.velocity_initial
  have hvelocityRight := Nright.velocity_initial
  simp only [GlobalParallelField.sineBrokenChartData,
    fixedChartPosition, fixedChartVelocity]
  rw [hcurveLeft, hcurveRight, hvelocityLeft, hvelocityRight]
  have hcoordLeft :
      (trivializationAt E TM c).continuousLinearMapAt ℝ
          (curve (shift G t₀) a) (p.sineTestField L a) =
        p.fixedChartSineField c L a := by
    unfold GlobalParallelField.sineTestField
      GlobalParallelField.fixedChartSineField
      GlobalParallelField.fixedChartCoordinates
    rw [map_smul]
  have hcoordRight :
      (trivializationAt E TM c).continuousLinearMapAt ℝ
          (curve (shift G t₀) b) (p.sineTestField L b) =
        p.fixedChartSineField c L b := by
    unfold GlobalParallelField.sineTestField
      GlobalParallelField.fixedChartSineField
      GlobalParallelField.fixedChartCoordinates
    rw [map_smul]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact hcoordLeft
  constructor
  · exact hcoordRight
  constructor
  · rw [LocalGeodesicData.coordinateAcceleration_eq_neg_connectionTerm,
      ← LocalGeodesicData.coordinateParallelOperator_self_eq_coordinateConnectionTerm,
      hcoordLeft]
  · rw [LocalGeodesicData.coordinateAcceleration_eq_neg_connectionTerm,
      ← LocalGeodesicData.coordinateParallelOperator_self_eq_coordinateConnectionTerm,
      hcoordRight]

theorem GlobalParallelField.sineBrokenChartData_base_derivatives
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    (L : ℝ) {a b : ℝ}
    (Nleft : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) a) (p.sineTestField L a))
    (Nright : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) b) (p.sineTestField L b))
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {O : Set M} (hOopen : IsOpen O)
    (hOsub : O ⊆ IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) c basis)
    {t : ℝ} (ht : curve (shift G t₀) t ∈ O) :
    let d := p.sineBrokenChartData L Nleft Nright c basis
    HasDerivAt d.z (d.dz t) t ∧
    HasDerivAt d.dz (d.ddz t) t ∧
    HasDerivAt d.J (d.dJ t) t ∧
    LocalGeodesicData.coordinateCovariantFieldDerivative
      (I := I) (M := M) cov c basis
        (d.z t) (d.dz t) (d.dz t) (d.ddz t) = 0 ∧
    d.z t ∈ (extChartAt I c).target ∧
    ∀ k : Fin (Module.finrank ℝ E),
      LocalGeodesicData.smoothFrame
        (I := I) (M := M) (E := E) c basis k =ᶠ[
          nhds ((extChartAt I c).symm (d.z t))]
        (trivializationAt E TM c).localFrame basis k := by
  let d := p.sineBrokenChartData L Nleft Nright c basis
  have hmem := hOsub ht
  have hagree : IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) c basis ∈ nhds (curve (shift G t₀) t) :=
    mem_of_superset (hOopen.mem_nhds ht) hOsub
  have hframe : ∀ k : Fin (Module.finrank ℝ E),
      LocalGeodesicData.smoothFrame
        (I := I) (M := M) (E := E) c basis k =ᶠ[
          nhds (curve (shift G t₀) t)]
        (trivializationAt E TM c).localFrame basis k := by
    intro k
    filter_upwards [hOopen.mem_nhds ht] with y hy
    exact (hOsub hy).2 k
  have hz := fixedChartPosition_hasDerivAt
    (I := I) (M := M) (shift G t₀) c basis hmetric t hagree
  have hdz := fixedChartVelocity_hasDerivAt
    (I := I) (M := M) (shift G t₀) c basis hmetric t hagree
  have hJ := p.fixedChartSineField_hasDerivAt
    hmetric c basis L t hmem hframe
  have htarget : fixedChartPosition (E := E) (shift G t₀) c t ∈
      (extChartAt I c).target :=
    (extChartAt I c).map_source hmem.1
  have hy : (extChartAt I c).symm
      (fixedChartPosition (E := E) (shift G t₀) c t) =
        curve (shift G t₀) t := by
    unfold fixedChartPosition
    exact (extChartAt I c).left_inv hmem.1
  refine ⟨hz, hdz, hJ, ?_, htarget, ?_⟩
  · simp [d, GlobalParallelField.sineBrokenChartData,
      LocalGeodesicData.coordinateCovariantFieldDerivative,
      LocalGeodesicData.coordinateAcceleration_eq_neg_connectionTerm,
      ← LocalGeodesicData.coordinateParallelOperator_self_eq_coordinateConnectionTerm]
  · intro k
    change LocalGeodesicData.smoothFrame
        (I := I) (M := M) (E := E) c basis k =ᶠ[
          nhds ((extChartAt I c).symm
            (fixedChartPosition (E := E) (shift G t₀) c t))]
        (trivializationAt E TM c).localFrame basis k
    rw [hy]
    exact hframe k

theorem GlobalParallelField.sineBrokenChartData_node_derivatives
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    (L : ℝ) {a b : ℝ}
    (Nleft : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) a) (p.sineTestField L a))
    (Nright : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) b) (p.sineTestField L b))
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {O : Set M} (hOopen : IsOpen O)
    (hOsub : O ⊆ IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) c basis)
    {e : ℝ} (hleft : curve Nleft e ∈ O) (hright : curve Nright e ∈ O) :
    let d := p.sineBrokenChartData L Nleft Nright c basis
    HasDerivAt d.leftNode (d.leftVelocity e) e ∧
    HasDerivAt d.rightNode (d.rightVelocity e) e ∧
    HasDerivAt d.leftVelocity (d.leftAcceleration e) e ∧
    HasDerivAt d.rightVelocity (d.rightAcceleration e) e := by
  let d := p.sineBrokenChartData L Nleft Nright c basis
  have hleftAgree : IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) c basis ∈ nhds (curve Nleft e) :=
    mem_of_superset (hOopen.mem_nhds hleft) hOsub
  have hrightAgree : IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) c basis ∈ nhds (curve Nright e) :=
    mem_of_superset (hOopen.mem_nhds hright) hOsub
  exact ⟨
    fixedChartPosition_hasDerivAt (I := I) (M := M)
      Nleft c basis hmetric e hleftAgree,
    fixedChartPosition_hasDerivAt (I := I) (M := M)
      Nright c basis hmetric e hrightAgree,
    fixedChartVelocity_hasDerivAt (I := I) (M := M)
      Nleft c basis hmetric e hleftAgree,
    fixedChartVelocity_hasDerivAt (I := I) (M := M)
      Nright c basis hmetric e hrightAgree⟩

theorem GlobalParallelField.sineBrokenChartData_component_continuity
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    (L : ℝ) {a b e t : ℝ}
    (Nleft : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) a) (p.sineTestField L a))
    (Nright : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) b) (p.sineTestField L b))
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {O : Set M} (hOopen : IsOpen O)
    (hOsub : O ⊆ IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) c basis)
    (hbase : curve (shift G t₀) t ∈ O)
    (hleft : curve Nleft e ∈ O) (hright : curve Nright e ∈ O) :
    let d := p.sineBrokenChartData L Nleft Nright c basis
    ContinuousAt d.z t ∧ ContinuousAt d.dz t ∧
    ContinuousAt d.J t ∧ ContinuousAt d.dJ t ∧
    ContinuousAt d.leftNode e ∧ ContinuousAt d.rightNode e ∧
    ContinuousAt d.leftVelocity e ∧ ContinuousAt d.rightVelocity e ∧
    ContinuousAt d.leftAcceleration e ∧
      ContinuousAt d.rightAcceleration e := by
  let d := p.sineBrokenChartData L Nleft Nright c basis
  obtain ⟨hz, hdz, hJ, _hgeo, _htarget, _hframe⟩ :=
    p.sineBrokenChartData_base_derivatives hmetric L Nleft Nright
      c basis hOopen hOsub hbase
  obtain ⟨hln, hrn, hlv, hrv⟩ :=
    p.sineBrokenChartData_node_derivatives hmetric L Nleft Nright
      c basis hOopen hOsub hleft hright
  have hmem := hOsub hbase
  have hframe : ∀ k : Fin (Module.finrank ℝ E),
      LocalGeodesicData.smoothFrame
        (I := I) (M := M) (E := E) c basis k =ᶠ[
          nhds (curve (shift G t₀) t)]
        (trivializationAt E TM c).localFrame basis k := by
    intro k
    filter_upwards [hOopen.mem_nhds hbase] with y hy
    exact (hOsub hy).2 k
  have hpcoord := p.fixedChartCoordinates_hasDerivAt'
    hmetric c basis t hmem hframe
  have hPcoord :=
    LocalGeodesicData.coordinateParallelOperator_apply_continuousAt
      (I := I) (M := M) (cov := cov) c basis
      hz.continuousAt hdz.continuousAt hpcoord.continuousAt
      ((extChartAt I c).map_source hmem.1)
  have hdJcont : ContinuousAt d.dJ t := by
    change ContinuousAt
      (p.fixedChartSineFieldDerivative c basis L) t
    unfold GlobalParallelField.fixedChartSineFieldDerivative
    exact ((show ContinuousAt (sineTestDeriv L) t by
        unfold sineTestDeriv
        fun_prop).smul
      hpcoord.continuousAt).sub
        ((hasDerivAt_sineTest L t).continuousAt.smul hPcoord)
  have hleftTarget : fixedChartPosition (E := E) Nleft c e ∈
      (extChartAt I c).target :=
    (extChartAt I c).map_source (hOsub hleft).1
  have hrightTarget : fixedChartPosition (E := E) Nright c e ∈
      (extChartAt I c).target :=
    (extChartAt I c).map_source (hOsub hright).1
  have hleftP := LocalGeodesicData.coordinateParallelOperator_apply_continuousAt
    (I := I) (M := M) (cov := cov) c basis
      hln.continuousAt hlv.continuousAt hlv.continuousAt hleftTarget
  have hrightP := LocalGeodesicData.coordinateParallelOperator_apply_continuousAt
    (I := I) (M := M) (cov := cov) c basis
      hrn.continuousAt hrv.continuousAt hrv.continuousAt hrightTarget
  have hla : ContinuousAt d.leftAcceleration e := by
    change ContinuousAt (fun s ↦ LocalGeodesicData.coordinateAcceleration
      (I := I) (M := M) cov c basis
        (d.leftNode s) (d.leftVelocity s)) e
    convert hleftP.neg using 1
    funext s
    rw [LocalGeodesicData.coordinateAcceleration_eq_neg_connectionTerm,
      ← LocalGeodesicData.coordinateParallelOperator_self_eq_coordinateConnectionTerm]
    rfl
  have hra : ContinuousAt d.rightAcceleration e := by
    change ContinuousAt (fun s ↦ LocalGeodesicData.coordinateAcceleration
      (I := I) (M := M) cov c basis
        (d.rightNode s) (d.rightVelocity s)) e
    convert hrightP.neg using 1
    funext s
    rw [LocalGeodesicData.coordinateAcceleration_eq_neg_connectionTerm,
      ← LocalGeodesicData.coordinateParallelOperator_self_eq_coordinateConnectionTerm]
    rfl
  exact ⟨hz.continuousAt, hdz.continuousAt, hJ.continuousAt, hdJcont,
    hln.continuousAt, hrn.continuousAt, hlv.continuousAt, hrv.continuousAt,
    hla, hra⟩
/-- Uniform compact parameter control for one chart piece.  The endpoint
geodesics and the whole spliced variation stay in the same open frame region,
and all three densities needed for two differentiations under the integral
are jointly continuous on the resulting compact rectangle. -/
theorem GlobalParallelField.exists_sineBrokenChartData_regular_rectangle
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [IsContMDiffRiemannianBundle I 2 E TM]
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    (htorsion : cov.torsion = 0)
    (L : ℝ) {a b : ℝ} (hab : a < b)
    (Nleft : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) a) (p.sineTestField L a))
    (Nright : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) b) (p.sineTestField L b))
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {O : Set M} (hOopen : IsOpen O)
    (hOsub : O ⊆ IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) c basis)
    (hbase : ∀ t ∈ Icc a b, curve (shift G t₀) t ∈ O) :
    let d := p.sineBrokenChartData L Nleft Nright c basis
    ∃ s : Set ℝ, IsCompact s ∧ s ∈ nhds (0 : ℝ) ∧
      ContinuousOn (fun q : ℝ × ℝ ↦
        d.energyDensity (I := I) (M := M) c basis q.1 q.2)
          (s ×ˢ Icc a b) ∧
      ContinuousOn (fun q : ℝ × ℝ ↦
        d.firstVariationDensity (I := I) (M := M) cov c basis q.1 q.2)
          (s ×ˢ Icc a b) ∧
      ContinuousOn (fun q : ℝ × ℝ ↦
        d.secondVariationDensityAt (I := I) (M := M) cov c basis q.1 q.2)
          (s ×ˢ Icc a b) ∧
      (∀ e ∈ s, curve Nleft e ∈ O ∧ curve Nright e ∈ O) ∧
      (∀ e ∈ s, ∀ t ∈ Icc a b,
        d.position e t ∈ (extChartAt I c).target ∧
        (extChartAt I c).symm (d.position e t) ∈ O) := by
  letI : IsContinuousRiemannianBundle E TM := by
    rcases (inferInstance : IsContMDiffRiemannianBundle I 1 E TM).exists_contMDiff with
      ⟨g, hg, hinner⟩
    exact ⟨g, hg.continuous, hinner⟩
  let d := p.sineBrokenChartData L Nleft Nright c basis
  obtain ⟨hleft0, hright0, _hleftV0, _hrightV0, _hla0, _hra0⟩ :=
    p.sineBrokenChartData_node_initial_data L Nleft Nright c basis
  let T : Set E := (extChartAt I c).target ∩
    (extChartAt I c).symm ⁻¹' O
  have hTopen : IsOpen T := by
    exact (continuousOn_extChartAt_symm (I := I) c).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := I) c) hOopen
  let D : Set (ℝ × ℝ) := {q |
    d.position q.1 q.2 ∈ T ∧ curve Nleft q.1 ∈ O ∧ curve Nright q.1 ∈ O}
  have hleftCurve : Continuous (curve Nleft) := by
    have hstate : Continuous Nleft.state :=
      continuous_iff_continuousAt.2 (fun e ↦ Nleft.continuousAt_state e)
    exact (FiberBundle.continuous_proj E TM).comp hstate
  have hrightCurve : Continuous (curve Nright) := by
    have hstate : Continuous Nright.state :=
      continuous_iff_continuousAt.2 (fun e ↦ Nright.continuousAt_state e)
    exact (FiberBundle.continuous_proj E TM).comp hstate
  have hslice : ({0} : Set ℝ) ×ˢ Icc a b ⊆ interior D := by
    rintro ⟨e, t⟩ ⟨he, ht⟩
    have he0 : e = 0 := he
    subst e
    have hbaseT := hbase t ht
    have hleftBase : curve Nleft 0 ∈ O := by
      rw [Nleft.curve_initial]
      exact hbase a ⟨le_rfl, hab.le⟩
    have hrightBase : curve Nright 0 ∈ O := by
      rw [Nright.curve_initial]
      exact hbase b ⟨hab.le, le_rfl⟩
    obtain ⟨hz, _hdz, hJ, _hgeo, _htarget, _hframe⟩ :=
      p.sineBrokenChartData_base_derivatives hmetric L Nleft Nright
        c basis hOopen hOsub hbaseT
    obtain ⟨hln, hrn, _hlv, _hrv⟩ :=
      p.sineBrokenChartData_node_derivatives hmetric L Nleft Nright
        c basis hOopen hOsub hleftBase hrightBase
    have hz' : ContinuousAt d.z t := hz.continuousAt
    have hJ' : ContinuousAt d.J t := hJ.continuousAt
    have hln' : ContinuousAt d.leftNode 0 := hln.continuousAt
    have hrn' : ContinuousAt d.rightNode 0 := hrn.continuousAt
    have hQ : ContinuousAt (fun q : ℝ × ℝ ↦ d.position q.1 q.2) (0, t) :=
      LocalGeodesicData.CoordinateBrokenVariationData.position_continuousAt
        d hz' hJ' hln' hrn'
    have hposition0 : d.position 0 t = d.z t := by
      unfold LocalGeodesicData.CoordinateBrokenVariationData.position
      exact LocalGeodesicData.coordinateBrokenVariationPiece_zero
        d.a d.b d.z d.J d.leftNode d.rightNode
          hleft0 hright0 t
    have hzTarget : d.z t ∈ (extChartAt I c).target := by
      change fixedChartPosition (E := E) (shift G t₀) c t ∈ _
      exact (extChartAt I c).map_source (hOsub hbaseT).1
    have hzO : (extChartAt I c).symm (d.z t) ∈ O := by
      change (extChartAt I c).symm
        (fixedChartPosition (E := E) (shift G t₀) c t) ∈ O
      rw [show (extChartAt I c).symm
        (fixedChartPosition (E := E) (shift G t₀) c t) =
          curve (shift G t₀) t by
        unfold fixedChartPosition
        exact (extChartAt I c).left_inv (hOsub hbaseT).1]
      exact hbaseT
    have hQT : d.position 0 t ∈ T := by
      rw [hposition0]
      exact ⟨hzTarget, hzO⟩
    have hQnear : {q : ℝ × ℝ | d.position q.1 q.2 ∈ T} ∈
        nhds (0, t) :=
      hQ.preimage_mem_nhds (hTopen.mem_nhds hQT)
    have hleftNear : {q : ℝ × ℝ | curve Nleft q.1 ∈ O} ∈
        nhds (0, t) :=
      (hleftCurve.continuousAt.comp continuousAt_fst).preimage_mem_nhds
        (hOopen.mem_nhds hleftBase)
    have hrightNear : {q : ℝ × ℝ | curve Nright q.1 ∈ O} ∈
        nhds (0, t) :=
      (hrightCurve.continuousAt.comp continuousAt_fst).preimage_mem_nhds
        (hOopen.mem_nhds hrightBase)
    apply mem_interior_iff_mem_nhds.2
    filter_upwards [hQnear, hleftNear, hrightNear] with q hq hl hr
    exact ⟨hq, hl, hr⟩
  obtain ⟨u, v, huOpen, hvOpen, hzeroU, htimeV, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc isOpen_interior hslice
  have hu : u ∈ nhds (0 : ℝ) :=
    huOpen.mem_nhds (hzeroU (mem_singleton 0))
  obtain ⟨l, r, _hzeroIcc, hsnhds, hsu⟩ :=
    exists_Icc_mem_subset_of_mem_nhds hu
  let s : Set ℝ := Icc l r
  have hsCompact : IsCompact s := isCompact_Icc
  have hgood : ∀ e ∈ s, ∀ t ∈ Icc a b,
      d.position e t ∈ (extChartAt I c).target ∧
      (extChartAt I c).symm (d.position e t) ∈ O ∧
      curve Nleft e ∈ O ∧ curve Nright e ∈ O := by
    intro e he t ht
    have hD : (e, t) ∈ D :=
      interior_subset (huv ⟨hsu he, htimeV ht⟩)
    exact ⟨hD.1.1, hD.1.2, hD.2.1, hD.2.2⟩
  have hcomponents : ∀ q ∈ s ×ˢ Icc a b,
      ContinuousAt d.z q.2 ∧ ContinuousAt d.dz q.2 ∧
      ContinuousAt d.J q.2 ∧ ContinuousAt d.dJ q.2 ∧
      ContinuousAt d.leftNode q.1 ∧ ContinuousAt d.rightNode q.1 ∧
      ContinuousAt d.leftVelocity q.1 ∧ ContinuousAt d.rightVelocity q.1 ∧
      ContinuousAt d.leftAcceleration q.1 ∧
        ContinuousAt d.rightAcceleration q.1 := by
    intro q hq
    have hg := hgood q.1 hq.1 q.2 hq.2
    exact p.sineBrokenChartData_component_continuity hmetric L Nleft Nright
      c basis hOopen hOsub (hbase q.2 hq.2) hg.2.2.1 hg.2.2.2
  have henergy : ContinuousOn (fun q : ℝ × ℝ ↦
      d.energyDensity (I := I) (M := M) c basis q.1 q.2)
      (s ×ˢ Icc a b) := by
    intro q hq
    obtain ⟨hz, hdz, hJ, hdJ, hln, hrn, _hlv, _hrv, _hla, _hra⟩ :=
      hcomponents q hq
    exact (LocalGeodesicData.CoordinateBrokenVariationData.energyDensity_continuousAt
      d c basis hz hdz hJ hdJ hln hrn (hgood q.1 hq.1 q.2 hq.2).1).continuousWithinAt
  have hfirst : ContinuousOn (fun q : ℝ × ℝ ↦
      d.firstVariationDensity (I := I) (M := M) cov c basis q.1 q.2)
      (s ×ˢ Icc a b) := by
    intro q hq
    obtain ⟨hz, hdz, hJ, hdJ, hln, hrn, hlv, hrv, _hla, _hra⟩ :=
      hcomponents q hq
    exact (LocalGeodesicData.CoordinateBrokenVariationData.firstVariationDensity_continuousAt
      d c basis hz hdz hJ hdJ hln hrn hlv hrv
        (hgood q.1 hq.1 q.2 hq.2).1).continuousWithinAt
  have hsecond : ContinuousOn (fun q : ℝ × ℝ ↦
      d.secondVariationDensityAt (I := I) (M := M) cov c basis q.1 q.2)
      (s ×ˢ Icc a b) := by
    intro q hq
    obtain ⟨hz, hdz, hJ, hdJ, hln, hrn, hlv, hrv, hla, hra⟩ :=
      hcomponents q hq
    have hg := hgood q.1 hq.1 q.2 hq.2
    exact (LocalGeodesicData.CoordinateBrokenVariationData.secondVariationDensityAt_continuousAt
      d htorsion c basis hz hdz hJ hdJ hln hrn hlv hrv hla hra
        hg.1 hOopen hg.2.1 (fun y hy k ↦ (hOsub hy).2 k)).continuousWithinAt
  refine ⟨s, hsCompact, hsnhds, henergy, hfirst, hsecond, ?_, ?_⟩
  · intro e he
    have hg := hgood e he a ⟨le_rfl, hab.le⟩
    exact ⟨hg.2.2.1, hg.2.2.2⟩
  · intro e he t ht
    have hg := hgood e he t ht
    exact ⟨hg.1, hg.2.1⟩

theorem GlobalParallelField.sineBrokenChartData_boundaryPairing_zero
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (L : ℝ) {a b : ℝ} (hab : a < b)
    (Nleft : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) a) (p.sineTestField L a))
    (Nright : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) b) (p.sineTestField L b))
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    let d := p.sineBrokenChartData L Nleft Nright c basis
    d.boundaryPairing (I := I) (M := M) cov c basis d.a = 0 ∧
      d.boundaryPairing (I := I) (M := M) cov c basis d.b = 0 := by
  let d := p.sineBrokenChartData L Nleft Nright c basis
  obtain ⟨_hln, _hrn, _hlv, _hrv, hla, hra⟩ :=
    p.sineBrokenChartData_node_initial_data L Nleft Nright c basis
  have hleft : d.secondCovariantField
      (I := I) (M := M) cov c basis d.a = 0 := by
    unfold LocalGeodesicData.CoordinateBrokenVariationData.secondCovariantField
    exact LocalGeodesicData.coordinateBrokenVariation_secondCovariantField_left_eq_zero
      (I := I) (M := M) cov c basis hab d.z d.J
        d.leftAcceleration d.rightAcceleration hla
  have hright : d.secondCovariantField
      (I := I) (M := M) cov c basis d.b = 0 := by
    unfold LocalGeodesicData.CoordinateBrokenVariationData.secondCovariantField
    exact LocalGeodesicData.coordinateBrokenVariation_secondCovariantField_right_eq_zero
      (I := I) (M := M) cov c basis hab d.z d.J
        d.leftAcceleration d.rightAcceleration hra
  exact ⟨
    d.boundaryPairing_eq_zero_of_secondCovariantField_eq_zero
      (I := I) (M := M) cov c basis hleft,
    d.boundaryPairing_eq_zero_of_secondCovariantField_eq_zero
      (I := I) (M := M) cov c basis hright⟩
/-- On one strict chart piece, the shared-node broken sine variation is
locally `C²` in its variation parameter and its integrated second derivative
is exactly the intrinsic index-form integral on that piece. -/
theorem GlobalParallelField.sineBrokenChartData_piece_secondVariation
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [IsContMDiffRiemannianBundle I 2 E TM]
    {G : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve G t₀)}
    (p : GlobalParallelField (I := I) (M := M) G t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    (htorsion : cov.torsion = 0)
    (L : ℝ) {a b : ℝ} (hab : a < b)
    (Nleft : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) a) (p.sineTestField L a))
    (Nright : GlobalGeodesic (I := I) (M := M) cov
      (curve (shift G t₀) b) (p.sineTestField L b))
    (c : M) (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {O : Set M} (hOopen : IsOpen O)
    (hOsub : O ⊆ IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) c basis)
    (hbase : ∀ t ∈ Icc a b, curve (shift G t₀) t ∈ O) :
    let d := p.sineBrokenChartData L Nleft Nright c basis
    ContDiffAt ℝ 2
        (fun e ↦ ∫ t in a..b,
          d.energyDensity (I := I) (M := M) c basis e t) 0 ∧
      iteratedDeriv 2
          (fun e ↦ ∫ t in a..b,
            d.energyDensity (I := I) (M := M) c basis e t) 0 =
        ∫ t in a..b,
          inner ℝ (p.sineTestDerivativeField L t)
              (p.sineTestDerivativeField L t) -
            inner ℝ (p.sineTestField L t)
              (curvature (cov := cov) (curve (shift G t₀) t)
                (p.sineTestField L t)
                (velocity (shift G t₀) t)
                (velocity (shift G t₀) t)) := by
  letI : IsContinuousRiemannianBundle E TM := by
    rcases (inferInstance : IsContMDiffRiemannianBundle I 1 E TM).exists_contMDiff with
      ⟨g, hg, hinner⟩
    exact ⟨g, hg.continuous, hinner⟩
  let d := p.sineBrokenChartData L Nleft Nright c basis
  let K : ℝ → ℝ := fun t ↦
    inner ℝ (p.sineTestDerivativeField L t)
        (p.sineTestDerivativeField L t) -
      inner ℝ (p.sineTestField L t)
        (curvature (cov := cov) (curve (shift G t₀) t)
          (p.sineTestField L t)
          (velocity (shift G t₀) t)
          (velocity (shift G t₀) t))
  obtain ⟨s, hs, hs0, henergy, hfirst, hsecond, hnodesO, hposition⟩ :=
    p.exists_sineBrokenChartData_regular_rectangle hmetric htorsion L hab
      Nleft Nright c basis hOopen hOsub hbase
  obtain ⟨hleftNode0, hrightNode0, hleftVelocity0, hrightVelocity0,
      _hleftAcceleration0, _hrightAcceleration0⟩ :=
    p.sineBrokenChartData_node_initial_data L Nleft Nright c basis
  have hnodes : ∀ e ∈ s,
      HasDerivAt d.leftNode (d.leftVelocity e) e ∧
      HasDerivAt d.rightNode (d.rightVelocity e) e ∧
      HasDerivAt d.leftVelocity (d.leftAcceleration e) e ∧
      HasDerivAt d.rightVelocity (d.rightAcceleration e) e := by
    intro e he
    exact p.sineBrokenChartData_node_derivatives hmetric L Nleft Nright
      c basis hOopen hOsub (hnodesO e he).1 (hnodesO e he).2
  have hframe : ∀ e ∈ s, ∀ t ∈ Icc a b,
      ∀ k : Fin (Module.finrank ℝ E),
        LocalGeodesicData.smoothFrame
          (I := I) (M := M) (E := E) c basis k =ᶠ[
            nhds ((extChartAt I c).symm (d.position e t))]
          (trivializationAt E TM c).localFrame basis k := by
    intro e he t ht k
    filter_upwards [hOopen.mem_nhds (hposition e he t ht).2] with y hy
    exact (hOsub hy).2 k
  have hdiff₁ : ∀ e ∈ s, ∀ t ∈ Icc a b,
      HasDerivAt
        (fun y ↦ d.energyDensity (I := I) (M := M) c basis y t)
        (d.firstVariationDensity cov c basis e t) e := by
    intro e he t ht
    exact d.energyDensity_hasDerivAt cov c basis hmetric
      (hnodes e he).1 (hnodes e he).2.1 (hposition e he t ht).1
      (hframe e he t ht)
  have hdiff₂ : ∀ e ∈ s, ∀ t ∈ Icc a b,
      HasDerivAt
        (fun y ↦ d.firstVariationDensity cov c basis y t)
        (d.secondVariationDensityAt cov c basis e t) e := by
    intro e he t ht
    exact d.firstVariationDensity_hasDerivAt cov c basis hmetric htorsion
      (hnodes e he).1 (hnodes e he).2.1
      (hnodes e he).2.2.1 (hnodes e he).2.2.2
      (hposition e he t ht).1 hOopen (hposition e he t ht).2
      (fun y hy k ↦ (hOsub hy).2 k)
  have hC2 : ContDiffAt ℝ 2
      (fun e ↦ ∫ t in a..b,
        d.energyDensity (I := I) (M := M) c basis e t) 0 :=
    intervalIntegral_contDiffAt_two_of_continuousOn
      (F := fun e t ↦ d.energyDensity (I := I) (M := M) c basis e t)
      (F₁ := fun e t ↦ d.firstVariationDensity cov c basis e t)
      (F₂ := fun e t ↦ d.secondVariationDensityAt cov c basis e t)
      hs hs0 hab.le henergy hfirst hsecond hdiff₁ hdiff₂
  have hbaseData : ∀ t ∈ Icc a b,
      HasDerivAt d.z (d.dz t) t ∧
      HasDerivAt d.dz (d.ddz t) t ∧
      HasDerivAt d.J (d.dJ t) t ∧
      LocalGeodesicData.coordinateCovariantFieldDerivative
        (I := I) (M := M) cov c basis
          (d.z t) (d.dz t) (d.dz t) (d.ddz t) = 0 ∧
      d.z t ∈ (extChartAt I c).target ∧
      ∀ k : Fin (Module.finrank ℝ E),
        LocalGeodesicData.smoothFrame
          (I := I) (M := M) (E := E) c basis k =ᶠ[
            nhds ((extChartAt I c).symm (d.z t))]
          (trivializationAt E TM c).localFrame basis k := by
    intro t ht
    exact p.sineBrokenChartData_base_derivatives hmetric L Nleft Nright
      c basis hOopen hOsub (hbase t ht)
  have hboundary : ∀ t ∈ Icc a b,
      HasDerivAt (d.boundaryPairing cov c basis)
        (d.boundaryDerivative cov c basis t) t := by
    intro t ht
    exact d.boundaryPairing_hasDerivAt cov c basis hmetric
      (hbaseData t ht).1 (hbaseData t ht).2.1
      (hbaseData t ht).2.2.1 (hbaseData t ht).2.2.2.1
      (hbaseData t ht).2.2.2.2.1 (hbaseData t ht).2.2.2.2.2
  have hscalar : IntervalIntegrable
      (fun t ↦ sineTestDeriv L t ^ 2 * inner ℝ w₀ w₀ -
        sineTest L t ^ 2 * p.curvatureCoefficient
          (curvature (I := I) (M := M) cov) t) volume a b := by
    have hkinetic : Continuous
        (fun t ↦ sineTestDeriv L t ^ 2 * inner ℝ w₀ w₀) := by
      unfold sineTestDeriv
      fun_prop
    exact (hkinetic.intervalIntegrable a b).sub
      (p.intervalIntegrable_sineTest_square_mul_curvatureCoefficient_curvature
        L a b)
  have hKintegrable : IntervalIntegrable K volume a b := by
    apply hscalar.congr
    intro t _ht
    dsimp only [K]
    rw [p.inner_sineTestDerivativeField_self hmetric L t,
      p.inner_sineTestField_curvature
        (curvature (I := I) (M := M) cov) L t]
  have hindexIntegrable : IntervalIntegrable
      (d.indexDensity cov c basis) volume a b := by
    apply hKintegrable.congr
    intro t ht
    have ht' : t ∈ Icc a b := by
      have : t ∈ Ioc a b := by simpa [uIoc_of_le hab.le] using ht
      exact ⟨this.1.le, this.2⟩
    exact (p.sineBrokenChartData_indexDensity L Nleft Nright c basis t
      (hOsub (hbase t ht')).1).symm
  have h0s : (0 : ℝ) ∈ s := mem_of_mem_nhds hs0
  have hsecond0Continuous : ContinuousOn
      (fun t ↦ (p.sineBrokenChartData L Nleft Nright c basis).secondVariationDensityAt
        cov c basis 0 t) (Icc a b) := by
    change ContinuousOn
      ((fun q : ℝ × ℝ ↦
        (p.sineBrokenChartData L Nleft Nright c basis).secondVariationDensityAt
          cov c basis q.1 q.2) ∘ fun t : ℝ ↦ ((0 : ℝ), t)) (Icc a b)
    exact hsecond.comp (f := fun t : ℝ ↦ ((0 : ℝ), t))
      (continuousOn_const.prodMk continuousOn_id)
      (fun t ht ↦ ⟨h0s, ht⟩)
  have hsecond0Integrable : IntervalIntegrable
      (fun t ↦ (p.sineBrokenChartData L Nleft Nright c basis).secondVariationDensityAt
        cov c basis 0 t) volume a b := by
    have hsecond0Continuous' : ContinuousOn
        (fun t ↦ (p.sineBrokenChartData L Nleft Nright c basis).secondVariationDensityAt
          cov c basis 0 t) [[a, b]] := by
      simpa [uIcc_of_le hab.le] using hsecond0Continuous
    exact hsecond0Continuous'.intervalIntegrable
  have hsecond0Integrable' : IntervalIntegrable
      (fun t ↦ d.secondVariationDensityAt cov c basis 0 t) volume a b :=
    hsecond0Integrable
  have hboundaryIntegrable : IntervalIntegrable
      (d.boundaryDerivative cov c basis) volume a b := by
    apply (hsecond0Integrable'.sub hindexIntegrable).congr
    intro t _ht
    change d.secondVariationDensityAt cov c basis 0 t -
      d.indexDensity cov c basis t = d.boundaryDerivative cov c basis t
    rw [d.secondVariationDensityAt_zero_eq cov c basis
      hleftNode0 hrightNode0 hleftVelocity0 hrightVelocity0]
    unfold LocalGeodesicData.CoordinateBrokenVariationData.secondVariationDensity
    ring
  have hmain := d.iteratedDeriv_two_integral_energyDensity_eq
    (I := I) (M := M) cov c basis hmetric htorsion hs hs0 hab.le
      henergy hfirst hsecond
      (fun e he ↦ (hnodes e he).1)
      (fun e he ↦ (hnodes e he).2.1)
      (fun e he ↦ (hnodes e he).2.2.1)
      (fun e he ↦ (hnodes e he).2.2.2)
      (fun e he t ht ↦ (hposition e he t ht).1)
      hOopen (fun e he t ht ↦ (hposition e he t ht).2)
      (fun y hy k ↦ (hOsub hy).2 k)
      hleftNode0 hrightNode0 hleftVelocity0 hrightVelocity0
      hboundary hindexIntegrable hboundaryIntegrable
  obtain ⟨hboundaryLeft, hboundaryRight⟩ :=
    p.sineBrokenChartData_boundaryPairing_zero L hab Nleft Nright c basis
  have hboundaryLeft' : d.boundaryPairing cov c basis a = 0 := by
    simpa only [GlobalParallelField.sineBrokenChartData_a] using hboundaryLeft
  have hboundaryRight' : d.boundaryPairing cov c basis b = 0 := by
    simpa only [GlobalParallelField.sineBrokenChartData_b] using hboundaryRight
  refine ⟨hC2, ?_⟩
  calc
    iteratedDeriv 2
        (fun e ↦ ∫ t in a..b,
          d.energyDensity (I := I) (M := M) c basis e t) 0 =
        (∫ t in a..b, d.indexDensity cov c basis t) +
          d.boundaryPairing cov c basis b -
          d.boundaryPairing cov c basis a := hmain
    _ = ∫ t in a..b, d.indexDensity cov c basis t := by
      rw [hboundaryLeft', hboundaryRight']
      ring
    _ = ∫ t in a..b, K t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc a b := by
        simpa [uIcc_of_le hab.le] using ht
      exact p.sineBrokenChartData_indexDensity L Nleft Nright c basis t
        (hOsub (hbase t ht')).1

end IntrinsicGeodesic.GlobalGeodesic
end BonnetMyersEntry
