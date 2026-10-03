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

public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentCorner
public import LeanPool.PoincareGeometry.BonnetMyers.GlobalGeodesic

/-!
# Geodesic-state gluing along exact metric segments

The positive corner-alignment equation is upgraded here to literal equality
of tangent-bundle states after both adjacent normal connectors are reparametrized
by arclength.  This is the chart-independent input for continuing one complete
geodesic through the continuous metric segment.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology RealInnerProductSpace

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace IntrinsicGeodesic.GlobalGeodesic

/-- If a local geodesic's prescribed initial state is the state of a complete
geodesic at time `t`, then the translated complete state and the local state
agree on a neighbourhood of zero.  The explicit cast is hidden only after its
equality in the total tangent bundle has been supplied. -/
theorem agrees_locally_with_local_of_state_eq
    [RiemannianBundle TM]
    {cov : CovariantDerivative I E TM}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {x₀ : M} {v₀ : TM x₀}
    (γ : IntrinsicGeodesic.GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t : ℝ) {y : M} {w : TM y}
    (α : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov y w)
    (hstate : γ.state t = (⟨y, w⟩ : Bundle.TotalSpace E TM)) :
    (fun s ↦ γ.state (t + s)) =ᶠ[𝓝 (0 : ℝ)] IntrinsicGeodesic.localState α := by
  have hstate' :
      (⟨IntrinsicGeodesic.GlobalGeodesic.curve γ t,
          IntrinsicGeodesic.GlobalGeodesic.velocity γ t⟩ :
        Bundle.TotalSpace E TM) = ⟨y, w⟩ := hstate
  let α' := IntrinsicGeodesic.GlobalGeodesic.castInitialState hstate' α
  have hagree := IntrinsicGeodesic.GlobalGeodesic.agrees_locally
    (IntrinsicGeodesic.GlobalGeodesic.shift γ t) α'
  filter_upwards [hagree] with s hs
  change γ.state (t + s) = IntrinsicGeodesic.localState α s
  simpa [α', IntrinsicGeodesic.GlobalGeodesic.localState_castInitialState] using hs

end IntrinsicGeodesic.GlobalGeodesic

/-- Equality of the complete initial tangent states lets the interval-level
ODE uniqueness theorem compare local geodesics whose source points and source
fibres were not definitionally the same before the state equality was known. -/
theorem IntrinsicGeodesic.LocalGeodesic.curve_eqOn_common_interval_of_initial_state_eq
    [RiemannianBundle TM]
    {cov : CovariantDerivative I E TM}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {x₁ x₂ : M} {v₁ : TM x₁} {v₂ : TM x₂}
    (α : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₁ v₁)
    (β : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₂ v₂)
    (hstate : IntrinsicGeodesic.localState α 0 =
      IntrinsicGeodesic.localState β 0) :
    Set.EqOn (IntrinsicGeodesic.LocalGeodesic.curve α)
      (IntrinsicGeodesic.LocalGeodesic.curve β)
      (Ioo (-(min α.solution.radius β.solution.radius))
        (min α.solution.radius β.solution.radius)) := by
  have hinitial : (⟨x₁, v₁⟩ : Bundle.TotalSpace E TM) = ⟨x₂, v₂⟩ := by
    have hα : IntrinsicGeodesic.localState α 0 =
        (⟨x₁, v₁⟩ : Bundle.TotalSpace E TM) := by
      apply Bundle.TotalSpace.ext
        (IntrinsicGeodesic.LocalGeodesic.curve_initial α)
      exact heq_of_eq (IntrinsicGeodesic.LocalGeodesic.velocity_initial α)
    have hβ : IntrinsicGeodesic.localState β 0 =
        (⟨x₂, v₂⟩ : Bundle.TotalSpace E TM) := by
      apply Bundle.TotalSpace.ext
        (IntrinsicGeodesic.LocalGeodesic.curve_initial β)
      exact heq_of_eq (IntrinsicGeodesic.LocalGeodesic.velocity_initial β)
    exact hα.symm.trans (hstate.trans hβ)
  let β' := IntrinsicGeodesic.GlobalGeodesic.castInitialState hinitial β
  have heq := IntrinsicGeodesic.LocalGeodesic.curve_eqOn_common_interval_of_same_initial
    cov _ _ α β'
  have hradius : β'.solution.radius = β.solution.radius := by
    cases hinitial
    rfl
  intro t ht
  have ht' : t ∈ Ioo (-(min α.solution.radius β'.solution.radius))
      (min α.solution.radius β'.solution.radius) := by
    simpa only [hradius] using ht
  calc
    IntrinsicGeodesic.LocalGeodesic.curve α t =
        IntrinsicGeodesic.LocalGeodesic.curve β' t := heq ht'
    _ = IntrinsicGeodesic.LocalGeodesic.curve β t := by
      have hcast := IntrinsicGeodesic.GlobalGeodesic.localState_castInitialState
        hinitial β
      exact congrArg Bundle.TotalSpace.proj (congrFun hcast t)
/-- Positively aligned adjacent normal connectors have exactly the same
tangent-bundle state at their common endpoint after unit-speed rescaling. -/
theorem rescaled_normal_connectors_state_eq
    [RiemannianBundle TM]
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (c₀ c : M) (uIn uOut : E)
    (incoming : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov c₀
        (IntrinsicGeodesic.canonicalBasis (E := E))) c₀ uIn)
    (outgoing : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov c
        (IntrinsicGeodesic.canonicalBasis (E := E))) c uOut)
    (hinRadius : incoming.radius = 2)
    (hinEnd : LocalChartSecondOrderSolution.curve incoming 1 = c)
    {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hnormalized :
      a⁻¹ • LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c₀)
          (IntrinsicGeodesic.canonicalBasis (E := E)) (incoming.velocity 1) c =
      d⁻¹ • LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c)
          (IntrinsicGeodesic.canonicalBasis (E := E)) uOut c) :
    let αIn₀ := IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution
      (I := I) (M := M) incoming
    let αOut₀ := IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution
      (I := I) (M := M) outgoing
    let αIn := IntrinsicGeodesic.LocalGeodesic.rescale αIn₀ a⁻¹ (inv_pos.mpr ha)
    let αOut := IntrinsicGeodesic.LocalGeodesic.rescale αOut₀ d⁻¹ (inv_pos.mpr hd)
    IntrinsicGeodesic.localState αIn a = IntrinsicGeodesic.localState αOut 0 := by
  subst c
  let αIn₀ := IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution
    (I := I) (M := M) incoming
  let αOut₀ := IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution
    (I := I) (M := M) outgoing
  let αIn := IntrinsicGeodesic.LocalGeodesic.rescale αIn₀ a⁻¹ (inv_pos.mpr ha)
  let αOut := IntrinsicGeodesic.LocalGeodesic.rescale αOut₀ d⁻¹ (inv_pos.mpr hd)
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hOne : (1 : ℝ) ∈ Ioo (-incoming.radius) incoming.radius := by
    rw [hinRadius]
    norm_num
  have hZero : (0 : ℝ) ∈ Ioo (-outgoing.radius) outgoing.radius := by
    constructor <;> linarith [outgoing.radius_pos]
  let scaleState (k : ℝ) : Bundle.TotalSpace E TM → Bundle.TotalSpace E TM :=
    fun q ↦ ⟨q.proj, k • q.snd⟩
  let TIn : TM (LocalChartSecondOrderSolution.curve incoming 1) :=
    LocalGeodesicData.coordinateFrameCombination
      (I := I) (M := M) (x₀ := c₀)
        (IntrinsicGeodesic.canonicalBasis (E := E)) (incoming.velocity 1)
          (LocalChartSecondOrderSolution.curve incoming 1)
  let TOut : TM (LocalChartSecondOrderSolution.curve incoming 1) :=
    LocalGeodesicData.coordinateFrameCombination
      (I := I) (M := M) (x₀ := LocalChartSecondOrderSolution.curve incoming 1)
        (IntrinsicGeodesic.canonicalBasis (E := E)) uOut
          (LocalChartSecondOrderSolution.curve incoming 1)
  have hcurveIn : IntrinsicGeodesic.LocalGeodesic.curve αIn₀ 1 =
      LocalChartSecondOrderSolution.curve incoming 1 :=
    congrFun (IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution_curve incoming) 1
  have hstateIn₀ : IntrinsicGeodesic.localState αIn₀ 1 =
      (⟨LocalChartSecondOrderSolution.curve incoming 1, TIn⟩ :
        Bundle.TotalSpace E TM) := by
    have hframe := LocalGeodesicData.tangentField_eq_coordinateFrameCombination
      (I := I) (M := M) (E := E) cov c₀
        (IntrinsicGeodesic.canonicalBasis (E := E)) αIn₀.solution
          αIn₀.solution.velocity (t := 1) (by simpa [αIn₀] using hOne)
    have hstateFrame : IntrinsicGeodesic.localState αIn₀ 1 =
        (⟨IntrinsicGeodesic.LocalGeodesic.curve αIn₀ 1,
          LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := c₀)
              (IntrinsicGeodesic.canonicalBasis (E := E)) (incoming.velocity 1)
                (IntrinsicGeodesic.LocalGeodesic.curve αIn₀ 1)⟩ :
          Bundle.TotalSpace E TM) := by
      refine Bundle.TotalSpace.ext (by rfl) ?_
      change HEq
        (LocalGeodesicData.tangentField cov c₀
          (IntrinsicGeodesic.canonicalBasis (E := E)) αIn₀.solution
            αIn₀.solution.velocity 1)
        (LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := c₀)
            (IntrinsicGeodesic.canonicalBasis (E := E)) (incoming.velocity 1)
              (αIn₀.solution.curve 1))
      simpa [αIn₀] using (heq_of_eq hframe)
    exact hstateFrame.trans (congrArg (fun y : M ↦
      (⟨y, LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c₀)
          (IntrinsicGeodesic.canonicalBasis (E := E)) (incoming.velocity 1) y⟩ :
        Bundle.TotalSpace E TM)) hcurveIn)
  have hcurveOut : IntrinsicGeodesic.LocalGeodesic.curve αOut₀ 0 =
      LocalChartSecondOrderSolution.curve incoming 1 :=
    IntrinsicGeodesic.LocalGeodesic.curve_initial αOut₀
  have hstateOut₀ : IntrinsicGeodesic.localState αOut₀ 0 =
      (⟨LocalChartSecondOrderSolution.curve incoming 1, TOut⟩ :
        Bundle.TotalSpace E TM) := by
    have hframe := LocalGeodesicData.tangentField_eq_coordinateFrameCombination
      (I := I) (M := M) (E := E) cov
        (LocalChartSecondOrderSolution.curve incoming 1)
        (IntrinsicGeodesic.canonicalBasis (E := E)) αOut₀.solution
          αOut₀.solution.velocity (t := 0) (by simpa [αOut₀] using hZero)
    have hstateFrame : IntrinsicGeodesic.localState αOut₀ 0 =
        (⟨IntrinsicGeodesic.LocalGeodesic.curve αOut₀ 0,
          LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M)
              (x₀ := LocalChartSecondOrderSolution.curve incoming 1)
              (IntrinsicGeodesic.canonicalBasis (E := E)) uOut
                (IntrinsicGeodesic.LocalGeodesic.curve αOut₀ 0)⟩ :
          Bundle.TotalSpace E TM) := by
      refine Bundle.TotalSpace.ext (by rfl) ?_
      change HEq
        (LocalGeodesicData.tangentField cov
          (LocalChartSecondOrderSolution.curve incoming 1)
          (IntrinsicGeodesic.canonicalBasis (E := E)) αOut₀.solution
            αOut₀.solution.velocity 0)
        (LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M)
            (x₀ := LocalChartSecondOrderSolution.curve incoming 1)
            (IntrinsicGeodesic.canonicalBasis (E := E)) uOut
              (αOut₀.solution.curve 0))
      simpa [αOut₀, outgoing.velocity_initial] using (heq_of_eq hframe)
    exact hstateFrame.trans (congrArg (fun y : M ↦
      (⟨y, LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := LocalChartSecondOrderSolution.curve incoming 1)
          (IntrinsicGeodesic.canonicalBasis (E := E)) uOut y⟩ :
        Bundle.TotalSpace E TM)) hcurveOut)
  have hInTime : a⁻¹ * a ∈ Ioo (-αIn₀.solution.radius) αIn₀.solution.radius := by
    simpa [αIn₀, inv_mul_cancel₀ ha0] using hOne
  have hOutTime : d⁻¹ * 0 ∈ Ioo (-αOut₀.solution.radius) αOut₀.solution.radius := by
    simpa [αOut₀] using hZero
  have hvIn := IntrinsicGeodesic.LocalGeodesic.rescale_actual_velocity
    αIn₀ a⁻¹ (inv_pos.mpr ha) hInTime
  have hvOut := IntrinsicGeodesic.LocalGeodesic.rescale_actual_velocity
    αOut₀ d⁻¹ (inv_pos.mpr hd) hOutTime
  have hstateResIn : IntrinsicGeodesic.localState αIn a =
      scaleState a⁻¹ (IntrinsicGeodesic.localState αIn₀ 1) := by
    have hbaseRes : IntrinsicGeodesic.LocalGeodesic.curve αIn a =
        IntrinsicGeodesic.LocalGeodesic.curve αIn₀ 1 := by
      simpa [αIn, inv_mul_cancel₀ ha0] using
        IntrinsicGeodesic.LocalGeodesic.rescale_curve αIn₀ a⁻¹ (inv_pos.mpr ha) a
    refine Bundle.TotalSpace.ext hbaseRes ?_
    have hvInOne := hvIn
    rw [inv_mul_cancel₀ ha0] at hvInOne
    exact (heq_of_eq hvInOne).trans (by rfl)
  have hstateResOut : IntrinsicGeodesic.localState αOut 0 =
      scaleState d⁻¹ (IntrinsicGeodesic.localState αOut₀ 0) := by
    have hbaseRes : IntrinsicGeodesic.LocalGeodesic.curve αOut 0 =
        IntrinsicGeodesic.LocalGeodesic.curve αOut₀ 0 := by
      simpa [αOut] using
        IntrinsicGeodesic.LocalGeodesic.rescale_curve αOut₀ d⁻¹ (inv_pos.mpr hd) 0
    refine Bundle.TotalSpace.ext hbaseRes ?_
    have hvOutZero := hvOut
    rw [mul_zero] at hvOutZero
    exact (heq_of_eq hvOutZero).trans (by rfl)
  have hnormalizedState :
      scaleState a⁻¹
          (⟨LocalChartSecondOrderSolution.curve incoming 1, TIn⟩ :
            Bundle.TotalSpace E TM) =
        scaleState d⁻¹
          (⟨LocalChartSecondOrderSolution.curve incoming 1, TOut⟩ :
            Bundle.TotalSpace E TM) := by
    refine Bundle.TotalSpace.ext (by rfl) ?_
    exact heq_of_eq hnormalized
  calc
    IntrinsicGeodesic.localState αIn a =
        scaleState a⁻¹ (IntrinsicGeodesic.localState αIn₀ 1) := hstateResIn
    _ = scaleState a⁻¹
        (⟨LocalChartSecondOrderSolution.curve incoming 1, TIn⟩ :
          Bundle.TotalSpace E TM) := congrArg (scaleState a⁻¹) hstateIn₀
    _ = scaleState d⁻¹
        (⟨LocalChartSecondOrderSolution.curve incoming 1, TOut⟩ :
          Bundle.TotalSpace E TM) := hnormalizedState
    _ = scaleState d⁻¹ (IntrinsicGeodesic.localState αOut₀ 0) :=
      congrArg (scaleState d⁻¹) hstateOut₀.symm
    _ = IntrinsicGeodesic.localState αOut 0 := hstateResOut.symm

/-- A normal connector parametrized on the unit interval becomes unit speed
at its terminal point after division by its positive endpoint distance.  The
statement is phrased through the total tangent state so dependent fibres are
transported only by an equality of their base points. -/
theorem rescaled_normal_connector_terminal_norm_one
    [RiemannianBundle TM]
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (c₀ : M) (uIn : E)
    (incoming : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov c₀
        (IntrinsicGeodesic.canonicalBasis (E := E))) c₀ uIn)
    {a : ℝ} (ha : 0 < a)
    (hnorm :
      ‖LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c₀)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (incoming.velocity 1)
          (LocalChartSecondOrderSolution.curve incoming 1)‖ = a)
    (hRadius : incoming.radius = 2) :
    let α₀ := IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution
      (I := I) (M := M) incoming
    let α := IntrinsicGeodesic.LocalGeodesic.rescale α₀ a⁻¹ (inv_pos.mpr ha)
    let q : Bundle.TotalSpace E TM := IntrinsicGeodesic.localState α a
    ‖q.snd‖ = 1 := by
  let α₀ := IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution
    (I := I) (M := M) incoming
  let α := IntrinsicGeodesic.LocalGeodesic.rescale α₀ a⁻¹ (inv_pos.mpr ha)
  let q : Bundle.TotalSpace E TM := IntrinsicGeodesic.localState α a
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hOne : (1 : ℝ) ∈ Ioo (-incoming.radius) incoming.radius := by
    rw [hRadius]
    norm_num
  have hTime : a⁻¹ * a ∈ Ioo (-α₀.solution.radius) α₀.solution.radius := by
    simpa [α₀, inv_mul_cancel₀ ha0] using hOne
  have hv := IntrinsicGeodesic.LocalGeodesic.rescale_actual_velocity
    α₀ a⁻¹ (inv_pos.mpr ha) hTime
  have hframe := LocalGeodesicData.tangentField_eq_coordinateFrameCombination
    (I := I) (M := M) (E := E) cov c₀
      (IntrinsicGeodesic.canonicalBasis (E := E)) α₀.solution
      α₀.solution.velocity (t := 1) (by simpa [α₀] using hOne)
  have hcurve : α₀.solution.curve 1 = incoming.curve 1 := by
    simpa [IntrinsicGeodesic.LocalGeodesic.curve] using
      congrFun (IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution_curve incoming) 1
  have hvelnorm : ‖IntrinsicGeodesic.LocalGeodesic.velocity α₀ 1‖ =
      ‖LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c₀)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (incoming.velocity 1)
          (LocalChartSecondOrderSolution.curve incoming 1)‖ := by
    rw [IntrinsicGeodesic.LocalGeodesic.velocity]
    rw [hframe]
    rw [IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution_velocity]
    apply congrArg (fun y : M ↦
      ‖LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c₀)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (incoming.velocity 1) y‖) hcurve
  rw [inv_mul_cancel₀ ha0] at hv
  let scaleState (k : ℝ) : Bundle.TotalSpace E TM → Bundle.TotalSpace E TM :=
    fun q ↦ ⟨q.proj, k • q.snd⟩
  have hbaseRes : IntrinsicGeodesic.LocalGeodesic.curve α a =
      IntrinsicGeodesic.LocalGeodesic.curve α₀ 1 := by
    simpa [α, inv_mul_cancel₀ ha0] using
      IntrinsicGeodesic.LocalGeodesic.rescale_curve α₀ a⁻¹ (inv_pos.mpr ha) a
  have hstateRes : IntrinsicGeodesic.localState α a =
      scaleState a⁻¹ (IntrinsicGeodesic.localState α₀ 1) := by
    refine Bundle.TotalSpace.ext hbaseRes ?_
    exact (heq_of_eq hv).trans (by rfl)
  have hnormRes := congrArg
    (fun q : Bundle.TotalSpace E TM ↦ ‖q.snd‖) hstateRes
  calc
    ‖q.snd‖ = ‖(scaleState a⁻¹ (IntrinsicGeodesic.localState α₀ 1)).snd‖ := by
      simpa only [q] using hnormRes
    _ = ‖a⁻¹ • IntrinsicGeodesic.LocalGeodesic.velocity α₀ 1‖ := by rfl
    _ = |a⁻¹| * ‖IntrinsicGeodesic.LocalGeodesic.velocity α₀ 1‖ := norm_smul _ _
    _ = a⁻¹ * ‖LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c₀)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (incoming.velocity 1)
          (LocalChartSecondOrderSolution.curve incoming 1)‖ := by
      rw [abs_of_pos (inv_pos.mpr ha)]
      exact congrArg (fun q : ℝ ↦ a⁻¹ * q) hvelnorm
    _ = a⁻¹ * a := by rw [hnorm]
    _ = 1 := inv_mul_cancel₀ ha0
/-- Once every sufficiently short outgoing normal connector has the same
normalized initial state as one fixed incoming connector, all of their
endpoints lie on one fixed intrinsic local geodesic. -/
theorem exists_local_geodesic_right_of_normal_corner_alignment
    [RiemannianBundle TM]
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {X : Type*} [PseudoMetricSpace X] {x z : X}
    (γ : MetricHopfRinow.SegmentParameter x z → M)
    (r t : MetricHopfRinow.SegmentParameter x z)
    (hrt : (r : ℝ) < (t : ℝ))
    (uIn : E)
    (incoming : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov (γ r)
        (IntrinsicGeodesic.canonicalBasis (E := E))) (γ r) uIn)
    (hinRadius : incoming.radius = 2)
    (hinEnd : LocalChartSecondOrderSolution.curve incoming 1 = γ t)
    (hinNorm :
      ‖LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := γ r)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (incoming.velocity 1)
          (LocalChartSecondOrderSolution.curve incoming 1)‖ =
        (t : ℝ) - (r : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hout : ∀ s : MetricHopfRinow.SegmentParameter x z,
      (t : ℝ) < (s : ℝ) → (s : ℝ) - (t : ℝ) < ε →
      ∃ uOut : E, ∃ outgoing : LocalChartSecondOrderSolution I
        (LocalGeodesicData.coordinateAcceleration cov (γ t)
          (IntrinsicGeodesic.canonicalBasis (E := E))) (γ t) uOut,
        outgoing.radius = 2 ∧
        LocalChartSecondOrderSolution.curve outgoing 0 = γ t ∧
        LocalChartSecondOrderSolution.curve outgoing 1 = γ s ∧
        ((t : ℝ) - (r : ℝ))⁻¹ •
            LocalGeodesicData.coordinateFrameCombination
              (I := I) (M := M) (x₀ := γ r)
                (IntrinsicGeodesic.canonicalBasis (E := E))
                (incoming.velocity 1) (γ t) =
          ((s : ℝ) - (t : ℝ))⁻¹ •
            LocalGeodesicData.coordinateFrameCombination
              (I := I) (M := M) (x₀ := γ t)
                (IntrinsicGeodesic.canonicalBasis (E := E)) uOut (γ t)) :
    ∃ c : M, ∃ v : TM c,
      ∃ β : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov c v,
        ‖v‖ = 1 ∧
        IntrinsicGeodesic.LocalGeodesic.curve β 0 = γ t ∧
        ∃ ρ > (0 : ℝ),
          ∀ s : MetricHopfRinow.SegmentParameter x z,
            (t : ℝ) < (s : ℝ) → (s : ℝ) - (t : ℝ) < ρ →
            IntrinsicGeodesic.LocalGeodesic.curve β
              ((s : ℝ) - (t : ℝ)) = γ s := by
  let a : ℝ := (t : ℝ) - (r : ℝ)
  have ha : 0 < a := sub_pos.mpr hrt
  let αIn₀ := IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution
    (I := I) (M := M) incoming
  let αIn := IntrinsicGeodesic.LocalGeodesic.rescale αIn₀ a⁻¹ (inv_pos.mpr ha)
  let q : Bundle.TotalSpace E TM := IntrinsicGeodesic.localState αIn a
  obtain ⟨β⟩ := IntrinsicGeodesic.exists_localGeodesic
    (I := I) (M := M) cov q.proj q.snd
  let ρ : ℝ := min ε β.solution.radius
  have hρ : 0 < ρ := lt_min hε β.solution.radius_pos
  have hβinitial : IntrinsicGeodesic.localState β 0 = q := by
    apply Bundle.TotalSpace.ext
      (IntrinsicGeodesic.LocalGeodesic.curve_initial β)
    exact heq_of_eq (IntrinsicGeodesic.LocalGeodesic.velocity_initial β)
  have hαInCurve : IntrinsicGeodesic.LocalGeodesic.curve αIn a = γ t := by
    calc
      IntrinsicGeodesic.LocalGeodesic.curve αIn a =
          IntrinsicGeodesic.LocalGeodesic.curve αIn₀ (a⁻¹ * a) :=
        IntrinsicGeodesic.LocalGeodesic.rescale_curve αIn₀ a⁻¹
          (inv_pos.mpr ha) a
      _ = IntrinsicGeodesic.LocalGeodesic.curve αIn₀ 1 := by
        rw [inv_mul_cancel₀ (ne_of_gt ha)]
      _ = LocalChartSecondOrderSolution.curve incoming 1 := by
        rw [IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution_curve]
      _ = γ t := hinEnd
  have hβzero : IntrinsicGeodesic.LocalGeodesic.curve β 0 = γ t := by
    calc
      IntrinsicGeodesic.LocalGeodesic.curve β 0 = q.proj :=
        IntrinsicGeodesic.LocalGeodesic.curve_initial β
      _ = IntrinsicGeodesic.LocalGeodesic.curve αIn a := rfl
      _ = γ t := hαInCurve
  have hqUnit : ‖q.snd‖ = 1 := by
    simpa only [a, αIn₀, αIn, q] using
      rescaled_normal_connector_terminal_norm_one
        (I := I) (M := M) cov (γ r) uIn incoming ha hinNorm hinRadius
  refine ⟨q.proj, q.snd, β, hqUnit, hβzero, ρ, hρ, ?_⟩
  intro s hts hst
  have hd : 0 < (s : ℝ) - (t : ℝ) := sub_pos.mpr hts
  have hstε : (s : ℝ) - (t : ℝ) < ε :=
    lt_of_lt_of_le hst (min_le_left _ _)
  have hstβ : (s : ℝ) - (t : ℝ) < β.solution.radius :=
    lt_of_lt_of_le hst (min_le_right _ _)
  obtain ⟨uOut, outgoing, houtRadius, _houtZero, houtEnd, hnormalized⟩ :=
    hout s hts hstε
  let d : ℝ := (s : ℝ) - (t : ℝ)
  let αOut₀ := IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution
    (I := I) (M := M) outgoing
  let αOut := IntrinsicGeodesic.LocalGeodesic.rescale αOut₀ d⁻¹
    (inv_pos.mpr hd)
  have hstateInOut : IntrinsicGeodesic.localState αIn a =
      IntrinsicGeodesic.localState αOut 0 := by
    simpa only [a, d, αIn₀, αIn, αOut₀, αOut] using
      (rescaled_normal_connectors_state_eq
        (I := I) (M := M) cov (γ r) (γ t) uIn uOut incoming outgoing
          hinRadius hinEnd (sub_pos.mpr hrt) hd hnormalized)
  have hstateβOut : IntrinsicGeodesic.localState β 0 =
      IntrinsicGeodesic.localState αOut 0 := by
    exact hβinitial.trans hstateInOut
  have heq :=
    IntrinsicGeodesic.LocalGeodesic.curve_eqOn_common_interval_of_initial_state_eq
      β αOut hstateβOut
  have hαOutRadius : αOut.solution.radius = 2 * d := by
    simp only [αOut, IntrinsicGeodesic.LocalGeodesic.rescale_radius,
      αOut₀, IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution_radius,
      houtRadius]
    field_simp
  have hdInterval : d ∈ Ioo
      (-(min β.solution.radius αOut.solution.radius))
      (min β.solution.radius αOut.solution.radius) := by
    rw [hαOutRadius]
    constructor
    · have hminPos : 0 < min β.solution.radius (2 * d) :=
        lt_min β.solution.radius_pos (by positivity)
      linarith
    · apply lt_min
      · simpa only [d] using hstβ
      · linarith
  calc
    IntrinsicGeodesic.LocalGeodesic.curve β d =
        IntrinsicGeodesic.LocalGeodesic.curve αOut d := heq hdInterval
    _ = IntrinsicGeodesic.LocalGeodesic.curve αOut₀ (d⁻¹ * d) :=
      IntrinsicGeodesic.LocalGeodesic.rescale_curve αOut₀ d⁻¹
        (inv_pos.mpr hd) d
    _ = IntrinsicGeodesic.LocalGeodesic.curve αOut₀ 1 := by
      rw [inv_mul_cancel₀ (ne_of_gt hd)]
    _ = LocalChartSecondOrderSolution.curve outgoing 1 := by
      rw [IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution_curve]
    _ = γ s := houtEnd
/-- Every point sufficiently shortly after a fixed segment parameter is the
centre of one local geodesic which contains all still-closer segment points
to its right.  The curve is fixed before the later endpoint is chosen. -/
theorem riemannian_metric_segment_exists_local_geodesic_right
    [T3Space M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    let cov := leviCivita (I := I) (M := M) g
    ∀ {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M),
      Continuous γ →
      (∀ p q, riemannianEDist I (γ p) (γ q) =
        ENNReal.ofReal |(q : ℝ) - (p : ℝ)|) →
      ∀ r : MetricHopfRinow.SegmentParameter x z,
        ∃ N : Set M, IsOpen N ∧ γ r ∈ N ∧
          ∀ t : MetricHopfRinow.SegmentParameter x z, γ t ∈ N →
            (r : ℝ) < (t : ℝ) →
            ∃ c : M, ∃ v : TM c,
            ∃ β : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M)
                cov c v,
                ‖v‖ = 1 ∧
                IntrinsicGeodesic.LocalGeodesic.curve β 0 = γ t ∧
                ∃ ρ > (0 : ℝ),
                  ∀ s : MetricHopfRinow.SegmentParameter x z,
                    (t : ℝ) < (s : ℝ) →
                    (s : ℝ) - (t : ℝ) < ρ →
                    IntrinsicGeodesic.LocalGeodesic.curve β
                      ((s : ℝ) - (t : ℝ)) = γ s := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := by infer_instance
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  let cov := leviCivita (I := I) (M := M) g
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov 1 := by
    simpa [cov] using (leviCivitaSmooth (I := I) (M := M) g)
  dsimp only
  intro x z γ hγ hsegment r
  obtain ⟨N, hNopen, hrN, hcorner⟩ :=
    riemannian_metric_segment_exists_normal_corner_alignment
      (I := I) (M := M) g γ hγ hsegment r
  refine ⟨N, hNopen, hrN, ?_⟩
  intro t htN hrt
  obtain ⟨uIn, incoming, hinRadius, _hinZero, hinEnd, hinNorm,
    _hinOpposite, ε, hε, hout⟩ :=
    hcorner t htN hrt
  have hinNorm' :
      ‖LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := γ r)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (incoming.velocity 1)
          (LocalChartSecondOrderSolution.curve incoming 1)‖ =
        (t : ℝ) - (r : ℝ) := by
    exact (congrArg (fun y : M ↦
      ‖LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := γ r)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (incoming.velocity 1) y‖) hinEnd).trans hinNorm
  apply exists_local_geodesic_right_of_normal_corner_alignment
    (I := I) (M := M) cov γ r t hrt uIn incoming hinRadius hinEnd hinNorm' ε hε
  intro s hts hst
  obtain ⟨uOut, outgoing, houtRadius, houtZero, houtEnd,
    _hInNorm, _hOutNorm, _halign, hnormalized⟩ := hout s hts hst
  exact ⟨uOut, outgoing, houtRadius, houtZero, houtEnd, hnormalized⟩

end BonnetMyersEntry
