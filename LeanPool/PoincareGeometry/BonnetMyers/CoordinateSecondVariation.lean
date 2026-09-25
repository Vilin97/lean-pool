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

public import LeanPool.PoincareGeometry.BonnetMyers.CoordinateCurvature
public import LeanPool.PoincareGeometry.BonnetMyers.MetricVariable

/-!
# Coordinate second variation

This module proves the pointwise, sign-sensitive differential identity behind
the second variation of energy.  It works in one manifold chart, differentiates
the metric pairing for independently varying coordinate vectors, identifies
the Christoffel commutator with the actual curvature tensor, and isolates the
endpoint derivative that cancels across a broken variation.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry.LocalGeodesicData

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

variable [RiemannianBundle (TangentSpace I : M → Type u)]

/-- Coordinate expression for the covariant derivative of a field with
coordinate value `w` and ordinary derivative `dw` along velocity `u`. -/
def coordinateCovariantFieldDerivative
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (z u w dw : E) : E :=
  dw + coordinateParallelOperator (I := I) (M := M) (E := E)
    cov x₀ b z u w
/-- The coordinate second-variation commutator.  This is the algebraic core
of `D_e D_t W = D_t D_e W - R(T,W)W` in the sign convention used here. -/
theorem coordinate_secondVariation_commutator
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (z u j dj c dc : E)
    (hsymm : ∀ a d : E,
      coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b z a d =
        coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b z d a)
    (hderivSymm :
      fderiv ℝ (fun q ↦ coordinateParallelOperator
          (I := I) (M := M) (E := E) cov x₀ b q j u) z j =
        fderiv ℝ (fun q ↦ coordinateParallelOperator
          (I := I) (M := M) (E := E) cov x₀ b q u j) z j) :
    let B := coordinateCovariantFieldDerivative
      (I := I) (M := M) cov x₀ b z u j dj
    let C := c + coordinateParallelOperator
      (I := I) (M := M) (E := E) cov x₀ b z j j
    let dB := dc +
      fderiv ℝ (fun q ↦ coordinateParallelOperator
        (I := I) (M := M) (E := E) cov x₀ b q j u) z j +
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b z c u +
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b z j dj
    let dC := dc +
      fderiv ℝ (fun q ↦ coordinateParallelOperator
        (I := I) (M := M) (E := E) cov x₀ b q j j) z u +
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b z dj j +
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b z j dj
    coordinateCovariantFieldDerivative
        (I := I) (M := M) cov x₀ b z j B dB =
      coordinateCovariantFieldDerivative
          (I := I) (M := M) cov x₀ b z u C dC -
        coordinateCurvatureOperator (I := I) (M := M)
          cov x₀ b z u j j := by
  dsimp only [coordinateCovariantFieldDerivative]
  rw [hderivSymm, hsymm c u, hsymm dj j]
  simp only [coordinateCurvatureOperator, map_add]
  abel

/-- Torsion-freeness makes the coordinate Christoffel operator symmetric as
a germ in every chart region where the chosen smooth frame is the coordinate
frame.  Consequently its base-point derivative is symmetric as well. -/
theorem coordinateParallelOperator_fderiv_comm_of_open_frameAgreement
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (htorsion : cov.torsion = 0)
    {z : E} (hz : z ∈ (extChartAt I x₀).target)
    {O : Set M} (hOopen : IsOpen O)
    (hzO : (extChartAt I x₀).symm z ∈ O)
    (hOframe : ∀ y ∈ O, ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b k y =
        (trivializationAt E TM x₀).localFrame b k y)
    (u j : E) :
    fderiv ℝ (fun q ↦ coordinateParallelOperator
        (I := I) (M := M) (E := E) cov x₀ b q j u) z =
      fderiv ℝ (fun q ↦ coordinateParallelOperator
        (I := I) (M := M) (E := E) cov x₀ b q u j) z := by
  have htarget : (extChartAt I x₀).target ∈ nhds z :=
    (isOpen_extChartAt_target (I := I) x₀).mem_nhds hz
  have hpre : {q : E | (extChartAt I x₀).symm q ∈ O} ∈ nhds z :=
    (continuousAt_extChartAt_symm'' hz).preimage_mem_nhds
      (hOopen.mem_nhds hzO)
  have heq :
      (fun q ↦ coordinateParallelOperator
          (I := I) (M := M) (E := E) cov x₀ b q j u) =ᶠ[nhds z]
        (fun q ↦ coordinateParallelOperator
          (I := I) (M := M) (E := E) cov x₀ b q u j) := by
    filter_upwards [htarget, hpre] with q hqtarget hqO
    have hframeq : ∀ k : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b k =ᶠ[
          nhds ((extChartAt I x₀).symm q)]
          (trivializationAt E TM x₀).localFrame b k := by
      intro k
      filter_upwards [hOopen.mem_nhds hqO] with y hy
      exact hOframe y hy k
    exact coordinateParallelOperator_apply_comm_of_torsion_eq_zero
      (I := I) (M := M) (E := E) cov x₀ b hqtarget htorsion hframeq
  exact heq.fderiv_eq

/-- The coordinate curvature term has exactly the scalar sign and slot order
used by the geometric index form. -/
theorem inner_coordinateCurvatureOperator_eq_indexForm_curvature
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [IsContMDiffRiemannianBundle I 2 E TM]
    (hmetric : cov.IsMetricCompatibleTangent)
    (htorsion : cov.torsion = 0)
    {y : M} (hy : y ∈ (extChartAt I x₀).source)
    (hframe : ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b k =ᶠ[nhds y]
        (trivializationAt E TM x₀).localFrame b k)
    (u j : E) :
    inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (coordinateCurvatureOperator (I := I) (M := M)
            cov x₀ b (extChartAt I x₀ y) u j j) y)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y) =
      inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b j y)
        (curvature (cov := cov) y
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b j y)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y)) := by
  let U := coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y
  let J := coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b j y
  rw [coordinateFrameCombination_coordinateCurvatureOperator
    (I := I) (M := M) (E := E) cov x₀ b hy htorsion hframe]
  change inner ℝ (curvature (cov := cov) y U J J) U =
    inner ℝ J (curvature (cov := cov) y J U U)
  rw [curvature_apply, curvature_apply]
  have hskew :=
    CovariantDerivative.curvatureTensor_inner_skew_adjoint_of_isMetricCompatibleTangent
      (I := I) (M := M) (E := E) cov hmetric y U J J U
  have hswap : CovariantDerivative.curvatureTensor (cov := cov) y J U U =
      -CovariantDerivative.curvatureTensor (cov := cov) y U J U :=
    CovariantDerivative.curvatureTensor_swap (cov := cov) y J U U
  rw [hswap, inner_neg_right]
  linarith

/-- Pointwise coordinate second-variation identity.  The final term is the
covariant time derivative of the endpoint-acceleration field; its metric
pairing with the geodesic velocity becomes a boundary derivative. -/
theorem coordinate_secondVariation_inner_identity
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [IsContMDiffRiemannianBundle I 2 E TM]
    (hmetric : cov.IsMetricCompatibleTangent)
    (htorsion : cov.torsion = 0)
    {z : E} (hz : z ∈ (extChartAt I x₀).target)
    {O : Set M} (hOopen : IsOpen O)
    (hzO : (extChartAt I x₀).symm z ∈ O)
    (hOframe : ∀ y ∈ O, ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b k y =
        (trivializationAt E TM x₀).localFrame b k y)
    (u j dj c dc : E) :
    let y := (extChartAt I x₀).symm z
    let B := coordinateCovariantFieldDerivative
      (I := I) (M := M) cov x₀ b z u j dj
    let C := c + coordinateParallelOperator
      (I := I) (M := M) (E := E) cov x₀ b z j j
    let dB := dc +
      fderiv ℝ (fun q ↦ coordinateParallelOperator
        (I := I) (M := M) (E := E) cov x₀ b q j u) z j +
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b z c u +
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b z j dj
    let dC := dc +
      fderiv ℝ (fun q ↦ coordinateParallelOperator
        (I := I) (M := M) (E := E) cov x₀ b q j j) z u +
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b z dj j +
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b z j dj
    let DeB := coordinateCovariantFieldDerivative
      (I := I) (M := M) cov x₀ b z j B dB
    let DtC := coordinateCovariantFieldDerivative
      (I := I) (M := M) cov x₀ b z u C dC
    inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b DeB y)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y) +
      inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b B y)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b B y) =
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b B y)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b B y) -
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b j y)
          (curvature (cov := cov) y
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b j y)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y)) +
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b DtC y)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y) := by
  have hsource : (extChartAt I x₀).symm z ∈
      (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hz
  have hframe : ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b k =ᶠ[
        nhds ((extChartAt I x₀).symm z)]
        (trivializationAt E TM x₀).localFrame b k := by
    intro k
    filter_upwards [hOopen.mem_nhds hzO] with y hy
    exact hOframe y hy k
  have hsymm : ∀ a d : E,
      coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b z a d =
        coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b z d a := by
    intro a d
    exact coordinateParallelOperator_apply_comm_of_torsion_eq_zero
      (I := I) (M := M) (E := E) cov x₀ b hz htorsion hframe
  have hderivSymm :=
    coordinateParallelOperator_fderiv_comm_of_open_frameAgreement
      (I := I) (M := M) (E := E) cov x₀ b htorsion hz
      hOopen hzO hOframe u j
  have hcomm := coordinate_secondVariation_commutator
    (I := I) (M := M) (E := E) cov x₀ b z u j dj c dc
      hsymm (congrArg (fun L : E →L[ℝ] E ↦ L j) hderivSymm)
  dsimp only at hcomm ⊢
  rw [hcomm]
  have hsub : ∀ a d : E,
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (a - d) ((extChartAt I x₀).symm z) =
        coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            a ((extChartAt I x₀).symm z) -
          coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            d ((extChartAt I x₀).symm z) := by
    intro a d
    unfold coordinateFrameCombination
    simp only [map_sub, Finsupp.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [hsub, inner_sub_left]
  have hcurv := inner_coordinateCurvatureOperator_eq_indexForm_curvature
    (I := I) (M := M) (E := E) cov x₀ b hmetric htorsion
      hsource hframe u j
  have hright : extChartAt I x₀ ((extChartAt I x₀).symm z) = z :=
    (extChartAt I x₀).right_inv hz
  rw [hright] at hcurv
  rw [hcurv]
  ring

/-- Metric differentiation for two independently varying coordinate vectors
over a varying coordinate base point. -/
theorem coordinate_metricPairing_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {Q A B : ℝ → E} {e : ℝ} {j da db : E}
    (hQ : HasDerivAt Q j e) (hA : HasDerivAt A da e)
    (hB : HasDerivAt B db e)
    (htarget : Q e ∈ (extChartAt I x₀).target)
    (hframe : ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b k =ᶠ[
        nhds ((extChartAt I x₀).symm (Q e))]
        (trivializationAt E TM x₀).localFrame b k) :
    HasDerivAt
      (fun s ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (A s) ((extChartAt I x₀).symm (Q s)))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (B s) ((extChartAt I x₀).symm (Q s))))
      (inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (da + coordinateParallelOperator (I := I) (M := M) (E := E)
              cov x₀ b (Q e) j (A e))
            ((extChartAt I x₀).symm (Q e)))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (B e) ((extChartAt I x₀).symm (Q e))) +
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (A e) ((extChartAt I x₀).symm (Q e)))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (db + coordinateParallelOperator (I := I) (M := M) (E := E)
              cov x₀ b (Q e) j (B e))
            ((extChartAt I x₀).symm (Q e)))) e := by
  have hγ := CurveConnection.hasMFDerivAt_inverseChartCurve_of_hasDerivAt
    (I := I) (M := M) (E := E) x₀ b Q htarget hQ
  have hγ' : CurveConnection.timeTangentMap (I := I) e
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b j
        ((extChartAt I x₀).symm (Q e))) 1 =
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b j
        ((extChartAt I x₀).symm (Q e)) := by
    rw [CurveConnection.timeTangentMap_eq_toSpanSingleton]
    change (1 : ℝ) • coordinateFrameCombination (I := I) (M := M)
      (x₀ := x₀) b j ((extChartAt I x₀).symm (Q e)) = _
    exact one_smul ℝ _
  have hy : (extChartAt I x₀).symm (Q e) ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact (extChartAt I x₀).map_target htarget
  have hright : extChartAt I x₀ ((extChartAt I x₀).symm (Q e)) = Q e :=
    (extChartAt I x₀).right_inv htarget
  convert coordinateFrameCombination_inner_hasDerivAt_variable
    (I := I) (M := M) (E := E) (H := H) cov x₀ b
    (u := j) (w := A) (v := B) (dw := da) (dv := db)
    (γ := fun s ↦ (extChartAt I x₀).symm (Q s)) (t := e)
    hγ hγ' hy hmetric hframe hA hB using 1
  all_goals rw [hright]

/-- Differentiating the first-variation density once more gives the squared
covariant first variation plus the covariant derivative, in the variation
direction, of that first variation. -/
theorem coordinate_firstVariationDensity_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {Q V B : ℝ → E} {e : ℝ} {j dj dB : E}
    (hQ : HasDerivAt Q j e) (hV : HasDerivAt V dj e)
    (hB : HasDerivAt B dB e)
    (hBvalue : B e = coordinateCovariantFieldDerivative
      (I := I) (M := M) cov x₀ b (Q e) j (V e) dj)
    (htarget : Q e ∈ (extChartAt I x₀).target)
    (hframe : ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b k =ᶠ[
        nhds ((extChartAt I x₀).symm (Q e))]
        (trivializationAt E TM x₀).localFrame b k) :
    HasDerivAt
      (fun s ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (B s) ((extChartAt I x₀).symm (Q s)))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (V s) ((extChartAt I x₀).symm (Q s))))
      (inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (coordinateCovariantFieldDerivative
              (I := I) (M := M) cov x₀ b (Q e) j (B e) dB)
            ((extChartAt I x₀).symm (Q e)))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (V e) ((extChartAt I x₀).symm (Q e))) +
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (B e) ((extChartAt I x₀).symm (Q e)))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (B e) ((extChartAt I x₀).symm (Q e)))) e := by
  have h := coordinate_metricPairing_hasDerivAt
    (I := I) (M := M) (E := E) cov x₀ b hmetric
    (Q := Q) (A := B) (B := V) hQ hB hV htarget hframe
  simpa only [coordinateCovariantFieldDerivative, hBvalue] using h

/-- Along a coordinate geodesic, the derivative of the endpoint term
`<C,T>` is `<D_t C,T>`. -/
theorem coordinate_boundaryPairing_hasDerivAt_of_geodesic
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {Q U C : ℝ → E} {t : ℝ} {u du dc : E}
    (hQ : HasDerivAt Q u t) (hU : HasDerivAt U du t)
    (hC : HasDerivAt C dc t)
    (hgeodesic : coordinateCovariantFieldDerivative
      (I := I) (M := M) cov x₀ b (Q t) u (U t) du = 0)
    (htarget : Q t ∈ (extChartAt I x₀).target)
    (hframe : ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b k =ᶠ[
        nhds ((extChartAt I x₀).symm (Q t))]
        (trivializationAt E TM x₀).localFrame b k) :
    HasDerivAt
      (fun s ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (C s) ((extChartAt I x₀).symm (Q s)))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (U s) ((extChartAt I x₀).symm (Q s))))
      (inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (coordinateCovariantFieldDerivative
            (I := I) (M := M) cov x₀ b (Q t) u (C t) dc)
          ((extChartAt I x₀).symm (Q t)))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (U t) ((extChartAt I x₀).symm (Q t)))) t := by
  have h := coordinate_metricPairing_hasDerivAt
    (I := I) (M := M) (E := E) cov x₀ b hmetric
    (Q := Q) (A := C) (B := U) hQ hC hU htarget hframe
  have hzero : du + coordinateParallelOperator
      (I := I) (M := M) (E := E) cov x₀ b (Q t) u (U t) = 0 := by
    simpa only [coordinateCovariantFieldDerivative] using hgeodesic
  rw [hzero] at h
  have hframezero : coordinateFrameCombination (I := I) (M := M)
      (x₀ := x₀) b 0 ((extChartAt I x₀).symm (Q t)) = 0 := by
    unfold coordinateFrameCombination
    simp only [map_zero, Finsupp.zero_apply, zero_smul, Finset.sum_const_zero]
  rw [hframezero, inner_zero_right, add_zero] at h
  simpa only [coordinateCovariantFieldDerivative] using h

/-! ### Ordinary differentiation of the coordinate Christoffel operator -/

/-- The coordinate Christoffel operator is linear in its velocity slot. -/
theorem coordinateParallelOperator_add_left_apply
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (z u v w : E) :
    coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b z (u + v) w =
      coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b z u w +
        coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b z v w := by
  simp only [coordinateParallelOperator_apply, map_add, Finsupp.add_apply,
    mul_add, add_mul, Finset.sum_add_distrib, add_smul]

/-- If the varying velocity slot vanishes at the differentiation point, only
its first derivative contributes to the Christoffel derivative. -/
theorem coordinateParallelOperator_hasDerivAt_of_left_eq_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {Q U : ℝ → E} {e : ℝ} {q' du : E}
    (hQ : HasDerivAt Q q' e) (hU : HasDerivAt U du e)
    (hU0 : U e = 0) (htarget : Q e ∈ (extChartAt I x₀).target)
    (w : E) :
    HasDerivAt
      (fun s ↦ coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b (Q s) (U s) w)
      (coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b (Q e) du w) e := by
  rw [show (fun s ↦ coordinateParallelOperator (I := I) (M := M) (E := E)
      cov x₀ b (Q s) (U s) w) =
      fun s ↦ ∑ i, ∑ j, ∑ k,
        ((b.repr w j) * (b.repr (U s) k) *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b i j k ((extChartAt I x₀).symm (Q s))) • b i by
    funext s
    exact coordinateParallelOperator_apply cov x₀ b (Q s) (U s) w]
  rw [coordinateParallelOperator_apply]
  convert HasDerivAt.sum (u := Finset.univ) (x := e) (A := fun i s ↦
      ∑ j, ∑ k,
        ((b.repr w j) * (b.repr (U s) k) *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b i j k ((extChartAt I x₀).symm (Q s))) • b i)
      (A' := fun i ↦ ∑ j, ∑ k,
        ((b.repr w j) * (b.repr du k) *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b i j k ((extChartAt I x₀).symm (Q e))) • b i) ?_ using 1
  · ext s
    simp
  · intro i hi
    convert HasDerivAt.sum (u := Finset.univ) (x := e) (A := fun j s ↦
        ∑ k,
          ((b.repr w j) * (b.repr (U s) k) *
            connectionCoefficient (I := I) (M := M) (E := E)
              cov x₀ b i j k ((extChartAt I x₀).symm (Q s))) • b i)
        (A' := fun j ↦ ∑ k,
          ((b.repr w j) * (b.repr du k) *
            connectionCoefficient (I := I) (M := M) (E := E)
              cov x₀ b i j k ((extChartAt I x₀).symm (Q e))) • b i) ?_ using 1
    · ext s
      simp
    · intro j hj
      convert HasDerivAt.sum (u := Finset.univ) (x := e) (A := fun k s ↦
          ((b.repr w j) * (b.repr (U s) k) *
            connectionCoefficient (I := I) (M := M) (E := E)
              cov x₀ b i j k ((extChartAt I x₀).symm (Q s))) • b i)
          (A' := fun k ↦
          ((b.repr w j) * (b.repr du k) *
            connectionCoefficient (I := I) (M := M) (E := E)
              cov x₀ b i j k ((extChartAt I x₀).symm (Q e))) • b i) ?_ using 1
      · ext s
        simp
      · intro k hk
        have hcoord : HasDerivAt (fun s ↦ b.repr (U s) k)
            (b.repr du k) e := by
          simpa using
            (hasDerivAt_const e (b.coord k).toContinuousLinearMap).clm_apply hU
        let g : E → ℝ := fun q ↦ connectionCoefficient
          (I := I) (M := M) (E := E) cov x₀ b i j k
            ((extChartAt I x₀).symm q)
        have hgdiff : DifferentiableAt ℝ g (Q e) :=
          (connectionCoefficient_comp_extChartAt_symm_contDiffAt_of_mem_target
            (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
            i j k htarget).differentiableAt (by norm_num)
        have hg : HasDerivAt (fun s ↦ g (Q s))
            (fderiv ℝ g (Q e) q') e := by
          simpa [Function.comp_def] using
            (hgdiff.hasFDerivAt.comp e hQ.hasFDerivAt).hasDerivAt
        have hterm := ((hasDerivAt_const e (b.repr w j)).mul hcoord |>.mul hg)
          |>.smul_const (b i)
        convert hterm using 1
        · funext s
          rfl
        · have hcoord0 : b.repr (U e) k = 0 := by
            simp [hU0]
          simp only [Pi.mul_apply, hcoord0, mul_zero, zero_mul, add_zero,
            zero_add, g]

/-- If the varying field slot vanishes at the differentiation point, only
its first derivative contributes to the Christoffel derivative. -/
theorem coordinateParallelOperator_hasDerivAt_of_right_eq_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {Q A W : ℝ → E} {e : ℝ} {q' da dw : E}
    (hQ : HasDerivAt Q q' e) (hA : HasDerivAt A da e)
    (hW : HasDerivAt W dw e) (hW0 : W e = 0)
    (htarget : Q e ∈ (extChartAt I x₀).target) :
    HasDerivAt
      (fun s ↦ coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b (Q s) (A s) (W s))
      (coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b (Q e) (A e) dw) e := by
  rw [show (fun s ↦ coordinateParallelOperator (I := I) (M := M) (E := E)
      cov x₀ b (Q s) (A s) (W s)) =
      fun s ↦ ∑ i, ∑ j, ∑ k,
        ((b.repr (W s) j) * (b.repr (A s) k) *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b i j k ((extChartAt I x₀).symm (Q s))) • b i by
    funext s
    exact coordinateParallelOperator_apply cov x₀ b (Q s) (A s) (W s)]
  rw [coordinateParallelOperator_apply]
  convert HasDerivAt.sum (u := Finset.univ) (x := e) (A := fun i s ↦
      ∑ j, ∑ k,
        ((b.repr (W s) j) * (b.repr (A s) k) *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b i j k ((extChartAt I x₀).symm (Q s))) • b i)
      (A' := fun i ↦ ∑ j, ∑ k,
        ((b.repr dw j) * (b.repr (A e) k) *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b i j k ((extChartAt I x₀).symm (Q e))) • b i) ?_ using 1
  · ext s
    simp
  · intro i hi
    convert HasDerivAt.sum (u := Finset.univ) (x := e) (A := fun j s ↦
        ∑ k,
          ((b.repr (W s) j) * (b.repr (A s) k) *
            connectionCoefficient (I := I) (M := M) (E := E)
              cov x₀ b i j k ((extChartAt I x₀).symm (Q s))) • b i)
        (A' := fun j ↦ ∑ k,
          ((b.repr dw j) * (b.repr (A e) k) *
            connectionCoefficient (I := I) (M := M) (E := E)
              cov x₀ b i j k ((extChartAt I x₀).symm (Q e))) • b i) ?_ using 1
    · ext s
      simp
    · intro j hj
      convert HasDerivAt.sum (u := Finset.univ) (x := e) (A := fun k s ↦
          ((b.repr (W s) j) * (b.repr (A s) k) *
            connectionCoefficient (I := I) (M := M) (E := E)
              cov x₀ b i j k ((extChartAt I x₀).symm (Q s))) • b i)
          (A' := fun k ↦
          ((b.repr dw j) * (b.repr (A e) k) *
            connectionCoefficient (I := I) (M := M) (E := E)
              cov x₀ b i j k ((extChartAt I x₀).symm (Q e))) • b i) ?_ using 1
      · ext s
        simp
      · intro k hk
        have hWcoord : HasDerivAt (fun s ↦ b.repr (W s) j)
            (b.repr dw j) e := by
          simpa using
            (hasDerivAt_const e (b.coord j).toContinuousLinearMap).clm_apply hW
        have hAcoord : HasDerivAt (fun s ↦ b.repr (A s) k)
            (b.repr da k) e := by
          simpa using
            (hasDerivAt_const e (b.coord k).toContinuousLinearMap).clm_apply hA
        let g : E → ℝ := fun q ↦ connectionCoefficient
          (I := I) (M := M) (E := E) cov x₀ b i j k
            ((extChartAt I x₀).symm q)
        have hgdiff : DifferentiableAt ℝ g (Q e) :=
          (connectionCoefficient_comp_extChartAt_symm_contDiffAt_of_mem_target
            (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
            i j k htarget).differentiableAt (by norm_num)
        have hg : HasDerivAt (fun s ↦ g (Q s))
            (fderiv ℝ g (Q e) q') e := by
          simpa [Function.comp_def] using
            (hgdiff.hasFDerivAt.comp e hQ.hasFDerivAt).hasDerivAt
        have hterm := (hWcoord.mul hAcoord |>.mul hg).smul_const (b i)
        convert hterm using 1
        · funext s
          rfl
        · have hcoord0 : b.repr (W e) j = 0 := by
            simp [hW0]
          simp only [Pi.mul_apply, hcoord0, zero_mul, add_zero, g]

/-- Product rule for the Christoffel operator when the coordinate base and
both vector slots vary simultaneously. -/
theorem coordinateParallelOperator_apply_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {Q A B : ℝ → E} {e : ℝ} {q' da db : E}
    (hQ : HasDerivAt Q q' e) (hA : HasDerivAt A da e)
    (hB : HasDerivAt B db e)
    (htarget : Q e ∈ (extChartAt I x₀).target) :
    HasDerivAt
      (fun s ↦ coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b (Q s) (A s) (B s))
      (fderiv ℝ (fun q ↦ coordinateParallelOperator
          (I := I) (M := M) (E := E) cov x₀ b q (A e) (B e))
          (Q e) q' +
        coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b (Q e) da (B e) +
        coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b (Q e) (A e) db) e := by
  let PA : E → E := fun q ↦ coordinateParallelOperator
    (I := I) (M := M) (E := E) cov x₀ b q (A e) (B e)
  have hPA : DifferentiableAt ℝ PA (Q e) :=
    (coordinateParallelOperator_fixed_contDiffAt_of_mem_target
      (I := I) (M := M) (E := E) cov x₀ b htarget (A e) (B e)).differentiableAt
      (by norm_num)
  have hbase : HasDerivAt (fun s ↦ PA (Q s))
      (fderiv ℝ PA (Q e) q') e := by
    simpa [Function.comp_def] using
      (hPA.hasFDerivAt.comp e hQ.hasFDerivAt).hasDerivAt
  have hAdiff : HasDerivAt (fun s ↦ A s - A e) da e := by
    simpa using hA.sub_const (A e)
  have hBdiff : HasDerivAt (fun s ↦ B s - B e) db e := by
    simpa using hB.sub_const (B e)
  have hleft := coordinateParallelOperator_hasDerivAt_of_left_eq_zero
    (I := I) (M := M) (E := E) cov x₀ b hQ hAdiff (by simp)
      htarget (B e)
  have hright := coordinateParallelOperator_hasDerivAt_of_right_eq_zero
    (I := I) (M := M) (E := E) cov x₀ b hQ hA hBdiff (by simp) htarget
  have hsum := hbase.add hleft |>.add hright
  convert hsum using 1
  funext s
  dsimp only [PA]
  calc
    coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b (Q s) (A s) (B s) =
        coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (Q s) (A s) (B e) +
          coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (Q s) (A s) (B s - B e) := by
      rw [← map_add]
      congr 2
      abel
    _ = (coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (Q s) (A e) (B e) +
          coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (Q s) (A s - A e) (B e)) +
          coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (Q s) (A s) (B s - B e) := by
      rw [← coordinateParallelOperator_add_left_apply]
      congr 2
      abel
    _ = _ := rfl

/-- Coordinate representative of `D_e (∂ₜ F)` for a two-parameter
variation: `Q` is the base point, `W = ∂ₑQ`, `V = ∂ₜQ`, and
`dV = ∂ₑ∂ₜQ`. -/
def coordinateFirstVariationCovariantField
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (Q W V dV : ℝ → E) (e : ℝ) : E :=
  coordinateCovariantFieldDerivative
    (I := I) (M := M) cov x₀ b (Q e) (W e) (V e) (dV e)

/-- Differentiating `D_e (∂ₜ F)` in the variation parameter gives the exact
coordinate expression used by the pointwise second-variation commutator. -/
theorem coordinateFirstVariationCovariantField_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {Q W V dV : ℝ → E} {e : ℝ} {j c dj dc : E}
    (hQ : HasDerivAt Q j e) (hW : HasDerivAt W c e)
    (hV : HasDerivAt V dj e) (hdV : HasDerivAt dV dc e)
    (htarget : Q e ∈ (extChartAt I x₀).target) :
    HasDerivAt
      (coordinateFirstVariationCovariantField
        (I := I) (M := M) cov x₀ b Q W V dV)
      (dc +
        fderiv ℝ (fun q ↦ coordinateParallelOperator
          (I := I) (M := M) (E := E) cov x₀ b q (W e) (V e))
          (Q e) j +
        coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b (Q e) c (V e) +
        coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b (Q e) (W e) dj) e := by
  have hP := coordinateParallelOperator_apply_hasDerivAt
    (I := I) (M := M) (E := E) cov x₀ b hQ hW hV htarget
  unfold coordinateFirstVariationCovariantField
  simp only [coordinateCovariantFieldDerivative]
  convert hdV.add hP using 1
  · funext s
    rfl
  · abel

/-- Half the squared speed of a coordinate variation. -/
def coordinateEnergyDensity
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (Q V : ℝ → E) (e : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * inner ℝ
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (V e) ((extChartAt I x₀).symm (Q e)))
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (V e) ((extChartAt I x₀).symm (Q e)))

/-- The first-variation density `<Dₑ(∂ₜF), ∂ₜF>`. -/
def coordinateFirstVariationDensity
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (Q W V dV : ℝ → E) (e : ℝ) : ℝ :=
  inner ℝ
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (coordinateFirstVariationCovariantField
        (I := I) (M := M) cov x₀ b Q W V dV e)
      ((extChartAt I x₀).symm (Q e)))
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (V e) ((extChartAt I x₀).symm (Q e)))

/-- First variation of the half squared speed. -/
theorem coordinateEnergyDensity_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {Q W V dV : ℝ → E} {e : ℝ}
    (hQ : HasDerivAt Q (W e) e) (hV : HasDerivAt V (dV e) e)
    (htarget : Q e ∈ (extChartAt I x₀).target)
    (hframe : ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b k =ᶠ[
        nhds ((extChartAt I x₀).symm (Q e))]
        (trivializationAt E TM x₀).localFrame b k) :
    HasDerivAt
      (coordinateEnergyDensity (I := I) (M := M) x₀ b Q V)
      (coordinateFirstVariationDensity
        (I := I) (M := M) cov x₀ b Q W V dV e) e := by
  have hpair := coordinate_metricPairing_hasDerivAt
    (I := I) (M := M) (E := E) cov x₀ b hmetric
      hQ hV hV htarget hframe
  have hscaled := hpair.const_mul (2 : ℝ)⁻¹
  change HasDerivAt
    (coordinateEnergyDensity (I := I) (M := M) x₀ b Q V) _ e at hscaled
  apply hscaled.congr_deriv
  unfold coordinateFirstVariationDensity coordinateFirstVariationCovariantField
    coordinateCovariantFieldDerivative
  rw [real_inner_comm
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (V e) ((extChartAt I x₀).symm (Q e)))]
  ring

/-- Second pointwise variation of the half squared speed. -/
theorem coordinateFirstVariationDensity_hasDerivAt_general
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {Q W V dV : ℝ → E} {e : ℝ} {c dc : E}
    (hQ : HasDerivAt Q (W e) e) (hW : HasDerivAt W c e)
    (hV : HasDerivAt V (dV e) e) (hdV : HasDerivAt dV dc e)
    (htarget : Q e ∈ (extChartAt I x₀).target)
    (hframe : ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b k =ᶠ[
        nhds ((extChartAt I x₀).symm (Q e))]
        (trivializationAt E TM x₀).localFrame b k) :
    let B := coordinateFirstVariationCovariantField
      (I := I) (M := M) cov x₀ b Q W V dV e
    let dB := dc +
      fderiv ℝ (fun q ↦ coordinateParallelOperator
        (I := I) (M := M) (E := E) cov x₀ b q (W e) (V e))
        (Q e) (W e) +
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b (Q e) c (V e) +
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b (Q e) (W e) (dV e)
    HasDerivAt
      (coordinateFirstVariationDensity
        (I := I) (M := M) cov x₀ b Q W V dV)
      (inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (coordinateCovariantFieldDerivative
              (I := I) (M := M) cov x₀ b (Q e) (W e) B dB)
            ((extChartAt I x₀).symm (Q e)))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (V e) ((extChartAt I x₀).symm (Q e))) +
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            B ((extChartAt I x₀).symm (Q e)))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            B ((extChartAt I x₀).symm (Q e)))) e := by
  dsimp only
  have hB := coordinateFirstVariationCovariantField_hasDerivAt
    (I := I) (M := M) (E := E) cov x₀ b hQ hW hV hdV htarget
  apply coordinate_firstVariationDensity_hasDerivAt
    (I := I) (M := M) (E := E) cov x₀ b hmetric
      hQ hV hB
  · rfl
  · exact htarget
  · exact hframe

/-- The pointwise second variation of energy is the index-form density plus
the time derivative of the acceleration boundary pairing. -/
theorem coordinateSecondVariationDensity_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [IsContMDiffRiemannianBundle I 2 E TM]
    (hmetric : cov.IsMetricCompatibleTangent)
    (htorsion : cov.torsion = 0)
    {Q W V dV : ℝ → E} {e : ℝ} {c dc : E}
    (hQ : HasDerivAt Q (W e) e) (hW : HasDerivAt W c e)
    (hV : HasDerivAt V (dV e) e) (hdV : HasDerivAt dV dc e)
    (htarget : Q e ∈ (extChartAt I x₀).target)
    {O : Set M} (hOopen : IsOpen O)
    (hO : (extChartAt I x₀).symm (Q e) ∈ O)
    (hOframe : ∀ y ∈ O, ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b k y =
        (trivializationAt E TM x₀).localFrame b k y) :
    let y := (extChartAt I x₀).symm (Q e)
    let B := coordinateCovariantFieldDerivative
      (I := I) (M := M) cov x₀ b (Q e) (V e) (W e) (dV e)
    let C := c + coordinateParallelOperator
      (I := I) (M := M) (E := E) cov x₀ b (Q e) (W e) (W e)
    let dC := dc +
      fderiv ℝ (fun q ↦ coordinateParallelOperator
        (I := I) (M := M) (E := E) cov x₀ b q (W e) (W e))
        (Q e) (V e) +
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b (Q e) (dV e) (W e) +
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b (Q e) (W e) (dV e)
    let DtC := coordinateCovariantFieldDerivative
      (I := I) (M := M) cov x₀ b (Q e) (V e) C dC
    HasDerivAt
      (coordinateFirstVariationDensity
        (I := I) (M := M) cov x₀ b Q W V dV)
      (inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b B y)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b B y) -
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (W e) y)
          (curvature (cov := cov) y
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (W e) y)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (V e) y)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (V e) y)) +
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b DtC y)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (V e) y)) e := by
  dsimp only
  have hframe : ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b k =ᶠ[
        nhds ((extChartAt I x₀).symm (Q e))]
        (trivializationAt E TM x₀).localFrame b k := by
    intro k
    filter_upwards [hOopen.mem_nhds hO] with y hy
    exact hOframe y hy k
  have hsecond := coordinateFirstVariationDensity_hasDerivAt_general
    (I := I) (M := M) (E := E) cov x₀ b hmetric
      hQ hW hV hdV htarget hframe
  have hcomm : coordinateParallelOperator
      (I := I) (M := M) (E := E) cov x₀ b (Q e) (W e) (V e) =
      coordinateParallelOperator
        (I := I) (M := M) (E := E) cov x₀ b (Q e) (V e) (W e) :=
    coordinateParallelOperator_apply_comm_of_torsion_eq_zero
      (I := I) (M := M) (E := E) cov x₀ b htarget htorsion hframe
  have hB : coordinateFirstVariationCovariantField
      (I := I) (M := M) cov x₀ b Q W V dV e =
      coordinateCovariantFieldDerivative
        (I := I) (M := M) cov x₀ b (Q e) (V e) (W e) (dV e) := by
    unfold coordinateFirstVariationCovariantField
      coordinateCovariantFieldDerivative
    rw [hcomm]
  rw [hB] at hsecond
  have hidentity := coordinate_secondVariation_inner_identity
    (I := I) (M := M) (E := E) cov x₀ b hmetric htorsion
      htarget hOopen hO hOframe (V e) (W e) (dV e) c dc
  exact hsecond.congr_deriv hidentity

end BonnetMyersEntry.LocalGeodesicData
