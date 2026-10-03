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

public import LeanPool.PoincareGeometry.BonnetMyers.StrongNormalNeighborhood
public import LeanPool.PoincareGeometry.BonnetMyers.GaussLemma
public import LeanPool.PoincareGeometry.BonnetMyers.GlobalIntrinsicGeodesic

/-!
# Gauss identities for two-point coordinate geodesics

The ordinary normal-coordinate Gauss lemma fixes the centre of its chart as
the initial point of every geodesic.  A strong normal neighbourhood instead
uses one chart while the initial point varies.  This file separates those two
roles: an ordinary second-order solution may start at an arbitrary coordinate
`p`, while its manifold curve is read through the fixed chart at `x₀`.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
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

namespace LocalGeodesicData

variable [RiemannianBundle (TangentSpace I : M → Type u)]

/-- Read an ordinary coordinate ODE solution through a fixed manifold chart.
Unlike `LocalChartSecondOrderSolution.curve`, the initial coordinate need not
be the coordinate of the chart centre. -/
def ordinaryManifoldCurve
    {F : E → E → E} {p u : E}
    (x₀ : M) (sol : LocalSecondOrderSolution F p u) : ℝ → M :=
  (extChartAt I x₀).symm ∘ sol.curve

/-- The coordinate-frame metric pairing at a chart coordinate.  Keeping the
coordinate as an explicit ordinary argument lets initial-point equalities be
rewritten before dependent tangent-space instances are unfolded. -/
def coordinateInner
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (z u v : E) : ℝ :=
  inner ℝ
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u
      ((extChartAt I x₀).symm z))
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v
      ((extChartAt I x₀).symm z))

/-- The coordinate velocity of an ordinary solution is the manifold tangent
of its inverse-chart curve whenever the coordinate point remains in the chart
target. -/
lemma ordinaryManifoldCurve_hasMFDerivAt_coordinateFrame
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {F : E → E → E} {p u : E}
    (sol : LocalSecondOrderSolution F p u) {t : ℝ}
    (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (htarget : sol.curve t ∈ (extChartAt I x₀).target) :
    HasMFDerivAt (𝓘(ℝ, ℝ)) I ((extChartAt I x₀).symm ∘ sol.curve) t
      (ContinuousLinearMap.toSpanSingleton ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity t) ((extChartAt I x₀).symm (sol.curve t)))) := by
  have hcoord : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) sol.curve t
      (ContinuousLinearMap.toSpanSingleton ℝ (sol.velocity t)) :=
    (sol.curve_hasDeriv t ht).hasFDerivAt.hasMFDerivAt
  have hsymmWithin : HasMFDerivWithinAt (𝓘(ℝ, E)) I (extChartAt I x₀).symm
      (range (I : H → E)) (sol.curve t)
      (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (sol.curve t)) :=
    (mdifferentiableWithinAt_extChartAt_symm
      (I := I) (x := x₀) (z := sol.curve t) htarget).hasMFDerivWithinAt
  have hsymm : HasMFDerivAt (𝓘(ℝ, E)) I (extChartAt I x₀).symm (sol.curve t)
      (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (sol.curve t)) := by
    apply hsymmWithin.hasMFDerivAt
    rw [I.range_eq_univ]
    exact Filter.univ_mem
  have hraw : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      ((extChartAt I x₀).symm ∘ sol.curve) t
      ((mfderiv[range (I : H → E)] (extChartAt I x₀).symm (sol.curve t)) ∘SL
        ContinuousLinearMap.toSpanSingleton ℝ (sol.velocity t)) :=
    hsymm.comp t hcoord
  have hsource : (extChartAt I x₀).symm (sol.curve t) ∈
      (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact (extChartAt I x₀).map_target htarget
  have hframe := coordinateFrameCombination_eq_symmL (I := I) (M := M)
    (x₀ := x₀) b hsource (sol.velocity t)
  have htriv := TangentBundle.symmL_trivializationAt
    (I := I) (𝕜 := ℝ) (E := E) (x₀ := x₀)
    (x := (extChartAt I x₀).symm (sol.curve t)) hsource
  have htriv' := htriv
  rw [(extChartAt I x₀).right_inv htarget] at htriv'
  have hmf :
      (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (sol.curve t))
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E)
            (sol.curve t)).symm (sol.velocity t)) =
        (trivializationAt E TM x₀).symmL ℝ
          ((extChartAt I x₀).symm (sol.curve t)) (sol.velocity t) := by
    rw [← htriv']
    rfl
  have hmap :
      (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (sol.curve t)) ∘SL
          ContinuousLinearMap.toSpanSingleton ℝ (sol.velocity t) =
        ContinuousLinearMap.toSpanSingleton ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity t) ((extChartAt I x₀).symm (sol.curve t))) := by
    apply ContinuousLinearMap.ext
    intro s
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    change (mfderiv[range (I : H → E)] (extChartAt I x₀).symm
      (sol.curve t))
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E)
        (sol.curve t)).symm (s • sol.velocity t)) =
      s • coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) ((extChartAt I x₀).symm (sol.curve t))
    rw [map_smul, map_smul, hmf, hframe]
  exact hraw.congr_mfderiv hmap

/-- Conservation of speed for an ordinary coordinate solution whose initial
point may differ from the centre of the fixed chart. -/
lemma ordinarySecondOrder_speed_inner_hasDerivAt_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    {p u : E}
    (sol : LocalSecondOrderSolution (coordinateAcceleration cov x₀ b) p u)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (htarget : sol.curve t ∈ (extChartAt I x₀).target)
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
        𝓝 ((extChartAt I x₀).symm (sol.curve t))]
        (trivializationAt E TM x₀).localFrame b j) :
    HasDerivAt
      (fun s ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity s) ((extChartAt I x₀).symm (sol.curve s)))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity s) ((extChartAt I x₀).symm (sol.curve s)))) 0 t := by
  have hγ := ordinaryManifoldCurve_hasMFDerivAt_coordinateFrame
    (I := I) (M := M) x₀ b sol ht htarget
  have hchart : extChartAt I x₀ ((extChartAt I x₀).symm (sol.curve t)) =
      sol.curve t := (extChartAt I x₀).right_inv htarget
  have hvel : HasDerivAt sol.velocity (deriv sol.velocity t) t := by
    rw [(sol.velocity_hasDeriv t ht).deriv]
    exact sol.velocity_hasDeriv t ht
  have hzero :
      deriv sol.velocity t + coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ b (sol.curve t)
        (sol.velocity t) (sol.velocity t) = 0 := by
    rw [(sol.velocity_hasDeriv t ht).deriv]
    simp [coordinateAcceleration, coordinateParallelOperator_apply,
      Finset.sum_smul]
  have hinner := coordinateFrameCombination_inner_hasDerivAt_variable
    (I := I) (M := M) (E := E) (H := H) cov x₀ b
    (u := sol.velocity t) (w := sol.velocity) (v := sol.velocity)
    (dw := deriv sol.velocity t) (dv := deriv sol.velocity t)
    (γ := (extChartAt I x₀).symm ∘ sol.curve) (t := t)
    (hγ := hγ) (hγ' := by
      change (1 : ℝ) • coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) b (sol.velocity t)
          ((extChartAt I x₀).symm (sol.curve t)) = _
      exact one_smul ℝ _) (hy := by
      rw [← extChartAt_source (I := I) x₀]
      exact (extChartAt I x₀).map_target htarget)
    hmetric hframe hvel hvel
  simp only [Function.comp_apply] at hinner
  rw [hchart] at hinner
  have hframeZero : coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b (0 : E)
        ((extChartAt I x₀).symm (sol.curve t)) = 0 := by
    change (IntrinsicAcceleration.coordinateFrameLinear
      (I := I) (M := M) x₀ b ((extChartAt I x₀).symm (sol.curve t))) 0 = 0
    exact map_zero _
  rw [hzero, hframeZero] at hinner
  rw [inner_zero_left, inner_zero_right, zero_add] at hinner
  simpa using hinner

/-- Speed conservation on a closed time interval for an ordinary coordinate
solution in a fixed chart. -/
theorem ordinarySecondOrder_speed_inner_eq_initial
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    {p u : E}
    (sol : LocalSecondOrderSolution (coordinateAcceleration cov x₀ b) p u)
    (hradius : 1 < sol.radius)
    (htarget : ∀ t ∈ Icc (0 : ℝ) 1,
      sol.curve t ∈ (extChartAt I x₀).target)
    (hframe : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 ((extChartAt I x₀).symm (sol.curve t))]
          (trivializationAt E TM x₀).localFrame b j) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      coordinateInner (I := I) (M := M) x₀ b
          (sol.curve t) (sol.velocity t) (sol.velocity t) =
        coordinateInner (I := I) (M := M) x₀ b p u u := by
  let speed : ℝ → ℝ := fun s ↦ coordinateInner (I := I) (M := M) x₀ b
    (sol.curve s) (sol.velocity s) (sol.velocity s)
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt speed 0 t := by
    intro t ht
    have htRadius : t ∈ Ioo (-sol.radius) sol.radius := by
      constructor <;> linarith [ht.1, ht.2, hradius]
    simpa only [speed, coordinateInner] using ordinarySecondOrder_speed_inner_hasDerivAt_zero
      (I := I) (M := M) cov x₀ b hmetric sol htRadius (htarget t ht) (hframe t ht)
  have hcont : ContinuousOn speed (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun t ht ↦
    (hderiv t ⟨ht.1, le_of_lt ht.2⟩).hasDerivWithinAt)
  intro t ht
  have hs := hconst t ht
  dsimp only [speed] at hs
  rw [sol.initial_velocity, sol.initial_curve] at hs
  exact hs

/-- An ordinary coordinate geodesic with conserved squared speed has path
length equal to its initial speed, even when its initial point differs from
the centre of the fixed ambient chart. -/
theorem ordinarySecondOrder_pathELength_eq_initial_speed
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {F : E → E → E} {p u : E}
    (sol : LocalSecondOrderSolution F p u)
    (hradius : 1 < sol.radius)
    (htarget : ∀ t ∈ Ioo (0 : ℝ) 1,
      sol.curve t ∈ (extChartAt I x₀).target)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      coordinateInner (I := I) (M := M) x₀ b
          (sol.curve t) (sol.velocity t) (sol.velocity t) =
        coordinateInner (I := I) (M := M) x₀ b p u u) :
    pathELength I (ordinaryManifoldCurve (I := I) x₀ sol) 0 1 =
      ENNReal.ofReal
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u
          ((extChartAt I x₀).symm p)‖ := by
  rw [show ordinaryManifoldCurve (I := I) x₀ sol =
      (extChartAt I x₀).symm ∘ sol.curve by rfl]
  rw [inverseChart_pathELength_eq_coordinate_speed
    (I := I) (M := M) x₀ b sol.curve sol.velocity htarget
      (fun t ht ↦ sol.curve_hasDeriv t (by
        constructor <;> linarith [ht.1, ht.2, hradius]))]
  have hnorm : ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) ((extChartAt I x₀).symm (sol.curve t))‖ =
      ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u
        ((extChartAt I x₀).symm p)‖ := by
    intro t ht
    have hs := hspeed t ⟨ht.1.le, ht.2.le⟩
    simp only [coordinateInner, real_inner_self_eq_norm_sq] at hs
    nlinarith [norm_nonneg
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) ((extChartAt I x₀).symm (sol.curve t))),
      norm_nonneg
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u
          ((extChartAt I x₀).symm p))]
  rw [show (∫⁻ t in Ioo (0 : ℝ) 1,
      ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) ((extChartAt I x₀).symm (sol.curve t))‖ₑ) =
      ∫⁻ _t in Ioo (0 : ℝ) 1,
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u
          ((extChartAt I x₀).symm p)‖ₑ by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    simpa only [ofReal_norm] using congrArg ENNReal.ofReal (hnorm t ht)]
  rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo]
  rw [sub_zero, ENNReal.ofReal_one, mul_one]
  exact (ofReal_norm _).symm

/-- An ordinary coordinate solution is a `C¹` manifold path on every closed
interval strictly inside its ODE domain, provided its coordinate image stays
in the fixed chart target. -/
theorem ordinaryManifoldCurve_contMDiffOn
    (x₀ : M) {F : E → E → E} {p u : E}
    (sol : LocalSecondOrderSolution F p u)
    {a c : ℝ} (ha : -sol.radius < a) (hc : c < sol.radius) (hac : a < c)
    (htarget : ∀ t ∈ Icc a c, sol.curve t ∈ (extChartAt I x₀).target) :
    ContMDiffOn (𝓘(ℝ, ℝ)) I 1
      (ordinaryManifoldCurve (I := I) x₀ sol) (Icc a c) := by
  have hcoordinate : ContDiffOn ℝ 1 sol.curve (Icc a c) := by
    rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hac)]
    constructor
    · intro t ht
      exact (sol.curve_hasDeriv t (Icc_subset_Ioo ha hc ht)).differentiableAt
        |>.differentiableWithinAt
    · have hvelocity : ContinuousOn sol.velocity (Icc a c) := by
        intro t ht
        exact (sol.velocity_hasDeriv t (Icc_subset_Ioo ha hc ht)).continuousAt
          |>.continuousWithinAt
      apply hvelocity.congr
      intro t ht
      exact (sol.curve_hasDeriv t
        (Icc_subset_Ioo ha hc ht)).hasDerivWithinAt.derivWithin
          ((uniqueDiffOn_Icc hac).uniqueDiffWithinAt ht)
  have hmaps : MapsTo sol.curve (Icc a c) (extChartAt I x₀).target := htarget
  have hcurve := (contMDiffOn_extChartAt_symm
    (I := I) (n := (1 : WithTop ℕ∞)) x₀).comp hcoordinate.contMDiffOn hmaps
  simpa only [ordinaryManifoldCurve, Function.comp_def] using hcurve

/-- A cutoff-flow trajectory in the genuine coordinate-geodesic region is
the fixed-chart state readout of any global geodesic with the same initial
state.  The slightly asymmetric interval contains both endpoint times and a
neighbourhood of them, which is convenient for time-one connector
identification. -/
theorem coordinateFlow_eq_globalGeodesic_fixedChartState
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    (G : E × E → E × E) (Φ : (E × E) → ℝ → E × E)
    (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ : ℝ ↦ G))
    {s : E × E}
    (hactual : ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ s t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ s t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ s t) ∧
        G =ᶠ[𝓝 (Φ s t)]
          (fun r ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) r))
    {c : M} {v : TM c}
    (g : IntrinsicGeodesic.GlobalGeodesic (I := I) (M := M) cov c v)
    (hinitial : s =
      (extChartAt I x₀ (IntrinsicGeodesic.GlobalGeodesic.curve g 0),
        (trivializationAt E TM x₀).continuousLinearMapAt ℝ
          (IntrinsicGeodesic.GlobalGeodesic.curve g 0)
          (IntrinsicGeodesic.GlobalGeodesic.velocity g 0)))
    (hglobalFrame : ∀ t ∈ Ioo (-1 : ℝ) 2,
      IntrinsicAcceleration.smoothFrameAgreementSet
        (I := I) (M := M) x₀ b ∈
          𝓝 (IntrinsicGeodesic.GlobalGeodesic.curve g t)) :
    Set.EqOn (Φ s) (fun t ↦
      (extChartAt I x₀ (IntrinsicGeodesic.GlobalGeodesic.curve g t),
        (trivializationAt E TM x₀).continuousLinearMapAt ℝ
          (IntrinsicGeodesic.GlobalGeodesic.curve g t)
          (IntrinsicGeodesic.GlobalGeodesic.velocity g t)))
      (Ioo (-1 : ℝ) 2) := by
  let p₂ : ℝ → E × E := fun t ↦
    (extChartAt I x₀ (IntrinsicGeodesic.GlobalGeodesic.curve g t),
      (trivializationAt E TM x₀).continuousLinearMapAt ℝ
        (IntrinsicGeodesic.GlobalGeodesic.curve g t)
        (IntrinsicGeodesic.GlobalGeodesic.velocity g t))
  have hp₁ : ∀ t ∈ Ioo (-1 : ℝ) 2,
      HasDerivAt (Φ s)
        (secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ s t)) t := by
    intro t ht
    have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [ht.1], ht.2.le⟩
    have h := hΦcurve s t
    change HasDerivAt (Φ s) (G (Φ s t)) t at h
    rw [(hactual t htI).2.1] at h
    exact h
  have hp₂ : ∀ t ∈ Ioo (-1 : ℝ) 2,
      HasDerivAt p₂
        (secondOrderSystem (coordinateAcceleration cov x₀ b) (p₂ t)) t := by
    intro t ht
    simpa only [p₂] using
      (IntrinsicGeodesic.GlobalGeodesic.hasDerivAt_fixedChartState
        (I := I) (M := M) g x₀ b hmetric t (hglobalFrame t ht))
  have hF : ∀ t ∈ Ioo (-1 : ℝ) 2,
      ContDiffAt ℝ 1
        (fun q : E × E ↦ secondOrderSystem
          (coordinateAcceleration cov x₀ b) q) (Φ s t) := by
    intro t ht
    apply coordinateAcceleration_system_contDiffAt_of_mem_target
    exact (hactual t ⟨by linarith [ht.1], ht.2.le⟩).1
  have hzero : (0 : ℝ) ∈ Ioo (-1 : ℝ) 2 := by norm_num
  have hinit : Φ s 0 = p₂ 0 := by
    rw [hΦzero, hinitial]
  exact secondOrder_pair_eqOn_of_same_initial
    (F := coordinateAcceleration cov x₀ b) (J := Ioo (-1 : ℝ) 2)
      isOpen_Ioo isPreconnected_Ioo hzero hp₁ hp₂ hF hinit

/-- The connector selected by a two-point endpoint equivalence is a genuine
`C¹` competitor for Riemannian distance, and its length is exactly its
initial speed. -/
theorem twoPointConnector_pathELength_eq_initial_speed
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    (G : E × E → E × E) (Φ : (E × E) → ℝ → E × E)
    (R : OpenPartialHomeomorph (E × E) (E × E))
    (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ : ℝ ↦ G))
    (hR : ∀ s, R s = (s.1, (Φ s 1).1))
    (hactual : ∀ s ∈ R.source, ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ s t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ s t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ s t) ∧
        G =ᶠ[𝓝 (Φ s t)]
          (fun r ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) r))
    (hframe : ∀ s ∈ R.source, ∀ t ∈ Icc (-1 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 ((extChartAt I x₀).symm (Φ s t).1)]
          (trivializationAt E TM x₀).localFrame b j)
    {p q : E} (hpq : (p, q) ∈ R.target) :
    let s : E × E := R.symm (p, q)
    pathELength I (fun t ↦ (extChartAt I x₀).symm (Φ s t).1) 0 1 =
      ENNReal.ofReal
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b s.2
          ((extChartAt I x₀).symm p)‖ ∧
    riemannianEDist I ((extChartAt I x₀).symm p)
        ((extChartAt I x₀).symm q) ≤
      pathELength I (fun t ↦ (extChartAt I x₀).symm (Φ s t).1) 0 1 := by
  dsimp only
  let s : E × E := R.symm (p, q)
  have hsSource : s ∈ R.source := R.map_target hpq
  have hright := R.right_inv hpq
  rw [hR] at hright
  have hsp : s.1 = p := congrArg Prod.fst hright
  have hsq : (Φ s 1).1 = q := congrArg Prod.snd hright
  let sol : LocalSecondOrderSolution (coordinateAcceleration cov x₀ b) p s.2 :=
    { curve := fun t ↦ (Φ s t).1
      velocity := fun t ↦ (Φ s t).2
      radius := 2
      radius_pos := by norm_num
      initial_curve := (congrArg Prod.fst (hΦzero s)).trans hsp
      initial_velocity := congrArg Prod.snd (hΦzero s)
      curve_hasDeriv := by
        intro t ht
        have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hsderiv := hΦcurve s t
        change HasDerivAt (Φ s) (G (Φ s t)) t at hsderiv
        rw [(hactual s hsSource t htI).2.1] at hsderiv
        simpa [secondOrderSystem] using hsderiv.hasFDerivAt.fst.hasDerivAt
      velocity_hasDeriv := by
        intro t ht
        have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hsderiv := hΦcurve s t
        change HasDerivAt (Φ s) (G (Φ s t)) t at hsderiv
        rw [(hactual s hsSource t htI).2.1] at hsderiv
        simpa [secondOrderSystem] using hsderiv.hasFDerivAt.snd.hasDerivAt }
  have htarget : ∀ t ∈ Icc (0 : ℝ) 1,
      sol.curve t ∈ (extChartAt I x₀).target := by
    intro t ht
    exact (hactual s hsSource t
      ⟨by linarith [ht.1], by linarith [ht.2]⟩).1
  have hspeed := ordinarySecondOrder_speed_inner_eq_initial
    (I := I) (M := M) cov x₀ b hmetric sol (by norm_num)
      htarget (fun t ht ↦ hframe s hsSource t
        ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hlength := ordinarySecondOrder_pathELength_eq_initial_speed
    (I := I) (M := M) x₀ b sol (by norm_num)
      (fun t ht ↦ htarget t ⟨ht.1.le, ht.2.le⟩) hspeed
  have hsmooth := ordinaryManifoldCurve_contMDiffOn
    (I := I) (M := M) x₀ sol (by norm_num) (by norm_num) (by norm_num)
      htarget
  have hdist := riemannianEDist_le_pathELength hsmooth rfl rfl (by norm_num)
  have hcurveEq : ordinaryManifoldCurve (I := I) x₀ sol =
      (fun t ↦ (extChartAt I x₀).symm (Φ s t).1) := by rfl
  have hstart : ordinaryManifoldCurve (I := I) x₀ sol 0 =
      (extChartAt I x₀).symm p := by
    change (extChartAt I x₀).symm (Φ s 0).1 = _
    rw [hΦzero, hsp]
  have hend : ordinaryManifoldCurve (I := I) x₀ sol 1 =
      (extChartAt I x₀).symm q := by
    change (extChartAt I x₀).symm (Φ s 1).1 = _
    rw [hsq]
  constructor
  · rw [← hcurveEq]
    exact hlength
  · rw [← hstart, ← hend, ← hcurveEq]
    exact hdist

/-- Half the squared initial speed of the unique coordinate geodesic from
`p` to `y` represented by a two-point endpoint local equivalence. -/
def twoPointConnectorEnergy
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (R : OpenPartialHomeomorph (E × E) (E × E)) (p y : E) : ℝ :=
  let u := (R.symm (p, y)).2
  (1 / 2 : ℝ) * coordinateInner (I := I) (M := M) x₀ b p u u

/-- Half the squared metric distance is bounded above by the energy of the
two-point connector.  Unlike local minimality, this only uses that the
connector is an admissible `C¹` path. -/
theorem half_dist_sq_le_twoPointConnectorEnergy
    [PseudoMetricSpace M]
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    (G : E × E → E × E) (Φ : (E × E) → ℝ → E × E)
    (R : OpenPartialHomeomorph (E × E) (E × E))
    (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ : ℝ ↦ G))
    (hR : ∀ s, R s = (s.1, (Φ s 1).1))
    (hactual : ∀ s ∈ R.source, ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ s t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ s t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ s t) ∧
        G =ᶠ[𝓝 (Φ s t)]
          (fun r ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) r))
    (hframe : ∀ s ∈ R.source, ∀ t ∈ Icc (-1 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 ((extChartAt I x₀).symm (Φ s t).1)]
          (trivializationAt E TM x₀).localFrame b j)
    (hedist : ∀ a c : M,
      riemannianEDist I a c = ENNReal.ofReal (dist a c))
    {p q : E} (hpq : (p, q) ∈ R.target) :
    (1 / 2 : ℝ) * dist ((extChartAt I x₀).symm p)
        ((extChartAt I x₀).symm q) ^ 2 ≤
      twoPointConnectorEnergy (I := I) (M := M) x₀ b R p q := by
  let s : E × E := R.symm (p, q)
  obtain ⟨hlength, hdist⟩ := twoPointConnector_pathELength_eq_initial_speed
    (I := I) (M := M) cov x₀ b hmetric G Φ R hΦzero hΦcurve hR
      hactual hframe hpq
  let A : ℝ := ‖coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b s.2 ((extChartAt I x₀).symm p)‖
  have hdistENN : ENNReal.ofReal
      (dist ((extChartAt I x₀).symm p) ((extChartAt I x₀).symm q)) ≤
      ENNReal.ofReal A := by
    rw [← hedist, ← hlength]
    exact hdist
  have hdistReal : dist ((extChartAt I x₀).symm p)
      ((extChartAt I x₀).symm q) ≤ A :=
    (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp hdistENN
  change (1 / 2 : ℝ) * dist ((extChartAt I x₀).symm p)
      ((extChartAt I x₀).symm q) ^ 2 ≤
    (1 / 2 : ℝ) * coordinateInner (I := I) (M := M) x₀ b p s.2 s.2
  simp only [coordinateInner, real_inner_self_eq_norm_sq]
  change (1 / 2 : ℝ) * dist ((extChartAt I x₀).symm p)
      ((extChartAt I x₀).symm q) ^ 2 ≤ (1 / 2 : ℝ) * A ^ 2
  nlinarith [(dist_nonneg : 0 ≤ dist ((extChartAt I x₀).symm p)
    ((extChartAt I x₀).symm q)), norm_nonneg
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b s.2
        ((extChartAt I x₀).symm p))]

/-- The time derivative of the pairing between an ordinary coordinate
geodesic velocity and the position component of a variational field. -/
theorem ordinarySecondOrder_radialVariation_inner_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    {p u : E}
    (sol : LocalSecondOrderSolution (coordinateAcceleration cov x₀ b) p u)
    {W : ℝ → E × E} {t : ℝ}
    (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (htarget : sol.curve t ∈ (extChartAt I x₀).target)
    (hWposition : HasDerivAt (fun s ↦ (W s).1) (W t).2 t)
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
        𝓝 ((extChartAt I x₀).symm (sol.curve t))]
        (trivializationAt E TM x₀).localFrame b j) :
    HasDerivAt
      (fun s ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity s) ((extChartAt I x₀).symm (sol.curve s)))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (W s).1 ((extChartAt I x₀).symm (sol.curve s))))
      (inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity t) ((extChartAt I x₀).symm (sol.curve t)))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          ((W t).2 + coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (sol.curve t) (sol.velocity t) (W t).1)
          ((extChartAt I x₀).symm (sol.curve t)))) t := by
  have hγ := ordinaryManifoldCurve_hasMFDerivAt_coordinateFrame
    (I := I) (M := M) x₀ b sol ht htarget
  have hchart : extChartAt I x₀ ((extChartAt I x₀).symm (sol.curve t)) =
      sol.curve t := (extChartAt I x₀).right_inv htarget
  have hvel : HasDerivAt sol.velocity (deriv sol.velocity t) t := by
    rw [(sol.velocity_hasDeriv t ht).deriv]
    exact sol.velocity_hasDeriv t ht
  have hzero :
      deriv sol.velocity t + coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ b (sol.curve t)
        (sol.velocity t) (sol.velocity t) = 0 := by
    rw [(sol.velocity_hasDeriv t ht).deriv]
    simp [coordinateAcceleration, coordinateParallelOperator_apply,
      Finset.sum_smul]
  have hinner := coordinateFrameCombination_inner_hasDerivAt_variable
    (I := I) (M := M) (E := E) (H := H) cov x₀ b
    (u := sol.velocity t) (w := sol.velocity) (v := fun s ↦ (W s).1)
    (dw := deriv sol.velocity t) (dv := (W t).2)
    (γ := (extChartAt I x₀).symm ∘ sol.curve) (t := t)
    (hγ := hγ) (hγ' := by
      change (1 : ℝ) • coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) b (sol.velocity t)
          ((extChartAt I x₀).symm (sol.curve t)) = _
      exact one_smul ℝ _) (hy := by
        rw [← extChartAt_source (I := I) x₀]
        exact (extChartAt I x₀).map_target htarget)
    hmetric hframe hvel hWposition
  simp only [Function.comp_apply] at hinner
  rw [hchart] at hinner
  have hframeZero : coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b (0 : E)
        ((extChartAt I x₀).symm (sol.curve t)) = 0 := by
    change (IntrinsicAcceleration.coordinateFrameLinear
      (I := I) (M := M) x₀ b ((extChartAt I x₀).symm (sol.curve t))) 0 = 0
    exact map_zero _
  rw [hzero, hframeZero] at hinner
  rw [inner_zero_left, zero_add] at hinner
  simpa using hinner

/-- A fixed-initial-position variation of an actual two-point coordinate
flow has the usual covariant Gauss pairing.  The initial coordinate `p` may
differ from the centre `extChartAt I x₀ x₀` of the ambient chart. -/
theorem exists_twoPoint_variation_covariant_pairing
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    (G : E × E → E × E) (Φ : (E × E) → ℝ → E × E)
    (S : Set (E × E))
    (hG : ContDiff ℝ 1 G) (hGcompact : HasCompactSupport G)
    (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ : ℝ ↦ G))
    (hSopen : IsOpen S)
    (hactual : ∀ q ∈ S, ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ q t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ q t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ q t) ∧
        G =ᶠ[𝓝 (Φ q t)]
          (fun r ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) r))
    (hframe : ∀ q ∈ S, ∀ t ∈ Icc (-1 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 ((extChartAt I x₀).symm (Φ q t).1)]
          (trivializationAt E TM x₀).localFrame b j)
    {p u : E} (hpu : (p, u) ∈ S) (w : E) :
    ∃ W : ℝ → E × E,
      W 0 = (0, w) ∧
      (∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivAt (fun s ↦ (W s).1) (W t).2 t) ∧
      (∀ t, 0 ≤ t →
        HasDerivAt (fun s : ℝ ↦ Φ (p, u + s • w) t) (W t) 0) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1,
        inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (Φ (p, u) t).2 ((extChartAt I x₀).symm (Φ (p, u) t).1))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              ((W t).2 + coordinateParallelOperator
                (I := I) (M := M) (E := E) cov x₀ b (Φ (p, u) t).1
                  (W t).1 (Φ (p, u) t).2)
              ((extChartAt I x₀).symm (Φ (p, u) t).1)) =
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              u ((extChartAt I x₀).symm p))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              w ((extChartAt I x₀).symm p))) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        coordinateInner (I := I) (M := M) x₀ b
            (Φ (p, u) t).1 (Φ (p, u) t).2 (Φ (p, u) t).2 =
          coordinateInner (I := I) (M := M) x₀ b p u u := by
  obtain ⟨K, A, W, hA, hAeq, hWzero, hWderiv, hWvariation⟩ :=
    exists_firstVariation_of_contDiff_compactSupport_flow
      hG hGcompact hΦzero hΦcurve (p, u) (0, w)
  have hAactual : ∀ t ∈ Icc (-2 : ℝ) 2,
      A t = fderiv ℝ
        (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q)
        (Φ (p, u) t) := by
    intro t ht
    calc
      A t = fderiv ℝ G (Φ (p, u) t) := hAeq t
      _ = fderiv ℝ
          (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q)
          (Φ (p, u) t) := ((hactual (p, u) hpu t ht).2.2).fderiv_eq
  have hWposition : ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivAt (fun s ↦ (W s).1) (W t).2 t := by
    intro t ht
    have hFdiff : DifferentiableAt ℝ
        (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q)
        (Φ (p, u) t) :=
      (coordinateAcceleration_system_contDiffAt_of_mem_target
        (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
        ((hactual (p, u) hpu t ht).1) (Φ (p, u) t).2).differentiableAt
          one_ne_zero
    have htime := (hWderiv t).hasFDerivAt.fst.hasDerivAt
    rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] at htime
    change HasDerivAt (fun s ↦ (W s).1) ((A t (W t)).1) t at htime
    rw [hAactual t ht,
      fderiv_secondOrderSystem_fst_apply
        (F := coordinateAcceleration cov x₀ b) hFdiff] at htime
    exact htime
  have hvariation : ∀ t, 0 ≤ t →
      HasDerivAt (fun s : ℝ ↦ Φ (p, u + s • w) t) (W t) 0 := by
    intro t ht
    simpa using hWvariation t ht
  have htendsto : Tendsto (fun s : ℝ ↦ (p, u + s • w)) (𝓝 0) (𝓝 (p, u)) := by
    have hcont : ContinuousAt (fun s : ℝ ↦ (p, u + s • w)) 0 := by fun_prop
    change Tendsto (fun s : ℝ ↦ (p, u + s • w)) (𝓝 0)
      (𝓝 (p, u + (0 : ℝ) • w)) at hcont
    simpa only [zero_smul, add_zero] using hcont
  have hperturbS : ∀ᶠ s in 𝓝 (0 : ℝ), (p, u + s • w) ∈ S :=
    htendsto.eventually (hSopen.mem_nhds hpu)
  let solOf : ∀ v : E, (p, v) ∈ S →
      LocalSecondOrderSolution (coordinateAcceleration cov x₀ b) p v :=
    fun v hv ↦
      { curve := fun t ↦ (Φ (p, v) t).1
        velocity := fun t ↦ (Φ (p, v) t).2
        radius := 2
        radius_pos := by norm_num
        initial_curve := congrArg Prod.fst (hΦzero (p, v))
        initial_velocity := congrArg Prod.snd (hΦzero (p, v))
        curve_hasDeriv := by
          intro t ht
          have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
          have hs := hΦcurve (p, v) t
          change HasDerivAt (Φ (p, v)) (G (Φ (p, v) t)) t at hs
          rw [(hactual (p, v) hv t htI).2.1] at hs
          simpa [secondOrderSystem] using hs.hasFDerivAt.fst.hasDerivAt
        velocity_hasDeriv := by
          intro t ht
          have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
          have hs := hΦcurve (p, v) t
          change HasDerivAt (Φ (p, v)) (G (Φ (p, v) t)) t at hs
          rw [(hactual (p, v) hv t htI).2.1] at hs
          simpa [secondOrderSystem] using hs.hasFDerivAt.snd.hasDerivAt }
  have hspeed (v : E) (hv : (p, v) ∈ S) : ∀ t ∈ Icc (0 : ℝ) 1,
      coordinateInner (I := I) (M := M) x₀ b
          (Φ (p, v) t).1 (Φ (p, v) t).2 (Φ (p, v) t).2 =
        coordinateInner (I := I) (M := M) x₀ b p v v := by
    intro t ht
    have hs := ordinarySecondOrder_speed_inner_eq_initial
      (I := I) (M := M) cov x₀ b hmetric (solOf v hv) (by norm_num)
      (fun s hs ↦ (hactual (p, v) hv s
        ⟨by linarith [hs.1], by linarith [hs.2]⟩).1)
      (fun s hs ↦ hframe (p, v) hv s
        ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      t ht
    simpa only [solOf] using hs
  have hpair : ∀ t ∈ Ioo (0 : ℝ) 1,
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (Φ (p, u) t).2 ((extChartAt I x₀).symm (Φ (p, u) t).1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            ((W t).2 + coordinateParallelOperator
              (I := I) (M := M) (E := E) cov x₀ b (Φ (p, u) t).1
                (W t).1 (Φ (p, u) t).2)
            ((extChartAt I x₀).symm (Φ (p, u) t).1)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            u ((extChartAt I x₀).symm p))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            w ((extChartAt I x₀).symm p)) := by
    intro t ht
    let Q : ℝ → E × E := fun s ↦ Φ (p, u + s • w) t
    have hQ : HasDerivAt Q (W t) 0 := by
      simpa only [Q] using hvariation t (le_of_lt ht.1)
    have htime := coordinate_flow_state_speed_hasDerivAt
      (I := I) (M := M) (E := E) (H := H) cov x₀ b hmetric hQ
      (by
        simpa only [Q, zero_smul, add_zero] using
          (hactual (p, u) hpu t
            ⟨by linarith [ht.1], by linarith [ht.2]⟩).1)
      (by
        intro j
        simpa only [Q, zero_smul, add_zero] using
          hframe (p, u) hpu t
            ⟨le_of_lt (by linarith [ht.1]), le_of_lt ht.2⟩ j)
    have hQzero : Q 0 = Φ (p, u) t := by simp [Q]
    rw [hQzero] at htime
    have htimeClean : HasDerivAt
        (fun s ↦ inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (Q s).2 ((extChartAt I x₀).symm (Q s).1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (Q s).2 ((extChartAt I x₀).symm (Q s).1)))
        (inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              ((W t).2 + coordinateParallelOperator
                (I := I) (M := M) (E := E) cov x₀ b (Φ (p, u) t).1
                  (W t).1 (Φ (p, u) t).2)
              ((extChartAt I x₀).symm (Φ (p, u) t).1))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (Φ (p, u) t).2 ((extChartAt I x₀).symm (Φ (p, u) t).1)) +
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (Φ (p, u) t).2 ((extChartAt I x₀).symm (Φ (p, u) t).1))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              ((W t).2 + coordinateParallelOperator
                (I := I) (M := M) (E := E) cov x₀ b (Φ (p, u) t).1
                  (W t).1 (Φ (p, u) t).2)
              ((extChartAt I x₀).symm (Φ (p, u) t).1))) 0 := by
      simpa only using htime
    let L : E →L[ℝ] TM ((extChartAt I x₀).symm p) :=
      (IntrinsicAcceleration.coordinateFrameLinear
        (I := I) (M := M) x₀ b ((extChartAt I x₀).symm p)).toContinuousLinearMap
    have huv : HasDerivAt (fun s : ℝ ↦ u + s • w) w 0 := by
      simpa [add_comm] using
        ((hasDerivAt_id' (0 : ℝ)).smul_const w |>.add_const u)
    have hL : HasDerivAt (fun s : ℝ ↦ L (u + s • w)) (L w) 0 :=
      L.hasFDerivAt.comp_hasDerivAt 0 huv
    have hinitial := hL.inner ℝ hL
    have hLapply (q : E) : L q =
        coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b q
          ((extChartAt I x₀).symm p) := rfl
    have hinitial' : HasDerivAt
        (fun s : ℝ ↦ inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (u + s • w) ((extChartAt I x₀).symm p))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (u + s • w) ((extChartAt I x₀).symm p)))
        (inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              u ((extChartAt I x₀).symm p))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              w ((extChartAt I x₀).symm p)) +
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              w ((extChartAt I x₀).symm p))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              u ((extChartAt I x₀).symm p))) 0 := by
      simpa only [hLapply, zero_smul, add_zero] using hinitial
    have hspeedEq :
        (fun s : ℝ ↦ coordinateInner (I := I) (M := M) x₀ b
          (Q s).1 (Q s).2 (Q s).2) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ ↦ coordinateInner (I := I) (M := M) x₀ b
          p (u + s • w) (u + s • w)) := by
      filter_upwards [hperturbS] with s hs
      simpa only [Q] using hspeed (u + s • w) hs t
        ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have htimeCoordinate : HasDerivAt
        (fun s : ℝ ↦ coordinateInner (I := I) (M := M) x₀ b
          (Q s).1 (Q s).2 (Q s).2)
        (inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              ((W t).2 + coordinateParallelOperator
                (I := I) (M := M) (E := E) cov x₀ b (Φ (p, u) t).1
                  (W t).1 (Φ (p, u) t).2)
              ((extChartAt I x₀).symm (Φ (p, u) t).1))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (Φ (p, u) t).2 ((extChartAt I x₀).symm (Φ (p, u) t).1)) +
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (Φ (p, u) t).2 ((extChartAt I x₀).symm (Φ (p, u) t).1))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              ((W t).2 + coordinateParallelOperator
                (I := I) (M := M) (E := E) cov x₀ b (Φ (p, u) t).1
                  (W t).1 (Φ (p, u) t).2)
              ((extChartAt I x₀).symm (Φ (p, u) t).1))) 0 := by
      simpa only [coordinateInner] using htimeClean
    have hinitialCoordinate : HasDerivAt
        (fun s : ℝ ↦ coordinateInner (I := I) (M := M) x₀ b
          p (u + s • w) (u + s • w))
        (inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              u ((extChartAt I x₀).symm p))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              w ((extChartAt I x₀).symm p)) +
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              w ((extChartAt I x₀).symm p))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              u ((extChartAt I x₀).symm p))) 0 := by
      simpa only [coordinateInner] using hinitial'
    have htime' := htimeCoordinate.congr_of_eventuallyEq hspeedEq.symm
    have hderivEq := hinitialCoordinate.unique htime'
    rw [real_inner_comm
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        u ((extChartAt I x₀).symm p))
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        w ((extChartAt I x₀).symm p))] at hderivEq
    rw [real_inner_comm
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (Φ (p, u) t).2 ((extChartAt I x₀).symm (Φ (p, u) t).1))
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        ((W t).2 + coordinateParallelOperator
          (I := I) (M := M) (E := E) cov x₀ b (Φ (p, u) t).1
            (W t).1 (Φ (p, u) t).2)
        ((extChartAt I x₀).symm (Φ (p, u) t).1))] at hderivEq
    linarith
  exact ⟨W, hWzero, hWposition, hvariation, hpair, hspeed u hpu⟩

/-- Endpoint Gauss identity for every connector represented by an open
two-point coordinate-flow source.  The derivative varies only the endpoint;
the initial coordinate is fixed. -/
theorem twoPoint_endpoint_gauss_identity
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent) (htorsion : cov.torsion = 0)
    (G : E × E → E × E) (Φ : (E × E) → ℝ → E × E)
    (S : Set (E × E))
    (hG : ContDiff ℝ 1 G) (hGcompact : HasCompactSupport G)
    (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ : ℝ ↦ G))
    (hΦsmooth : ContDiff ℝ 1 (fun q ↦ Φ q 1))
    (hSopen : IsOpen S)
    (hactual : ∀ q ∈ S, ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ q t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ q t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ q t) ∧
        G =ᶠ[𝓝 (Φ q t)]
          (fun r ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) r))
    (hframe : ∀ q ∈ S, ∀ t ∈ Icc (-1 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 ((extChartAt I x₀).symm (Φ q t).1)]
          (trivializationAt E TM x₀).localFrame b j)
    {p u : E} (hpu : (p, u) ∈ S) (w : E) :
    coordinateInner (I := I) (M := M) x₀ b
        (Φ (p, u) 1).1 (Φ (p, u) 1).2
        (fderiv ℝ (fun v : E ↦ (Φ (p, v) 1).1) u w) =
      coordinateInner (I := I) (M := M) x₀ b p u w := by
  obtain ⟨W, hWzero, hWposition, hvariation, hpair, _hspeed⟩ :=
    exists_twoPoint_variation_covariant_pairing
      (I := I) (M := M) cov x₀ b hmetric G Φ S hG hGcompact
        hΦzero hΦcurve hSopen hactual hframe hpu w
  let sol : LocalSecondOrderSolution (coordinateAcceleration cov x₀ b) p u :=
    { curve := fun t ↦ (Φ (p, u) t).1
      velocity := fun t ↦ (Φ (p, u) t).2
      radius := 2
      radius_pos := by norm_num
      initial_curve := congrArg Prod.fst (hΦzero (p, u))
      initial_velocity := congrArg Prod.snd (hΦzero (p, u))
      curve_hasDeriv := by
        intro t ht
        have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hs := hΦcurve (p, u) t
        change HasDerivAt (Φ (p, u)) (G (Φ (p, u) t)) t at hs
        rw [(hactual (p, u) hpu t htI).2.1] at hs
        simpa [secondOrderSystem] using hs.hasFDerivAt.fst.hasDerivAt
      velocity_hasDeriv := by
        intro t ht
        have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hs := hΦcurve (p, u) t
        change HasDerivAt (Φ (p, u)) (G (Φ (p, u) t)) t at hs
        rw [(hactual (p, u) hpu t htI).2.1] at hs
        simpa [secondOrderSystem] using hs.hasFDerivAt.snd.hasDerivAt }
  let cross : ℝ → ℝ := fun t ↦ coordinateInner (I := I) (M := M) x₀ b
    (Φ (p, u) t).1 (Φ (p, u) t).2 (W t).1
  let C : ℝ := coordinateInner (I := I) (M := M) x₀ b p u w
  have hcrossDynamic : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt cross
        (inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (Φ (p, u) t).2 ((extChartAt I x₀).symm (Φ (p, u) t).1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            ((W t).2 + coordinateParallelOperator
              (I := I) (M := M) (E := E) cov x₀ b (Φ (p, u) t).1
                (Φ (p, u) t).2 (W t).1)
            ((extChartAt I x₀).symm (Φ (p, u) t).1))) t := by
    intro t ht
    have htRadius : t ∈ Ioo (-sol.radius) sol.radius := by
      change t ∈ Ioo (-2 : ℝ) 2
      constructor <;> linarith [ht.1, ht.2]
    have hraw := ordinarySecondOrder_radialVariation_inner_hasDerivAt
      (I := I) (M := M) cov x₀ b hmetric sol htRadius
      ((hactual (p, u) hpu t
        ⟨by linarith [ht.1], by linarith [ht.2]⟩).1)
      (hWposition t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (hframe (p, u) hpu t
        ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    simpa only [cross, coordinateInner, sol] using hraw
  have hzero : cross 0 = 0 := by
    have hstate0 := hΦzero (p, u)
    have hframeZero : coordinateFrameCombination
        (I := I) (M := M) (x₀ := x₀) b (0 : E)
          ((extChartAt I x₀).symm p) = 0 := by
      change (IntrinsicAcceleration.coordinateFrameLinear
        (I := I) (M := M) x₀ b ((extChartAt I x₀).symm p)) 0 = 0
      exact map_zero _
    dsimp only [cross, coordinateInner]
    rw [hstate0, hWzero, hframeZero, inner_zero_right]
  have hderivZero : HasDerivAt cross C 0 := by
    have hraw := hcrossDynamic 0 (by constructor <;> norm_num)
    have hstate0 := hΦzero (p, u)
    have hparallelZero : coordinateParallelOperator
        (I := I) (M := M) (E := E) cov x₀ b p u (0 : E) = 0 := by
      simp [coordinateParallelOperator_apply]
    rw [hstate0, hWzero, hparallelZero, add_zero] at hraw
    simpa only [C, coordinateInner] using hraw
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt cross C t := by
    intro t ht
    have hraw := hcrossDynamic t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hcomm := coordinateParallelOperator_apply_comm_of_torsion_eq_zero
      (I := I) (M := M) (E := E) cov x₀ b
      ((hactual (p, u) hpu t
        ⟨by linarith [ht.1], by linarith [ht.2]⟩).1)
      htorsion
      (hframe (p, u) hpu t
        ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (u := (Φ (p, u) t).2) (w := (W t).1)
    rw [hcomm, hpair t ht] at hraw
    simpa only [C, coordinateInner] using hraw
  have hcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt cross t := by
    intro t ht
    exact (hcrossDynamic t ht).continuousAt
  have hcrossEq : ∀ t ∈ Icc (0 : ℝ) 1, cross t = t * C :=
    eq_time_mul_of_hasDerivAt hzero hderivZero hderiv hcont
  have hone : cross 1 = C := by
    simpa using hcrossEq 1 (by constructor <;> norm_num)
  have hendpointVariation : HasDerivAt
      (fun s : ℝ ↦ (Φ (p, u + s • w) 1).1) (W 1).1 0 := by
    have hs := (hvariation 1 (by norm_num)).hasFDerivAt.fst.hasDerivAt
    simpa [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using hs
  have hinit : ContDiff ℝ 1 (fun v : E ↦ (p, v)) :=
    (contDiff_const (𝕜 := ℝ) (n := 1) (c := p)).prodMk contDiff_id
  have hendpointSmooth : ContDiff ℝ 1 (fun v : E ↦ (Φ (p, v) 1).1) := by
    simpa only [Function.comp_apply] using (hΦsmooth.comp hinit).fst
  have huv : HasDerivAt (fun s : ℝ ↦ u + s • w) w 0 := by
    simpa [add_comm] using
      ((hasDerivAt_id' (0 : ℝ)).smul_const w |>.add_const u)
  have hendpointAt : HasFDerivAt (fun v : E ↦ (Φ (p, v) 1).1)
      (fderiv ℝ (fun v : E ↦ (Φ (p, v) 1).1) u) u :=
    (hendpointSmooth.differentiable one_ne_zero u).hasFDerivAt
  have hendpointAt' : HasFDerivAt (fun v : E ↦ (Φ (p, v) 1).1)
      (fderiv ℝ (fun v : E ↦ (Φ (p, v) 1).1) u) (u + (0 : ℝ) • w) := by
    simpa using hendpointAt
  have hchain : HasDerivAt (fun s : ℝ ↦ (Φ (p, u + s • w) 1).1)
      (fderiv ℝ (fun v : E ↦ (Φ (p, v) 1).1) u w) 0 := by
    change HasDerivAt
      ((fun v : E ↦ (Φ (p, v) 1).1) ∘ (fun s : ℝ ↦ u + s • w))
      (fderiv ℝ (fun v : E ↦ (Φ (p, v) 1).1) u w) 0
    exact hendpointAt'.comp_hasDerivAt 0 huv
  have hfderiv : fderiv ℝ (fun v : E ↦ (Φ (p, v) 1).1) u w = (W 1).1 :=
    hchain.unique hendpointVariation
  dsimp only [cross, C] at hone
  rw [← hfderiv] at hone
  exact hone

/-- Connector energy can equally be read as half the squared norm of the
terminal velocity. -/
theorem twoPointConnectorEnergy_eq_half_terminal_speed_sq
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    (G : E × E → E × E) (Φ : (E × E) → ℝ → E × E)
    (R : OpenPartialHomeomorph (E × E) (E × E))
    (hG : ContDiff ℝ 1 G) (hGcompact : HasCompactSupport G)
    (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ : ℝ ↦ G))
    (hR : ∀ s, R s = (s.1, (Φ s 1).1))
    (hactual : ∀ s ∈ R.source, ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ s t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ s t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ s t) ∧
        G =ᶠ[𝓝 (Φ s t)]
          (fun r ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) r))
    (hframe : ∀ s ∈ R.source, ∀ t ∈ Icc (-1 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 ((extChartAt I x₀).symm (Φ s t).1)]
          (trivializationAt E TM x₀).localFrame b j)
    {p q : E} (hpq : (p, q) ∈ R.target) :
    twoPointConnectorEnergy (I := I) (M := M) x₀ b R p q =
      (1 / 2 : ℝ) *
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (Φ (R.symm (p, q)) 1).2 ((extChartAt I x₀).symm q)‖ ^ 2 := by
  let s : E × E := R.symm (p, q)
  let u : E := s.2
  have hsSource : s ∈ R.source := R.map_target hpq
  have hright := R.right_inv hpq
  rw [hR] at hright
  have hsp : s.1 = p := congrArg Prod.fst hright
  have hsq : (Φ s 1).1 = q := congrArg Prod.snd hright
  have hsPair : s = (p, u) := by
    apply Prod.ext
    · exact hsp
    · rfl
  have hpu : (p, u) ∈ R.source := hsPair ▸ hsSource
  obtain ⟨_W, _hWzero, _hWposition, _hvariation, _hpair, hspeed⟩ :=
    exists_twoPoint_variation_covariant_pairing
      (I := I) (M := M) cov x₀ b hmetric G Φ R.source hG hGcompact
        hΦzero hΦcurve R.open_source hactual hframe hpu 0
  have hspeed1 := hspeed 1 (by constructor <;> norm_num)
  have hspeedPair : coordinateInner (I := I) (M := M) x₀ b q
      (Φ (p, u) 1).2 (Φ (p, u) 1).2 =
      coordinateInner (I := I) (M := M) x₀ b p u u := by
    have hsq' := hsq
    rw [hsPair] at hsq'
    rw [hsq'] at hspeed1
    exact hspeed1
  have hspeed1' : coordinateInner (I := I) (M := M) x₀ b q
      (Φ s 1).2 (Φ s 1).2 =
      coordinateInner (I := I) (M := M) x₀ b p s.2 s.2 := by
    calc
      coordinateInner (I := I) (M := M) x₀ b q
          (Φ s 1).2 (Φ s 1).2 =
        coordinateInner (I := I) (M := M) x₀ b q
          (Φ (p, u) 1).2 (Φ (p, u) 1).2 := by rw [hsPair]
      _ = coordinateInner (I := I) (M := M) x₀ b p u u := hspeedPair
      _ = coordinateInner (I := I) (M := M) x₀ b p s.2 s.2 := by rw [hsPair]
  change (1 / 2 : ℝ) * coordinateInner (I := I) (M := M) x₀ b p s.2 s.2 = _
  rw [← hspeed1']
  simp only [coordinateInner, real_inner_self_eq_norm_sq]
  simp only [s]

/-- The two-point connector energy is `C¹` in its terminal coordinate, and
its differential is pairing with the terminal velocity of the connector.
This is the moving-base endpoint first-variation formula needed for uniform
corner elimination. -/
theorem twoPointConnectorEnergy_contDiffAt_and_fderiv_apply
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent) (htorsion : cov.torsion = 0)
    (G : E × E → E × E) (Φ : (E × E) → ℝ → E × E)
    (R : OpenPartialHomeomorph (E × E) (E × E))
    (hG : ContDiff ℝ 1 G) (hGcompact : HasCompactSupport G)
    (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ : ℝ ↦ G))
    (hΦsmooth : ContDiff ℝ 1 (fun q ↦ Φ q 1))
    (hR : ∀ s, R s = (s.1, (Φ s 1).1))
    (hinverseSmooth : ∀ y ∈ R.target, ContDiffAt ℝ 1 R.symm y)
    (hactual : ∀ s ∈ R.source, ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ s t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ s t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ s t) ∧
        G =ᶠ[𝓝 (Φ s t)]
          (fun r ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) r))
    (hframe : ∀ s ∈ R.source, ∀ t ∈ Icc (-1 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 ((extChartAt I x₀).symm (Φ s t).1)]
          (trivializationAt E TM x₀).localFrame b j)
    {p q : E} (hpq : (p, q) ∈ R.target) :
    ContDiffAt ℝ 1
        (twoPointConnectorEnergy (I := I) (M := M) x₀ b R p) q ∧
      ∀ w : E,
        fderiv ℝ
            (twoPointConnectorEnergy (I := I) (M := M) x₀ b R p) q w =
          coordinateInner (I := I) (M := M) x₀ b q
            (Φ (R.symm (p, q)) 1).2 w := by
  let s : E × E := R.symm (p, q)
  let u : E := s.2
  let V : Set E := {y | (p, y) ∈ R.target}
  let ψ : E → E := fun y ↦ (R.symm (p, y)).2
  let F : E → E := fun v ↦ (Φ (p, v) 1).1
  let L : E →L[ℝ] TM ((extChartAt I x₀).symm p) :=
    (IntrinsicAcceleration.coordinateFrameLinear
      (I := I) (M := M) x₀ b ((extChartAt I x₀).symm p)).toContinuousLinearMap
  have hsSource : s ∈ R.source := R.map_target hpq
  have hright := R.right_inv hpq
  rw [hR] at hright
  have hsp : s.1 = p := congrArg Prod.fst hright
  have hsq : (Φ s 1).1 = q := congrArg Prod.snd hright
  have hsPair : s = (p, u) := by
    apply Prod.ext
    · exact hsp
    · rfl
  have hpu : (p, u) ∈ R.source := hsPair ▸ hsSource
  have hVopen : IsOpen V := by
    exact R.open_target.preimage (continuous_const.prodMk continuous_id)
  have hqV : q ∈ V := hpq
  have hψon : ContDiffOn ℝ 1 ψ V := by
    intro y hy
    have hι : ContDiffAt ℝ 1 (fun z : E ↦ (p, z)) y :=
      contDiffAt_const.prodMk contDiffAt_id
    have hraw := (hinverseSmooth (p, y) hy).comp y hι |>.snd
    simpa only [ψ, Function.comp_apply] using hraw.contDiffWithinAt
  have hFsmooth : ContDiff ℝ 1 F := by
    have hι : ContDiff ℝ 1 (fun v : E ↦ (p, v)) :=
      (contDiff_const (𝕜 := ℝ) (n := 1) (c := p)).prodMk contDiff_id
    simpa only [F, Function.comp_apply] using (hΦsmooth.comp hι).fst
  have hrightF : ∀ y ∈ V, F (ψ y) = y := by
    intro y hy
    have hr := R.right_inv hy
    rw [hR] at hr
    have hfirst : (R.symm (p, y)).1 = p := congrArg Prod.fst hr
    have hsecond : (Φ (R.symm (p, y)) 1).1 = y := congrArg Prod.snd hr
    have hstate : R.symm (p, y) = (p, ψ y) := by
      apply Prod.ext
      · exact hfirst
      · rfl
    simpa only [F, ← hstate] using hsecond
  have hψq : ψ q = u := by rfl
  have hinverse : (fderiv ℝ F u).comp (fderiv ℝ ψ q) =
      ContinuousLinearMap.id ℝ E := by
    simpa only [hψq] using fderiv_comp_fderiv_of_open_rightInverse
      hFsmooth hVopen hψon hrightF hqV
  have hψat : HasFDerivAt ψ (fderiv ℝ ψ q) q :=
    (hψon.contDiffAt (hVopen.mem_nhds hqV)).differentiableAt one_ne_zero
      |>.hasFDerivAt
  have hLψ : HasFDerivAt (fun y ↦ L (ψ y))
      (L.comp (fderiv ℝ ψ q)) q := L.hasFDerivAt.comp q hψat
  have hLapply (v : E) : L v =
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v
        ((extChartAt I x₀).symm p) := rfl
  have henergyEq :
      twoPointConnectorEnergy (I := I) (M := M) x₀ b R p =
        (fun y ↦ (1 / 2 : ℝ) * ‖L (ψ y)‖ ^ 2) := by
    funext y
    simp only [twoPointConnectorEnergy, coordinateInner, ψ, hLapply,
      real_inner_self_eq_norm_sq]
  have henergy : HasFDerivAt
      (twoPointConnectorEnergy (I := I) (M := M) x₀ b R p)
      ((1 / 2 : ℝ) •
        (2 • (innerSL ℝ (L (ψ q))).comp (L.comp (fderiv ℝ ψ q)))) q := by
    rw [henergyEq]
    exact hLψ.norm_sq.const_mul (1 / 2 : ℝ)
  have hψcont : ContDiffAt ℝ 1 ψ q :=
    hψon.contDiffAt (hVopen.mem_nhds hqV)
  have hLψcont : ContDiffAt ℝ 1 (fun y ↦ L (ψ y)) q :=
    L.contDiff.comp_contDiffAt q hψcont
  have henergyCont : ContDiffAt ℝ 1
      (fun y ↦ (1 / 2 : ℝ) * ‖L (ψ y)‖ ^ 2) q := by
    simpa [smul_eq_mul] using
      (hLψcont.norm_sq ℝ).const_smul (1 / 2 : ℝ)
  refine ⟨henergyEq.symm ▸ henergyCont, ?_⟩
  intro w
  rw [henergy.fderiv]
  have hgauss := twoPoint_endpoint_gauss_identity
    (I := I) (M := M) cov x₀ b hmetric htorsion G Φ R.source hG hGcompact
      hΦzero hΦcurve hΦsmooth R.open_source hactual hframe hpu
      (fderiv ℝ ψ q w)
  have hinverseW : fderiv ℝ F u (fderiv ℝ ψ q w) = w := by
    have h := congrArg (fun A : E →L[ℝ] E ↦ A w) hinverse
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using h
  have hsState : (p, u) = s := hsPair.symm
  have hendpoint : (Φ (p, u) 1).1 = q := by
    simpa only [hsState] using hsq
  have hterminal : (Φ (p, u) 1).2 = (Φ s 1).2 := by rw [hsState]
  rw [hinverseW, hendpoint] at hgauss
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, one_div, hψq]
  ring_nf
  change coordinateInner (I := I) (M := M) x₀ b p u
      (fderiv ℝ ψ q w) = _
  rw [← hgauss]
  simp only [s] at hterminal
  simpa only [hterminal]

end LocalGeodesicData

end BonnetMyersEntry
