/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.NormalNeighborhood
import LeanPool.PoincareGeometry.BonnetMyers.ChartGluing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# Local Gauss-lemma identities

This module begins the metric part of the normal-neighbourhood argument.  It
combines the actual coordinate geodesic equation, metric compatibility, and
the transverse variation field constructed by the localized flow.  The first
result is the differentiated radial--variation cross term.  It is a genuine
geometric identity, but not yet the integrated Gauss lemma or a minimizing
statement.
-/

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology BigOperators

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace LocalGeodesicData

variable [RiemannianBundle (TangentSpace I : M → Type u)]

section
omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [RiemannianBundle (TangentSpace I : M → Type u)] in
/-- On the chart source, the local tangent frame is the pullback through the
extended chart of the corresponding constant model-space vector field. -/
lemma localFrame_eq_mpullback_extChartAt_const
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (j : Fin (Module.finrank ℝ E)) {y : M}
    (hy : y ∈ (extChartAt I x₀).source) :
    (trivializationAt E TM x₀).localFrame b j y =
      VectorField.mpullback I 𝓘(ℝ, E) (extChartAt I x₀)
        (fun q : E ↦ (b j : TangentSpace 𝓘(ℝ, E) q)) y := by
  let C : (q : E) → TangentSpace 𝓘(ℝ, E) q := fun _ ↦ b j
  change (trivializationAt E TM x₀).localFrame b j y =
    VectorField.mpullback I 𝓘(ℝ, E) (extChartAt I x₀) C y
  have hyb : y ∈ (trivializationAt E TM x₀).baseSet := by simpa using hy
  rw [(trivializationAt E TM x₀).localFrame_apply_of_mem_baseSet b hyb]
  rw [Bundle.Trivialization.basisAt]
  simp only [Module.Basis.coe_map, Function.comp_apply]
  rw [(trivializationAt E TM x₀).linearEquivAt_symm_apply y hyb]
  rw [← Bundle.Trivialization.symmL_apply (R := ℝ)
    (e := trivializationAt E TM x₀) hyb (b j)]
  rw [TangentBundle.symmL_trivializationAt (by simpa using hy)]
  rw [VectorField.mpullback_apply]
  have hinv : (mfderiv% (extChartAt I x₀) y).inverse =
      mfderiv[range I] (extChartAt I x₀).symm (extChartAt I x₀ y) := by
    apply ContinuousLinearMap.inverse_eq
    · exact mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' hy
    · exact mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy
  rw [hinv]
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)] in
/-- Coordinate vector fields commute on the source of their defining chart. -/
lemma mlieBracket_localFrame_eq_zero
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (j k : Fin (Module.finrank ℝ E)) {y : M}
    (hy : y ∈ (extChartAt I x₀).source) :
    VectorField.mlieBracket I
      ((trivializationAt E TM x₀).localFrame b j)
      ((trivializationAt E TM x₀).localFrame b k) y = 0 := by
  let Cj : (q : E) → TangentSpace 𝓘(ℝ, E) q := fun _ ↦ b j
  let Ck : (q : E) → TangentSpace 𝓘(ℝ, E) q := fun _ ↦ b k
  let Pj := VectorField.mpullback I 𝓘(ℝ, E) (extChartAt I x₀) Cj
  let Pk := VectorField.mpullback I 𝓘(ℝ, E) (extChartAt I x₀) Ck
  have hje : (trivializationAt E TM x₀).localFrame b j =ᶠ[𝓝 y] Pj := by
    filter_upwards [(isOpen_extChartAt_source x₀).mem_nhds hy] with q hq
    exact localFrame_eq_mpullback_extChartAt_const
      (I := I) (M := M) (E := E) x₀ b j hq
  have hke : (trivializationAt E TM x₀).localFrame b k =ᶠ[𝓝 y] Pk := by
    filter_upwards [(isOpen_extChartAt_source x₀).mem_nhds hy] with q hq
    exact localFrame_eq_mpullback_extChartAt_const
      (I := I) (M := M) (E := E) x₀ b k hq
  rw [hje.mlieBracket_vectorField_eq hke]
  have hCj : MDiffAt (T% Cj) (extChartAt I x₀ y) := by
    have h : CMDiffAt 1 (T% Cj) (extChartAt I x₀ y) :=
      (contMDiffAt_vectorSpace_iff_contDiffAt (n := (1 : ℕ∞))).2 (by
        simpa [Cj] using (contDiffAt_const (x := extChartAt I x₀ y) (c := b j) :
          ContDiffAt ℝ 1 (fun _ : E ↦ b j) (extChartAt I x₀ y)))
    exact h.mdifferentiableAt one_ne_zero
  have hCk : MDiffAt (T% Ck) (extChartAt I x₀ y) := by
    have h : CMDiffAt 1 (T% Ck) (extChartAt I x₀ y) :=
      (contMDiffAt_vectorSpace_iff_contDiffAt (n := (1 : ℕ∞))).2 (by
        simpa [Ck] using (contDiffAt_const (x := extChartAt I x₀ y) (c := b k) :
          ContDiffAt ℝ 1 (fun _ : E ↦ b k) (extChartAt I x₀ y)))
    exact h.mdifferentiableAt one_ne_zero
  have hmin : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : ENat.LEInfty (2 : ℕ∞ω)).out
  have : ENat.LEInfty (minSmoothness ℝ 2) := ⟨hmin⟩
  have hyc : y ∈ (chartAt H x₀).source := by
    simpa only [← extChartAt_source (I := I)] using hy
  have hbr := VectorField.mpullback_mlieBracket
    (I := I) (I' := 𝓘(ℝ, E)) (f := extChartAt I x₀)
    (V := Cj) (W := Ck) (x₀ := y) hCj hCk
    (n := ∞) (contMDiffAt_extChartAt' hyc) hmin
  have hCbr : VectorField.mlieBracket 𝓘(ℝ, E) Cj Ck
      (extChartAt I x₀ y) = 0 := by
    rw [← VectorField.mlieBracketWithin_univ,
      VectorField.mlieBracketWithin_eq_lieBracketWithin]
    simp [VectorField.lieBracketWithin, Cj, Ck]
  rw [VectorField.mpullback_apply, hCbr, map_zero] at hbr
  exact hbr.symm

end

omit [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)] in
/-- Torsion-freeness makes the two lower connection-coefficient indices
symmetric wherever the smooth global extensions have the coordinate-frame
germs. -/
theorem connectionCoefficient_symm_of_torsion_eq_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {y : M} (hy : y ∈ (extChartAt I x₀).source)
    (htorsion : cov.torsion = 0)
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[𝓝 y]
        (trivializationAt E TM x₀).localFrame b j) :
    ∀ i j k : Fin (Module.finrank ℝ E),
      connectionCoefficient (I := I) (M := M) (E := E) cov x₀ b i j k y =
        connectionCoefficient (I := I) (M := M) (E := E) cov x₀ b i k j y := by
  intro i j k
  let Sj := smoothFrame (I := I) (M := M) (E := E) x₀ b j
  let Sk := smoothFrame (I := I) (M := M) (E := E) x₀ b k
  have hSj : MDiffAt (T% Sj) y := by
    have hs : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun z ↦ TotalSpace.mk' E (E := TM) z (Sj z)) := by
      simpa [Sj, smoothFrame] using
        CovariantDerivative.smoothExtend_contMDiff_two
          (I := I) (F := E) (V := TM) x₀
            ((trivializationAt E TM x₀).localFrame b j x₀)
    exact (hs y).mdifferentiableAt (by norm_num)
  have hSk : MDiffAt (T% Sk) y := by
    have hs : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun z ↦ TotalSpace.mk' E (E := TM) z (Sk z)) := by
      simpa [Sk, smoothFrame] using
        CovariantDerivative.smoothExtend_contMDiff_two
          (I := I) (F := E) (V := TM) x₀
            ((trivializationAt E TM x₀).localFrame b k x₀)
    exact (hs y).mdifferentiableAt (by norm_num)
  have htor : cov Sj y (Sk y) - cov Sk y (Sj y) =
      VectorField.mlieBracket I Sk Sj y := by
    exact (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htorsion hSk hSj
  have hbr : VectorField.mlieBracket I Sk Sj y = 0 := by
    rw [(hframe k).mlieBracket_vectorField_eq (hframe j)]
    exact mlieBracket_localFrame_eq_zero
      (I := I) (M := M) (E := E) x₀ b k j hy
  rw [hbr] at htor
  have hcov : cov Sj y (Sk y) = cov Sk y (Sj y) := sub_eq_zero.mp htor
  simp [connectionCoefficient, Sj, Sk, hcov]

/-- Symmetry of the two lower connection-coefficient indices makes the
coordinate parallel operator symmetric in the field and curve directions. -/
theorem coordinateParallelOperator_apply_comm_of_connectionCoefficient
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (z u w : E)
    (hsymm : ∀ i j k : Fin (Module.finrank ℝ E),
      connectionCoefficient (I := I) (M := M) (E := E) cov x₀ b i j k
          ((extChartAt I x₀).symm z) =
        connectionCoefficient (I := I) (M := M) (E := E) cov x₀ b i k j
          ((extChartAt I x₀).symm z)) :
    coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b z u w =
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b z w u := by
  rw [coordinateParallelOperator_apply, coordinateParallelOperator_apply]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ j, ∑ k,
        ((b.repr w j) * (b.repr u k) *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b i j k ((extChartAt I x₀).symm z)) • b i) =
      ∑ j, ∑ k,
        ((b.repr w j) * (b.repr u k) *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b i k j ((extChartAt I x₀).symm z)) • b i := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        rw [hsymm i j k]
    _ = ∑ j, ∑ k,
        ((b.repr u j) * (b.repr w k) *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b i j k ((extChartAt I x₀).symm z)) • b i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      ring

/-- Torsion-freeness supplies the coordinate parallel-operator symmetry at
every chart point where the canonical smooth-frame extensions have the local
coordinate-frame germs. -/
theorem coordinateParallelOperator_apply_comm_of_torsion_eq_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {z u w : E} (hz : z ∈ (extChartAt I x₀).target)
    (htorsion : cov.torsion = 0)
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
        𝓝 ((extChartAt I x₀).symm z)]
        (trivializationAt E TM x₀).localFrame b j) :
    coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b z u w =
      coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b z w u := by
  apply coordinateParallelOperator_apply_comm_of_connectionCoefficient
  exact connectionCoefficient_symm_of_torsion_eq_zero
    (I := I) (M := M) (E := E) cov x₀ b
      ((extChartAt I x₀).map_target hz) htorsion hframe

/-- Along an actual coordinate geodesic, the derivative of the inner product
between its velocity and a transverse variation field is the inner product
with the direct covariant derivative of that variation field.  The geodesic
acceleration term vanishes by the coordinate ODE.

This is the differential cross-term identity used in the Gauss lemma; the
remaining step is to identify and integrate the direct covariant derivative
coming from the two-parameter geodesic variation. -/
theorem radial_variation_inner_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {W : ℝ → E × E} {t : ℝ}
    (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hWposition : HasDerivAt (fun s ↦ (W s).1) (W t).2 t)
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
        𝓝 (LocalChartSecondOrderSolution.curve sol t)]
        (trivializationAt E TM x₀).localFrame b j) :
    HasDerivAt
      (fun s ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (W s).1 (LocalChartSecondOrderSolution.curve sol s)))
      (inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          ((W t).2 + coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b
            (extChartAt I x₀ (LocalChartSecondOrderSolution.curve sol t))
            (sol.velocity t) (W t).1)
          (LocalChartSecondOrderSolution.curve sol t))) t := by
  have hγ := curve_derivative_velocity
    (I := I) (M := M) (E := E) (H := H) cov x₀ b sol ht
  have hzero :
      deriv sol.velocity t + coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ b
        (extChartAt I x₀ (LocalChartSecondOrderSolution.curve sol t))
        (sol.velocity t) (sol.velocity t) = 0 := by
    have hacc := local_solution_coordinateCovariantAcceleration_eq_zero
      (I := I) (M := M) (E := E) (H := H)
      (F := coordinateAcceleration cov x₀ b)
      (cov := cov) (x₀ := x₀) (b := b) sol ht
    have hcurveeq := LocalChartSecondOrderSolution.curve_eq_chart sol ht
    rw [coordinateCovariantAcceleration] at hacc
    rw [← hcurveeq] at hacc
    simpa [coordinateParallelOperator_apply, coordinateConnectionTerm,
      Finset.sum_smul] using hacc
  have hvelocity : HasDerivAt sol.velocity (deriv sol.velocity t) t := by
    rw [(sol.velocity_hasDeriv t ht).deriv]
    exact sol.velocity_hasDeriv t ht
  have hinner := coordinateFrameCombination_inner_hasDerivAt_variable
    (I := I) (M := M) (E := E) (H := H) cov x₀ b
    (u := sol.velocity t) (w := sol.velocity) (v := fun s ↦ (W s).1)
    (dw := deriv sol.velocity t) (dv := (W t).2)
    (γ := LocalChartSecondOrderSolution.curve sol) (t := t)
    (hγ := hγ) (hγ' := by
      change (1 : ℝ) • coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) b (sol.velocity t)
          (LocalChartSecondOrderSolution.curve sol t) = _
      simp)
    (hy := by
      rw [← extChartAt_source (I := I) x₀]
      change (extChartAt I x₀).symm (sol.coordinate t) ∈
        (extChartAt I x₀).source
      exact (extChartAt I x₀).map_target (sol.coordinate_mem_target t ht))
    hmetric hframe hvelocity hWposition
  convert hinner using 1
  rw [hzero]
  simp [coordinateFrameCombination]

/-- The radial--variation cross term starts at zero, and its derivative at
the centre is the inner product of the two initial coordinate directions.
This supplies the exact initial data for the later integration step in the
Gauss lemma. -/
theorem radial_variation_inner_initial
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ w : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {W : ℝ → E × E} (hWzero : W 0 = (0, w))
    (hWposition : HasDerivAt (fun s ↦ (W s).1) (W 0).2 0)
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
        𝓝 (LocalChartSecondOrderSolution.curve sol 0)]
        (trivializationAt E TM x₀).localFrame b j) :
    let cross : ℝ → ℝ := fun s ↦ inner ℝ
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s))
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (W s).1 (LocalChartSecondOrderSolution.curve sol s))
    cross 0 = 0 ∧
      HasDerivAt cross
        (inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u₀ x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)) 0 := by
  let cross : ℝ → ℝ := fun s ↦ inner ℝ
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s))
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (W s).1 (LocalChartSecondOrderSolution.curve sol s))
  have ht : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [sol.radius_pos]
  have hcross := radial_variation_inner_hasDerivAt
    (I := I) (M := M) (E := E) (H := H) cov x₀ b sol hmetric ht
      hWposition hframe
  constructor
  · dsimp [cross]
    rw [hWzero]
    simp [coordinateFrameCombination]
  · change HasDerivAt cross _ 0
    rw [sol.velocity_initial, hWzero] at hcross
    have hPzero : coordinateParallelOperator (I := I) (M := M) (E := E)
      cov x₀ b (extChartAt I x₀ (LocalChartSecondOrderSolution.curve sol 0))
          u₀ 0 = 0 := by
      simp [coordinateParallelOperator_apply]
    rw [hPzero, add_zero, LocalChartSecondOrderSolution.curve_initial] at hcross
    exact hcross

/-- If the coordinate frame has the canonical smooth germs all along the
unit time interval, metric compatibility and the geodesic equation make the
squared speed constant on that whole interval. -/
theorem coordinate_geodesic_speed_inner_eq_initial_of_frame
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hradius : 1 < sol.radius)
    (hframe : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 (LocalChartSecondOrderSolution.curve sol t)]
          (trivializationAt E TM x₀).localFrame b j) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 0) (LocalChartSecondOrderSolution.curve sol 0))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 0) (LocalChartSecondOrderSolution.curve sol 0)) := by
  let speed : ℝ → ℝ := fun s ↦ inner ℝ
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s))
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s))
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt speed 0 t := by
    intro t ht
    have htRadius : t ∈ Ioo (-sol.radius) sol.radius := by
      constructor <;> linarith [ht.1, ht.2, hradius]
    simpa [speed] using local_speed_deriv
      (I := I) (M := M) (E := E) (H := H) cov x₀ b sol htRadius hmetric
        (hframe t ht)
  have hcont : ContinuousOn speed (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun t ht ↦
    (hderiv t ⟨ht.1, le_of_lt ht.2⟩).hasDerivWithinAt)
  intro t ht
  simpa [speed] using hconst t ht

/-- The derivative, in a transverse state parameter, of the squared speed is
twice the metric pairing with the corresponding coordinate covariant
derivative.  This is the parameter-direction counterpart of the
time-direction energy identity. -/
theorem coordinate_flow_state_speed_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {Q : ℝ → E × E} {W : E × E}
    (hQ : HasDerivAt Q W 0)
    (htarget : (Q 0).1 ∈ (extChartAt I x₀).target)
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
        𝓝 ((extChartAt I x₀).symm (Q 0).1)]
        (trivializationAt E TM x₀).localFrame b j) :
    HasDerivAt
      (fun s ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (Q s).2 ((extChartAt I x₀).symm (Q s).1))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (Q s).2 ((extChartAt I x₀).symm (Q s).1)))
      (inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (W.2 + coordinateParallelOperator (I := I) (M := M) (E := E)
              cov x₀ b (Q 0).1 W.1 (Q 0).2)
            ((extChartAt I x₀).symm (Q 0).1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (Q 0).2 ((extChartAt I x₀).symm (Q 0).1)) +
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (Q 0).2 ((extChartAt I x₀).symm (Q 0).1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (W.2 + coordinateParallelOperator (I := I) (M := M) (E := E)
              cov x₀ b (Q 0).1 W.1 (Q 0).2)
            ((extChartAt I x₀).symm (Q 0).1))) 0 := by
  have hpos : HasDerivAt (fun s ↦ (Q s).1) W.1 0 := by
    simpa [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using
        hQ.hasFDerivAt.fst.hasDerivAt
  have hvel : HasDerivAt (fun s ↦ (Q s).2) W.2 0 := by
    simpa [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using
        hQ.hasFDerivAt.snd.hasDerivAt
  have hγ := CurveConnection.hasMFDerivAt_inverseChartCurve_of_hasDerivAt
    (I := I) (M := M) (E := E) x₀ b (fun s ↦ (Q s).1) htarget hpos
  have hγ' : CurveConnection.timeTangentMap (I := I) (0 : ℝ)
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b W.1
        ((extChartAt I x₀).symm (Q 0).1)) 1 =
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b W.1
        ((extChartAt I x₀).symm (Q 0).1) := by
    rw [CurveConnection.timeTangentMap_eq_toSpanSingleton]
    change (1 : ℝ) • coordinateFrameCombination (I := I) (M := M)
      (x₀ := x₀) b W.1 ((extChartAt I x₀).symm (Q 0).1) = _
    exact one_smul ℝ _
  have hy : (extChartAt I x₀).symm (Q 0).1 ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact (extChartAt I x₀).map_target htarget
  have hright : extChartAt I x₀ ((extChartAt I x₀).symm (Q 0).1) = (Q 0).1 :=
    (extChartAt I x₀).right_inv htarget
  convert coordinateFrameCombination_inner_hasDerivAt_variable
    (I := I) (M := M) (E := E) (H := H) cov x₀ b
    (u := W.1) (w := fun s ↦ (Q s).2) (v := fun s ↦ (Q s).2)
    (dw := W.2) (dv := W.2)
    (γ := fun s ↦ (extChartAt I x₀).symm (Q s).1) (t := 0)
    hγ hγ' hy hmetric hframe hvel hvel using 1
  all_goals rw [hright]

/-- Every actual orbit in the common coordinate-flow region has the same
squared speed at time `t ∈ (-1,1)` as at its initial state. -/
theorem coordinate_geodesic_flow_speed_inner_eq_initial
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (G : E × E → E × E) (Φ : (E × E) → ℝ → E × E)
    (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G))
    {u : E}
    (hactual : ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ (extChartAt I x₀ x₀, u) t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ (extChartAt I x₀ x₀, u) t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b)
            (Φ (extChartAt I x₀ x₀, u) t))
    (hframe : ∀ t ∈ Icc (-1 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 ((extChartAt I x₀).symm
            (Φ (extChartAt I x₀ x₀, u) t).1)]
          (trivializationAt E TM x₀).localFrame b j) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (Φ (extChartAt I x₀ x₀, u) t).2
            ((extChartAt I x₀).symm
              (Φ (extChartAt I x₀ x₀, u) t).1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (Φ (extChartAt I x₀ x₀, u) t).2
            ((extChartAt I x₀).symm
              (Φ (extChartAt I x₀ x₀, u) t).1)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀) := by
  let z : E := extChartAt I x₀ x₀
  let sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u :=
    { coordinate := fun t ↦ (Φ (z, u) t).1
      velocity := fun t ↦ (Φ (z, u) t).2
      radius := 2
      radius_pos := by norm_num
      coordinate_initial := by
        have hzero := hΦzero (z, u)
        change (Φ (z, u) 0).1 = extChartAt I x₀ x₀
        simpa only [z] using congrArg Prod.fst hzero
      velocity_initial := by
        exact congrArg Prod.snd (hΦzero (z, u))
      coordinate_hasDeriv := by
        intro t ht
        have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hstate := hΦcurve (z, u) t
        change HasDerivAt (Φ (z, u)) (G (Φ (z, u) t)) t at hstate
        rw [(hactual t htI).2] at hstate
        simpa [secondOrderSystem, z] using hstate.hasFDerivAt.fst.hasDerivAt
      velocity_hasDeriv := by
        intro t ht
        have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hstate := hΦcurve (z, u) t
        change HasDerivAt (Φ (z, u)) (G (Φ (z, u) t)) t at hstate
        rw [(hactual t htI).2] at hstate
        simpa [secondOrderSystem, z] using hstate.hasFDerivAt.snd.hasDerivAt
      coordinate_mem_target := by
        intro t ht
        exact (hactual t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).1 }
  have hframeSol : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 (LocalChartSecondOrderSolution.curve sol t)]
          (trivializationAt E TM x₀).localFrame b j := by
    intro t ht j
    simpa [sol, z, LocalChartSecondOrderSolution.curve, Function.comp_def] using
      hframe t ⟨by linarith [ht.1], ht.2⟩ j
  intro t ht
  have hspeed := coordinate_geodesic_speed_inner_eq_initial_of_frame
    (I := I) (M := M) (E := E) (H := H) cov x₀ b sol hmetric
      (by norm_num) hframeSol t ht
  rw [sol.velocity_initial, LocalChartSecondOrderSolution.curve_initial] at hspeed
  convert hspeed using 1
  rfl

/-- Differentiating conservation of squared speed across the common family of
actual geodesics identifies the covariant transverse pairing at every positive
unit time with its initial pairing. -/
theorem radial_variation_covariant_pairing_eq_initial
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (G : E × E → E × E) (Φ : (E × E) → ℝ → E × E)
    (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G))
    (U : Set E) (hUopen : IsOpen U)
    {u : E} (hu : u ∈ U)
    (hactual : ∀ q ∈ U, ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ (extChartAt I x₀ x₀, q) t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ (extChartAt I x₀ x₀, q) t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b)
            (Φ (extChartAt I x₀ x₀, q) t))
    (hframe : ∀ q ∈ U, ∀ t ∈ Icc (-1 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          nhds ((extChartAt I x₀).symm
            (Φ (extChartAt I x₀ x₀, q) t).1)]
          (trivializationAt E TM x₀).localFrame b j)
    {w : E} {W : ℝ → E × E}
    (hWvariation : ∀ t, 0 ≤ t →
      HasDerivAt (fun s : ℝ ↦ Φ (extChartAt I x₀ x₀, u + s • w) t) (W t) 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (Φ (extChartAt I x₀ x₀, u) t).2
          ((extChartAt I x₀).symm
            (Φ (extChartAt I x₀ x₀, u) t).1))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          ((W t).2 + coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (Φ (extChartAt I x₀ x₀, u) t).1
            (W t).1 (Φ (extChartAt I x₀ x₀, u) t).2)
          ((extChartAt I x₀).symm
            (Φ (extChartAt I x₀ x₀, u) t).1)) =
      inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀) := by
  let z : E := extChartAt I x₀ x₀
  let Q : ℝ → E × E := fun s ↦ Φ (z, u + s • w) t
  have hQ : HasDerivAt Q (W t) 0 := by
    simpa only [Q, z] using hWvariation t (le_of_lt ht.1)
  have htime := coordinate_flow_state_speed_hasDerivAt
    (I := I) (M := M) (E := E) (H := H) cov x₀ b hmetric hQ
      (by
        simpa only [Q, z, zero_smul, add_zero] using
          (hactual u hu t ⟨by linarith [ht.1], by linarith [ht.2]⟩).1)
      (by
        intro j
        simpa only [Q, z, zero_smul, add_zero] using
          hframe u hu t ⟨le_of_lt (by linarith [ht.1]), le_of_lt ht.2⟩ j)
  have hQzero : Q 0 = Φ (z, u) t := by simp [Q]
  rw [hQzero] at htime
  have htimeClean : HasDerivAt
      (fun s ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (Q s).2 ((extChartAt I x₀).symm (Q s).1))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (Q s).2 ((extChartAt I x₀).symm (Q s).1)))
      (inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            ((W t).2 + coordinateParallelOperator (I := I) (M := M) (E := E)
              cov x₀ b (Φ (extChartAt I x₀ x₀, u) t).1
              (W t).1 (Φ (extChartAt I x₀ x₀, u) t).2)
            ((extChartAt I x₀).symm
              (Φ (extChartAt I x₀ x₀, u) t).1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (Φ (extChartAt I x₀ x₀, u) t).2
            ((extChartAt I x₀).symm
              (Φ (extChartAt I x₀ x₀, u) t).1)) +
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (Φ (extChartAt I x₀ x₀, u) t).2
            ((extChartAt I x₀).symm
              (Φ (extChartAt I x₀ x₀, u) t).1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            ((W t).2 + coordinateParallelOperator (I := I) (M := M) (E := E)
              cov x₀ b (Φ (extChartAt I x₀ x₀, u) t).1
              (W t).1 (Φ (extChartAt I x₀ x₀, u) t).2)
            ((extChartAt I x₀).symm
              (Φ (extChartAt I x₀ x₀, u) t).1))) 0 := by
    simpa only [z] using htime
  let L : E →L[ℝ] TM x₀ :=
    (IntrinsicAcceleration.coordinateFrameLinear
      (I := I) (M := M) x₀ b x₀).toContinuousLinearMap
  have huv : HasDerivAt (fun s : ℝ ↦ u + s • w) w 0 := by
    simpa [add_comm] using
      ((hasDerivAt_id' (0 : ℝ)).smul_const w |>.add_const u)
  have hL : HasDerivAt (fun s : ℝ ↦ L (u + s • w)) (L w) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 huv
  have hinitial := hL.inner ℝ hL
  have hinitial' : HasDerivAt
      (fun s : ℝ ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (u + s • w) x₀)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (u + s • w) x₀))
      (inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀) +
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)) 0 := by
    simpa [L, IntrinsicAcceleration.coordinateFrameLinear_apply,
      IntrinsicAcceleration.coordinateFrameVector] using hinitial
  have htendsto : Tendsto (fun s : ℝ ↦ u + s • w) (nhds 0) (nhds u) :=
    by
      have hcont := huv.continuousAt
      change Tendsto (fun s : ℝ ↦ u + s • w) (nhds 0)
        (nhds (u + (0 : ℝ) • w)) at hcont
      simpa using hcont
  have hperturbU : ∀ᶠ s in nhds (0 : ℝ), u + s • w ∈ U :=
    htendsto.eventually (hUopen.mem_nhds hu)
  have hspeedEq :
      (fun s : ℝ ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (Q s).2 ((extChartAt I x₀).symm (Q s).1))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (Q s).2 ((extChartAt I x₀).symm (Q s).1))) =ᶠ[nhds (0 : ℝ)]
      (fun s : ℝ ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (u + s • w) x₀)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (u + s • w) x₀)) := by
    filter_upwards [hperturbU] with s hs
    simpa only [Q, z] using coordinate_geodesic_flow_speed_inner_eq_initial
      (I := I) (M := M) (E := E) (H := H) cov x₀ b hmetric G Φ hΦzero hΦcurve
        (hactual (u + s • w) hs) (hframe (u + s • w) hs) t
        ⟨by linarith [ht.1], le_of_lt ht.2⟩
  have htime' := htimeClean.congr_of_eventuallyEq hspeedEq.symm
  have hderivEq := hinitial'.unique htime'
  rw [real_inner_comm
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)] at hderivEq
  rw [real_inner_comm
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (Φ (extChartAt I x₀ x₀, u) t).2
      ((extChartAt I x₀).symm (Φ (extChartAt I x₀ x₀, u) t).1))
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      ((W t).2 + coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b (Φ (extChartAt I x₀ x₀, u) t).1
        (W t).1 (Φ (extChartAt I x₀ x₀, u) t).2)
      ((extChartAt I x₀).symm (Φ (extChartAt I x₀ x₀, u) t).1))] at hderivEq
  linarith


/-- Torsion symmetry converts the direct covariant transverse pairing into
the derivative appearing in the radial cross term. -/
theorem radial_variation_inner_hasDerivAt_initial_of_torsion
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (htorsion : cov.torsion = 0)
    {W : ℝ → E × E} {t C : ℝ}
    (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hWposition : HasDerivAt (fun s ↦ (W s).1) (W t).2 t)
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
        nhds (LocalChartSecondOrderSolution.curve sol t)]
        (trivializationAt E TM x₀).localFrame b j)
    (hpair : inner ℝ
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        ((W t).2 + coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b (extChartAt I x₀ (LocalChartSecondOrderSolution.curve sol t))
          (W t).1 (sol.velocity t))
        (LocalChartSecondOrderSolution.curve sol t)) = C) :
    HasDerivAt
      (fun s ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (W s).1 (LocalChartSecondOrderSolution.curve sol s))) C t := by
  have hcross := radial_variation_inner_hasDerivAt
    (I := I) (M := M) (E := E) (H := H) cov x₀ b sol hmetric ht
      hWposition hframe
  have hz : extChartAt I x₀ (LocalChartSecondOrderSolution.curve sol t) ∈
      (extChartAt I x₀).target := by
    rw [LocalChartSecondOrderSolution.curve_eq_chart sol ht]
    exact sol.coordinate_mem_target t ht
  have hsource : LocalChartSecondOrderSolution.curve sol t ∈
      (extChartAt I x₀).source := by
    change (extChartAt I x₀).symm (sol.coordinate t) ∈
      (extChartAt I x₀).source
    exact (extChartAt I x₀).map_target (sol.coordinate_mem_target t ht)
  have hframe' : ∀ j : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
        nhds ((extChartAt I x₀).symm
          (extChartAt I x₀ (LocalChartSecondOrderSolution.curve sol t)))]
        (trivializationAt E TM x₀).localFrame b j := by
    intro j
    rw [(extChartAt I x₀).left_inv hsource]
    exact hframe j
  have hcomm := coordinateParallelOperator_apply_comm_of_torsion_eq_zero
    (I := I) (M := M) (E := E) cov x₀ b hz htorsion hframe'
    (u := sol.velocity t) (w := (W t).1)
  rw [hcomm, hpair] at hcross
  exact hcross


/-- A scalar function with fixed derivative on the positive unit interval and
the corresponding initial derivative is exactly the associated linear function,
including both endpoints by continuity. -/
theorem eq_time_mul_of_hasDerivAt
    {cross : ℝ → ℝ} {C : ℝ}
    (hzero : cross 0 = 0)
    (hderivZero : HasDerivAt cross C 0)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt cross C t)
    (hcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt cross t) :
    ∀ t ∈ Icc (0 : ℝ) 1, cross t = t * C := by
  apply eq_of_has_deriv_right_eq (f' := fun _ ↦ C)
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | htpos
    · exact hderivZero.hasDerivWithinAt
    · exact (hderiv t ⟨htpos, ht.2⟩).hasDerivWithinAt
  · intro t ht
    simpa using ((hasDerivAt_id t).mul_const C).hasDerivWithinAt
  · intro t ht
    exact (hcont t ht).continuousWithinAt
  · fun_prop
  · simpa using hzero


/-- The common normal-flow neighbourhood supplies the preceding cross-term
identity for every small initial velocity and every transverse initial
direction.  The returned `W` is simultaneously the derivative of the full
position--velocity flow with respect to the initial velocity, has the Jacobi
initial data `(0,w)`, and satisfies the metric cross-term identity throughout
the open unit interval. -/
theorem exists_open_velocity_neighborhood_radial_variation_inner_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    let z := extChartAt I x₀ x₀
    ∃ Φ : (E × E) → ℝ → E × E, ∃ U : Set E,
      ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
      HasFDerivAt (fun u : E ↦ (Φ (z, u) 1).1)
        (ContinuousLinearMap.id ℝ E) 0 ∧
      (∀ t, Φ (z, 0) t = (z, 0)) ∧
      IsOpen U ∧ 0 ∈ U ∧
      ∀ u ∈ U, ∀ w : E,
        ∃ sol : LocalChartSecondOrderSolution I
          (coordinateAcceleration cov x₀ b) x₀ u,
        ∃ W : ℝ → E × E,
        sol.radius = 2 ∧
        (∀ t, sol.coordinate t = (Φ (z, u) t).1 ∧
          sol.velocity t = (Φ (z, u) t).2) ∧
        W 0 = (0, w) ∧
        (∀ t, 0 ≤ t →
          HasDerivAt (fun s : ℝ ↦ Φ (z, u + s • w) t) (W t) 0) ∧
        (fun s ↦ inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (W s).1 (LocalChartSecondOrderSolution.curve sol s))) 0 = 0 ∧
        HasDerivAt
          (fun s ↦ inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (W s).1 (LocalChartSecondOrderSolution.curve sol s)))
          (inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)) 0 ∧
        (∀ t ∈ Icc (-1 : ℝ) 1,
          HasDerivAt
            (fun s ↦ inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (W s).1 (LocalChartSecondOrderSolution.curve sol s)))
            (inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                ((W t).2 + coordinateParallelOperator
                  (I := I) (M := M) (E := E) cov x₀ b
                  (extChartAt I x₀ (LocalChartSecondOrderSolution.curve sol t))
                  (sol.velocity t) (W t).1)
                (LocalChartSecondOrderSolution.curve sol t))) t) ∧
        (cov.torsion = 0 → ∀ t ∈ Ioo (0 : ℝ) 1,
          HasDerivAt
            (fun s ↦ inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity s) (LocalChartSecondOrderSolution.curve sol s))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (W s).1 (LocalChartSecondOrderSolution.curve sol s)))
            (inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)) t) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) =
            inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)) := by
  let b := IntrinsicGeodesic.canonicalBasis (E := E)
  let z : E := extChartAt I x₀ x₀
  obtain ⟨G, Φ, U, hG, hGcompact, hΦzero, hΦcurve, hΦsmooth, hend, hfix,
    hUopen, hzeroU, hradial, hactual, hframe, hvariation⟩ :=
    exists_open_velocity_neighborhood_actual_firstVariation_smoothFrame
      (I := I) (M := M) (E := E) cov x₀
  refine ⟨Φ, U, hΦsmooth, hend, hfix, hUopen, hzeroU, ?_⟩
  intro u hu w
  obtain ⟨K, A, W, hA, hAeq, hAactual, hWzero, hWderiv, hWposition,
    hWvariation, hperturb⟩ := hvariation u hu w
  let sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u :=
    { coordinate := fun t ↦ (Φ (z, u) t).1
      velocity := fun t ↦ (Φ (z, u) t).2
      radius := 2
      radius_pos := by norm_num
      coordinate_initial := by
        have hzero := hΦzero (z, u)
        change (Φ (z, u) 0).1 = extChartAt I x₀ x₀
        simpa only [z] using congrArg Prod.fst hzero
      velocity_initial := by
        have hzero := hΦzero (z, u)
        exact congrArg Prod.snd hzero
      coordinate_hasDeriv := by
        intro t ht
        have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hstate := hΦcurve (z, u) t
        change HasDerivAt (Φ (z, u)) (G (Φ (z, u) t)) t at hstate
        rw [(hactual u hu t htI).2.1] at hstate
        simpa [secondOrderSystem, b, z] using hstate.hasFDerivAt.fst.hasDerivAt
      velocity_hasDeriv := by
        intro t ht
        have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hstate := hΦcurve (z, u) t
        change HasDerivAt (Φ (z, u)) (G (Φ (z, u) t)) t at hstate
        rw [(hactual u hu t htI).2.1] at hstate
        simpa [secondOrderSystem, b, z] using hstate.hasFDerivAt.snd.hasDerivAt
      coordinate_mem_target := by
        intro t ht
        exact (hactual u hu t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).1 }
  refine ⟨sol, W, rfl, ?_, hWzero, hWvariation, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact ⟨rfl, rfl⟩
  · have hframe0 : ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 (LocalChartSecondOrderSolution.curve sol 0)]
          (trivializationAt E TM x₀).localFrame b j := by
      intro j
      simpa [sol, LocalChartSecondOrderSolution.curve, Function.comp_def, b, z] using
        hframe u hu 0 (by constructor <;> norm_num) j
    exact (radial_variation_inner_initial
      (I := I) (M := M) (E := E) (H := H) cov x₀ b sol hmetric hWzero
        (hWposition 0 (by constructor <;> norm_num)) hframe0).1
  · have hframe0 : ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 (LocalChartSecondOrderSolution.curve sol 0)]
          (trivializationAt E TM x₀).localFrame b j := by
      intro j
      simpa [sol, LocalChartSecondOrderSolution.curve, Function.comp_def, b, z] using
        hframe u hu 0 (by constructor <;> norm_num) j
    exact (radial_variation_inner_initial
      (I := I) (M := M) (E := E) (H := H) cov x₀ b sol hmetric hWzero
        (hWposition 0 (by constructor <;> norm_num)) hframe0).2
  · intro t ht
    have htRadius : t ∈ Ioo (-sol.radius) sol.radius := by
      change t ∈ Ioo (-2 : ℝ) 2
      constructor <;> linarith [ht.1, ht.2]
    have hframe' : ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 (LocalChartSecondOrderSolution.curve sol t)]
          (trivializationAt E TM x₀).localFrame b j := by
      intro j
      simpa [sol, LocalChartSecondOrderSolution.curve, Function.comp_def, b, z] using
        hframe u hu t ht j
    exact radial_variation_inner_hasDerivAt
      (I := I) (M := M) (E := E) (H := H) cov x₀ b sol hmetric
        htRadius (hWposition t ⟨by linarith [ht.1], by linarith [ht.2]⟩) hframe'
  · intro htorsion t ht
    have htRadius : t ∈ Ioo (-sol.radius) sol.radius := by
      change t ∈ Ioo (-2 : ℝ) 2
      constructor <;> linarith [ht.1, ht.2]
    have hframe' : ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 (LocalChartSecondOrderSolution.curve sol t)]
          (trivializationAt E TM x₀).localFrame b j := by
      intro j
      simpa [sol, LocalChartSecondOrderSolution.curve, Function.comp_def, b, z] using
        hframe u hu t ⟨by linarith [ht.1], le_of_lt ht.2⟩ j
    have hpairFlow := radial_variation_covariant_pairing_eq_initial
      (I := I) (M := M) (E := E) (H := H) cov x₀ b hmetric
        G Φ hΦzero hΦcurve U hUopen hu
        (fun q hq s hs ↦ ⟨(hactual q hq s hs).1, (hactual q hq s hs).2.1⟩)
        hframe hWvariation ht
    have hpair : inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          ((W t).2 + coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (extChartAt I x₀ (LocalChartSecondOrderSolution.curve sol t))
            (W t).1 (sol.velocity t))
          (LocalChartSecondOrderSolution.curve sol t)) =
      inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀) := by
      have hcoord := LocalChartSecondOrderSolution.curve_eq_chart sol htRadius
      have hcurve : LocalChartSecondOrderSolution.curve sol t =
          (extChartAt I x₀).symm (Φ (extChartAt I x₀ x₀, u) t).1 := rfl
      rw [hcoord, hcurve]
      exact hpairFlow
    exact radial_variation_inner_hasDerivAt_initial_of_torsion
      (I := I) (M := M) (E := E) (H := H) cov x₀ b sol hmetric htorsion
        htRadius (hWposition t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        hframe' hpair
  · intro t ht
    have hspeed := coordinate_geodesic_flow_speed_inner_eq_initial
      (I := I) (M := M) (E := E) (H := H) cov x₀ b hmetric
        G Φ hΦzero hΦcurve
        (fun s hs ↦ ⟨(hactual u hu s hs).1, (hactual u hu s hs).2.1⟩)
        (hframe u hu) t ht
    change inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (Φ (z, u) t).2 ((extChartAt I x₀).symm (Φ (z, u) t).1))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (Φ (z, u) t).2 ((extChartAt I x₀).symm (Φ (z, u) t).1)) =
      inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
    simpa only [z] using hspeed

/-- On one common open normal-flow neighbourhood, the radial--transverse
cross term satisfies the integrated Gauss identity all the way to time one.
The same variation remains the derivative of the full geodesic flow with
respect to its initial velocity. -/
theorem exists_open_velocity_neighborhood_radial_variation_inner_eq
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (htorsion : cov.torsion = 0) :
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    let z := extChartAt I x₀ x₀
    ∃ Φ : (E × E) → ℝ → E × E, ∃ U : Set E,
      ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
      HasFDerivAt (fun u : E ↦ (Φ (z, u) 1).1)
        (ContinuousLinearMap.id ℝ E) 0 ∧
      (∀ t, Φ (z, 0) t = (z, 0)) ∧
      IsOpen U ∧ 0 ∈ U ∧
      ∀ u ∈ U, ∀ w : E,
        ∃ sol : LocalChartSecondOrderSolution I
          (coordinateAcceleration cov x₀ b) x₀ u,
        ∃ W : ℝ → E × E,
        sol.radius = 2 ∧
        (∀ t, sol.coordinate t = (Φ (z, u) t).1 ∧
          sol.velocity t = (Φ (z, u) t).2) ∧
        W 0 = (0, w) ∧
        (∀ t, 0 ≤ t →
          HasDerivAt (fun s : ℝ ↦ Φ (z, u + s • w) t) (W t) 0) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (W t).1 (LocalChartSecondOrderSolution.curve sol t)) =
            t * inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)) ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) =
            inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀) := by
  let b := IntrinsicGeodesic.canonicalBasis (E := E)
  let z : E := extChartAt I x₀ x₀
  obtain ⟨Φ, U, hΦsmooth, hend, hfix, hUopen, hzeroU, hall⟩ :=
    exists_open_velocity_neighborhood_radial_variation_inner_hasDerivAt
      (I := I) (M := M) (E := E) cov x₀ hmetric
  refine ⟨Φ, U, hΦsmooth, hend, hfix, hUopen, hzeroU, ?_⟩
  intro u hu w
  obtain ⟨sol, W, hradius, hflow, hWzero, hWvariation,
    hcrossZero, hcrossDerivZero, hcrossDynamic, hcrossFixed, hspeed⟩ := hall u hu w
  refine ⟨sol, W, hradius, hflow, hWzero, hWvariation, ?_, hspeed⟩
  let cross : ℝ → ℝ := fun t ↦ inner ℝ
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (W t).1 (LocalChartSecondOrderSolution.curve sol t))
  let C : ℝ := inner ℝ
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)
  have hzero : cross 0 = 0 := by simpa only [cross] using hcrossZero
  have hderivZero : HasDerivAt cross C 0 := by
    simpa only [cross, C] using hcrossDerivZero
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt cross C t := by
    simpa only [cross, C] using hcrossFixed htorsion
  have hcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt cross t := by
    intro t ht
    have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    exact (hcrossDynamic t ht').continuousAt
  simpa only [cross, C] using
    eq_time_mul_of_hasDerivAt hzero hderivZero hderiv hcont

/-- The metric identity and conservation of radial speed imply the basic
radial lower bound on an arbitrary endpoint variation. -/
theorem abs_inner_le_norm_mul_of_gauss
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (u w : X) (T V : Y)
    (hgauss : inner ℝ T V = inner ℝ u w)
    (hspeed : inner ℝ T T = inner ℝ u u) :
    |inner ℝ u w| ≤ ‖u‖ * ‖V‖ := by
  have hnorm : ‖T‖ = ‖u‖ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hspeed
    nlinarith [norm_nonneg T, norm_nonneg u]
  rw [← hgauss, ← hnorm]
  exact abs_real_inner_le_norm T V

/-- A one-dimensional integral form of the radial estimate.  The square-root
regularization avoids assuming that the norm is differentiable when the path
passes through the origin. -/
theorem radial_norm_le_integral_of_gauss
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (q q' : ℝ → X) (B : ℝ → ℝ)
    (hq : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt q (q' t) t)
    (hq0 : q 0 = 0)
    (hBint : IntegrableOn B (Icc (0 : ℝ) 1))
    (hBnonneg : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ B t)
    (hgauss : ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ (q t) (q' t)| ≤ ‖q t‖ * B t) :
    ‖q 1‖ ≤ ∫ t in (0 : ℝ)..1, B t := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let r : ℝ → ℝ := fun t ↦ Real.sqrt (‖q t‖ ^ 2 + δ ^ 2)
  let r' : ℝ → ℝ := fun t ↦ inner ℝ (q t) (q' t) / r t
  have hrDeriv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt r (r' t) t := by
    intro t ht
    have hqt := hq t ht
    have hsq := hqt.norm_sq
    have hsum : HasDerivAt (fun s ↦ ‖q s‖ ^ 2 + δ ^ 2)
        (2 * inner ℝ (q t) (q' t)) t := hsq.add_const (δ ^ 2)
    have hpos : 0 < ‖q t‖ ^ 2 + δ ^ 2 := by positivity
    have hsqrt := hsum.sqrt hpos.ne'
    simpa [r, r', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsqrt
  have hrCont : ContinuousOn r (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hrDeriv t ht).continuousAt.continuousWithinAt
  have hrBound : ∀ t ∈ Ioo (0 : ℝ) 1, r' t ≤ B t := by
    intro t ht
    have hBt := hBnonneg t ⟨ht.1.le, ht.2.le⟩
    have hrt : 0 < r t := by
      dsimp [r]
      positivity
    have hnorm_le : ‖q t‖ ≤ r t := by
      dsimp [r]
      rw [Real.le_sqrt (norm_nonneg _)
        (add_nonneg (sq_nonneg _) (sq_nonneg _))]
      nlinarith [sq_nonneg δ]
    calc
      r' t ≤ |inner ℝ (q t) (q' t)| / r t := by
        dsimp [r']
        exact div_le_div_of_nonneg_right (le_abs_self _) hrt.le
      _ ≤ (‖q t‖ * B t) / r t := by
        exact div_le_div_of_nonneg_right (hgauss t ⟨ht.1.le, ht.2.le⟩) hrt.le
      _ ≤ B t := by
        rw [div_le_iff₀ hrt]
        simpa [mul_comm] using mul_le_mul_of_nonneg_right hnorm_le hBt
  have hmain : r 1 - r 0 ≤ ∫ t in (0 : ℝ)..1, B t := by
    exact intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
      (by norm_num) hrCont
      (fun t ht ↦ (hrDeriv t ⟨ht.1.le, ht.2.le⟩).hasDerivWithinAt)
      hBint hrBound
  have hr0 : r 0 = δ := by
    simp [r, hq0, Real.sqrt_sq_eq_abs, abs_of_pos hδ]
  have hq1 : ‖q 1‖ ≤ r 1 := by
    dsimp [r]
    rw [Real.le_sqrt (norm_nonneg _)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    nlinarith [sq_nonneg δ]
  rw [hr0] at hmain
  linarith

/-- Extended-real integral form of the radial estimate for a `C¹` path.
Unlike the real-integral version, this theorem does not require a separate
integrability hypothesis; an infinite speed integral is handled directly. -/
theorem enorm_radial_norm_le_lintegral_of_gauss
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (q : ℝ → X) (B : ℝ → ℝ)
    (hq : ContDiffOn ℝ 1 q (Icc (0 : ℝ) 1))
    (hq0 : q 0 = 0)
    (hBnonneg : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ B t)
    (hgauss : ∀ t ∈ Ioo (0 : ℝ) 1,
      |inner ℝ (q t) (deriv q t)| ≤ ‖q t‖ * B t) :
    ENNReal.ofReal ‖q 1‖ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (B t) := by
  let L : ℝ≥0∞ := ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (B t)
  by_cases hL : L = (∞ : ℝ≥0∞)
  · change ENNReal.ofReal ‖q 1‖ ≤ L
    rw [hL]
    exact le_top
  apply (ENNReal.ofReal_le_iff_le_toReal hL).2
  apply le_of_forall_pos_le_add
  intro δ hδ
  let r : ℝ → ℝ := fun t ↦ Real.sqrt (‖q t‖ ^ 2 + δ ^ 2)
  let r' : ℝ → ℝ := fun t ↦ inner ℝ (q t) (deriv q t) / r t
  have hrSmooth : ContDiffOn ℝ 1 r (Icc (0 : ℝ) 1) := by
    intro t ht
    have hsum : ContDiffWithinAt ℝ 1
        (fun s ↦ ‖q s‖ ^ 2 + δ ^ 2) (Icc (0 : ℝ) 1) t :=
      (hq t ht).norm_sq ℝ |>.add contDiffWithinAt_const
    have hpos : 0 < ‖q t‖ ^ 2 + δ ^ 2 := by positivity
    exact hsum.sqrt hpos.ne'
  have hrDeriv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt r (r' t) t := by
    intro t ht
    have hqt : HasDerivAt q (deriv q t) t :=
      ((hq t ⟨ht.1.le, ht.2.le⟩).contDiffAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero |>.hasDerivAt
    have hsum : HasDerivAt (fun s ↦ ‖q s‖ ^ 2 + δ ^ 2)
        (2 * inner ℝ (q t) (deriv q t)) t := hqt.norm_sq.add_const (δ ^ 2)
    have hpos : 0 < ‖q t‖ ^ 2 + δ ^ 2 := by positivity
    have hsqrt := hsum.sqrt hpos.ne'
    simpa [r, r', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsqrt
  have hrBound : ∀ t ∈ Ioo (0 : ℝ) 1, |r' t| ≤ B t := by
    intro t ht
    have hBt := hBnonneg t ht
    have hrt : 0 < r t := by
      dsimp [r]
      positivity
    have hnorm_le : ‖q t‖ ≤ r t := by
      dsimp [r]
      rw [Real.le_sqrt (norm_nonneg _)
        (add_nonneg (sq_nonneg _) (sq_nonneg _))]
      nlinarith [sq_nonneg δ]
    calc
      |r' t| = |inner ℝ (q t) (deriv q t)| / r t := by
        simp [r', abs_div, abs_of_pos hrt]
      _ ≤ (‖q t‖ * B t) / r t := by
        exact div_le_div_of_nonneg_right (hgauss t ht) hrt.le
      _ ≤ B t := by
        rw [div_le_iff₀ hrt]
        simpa [mul_comm] using mul_le_mul_of_nonneg_right hnorm_le hBt
  have hdisp := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hrSmooth (by norm_num)
  have hdisp' : ‖r 1 - r 0‖ₑ ≤ L := by
    apply hdisp.trans
    rw [← restrict_Ioo_eq_restrict_Icc]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change ‖deriv r t‖ₑ ≤ ENNReal.ofReal (B t)
    have hdr : deriv r t = r' t := (hrDeriv t ht).deriv
    rw [hdr, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hrBound t ht)
  have hr0 : r 0 = δ := by
    simp [r, hq0, Real.sqrt_sq_eq_abs, abs_of_pos hδ]
  have hq1 : ‖q 1‖ ≤ r 1 := by
    dsimp [r]
    rw [Real.le_sqrt (norm_nonneg _)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    nlinarith [sq_nonneg δ]
  have hsubNonneg : 0 ≤ r 1 - r 0 := by
    rw [hr0]
    have hsqrtδ : δ ≤ r 1 := by
      dsimp [r]
      rw [Real.le_sqrt hδ.le (add_nonneg (sq_nonneg _) (sq_nonneg _))]
      nlinarith [sq_nonneg (‖q 1‖)]
    linarith
  have hsub : r 1 - r 0 ≤ L.toReal := by
    rw [Real.enorm_eq_ofReal hsubNonneg] at hdisp'
    simpa [ENNReal.toReal_ofReal hsubNonneg] using
      (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hL).2 hdisp'
  rw [hr0] at hsub
  linarith

/-- Directional local Gauss lemma for the time-one endpoint map.  The
derivative of the endpoint in an arbitrary initial-velocity direction pairs
with the terminal radial velocity exactly as that direction pairs with the
initial radial velocity at the centre. -/
theorem exists_open_velocity_neighborhood_endpoint_gauss_identity
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (htorsion : cov.torsion = 0) :
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    let z := extChartAt I x₀ x₀
    ∃ Φ : (E × E) → ℝ → E × E, ∃ U : Set E,
      IsOpen U ∧ 0 ∈ U ∧
      ContDiff ℝ 1 (fun u : E ↦ (Φ (z, u) 1).1) ∧
      HasFDerivAt (fun u : E ↦ (Φ (z, u) 1).1)
        (ContinuousLinearMap.id ℝ E) 0 ∧
      (Φ (z, 0) 1).1 = z ∧
      ∀ u ∈ U, ∀ w : E,
        ∃ sol : LocalChartSecondOrderSolution I
          (coordinateAcceleration cov x₀ b) x₀ u,
          sol.radius = 2 ∧
          sol.coordinate 1 = (Φ (z, u) 1).1 ∧
          sol.velocity 1 = (Φ (z, u) 1).2 ∧
          inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (fderiv ℝ (fun v : E ↦ (Φ (z, v) 1).1) u w)
                (LocalChartSecondOrderSolution.curve sol 1)) =
            inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀) ∧
          inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)) =
            inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀) ∧
          (∀ t ∈ Icc (0 : ℝ) 1,
            inner ℝ
                (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                  (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
                (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                  (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) =
              inner ℝ
                (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
                (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)) ∧
          pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 =
            ENNReal.ofReal
              ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ ∧
          |inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)| ≤
            ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ *
              ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (fderiv ℝ (fun v : E ↦ (Φ (z, v) 1).1) u w)
                (LocalChartSecondOrderSolution.curve sol 1)‖ := by
  let b := IntrinsicGeodesic.canonicalBasis (E := E)
  let z : E := extChartAt I x₀ x₀
  obtain ⟨Φ, U, hΦsmooth, hend, hfix, hUopen, hzeroU, hall⟩ :=
    exists_open_velocity_neighborhood_radial_variation_inner_eq
      (I := I) (M := M) (E := E) cov x₀ hmetric htorsion
  have hinit : ContDiff ℝ 1 (fun u : E ↦ (z, u)) := by
    simpa only [id_eq] using
      (contDiff_const (𝕜 := ℝ) (n := 1) (c := z)).prodMk
        (contDiff_id (𝕜 := ℝ) (n := 1))
  have hendpoint : ContDiff ℝ 1 (fun u : E ↦ (Φ (z, u) 1).1) := by
    simpa only [Function.comp_apply] using (hΦsmooth.comp hinit).fst
  have hendpointZero : (Φ (z, 0) 1).1 = z := by
    exact congrArg Prod.fst (hfix 1)
  refine ⟨Φ, U, hUopen, hzeroU, hendpoint, hend, hendpointZero, ?_⟩
  intro u hu w
  obtain ⟨sol, W, hradius, hflow, hWzero, hWvariation, hgauss, hspeed⟩ := hall u hu w
  have hstate := hWvariation 1 (by norm_num)
  have hposition : HasDerivAt
      (fun s : ℝ ↦ (Φ (z, u + s • w) 1).1) (W 1).1 0 := by
    simpa [z, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using
        hstate.hasFDerivAt.fst.hasDerivAt
  have huv : HasDerivAt (fun s : ℝ ↦ u + s • w) w 0 := by
    simpa [add_comm] using
      ((hasDerivAt_id' (0 : ℝ)).smul_const w |>.add_const u)
  have hendpointAt : HasFDerivAt (fun v : E ↦ (Φ (z, v) 1).1)
      (fderiv ℝ (fun v : E ↦ (Φ (z, v) 1).1) u) u :=
    (hendpoint.differentiable one_ne_zero u).hasFDerivAt
  have hendpointAt' : HasFDerivAt (fun v : E ↦ (Φ (z, v) 1).1)
      (fderiv ℝ (fun v : E ↦ (Φ (z, v) 1).1) u) (u + (0 : ℝ) • w) := by
    simpa using hendpointAt
  have hchain : HasDerivAt
      (fun s : ℝ ↦ (Φ (z, u + s • w) 1).1)
      (fderiv ℝ (fun v : E ↦ (Φ (z, v) 1).1) u w) 0 := by
    change HasDerivAt
      ((fun v : E ↦ (Φ (z, v) 1).1) ∘ (fun s : ℝ ↦ u + s • w))
      (fderiv ℝ (fun v : E ↦ (Φ (z, v) 1).1) u w) 0
    exact hendpointAt'.comp_hasDerivAt 0 huv
  have hfderiv : fderiv ℝ (fun v : E ↦ (Φ (z, v) 1).1) u w = (W 1).1 :=
    hchain.unique hposition
  have hone := hgauss 1 (by constructor <;> norm_num)
  rw [one_mul] at hone
  have hspeedOne := hspeed 1 (by constructor <;> norm_num)
  have hlength : pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 =
      ENNReal.ofReal
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ := by
    rw [local_geodesic_pathELength_eq_coordinate_speed
      (I := I) (M := M) (E := E) (H := H) cov x₀ b sol
        (by rw [hradius]; norm_num) (by rw [hradius]; norm_num)]
    rw [show (∫⁻ t in Ioo (0 : ℝ) 1,
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)‖ₑ) =
        ∫⁻ _t in Ioo (0 : ℝ) 1,
          ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ₑ by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      have hs := hspeed t ⟨ht.1.le, ht.2.le⟩
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hs
      have hn :
          ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)‖ =
          ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ := by
        nlinarith [norm_nonneg
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)),
          norm_nonneg
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)]
      simpa only [ofReal_norm] using congrArg ENNReal.ofReal hn]
    rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo]
    simp
  have hbound := abs_inner_le_norm_mul_of_gauss
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (W 1).1 (LocalChartSecondOrderSolution.curve sol 1)) hone hspeedOne
  rw [hfderiv]
  exact ⟨sol, hradius, (hflow 1).1, (hflow 1).2, hone, hspeedOne, hspeed,
    hlength, hbound⟩

/-- Clean normal-coordinate form of the radial norm estimate.  Near the
origin, the time-one endpoint map is `C¹`, has identity derivative at the
origin, and its differential cannot decrease the radial component measured
by the metric at the centre. -/
theorem exists_open_normalCoordinate_radial_norm_bound
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (htorsion : cov.torsion = 0) :
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    let z := extChartAt I x₀ x₀
    ∃ F : E → E, ∃ U : Set E,
      IsOpen U ∧ 0 ∈ U ∧ ContDiff ℝ 1 F ∧
      HasFDerivAt F (ContinuousLinearMap.id ℝ E) 0 ∧ F 0 = z ∧
      (∀ u ∈ U, F u ∈ (extChartAt I x₀).target) ∧
      (∀ u ∈ U, ∃ sol : LocalChartSecondOrderSolution I
        (coordinateAcceleration cov x₀ b) x₀ u,
        sol.radius = 2 ∧ sol.coordinate 1 = F u ∧
        pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 =
          ENNReal.ofReal
            ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ ∧
        (∀ w : E,
          inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (fderiv ℝ F u w) (LocalChartSecondOrderSolution.curve sol 1)) =
            inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)) ∧
        inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)) =
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀) ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) =
            inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)) ∧
      ∀ u ∈ U, ∀ w : E,
        |inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)| ≤
          ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ *
            ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (fderiv ℝ F u w) ((extChartAt I x₀).symm (F u))‖ := by
  let b := IntrinsicGeodesic.canonicalBasis (E := E)
  let z : E := extChartAt I x₀ x₀
  obtain ⟨Φ, U, hUopen, hzeroU, hendpoint, hend, hendpointZero, hall⟩ :=
    exists_open_velocity_neighborhood_endpoint_gauss_identity
      (I := I) (M := M) (E := E) cov x₀ hmetric htorsion
  let F : E → E := fun u ↦ (Φ (z, u) 1).1
  have hgeodesic : ∀ u ∈ U, ∃ sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u,
      sol.radius = 2 ∧ sol.coordinate 1 = F u ∧
      pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 =
        ENNReal.ofReal
          ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ ∧
      (∀ w : E,
        inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (fderiv ℝ F u w) (LocalChartSecondOrderSolution.curve sol 1)) =
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)) ∧
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) =
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀) := by
    intro u hu
    obtain ⟨sol, hradius, hcoordinate, hvelocity, _hgauss, hspeed,
      hspeedAll, hlength, _hbound⟩ := hall u hu 0
    have hcoordinateF : sol.coordinate 1 = F u := by
      simpa only [F, z] using hcoordinate
    refine ⟨sol, hradius, hcoordinateF, hlength, ?_, hspeed, hspeedAll⟩
    intro w
    obtain ⟨solw, _hradiusw, hcoordinatew, hvelocityw, hgaussw, _hspeedw,
      _hspeedAllw, _hlengthw, _hboundw⟩ := hall u hu w
    have hcurvew : LocalChartSecondOrderSolution.curve solw 1 =
        LocalChartSecondOrderSolution.curve sol 1 := by
      change (extChartAt I x₀).symm (solw.coordinate 1) =
        (extChartAt I x₀).symm (sol.coordinate 1)
      rw [hcoordinatew, hcoordinate]
    have hvelocityEq : solw.velocity 1 = sol.velocity 1 :=
      hvelocityw.trans hvelocity.symm
    rw [hcurvew, hvelocityEq] at hgaussw
    simpa only [F] using hgaussw
  refine ⟨F, U, hUopen, hzeroU, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [F] using hendpoint
  · simpa only [F] using hend
  · simpa only [F] using hendpointZero
  · intro u hu
    obtain ⟨sol, hradius, hcoordinate, _⟩ := hall u hu 0
    have hmem := sol.coordinate_mem_target 1 (by rw [hradius]; norm_num)
    rw [hcoordinate] at hmem
    simpa only [F, z] using hmem
  · intro u hu
    exact hgeodesic u hu
  · intro u hu w
    obtain ⟨sol, hradius, hcoordinate, hlength, hgauss, hspeed, _hspeedAll⟩ :=
      hgeodesic u hu
    have hcurve : LocalChartSecondOrderSolution.curve sol 1 =
        (extChartAt I x₀).symm (F u) := by
      change (extChartAt I x₀).symm (sol.coordinate 1) =
        (extChartAt I x₀).symm (F u)
      rw [hcoordinate]
    rw [← hcurve]
    exact abs_inner_le_norm_mul_of_gauss
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (fderiv ℝ F u w) (LocalChartSecondOrderSolution.curve sol 1))
      (hgauss w) hspeed

/-- The normal-coordinate endpoint map restricts to a genuine local C1
diffeomorphism while retaining the radial differential norm bound. -/
theorem exists_localDiffeomorph_normalCoordinate_radial_norm_bound
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (htorsion : cov.torsion = 0) :
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    let z := extChartAt I x₀ x₀
    ∃ F ψ : E → E, ∃ U V : Set E,
      IsOpen U ∧ 0 ∈ U ∧ IsOpen V ∧ z ∈ V ∧
      ContDiff ℝ 1 F ∧ ContDiffOn ℝ 1 ψ V ∧ F 0 = z ∧
      (∀ u ∈ U, ψ (F u) = u) ∧ (∀ y ∈ V, F (ψ y) = y) ∧
      (∀ u ∈ U, F u ∈ V) ∧ (∀ y ∈ V, ψ y ∈ U) ∧
      (∀ u ∈ U, F u ∈ (extChartAt I x₀).target) ∧
      (∀ u ∈ U, ∃ sol : LocalChartSecondOrderSolution I
        (coordinateAcceleration cov x₀ b) x₀ u,
        sol.radius = 2 ∧ sol.coordinate 1 = F u ∧
        pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 =
          ENNReal.ofReal
            ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ ∧
        (∀ w : E,
          inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (fderiv ℝ F u w) (LocalChartSecondOrderSolution.curve sol 1)) =
            inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)) ∧
        inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)) =
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀) ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) =
            inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)) ∧
      ∀ u ∈ U, ∀ w : E,
        |inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)| ≤
          ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ *
            ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (fderiv ℝ F u w) ((extChartAt I x₀).symm (F u))‖ := by
  let b := IntrinsicGeodesic.canonicalBasis (E := E)
  let z : E := extChartAt I x₀ x₀
  obtain ⟨F, Uraw, hUrawOpen, hzeroUraw, hF, hFderiv, hFzero,
    hFtargetRaw, hgeodesicRaw, hbound⟩ :=
    exists_open_normalCoordinate_radial_norm_bound
      (I := I) (M := M) (E := E) cov x₀ hmetric htorsion
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.refl ℝ E
  have hderiv : HasFDerivAt F (e : E →L[ℝ] E) 0 := by
    simpa only [e, ContinuousLinearEquiv.coe_refl] using hFderiv
  have hne : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  let hstrict : HasStrictFDerivAt F (e : E →L[ℝ] E) 0 :=
    hF.contDiffAt.hasStrictFDerivAt' hderiv hne
  let R : OpenPartialHomeomorph E E := hstrict.toOpenPartialHomeomorph F
  let R₀ : OpenPartialHomeomorph E E := R.restrOpen Uraw hUrawOpen
  have hzeroR₀ : (0 : E) ∈ R₀.source := by
    change 0 ∈ R.source ∧ 0 ∈ Uraw
    exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hzeroUraw⟩
  have hinverseSmooth : ContDiffAt ℝ 1 R₀.symm (R₀ 0) := by
    change ContDiffAt ℝ 1 (hstrict.localInverse F e 0) (F 0)
    simpa only [ContDiffAt.localInverse] using
      hF.contDiffAt.to_localInverse hderiv hne
  let R' : OpenPartialHomeomorph E E := R₀.restrContDiff ℝ 1 (by norm_num)
  have hzeroSource : (0 : E) ∈ R'.source := by
    change 0 ∈ R₀.source ∧ ContDiffAt ℝ 1 R₀ 0 ∧
      ContDiffAt ℝ 1 R₀.symm (R₀ 0)
    refine ⟨hzeroR₀, ?_, hinverseSmooth⟩
    simpa only [R₀, OpenPartialHomeomorph.coe_restrOpen, R,
      HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using hF.contDiffAt
  let ψ : E → E := R'.symm
  let U : Set E := R'.source
  let V : Set E := R'.target
  have hUopen : IsOpen U := R'.open_source
  have hVopen : IsOpen V := R'.open_target
  have hzeroU : (0 : E) ∈ U := hzeroSource
  have hFzeroR' : R' 0 = z := by
    change R₀ 0 = z
    change R 0 = z
    rw [show R 0 = F 0 by
      simpa only [R] using congrFun hstrict.toOpenPartialHomeomorph_coe 0]
    exact hFzero
  have hzV : z ∈ V := by
    rw [← hFzeroR']
    exact R'.map_source hzeroSource
  have hψsmooth : ContDiffOn ℝ 1 ψ V := by
    change ContDiffOn ℝ 1 R'.symm R'.target
    exact R₀.contDiffOn_restrContDiff_target ℝ (by norm_num)
  have hUsub : U ⊆ Uraw := by
    intro u hu
    have huR₀ : u ∈ R₀.source := hu.1
    exact huR₀.2
  have hR'eqF (u : E) : R' u = F u := by
    change R₀ u = F u
    change R u = F u
    simpa only [R] using congrFun hstrict.toOpenPartialHomeomorph_coe u
  have hleft : ∀ u ∈ U, ψ (F u) = u := by
    intro u hu
    change R'.symm (F u) = u
    rw [← hR'eqF u]
    exact R'.left_inv hu
  have hright : ∀ y ∈ V, F (ψ y) = y := by
    intro y hy
    change F (R'.symm y) = y
    rw [← hR'eqF (R'.symm y)]
    exact R'.right_inv hy
  have hFmemV : ∀ u ∈ U, F u ∈ V := by
    intro u hu
    rw [← hR'eqF u]
    exact R'.map_source hu
  have hψmemU : ∀ y ∈ V, ψ y ∈ U := by
    intro y hy
    exact R'.map_target hy
  have hFtarget : ∀ u ∈ U, F u ∈ (extChartAt I x₀).target := by
    intro u hu
    exact hFtargetRaw u (hUsub hu)
  have hgeodesic : ∀ u ∈ U, ∃ sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u,
      sol.radius = 2 ∧ sol.coordinate 1 = F u ∧
      pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 =
        ENNReal.ofReal
          ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ ∧
      (∀ w : E,
        inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (fderiv ℝ F u w) (LocalChartSecondOrderSolution.curve sol 1)) =
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)) ∧
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) =
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀) := by
    intro u hu
    exact hgeodesicRaw u (hUsub hu)
  refine ⟨F, ψ, U, V, hUopen, hzeroU, hVopen, hzV, hF, hψsmooth,
    hFzero, hleft, hright, hFmemV, hψmemU, hFtarget, hgeodesic, ?_⟩
  intro u hu w
  exact hbound u (hUsub hu) w

/-- A local coordinate geodesic whose squared speed equals its initial
squared speed on `[0,1]` has length exactly its initial speed. -/
theorem local_geodesic_pathELength_eq_initial_speed_of_inner_eq
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u)
    (hradius : (1 : ℝ) < sol.radius)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)) :
    pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 =
      ENNReal.ofReal
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ := by
  rw [local_geodesic_pathELength_eq_coordinate_speed
    (I := I) (M := M) (E := E) (H := H) cov x₀ b sol
      (by linarith [sol.radius_pos]) hradius]
  have hnorm : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)‖ =
      ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ := by
    intro t ht
    have hs := hspeed t ht
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hs
    nlinarith [norm_nonneg
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)),
      norm_nonneg (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)]
  rw [show (∫⁻ t in Ioo (0 : ℝ) 1,
      ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)‖ₑ) =
      ∫⁻ _t in Ioo (0 : ℝ) 1,
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ₑ by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    simpa only [ofReal_norm] using
      congrArg ENNReal.ofReal (hnorm t ⟨ht.1.le, ht.2.le⟩)]
  rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo]
  simp

/-- On every nontrivial subinterval of `[0,1]`, a coordinate geodesic with
conserved squared speed has length equal to elapsed time times its initial
speed. -/
theorem local_geodesic_pathELength_eq_initial_speed_mul_of_inner_eq
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {u : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u)
    (hradius : sol.radius = 2)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀))
    {a c : ℝ} (ha : 0 ≤ a) (_hac : a < c) (hc : c ≤ 1) :
    pathELength I (LocalChartSecondOrderSolution.curve sol) a c =
      ENNReal.ofReal
          ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ *
        ENNReal.ofReal (c - a) := by
  rw [local_geodesic_pathELength_eq_coordinate_speed
    (I := I) (M := M) (E := E) (H := H) cov x₀ b sol
      (by rw [hradius]; linarith) (by rw [hradius]; linarith)]
  have hnorm : ∀ t ∈ Icc a c,
      ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)‖ =
      ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ := by
    intro t ht
    have hs := hspeed t ⟨ha.trans ht.1, ht.2.trans hc⟩
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hs
    nlinarith [norm_nonneg
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)),
      norm_nonneg (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)]
  rw [show (∫⁻ t in Ioo a c,
      ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)‖ₑ) =
      ∫⁻ _t in Ioo a c,
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ₑ by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    simpa only [ofReal_norm] using
      congrArg ENNReal.ofReal (hnorm t ⟨ht.1.le, ht.2.le⟩)]
  rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo]
  simp only [ofReal_norm]

/-- The path length of an inverse-chart curve is the integral of the norm of
its coordinate velocity expressed in the local tangent frame. -/
theorem inverseChart_pathELength_eq_coordinate_speed
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (z z' : ℝ → E)
    (htarget : ∀ t ∈ Ioo (0 : ℝ) 1, z t ∈ (extChartAt I x₀).target)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt z (z' t) t) :
    pathELength I ((extChartAt I x₀).symm ∘ z) 0 1 =
      ∫⁻ t in Ioo (0 : ℝ) 1,
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (z' t) ((extChartAt I x₀).symm (z t))‖ₑ := by
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hmf := CurveConnection.hasMFDerivAt_inverseChartCurve_of_hasDerivAt
    (I := I) (M := M) (E := E) x₀ b z (htarget t ht) (hderiv t ht)
  change ‖mfderiv% ((extChartAt I x₀).symm ∘ z) t 1‖ₑ = _
  rw [hmf.mfderiv]
  rw [CurveConnection.timeTangentMap_eq_toSpanSingleton]
  change ‖(1 : ℝ) • coordinateFrameCombination (I := I) (M := M)
    (x₀ := x₀) b (z' t) ((extChartAt I x₀).symm (z t))‖ₑ = _
  rw [one_smul]

/-- The directional Gauss estimate integrates to a genuine lower bound for
every differentiable coordinate path that remains in the normal-coordinate
source.  The explicit integrability hypothesis is the remaining analytic
condition needed before applying this to arbitrary `C¹` manifold paths. -/
theorem normalCoordinate_pathELength_ge_radial
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (F : E → E) (U : Set E)
    (hF : ContDiff ℝ 1 F)
    (hFtarget : ∀ u ∈ U, F u ∈ (extChartAt I x₀).target)
    (hbound : ∀ u ∈ U, ∀ w : E,
      |inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)| ≤
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ *
          ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (fderiv ℝ F u w) ((extChartAt I x₀).symm (F u))‖)
    {u : E} (q q' : ℝ → E)
    (hq0 : q 0 = 0) (hq1 : q 1 = u)
    (hqU : ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ U)
    (hqderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt q (q' t) t)
    (hspeedInt : IntegrableOn
      (fun t ↦ ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (fderiv ℝ F (q t) (q' t))
        ((extChartAt I x₀).symm (F (q t)))‖) (Icc (0 : ℝ) 1)) :
    ENNReal.ofReal
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ ≤
      pathELength I ((extChartAt I x₀).symm ∘ F ∘ q) 0 1 := by
  let L : E →L[ℝ] TM x₀ :=
    (IntrinsicAcceleration.coordinateFrameLinear
      (I := I) (M := M) x₀ b x₀).toContinuousLinearMap
  let z : ℝ → E := F ∘ q
  let z' : ℝ → E := fun t ↦ fderiv ℝ F (q t) (q' t)
  let B : ℝ → ℝ := fun t ↦
    ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (z' t) ((extChartAt I x₀).symm (z t))‖
  have hzderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt z (z' t) t := by
    intro t ht
    have hFat : HasFDerivAt F (fderiv ℝ F (q t)) (q t) :=
      (hF.differentiable one_ne_zero (q t)).hasFDerivAt
    exact hFat.comp_hasDerivAt t (hqderiv t ht)
  have hLderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s ↦ L (q s)) (L (q' t)) t := by
    intro t ht
    exact L.hasFDerivAt.comp_hasDerivAt t (hqderiv t ht)
  have hLzero : L (q 0) = 0 := by rw [hq0, map_zero]
  have hgaussL : ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ (L (q t)) (L (q' t))| ≤ ‖L (q t)‖ * B t := by
    intro t ht
    simpa [L, B, z, z', IntrinsicAcceleration.coordinateFrameLinear_apply,
      IntrinsicAcceleration.coordinateFrameVector] using
        hbound (q t) (hqU t ht) (q' t)
  have hreal : ‖L (q 1)‖ ≤ ∫ t in (0 : ℝ)..1, B t :=
    radial_norm_le_integral_of_gauss
      (fun t ↦ L (q t)) (fun t ↦ L (q' t)) B hLderiv hLzero
      (by simpa [B, z, z'] using hspeedInt)
      (fun _ _ ↦ norm_nonneg _) hgaussL
  have hIntNonneg : 0 ≤ ∫ t in (0 : ℝ)..1, B t := by
    exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ norm_nonneg _)
  have hEnn : ENNReal.ofReal ‖L (q 1)‖ ≤
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, B t) :=
    (ENNReal.ofReal_le_ofReal_iff hIntNonneg).2 hreal
  have hIntEq : ENNReal.ofReal (∫ t in (0 : ℝ)..1, B t) =
      ∫⁻ t in Ioo (0 : ℝ) 1,
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (z' t) ((extChartAt I x₀).symm (z t))‖ₑ := by
    have hBintIoc : Integrable B (volume.restrict (Ioc (0 : ℝ) 1)) := by
      change IntegrableOn B (Ioc (0 : ℝ) 1)
      exact (by
        simpa [B, z, z'] using
          hspeedInt.mono_set (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ Icc 0 1))
    rw [intervalIntegral.integral_of_le (by norm_num)]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      hBintIoc (ae_of_all _ fun _ ↦ norm_nonneg _)]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    apply lintegral_congr
    intro t
    exact ofReal_norm _
  have hlength := inverseChart_pathELength_eq_coordinate_speed
    (I := I) (M := M) (E := E) x₀ b z z'
      (fun t ht ↦ hFtarget (q t) (hqU t ⟨ht.1.le, ht.2.le⟩))
      (fun t ht ↦ hzderiv t ⟨ht.1.le, ht.2.le⟩)
  rw [hIntEq, ← hlength] at hEnn
  simpa [L, hq1, z, Function.comp_def,
    IntrinsicAcceleration.coordinateFrameLinear_apply,
    IntrinsicAcceleration.coordinateFrameVector] using hEnn

/-- Every `C¹` path in the normal-coordinate source has length at least the
radial norm of its endpoint.  The extended-real formulation removes any
separate finiteness or speed-integrability assumption. -/
theorem normalCoordinate_contDiff_pathELength_ge_radial
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (F : E → E) (U : Set E)
    (hF : ContDiff ℝ 1 F)
    (hFtarget : ∀ u ∈ U, F u ∈ (extChartAt I x₀).target)
    (hbound : ∀ u ∈ U, ∀ w : E,
      |inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)| ≤
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ *
          ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (fderiv ℝ F u w) ((extChartAt I x₀).symm (F u))‖)
    {u : E} (q : ℝ → E)
    (hq0 : q 0 = 0) (hq1 : q 1 = u)
    (hqU : ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ U)
    (hq : ContDiffOn ℝ 1 q (Icc (0 : ℝ) 1)) :
    ENNReal.ofReal
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ ≤
      pathELength I ((extChartAt I x₀).symm ∘ F ∘ q) 0 1 := by
  let L : E →L[ℝ] TM x₀ :=
    (IntrinsicAcceleration.coordinateFrameLinear
      (I := I) (M := M) x₀ b x₀).toContinuousLinearMap
  let z : ℝ → E := F ∘ q
  let z' : ℝ → E := fun t ↦ fderiv ℝ F (q t) (deriv q t)
  let B : ℝ → ℝ := fun t ↦
    ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (z' t) ((extChartAt I x₀).symm (z t))‖
  have hQ : ContDiffOn ℝ 1 (fun t ↦ L (q t)) (Icc (0 : ℝ) 1) := by
    exact L.contDiff.comp_contDiffOn hq
  have hQzero : L (q 0) = 0 := by simp [hq0]
  have hgaussQ : ∀ t ∈ Ioo (0 : ℝ) 1,
      |inner ℝ (L (q t)) (deriv (fun s ↦ L (q s)) t)| ≤ ‖L (q t)‖ * B t := by
    intro t ht
    have hqt : HasDerivAt q (deriv q t) t :=
      ((hq t ⟨ht.1.le, ht.2.le⟩).contDiffAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero |>.hasDerivAt
    have hQL : HasDerivAt (fun s ↦ L (q s)) (L (deriv q t)) t :=
      L.hasFDerivAt.comp_hasDerivAt t hqt
    have hQderiv : deriv (fun s ↦ L (q s)) t = L (deriv q t) := hQL.deriv
    rw [hQderiv]
    simpa [L, B, z, z', IntrinsicAcceleration.coordinateFrameLinear_apply,
      IntrinsicAcceleration.coordinateFrameVector] using
        hbound (q t) (hqU t ⟨ht.1.le, ht.2.le⟩) (deriv q t)
  have hradial := enorm_radial_norm_le_lintegral_of_gauss
    (fun t ↦ L (q t)) B hQ hQzero (fun _ _ ↦ norm_nonneg _) hgaussQ
  have hzderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt z (z' t) t := by
    intro t ht
    have hqt : HasDerivAt q (deriv q t) t :=
      ((hq t ⟨ht.1.le, ht.2.le⟩).contDiffAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero |>.hasDerivAt
    have hFat : HasFDerivAt F (fderiv ℝ F (q t)) (q t) :=
      (hF.differentiable one_ne_zero (q t)).hasFDerivAt
    exact hFat.comp_hasDerivAt t hqt
  have hlength := inverseChart_pathELength_eq_coordinate_speed
    (I := I) (M := M) (E := E) x₀ b z z'
      (fun t ht ↦ hFtarget (q t) (hqU t ⟨ht.1.le, ht.2.le⟩)) hzderiv
  have hradial' : ENNReal.ofReal ‖L (q 1)‖ ≤
      ∫⁻ t in Ioo (0 : ℝ) 1,
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (z' t) ((extChartAt I x₀).symm (z t))‖ₑ := by
    simpa only [B, ofReal_norm] using hradial
  rw [← hlength] at hradial'
  simpa [L, z, hq1, Function.comp_def,
    IntrinsicAcceleration.coordinateFrameLinear_apply,
    IntrinsicAcceleration.coordinateFrameVector] using hradial'

/-- Every `C¹` manifold path that remains in the normal-coordinate
neighbourhood has length at least the radial norm of its endpoint.  This is
the manifold-level local length comparison supplied by the Gauss lemma. -/
theorem normalCoordinate_manifold_pathELength_ge_radial
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (F ψ : E → E) (U V : Set E)
    (hzeroU : (0 : E) ∈ U)
    (hF : ContDiff ℝ 1 F) (hψ : ContDiffOn ℝ 1 ψ V)
    (hFzero : F 0 = extChartAt I x₀ x₀)
    (hleft : ∀ u ∈ U, ψ (F u) = u)
    (hright : ∀ y ∈ V, F (ψ y) = y)
    (hψmemU : ∀ y ∈ V, ψ y ∈ U)
    (hFtarget : ∀ u ∈ U, F u ∈ (extChartAt I x₀).target)
    (hbound : ∀ u ∈ U, ∀ w : E,
      |inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)| ≤
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ *
          ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (fderiv ℝ F u w) ((extChartAt I x₀).symm (F u))‖)
    {u : E} (hu : u ∈ U) (γ : ℝ → M)
    (hγ0 : γ 0 = x₀) (hγ1 : γ 1 = (extChartAt I x₀).symm (F u))
    (hγsource : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (extChartAt I x₀).source)
    (hγV : ∀ t ∈ Icc (0 : ℝ) 1, extChartAt I x₀ (γ t) ∈ V)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Icc (0 : ℝ) 1)) :
    ENNReal.ofReal
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ ≤
      pathELength I γ 0 1 := by
  let c : ℝ → E := (extChartAt I x₀) ∘ γ
  let q : ℝ → E := ψ ∘ c
  have hcMDiff : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 c (Icc (0 : ℝ) 1) := by
    exact (contMDiffOn_extChartAt (I := I) (x := x₀)).comp hγ
      (fun t ht ↦ by
        rw [← extChartAt_source (I := I) x₀]
        exact hγsource t ht)
  have hc : ContDiffOn ℝ 1 c (Icc (0 : ℝ) 1) := hcMDiff.contDiffOn
  have hq : ContDiffOn ℝ 1 q (Icc (0 : ℝ) 1) := by
    exact hψ.comp hc (fun t ht ↦ hγV t ht)
  have hq0 : q 0 = 0 := by
    change ψ (extChartAt I x₀ (γ 0)) = 0
    rw [hγ0, ← hFzero]
    exact hleft 0 hzeroU
  have hFuTarget : F u ∈ (extChartAt I x₀).target := hFtarget u hu
  have hq1 : q 1 = u := by
    change ψ (extChartAt I x₀ (γ 1)) = u
    rw [hγ1, (extChartAt I x₀).right_inv hFuTarget]
    exact hleft u hu
  have hqU : ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ U := by
    intro t ht
    exact hψmemU (c t) (hγV t ht)
  have hradial := normalCoordinate_contDiff_pathELength_ge_radial
    (I := I) (M := M) (E := E) x₀ b F U hF hFtarget hbound
      q hq0 hq1 hqU hq
  have heq : EqOn ((extChartAt I x₀).symm ∘ F ∘ q) γ (Icc (0 : ℝ) 1) := by
    intro t ht
    change (extChartAt I x₀).symm (F (ψ (extChartAt I x₀ (γ t)))) = γ t
    rw [hright (extChartAt I x₀ (γ t)) (hγV t ht)]
    exact (extChartAt I x₀).left_inv (hγsource t ht)
  rw [pathELength_congr (I := I) heq] at hradial
  exact hradial

/-- A normal-coordinate neighbourhood with its integrated local length
comparison.  Every `C¹` model-space path in the source from zero to `u`
induces an inverse-chart path whose length is bounded below by the radial
norm of `u`. -/
theorem exists_localDiffeomorph_normalCoordinate_pathELength_bound
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (htorsion : cov.torsion = 0) :
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    let z := extChartAt I x₀ x₀
    ∃ F ψ : E → E, ∃ U V : Set E,
      IsOpen U ∧ 0 ∈ U ∧ IsOpen V ∧ z ∈ V ∧
      ContDiff ℝ 1 F ∧ ContDiffOn ℝ 1 ψ V ∧ F 0 = z ∧
      (∀ u ∈ U, ψ (F u) = u) ∧ (∀ y ∈ V, F (ψ y) = y) ∧
      (∀ u ∈ U, F u ∈ V) ∧ (∀ y ∈ V, ψ y ∈ U) ∧
      (∀ u ∈ U, F u ∈ (extChartAt I x₀).target) ∧
      ∀ u ∈ U, ∀ q : ℝ → E,
        q 0 = 0 → q 1 = u →
        (∀ t ∈ Icc (0 : ℝ) 1, q t ∈ U) →
        ContDiffOn ℝ 1 q (Icc (0 : ℝ) 1) →
        ENNReal.ofReal
            ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ ≤
          pathELength I ((extChartAt I x₀).symm ∘ F ∘ q) 0 1 := by
  let b := IntrinsicGeodesic.canonicalBasis (E := E)
  let z : E := extChartAt I x₀ x₀
  obtain ⟨F, ψ, U, V, hUopen, hzeroU, hVopen, hzV, hF, hψ,
    hFzero, hleft, hright, hFmemV, hψmemU, hFtarget, _hgeodesic, hbound⟩ :=
      exists_localDiffeomorph_normalCoordinate_radial_norm_bound
        (I := I) (M := M) (E := E) cov x₀ hmetric htorsion
  refine ⟨F, ψ, U, V, hUopen, hzeroU, hVopen, hzV, hF, hψ,
    hFzero, hleft, hright, hFmemV, hψmemU, hFtarget, ?_⟩
  intro u _hu q hq0 hq1 hqU hq
  exact normalCoordinate_contDiff_pathELength_ge_radial
    (I := I) (M := M) (E := E) x₀ b F U hF hFtarget hbound
      q hq0 hq1 hqU hq

/-- There is a genuine manifold normal neighbourhood on which every `C¹`
competitor from the centre to a normal-coordinate endpoint has length at
least the endpoint's radial norm. -/
theorem exists_normalCoordinate_manifold_pathELength_bound
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (htorsion : cov.torsion = 0) :
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    let z := extChartAt I x₀ x₀
    ∃ F ψ : E → E, ∃ U V : Set E,
      IsOpen U ∧ 0 ∈ U ∧ IsOpen V ∧ z ∈ V ∧
      ContDiff ℝ 1 F ∧ ContDiffOn ℝ 1 ψ V ∧ F 0 = z ∧
      (∀ u ∈ U, ψ (F u) = u) ∧ (∀ y ∈ V, F (ψ y) = y) ∧
      (∀ u ∈ U, F u ∈ V) ∧ (∀ y ∈ V, ψ y ∈ U) ∧
      (∀ u ∈ U, F u ∈ (extChartAt I x₀).target) ∧
      ∀ u ∈ U, ∀ γ : ℝ → M,
        γ 0 = x₀ → γ 1 = (extChartAt I x₀).symm (F u) →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (extChartAt I x₀).source) →
        (∀ t ∈ Icc (0 : ℝ) 1, extChartAt I x₀ (γ t) ∈ V) →
        ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Icc (0 : ℝ) 1) →
        ENNReal.ofReal
            ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ ≤
          pathELength I γ 0 1 := by
  let b := IntrinsicGeodesic.canonicalBasis (E := E)
  let z : E := extChartAt I x₀ x₀
  obtain ⟨F, ψ, U, V, hUopen, hzeroU, hVopen, hzV, hF, hψ,
    hFzero, hleft, hright, hFmemV, hψmemU, hFtarget, _hgeodesic, hbound⟩ :=
      exists_localDiffeomorph_normalCoordinate_radial_norm_bound
        (I := I) (M := M) (E := E) cov x₀ hmetric htorsion
  refine ⟨F, ψ, U, V, hUopen, hzeroU, hVopen, hzV, hF, hψ,
    hFzero, hleft, hright, hFmemV, hψmemU, hFtarget, ?_⟩
  intro u hu γ hγ0 hγ1 hγsource hγV hγ
  exact normalCoordinate_manifold_pathELength_ge_radial
    (I := I) (M := M) (E := E) x₀ b F ψ U V hzeroU hF hψ hFzero
      hleft hright hψmemU hFtarget hbound hu γ hγ0 hγ1 hγsource hγV hγ

/-- Normal radial geodesics are locally length minimizing: within the normal
neighbourhood, their length is no larger than that of any `C¹` competitor
with the same endpoints. -/
theorem exists_normalCoordinate_locally_lengthMinimizing_geodesic
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (htorsion : cov.torsion = 0) :
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    let z := extChartAt I x₀ x₀
    ∃ F ψ : E → E, ∃ U V : Set E,
      IsOpen U ∧ 0 ∈ U ∧ IsOpen V ∧ z ∈ V ∧
      ContDiff ℝ 1 F ∧ ContDiffOn ℝ 1 ψ V ∧ F 0 = z ∧
      (∀ u ∈ U, ψ (F u) = u) ∧ (∀ y ∈ V, F (ψ y) = y) ∧
      (∀ u ∈ U, F u ∈ V) ∧ (∀ y ∈ V, ψ y ∈ U) ∧
      (∀ u ∈ U, F u ∈ (extChartAt I x₀).target) ∧
      ∀ u ∈ U, ∃ sol : LocalChartSecondOrderSolution I
        (coordinateAcceleration cov x₀ b) x₀ u,
        sol.radius = 2 ∧ sol.coordinate 1 = F u ∧
        pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 =
          ENNReal.ofReal
            ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ ∧
        (∀ w : E,
          inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (fderiv ℝ F u w) (LocalChartSecondOrderSolution.curve sol 1)) =
            inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w x₀)) ∧
        inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
              (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)) =
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
                (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) =
            inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)) ∧
        ∀ γ : ℝ → M,
          γ 0 = x₀ → γ 1 = (extChartAt I x₀).symm (F u) →
          (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (extChartAt I x₀).source) →
          (∀ t ∈ Icc (0 : ℝ) 1, extChartAt I x₀ (γ t) ∈ V) →
          ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Icc (0 : ℝ) 1) →
          pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 ≤
            pathELength I γ 0 1 := by
  let b := IntrinsicGeodesic.canonicalBasis (E := E)
  let z : E := extChartAt I x₀ x₀
  obtain ⟨F, ψ, U, V, hUopen, hzeroU, hVopen, hzV, hF, hψ,
    hFzero, hleft, hright, hFmemV, hψmemU, hFtarget, hgeodesic, hbound⟩ :=
      exists_localDiffeomorph_normalCoordinate_radial_norm_bound
        (I := I) (M := M) (E := E) cov x₀ hmetric htorsion
  refine ⟨F, ψ, U, V, hUopen, hzeroU, hVopen, hzV, hF, hψ,
    hFzero, hleft, hright, hFmemV, hψmemU, hFtarget, ?_⟩
  intro u hu
  obtain ⟨sol, hradius, hcoordinate, hlength, hgauss, hspeed, hspeedAll⟩ :=
    hgeodesic u hu
  refine ⟨sol, hradius, hcoordinate, hlength, hgauss, hspeed, hspeedAll, ?_⟩
  intro γ hγ0 hγ1 hγsource hγV hγ
  have hcompetitor := normalCoordinate_manifold_pathELength_ge_radial
    (I := I) (M := M) (E := E) x₀ b F ψ U V hzeroU hF hψ hFzero
      hleft hright hψmemU hFtarget hbound hu γ hγ0 hγ1 hγsource hγV hγ
  rw [hlength]
  exact hcompetitor


end LocalGeodesicData

end BonnetMyersEntry
