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

public import LeanPool.PoincareGeometry.BonnetMyers.GaussLemma
public import LeanPool.PoincareGeometry.BonnetMyers.Curvature

/-!
# Coordinate curvature along a geodesic chart

This module derives the coordinate curvature operator from the actual
covariant-derivative curvature tensor.  It is the local differential identity
needed to linearize the geodesic acceleration in the independent
second-variation proof.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter
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

/-- Applying the derivative of the chart to the tangent represented by a
model vector returns that model vector. -/
theorem mfderiv_extChartAt_coordinateFrameCombination
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {y : M} (hy : y ∈ (extChartAt I x₀).source) (u : E) :
    (mfderiv (I := I) 𝓘(ℝ, E) (extChartAt I x₀) y)
        (coordinateFrameCombination (I := I) (M := M)
          (x₀ := x₀) b u y) = u := by
  have hychart : y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact hy
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt
    (𝕜 := ℝ) (I := I) hychart]
  rw [coordinateFrameCombination_eq_symmL
    (I := I) (M := M) (x₀ := x₀) b hychart]
  exact (trivializationAt E TM x₀).continuousLinearMapAt_symmL
    (by simpa using hychart) u

/-- The manifold derivative of an ordinary scalar coordinate function, in a
coordinate-frame direction, is its ordinary Fréchet derivative. -/
theorem mvfderiv_comp_extChartAt_apply_coordinateFrameCombination
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {f : E → ℝ} {y : M} (hy : y ∈ (extChartAt I x₀).source)
    (hf : DifferentiableAt ℝ f (extChartAt I x₀ y)) (u : E) :
    mvfderiv (I := I) (f ∘ extChartAt I x₀) y
        (coordinateFrameCombination (I := I) (M := M)
          (x₀ := x₀) b u y) =
      fderiv ℝ f (extChartAt I x₀ y) u := by
  have hychart : y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact hy
  have hchart : MDiffAt (extChartAt I x₀) y :=
    mdifferentiableAt_extChartAt hychart
  have hfM : MDiffAt f (extChartAt I x₀ y) :=
    hf.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  rw [mvfderiv_comp_apply y hfM hchart]
  rw [mfderiv_extChartAt_coordinateFrameCombination
    (I := I) (M := M) x₀ b hy u]
  simp only [mvfderiv, mfderiv_eq_fderiv]
  rfl

/-- A `C¹` model-space coefficient function defines a `C¹` tangent section
through the coordinate frame. -/
theorem coordinateFrameFunction_contMDiffAt
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {f : E → E} {y : M} (hy : y ∈ (extChartAt I x₀).source)
    (hf : ContDiffAt ℝ 1 f (extChartAt I x₀ y)) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun z ↦ TotalSpace.mk' E z
        (coordinateFrameCombination (I := I) (M := M)
          (x₀ := x₀) b (f (extChartAt I x₀ z)) z)) y := by
  let e := trivializationAt E TM x₀
  have hychart : y ∈ (chartAt H x₀).source := by
    simpa only [← extChartAt_source (I := I)] using hy
  have hbase : y ∈ e.baseSet := by simpa [e] using hychart
  have hfi : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ) 1
        (fun z ↦ b.repr (f (extChartAt I x₀ z)) i) y := by
    intro i
    have hchart : ContMDiffAt I 𝓘(ℝ, E) 1 (extChartAt I x₀) y :=
      contMDiffAt_extChartAt' hychart
    have hcoord : ContDiffAt ℝ 1 (fun q ↦ b.repr (f q) i)
        (extChartAt I x₀ y) :=
      (b.coord i).toContinuousLinearMap.contDiff.contDiffAt.comp
        (extChartAt I x₀ y) hf
    exact hcoord.contMDiffAt.comp y hchart
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun z ↦ TotalSpace.mk' E z
          ((b.repr (f (extChartAt I x₀ z)) i) • e.localFrame b i z)) y := by
    intro i
    have hlocal := contMDiffAt_localFrame_of_mem (I := I) (e := e)
      (b := b) (n := (1 : WithTop ℕ∞)) i hbase
    exact (hfi i).smul_section hlocal
  have hsum := ContMDiffAt.sum_section
    (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
    (fun i _hi ↦ hterm i)
  simpa [coordinateFrameCombination, e] using hsum

/-- The coordinate Christoffel operator is `C¹` in the base coordinate when
its two vector arguments are fixed. -/
theorem coordinateParallelOperator_fixed_contDiffAt_of_mem_target
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {z : E} (hz : z ∈ (extChartAt I x₀).target) (u w : E) :
    ContDiffAt ℝ 1
      (fun q ↦ coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b q u w) z := by
  have hterm : ∀ i j k : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ 1
        (fun q ↦ ((b.repr w j) * (b.repr u k) *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b i j k ((extChartAt I x₀).symm q)) • b i) z := by
    intro i j k
    exact ((contDiffAt_const.mul
      (connectionCoefficient_comp_extChartAt_symm_contDiffAt_of_mem_target
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
      i j k hz)).smul_const (b i))
  have hsum : ContDiffAt ℝ 1
      (fun q ↦ ∑ i, ∑ j, ∑ k,
        ((b.repr w j) * (b.repr u k) *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b i j k ((extChartAt I x₀).symm q)) • b i) z := by
    apply ContDiffAt.sum
    intro i hi
    apply ContDiffAt.sum
    intro j hj
    apply ContDiffAt.sum
    intro k hk
    exact hterm i j k
  simpa only [coordinateParallelOperator_apply] using hsum

/-- Curvature written in a coordinate frame.  The ordering matches
`R(u,v)w = ∇_u∇_v w - ∇_v∇_u w` for commuting coordinate fields. -/
noncomputable def coordinateCurvatureOperator
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (z u v w : E) : E :=
  fderiv ℝ (fun q ↦ coordinateParallelOperator (I := I) (M := M) (E := E)
      cov x₀ b q v w) z u -
    fderiv ℝ (fun q ↦ coordinateParallelOperator (I := I) (M := M) (E := E)
      cov x₀ b q u w) z v +
    coordinateParallelOperator (I := I) (M := M) (E := E)
      cov x₀ b z u
        (coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b z v w) -
    coordinateParallelOperator (I := I) (M := M) (E := E)
      cov x₀ b z v
        (coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b z u w)

/-- A global smooth representative of a constant coordinate vector field. -/
noncomputable def smoothCoordinateField
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (u : E) : (y : M) → TM y := fun y ↦
  ∑ i, (b.repr u i) •
    smoothFrame (I := I) (M := M) (E := E) x₀ b i y

theorem smoothCoordinateField_contMDiff_two
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (u : E) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y
        (smoothCoordinateField (I := I) (M := M) x₀ b u y)) := by
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y
          ((b.repr u i) • smoothFrame (I := I) (M := M) (E := E)
            x₀ b i y)) := by
    intro i
    have hs : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y
          (smoothFrame (I := I) (M := M) (E := E) x₀ b i y)) := by
      simpa [smoothFrame] using
        CovariantDerivative.smoothExtend_contMDiff_two
          (I := I) (F := E) (V := TM) x₀
            ((trivializationAt E TM x₀).localFrame b i x₀)
    exact contMDiff_const.smul_section hs
  have hsum := ContMDiff.sum_section
    (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
    (fun i _hi ↦ hterm i)
  simpa [smoothCoordinateField] using hsum

theorem smoothCoordinateField_eventuallyEq_coordinateFrameCombination
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (u : E) {y : M}
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 y,
        smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
          (trivializationAt E TM x₀).localFrame b j z) :
    smoothCoordinateField (I := I) (M := M) x₀ b u =ᶠ[𝓝 y]
      fun z ↦ coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) b u z := by
  have hall : ∀ᶠ z in 𝓝 y,
      ∀ j ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
          (trivializationAt E TM x₀).localFrame b j z :=
    (Finset.eventually_all Finset.univ).2 (fun j _hj ↦ hframe j)
  filter_upwards [hall] with z hz
  unfold smoothCoordinateField coordinateFrameCombination
  apply Finset.sum_congr rfl
  intro i hi
  rw [hz i hi]

/-- Constant coordinate fields commute.  Here this is recovered from
torsion-freeness and the symmetry of the chart Christoffel operator. -/
theorem mlieBracket_coordinateFrameCombination_eq_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {y : M} (hy : y ∈ (extChartAt I x₀).source)
    (htorsion : cov.torsion = 0)
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 y,
        smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
          (trivializationAt E TM x₀).localFrame b j z)
    (u v : E) :
    VectorField.mlieBracket I
      (fun z ↦ coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) b u z)
      (fun z ↦ coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) b v z) y = 0 := by
  let U : (z : M) → TM z := fun z ↦ coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b u z
  let V : (z : M) → TM z := fun z ↦ coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b v z
  have hychart : y ∈ (chartAt H x₀).source := by
    simpa only [← extChartAt_source (I := I)] using hy
  have hU : MDiffAt (T% U) y :=
    (coordinateFrameCombination_contMDiffAt (I := I) (M := M)
      (x₀ := x₀) y b u hychart).mdifferentiableAt one_ne_zero
  have hV : MDiffAt (T% V) y :=
    (coordinateFrameCombination_contMDiffAt (I := I) (M := M)
      (x₀ := x₀) y b v hychart).mdifferentiableAt one_ne_zero
  have htor := (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp
    htorsion hU hV
  have hcovV := cov_coordinateFrameCombination_apply
    (I := I) (M := M) (E := E) cov x₀ y b u v hychart hframe
  have hcovU := cov_coordinateFrameCombination_apply
    (I := I) (M := M) (E := E) cov x₀ y b v u hychart hframe
  have hz : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hy
  have hleft : (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
    (extChartAt I x₀).left_inv hy
  have hframe' : ∀ j : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
        𝓝 ((extChartAt I x₀).symm (extChartAt I x₀ y))]
          (trivializationAt E TM x₀).localFrame b j := by
    rw [hleft]
    exact hframe
  have hsymm := coordinateParallelOperator_apply_comm_of_torsion_eq_zero
    (I := I) (M := M) (E := E) cov x₀ b hz htorsion hframe'
    (u := u) (w := v)
  change cov V y (U y) - cov U y (V y) = _ at htor
  rw [hcovV, hcovU, hsymm] at htor
  simpa [U, V] using htor.symm

/-- Near a point where the smooth frame extensions agree with the chart
frame, differentiating one smooth constant-coordinate field along another is
represented by the coordinate Christoffel operator. -/
theorem cov_smoothCoordinateField_eventuallyEq_coordinateParallelField
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {y : M} (hy : y ∈ (extChartAt I x₀).source)
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 y,
        smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
          (trivializationAt E TM x₀).localFrame b j z)
    (u w : E) :
    cov.along
        (smoothCoordinateField (I := I) (M := M) x₀ b u)
        (smoothCoordinateField (I := I) (M := M) x₀ b w) =ᶠ[𝓝 y]
      fun q ↦ coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) b
        (coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b (extChartAt I x₀ q) u w) q := by
  let U := smoothCoordinateField (I := I) (M := M) x₀ b u
  let W := smoothCoordinateField (I := I) (M := M) x₀ b w
  let Uc : (q : M) → TM q := fun q ↦ coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b u q
  let Wc : (q : M) → TM q := fun q ↦ coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b w q
  have hUeq : U =ᶠ[𝓝 y] Uc := by
    simpa [U, Uc] using smoothCoordinateField_eventuallyEq_coordinateFrameCombination
      (I := I) (M := M) (E := E) x₀ b u hframe
  have hWeq : W =ᶠ[𝓝 y] Wc := by
    simpa [W, Wc] using smoothCoordinateField_eventuallyEq_coordinateFrameCombination
      (I := I) (M := M) (E := E) x₀ b w hframe
  have hframes : ∀ᶠ q in 𝓝 y,
      ∀ j ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        ∀ᶠ z in 𝓝 q,
          smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
            (trivializationAt E TM x₀).localFrame b j z :=
    (Finset.eventually_all Finset.univ).2 fun j _hj ↦
      eventually_eventually_nhds.2 (hframe j)
  have hUlocal : ∀ᶠ q in 𝓝 y, U =ᶠ[𝓝 q] Uc :=
    eventually_eventually_nhds.2 hUeq
  have hWlocal : ∀ᶠ q in 𝓝 y, W =ᶠ[𝓝 q] Wc :=
    eventually_eventually_nhds.2 hWeq
  filter_upwards [hUlocal, hWlocal, hframes,
    (isOpen_extChartAt_source x₀).mem_nhds hy] with q hUq hWq hframeq hq
  have hqchart : q ∈ (chartAt H x₀).source := by
    simpa only [← extChartAt_source (I := I)] using hq
  have hWdiff : MDiffAt (T% W) q :=
    ((smoothCoordinateField_contMDiff_two (I := I) (M := M) (E := E)
      x₀ b w).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2) q)
      |>.mdifferentiableAt one_ne_zero
  have hWcdiff : MDiffAt (T% Wc) q :=
    (coordinateFrameCombination_contMDiffAt (I := I) (M := M)
      (x₀ := x₀) q b w hqchart).mdifferentiableAt one_ne_zero
  have hcovW : cov W q = cov Wc q :=
    IsCovariantDerivativeOn.congr_of_eventuallyEq cov.isCovariantDerivativeOn
      hWdiff hWcdiff Filter.univ_mem hWq
  have hUvalue : U q = Uc q := hUq.self_of_nhds
  have hframeq' : ∀ j : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 q,
        smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
          (trivializationAt E TM x₀).localFrame b j z :=
    fun j ↦ hframeq j (Finset.mem_univ j)
  calc
    cov.along U W q = cov W q (U q) := rfl
    _ = cov Wc q (Uc q) := by rw [hcovW, hUvalue]
    _ = coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b (extChartAt I x₀ q) u w) q :=
      cov_coordinateFrameCombination_apply (I := I) (M := M) (E := E)
        cov x₀ q b u w hqchart hframeq'

/-- Covariant differentiation of a variable coordinate field is ordinary
coordinate differentiation plus the Christoffel operator. -/
theorem cov_coordinateFrameFunction_apply
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {f : E → E} {y : M} (hy : y ∈ (extChartAt I x₀).source)
    (hf : ContDiffAt ℝ 1 f (extChartAt I x₀ y)) (u : E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 y,
        smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
          (trivializationAt E TM x₀).localFrame b j z) :
    cov (fun z ↦ coordinateFrameCombination (I := I) (M := M)
          (x₀ := x₀) b (f (extChartAt I x₀ z)) z) y
        (coordinateFrameCombination (I := I) (M := M)
          (x₀ := x₀) b u y) =
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (fderiv ℝ f (extChartAt I x₀ y) u +
          coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (extChartAt I x₀ y) u
              (f (extChartAt I x₀ y))) y := by
  let e := trivializationAt E TM x₀
  let U : TM y := coordinateFrameCombination (I := I) (M := M)
    (x₀ := x₀) b u y
  let X : (z : M) → TM z := fun z ↦
    coordinateFrameCombination (I := I) (M := M)
      (x₀ := x₀) b (f (extChartAt I x₀ z)) z
  have hychart : y ∈ (chartAt H x₀).source := by
    simpa only [← extChartAt_source (I := I)] using hy
  have hbase : y ∈ e.baseSet := by simpa [e] using hychart
  have hfi : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ) 1
        (fun z ↦ b.repr (f (extChartAt I x₀ z)) i) y := by
    intro i
    have hchart : ContMDiffAt I 𝓘(ℝ, E) 1 (extChartAt I x₀) y :=
      contMDiffAt_extChartAt' hychart
    have hcoord : ContDiffAt ℝ 1 (fun q ↦ b.repr (f q) i)
        (extChartAt I x₀ y) :=
      (b.coord i).toContinuousLinearMap.contDiff.contDiffAt.comp
        (extChartAt I x₀ y) hf
    exact hcoord.contMDiffAt.comp y hchart
  have hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun z ↦ TotalSpace.mk' E z (X z)) y := by
    have hterm : ∀ i : Fin (Module.finrank ℝ E),
        ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
          (fun z ↦ TotalSpace.mk' E z
            ((b.repr (f (extChartAt I x₀ z)) i) • e.localFrame b i z)) y := by
      intro i
      have hlocal := contMDiffAt_localFrame_of_mem (I := I) (e := e)
        (b := b) (n := (1 : WithTop ℕ∞)) i hbase
      exact (hfi i).smul_section hlocal
    have hsum := ContMDiffAt.sum_section
      (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (fun i _hi ↦ hterm i)
    simpa [X, coordinateFrameCombination, e] using hsum
  have hdecomp :=
    CovariantDerivative.TangentFrame.covariantDerivative_apply_eq_sum_localFrame_add_sum_covariantDerivative_localFrame
      (I := I) (E := E) e b cov hbase
      (hX.mdifferentiableAt one_ne_zero) U
  have hcoeff : ∀ i : Fin (Module.finrank ℝ E),
      (LinearMap.piApply (e.localFrameCoeff I b i)) X =ᶠ[𝓝 y]
        (fun z ↦ b.repr (f (extChartAt I x₀ z)) i) := by
    intro i
    filter_upwards [e.open_baseSet.mem_nhds hbase] with z hz
    change (e.localFrameCoeff I b i z) (X z) = _
    rw [e.localFrameCoeff_apply_of_mem_baseSet (I := I) (b := b) hz X i]
    have hsum := Module.Basis.sum_repr (e.basisAt b hz) (X z)
    have hframe : ∀ j : Fin (Module.finrank ℝ E),
        e.localFrame b j z = (e.basisAt b hz) j := by
      intro j
      exact e.localFrame_apply_of_mem_baseSet (b := b) hz
    have hXsum : X z = ∑ j, (b.repr (f (extChartAt I x₀ z)) j) •
        (e.basisAt b hz) j := by
      simp only [X, coordinateFrameCombination]
      exact Finset.sum_congr rfl (fun j _hj ↦ by rw [hframe j])
    rw [hXsum, map_sum]
    simp [Module.Basis.repr_self]
  have hderiv : ∀ i : Fin (Module.finrank ℝ E),
      mvfderiv (I := I) ((LinearMap.piApply
          (e.localFrameCoeff I b i)) X) y U =
        b.repr (fderiv ℝ f (extChartAt I x₀ y) u) i := by
    intro i
    have heq : mvfderiv (I := I)
        ((LinearMap.piApply (e.localFrameCoeff I b i)) X) y =
        mvfderiv (I := I)
          (fun z ↦ b.repr (f (extChartAt I x₀ z)) i) y :=
      (hcoeff i).mfderiv_eq
    rw [heq]
    have hscalar := mvfderiv_comp_extChartAt_apply_coordinateFrameCombination
      (I := I) (M := M) (E := E) x₀ b hy
      ((b.coord i).toContinuousLinearMap.differentiableAt.comp
        (extChartAt I x₀ y) (hf.differentiableAt one_ne_zero)) u
    have hf' := hf.differentiableAt one_ne_zero
    have hcoordDeriv : fderiv ℝ ((b.coord i).toContinuousLinearMap ∘ f)
        (extChartAt I x₀ y) =
        (b.coord i).toContinuousLinearMap.comp
          (fderiv ℝ f (extChartAt I x₀ y)) :=
      ((b.coord i).toContinuousLinearMap.hasFDerivAt.comp
        (extChartAt I x₀ y) hf'.hasFDerivAt).fderiv
    rw [hcoordDeriv] at hscalar
    simpa [U, Function.comp_def, ContinuousLinearMap.comp_apply] using hscalar
  have hderivSum :
      (∑ i, mvfderiv (I := I)
          ((LinearMap.piApply (e.localFrameCoeff I b i)) X) y U •
            e.localFrame b i y) =
        coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (fderiv ℝ f (extChartAt I x₀ y) u) y := by
    simp_rw [hderiv]
    rfl
  have hcoeffPoint : ∀ i : Fin (Module.finrank ℝ E),
      (LinearMap.piApply (e.localFrameCoeff I b i)) X y =
        b.repr (f (extChartAt I x₀ y)) i := fun i ↦ (hcoeff i).self_of_nhds
  have hconnectionSum :
      (∑ i, (LinearMap.piApply (e.localFrameCoeff I b i)) X y •
          cov (e.localFrame b i) y U) =
        cov (fun z ↦ coordinateFrameCombination (I := I) (M := M)
          (x₀ := x₀) b (f (extChartAt I x₀ y)) z) y U := by
    simp_rw [hcoeffPoint]
    symm
    unfold coordinateFrameCombination
    let Ufield : (z : M) → TM z := fun z ↦
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u z
    have hsumAlong : ∀ S : Finset (Fin (Module.finrank ℝ E)),
        cov.along Ufield
            (fun z ↦ ∑ i ∈ S, b.repr (f (extChartAt I x₀ y)) i •
              e.localFrame b i z) y =
          ∑ i ∈ S, b.repr (f (extChartAt I x₀ y)) i •
            cov.along Ufield (e.localFrame b i) y := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
          simp only [Finset.sum_empty]
          change cov.along Ufield (0 : (z : M) → TM z) y = 0
          simp [CovariantDerivative.along]
      | @insert i S hi ih =>
          have hlocal : MDiffAt (T% (e.localFrame b i)) y :=
            (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
              (n := (1 : WithTop ℕ∞)) i hbase).mdifferentiableAt one_ne_zero
          have hterm : MDiffAt
              (T% (fun z ↦ b.repr (f (extChartAt I x₀ y)) i •
                e.localFrame b i z)) y :=
            hlocal.smul_const_section
          have hrest : MDiffAt
              (T% (fun z ↦ ∑ j ∈ S, b.repr (f (extChartAt I x₀ y)) j •
                e.localFrame b j z)) y := by
            apply MDifferentiableAt.sum_section
            intro j hj
            exact (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
              (n := (1 : WithTop ℕ∞)) j hbase).mdifferentiableAt one_ne_zero
              |>.smul_const_section
          have hadd := cov.along_add_right_apply (X := Ufield)
            (x := y) hterm hrest
          have hsmul := cov.along_smul_right_apply (X := Ufield) (x := y)
            (f := fun _ : M ↦ b.repr (f (extChartAt I x₀ y)) i)
            (σ := e.localFrame b i) mdifferentiableAt_const hlocal
          simp only [mvfderiv_const, zero_apply,
            zero_smul, add_zero] at hsmul
          simp only [Finset.sum_insert hi]
          change cov.along Ufield
            ((fun z ↦ b.repr (f (extChartAt I x₀ y)) i • e.localFrame b i z) +
              (fun z ↦ ∑ j ∈ S, b.repr (f (extChartAt I x₀ y)) j •
                e.localFrame b j z)) y = _
          exact hadd.trans (congrArg₂ (· + ·) hsmul ih)
    have hall := hsumAlong Finset.univ
    simpa [CovariantDerivative.along, Ufield, e] using hall
  have hconstant := cov_coordinateFrameCombination_apply
    (I := I) (M := M) (E := E) cov x₀ y b u
      (f (extChartAt I x₀ y)) hychart hframe
  rw [hdecomp, hderivSum, hconnectionSum, hconstant]
  unfold coordinateFrameCombination
  simp only [map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]

/-- The coordinate curvature operator is the actual curvature tensor of the
torsion-free connection, expressed in the chosen chart frame. -/
theorem coordinateFrameCombination_coordinateCurvatureOperator
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {y : M} (hy : y ∈ (extChartAt I x₀).source)
    (htorsion : cov.torsion = 0)
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 y,
        smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
          (trivializationAt E TM x₀).localFrame b j z)
    (u v w : E) :
    coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (coordinateCurvatureOperator (I := I) (M := M)
          cov x₀ b (extChartAt I x₀ y) u v w) y =
      curvature (cov := cov) y
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v y)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w y) := by
  let X := smoothCoordinateField (I := I) (M := M) x₀ b u
  let Y := smoothCoordinateField (I := I) (M := M) x₀ b v
  let Z := smoothCoordinateField (I := I) (M := M) x₀ b w
  let Xc : (q : M) → TM q := fun q ↦ coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b u q
  let Yc : (q : M) → TM q := fun q ↦ coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b v q
  let Zc : (q : M) → TM q := fun q ↦ coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b w q
  let Pvw : E → E := fun q ↦ coordinateParallelOperator
    (I := I) (M := M) (E := E) cov x₀ b q v w
  let Puw : E → E := fun q ↦ coordinateParallelOperator
    (I := I) (M := M) (E := E) cov x₀ b q u w
  let Acoord : (q : M) → TM q := fun q ↦ coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b (Pvw (extChartAt I x₀ q)) q
  let Bcoord : (q : M) → TM q := fun q ↦ coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b (Puw (extChartAt I x₀ q)) q
  have hX2 := smoothCoordinateField_contMDiff_two
    (I := I) (M := M) (E := E) x₀ b u
  have hY2 := smoothCoordinateField_contMDiff_two
    (I := I) (M := M) (E := E) x₀ b v
  have hZ2 := smoothCoordinateField_contMDiff_two
    (I := I) (M := M) (E := E) x₀ b w
  have hX1 : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun q ↦ TotalSpace.mk' E q (X q)) := by
    simpa [X] using hX2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hY1 : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun q ↦ TotalSpace.mk' E q (Y q)) := by
    simpa [Y] using hY2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hZ2' : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun q ↦ TotalSpace.mk' E q (Z q)) := by simpa [Z] using hZ2
  have hXeq : X =ᶠ[𝓝 y] Xc := by
    simpa [X, Xc] using smoothCoordinateField_eventuallyEq_coordinateFrameCombination
      (I := I) (M := M) (E := E) x₀ b u hframe
  have hYeq : Y =ᶠ[𝓝 y] Yc := by
    simpa [Y, Yc] using smoothCoordinateField_eventuallyEq_coordinateFrameCombination
      (I := I) (M := M) (E := E) x₀ b v hframe
  have hZeq : Z =ᶠ[𝓝 y] Zc := by
    simpa [Z, Zc] using smoothCoordinateField_eventuallyEq_coordinateFrameCombination
      (I := I) (M := M) (E := E) x₀ b w hframe
  have hXvalue : X y = Xc y := hXeq.self_of_nhds
  have hYvalue : Y y = Yc y := hYeq.self_of_nhds
  have hZvalue : Z y = Zc y := hZeq.self_of_nhds
  have hz : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hy
  have hPvw : ContDiffAt ℝ 1 Pvw (extChartAt I x₀ y) := by
    simpa [Pvw] using coordinateParallelOperator_fixed_contDiffAt_of_mem_target
      (I := I) (M := M) (E := E) cov x₀ b hz v w
  have hPuw : ContDiffAt ℝ 1 Puw (extChartAt I x₀ y) := by
    simpa [Puw] using coordinateParallelOperator_fixed_contDiffAt_of_mem_target
      (I := I) (M := M) (E := E) cov x₀ b hz u w
  have hAcoord : MDiffAt (T% Acoord) y := by
    exact (coordinateFrameFunction_contMDiffAt (I := I) (M := M) (E := E)
      x₀ b hy hPvw).mdifferentiableAt one_ne_zero
  have hBcoord : MDiffAt (T% Bcoord) y := by
    exact (coordinateFrameFunction_contMDiffAt (I := I) (M := M) (E := E)
      x₀ b hy hPuw).mdifferentiableAt one_ne_zero
  have hAreg : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun q ↦ TotalSpace.mk' E q (cov.along Y Z q)) :=
    cov.contMDiff_along hY1 hZ2'
  have hBreg : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun q ↦ TotalSpace.mk' E q (cov.along X Z q)) :=
    cov.contMDiff_along hX1 hZ2'
  have hAeq : cov.along Y Z =ᶠ[𝓝 y] Acoord := by
    simpa [Y, Z, Acoord, Pvw] using
      cov_smoothCoordinateField_eventuallyEq_coordinateParallelField
        (I := I) (M := M) (E := E) cov x₀ b hy hframe v w
  have hBeq : cov.along X Z =ᶠ[𝓝 y] Bcoord := by
    simpa [X, Z, Bcoord, Puw] using
      cov_smoothCoordinateField_eventuallyEq_coordinateParallelField
        (I := I) (M := M) (E := E) cov x₀ b hy hframe u w
  have hcovA : cov (cov.along Y Z) y = cov Acoord y :=
    IsCovariantDerivativeOn.congr_of_eventuallyEq cov.isCovariantDerivativeOn
      ((hAreg y).mdifferentiableAt one_ne_zero) hAcoord Filter.univ_mem hAeq
  have hcovB : cov (cov.along X Z) y = cov Bcoord y :=
    IsCovariantDerivativeOn.congr_of_eventuallyEq cov.isCovariantDerivativeOn
      ((hBreg y).mdifferentiableAt one_ne_zero) hBcoord Filter.univ_mem hBeq
  have hfirst : cov (cov.along Y Z) y (X y) =
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (fderiv ℝ Pvw (extChartAt I x₀ y) u +
          coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (extChartAt I x₀ y) u
              (Pvw (extChartAt I x₀ y))) y := by
    rw [hcovA, hXvalue]
    exact cov_coordinateFrameFunction_apply (I := I) (M := M) (E := E)
      cov x₀ b hy hPvw u hframe
  have hsecond : cov (cov.along X Z) y (Y y) =
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (fderiv ℝ Puw (extChartAt I x₀ y) v +
          coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (extChartAt I x₀ y) v
              (Puw (extChartAt I x₀ y))) y := by
    rw [hcovB, hYvalue]
    exact cov_coordinateFrameFunction_apply (I := I) (M := M) (E := E)
      cov x₀ b hy hPuw v hframe
  have hbracket : VectorField.mlieBracket I X Y y = 0 := by
    rw [hXeq.mlieBracket_vectorField_eq hYeq]
    exact mlieBracket_coordinateFrameCombination_eq_zero
      (I := I) (M := M) (E := E) cov x₀ b hy htorsion hframe u v
  have hcurv := curvature_apply_contMDiff cov X Y Z hX1 hY1 hZ2' y
  change curvature (cov := cov) y (X y) (Y y) (Z y) =
    cov (cov.along Y Z) y (X y) - cov (cov.along X Z) y (Y y) -
      cov Z y (VectorField.mlieBracket I X Y y) at hcurv
  rw [hfirst, hsecond, hbracket, map_zero, sub_zero,
    hXvalue, hYvalue, hZvalue] at hcurv
  change coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (coordinateCurvatureOperator (I := I) (M := M)
        cov x₀ b (extChartAt I x₀ y) u v w) y =
    curvature (cov := cov) y (Xc y) (Yc y) (Zc y)
  rw [hcurv]
  simp only [Xc, Yc, Zc, Pvw, Puw, coordinateCurvatureOperator]
  unfold coordinateFrameCombination
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply,
    sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  abel

end LocalGeodesicData

end BonnetMyersEntry
