/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurck

/-!
# The standard Ricci--DeTurck metric equation

This file keeps the standard DeTurck gauge separate from the older
trace-one-form construction.  Its correction is the metric Lie-derivative
term formed from `standardDeTurckVectorField`, namely the symmetrized
covariant derivative with respect to the evolving metric's Levi-Civita
connection.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

section ChosenLeviCivita

variable [SigmaCompactSpace M]

/-- The metric correction in the standard Ricci--DeTurck equation.  It is
the symmetrized covariant derivative of the standard metric-contracted
connection-difference vector field. -/
def standardDeTurckCorrection
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) :
    MetricTensorFamily (I := I) (M := M) :=
  fun t x u v ↦ by
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    exact
      (g t).inner x
        (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
          (standardDeTurckVectorField (I := I) (M := M) g background t) x u) v +
      (g t).inner x u
        (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
          (standardDeTurckVectorField (I := I) (M := M) g background t) x v)

@[simp] theorem standardDeTurckCorrection_apply
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    standardDeTurckCorrection (I := I) (M := M) g background t x u v = by
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      exact
        (g t).inner x
          (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
            (standardDeTurckVectorField (I := I) (M := M) g background t) x u) v +
        (g t).inner x u
          (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
            (standardDeTurckVectorField (I := I) (M := M) g background t) x v) := rfl

/-- A zero connection-difference tensor makes the standard DeTurck vector
zero at the specified point and time. -/
theorem standardDeTurckVectorField_apply_eq_zero_of_difference_eq_zero
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M)
    (hdiff :
      CovariantDerivative.difference
        ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) = 0) :
    standardDeTurckVectorField (I := I) (M := M) g background t x = 0 := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let B := standardDeTurckDifferenceBilinear (I := I) (M := M) g background t x
  let L : TM x →ₗ[ℝ] TM x →ₗ[ℝ] TM x :=
    { toFun := fun u => (B u).toLinearMap
      map_add' := by
        intro u v
        ext w
        exact congrArg (fun q : TM x →L[ℝ] TM x => q w) (B.map_add u v)
      map_smul' := by
        intro c u
        ext w
        exact congrArg (fun q : TM x →L[ℝ] TM x => q w) (B.map_smul c u) }
  change TensorProduct.lift L
      (InnerProductSpace.canonicalCovariantTensor (TM x)) = (0 : TM x)
  have hB : B = 0 := by
    ext u v
    change standardDeTurckDifferenceBilinear
      (I := I) (M := M) g background t x u v = 0
    rw [standardDeTurckDifferenceBilinear_apply]
    simpa using congrArg (fun D => D x v u) hdiff
  have hL : L = 0 := by
    ext u v
    change B u v = 0
    rw [hB]
    rfl
  rw [hL]
  refine TensorProduct.induction_on
    (motive := fun z =>
      TensorProduct.lift (0 : TM x →ₗ[ℝ] TM x →ₗ[ℝ] TM x) z = (0 : TM x))
    (InnerProductSpace.canonicalCovariantTensor (TM x)) ?_ ?_ ?_
  · exact LinearMap.map_zero _
  · intro u v
    simp
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

/-- If the background agrees pointwise with the chosen Levi-Civita
connection, the standard DeTurck vector vanishes at that point and time. -/
theorem standardDeTurckVectorField_apply_eq_zero_of_background_eq_chosenLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M)
    (hbackground : background t = (chosenLeviCivitaFamily (I := I) (M := M) g) t) :
    standardDeTurckVectorField (I := I) (M := M) g background t x = 0 := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  apply standardDeTurckVectorField_apply_eq_zero_of_difference_eq_zero
    (I := I) (M := M) g background t x
  simpa [hbackground] using
    (CovariantDerivative.difference_eq_zero_of_isLeviCivita
      (((chosenLeviCivitaFamily (I := I) (M := M) g) t))
      (((chosenLeviCivitaFamily (I := I) (M := M) g) t))
      ((chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) g) t)
      ((chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) g) t))

/-- If the background is Levi-Civita for the evolving metric, the standard
metric-contracted connection difference is zero. -/
theorem standardDeTurckVectorField_eq_zero_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    standardDeTurckVectorField (I := I) (M := M) g background = 0 := by
  funext t x
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  exact standardDeTurckVectorField_apply_eq_zero_of_difference_eq_zero
    (I := I) (M := M) g background t x
    (CovariantDerivative.difference_eq_zero_of_isLeviCivita
      (((chosenLeviCivitaFamily (I := I) (M := M) g) t))
      (background t)
      ((chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) g) t)
      (hbackground t))

/-- The standard DeTurck metric correction is symmetric in its tangent slots. -/
theorem standardDeTurckCorrection_symm
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    standardDeTurckCorrection (I := I) (M := M) g background t x u v =
      standardDeTurckCorrection (I := I) (M := M) g background t x v u := by
  rw [standardDeTurckCorrection_apply, standardDeTurckCorrection_apply]
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let nablaW :=
    ((chosenLeviCivitaFamily (I := I) (M := M) g) t)
      (standardDeTurckVectorField (I := I) (M := M) g background t) x
  have h₁ : (g t).inner x (nablaW u) v = (g t).inner x v (nablaW u) :=
    (g t).symm x _ _
  have h₂ : (g t).inner x u (nablaW v) = (g t).inner x (nablaW v) u :=
    (g t).symm x _ _
  rw [h₁, h₂]
  abel

/-- A vanishing standard DeTurck vector has vanishing metric correction at
the same time. -/
theorem standardDeTurckCorrection_apply_eq_zero_of_vector_eq_zero
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x)
    (hvector :
      standardDeTurckVectorField (I := I) (M := M) g background t = 0) :
    standardDeTurckCorrection (I := I) (M := M) g background t x u v = 0 := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hcovZero :
      (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
        (standardDeTurckVectorField (I := I) (M := M) g background t) x) = 0 := by
    rw [hvector]
    exact congrArg
      (fun A => A x)
      (CovariantDerivative.zero
        (cov := ((chosenLeviCivitaFamily (I := I) (M := M) g) t)))
  have hcovU :
      (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
        (standardDeTurckVectorField (I := I) (M := M) g background t) x u) = 0 := by
    simpa using congrArg (fun A => A u) hcovZero
  have hcovV :
      (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
        (standardDeTurckVectorField (I := I) (M := M) g background t) x v) = 0 := by
    simpa using congrArg (fun A => A v) hcovZero
  rw [standardDeTurckCorrection_apply, hcovU, hcovV]
  simp

/-- Pointwise agreement of the background with the chosen Levi-Civita
connection makes the standard correction vanish at that point and time. -/
theorem standardDeTurckCorrection_apply_eq_zero_of_background_eq_chosenLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x)
    (hbackground : background t = (chosenLeviCivitaFamily (I := I) (M := M) g) t) :
    standardDeTurckCorrection (I := I) (M := M) g background t x u v = 0 :=
  standardDeTurckCorrection_apply_eq_zero_of_vector_eq_zero
    (I := I) (M := M) g background t x u v
    (by
      funext y
      exact standardDeTurckVectorField_apply_eq_zero_of_background_eq_chosenLeviCivita
        (I := I) (M := M) g background t y hbackground)

/-- A Levi-Civita background makes the standard DeTurck correction vanish. -/
theorem standardDeTurckCorrection_eq_zero_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    standardDeTurckCorrection (I := I) (M := M) g background = 0 := by
  funext t x u v
  exact standardDeTurckCorrection_apply_eq_zero_of_vector_eq_zero
    (I := I) (M := M) g background t x u v
    (congrArg (fun W => W t)
      (standardDeTurckVectorField_eq_zero_of_isLeviCivita
        (I := I) (M := M) g background hbackground))

/-- The standard gauge-fixed Ricci-flow right-hand side `-2 Ric(g) + L_W g`.
The first summand is the intrinsic Ricci-flow operator, and the second is the
actual Levi-Civita covariant-derivative correction above. -/
def standardRicciDeTurckRHS
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) :
    MetricTensorFamily (I := I) (M := M) :=
  fun t x u v ↦
    intrinsicRicciFlowRHS (I := I) (M := M) g t x u v +
      standardDeTurckCorrection (I := I) (M := M) g background t x u v

@[simp] theorem standardRicciDeTurckRHS_apply
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    standardRicciDeTurckRHS (I := I) (M := M) g background t x u v =
      intrinsicRicciFlowRHS (I := I) (M := M) g t x u v +
        standardDeTurckCorrection (I := I) (M := M) g background t x u v := rfl

/-- Pointwise agreement of the background with the chosen Levi-Civita
connection reduces the standard Ricci--DeTurck right-hand side to the
intrinsic Ricci-flow right-hand side at that point and time. -/
theorem standardRicciDeTurckRHS_apply_eq_intrinsicRicciFlowRHS_of_background_eq_chosenLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x)
    (hbackground : background t = (chosenLeviCivitaFamily (I := I) (M := M) g) t) :
    standardRicciDeTurckRHS (I := I) (M := M) g background t x u v =
      intrinsicRicciFlowRHS (I := I) (M := M) g t x u v := by
  rw [standardRicciDeTurckRHS_apply,
    standardDeTurckCorrection_apply_eq_zero_of_background_eq_chosenLeviCivita
      (I := I) (M := M) g background t x u v hbackground,
    add_zero]

/-- The standard Ricci--DeTurck right-hand side is symmetric as a metric
two-tensor. -/
theorem standardRicciDeTurckRHS_symm
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    standardRicciDeTurckRHS (I := I) (M := M) g background t x u v =
      standardRicciDeTurckRHS (I := I) (M := M) g background t x v u := by
  rw [standardRicciDeTurckRHS_apply, standardRicciDeTurckRHS_apply,
    intrinsicRicciFlowRHS_symm (I := I) (M := M) g t x u v,
    standardDeTurckCorrection_symm (I := I) (M := M) g background t x u v]

/-- A Levi-Civita background reduces the standard Ricci--DeTurck equation to
the intrinsic Ricci-flow equation. -/
theorem standardRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    standardRicciDeTurckRHS (I := I) (M := M) g background =
      intrinsicRicciFlowRHS (I := I) (M := M) g := by
  funext t x u v
  have hcorr :
      standardDeTurckCorrection (I := I) (M := M) g background t x u v = 0 := by
    simpa using congrArg (fun F => F t x u v)
      (standardDeTurckCorrection_eq_zero_of_isLeviCivita
        (I := I) (M := M) g background hbackground)
  rw [standardRicciDeTurckRHS_apply, hcorr, add_zero]

/-- In the evolving metric's own chosen Levi-Civita gauge, the standard
DeTurck correction is identically zero. -/
theorem standardDeTurckCorrection_chosenLeviCivitaFamily_eq_zero
    (g : MetricFamily (I := I) (M := M)) :
    standardDeTurckCorrection (I := I) (M := M) g
      (chosenLeviCivitaFamily (I := I) (M := M) g) = 0 :=
  standardDeTurckCorrection_eq_zero_of_isLeviCivita
    (I := I) (M := M) g
    (chosenLeviCivitaFamily (I := I) (M := M) g)
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) g)

/-- In the evolving metric's own chosen Levi-Civita gauge, the standard
Ricci--DeTurck right-hand side is the intrinsic Ricci-flow right-hand side. -/
theorem standardRicciDeTurckRHS_chosenLeviCivitaFamily_eq_intrinsicRicciFlowRHS
    (g : MetricFamily (I := I) (M := M)) :
    standardRicciDeTurckRHS (I := I) (M := M) g
      (chosenLeviCivitaFamily (I := I) (M := M) g) =
        intrinsicRicciFlowRHS (I := I) (M := M) g :=
  standardRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita
    (I := I) (M := M) g
    (chosenLeviCivitaFamily (I := I) (M := M) g)
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) g)

end ChosenLeviCivita

end RicciFlow
