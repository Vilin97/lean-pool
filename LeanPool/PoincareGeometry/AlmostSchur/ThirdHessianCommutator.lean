/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.CovariantAlongRegularity
public import LeanPool.PoincareGeometry.AlmostSchur.Hessian
public import LeanPool.PoincareGeometry.AlmostSchur.MetricConnectionCoordinates
public import LeanPool.PoincareGeometry.AlmostSchur.TorsionCoordinates
public import LeanPool.PoincareGeometry.AlmostSchur.GradientRegularity

/-! # The corrected third Hessian and its raw curvature commutator

All derivatives below use the actual connection. The curvature expression is
the explicit commutator on sections, not yet a bundled curvature tensor or Ricci
contraction. The C³ theorem discharges the gradient regularity requirement.
-/

@[expose] public noncomputable section
open Bundle FiberBundle VectorField
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The raw curvature commutator on actual tangent fields, with sign convention
`R(X,Y)Z = ∇X ∇Y Z - ∇Y ∇X Z - ∇[X,Y] Z`. -/
def rawCurvature (cov : CovariantDerivative I E TM) (X Y Z : Π x, TM x) :
    Π x, TM x := fun x ↦
  covariantAlong cov X (covariantAlong cov Y Z) x -
    covariantAlong cov Y (covariantAlong cov X Z) x -
    cov Z x (mlieBracket I X Y x)

/-- Differentiate the Hessian pairing and subtract both slot corrections. -/
def thirdHessian (cov : CovariantDerivative I E TM) (f : M → ℝ)
    (X Y W : Π x, TM x) (x : M) : ℝ :=
  mvfderiv I (fun y ↦ hessian cov f y (Y y) (W y)) x (X x) -
    hessian cov f x (covariantAlong cov X Y x) (W x) -
    hessian cov f x (Y x) (covariantAlong cov X W x)
omit [CompleteSpace E] in
/-- Metric compatibility identifies the corrected scalar derivative with the
corrected second covariant derivative of the actual gradient. -/
theorem thirdHessian_eq_inner (cov : CovariantDerivative I E TM)
    (hm : tangentMetricCompatible cov) (f : M → ℝ)
    (X Y W : Π x, TM x) (x : M)
    (hYG : MDiffAt (T% (covariantAlong cov Y (gradient (I := I) f))) x)
    (hW : MDiffAt (T% W) x) :
    thirdHessian cov f X Y W x =
      inner ℝ (covariantAlong cov X (covariantAlong cov Y (gradient (I := I) f)) x -
        cov (gradient (I := I) f) x (covariantAlong cov X Y x)) (W x) := by
  have h := CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq hm X hYG hW
  change mvfderiv I (fun y ↦ inner ℝ
      (covariantAlong cov Y (gradient (I := I) f) y) (W y)) x (X x) =
    inner ℝ (covariantAlong cov X (covariantAlong cov Y (gradient (I := I) f)) x)
      (W x) + inner ℝ (covariantAlong cov Y (gradient (I := I) f) x)
      (covariantAlong cov X W x) at h
  unfold thirdHessian
  simp only [hessian_apply]
  simp only [covariantAlong] at h ⊢
  rw [h, inner_sub_left]
  ring

/-- Antisymmetrizing the corrected third Hessian gives the explicit raw
curvature paired with the last field. Only torsion at the point is needed. -/
theorem thirdHessian_sub_eq_rawCurvature (cov : CovariantDerivative I E TM)
    (hm : tangentMetricCompatible cov) (f : M → ℝ)
    (X Y W : Π x, TM x) (x : M) (ht : cov.torsion x = 0)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hW : MDiffAt (T% W) x)
    (hXG : MDiffAt (T% (covariantAlong cov X (gradient (I := I) f))) x)
    (hYG : MDiffAt (T% (covariantAlong cov Y (gradient (I := I) f))) x) :
    thirdHessian cov f X Y W x - thirdHessian cov f Y X W x =
      inner ℝ (rawCurvature cov X Y (gradient (I := I) f) x) (W x) := by
  rw [thirdHessian_eq_inner cov hm f X Y W x hYG hW,
    thirdHessian_eq_inner cov hm f Y X W x hXG hW]
  have hT := cov.torsion_apply hX hY
  rw [ht] at hT
  have hbr : mlieBracket I X Y x = covariantAlong cov X Y x -
      covariantAlong cov Y X x := by
    change 0 = covariantAlong cov X Y x - covariantAlong cov Y X x -
      mlieBracket I X Y x at hT
    exact (sub_eq_zero.mp hT.symm).symm
  simp only [rawCurvature, hbr, map_sub, inner_sub_left]
  ring

/-- C³ scalar data and a C¹ connection discharge all differentiated-gradient
premises of the actual third-Hessian commutator. -/
theorem thirdHessian_sub_eq_rawCurvature_of_contMDiff
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    {X Y W : Π x, TM x}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% W)) (x : M) :
    thirdHessian cov f X Y W x - thirdHessian cov f Y X W x =
      inner ℝ (rawCurvature cov X Y (gradient (I := I) f) x) (W x) := by
  have hG := contMDiff_gradient (I := I) 2 hf
  exact thirdHessian_sub_eq_rawCurvature cov hm f X Y W x (congrFun ht x)
    ((hX x).mdifferentiableAt (by norm_num))
    ((hY x).mdifferentiableAt (by norm_num))
    ((hW x).mdifferentiableAt (by norm_num))
    (((contMDiff_covariantAlong 1 cov hX hG) x).mdifferentiableAt (by norm_num))
    (((contMDiff_covariantAlong 1 cov hY hG) x).mdifferentiableAt (by norm_num))

end AlmostSchur
