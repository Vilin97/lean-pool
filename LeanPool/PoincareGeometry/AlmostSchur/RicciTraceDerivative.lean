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

public import LeanPool.PoincareGeometry.AlmostSchur.CurvatureRicciRegularity

/-! # Actual Ricci differentiation as a curvature contraction

The scalar differential is the manifold differential of bundled Ricci paired
with fields. The two Ricci slot corrections and the moving-frame correction
are explicit, with no parallel-frame assumption.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 3 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)
local instance ricciDerivativeFiniteDimensional (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- Corrected differentiation of actual bundled curvature on tangent fields. -/
def curvatureDirectionalDerivative (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] (X U Y Z : Π y, TM y) (x : M) : TM x :=
  cov (fun y ↦ cov.curvatureTensorAlmostSchur y (U y) (Y y) (Z y)) x (X x) -
    cov.curvatureTensorAlmostSchur x (cov U x (X x)) (Y x) (Z x) -
    cov.curvatureTensorAlmostSchur x (U x) (cov Y x (X x)) (Z x) -
    cov.curvatureTensorAlmostSchur x (U x) (Y x) (cov Z x (X x))

/-- Corrected differential of the genuine Ricci scalar pairing. -/
def ricciDirectionalDerivative (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] (X Y Z : Π y, TM y) (x : M) : ℝ :=
  mvfderiv I (fun y ↦ cov.ricciCurvatureAlmostSchur y (Y y) (Z y)) x (X x) -
    cov.ricciCurvatureAlmostSchur x (cov Y x (X x)) (Z x) -
    cov.ricciCurvatureAlmostSchur x (Y x) (cov Z x (X x))

/-- Differentiating Ricci commutes with its actual curvature trace, including
the connection correction for the moving first/output trace slots. -/
theorem mvfderiv_ricciCurvature_eq_contraction
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (X Y Z : Π y, TM y) (x : M)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Z) x)
    {ι : Type} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (hx : x ∈ e.baseSet) :
    mvfderiv I (fun y ↦ cov.ricciCurvatureAlmostSchur y (Y y) (Z y)) x (X x) =
      ∑ i, e.localFrameCoeff I b i x
        (cov (fun y ↦ cov.curvatureTensorAlmostSchur y (e.localFrame b i y) (Y y) (Z y)) x (X x) -
          cov.curvatureTensorAlmostSchur x (cov (e.localFrame b i) x (X x)) (Y x) (Z x)) := by
  have hA := (contMDiffAt_ricciTraceEndomorphism_one cov hm ht hY hZ).mdifferentiableAt
    (by norm_num)
  exact mvfderiv_trace_eq_covariant_contraction cov e b
    (ricciTraceEndomorphism cov Y Z) X x hx hA

/-- The corrected Ricci derivative is the first/output contraction of the
corrected actual curvature derivative. No derivative-trace identity is assumed. -/
theorem ricciDirectionalDerivative_eq_contraction
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (X Y Z : Π y, TM y) (x : M)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Z) x)
    {ι : Type} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (hx : x ∈ e.baseSet) :
    ricciDirectionalDerivative cov X Y Z x =
      ∑ i, e.localFrameCoeff I b i x
        (curvatureDirectionalDerivative cov X (e.localFrame b i) Y Z x) := by
  have h1 := trace_eq_sum_localFrameCoeff e b
    (ricciTraceEndomorphism cov (cov.alongAlmostSchur X Y) Z) x hx
  have h2 := trace_eq_sum_localFrameCoeff e b
    (ricciTraceEndomorphism cov Y (cov.alongAlmostSchur X Z)) x hx
  unfold ricciDirectionalDerivative
  rw [mvfderiv_ricciCurvature_eq_contraction cov hm ht X Y Z x hY hZ e b hx]
  change _ - LinearMap.trace ℝ (TM x)
      (ricciTraceEndomorphism cov (cov.alongAlmostSchur X Y) Z x).toLinearMap -
      LinearMap.trace ℝ (TM x) (ricciTraceEndomorphism cov Y (cov.alongAlmostSchur X Z) x).toLinearMap = _
  rw [h1, h2]
  simp only [curvatureDirectionalDerivative, map_sub, Finset.sum_sub_distrib]
  rfl

end AlmostSchur
