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

public import LeanPool.PoincareGeometry.AlmostSchur.LocalCurvatureTensor
public import LeanPool.PoincareGeometry.AlmostSchur.CurvatureVendor.Contractions
public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaBochner

/-! # Identifying the actual Bochner contraction with bundled Ricci

The right-slot localization theorem is proved from local regularity. Thus the
identification below has no global chart-coefficient or representative premise.
The curvature sign convention is unchanged: R(X,Y)Z = [∇X,∇Y]Z − ∇[X,Y]Z.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)
local instance bundledRicciFiniteDimensional (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- The two independently defined raw commutators have exactly the same sign. -/
theorem rawCurvature_eq_curvatureAux (cov : CovariantDerivative I E TM)
    (X Y Z : Π x, TM x) (x : M) :
    rawCurvature cov X Y Z x = cov.curvatureAuxAlmostSchur X Y Z x := rfl

/-- Local C³ scalar regularity suffices to identify any chart contraction with
the actual fibrewise Ricci tensor evaluated twice on the gradient. -/
theorem chartRawRicciGradient_eq_ricciCurvature
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 3 f x)
    {ι : Type} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (hx : x ∈ e.baseSet) :
    chartRawRicciGradient cov f e b x =
      cov.ricciCurvatureAlmostSchur x (gradient (I := I) f x) (gradient (I := I) f x) := by
  let G := gradient (I := I) f
  have hG : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% G) x :=
    contMDiffAt_gradient (I := I) 2 hf
  let A (y : M) : TM y →L[ℝ] TM y :=
    (cov.ricciEndomorphismAlmostSchur y (G y) (G y)).toContinuousLinearMap
  rw [CovariantDerivative.ricciCurvature_applyAlmostSchur]
  change chartRawRicciGradient cov f e b x = LinearMap.trace ℝ (TM x) (A x).toLinearMap
  rw [trace_eq_sum_localFrameCoeff e b A x hx]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (e.localFrameCoeff I b i x)
  change rawCurvature cov (e.localFrame b i) G G x =
    cov.curvatureTensorAlmostSchur x (e.localFrame b i x) (G x) (G x)
  rw [rawCurvature_eq_curvatureAux]
  exact curvatureAux_eq_curvatureTensor_of_contMDiffAt cov
    (contMDiffAt_localFrame_of_mem 2 e b i hx) hG hG

/-- The canonical raw gradient contraction is bundled Ricci, from local C³
regularity alone; no metric-compatibility or torsion premise is needed here. -/
theorem rawRicciGradient_eq_ricciCurvature
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 3 f x) :
    rawRicciGradient cov f x =
      cov.ricciCurvatureAlmostSchur x (gradient (I := I) f x) (gradient (I := I) f x) :=
  chartRawRicciGradient_eq_ricciCurvature cov hf (trivializationAt E TM x)
    (stdOrthonormalBasis ℝ E).toBasis (mem_baseSet_trivializationAt E TM x)

/-- Bochner flux for the constructed Levi–Civita connection, with genuine
bundled Ricci in place of the raw contraction. -/
theorem leviCivita_divergence_bochnerFlux_ricci
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) (x : M) :
    let cov := leviCivitaConnection (I := I) (M := M)
    divergence cov (bochnerFlux cov f) x = (laplacian cov f x) ^ 2 -
      hessianNormSq cov f x -
      cov.ricciCurvatureAlmostSchur x (gradient (I := I) f x) (gradient (I := I) f x) := by
  dsimp only
  rw [leviCivita_divergence_bochnerFlux hf x,
    rawRicciGradient_eq_ricciCurvature _ (hf x)]

end AlmostSchur
