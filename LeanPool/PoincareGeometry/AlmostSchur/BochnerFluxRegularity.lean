/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.CovariantAlongRegularity
public import LeanPool.PoincareGeometry.AlmostSchur.GradientRegularity
public import LeanPool.PoincareGeometry.AlmostSchur.Hessian

/-! # Genuine regularity of the Bochner flux

Trace regularity is proved by conjugation into tangent coordinates. In
particular C¹ regularity of the Laplacian is not assumed as PDE data.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff Topology
namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
local notation "TM" => (TangentSpace I : M → Type _)

local instance bochnerFluxFiniteDimensionalTangentSpace (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- Trace as a continuous linear functional on model-space endomorphisms. -/
def endomorphismTrace : (E →L[ℝ] E) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ LinearMap.trace ℝ E A.toLinearMap
      map_add' := by intros; simp
      map_smul' := by intros; simp }

/-- Conjugating a tangent endomorphism into any valid tangent chart preserves trace. -/
theorem trace_inCoordinates (A : Π y, TM y →L[ℝ] TM y) (c y : M)
    (hy : y ∈ (trivializationAt E TM c).baseSet) :
    endomorphismTrace (ContinuousLinearMap.inCoordinates E TM E TM c y c y (A y)) =
      LinearMap.trace ℝ (TM y) (A y).toLinearMap := by
  let e := trivializationAt E TM c
  rw [ContinuousLinearMap.inCoordinates_eq hy hy]
  change LinearMap.trace ℝ E
    ((e.continuousLinearEquivAt ℝ y hy).toContinuousLinearMap.comp
      ((A y).comp (e.continuousLinearEquivAt ℝ y hy).symm.toContinuousLinearMap)).toLinearMap = _
  exact LinearMap.trace_conj' (A y).toLinearMap (e.linearEquivAt ℝ y hy)

/-- The scalar trace of a Cᵏ tangent endomorphism section is Cᵏ. -/
theorem contMDiff_trace_endomorphism (k : ℕ∞ω)
    [ContMDiffVectorBundle k E TM I] (A : Π y, TM y →L[ℝ] TM y)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) k
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y))) :
    ContMDiff I 𝓘(ℝ, ℝ) k (fun y ↦ LinearMap.trace ℝ (TM y) (A y).toLinearMap) := by
  intro x
  have hc := ((contMDiffAt_hom_bundle _).mp (hA x)).2
  have ht := (endomorphismTrace (E := E)).contMDiff.contMDiffAt.comp x hc
  apply ht.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E TM x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E TM x)] with y hy
  exact (trace_inCoordinates A x y hy).symm

variable [RiemannianBundle (TangentSpace I : M → Type _)]

/-- The geometric Bochner flux, built from the actual gradient and connection. -/
def bochnerFlux (cov : CovariantDerivative I E TM) (f : M → ℝ) : Π x, TM x :=
  fun x ↦ laplacian cov f x • gradient (I := I) f x -
    covariantAlong cov (gradient (I := I) f) (gradient (I := I) f) x

/-- C³ scalar data and a C² metric yield a C¹ Laplacian for a C¹ connection. -/
theorem contMDiff_laplacian [ContMDiffVectorBundle 1 E TM I]
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) :
    ContMDiff I 𝓘(ℝ, ℝ) 1 (laplacian cov f) := by
  have hG := contMDiff_gradient (I := I) 2 hf
  have hc := (CovariantDerivative.ContMDiffCovariantDerivative.contMDiff
    (cov := cov) (k := 1)).contMDiff hG.contMDiffOn
  exact contMDiff_trace_endomorphism 1 _ (contMDiffOn_univ.mp hc)

/-- The actual flux has the C¹ regularity required by global Green. -/
theorem contMDiff_bochnerFlux [ContMDiffVectorBundle 1 E TM I]
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% (bochnerFlux cov f)) := by
  have hG := contMDiff_gradient (I := I) 2 hf
  have hG1 := hG.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  exact ((contMDiff_laplacian cov hf).smul_section hG1).sub_section
    (contMDiff_covariantAlong 1 cov hG1 hG)

end AlmostSchur
