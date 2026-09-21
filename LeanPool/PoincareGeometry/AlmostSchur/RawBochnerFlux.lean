/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.ThirdHessianSymmetry
public import LeanPool.PoincareGeometry.AlmostSchur.CovariantTraceDerivative
public import LeanPool.PoincareGeometry.AlmostSchur.DivergenceCoordinates
public import LeanPool.PoincareGeometry.AlmostSchur.HessianNorm

/-! # Bochner flux with an explicit raw curvature contraction

The contraction uses a genuine moving local frame and its dual coefficients.
It is not a definition of a bundled Ricci tensor. The connection terms are
retained and cancel by the proved covariant trace differentiation theorem.
-/

@[expose] public noncomputable section
open Bundle FiberBundle VectorField
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)
local instance rawBochnerFiniteDimensionalTangentSpace (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

omit [I.Boundaryless] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Torsion-freeness identifies the raw commutator with both corrected slots. -/
theorem rawCurvature_eq_corrected_commutator
    (cov : CovariantDerivative I E TM) (X Y Z : Π x, TM x) (x : M)
    (ht : cov.torsion x = 0) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    rawCurvature cov X Y Z x =
      (covariantAlong cov X (covariantAlong cov Y Z) x -
        cov Z x (covariantAlong cov X Y x)) -
      (covariantAlong cov Y (covariantAlong cov X Z) x -
        cov Z x (covariantAlong cov Y X x)) := by
  have hT := cov.torsion_apply hX hY
  rw [ht] at hT
  have hbr : mlieBracket I X Y x = covariantAlong cov X Y x -
      covariantAlong cov Y X x := by
    change 0 = covariantAlong cov X Y x - covariantAlong cov Y X x -
      mlieBracket I X Y x at hT
    exact (sub_eq_zero.mp hT.symm).symm
  simp only [rawCurvature, hbr, map_sub]
  abel

/-- The square of the actual gradient derivative contracts to the Hessian
norm because its symmetry was proved from metric compatibility and torsion. -/
theorem trace_gradientDerivative_sq (cov : CovariantDerivative I E TM)
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (x : M) :
    LinearMap.trace ℝ (TM x)
      ((cov (gradient (I := I) f) x).comp (cov (gradient (I := I) f) x)).toLinearMap =
      hessianNormSq cov f x := by
  let A := cov (gradient (I := I) f) x
  have hs : A = A.adjoint := (ContinuousLinearMap.eq_adjoint_iff A A).mpr (by
    intro u v
    have h := hessian_symmetric cov hm ht hf x u v
    simpa only [hessian_apply, real_inner_comm] using h)
  change LinearMap.trace ℝ (TM x) (A.comp A).toLinearMap =
    LinearMap.trace ℝ (TM x) (A.adjoint.comp A).toLinearMap
  rw [← hs]

/-- Raw curvature contracted in the first/output slots using a genuine local
frame and its dual, with the actual gradient in the remaining slots. -/
def chartRawRicciGradient {ι : Type} [Fintype ι]
    (cov : CovariantDerivative I E TM) (f : M → ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (x : M) : ℝ :=
  ∑ i, e.localFrameCoeff I b i x
    (rawCurvature cov (e.localFrame b i) (gradient (I := I) f) (gradient (I := I) f) x)

/-- The actual raw contraction is the difference of the acceleration
divergence, Hessian norm, and the directional derivative of the Laplacian. -/
theorem chartRawRicciGradient_eq [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    {ι : Type} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (x : M) (hx : x ∈ e.baseSet) :
    chartRawRicciGradient cov f e b x =
      divergence cov (covariantAlong cov (gradient (I := I) f) (gradient (I := I) f)) x -
        hessianNormSq cov f x - mvfderiv I (laplacian cov f) x (gradient (I := I) f x) := by
  classical
  let G := gradient (I := I) f
  let A := cov G
  have hG := contMDiff_gradient (I := I) 2 hf
  have hGd : MDiffAt (T% G) x := (hG x).mdifferentiableAt (by norm_num)
  have hA := (contMDiffOn_univ.mp
    ((CovariantDerivative.ContMDiffCovariantDerivative.contMDiff
      (cov := cov) (k := 1)).contMDiff hG.contMDiffOn) x).mdifferentiableAt (by norm_num)
  have hF (i : ι) : MDiffAt (T% (e.localFrame b i)) x :=
    (contMDiffAt_localFrame_of_mem 1 e b i hx).mdifferentiableAt (by simp)
  have hterm (i : ι) :
      e.localFrameCoeff I b i x (rawCurvature cov (e.localFrame b i) G G x) =
      e.localFrameCoeff I b i x
        (cov (covariantAlong cov G G) x (e.localFrame b i x)) -
      e.localFrameCoeff I b i x (A x (A x (e.localFrame b i x))) -
      e.localFrameCoeff I b i x
        (cov (fun y ↦ A y (e.localFrame b i y)) x (G x) -
          A x (cov (e.localFrame b i) x (G x))) := by
    rw [rawCurvature_eq_corrected_commutator cov _ G G x (congrFun ht x) (hF i) hGd]
    have he : covariantAlong cov (e.localFrame b i) G =
        (fun y ↦ A y (e.localFrame b i y)) := rfl
    dsimp only [covariantAlong, A]
    simp only [map_sub]
    rw [he]
  have hd := trace_eq_sum_localFrameCoeff e b (cov (covariantAlong cov G G)) x hx
  have hs := trace_eq_sum_localFrameCoeff e b (fun y ↦ (A y).comp (A y)) x hx
  have ht' := mvfderiv_trace_eq_covariant_contraction cov e b A G x hx hA
  have hnorm := trace_gradientDerivative_sq cov hm ht (hf.of_le (by norm_num)) x
  change (∑ i, e.localFrameCoeff I b i x (rawCurvature cov (e.localFrame b i) G G x)) = _
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← hd, ← ht']
  have hs' : (∑ i, e.localFrameCoeff I b i x (A x (A x (e.localFrame b i x)))) =
      hessianNormSq cov f x := by
    exact hs.symm.trans hnorm
  rw [hs']
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Subtraction for the actual divergence, derived from connection additivity
on differentiable sections. -/
theorem divergence_sub (cov : CovariantDerivative I E TM)
    (X Y : Π x, TM x) (x : M) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    divergence cov (fun y ↦ X y - Y y) x = divergence cov X x - divergence cov Y x := by
  have hsub : MDiffAt (T% (X - Y)) x := mdifferentiableAt_sub_section hX hY
  have h := cov.isCovariantDerivativeOnUniv.add hsub hY
  rw [sub_add_cancel] at h
  have hc : cov (X - Y) x = cov X x - cov Y x := eq_sub_iff_add_eq.mpr h.symm
  change LinearMap.trace ℝ (TM x) (cov (X - Y) x).toLinearMap = _
  rw [hc]
  simp only [ContinuousLinearMap.toLinearMap_sub, map_sub, divergence]

/-- Pointwise Bochner flux identity with the explicit raw curvature contraction
in any genuine local frame. All scalar and field regularity is derived. -/
theorem divergence_bochnerFlux_eq_chartRawRicciGradient
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    {ι : Type} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (x : M) (hx : x ∈ e.baseSet) :
    divergence cov (bochnerFlux cov f) x = (laplacian cov f x) ^ 2 -
      hessianNormSq cov f x - chartRawRicciGradient cov f e b x := by
  have hG := contMDiff_gradient (I := I) 2 hf
  have hG1 := hG.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hl := contMDiff_laplacian cov hf
  have hacc := contMDiff_covariantAlong 1 cov hG1 hG
  change divergence cov (fun y ↦ (laplacian cov f • gradient (I := I) f) y -
    covariantAlong cov (gradient (I := I) f) (gradient (I := I) f) y) x = _
  rw [divergence_sub cov _ _ x
    (((hl.smul_section hG1) x).mdifferentiableAt (by simp))
    ((hacc x).mdifferentiableAt (by simp))]
  change divergence cov (fun y ↦ laplacian cov f y • gradient (I := I) f y) x -
    divergence cov (covariantAlong cov (gradient (I := I) f) (gradient (I := I) f)) x = _
  rw [divergence_smul cov _ _ x ((hl x).mdifferentiableAt (by simp))
      ((hG1 x).mdifferentiableAt (by simp)), divergence_gradient,
    chartRawRicciGradient_eq cov hm ht hf e b x hx]
  ring

/-- Canonical raw gradient contraction. This is computed from the actual
commutator; identification with a bundled Ricci tensor remains separate. -/
def rawRicciGradient (cov : CovariantDerivative I E TM) (f : M → ℝ) (x : M) : ℝ :=
  chartRawRicciGradient cov f (trivializationAt E TM x)
    (stdOrthonormalBasis ℝ E).toBasis x

/-- The Bochner flux identity with the canonical actual raw contraction. -/
theorem divergence_bochnerFlux [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) (x : M) :
    divergence cov (bochnerFlux cov f) x = (laplacian cov f x) ^ 2 -
      hessianNormSq cov f x - rawRicciGradient cov f x :=
  divergence_bochnerFlux_eq_chartRawRicciGradient cov hm ht hf
    (trivializationAt E TM x) (stdOrthonormalBasis ℝ E).toBasis x
    (mem_baseSet_trivializationAt E TM x)

/-- The raw gradient contraction does not depend on the chosen local frame. -/
theorem rawRicciGradient_eq_chart [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    {ι : Type} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (x : M) (hx : x ∈ e.baseSet) :
    rawRicciGradient cov f x = chartRawRicciGradient cov f e b x := by
  have h1 := divergence_bochnerFlux cov hm ht hf x
  have h2 := divergence_bochnerFlux_eq_chartRawRicciGradient cov hm ht hf e b x hx
  linarith

end AlmostSchur
