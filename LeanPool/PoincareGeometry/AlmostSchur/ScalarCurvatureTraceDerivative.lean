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

public import LeanPool.PoincareGeometry.AlmostSchur.RicciTraceDerivative

/-! # Differentiating actual scalar curvature via metric-raised Ricci

The raised operator is defined by Riesz duality from the bundled Ricci tensor.
Its trace is proved to be the existing scalarCurvatureAlmostSchur, then differentiated
using the moving-frame trace theorem.
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
local instance scalarDerivativeFiniteDimensional (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- Metric-raised Ricci, constructed by Riesz duality rather than stipulated. -/
def ricciRaisedEndomorphism (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] (x : M) : TM x →L[ℝ] TM x :=
  InnerProductSpace.continuousLinearMapOfBilin
    (((LinearMap.toContinuousLinearMap : (TM x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (TM x →L[ℝ] ℝ)).toLinearMap.comp
      (cov.ricciCurvatureAlmostSchur x)).toContinuousLinearMap)

/-- The raised operator has exactly the prescribed Ricci pairing. -/
theorem inner_ricciRaisedEndomorphism (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] (x : M) (u v : TM x) :
    inner ℝ (ricciRaisedEndomorphism cov x u) v = cov.ricciCurvatureAlmostSchur x u v := by
  unfold ricciRaisedEndomorphism
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

/-- The existing scalar curvature is the trace of actual metric-raised Ricci. -/
theorem scalarCurvature_eq_trace_ricciRaisedEndomorphism
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1] (x : M) :
    cov.scalarCurvatureAlmostSchur x = LinearMap.trace ℝ (TM x) (ricciRaisedEndomorphism cov x).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (TM x))]
  unfold CovariantDerivative.scalarCurvatureAlmostSchur
  apply Finset.sum_congr rfl
  intro i _
  change cov.ricciCurvatureAlmostSchur x _ _ = inner ℝ _ (ricciRaisedEndomorphism cov x _)
  rw [real_inner_comm, inner_ricciRaisedEndomorphism]

/-- The actual raised Ricci operator is a C¹ hom-bundle section. -/
theorem contMDiffAt_ricciRaisedEndomorphism_one
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0) (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := fun z ↦ TM z →L[ℝ] TM z)
        y (ricciRaisedEndomorphism cov y)) x := by
  let b := Module.finBasis ℝ E
  let e := trivializationAt E TM x
  have hx := mem_baseSet_trivializationAt E TM x
  apply contMDiffAt_endomorphism_of_localFrame 1 _ x b
  intro i
  apply contMDiffAt_section_of_inner_localFrame b x x (mem_chart_source H x)
  intro j
  simp only [inner_ricciRaisedEndomorphism]
  exact contMDiffAt_ricciCurvature_apply_one cov hm ht
    (contMDiffAt_localFrame_of_mem 3 e b i hx)
    (contMDiffAt_localFrame_of_mem 3 e b j hx)

/-- Actual scalar curvature has the differentiability needed in contracted Bianchi. -/
theorem contMDiffAt_scalarCurvature_one
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0) (x : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) 1 cov.scalarCurvatureAlmostSchur x := by
  let e := trivializationAt E TM x
  let b := Module.finBasis ℝ E
  have hx := mem_baseSet_trivializationAt E TM x
  have hA := contMDiffAt_ricciRaisedEndomorphism_one cov hm ht x
  have hs : ContMDiffAt I 𝓘(ℝ, ℝ) 1
      (fun y ↦ ∑ i, e.localFrameCoeff I b i y
        (ricciRaisedEndomorphism cov y (e.localFrame b i y))) x :=
    ContMDiffAt.sum (fun i _ ↦ contMDiffAt_localFrameCoeff b hx
      (hA.clm_bundle_apply (contMDiffAt_localFrame_of_mem 1 e b i hx)) i)
  apply hs.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  rw [scalarCurvature_eq_trace_ricciRaisedEndomorphism]
  exact trace_eq_sum_localFrameCoeff e b (ricciRaisedEndomorphism cov) y hy

/-- The genuine scalar-curvature differential equals the corrected moving-frame
trace derivative of the raised Ricci operator. -/
theorem mvfderiv_scalarCurvature_eq_contraction
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (X : Π y, TM y) (x : M)
    {ι : Type} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (hx : x ∈ e.baseSet) :
    mvfderiv I cov.scalarCurvatureAlmostSchur x (X x) =
      ∑ i, e.localFrameCoeff I b i x
        (cov (fun y ↦ ricciRaisedEndomorphism cov y (e.localFrame b i y)) x (X x) -
          ricciRaisedEndomorphism cov x (cov (e.localFrame b i) x (X x))) := by
  have he : cov.scalarCurvatureAlmostSchur =
      (fun y ↦ LinearMap.trace ℝ (TM y) (ricciRaisedEndomorphism cov y).toLinearMap) :=
    funext (scalarCurvature_eq_trace_ricciRaisedEndomorphism cov)
  rw [he]
  exact mvfderiv_trace_eq_covariant_contraction cov e b (ricciRaisedEndomorphism cov) X x hx
    ((contMDiffAt_ricciRaisedEndomorphism_one cov hm ht x).mdifferentiableAt (by norm_num))

end AlmostSchur
