/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.MetricConnectionCoordinates

/-!
# Intrinsic divergence in tangent coordinates

The divergence is the trace of the supplied connection on the actual tangent
fiber. Conjugation invariance of trace identifies it with the coordinate
connection divergence.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

local instance divergenceFiniteDimensionalTangentSpace (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x

/-- Intrinsic divergence: trace on the actual tangent fiber. -/
def divergence (cov : CovariantDerivative I E TM) (X : Π x : M, TM x) (x : M) : ℝ :=
  LinearMap.trace ℝ (TM x) (cov X x).toLinearMap

/-- The divergence product rule is the trace of the connection Leibniz rule. -/
theorem divergence_smul (cov : CovariantDerivative I E TM)
    (f : M → ℝ) (X : Π x : M, TM x) (x : M)
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) :
    divergence cov (fun y => f y • X y) x =
      f x * divergence cov X x + mvfderiv I f x (X x) := by
  change LinearMap.trace ℝ (TM x) (cov (f • X) x).toLinearMap = _
  rw [cov.isCovariantDerivativeOnUniv.leibniz hX hf]
  simp [divergence, LinearMap.trace_smulRight]

/-- Finite additivity of intrinsic divergence. -/
theorem divergence_sum (cov : CovariantDerivative I E TM)
    {κ : Type*} (s : Finset κ) (X : κ → Π x : M, TM x) (x : M)
    (hX : ∀ i ∈ s, MDiffAt (T% (X i)) x) :
    divergence cov (fun y => ∑ i ∈ s, X i y) x = ∑ i ∈ s, divergence cov (X i) x := by
  rw [divergence, covariantDerivative_sum cov s X x hX]
  simp [divergence]

/-- Intrinsic divergence vanishes away from the topological support of the
field, because a connection depends only on the local section. -/
theorem divergence_eq_zero_of_notMem_tsupport
    (cov : CovariantDerivative I E TM) (X : Π x : M, TM x) (x : M)
    (hX : MDiffAt (T% X) x) (hx : x ∉ tsupport (fun y => ‖X y‖)) :
    divergence cov X x = 0 := by
  have he : ∀ᶠ y in 𝓝 x, X y = 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    exact norm_eq_zero.mp hy
  have hc := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hX
    (mdifferentiableAt_zeroSection ..) (by simp) he
  rw [divergence, hc]
  change LinearMap.trace ℝ (TM x) (cov 0 x).toLinearMap = 0
  simp only [congrFun cov.zero x, Pi.zero_apply, ContinuousLinearMap.toLinearMap_zero, map_zero]

/-- The Laplace–Beltrami trace is the divergence of the actual gradient. -/
theorem divergence_gradient (cov : CovariantDerivative I E TM) (f : M → ℝ) (x : M) :
    divergence cov (gradient (I := I) f) x = laplacian cov f x := rfl

/-- The genuine coordinate vector field, defined using the tangent chart. -/
def coordinateVectorField (c : M) (X : Π x : M, TM x) (z : E) : E :=
  (trivializationAt E TM c).continuousLinearMapAt ℝ ((extChartAt I c).symm z)
    (X ((extChartAt I c).symm z))

/-- Coordinate representation preserves C1 regularity on the chart domain. -/
theorem contDiffOn_coordinateVectorField (c : M) (X : Π x : M, TM x)
    (hX : CMDiff[(chartAt H c).source] 1 (T% X)) :
    ContDiffOn ℝ 1 (coordinateVectorField (I := I) c X) (extChartAt I c).target := by
  classical
  let e := trivializationAt E TM c
  let b := (stdOrthonormalBasis ℝ E).toBasis
  have heq : coordinateVectorField (I := I) c X =
      fun z => ∑ i, (e.localFrameCoeff I b i ((extChartAt I c).symm z)
        (X ((extChartAt I c).symm z))) • b i := by
    funext z
    exact (localFrameCoeff_sum_coordinates e b X _).symm
  rw [heq]
  intro z hz
  let x := (extChartAt I c).symm z
  have hx : x ∈ (chartAt H c).source := by
    simpa only [extChartAt_source] using (extChartAt I c).map_target hz
  have hxe : x ∈ e.baseSet := hx
  have hXa := (hX x hx).contMDiffAt ((chartAt H c).open_source.mem_nhds hx)
  have hi : CMDiffAt 1 (extChartAt I c).symm z :=
    (contMDiffOn_extChartAt_symm c z hz).contMDiffAt ((isOpen_extChartAt_target c).mem_nhds hz)
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.sum
  intro i _
  have ha := contMDiffAt_localFrameCoeff (I := I) b hxe hXa i
  exact ((ha.comp z hi).contDiffAt).smul_const (b i)

/-- The coordinate connection coefficients, evaluated at coordinate points. -/
def coordinateConnection (cov : CovariantDerivative I E TM)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) (z : E) :
    E →L[ℝ] E →L[ℝ] E :=
  frameConnectionCoefficients cov (trivializationAt E TM c) b ((extChartAt I c).symm z)

/-- Directional derivatives along the coordinate vector field are the
intrinsic manifold differential applied to the original field. -/
theorem fderiv_chart_coordinateVectorField (f : M → ℝ) (X : Π x : M, TM x)
    (c x : M) (hx : x ∈ (chartAt H c).source) (hf : MDiffAt f x) :
    fderiv ℝ (f ∘ (extChartAt I c).symm) (extChartAt I c x)
      (coordinateVectorField (I := I) c X (extChartAt I c x)) = mvfderiv I f x (X x) := by
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  dsimp only [coordinateVectorField]
  rw [(extChartAt I c).left_inv hx', fderiv_chart_comp f c x hx hf,
    (trivializationAt E TM c).symmL_continuousLinearMapAt hx]

/-- A C1 function on the manifold chart is C1 after passing to coordinates. -/
theorem contDiffOn_chart_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : M) (f : M → F) (hf : CMDiff[(chartAt H c).source] 1 f) :
    ContDiffOn ℝ 1 (f ∘ (extChartAt I c).symm) (extChartAt I c).target := by
  apply ContMDiffOn.contDiffOn
  apply hf.comp (contMDiffOn_extChartAt_symm c)
  intro z hz
  simpa only [extChartAt_source, Set.mem_preimage] using (extChartAt I c).map_target hz

/-- Trace is unchanged by the actual tangent-coordinate identification. -/
theorem divergence_eq_localConnectionDivergence
    (cov : CovariantDerivative I E TM) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (X : Π x : M, TM x) (c x : M)
    (hx : x ∈ (chartAt H c).source) (hX : MDiffAt (T% X) x) :
    divergence cov X x = localConnectionDivergence (coordinateConnection cov b c)
      (coordinateVectorField (I := I) c X) (extChartAt I c x) := by
  let e := trivializationAt E TM c
  have hxe : x ∈ e.baseSet := hx
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  have hinv := (extChartAt I c).left_inv hx'
  have hc : (e.linearEquivAt ℝ x hxe).conj (cov X x).toLinearMap =
      (fderiv ℝ (coordinateVectorField (I := I) c X) (extChartAt I c x) +
        (coordinateConnection cov b c (extChartAt I c x)).flip
          (coordinateVectorField (I := I) c X (extChartAt I c x))).toLinearMap := by
    ext u
    have h := covariantDerivative_chart cov b X c x hx hX u
    change e.continuousLinearMapAt ℝ x (cov X x (e.symmL ℝ x u)) = _ at h
    change (e.linearEquivAt ℝ x hxe) (cov X x ((e.linearEquivAt ℝ x hxe).symm u)) =
      fderiv ℝ (coordinateVectorField (I := I) c X) (extChartAt I c x) u +
        coordinateConnection cov b c (extChartAt I c x) u
          (coordinateVectorField (I := I) c X (extChartAt I c x))
    rw [e.linearEquivAt_apply, e.linearEquivAt_symm_apply, ← e.symmL_apply (R := ℝ) hxe,
      ← e.continuousLinearMapAt_apply_of_mem ℝ hxe]
    dsimp only [coordinateConnection, coordinateVectorField]
    rw [hinv]
    exact h.trans (add_comm _ _)
  rw [divergence, ← LinearMap.trace_conj' (cov X x).toLinearMap (e.linearEquivAt ℝ x hxe), hc]
  rfl

variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- The coordinate compatibility required by the density divergence theorem
is supplied by the actual metric-compatible connection. -/
theorem coordinateConnection_localMetricCompatible
    (cov : CovariantDerivative I E TM) (hcov : tangentMetricCompatible cov)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    (c x : M) (hx : x ∈ (chartAt H c).source) :
    localMetricCompatible b (coordinateMetric (I := I) b c)
      (coordinateConnection cov b c) (extChartAt I c x) := by
  intro u
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  simpa only [coordinateConnection, coordinateMetric, (extChartAt I c).left_inv hx'] using
    coordinateMetric_compatibility cov hcov b c x hx u

end AlmostSchur
