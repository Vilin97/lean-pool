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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianCoordinate

/-!
# Fixed-chart form of the connection Laplacian

This module transfers the local-frame coefficient formulas for the genuine
connection Laplacian to one fixed extended manifold chart.  Directional
manifold derivatives become within Fréchet derivatives of the chart
representatives, evaluated on the pulled-back local-frame vector fields.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₀" => (Bundle.Trivial M ℝ)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

-- Stabilize synthesis for the nested operator spaces used as the model and
-- fibers of the induced tensor bundles.
local instance chartOneModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartOneModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance chartOneFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₁ x) := inferInstance
local instance chartOneFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₁ x) := inferInstance
local instance chartTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance chartTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance chartTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance chartTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance
local instance chartThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance chartThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance chartThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) := inferInstance
local instance chartThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) := inferInstance

/-- Directional manifold differentiation is within Fréchet differentiation
in any fixed extended chart containing the evaluation point. -/
theorem mvfderiv_apply_eq_fderivWithin_fixedChart
    {g : M → ℝ} {X : ∀ x : M, TM x} {p y : M}
    (hy : y ∈ (extChartAt I p).source) (hg : MDiffAt g y) :
    mvfderiv (I := I) g y (X y) =
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p g) (Set.range I)
        ((extChartAt I p) y)
        (VectorField.mpullbackWithin 𝓘(ℝ, E) I
          (extChartAt I p).symm X (Set.range I) ((extChartAt I p) y)) := by
  let φ := extChartAt I p
  let z := φ y
  have hy_eq : φ.symm z = y := by
    simpa [φ, z] using PartialEquiv.left_inv φ hy
  have hz : z ∈ φ.target := by
    simpa [φ, z] using PartialEquiv.map_source φ hy
  have hz_range : z ∈ Set.range I := by
    simpa [φ, z] using extChartAt_target_subset_range p hz
  have hg' : HasMFDerivAt I 𝓘(ℝ) g (φ.symm z) (mfderiv% g y) := by
    rw [hy_eq]
    exact hg.hasMFDerivAt
  have hcomp :
      HasMFDerivWithinAt 𝓘(ℝ, E) 𝓘(ℝ) (g ∘ φ.symm) (Set.range I) z
        ((mfderiv% g y).comp (mfderiv[Set.range I] φ.symm z)) := by
    exact HasMFDerivAt.comp_hasMFDerivWithinAt
      (f := φ.symm) (s := Set.range I) (x := z) hg'
      (mdifferentiableWithinAt_extChartAt_symm hz).hasMFDerivWithinAt
  have hderiv :
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) p g) (Set.range I) z =
        (((mfderiv% g y).comp (mfderiv[Set.range I] φ.symm z)) :
          E →L[ℝ] ℝ) := by
    simpa [writtenInExtChartAt, φ, z] using
      hcomp.hasFDerivWithinAt.fderivWithin
        (I.uniqueDiffOn.uniqueDiffWithinAt hz_range)
  have hmp :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm X (Set.range I) z =
        (mfderiv[Set.range I] φ.symm z).inverse (X y) := by
    change (mfderiv[Set.range I] φ.symm z).inverse (X (φ.symm z)) =
      (mfderiv[Set.range I] φ.symm z).inverse (X y)
    rw [hy_eq]
  rw [hderiv, hmp]
  change (mfderiv% g y) (X y) =
    (((mfderiv% g y).comp (mfderiv[Set.range I] φ.symm z))
      ((mfderiv[Set.range I] φ.symm z).inverse (X y)))
  rw [← hy_eq, ContinuousLinearMap.comp_apply]
  rcases isInvertible_mfderivWithin_extChartAt_symm hz with ⟨e, he⟩
  rw [← he, ContinuousLinearMap.inverse_equiv]
  have hsymm : e.toContinuousLinearMap (e.symm (X (φ.symm z))) = X (φ.symm z) := by
    exact ContinuousLinearEquiv.apply_symm_apply e (X (φ.symm z))
  have hconv :
      (mfderiv% g (φ.symm z)) (X (φ.symm z)) =
        (mfderiv% g (φ.symm z)) (e.toContinuousLinearMap (e.symm (X (φ.symm z)))) := by
    exact congrArg (fun v => (mfderiv% g (φ.symm z)) v) hsymm.symm
  exact hconv

/-- The model-space vector field obtained by pulling a local tangent frame
back through a fixed extended chart. -/
def localFrameInChart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (i : ι) : E → E :=
  VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
    (e.localFrame b i) (Set.range I)

/-- A covariant-two-tensor coefficient transported through a fixed chart. -/
def localTwoTensorComponentInChart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x)
    (out : ι × ι) : E → ℝ :=
  writtenInExtChartAt I 𝓘(ℝ) p
    (localTwoTensorComponent (I := I) e b h out)

/-- An induced two-tensor frame-connection coefficient transported through a
fixed chart. -/
def localTwoTensorConnectionCoefficientInChart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM) (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (out input : ι × ι) (i : ι) : E → ℝ :=
  writtenInExtChartAt I 𝓘(ℝ) p
    (localTwoTensorConnectionCoefficient (I := I) cov e b out input i)

/-- Fixed-chart expression for the first covariant-derivative coefficient. -/
def localFirstCovariantComponentInChart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM) (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x)
    (out : ι × ι) (i : ι) : E → ℝ :=
  fun z =>
    fderivWithin ℝ (localTwoTensorComponentInChart (I := I) p e b h out)
        (Set.range I) z (localFrameInChart (I := I) p e b i z) +
      ∑ input : ι × ι,
        localTwoTensorComponentInChart (I := I) p e b h input z *
          localTwoTensorConnectionCoefficientInChart (I := I)
            cov p e b out input i z

/-- On the overlap of the frame domain and the fixed chart, the intrinsic
first covariant coefficient is exactly its fixed-chart Fréchet expression. -/
theorem localFirstCovariantComponent_eq_inChart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM) (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x}
    {y : M} (out : ι × ι) (i : ι)
    (hyChart : y ∈ (extChartAt I p).source)
    (hg : MDiffAt (localTwoTensorComponent (I := I) e b h out) y) :
    localFirstCovariantComponent (I := I) cov e b h out i y =
      localFirstCovariantComponentInChart (I := I)
        cov p e b h out i ((extChartAt I p) y) := by
  unfold localFirstCovariantComponent localFirstCovariantComponentInChart
  rw [mvfderiv_apply_eq_fderivWithin_fixedChart
    (I := I) (p := p) (y := y) hyChart hg]
  simp [localTwoTensorComponentInChart,
    localTwoTensorConnectionCoefficientInChart, localFrameInChart,
    writtenInExtChartAt, hyChart]
  simp_all only [mfld_simps]

/-- The fixed-chart representative of an induced covariant-three-tensor
frame-connection coefficient. -/
def localThreeTensorConnectionCoefficientInChart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM) (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (out input : (ι × ι) × ι)
    (i : ι) : E → ℝ :=
  writtenInExtChartAt I 𝓘(ℝ) p
    (localThreeTensorConnectionCoefficient (I := I)
      cov e b out input i)

/-- Fixed-chart expression for a second covariant-derivative coefficient.
The outer derivative is an ordinary within Fréchet derivative of the already
expanded first covariant coefficient. -/
def localSecondCovariantComponentInChart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM) (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x)
    (out : ι × ι) (j i : ι) : E → ℝ :=
  fun z =>
    fderivWithin ℝ
        (localFirstCovariantComponentInChart (I := I) cov p e b h out j)
        (Set.range I) z (localFrameInChart (I := I) p e b i z) +
      ∑ input : (ι × ι) × ι,
        localFirstCovariantComponentInChart (I := I)
            cov p e b h input.1 input.2 z *
          localThreeTensorConnectionCoefficientInChart (I := I)
            cov p e b (out, j) input i z

/-- On a fixed chart, the chart representative of the intrinsic first
covariant coefficient agrees locally with its explicit Fréchet expression.
The neighborhood statement is the locality input needed for the next
Fréchet derivative. -/
theorem writtenInExtChartAt_localFirstCovariantComponent_eventuallyEq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM) (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x}
    (hreg : ∀ y ∈ e.baseSet, ∀ out : ι × ι,
      MDiffAt (localTwoTensorComponent (I := I) e b h out) y)
    {y : M} (hyFrame : y ∈ e.baseSet)
    (hyChart : y ∈ (extChartAt I p).source)
    (out : ι × ι) (j : ι) :
    writtenInExtChartAt I 𝓘(ℝ) p
        (localFirstCovariantComponent (I := I) cov e b h out j)
      =ᶠ[nhdsWithin ((extChartAt I p) y) (Set.range I)]
        localFirstCovariantComponentInChart (I := I) cov p e b h out j := by
  have hzTarget : (extChartAt I p) y ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hyChart
  have hySymm : (extChartAt I p).symm ((extChartAt I p) y) ∈
      e.baseSet := by
    rw [(extChartAt I p).left_inv hyChart]
    exact hyFrame
  have hframeNear : (extChartAt I p).symm ⁻¹' e.baseSet ∈
      nhds ((extChartAt I p) y) :=
    (continuousAt_extChartAt_symm'' hzTarget).preimage_mem_nhds
      (e.open_baseSet.mem_nhds hySymm)
  filter_upwards [extChartAt_target_mem_nhdsWithin' hyChart,
    mem_nhdsWithin_of_mem_nhds hframeNear] with z hz hzFrame
  let y' := (extChartAt I p).symm z
  have hy' : y' ∈ (extChartAt I p).source :=
    (extChartAt I p).map_target hz
  have hzy : (extChartAt I p) y' = z := by
    simpa [y'] using PartialEquiv.right_inv (extChartAt I p) hz
  calc
    writtenInExtChartAt I 𝓘(ℝ) p
          (localFirstCovariantComponent (I := I) cov e b h out j) z =
        localFirstCovariantComponent (I := I) cov e b h out j y' := by
          rfl
    _ = localFirstCovariantComponentInChart (I := I)
          cov p e b h out j ((extChartAt I p) y') :=
        localFirstCovariantComponent_eq_inChart
          (I := I) cov p e b out j hy' (hreg y' hzFrame out)
    _ = localFirstCovariantComponentInChart (I := I)
          cov p e b h out j z := by rw [hzy]

/-- The intrinsic second covariant coefficient is exactly the fixed-chart
second-order Fréchet expression. -/
theorem localSecondCovariantComponent_eq_inChart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM) (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x}
    (hreg : ∀ y ∈ e.baseSet, ∀ out : ι × ι,
      MDiffAt (localTwoTensorComponent (I := I) e b h out) y)
    {y : M} (hyFrame : y ∈ e.baseSet)
    (hyChart : y ∈ (extChartAt I p).source)
    (out : ι × ι) (j i : ι)
    (hfirst : MDiffAt
      (localFirstCovariantComponent (I := I) cov e b h out j) y) :
    localSecondCovariantComponent (I := I) cov e b h out j i y =
      localSecondCovariantComponentInChart (I := I)
        cov p e b h out j i ((extChartAt I p) y) := by
  unfold localSecondCovariantComponent localSecondCovariantComponentInChart
  rw [mvfderiv_apply_eq_fderivWithin_fixedChart
    (I := I) (p := p) (y := y) hyChart hfirst]
  let z := (extChartAt I p) y
  have hz : z ∈ Set.range I := by
    exact extChartAt_target_subset_range p ((extChartAt I p).map_source hyChart)
  have heqz :
      writtenInExtChartAt I 𝓘(ℝ) p
          (localFirstCovariantComponent (I := I) cov e b h out j)
        =ᶠ[nhdsWithin z (Set.range I)]
          localFirstCovariantComponentInChart (I := I) cov p e b h out j := by
    simpa [z] using
      (writtenInExtChartAt_localFirstCovariantComponent_eventuallyEq
        (I := I) cov p e b hreg hyFrame hyChart out j)
  rw [heqz.fderivWithin_eq_of_mem hz]
  congr 1
  apply Finset.sum_congr rfl
  intro input hinput
  rw [localFirstCovariantComponent_eq_inChart
    (I := I) cov p e b input.1 input.2 hyChart
      (hreg y hyFrame input.1)]
  simp [localThreeTensorConnectionCoefficientInChart,
    writtenInExtChartAt]
  simp_all only [mfld_simps]

/-- The inverse Gram-matrix coefficient of the local tangent frame in a fixed
manifold chart. -/
def localFrameInverseGramMatrixInChart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (i j : ι) : E → ℝ :=
  writtenInExtChartAt I 𝓘(ℝ) p
    (fun x => localFrameInverseGramMatrix (I := I) e b x i j)

/-- Full fixed-chart coefficient of the genuine connection Laplacian.  Its
principal contraction is the inverse frame Gram matrix, and its second-order
input is the expanded fixed-chart covariant Hessian coefficient above. -/
def localConnectionLaplacianComponentInChart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM) (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x)
    (out : ι × ι) : E → ℝ :=
  fun z =>
    ∑ i : ι, ∑ j : ι,
      localFrameInverseGramMatrixInChart (I := I) p e b i j z *
        localSecondCovariantComponentInChart (I := I)
          cov p e b h out j i z

/-- The named intrinsic local coefficient of the connection Laplacian agrees
with its complete fixed-chart second-order expression. -/
theorem localConnectionLaplacianComponent_eq_inChart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM) (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x}
    (hreg : ∀ y ∈ e.baseSet, ∀ out : ι × ι,
      MDiffAt (localTwoTensorComponent (I := I) e b h out) y)
    {y : M} (hyFrame : y ∈ e.baseSet)
    (hyChart : y ∈ (extChartAt I p).source)
    (hfirst : ∀ out : ι × ι, ∀ j : ι,
      MDiffAt (localFirstCovariantComponent (I := I) cov e b h out j) y)
    (out : ι × ι) :
    localConnectionLaplacianComponent (I := I) cov e b h out y =
      localConnectionLaplacianComponentInChart (I := I)
        cov p e b h out ((extChartAt I p) y) := by
  unfold localConnectionLaplacianComponent
    localConnectionLaplacianComponentInChart
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [localSecondCovariantComponent_eq_inChart
    (I := I) cov p e b hreg hyFrame hyChart out j i (hfirst out j)]
  simp [localFrameInverseGramMatrixInChart, writtenInExtChartAt]
  simp_all only [mfld_simps]

/-- **Actual connection Laplacian in one fixed chart.**  Evaluating the
intrinsic connection Laplacian on a local tensor-frame vector is exactly the
finite fixed-chart differential expression built from Fréchet derivatives,
the inverse metric, and the induced connection coefficients. -/
theorem connectionLaplacian_apply_eq_inChart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM) (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x}
    (hregFrame : ∀ y ∈ e.baseSet,
      MDiffAt
        (fun z => TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) z (h z)) y)
    (hregChart : ∀ y ∈ e.baseSet,
      ∀ out : ι × ι,
        MDiffAt (localTwoTensorComponent (I := I) e b h out) y)
    {y : M} (hyFrame : y ∈ e.baseSet)
    (hyChart : y ∈ (extChartAt I chartCenter).source)
    (hcovFirst : MDiffAt
      (fun z => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) z
        (covariantTwoTensorCovariantDerivative cov h z)) y)
    (hlocalFirst : ∀ out : ι × ι, ∀ j : ι,
      MDiffAt (localFirstCovariantComponent (I := I) cov e b h out j) y)
    (p q : ι) :
    connectionLaplacian cov h y
        (e.localFrame b p y) (e.localFrame b q y) =
      localConnectionLaplacianComponentInChart (I := I)
        cov chartCenter e b h (q, p) ((extChartAt I chartCenter) y) := by
  rw [connectionLaplacian_apply_eq_localConnectionLaplacianComponent
    (I := I) cov e b hregFrame hyFrame hcovFirst p q]
  exact localConnectionLaplacianComponent_eq_inChart
    (I := I) cov chartCenter e b hregChart hyFrame hyChart hlocalFirst (q, p)

end CovariantDerivative
