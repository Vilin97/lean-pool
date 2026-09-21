/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.Hessian
public import LeanPool.PoincareGeometry.AlmostSchur.ChartMetric
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The actual connection in a local tangent frame

The frame expansion is obtained from the covariant derivative axioms and
Mathlib's differentiable coefficient reconstruction, not postulated as a
coordinate connection formula.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff BigOperators

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Additivity of the actual connection over a finite family of sections
differentiable at the evaluation point. -/
theorem covariantDerivative_sum
    (cov : CovariantDerivative I E TM) {ι : Type*} (s : Finset ι)
    (σ : ι → Π x : M, TM x) (x : M)
    (hσ : ∀ i ∈ s, MDiffAt (T% (σ i)) x) :
    cov (fun y => ∑ i ∈ s, σ i y) x = ∑ i ∈ s, cov (σ i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact congrFun cov.zero x
  | @insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
    simp only [Finset.sum_insert ha]
    change cov (σ a + (fun y => ∑ i ∈ s, σ i y)) x = _
    rw [cov.isCovariantDerivativeOnUniv.add hσ.1 (.sum_section hσ.2), ih hσ.2]

variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

/-- Expansion of a connection in a genuine local tangent frame. The first
term differentiates the frame, and the second differentiates the coefficients. -/
theorem covariantDerivative_localFrame
    (cov : CovariantDerivative I E TM) {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (σ : Π x : M, TM x) (x : M) (hx : x ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) x) :
    cov σ x = Finset.univ.sum (fun i : ι =>
      (e.localFrameCoeff I b i x (σ x)) • cov (e.localFrame b i) x +
        (mvfderiv I (fun y => e.localFrameCoeff I b i y (σ y)) x).smulRight
          (e.localFrame b i x)) := by
  classical
  let a := fun i y => e.localFrameCoeff I b i y (σ y)
  have he (i : ι) : MDiffAt (T% (e.localFrame b i)) x :=
    (contMDiffAt_localFrame_of_mem 1 e b i hx).mdifferentiableAt (by simp)
  have ha (i : ι) : MDiffAt (a i) x := mdifferentiableAt_localFrameCoeff b hx hσ i
  have hex : cov σ x = cov (fun y => ∑ i, a i y • e.localFrame b i y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ
      (.sum_section fun i _ => (ha i).smul_section (he i))
      (by simp) (e.eventually_eq_localFrame_sum_coeff_smul b hx)
  rw [hex, covariantDerivative_sum]
  · apply Finset.sum_congr rfl
    intro i _
    exact cov.isCovariantDerivativeOnUniv.leibniz (he i) (ha i)
  · exact fun i _ => (ha i).smul_section (he i)

/-- Bilinear coordinate connection coefficients obtained by applying the
actual covariant derivative to the local coordinate frame. -/
def frameConnectionCoefficients
    (cov : CovariantDerivative I E TM) {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (x : M) : E →L[ℝ] E →L[ℝ] E :=
  ∑ i : ι, ((b.coord i).toContinuousLinearMap.smulRight
    ((e.continuousLinearMapAt ℝ x).comp ((cov (e.localFrame b i) x).comp (e.symmL ℝ x)))).flip

/-- Evaluation of the connection coefficients on two coordinate vectors. -/
theorem frameConnectionCoefficients_apply
    (cov : CovariantDerivative I E TM) {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (x : M) (u v : E) :
    frameConnectionCoefficients cov e b x u v = ∑ i,
      b.repr v i • e.continuousLinearMapAt ℝ x
        (cov (e.localFrame b i) x (e.symmL ℝ x u)) := by
  simp [frameConnectionCoefficients, Module.Basis.coord_apply]

/-- A coordinate frame vector is sent back to its model basis vector. -/
theorem localFrame_coordinates {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (x : M) (hx : x ∈ e.baseSet) (i : ι) :
    e.continuousLinearMapAt ℝ x (e.localFrame b i x) = b i := by
  rw [e.localFrame_apply_of_mem_baseSet b hx]
  change e.continuousLinearMapAt ℝ x ((e.linearEquivAt ℝ x hx).symm (b i)) = b i
  rw [e.linearEquivAt_symm_apply, ← e.symmL_apply (R := ℝ) hx]
  exact e.continuousLinearMapAt_symmL hx _

/-- The actual connection in coordinates is the coefficient derivative
plus the bilinear frame-connection term. -/
theorem covariantDerivative_coordinates
    (cov : CovariantDerivative I E TM) {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (σ : Π x : M, TM x) (x : M) (hx : x ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) x) (u : E) :
    e.continuousLinearMapAt ℝ x (cov σ x (e.symmL ℝ x u)) =
      frameConnectionCoefficients cov e b x u (e.continuousLinearMapAt ℝ x (σ x)) +
        ∑ i : ι, (mvfderiv I (fun y => e.localFrameCoeff I b i y (σ y)) x
          (e.symmL ℝ x u)) • b i := by
  rw [covariantDerivative_localFrame cov e b σ x hx hσ]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    map_sum, map_add, map_smul, Finset.sum_add_distrib]
  rw [frameConnectionCoefficients_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [e.localFrameCoeff_eq_coeff (b := b) hx,
      e.continuousLinearMapAt_apply_of_mem ℝ hx]
  · apply Finset.sum_congr rfl
    intro i _
    rw [localFrame_coordinates e b x hx]
/-- Differentiation in a chart is differentiation on the manifold evaluated
on the inverse tangent trivialization. -/
theorem fderiv_chart_comp [I.Boundaryless]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : M → F) (c x : M) (hx : x ∈ (chartAt H c).source)
    (ha : MDiffAt a x) (u : E) :
    fderiv ℝ (a ∘ (extChartAt I c).symm) (extChartAt I c x) u =
      mvfderiv I a x ((trivializationAt E TM c).symmL ℝ x u) := by
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  have hi := mdifferentiableWithinAt_extChartAt_symm
    (I := I) (x := c) ((extChartAt I c).map_source hx')
  have hi' : MDiffAt (extChartAt I c).symm (extChartAt I c x) := by
    simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using hi
  have h := mfderiv_comp_apply_of_eq (extChartAt I c x) ha hi'
    ((extChartAt I c).left_inv hx') u
  rw [TangentBundle.symmL_trivializationAt hx]
  simp only [I.range_eq_univ, mfderivWithin_univ, mvfderiv, mfderiv_eq_fderiv,
    ContinuousLinearMap.comp_apply] at *
  convert! h using 0

/-- The coefficient reconstruction also holds outside the trivialization
domain, where both sides are defined to be zero. -/
theorem localFrameCoeff_sum_coordinates {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (σ : Π x : M, TM x) (x : M) :
    (∑ i : ι, e.localFrameCoeff I b i x (σ x) • b i) =
      e.continuousLinearMapAt ℝ x (σ x) := by
  by_cases hx : x ∈ e.baseSet
  · simp only [e.localFrameCoeff_eq_coeff (b := b) hx, b.sum_repr,
      e.continuousLinearMapAt_apply_of_mem ℝ hx]
  · simp [e.localFrameCoeff_apply_of_notMem_baseSet b hx,
      Trivialization.continuousLinearMapAt_apply, e.linearMapAt_def_of_notMem hx]

/-- The genuine covariant derivative is the ordinary derivative of the
coordinate vector field plus its frame-connection term. -/
theorem covariantDerivative_chart [I.Boundaryless]
    (cov : CovariantDerivative I E TM) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (σ : Π x : M, TM x) (c x : M)
    (hx : x ∈ (chartAt H c).source) (hσ : MDiffAt (T% σ) x) (u : E) :
    let e := trivializationAt E TM c
    e.continuousLinearMapAt ℝ x (cov σ x (e.symmL ℝ x u)) =
      frameConnectionCoefficients cov e b x u (e.continuousLinearMapAt ℝ x (σ x)) +
        fderiv ℝ (fun z => e.continuousLinearMapAt ℝ ((extChartAt I c).symm z)
          (σ ((extChartAt I c).symm z))) (extChartAt I c x) u := by
  classical
  let e := trivializationAt E TM c
  have hxe : x ∈ e.baseSet := hx
  let a := fun i y => e.localFrameCoeff I b i y (σ y)
  have ha (i : ι) : MDiffAt (a i) x := mdifferentiableAt_localFrameCoeff b hxe hσ i
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  have hi : MDiffAt (extChartAt I c).symm (extChartAt I c x) := by
    simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
      (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := c)
        ((extChartAt I c).map_source hx'))
  have hd (i : ι) : DifferentiableAt ℝ (a i ∘ (extChartAt I c).symm)
      (extChartAt I c x) :=
    mdifferentiableAt_iff_differentiableAt.mp
      ((ha i).comp_of_eq (extChartAt I c x) hi ((extChartAt I c).left_inv hx'))
  change e.continuousLinearMapAt ℝ x (cov σ x (e.symmL ℝ x u)) = _
  rw [covariantDerivative_coordinates cov e b σ x hxe hσ]
  congr 1
  have heq : (fun z => e.continuousLinearMapAt ℝ ((extChartAt I c).symm z)
      (σ ((extChartAt I c).symm z))) =
      (fun z => ∑ i : ι, (a i ∘ (extChartAt I c).symm) z • b i) := by
    funext z
    exact (localFrameCoeff_sum_coordinates e b σ _).symm
  rw [heq, fderiv_fun_sum (fun i _ => (hd i).smul_const (b i))]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_smul_const (hd i), ContinuousLinearMap.smulRight_apply,
    fderiv_chart_comp (a i) c x hx (ha i)]

/-- The local frame is precisely the inverse trivialization of the basis,
including the common zero extension outside the chart. -/
theorem localFrame_eq_symmL {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (i : ι) (x : M) :
    e.localFrame b i x = e.symmL ℝ x (b i) := by
  by_cases hx : x ∈ e.baseSet
  · rw [e.localFrame_apply_of_mem_baseSet b hx]
    change (e.linearEquivAt ℝ x hx).symm (b i) = _
    rw [e.linearEquivAt_symm_apply, e.symmL_apply hx]
  · rw [e.localFrame_apply_of_notMem b hx, e.symmL_apply_of_notMem hx]

/-- Connection coefficients on a basis vector recover the derivative of
that actual frame vector. -/
theorem frameConnectionCoefficients_basis
    (cov : CovariantDerivative I E TM) {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (x : M) (u : E) (i : ι) :
    frameConnectionCoefficients cov e b x u (b i) =
      e.continuousLinearMapAt ℝ x (cov (e.localFrame b i) x (e.symmL ℝ x u)) := by
  classical
  simp [frameConnectionCoefficients_apply, Finsupp.single_apply]

end AlmostSchur
