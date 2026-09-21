/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.BochnerFluxRegularity
public import LeanPool.PoincareGeometry.AlmostSchur.ConnectionCoordinates

/-! # Differentiating trace in a moving local frame

The two connection corrections cancel by interchanging finite sums. No
parallel-frame or normal-coordinate hypothesis is used.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)
local instance covariantTraceFiniteDimensionalTangentSpace (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

omit [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- Trace is the sum of diagonal coefficients in the actual local frame. -/
theorem trace_eq_sum_localFrameCoeff {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (A : Π y, TM y →L[ℝ] TM y) (x : M) (hx : x ∈ e.baseSet) :
    LinearMap.trace ℝ (TM x) (A x).toLinearMap =
      ∑ i, e.localFrameCoeff I b i x (A x (e.localFrame b i x)) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (e.basisAt b hx)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [e.localFrameCoeff_apply_of_mem_baseSet b hx
    (fun y ↦ A y (e.localFrame b i y)) i, e.localFrame_apply_of_mem_baseSet b hx]
  rfl

/-- Differentiation commutes with the finite diagonal trace sum. -/
theorem mvfderiv_trace_eq_sum_localFrameCoeff {ι : Type} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (A : Π y, TM y →L[ℝ] TM y) (x : M) (hx : x ∈ e.baseSet)
    (hA : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)) x) (v : TM x) :
    mvfderiv I (fun y ↦ LinearMap.trace ℝ (TM y) (A y).toLinearMap) x v =
      ∑ i, mvfderiv I
        (fun y ↦ e.localFrameCoeff I b i y (A y (e.localFrame b i y))) x v := by
  classical
  let a := fun i y ↦ e.localFrameCoeff I b i y (A y (e.localFrame b i y))
  have ha (i : ι) : MDiffAt (a i) x :=
    mdifferentiableAt_localFrameCoeff b hx
      (hA.clm_bundle_apply ((contMDiffAt_localFrame_of_mem 1 e b i hx).mdifferentiableAt
        (by simp))) i
  have he : (fun y ↦ LinearMap.trace ℝ (TM y) (A y).toLinearMap) =ᶠ[𝓝 x]
      (fun y ↦ ∑ i, a i y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact trace_eq_sum_localFrameCoeff e b A y hy
  have hsum (s : Finset ι) : mvfderiv I (fun y ↦ ∑ i ∈ s, a i y) x =
      ∑ i ∈ s, mvfderiv I (a i) x := by
    induction s using Finset.induction_on with
    | empty => simp [mvfderiv_const]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      have hd : MDiffAt (fun y ↦ ∑ j ∈ s, a j y) x := by
        convert (MDifferentiableAt.sum (t := s) (f := a) (fun j _ ↦ ha j)) using 1
        ext y
        simp
      change mvfderiv I (a i + (fun y ↦ ∑ j ∈ s, a j y)) x = _
      rw [mvfderiv_add (ha i) hd, ih]
  rw [show mvfderiv I (fun y ↦ LinearMap.trace ℝ (TM y) (A y).toLinearMap) x =
      mvfderiv I (fun y ↦ ∑ i, a i y) x from he.mfderiv_eq]
  simpa only [Finset.mem_univ, Finset.sum_const_zero, sum_apply] using
    congrArg (fun L ↦ L v) (hsum Finset.univ)

/-- The derivative of trace is the contraction of the corrected covariant
derivative of the endomorphism. All moving-frame terms cancel explicitly. -/
theorem mvfderiv_trace_eq_covariant_contraction {ι : Type} [Fintype ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (A : Π y, TM y →L[ℝ] TM y) (X : Π y, TM y) (x : M) (hx : x ∈ e.baseSet)
    (hA : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)) x) :
    mvfderiv I (fun y ↦ LinearMap.trace ℝ (TM y) (A y).toLinearMap) x (X x) =
      ∑ i, e.localFrameCoeff I b i x
        (cov (fun y ↦ A y (e.localFrame b i y)) x (X x) -
          A x (cov (e.localFrame b i) x (X x))) := by
  classical
  let F := e.localFrame b
  let a := fun i j y ↦ e.localFrameCoeff I b i y (A y (F j y))
  let C := fun i j ↦ e.localFrameCoeff I b i x (cov (F j) x (X x))
  have hF (i : ι) : MDiffAt (T% (F i)) x :=
    (contMDiffAt_localFrame_of_mem 1 e b i hx).mdifferentiableAt (by simp)
  have hAF (i : ι) : MDiffAt (T% (fun y ↦ A y (F i y))) x :=
    hA.clm_bundle_apply (hF i)
  have hcoeff (i j : ι) : e.localFrameCoeff I b i x (F j x) = if j = i then 1 else 0 := by
    rw [e.localFrameCoeff_apply_of_mem_baseSet b hx (F j) i]
    simp [F, e.localFrame_apply_of_mem_baseSet b hx, Finsupp.single_apply]
  have hfirst (i : ι) : e.localFrameCoeff I b i x
      (cov (fun y ↦ A y (F i y)) x (X x)) =
      (∑ j, a j i x * C i j) + mvfderiv I (a i i) x (X x) := by
    rw [covariantDerivative_localFrame cov e b _ x hx (hAF i)]
    simp only [sum_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      map_sum, map_add, map_smul, smul_eq_mul]
    change (∑ j, (a j i x * C i j + mvfderiv I (a j i) x (X x) *
      e.localFrameCoeff I b i x (F j x))) = _
    simp only [hcoeff, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsecond (i : ι) : e.localFrameCoeff I b i x
      (A x (cov (F i) x (X x))) = ∑ j, C j i * a i j x := by
    have he := e.eq_sum_localFrameCoeff_smul (I := I) (b := b)
      (s := fun y ↦ cov (F i) y (X y)) hx
    rw [he]
    simp only [map_sum, map_smul, smul_eq_mul]
    rfl
  rw [mvfderiv_trace_eq_sum_localFrameCoeff e b A x hx hA]
  change (∑ i, mvfderiv I (a i i) x (X x)) = _
  change _ = ∑ i, e.localFrameCoeff I b i x
    (cov (fun y ↦ A y (F i y)) x (X x) - A x (cov (F i) x (X x)))
  simp only [map_sub, hfirst, hsecond, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hc : (∑ i, ∑ j, a j i x * C i j) = ∑ i, ∑ j, C j i * a i j x := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hc]
  ring

end AlmostSchur
