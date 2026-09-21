/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.SchurMetricDerivative
public import Mathlib.Analysis.InnerProductSpace.Trace
public import LeanPool.PoincareGeometry.SchurLocalFrame

/-!
# Differentiating metric contraction

The inverse Gram matrix of a smooth local frame supplies a differentiable
formula for metric contraction. Orthonormality is required only at the point
of evaluation, never on a neighborhood; derivatives of the inverse Gram
matrix account for the motion of the frame.
-/

@[expose] public noncomputable section

open Bundle Filter
open scoped Manifold ContDiff BigOperators Topology

namespace SchurRigidity

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type} {x : M}

lemma mvfderiv_sum_apply (t : Finset ι) (f : ι → M → ℝ)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ) (f i) x) (w : TangentSpace I x) :
    mvfderiv (I := I) (fun y ↦ ∑ i ∈ t, f i y) x w =
      ∑ i ∈ t, mvfderiv (I := I) (f i) x w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [mvfderiv_const]
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    rw [mvfderiv_fun_add (hf i (Finset.mem_insert_self i t))
      (by convert (MDifferentiableAt.sum (I := I) (z := x) (f := f) (t := t)
            (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))) using 1
          funext y
          simp only [Finset.sum_apply])]
    simp only [add_apply]
    rw [ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))]

lemma mvfderiv_eq_of_eventuallyEq {f g : M → ℝ} (h : f =ᶠ[𝓝 x] g) :
    mvfderiv (I := I) f x = mvfderiv (I := I) g x := by
  unfold mvfderiv
  rw [h.mfderiv_eq, h.eq_of_nhds]
  rfl

/-- Differentiate `K G = 1` at `G = K = 1`. This is an ordinary product-rule
consequence, not an inverse-derivative assumption. -/
lemma mvfderiv_matrix_inverse_at_one [Fintype ι] [DecidableEq ι]
    (G K : M → Matrix ι ι ℝ)
    (hG : ∀ i j, MDifferentiableAt I 𝓘(ℝ) (fun y ↦ G y i j) x)
    (hK : ∀ i j, MDifferentiableAt I 𝓘(ℝ) (fun y ↦ K y i j) x)
    (hprod : (fun y ↦ K y * G y) =ᶠ[𝓝 x] (fun _ ↦ 1))
    (hGx : G x = 1) (hKx : K x = 1) (i j : ι) (w : TangentSpace I x) :
    mvfderiv (I := I) (fun y ↦ K y i j) x w =
      -mvfderiv (I := I) (fun y ↦ G y i j) x w := by
  have he : (fun y ↦ ∑ k, K y i k * G y k j) =ᶠ[𝓝 x]
      (fun _ ↦ (1 : Matrix ι ι ℝ) i j) := by
    filter_upwards [hprod] with y hy
    exact congrArg (fun C : Matrix ι ι ℝ ↦ C i j) hy
  have hd := congrArg (fun D ↦ D w) (mvfderiv_eq_of_eventuallyEq (I := I) he)
  rw [mvfderiv_sum_apply Finset.univ (fun k y ↦ K y i k * G y k j)
    (fun k _ ↦ (hK i k).mul (hG k j))] at hd
  simp only [mvfderiv_fun_mul (hK _ _) (hG _ _), add_apply,
    smul_apply, smul_eq_mul, mvfderiv_const,
    zero_apply, hGx, hKx, Matrix.one_apply] at hd
  simp only [Finset.sum_add_distrib, ite_mul, one_mul, zero_mul] at hd
  simp at hd
  linarith

/-- Product rule for the inverse-Gram contraction at an orthonormal point. -/
lemma mvfderiv_inverse_contraction_at_one [Fintype ι] [DecidableEq ι]
    (G K a : M → Matrix ι ι ℝ)
    (hG : ∀ i j, MDifferentiableAt I 𝓘(ℝ) (fun y ↦ G y i j) x)
    (hK : ∀ i j, MDifferentiableAt I 𝓘(ℝ) (fun y ↦ K y i j) x)
    (ha : ∀ i j, MDifferentiableAt I 𝓘(ℝ) (fun y ↦ a y i j) x)
    (hprod : (fun y ↦ K y * G y) =ᶠ[𝓝 x] (fun _ ↦ 1))
    (hGx : G x = 1) (hKx : K x = 1) (w : TangentSpace I x) :
    mvfderiv (I := I) (fun y ↦ ∑ i, ∑ j, K y i j * a y i j) x w =
      (∑ i, mvfderiv (I := I) (fun y ↦ a y i i) x w) -
        ∑ i, ∑ j, mvfderiv (I := I) (fun y ↦ G y i j) x w * a x i j := by
  have hd (i : ι) : MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ ∑ j, K y i j * a y i j) x := by
    convert (MDifferentiableAt.sum (I := I) (z := x) (t := Finset.univ)
      (f := fun j y ↦ K y i j * a y i j) (fun j _ ↦ (hK i j).mul (ha i j))) using 1
    funext y
    simp only [Finset.sum_apply]
  rw [mvfderiv_sum_apply Finset.univ _ (fun i _ ↦ hd i)]
  simp_rw [mvfderiv_sum_apply Finset.univ (fun j y ↦ K y _ j * a y _ j)
    (fun j _ ↦ (hK _ j).mul (ha _ j))]
  simp_rw [mvfderiv_fun_mul (hK _ _) (ha _ _), add_apply, smul_apply, smul_eq_mul,
    mvfderiv_matrix_inverse_at_one G K hG hK hprod hGx hKx]
  simp [hKx, Matrix.one_apply, ite_mul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, mul_comm, sub_eq_add_neg]

end Calculus

section ContractionAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι]

/-- The two frame-derivative corrections are exactly the contraction of the
Gram derivative. Neither the tensor nor the frame derivative is symmetric. -/
lemma sum_frame_corrections (A : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ V) (C : ι → V) :
    (∑ i, (A (C i) (b i) + A (b i) (C i))) =
      ∑ i, ∑ j, (inner ℝ (C i) (b j) + inner ℝ (b i) (C j)) * A (b i) (b j) := by
  have hleft (i : ι) : A (C i) (b i) =
      ∑ j, inner ℝ (b j) (C i) * A (b j) (b i) := by
    have h := congrArg (fun v ↦ A v (b i)) (b.sum_repr' (C i))
    simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] using h.symm
  have hright (i : ι) : A (b i) (C i) =
      ∑ j, inner ℝ (b j) (C i) * A (b i) (b j) := by
    have h := congrArg (fun v ↦ A (b i) v) (b.sum_repr' (C i))
    simpa only [map_sum, map_smul, smul_eq_mul] using h.symm
  simp_rw [hleft, hright, Finset.sum_add_distrib, add_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_comm]
  · exact Finset.sum_comm

end ContractionAlgebra

section MetricTrace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Raise one slot of a bilinear tensor with the actual Riesz map. -/
def raisedEndomorphism (x : M) (A : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ) : TM x →ₗ[ℝ] TM x :=
  (CovariantDerivative.rieszMap (I := I) x).toLinearMap.comp
    (LinearMap.toContinuousLinearMap.toLinearMap.comp A)

/-- Metric trace of an arbitrary bilinear tensor, without a symmetry assumption. -/
def metricTrace (A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ) (x : M) : ℝ :=
  LinearMap.trace ℝ (TM x) (raisedEndomorphism x (A x))

omit [T2Space M] [ContMDiffVectorBundle 2 E TM I] in
lemma metricTrace_eq_sum (A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x)) :
    metricTrace A x = ∑ i, A x (b i) (b i) := by
  rw [metricTrace, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm]
  exact CovariantDerivative.rieszMap_apply_inner x _ _

lemma scalarCurvature_eq_metricTrace
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1] (x : M) :
    cov.scalarCurvature x = metricTrace cov.ricciCurvature x := by
  rw [metricTrace_eq_sum _ x (stdOrthonormalBasis ℝ (TM x))]
  rfl

omit [T2Space M] [ContMDiffVectorBundle 2 E TM I] in
/-- The inverse-Gram formula follows from the coordinate formula for the Riesz map. -/
lemma metricTrace_eq_inverseGram
    (A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) :
    metricTrace A x = ∑ i, ∑ j,
      ((CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹ : Matrix ι ι ℝ) i j *
        A x (e.localFrame b i x) (e.localFrame b j x) := by
  rw [metricTrace, LinearMap.trace_eq_matrix_trace ℝ (e.basisAt b hx)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.localFrame_apply_of_mem_baseSet (b := b) hx]
  have hc := CovariantDerivative.localFrameCoeff_rieszMap (I := I) e b
    (omega := fun y ↦ (A y (e.localFrame b i y)).toContinuousLinearMap) hx i
  rw [Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
    (I := I) (e := e) (b := b) (hx := hx)
    (s := fun y ↦ CovariantDerivative.rieszMap (I := I) y
      (A y (e.localFrame b i y)).toContinuousLinearMap)] at hc
  exact hc

/-- Differentiation commutes with metric contraction of a general bilinear
tensor. The frame is orthonormal only at `x`; the inverse Gram matrix is
differentiated on its full base set. The hypotheses concern differentiability
of actual scalar evaluations, not a postulated contraction identity. -/
theorem mvfderiv_metricTrace_eq_sum_bilinearDerivative
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) (hmetric : cov.IsMetricCompatibleTangent)
    (A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (o : OrthonormalBasis ι ℝ (TM x))
    (ho : ∀ i, e.localFrame b i x = o i)
    (hA : ∀ i j, MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ A y (e.localFrame b i y) (e.localFrame b j y)) x)
    (w : TM x) :
    mvfderiv (I := I) (metricTrace A) x w =
      ∑ i, bilinearDerivative cov A (e.localFrame b i) (e.localFrame b i) x w := by
  let G : M → Matrix ι ι ℝ := fun y ↦ CovariantDerivative.localFrameGramMatrix (I := I) e b y
  let K : M → Matrix ι ι ℝ := fun y ↦ (G y)⁻¹
  let a : M → Matrix ι ι ℝ := fun y i j ↦ A y (e.localFrame b i y) (e.localFrame b j y)
  have hG : ∀ i j, MDifferentiableAt I 𝓘(ℝ) (fun y ↦ G y i j) x := by
    intro i j
    have hg := CovariantDerivative.contMDiffOn_localFrameGramMatrix (I := I)
      e b e.open_baseSet (Set.Subset.refl _)
    rw [contMDiffOn_pi_space] at hg
    have hgi := hg i
    rw [contMDiffOn_pi_space] at hgi
    exact ((hgi j x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt
      (by norm_num)
  have hK : ∀ i j, MDifferentiableAt I 𝓘(ℝ) (fun y ↦ K y i j) x := by
    intro i j
    have hk := CovariantDerivative.contMDiffOn_localFrameGramMatrix_inv (I := I)
      e b e.open_baseSet (Set.Subset.refl _)
    rw [contMDiffOn_pi_space] at hk
    have hki := hk i
    rw [contMDiffOn_pi_space] at hki
    exact ((hki j x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt
      (by norm_num)
  have hprod : (fun y ↦ K y * G y) =ᶠ[𝓝 x] (fun _ ↦ 1) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact Matrix.nonsing_inv_mul _
      (CovariantDerivative.localFrameGramMatrix_isUnit_det (I := I) e b hy)
  have hGx : G x = 1 := by
    ext i j
    simp only [G, CovariantDerivative.localFrameGramMatrix, ho, o.inner_eq_ite,
      Matrix.one_apply]
  have hKx : K x = 1 := by simp [K, hGx]
  have heq : metricTrace A =ᶠ[𝓝 x] (fun y ↦ ∑ i, ∑ j, K y i j * a y i j) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact metricTrace_eq_inverseGram A e b hy
  have hframe (i : ι) : MDiffAt (T% (e.localFrame b i)) x :=
    (((e.contMDiffOn_localFrame_baseSet (I := I) (n := (2 : WithTop ℕ∞))
      (b := b) i) x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt
        (by norm_num)
  have hGram (i j : ι) : mvfderiv (I := I) (fun y ↦ G y i j) x w =
      inner ℝ (cov (e.localFrame b i) x w) (o j) +
        inner ℝ (o i) (cov (e.localFrame b j) x w) := by
    simpa only [G, CovariantDerivative.localFrameGramMatrix, ho] using
      hmetric (hframe i) (hframe j) w
  rw [mvfderiv_eq_of_eventuallyEq heq,
    mvfderiv_inverse_contraction_at_one G K a hG hK hA hprod hGx hKx]
  simp_rw [hGram]
  have hc := sum_frame_corrections (A x) o (fun i ↦ cov (e.localFrame b i) x w)
  simp only [a, ho]
  rw [← hc]
  simp only [bilinearDerivative, ho, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- Smooth metric contraction preserves differentiability of local components. -/
theorem mdifferentiableAt_metricTrace
    [IsContMDiffRiemannianBundle I 2 E TM]
    (A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet)
    (hA : ∀ i j, MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ A y (e.localFrame b i y) (e.localFrame b j y)) x) :
    MDifferentiableAt I 𝓘(ℝ) (metricTrace A) x := by
  let K : M → Matrix ι ι ℝ := fun y ↦
    (CovariantDerivative.localFrameGramMatrix (I := I) e b y)⁻¹
  have hK (i j : ι) : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ K y i j) x := by
    have hk := CovariantDerivative.contMDiffOn_localFrameGramMatrix_inv (I := I)
      e b e.open_baseSet (Set.Subset.refl _)
    rw [contMDiffOn_pi_space] at hk
    have hki := hk i
    rw [contMDiffOn_pi_space] at hki
    exact ((hki j x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt
      (by norm_num)
  have hd : MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ ∑ i, ∑ j, K y i j * A y (e.localFrame b i y) (e.localFrame b j y)) x := by
    have hi (i : ι) : MDifferentiableAt I 𝓘(ℝ)
        (fun y ↦ ∑ j, K y i j * A y (e.localFrame b i y) (e.localFrame b j y)) x := by
      simpa only [Finset.sum_fn] using
        (MDifferentiableAt.sum (I := I) (t := Finset.univ)
          (f := fun j y ↦ K y i j * A y (e.localFrame b i y) (e.localFrame b j y))
          (fun j _ ↦ (hK i j).mul (hA i j)))
    simpa only [Finset.sum_fn] using
      (MDifferentiableAt.sum (I := I) (t := Finset.univ)
        (f := fun i y ↦ ∑ j, K y i j * A y (e.localFrame b i y) (e.localFrame b j y))
        (fun i _ ↦ hi i))
  apply hd.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact metricTrace_eq_inverseGram A e b hy

theorem mdifferentiableAt_metricTrace_schurFrame
    [ContMDiffVectorBundle 3 E TM I]
    [IsContMDiffRiemannianBundle I 2 E TM]
    (A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TM x))
    (hA : ∀ i j, MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ A y (CovariantDerivative.schurFrame x b.toBasis i y)
        (CovariantDerivative.schurFrame x b.toBasis j y)) x) :
    MDifferentiableAt I 𝓘(ℝ) (metricTrace A) x := by
  apply mdifferentiableAt_metricTrace A (trivializationAt E TM x)
    (CovariantDerivative.schurModelBasis x b.toBasis)
    (FiberBundle.mem_baseSet_trivializationAt E TM x)
  intro i j
  apply (hA i j).congr_of_eventuallyEq
  filter_upwards [CovariantDerivative.schurFrame_eventuallyEq_localFrame x b.toBasis]
    with y hy
  rw [hy i, hy j]

/-- The scalar-curvature specialization uses the repository's actual Ricci
tensor and the section formula for its covariant derivative. -/
theorem mvfderiv_scalarCurvature_eq_sum_bilinearDerivative
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (o : OrthonormalBasis ι ℝ (TM x))
    (ho : ∀ i, e.localFrame b i x = o i)
    (hRic : ∀ i j, MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ cov.ricciCurvature y (e.localFrame b i y) (e.localFrame b j y)) x)
    (w : TM x) :
    mvfderiv (I := I) cov.scalarCurvature x w =
      ∑ i, bilinearDerivative cov cov.ricciCurvature
        (e.localFrame b i) (e.localFrame b i) x w := by
  have heq : cov.scalarCurvature = metricTrace cov.ricciCurvature :=
    funext (scalarCurvature_eq_metricTrace cov)
  rw [heq]
  exact mvfderiv_metricTrace_eq_sum_bilinearDerivative cov hmetric cov.ricciCurvature
    e b hx o ho hRic w

/-- Canonical smooth extensions discharge the frame choice in the metric-trace
derivative. Only differentiability of the actual tensor components is assumed. -/
theorem mvfderiv_metricTrace_eq_sum_schurFrame
    [ContMDiffVectorBundle 3 E TM I]
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) (hmetric : cov.IsMetricCompatibleTangent)
    (A : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TM x))
    (hA : ∀ i j, MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ A y (CovariantDerivative.schurFrame x b.toBasis i y)
        (CovariantDerivative.schurFrame x b.toBasis j y)) x)
    (w : TM x) :
    mvfderiv (I := I) (metricTrace A) x w =
      ∑ i, bilinearDerivative cov A
        (CovariantDerivative.schurFrame x b.toBasis i)
        (CovariantDerivative.schurFrame x b.toBasis i) x w := by
  let e := trivializationAt E TM x
  let B := CovariantDerivative.schurModelBasis x b.toBasis
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E TM x
  have he := CovariantDerivative.schurFrame_eventuallyEq_localFrame x b.toBasis
  have hlocal (i : ι) : MDiffAt (T% (e.localFrame B i)) x :=
    (((e.contMDiffOn_localFrame_baseSet (I := I) (n := (2 : WithTop ℕ∞))
      (b := B) i) x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt
        (by norm_num)
  have hglobal (i : ι) : MDiffAt (T% (CovariantDerivative.schurFrame x b.toBasis i)) x :=
    ((CovariantDerivative.schurFrame_contMDiff_three x b.toBasis i) x).mdifferentiableAt
      (by norm_num)
  have halocal (i j : ι) : MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ A y (e.localFrame B i y) (e.localFrame B j y)) x := by
    apply (hA i j).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    rw [hy i, hy j]
  rw [mvfderiv_metricTrace_eq_sum_bilinearDerivative cov hmetric A e B hx b
    (fun i ↦ CovariantDerivative.schurModelBasis_localFrame_at x b.toBasis i)
    halocal w]
  apply Finset.sum_congr rfl
  intro i _
  apply bilinearDerivative_congr_of_eventuallyEq cov A _ _ _ _ x w
    (hlocal i) (hlocal i) (hglobal i) (hglobal i)
  · filter_upwards [he] with y hy
    exact (hy i).symm
  · filter_upwards [he] with y hy
    exact (hy i).symm

end MetricTrace

end SchurRigidity
