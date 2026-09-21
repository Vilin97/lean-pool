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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchiBridge
public import LeanPool.PoincareGeometry.CurvatureEvaluation
public import LeanPool.PoincareGeometry.SchurMetricDerivative
public import LeanPool.PoincareGeometry.ScalarDerivative
public import LeanPool.PoincareGeometry.SchurLocalFrame
public import LeanPool.PoincareGeometry.BilinearDerivativeTensor

/-! Differential contraction calculus for the actual connection curvature. -/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 2) M] [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I (minSmoothness ℝ 4) M]
  [IsManifold I ((2 : ℕ∞) + 1) M] [IsManifold I ((3 : ℕ∞) + 1) M]

/-- Regularity of the curvature commutator on sufficiently smooth sections. -/
theorem ricciDerivative_curvatureAux_contMDiff
    {Y Z W : Π x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% (cov.curvatureAux Y Z W)) := by
  have hY₁ := hY.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hZ₁ := hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hW₂ := hW.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hbr : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (T% (VectorField.mlieBracket I Y Z)) := by
    simpa using (ContDiff.mlieBracket_vectorField (I := I)
      (m := (1 : ℕ∞)) (n := (2 : ℕ∞)) hY hZ (by norm_num))
  exact ((cov.contMDiff_along (n := 1) hY₁ (cov.contMDiff_along (n := 2) hZ hW)).sub_section
    (cov.contMDiff_along (n := 1) hZ₁ (cov.contMDiff_along (n := 2) hY hW))).sub_section
    (cov.contMDiff_along (n := 1) hbr hW₂)

/-- Differentiate an actual curvature component. All four moving input/output-slot
corrections are explicit; the corrected derivative is `secondBianchiAux`. -/
theorem ricciDerivative_curvature_inner
    (hmetric : cov.IsMetricCompatibleTangent)
    (X Y Z W V : Π x : M, TangentSpace I x) (x : M)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W))
    (hV : MDiffAt (T% V) x) :
    mvfderiv (I := I) (fun y ↦ inner ℝ (cov.curvatureAux Y Z W y) (V y)) x (X x) =
      inner ℝ (cov.secondBianchiAux X Y Z W x) (V x) +
      inner ℝ (cov.curvatureAux (cov.along X Y) Z W x) (V x) +
      inner ℝ (cov.curvatureAux Y (cov.along X Z) W x) (V x) +
      inner ℝ (cov.curvatureAux Y Z (cov.along X W) x) (V x) +
      inner ℝ (cov.curvatureAux Y Z W x) (cov.along X V x) := by
  have hR := ((ricciDerivative_curvatureAux_contMDiff cov hY hZ hW) x).mdifferentiableAt
    one_ne_zero
  rw [hmetric hR hV]
  simp only [secondBianchiAux_apply, inner_sub_left, CovariantDerivative.along]
  abel

/-- Finite sums commute with the actual scalar manifold derivative. -/
theorem ricciDerivative_mvfderiv_sum {ι : Type} (s : Finset ι)
    (f : ι → M → ℝ) (x : M) (v : TangentSpace I x)
    (hf : ∀ i ∈ s, MDiffAt (f i) x) :
    mvfderiv (I := I) (fun y ↦ ∑ i ∈ s, f i y) x v =
      ∑ i ∈ s, mvfderiv (I := I) (f i) x v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change mvfderiv (I := I) (0 : M → ℝ) x v = 0
    rw [mvfderiv_zero, zero_apply]
  | @insert i s hi ih =>
    have hs : MDiffAt (fun y ↦ ∑ j ∈ s, f j y) x := by
      simpa only [Finset.sum_fn] using
        (MDifferentiableAt.sum (I := I) (f := f) (t := s) (z := x)
          (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))
    simp only [Finset.sum_insert hi]
    rw [mvfderiv_fun_add (hf i (Finset.mem_insert_self i s)) hs]
    simp only [add_apply]
    rw [ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))]

/-- The two contracted moving-frame terms cancel for the actual Ricci endomorphism
when the frame velocity matrix is skew. -/
theorem ricciDerivative_frame_cancellation {ι : Type*} [Fintype ι]
    (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (q : ι → TangentSpace I x) (u w : TangentSpace I x)
    (hq : ∀ i j, inner ℝ (q i) (b j) + inner ℝ (b i) (q j) = 0) :
    (∑ i, inner ℝ (curvatureTensor (cov := cov) x (q i) u w) (b i)) +
      (∑ i, inner ℝ (curvatureTensor (cov := cov) x (b i) u w) (q i)) = 0 := by
  let L := ricciEndomorphism (cov := cov) x u w
  change (∑ i, inner ℝ (L (q i)) (b i)) +
    (∑ i, inner ℝ (L (b i)) (q i)) = 0
  have h1 (i) : inner ℝ (L (q i)) (b i) =
      ∑ j, inner ℝ (b j) (q i) * inner ℝ (L (b j)) (b i) := by
    conv_lhs => rw [← b.sum_repr' (q i)]
    simp only [map_sum, map_smul, sum_inner, real_inner_smul_left]
  have h2 (i) : inner ℝ (L (b i)) (q i) =
      ∑ j, inner ℝ (b j) (q i) * inner ℝ (L (b i)) (b j) := by
    conv_lhs => rw [← b.sum_repr' (q i)]
    simp only [inner_sum, real_inner_smul_right]
  simp only [h1, h2]
  rw [Finset.sum_comm (f := fun i j ↦
    inner ℝ (b j) (q i) * inner ℝ (L (b j)) (b i))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  have h := hq i j
  rw [real_inner_comm (q i) (b j), ← add_mul, add_comm, h, zero_mul]

/-- Metric compatibility differentiates local orthonormality into skew frame velocity.
Only orthonormality near the evaluation point is required. -/
theorem ricciDerivative_frame_velocity_skew {ι : Type*} [Fintype ι]
    (hmetric : cov.IsMetricCompatibleTangent)
    (e : ι → Π y : M, TangentSpace I y) (x : M) (v : TangentSpace I x)
    (he : ∀ i, MDiffAt (T% (e i)) x)
    (horth : ∀ᶠ y in nhds x, Orthonormal ℝ (fun i ↦ e i y)) (i j : ι) :
    inner ℝ (cov (e i) x v) (e j x) + inner ℝ (e i x) (cov (e j) x v) = 0 := by
  classical
  have heq : (fun y ↦ inner ℝ (e i y) (e j y)) =ᶠ[nhds x]
      (fun _ ↦ if i = j then (1 : ℝ) else 0) := by
    filter_upwards [horth] with y hy
    exact (orthonormal_iff_ite.mp hy) i j
  have hd := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ))
  have hz : mvfderiv (I := I) (fun y ↦ inner ℝ (e i y) (e j y)) x v = 0 := by
    simp only [mvfderiv, hd, mfderiv_const]
    rfl
  rw [hmetric (he i) (he j)] at hz
  exact hz

/-- Ricci is the orthonormal trace of the actual curvature tensor. -/
theorem ricciDerivative_ricci_eq_sum {ι : Type*} [Fintype ι]
    (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (u w : TangentSpace I x) :
    ricciCurvature (cov := cov) x u w =
      ∑ i, inner ℝ (curvatureTensor (cov := cov) x (b i) u w) (b i) := by
  rw [ricciCurvature_apply, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_comm _ _

/-- Intrinsic Ricci derivative equals contraction of the actual corrected curvature derivative.
The frame consists of C³ sections and is an orthonormal basis only near `x`; no
differential identity or parallel-frame condition is assumed. -/
theorem ricciDerivative_eq_trace_sections
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (hmetric : cov.IsMetricCompatibleTangent)
    {ι : Type} [Fintype ι]
    (e : ι → Π y : M, TangentSpace I y)
    (X U W : Π y : M, TangentSpace I y) (x : M)
    (he : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (e i)))
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% X))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% U))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W))
    (hb : ∀ᶠ y in nhds x, ∃ b : OrthonormalBasis ι ℝ (TangentSpace I y),
      ∀ i, b i = e i y) :
    SchurRigidity.bilinearDerivative cov (ricciCurvature (cov := cov)) U W x (X x) =
      ∑ i, inner ℝ (cov.secondBianchiAux X (e i) U W x) (e i x) := by
  classical
  have he₂ i := (he i).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have he₁ i := (he i).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hU₂ := hU.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hU₁ := hU.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hW₂ := hW.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hXe i := cov.contMDiff_along (n := 2) hX (he i)
  have hXU := cov.contMDiff_along (n := 2) hX hU
  have hXW := cov.contMDiff_along (n := 2) hX hW
  have hemd i := ((he i) x).mdifferentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  let f : ι → M → ℝ := fun i y ↦ inner ℝ (cov.curvatureAux (e i) U W y) (e i y)
  have hf i : MDiffAt (f i) x :=
    mdiffAt_inner_sections
      (((ricciDerivative_curvatureAux_contMDiff cov (he₂ i) hU₂ hW) x).mdifferentiableAt
        one_ne_zero) (hemd i)
  have heq : (fun y ↦ ricciCurvature (cov := cov) y (U y) (W y)) =ᶠ[nhds x]
      (fun y ↦ ∑ i, f i y) := by
    filter_upwards [hb] with y hy
    obtain ⟨b, hbe⟩ := hy
    rw [ricciDerivative_ricci_eq_sum cov y b]
    apply Finset.sum_congr rfl
    intro i _
    rw [hbe i]
    exact congrArg (fun z ↦ inner ℝ z (e i y))
      (cov.curvatureAux_eq_curvatureTensor_apply_of_contMDiff
        (he₁ i) hU₁ hW₂ y).symm
  have hdiff : mvfderiv (I := I)
      (fun y ↦ ricciCurvature (cov := cov) y (U y) (W y)) x (X x) =
      ∑ i, mvfderiv (I := I) (f i) x (X x) := by
    have hd := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ))
    have hm : mvfderiv (I := I)
        (fun y ↦ ricciCurvature (cov := cov) y (U y) (W y)) x =
        mvfderiv (I := I) (fun y ↦ ∑ i, f i y) x := by
      ext v
      change mfderiv I 𝓘(ℝ) (fun y ↦ ricciCurvature (cov := cov) y (U y) (W y)) x v =
        mfderiv I 𝓘(ℝ) (fun y ↦ ∑ i, f i y) x v
      rw [hd]
      rfl
    rw [hm]
    exact ricciDerivative_mvfderiv_sum Finset.univ f x (X x) (fun i _ ↦ hf i)
  obtain ⟨b, hbe⟩ := hb.self_of_nhds
  have horth : ∀ᶠ y in nhds x, Orthonormal ℝ (fun i ↦ e i y) := by
    filter_upwards [hb] with y hy
    obtain ⟨by', hby⟩ := hy
    have hh : (fun i ↦ e i y) = by' := funext (fun i ↦ (hby i).symm)
    rw [hh]
    exact by'.orthonormal
  have hc := ricciDerivative_frame_cancellation cov x b
    (fun i ↦ cov.along X (e i) x) (U x) (W x) (by
      intro i j
      simp only [hbe, CovariantDerivative.along]
      exact ricciDerivative_frame_velocity_skew cov hmetric e x (X x) hemd horth i j)
  simp only [hbe] at hc
  have hd i := ricciDerivative_curvature_inner cov hmetric X (e i) U W (e i) x
    (he₂ i) hU₂ hW (hemd i)
  have hEval (Y Z V : Π y : M, TangentSpace I y)
      (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Y))
      (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Z))
      (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% V)) :=
    cov.curvatureAux_eq_curvatureTensor_apply_of_contMDiff hY hZ hV x
  have hd' i : mvfderiv (I := I) (f i) x (X x) =
      inner ℝ (cov.secondBianchiAux X (e i) U W x) (e i x) +
      inner ℝ (cov.curvatureTensor x (cov.along X (e i) x) (U x) (W x)) (e i x) +
      inner ℝ (cov.curvatureTensor x (e i x) (cov.along X U x) (W x)) (e i x) +
      inner ℝ (cov.curvatureTensor x (e i x) (U x) (cov.along X W x)) (e i x) +
      inner ℝ (cov.curvatureTensor x (e i x) (U x) (W x)) (cov.along X (e i) x) := by
    simpa only [hEval _ _ _ ((hXe i).of_le (by norm_num)) hU₁ hW₂,
      hEval _ _ _ (he₁ i) (hXU.of_le (by norm_num)) hW₂,
      hEval _ _ _ (he₁ i) hU₁ hXW, hEval _ _ _ (he₁ i) hU₁ hW₂] using hd i
  have hrU := ricciDerivative_ricci_eq_sum cov x b (cov.along X U x) (W x)
  have hrW := ricciDerivative_ricci_eq_sum cov x b (U x) (cov.along X W x)
  simp only [hbe] at hrU hrW
  unfold SchurRigidity.bilinearDerivative
  rw [hdiff]
  change (∑ i, mvfderiv (I := I) (f i) x (X x)) -
    ricciCurvature (cov := cov) x (cov.along X U x) (W x) -
    ricciCurvature (cov := cov) x (U x) (cov.along X W x) = _
  simp only [hd', Finset.sum_add_distrib]
  rw [hrU, hrW]
  linarith

/-- The Ricci trace bridge specialized to the Schur hypothesis `Ric = f g`. -/
theorem ricciDerivative_trace_eq_of_ricci_eq_mul_inner
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (hmetric : cov.IsMetricCompatibleTangent)
    {ι : Type} [Fintype ι]
    (e : ι → Π y : M, TangentSpace I y)
    (X U W : Π y : M, TangentSpace I y) (x : M)
    (he : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (e i)))
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% X))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% U))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W))
    (hb : ∀ᶠ y in nhds x, ∃ b : OrthonormalBasis ι ℝ (TangentSpace I y),
      ∀ i, b i = e i y)
    (f : M → ℝ) (hf : MDiffAt f x)
    (hRic : ∀ y u v, ricciCurvature (cov := cov) y u v = f y * inner ℝ u v) :
    (∑ i, inner ℝ (cov.secondBianchiAux X (e i) U W x) (e i x)) =
      mvfderiv (I := I) f x (X x) * inner ℝ (U x) (W x) := by
  rw [← ricciDerivative_eq_trace_sections cov hmetric e X U W x he hX hU hW hb]
  exact SchurRigidity.bilinearDerivative_eq_of_eq_mul_inner cov hmetric _ f hRic
    U W x (X x) hf
    ((hU x).mdifferentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0))
    ((hW x).mdifferentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0))

/-- The actual curvature endomorphism paired with the metric; its metric trace is Ricci. -/
def ricciDerivative_curvaturePair (x : M) (u w : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  (innerₗ (TangentSpace I x)).comp (ricciEndomorphism (cov := cov) x u w)

@[simp] theorem ricciDerivative_curvaturePair_apply (x : M)
    (u w a b : TangentSpace I x) :
    ricciDerivative_curvaturePair cov x u w a b =
      inner ℝ (curvatureTensor (cov := cov) x a u w) b := rfl

/-- This pairing contracts to the existing intrinsic Ricci definition. -/
theorem ricciDerivative_metricTrace_curvaturePair
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (U W : Π y : M, TangentSpace I y) (x : M) :
    SchurRigidity.metricTrace (fun y ↦ ricciDerivative_curvaturePair cov y (U y) (W y)) x =
      ricciCurvature (cov := cov) x (U x) (W x) := by
  rw [SchurRigidity.metricTrace_eq_sum _ x (stdOrthonormalBasis ℝ (TangentSpace I x)),
    ricciDerivative_ricci_eq_sum cov x (stdOrthonormalBasis ℝ (TangentSpace I x))]
  rfl

/-- Smooth section components of the actual curvature pairing are differentiable. -/
theorem ricciDerivative_curvaturePair_mdiffAt
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (Y U W V : Π y : M, TangentSpace I y) (x : M)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Y))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% U))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W))
    (hV : MDiffAt (T% V) x) :
    MDiffAt (fun y ↦ ricciDerivative_curvaturePair cov y (U y) (W y) (Y y) (V y)) x := by
  have heq : (fun y ↦ ricciDerivative_curvaturePair cov y (U y) (W y) (Y y) (V y)) =
      (fun y ↦ inner ℝ (cov.curvatureAux Y U W y) (V y)) := by
    funext y
    rw [ricciDerivative_curvaturePair_apply,
      cov.curvatureAux_eq_curvatureTensor_apply_of_contMDiff
        (hY.of_le (by norm_num)) (hU.of_le (by norm_num)) (hW.of_le (by norm_num)) y]
  rw [heq]
  exact mdiffAt_inner_sections
    (((ricciDerivative_curvatureAux_contMDiff cov hY hU hW) x).mdifferentiableAt
      one_ne_zero) hV

/-- Differentiating the actual curvature pairing leaves precisely the two free
Ricci-slot corrections after its own two bilinear slots have been corrected. -/
theorem ricciDerivative_curvaturePair_bilinearDerivative
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (hmetric : cov.IsMetricCompatibleTangent)
    (X Y U W V : Π y : M, TangentSpace I y) (x : M)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% Y))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% U))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W))
    (hV : MDiffAt (T% V) x) :
    SchurRigidity.bilinearDerivative cov
      (fun y ↦ ricciDerivative_curvaturePair cov y (U y) (W y)) Y V x (X x) =
      inner ℝ (cov.secondBianchiAux X Y U W x) (V x) +
      inner ℝ (cov.curvatureTensor x (Y x) (cov.along X U x) (W x)) (V x) +
      inner ℝ (cov.curvatureTensor x (Y x) (U x) (cov.along X W x)) (V x) := by
  have hY₂ := hY.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hY₁ := hY.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hU₂ := hU.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hU₁ := hU.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hW₂ := hW.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have heq : (fun y ↦ ricciDerivative_curvaturePair cov y (U y) (W y) (Y y) (V y)) =
      (fun y ↦ inner ℝ (cov.curvatureAux Y U W y) (V y)) := by
    funext y
    rw [ricciDerivative_curvaturePair_apply,
      cov.curvatureAux_eq_curvatureTensor_apply_of_contMDiff hY₁ hU₁ hW₂ y]
  have hd := ricciDerivative_curvature_inner cov hmetric X Y U W V x hY₂ hU₂ hW hV
  rw [cov.curvatureAux_eq_curvatureTensor_apply_of_contMDiff
      ((cov.contMDiff_along (n := 2) hX hY).of_le (by norm_num)) hU₁ hW₂ x,
    cov.curvatureAux_eq_curvatureTensor_apply_of_contMDiff hY₁
      ((cov.contMDiff_along (n := 2) hX hU).of_le (by norm_num)) hW₂ x,
    cov.curvatureAux_eq_curvatureTensor_apply_of_contMDiff hY₁ hU₁
      (cov.contMDiff_along (n := 2) hX hW) x,
    cov.curvatureAux_eq_curvatureTensor_apply_of_contMDiff hY₁ hU₁ hW₂ x] at hd
  unfold SchurRigidity.bilinearDerivative
  rw [heq, hd]
  simp only [ricciDerivative_curvaturePair_apply, CovariantDerivative.along]
  abel

/-- The intrinsic Ricci derivative trace bridge with an internally constructed
frame. There is no local orthonormal-frame or contraction-identity hypothesis. -/
theorem ricciDerivative_eq_trace_schurFrame
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    (hmetric : cov.IsMetricCompatibleTangent)
    {ι : Type} [Fintype ι] [DecidableEq ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (X U W : Π y : M, TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% X))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% U))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W)) :
    SchurRigidity.bilinearDerivative cov cov.ricciCurvature U W x (X x) =
      ∑ i, inner ℝ (cov.secondBianchiAux X
        (schurFrame x b.toBasis i) U W x) (b i) := by
  let A := fun y ↦ ricciDerivative_curvaturePair cov y (U y) (W y)
  let e := schurFrame (I := I) x b.toBasis
  have he (i : ι) : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (e i)) :=
    schurFrame_contMDiff_three x b.toBasis i
  have hx (i : ι) : e i x = b i := schurFrame_at x b.toBasis i
  have hmd (i : ι) : MDiffAt (T% (e i)) x :=
    ((he i) x).mdifferentiableAt (by norm_num)
  have ha (i j : ι) : MDiffAt (fun y ↦ A y (e i y) (e j y)) x :=
    ricciDerivative_curvaturePair_mdiffAt cov (e i) U W (e j) x
      ((he i).of_le (by norm_num)) (hU.of_le (by norm_num)) hW (hmd j)
  have hd := SchurRigidity.mvfderiv_metricTrace_eq_sum_schurFrame cov hmetric A x b ha (X x)
  have htrace : SchurRigidity.metricTrace A =
      (fun y ↦ cov.ricciCurvature y (U y) (W y)) :=
    funext (ricciDerivative_metricTrace_curvaturePair cov U W)
  rw [htrace] at hd
  have hi (i : ι) : SchurRigidity.bilinearDerivative cov A (e i) (e i) x (X x) =
      inner ℝ (cov.secondBianchiAux X (e i) U W x) (b i) +
      inner ℝ (cov.curvatureTensor x (b i) (cov.along X U x) (W x)) (b i) +
      inner ℝ (cov.curvatureTensor x (b i) (U x) (cov.along X W x)) (b i) := by
    simpa only [hx] using ricciDerivative_curvaturePair_bilinearDerivative cov
      hmetric X (e i) U W (e i) x hX (he i) hU hW (hmd i)
  change mvfderiv (I := I) (fun y ↦ cov.ricciCurvature y (U y) (W y)) x (X x) =
    ∑ i, SchurRigidity.bilinearDerivative cov A (e i) (e i) x (X x) at hd
  simp_rw [hi, Finset.sum_add_distrib] at hd
  rw [← ricciDerivative_ricci_eq_sum cov x b (cov.along X U x) (W x),
    ← ricciDerivative_ricci_eq_sum cov x b (U x) (cov.along X W x)] at hd
  unfold SchurRigidity.bilinearDerivative
  change mvfderiv (I := I) (fun y ↦ cov.ricciCurvature y (U y) (W y)) x (X x) -
    cov.ricciCurvature x (cov.along X U x) (W x) -
    cov.ricciCurvature x (U x) (cov.along X W x) = _
  linarith

/-- Actual Ricci evaluations on sufficiently smooth fields are differentiable. -/
theorem ricciDerivative_ricci_mdiffAt
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    (U W : Π y : M, TangentSpace I y) (x : M)
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% U))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W)) :
    MDiffAt (fun y ↦ cov.ricciCurvature y (U y) (W y)) x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  let A := fun y ↦ ricciDerivative_curvaturePair cov y (U y) (W y)
  have ha (i j) : MDiffAt (fun y ↦ A y
      (schurFrame x b.toBasis i y) (schurFrame x b.toBasis j y)) x :=
    ricciDerivative_curvaturePair_mdiffAt cov _ U W _ x
      ((schurFrame_contMDiff_three x b.toBasis i).of_le (by norm_num)) hU hW
      (((schurFrame_contMDiff_three x b.toBasis j) x).mdifferentiableAt (by norm_num))
  have hd := SchurRigidity.mdifferentiableAt_metricTrace_schurFrame A x b ha
  have heq : SchurRigidity.metricTrace A =
      (fun y ↦ cov.ricciCurvature y (U y) (W y)) :=
    funext (ricciDerivative_metricTrace_curvaturePair cov U W)
  rwa [heq] at hd

/-- Full C¹ evaluation regularity of the intrinsic Ricci tensor, including on
arbitrary differentiable sections, is derived from its local components. -/
theorem ricciDerivative_ricci_evaluation_regular
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    (x : M) : SchurRigidity.BilinearEvaluationMDifferentiableAt cov.ricciCurvature x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  apply SchurRigidity.bilinearEvaluationMDifferentiableAt_of_localFrame
    cov.ricciCurvature (schurModelBasis x b.toBasis) x
  intro i j
  have hd := ricciDerivative_ricci_mdiffAt cov
    (schurFrame x b.toBasis i) (schurFrame x b.toBasis j) x
    ((schurFrame_contMDiff_three x b.toBasis i).of_le (by norm_num))
    (schurFrame_contMDiff_three x b.toBasis j)
  apply hd.congr_of_eventuallyEq
  filter_upwards [schurFrame_eventuallyEq_localFrame x b.toBasis] with y hy
  rw [hy i, hy j]

end CovariantDerivative
