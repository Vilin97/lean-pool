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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurckTraceDerivative
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConnectionChange
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TangentFrameCoordinate
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.VectorValuedBilinearFrameCoordinate
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.MetricDefectLocalFrame
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.BackgroundNormalFrameBridge

/-!
# Intrinsic trace derivative for the standard DeTurck field

This file records the normal-point local-frame algebra needed to convert the
inverse-Gram derivative in the standard DeTurck trace into an intrinsic
metric-defect formula.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Filter Matrix
open scoped Manifold ContDiff Topology BigOperators

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TCorr" =>
  (fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x)

local instance tangentFiberBundle : FiberBundle E TM := TangentSpace.fiberBundle
local instance tangentVectorBundle : VectorBundle ℝ E TM := TangentSpace.vectorBundle

/-- The local Gram matrix is the identity when the local-frame values are
orthonormal at the selected point. -/
private theorem localFrameGramMatrix_eq_one_of_orthonormal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M)) (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (horth : ∀ i j : ι,
      (g t).inner x (e.localFrame b i x) (e.localFrame b j x) =
        if i = j then 1 else 0) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    (show Matrix ι ι ℝ from
      CovariantDerivative.localFrameGramMatrix (I := I) e b x) = 1 := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  ext i j
  change (g t).inner x (e.localFrame b i x) (e.localFrame b j x) =
    (1 : Matrix ι ι ℝ) i j
  simpa [Matrix.one_apply] using horth i j

private theorem neg_one_mul_mul_one_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (i j : ι) :
    (- ((1 : Matrix ι ι ℝ) * D * (1 : Matrix ι ι ℝ))) i j = - D i j := by
  rw [Matrix.one_mul, Matrix.mul_one]
  rfl

private theorem neg_one_mul_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (i j : ι) :
    (- ((1 : Matrix ι ι ℝ) * D)) i j = - D i j := by
  rw [Matrix.one_mul]
  rfl

/-- At an orthonormal frame value, inverse-Gram differentiation is the
negative derivative of the Gram coefficient. -/
private theorem mvfderiv_localFrameInverseGramMatrix_eq_neg_mvfderiv_gram_of_orthonormal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M)) (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (u : TM x) (i j : ι)
    (horth : ∀ p q : ι,
      (g t).inner x (e.localFrame b p x) (e.localFrame b q x) =
        if p = q then 1 else 0) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
    mvfderiv (I := I)
        (fun y => CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j) x u =
      - mvfderiv (I := I)
        (fun y => CovariantDerivative.localFrameGramMatrix (I := I) e b y i j) x u := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  have hgram : (show Matrix ι ι ℝ from
      CovariantDerivative.localFrameGramMatrix (I := I) e b x) = 1 :=
    localFrameGramMatrix_eq_one_of_orthonormal (I := I) (M := M) g t e b hx horth
  rw [CovariantDerivative.mvfderiv_localFrameInverseGramMatrix_apply
    (I := I) (E := E) e b hx u i j]
  rw [hgram]
  simp only [inv_one]
  exact neg_one_mul_mul_one_apply
    (show Matrix ι ι ℝ from fun p q => mvfderiv (I := I)
      (fun y => CovariantDerivative.localFrameGramMatrix (I := I) e b y p q) x u) i j

/-- A frame coefficient equals the metric pairing with the corresponding
frame vector at an orthonormal point. -/
private theorem localFrameCoeff_eq_inner_of_orthonormal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M)) (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (horth : ∀ i j : ι,
      (g t).inner x (e.localFrame b i x) (e.localFrame b j x) =
        if i = j then 1 else 0)
    (k : ι) (z : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    e.localFrameCoeff I b k x z = (g t).inner x (e.localFrame b k x) z := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hcoeff : e.localFrameCoeff I b k x z = (e.basisAt b hx).repr z k := by
    simpa using
      (Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
        (I := I) (e := e) (b := b) hx (FiberBundle.extend E z) k)
  have horthBasis (i : ι) :
      inner ℝ ((e.basisAt b hx) k) ((e.basisAt b hx) i) =
        if k = i then 1 else 0 := by
    change (g t).inner x ((e.basisAt b hx) k) ((e.basisAt b hx) i) = _
    simpa [Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hx]
      using horth k i
  calc
    e.localFrameCoeff I b k x z = (e.basisAt b hx).repr z k := hcoeff
    _ = (g t).inner x (e.localFrame b k x) z := by
      rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hx]
      change (e.basisAt b hx).repr z k = inner ℝ ((e.basisAt b hx) k) z
      conv_rhs => rw [← (e.basisAt b hx).sum_repr z]
      rw [inner_sum]
      simp only [real_inner_smul_right]
      simp [horthBasis]

/-- Pointwise reconstruction in a genuine local tangent frame. -/
private theorem localFrame_eq_sum_localFrameCoeff_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (z : TM x) :
    z = ∑ i, e.localFrameCoeff I b i x z • e.localFrame b i x := by
  simpa using
    (e.eq_sum_localFrameCoeff_smul (I := I) (b := b)
      (s := FiberBundle.extend E z) (x' := x) hx)

/-- The tangent-bundle local coordinate formula for a covariant derivative. -/
private theorem localFrameCoeff_covariantDerivative_eq_mvfderiv_add_connection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    {σ : ∀ y : M, TM y} (hσ : MDiffAt (T% σ) x)
    (u : TM x) (k : ι) :
    e.localFrameCoeff I b k x ((background t) σ x u) =
      mvfderiv (I := I) (fun y => e.localFrameCoeff I b k y (σ y)) x u +
        ∑ q, e.localFrameCoeff I b q x (σ x) *
          e.localFrameCoeff I b k x ((background t) (e.localFrame b q) x u) := by
  exact CovariantDerivative.TangentFrame.localFrameCoeff_covariantDerivative_eq_mvfderiv_add_connection
      (I := I) e b (background t) hx hσ u k

/-- Finite-dimensional cancellation of all local-frame connection
coefficients in a differentiated metric trace. -/
private theorem normal_trace_component_cancellation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → ι → ι → ℝ) (Γ : ι → ι → ℝ)
    (D DA : ι → ι → ℝ) (W dW covW : ι → ℝ)
    (hW : ∀ q, W q = ∑ i, C q i i)
    (k : ι)
    (hdW : dW k =
      (∑ i, DA i i) +
        (∑ i, ∑ p, Γ p i * C k p i) +
        (∑ i, ∑ p, Γ p i * C k i p) -
        (∑ i, ∑ p, C p i i * Γ k p) -
        (∑ i, ∑ j, C k i j * D i j) -
        (∑ i, ∑ j, C k i j * Γ j i) -
        (∑ i, ∑ j, C k i j * Γ i j))
    (hcovW : ∀ k, covW k = dW k + ∑ q, W q * Γ k q)
    :
    covW k = (∑ i, DA i i) - ∑ i, ∑ j, D i j * C k i j := by
  have hWsum : ∑ q, W q * Γ k q = ∑ i, ∑ p, C p i i * Γ k p := by
    simp_rw [hW]
    calc
      ∑ q, (∑ i, C q i i) * Γ k q = ∑ q, ∑ i, C q i i * Γ k q := by
        apply Finset.sum_congr rfl
        intro q _
        exact Finset.sum_mul Finset.univ (fun i => C q i i) (Γ k q)
      _ = ∑ i, ∑ q, C q i i * Γ k q := Finset.sum_comm
      _ = ∑ i, ∑ p, C p i i * Γ k p := rfl
  have hswap : ∑ i, ∑ p, Γ p i * C k p i =
      ∑ i, ∑ j, C k i j * Γ i j := by
    calc
      ∑ i, ∑ p, Γ p i * C k p i = ∑ p, ∑ i, Γ p i * C k p i :=
        Finset.sum_comm
      _ = ∑ i, ∑ j, C k i j * Γ i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hswap' : ∑ i, ∑ p, Γ p i * C k i p =
      ∑ i, ∑ j, C k i j * Γ j i := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hD : ∑ i, ∑ j, C k i j * D i j = ∑ i, ∑ j, D i j * C k i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcovW k, hdW, hWsum, hswap, hswap', hD]
  ring

/-- Substitute the moving-frame product rule and the Gram derivative into a
calibrated raw trace derivative.  This leaves exactly the connection terms
which cancel against the covariant derivative of the trace. -/
private theorem normal_trace_mvfderiv_expansion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → ι → ι → ℝ) (Γ : ι → ι → ℝ)
    (D : ι → ι → ℝ) (DA : ι → ι → ι → ℝ) (dC : ι → ι → ι → ℝ)
    (dG : ι → ι → ℝ) (dW : ι → ℝ)
    (hdC : ∀ k i j, dC k i j =
      DA k i j + (∑ p, Γ p i * C k p j) +
        ((∑ p, Γ p j * C k i p) - ∑ p, C p i j * Γ k p))
    (hdG : ∀ i j, dG i j = D i j + Γ j i + Γ i j)
    (hraw : ∀ k, dW k = ∑ i, ∑ j,
      ((if i = j then 1 else 0) * dC k i j + C k i j * (- dG i j)))
    (k : ι) :
    dW k =
      (∑ i, DA k i i) +
        (∑ i, ∑ p, Γ p i * C k p i) +
        (∑ i, ∑ p, Γ p i * C k i p) -
        (∑ i, ∑ p, C p i i * Γ k p) -
        (∑ i, ∑ j, C k i j * D i j) -
        (∑ i, ∑ j, C k i j * Γ j i) -
        (∑ i, ∑ j, C k i j * Γ i j) := by
  have hdiag (f : ι → ι → ℝ) :
      (∑ i, ∑ j, if i = j then f i j else 0) = ∑ i, f i i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_ite_eq Finset.univ i]
    simp
  rw [hraw k]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, mul_neg]
  rw [hdiag]
  simp_rw [hdC, hdG]
  simp_rw [mul_add]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  ring

/-- The local component derivative of the explicit correction, with all three
moving-frame terms explicit. -/
private theorem mvfderiv_standardDeTurckCorrectionLocalComponent_eq_covariantDerivative_add_connection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (u : TM x) (k i j : ι)
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) y
        (explicitLeviCivitaCorrection (I := I) (M := M) g background t y)) x) :
    mvfderiv (I := I)
        (standardDeTurckCorrectionLocalComponent (I := I) (M := M)
          g background t e b k i j) x u =
      e.localFrameCoeff I b k x
        (CovariantDerivative.covariantDerivativeOneForm (background t)
          (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x u
          (e.localFrame b j x) (e.localFrame b i x)) +
        (∑ p, e.localFrameCoeff I b p x
            ((background t) (e.localFrame b i) x u) *
          standardDeTurckCorrectionLocalComponent (I := I) (M := M)
            g background t e b k p j x) +
        ((∑ p, e.localFrameCoeff I b p x
            ((background t) (e.localFrame b j) x u) *
          standardDeTurckCorrectionLocalComponent (I := I) (M := M)
            g background t e b k i p x) -
          ∑ p, standardDeTurckCorrectionLocalComponent (I := I) (M := M)
            g background t e b p i j x *
          e.localFrameCoeff I b k x
            ((background t) (e.localFrame b p) x u)) := by
  change mvfderiv (I := I) (fun y =>
    e.localFrameCoeff I b k y
      (explicitLeviCivitaCorrection (I := I) (M := M) g background t y
        (e.localFrame b j y) (e.localFrame b i y))) x u = _
  simpa only [standardDeTurckCorrectionLocalComponent] using
    (CovariantDerivative.mvfderiv_localFrameCoeff_vectorValuedBilinear_apply_eq_covariantDerivative_add_connection
        (I := I) (M := M) e b (background t) hx u k i j hA)

/-- At an orthonormal frame value, the standard DeTurck coefficient is the
ordinary diagonal trace of the correction components. -/
private theorem standardDeTurckVectorField_localFrameCoeff_eq_sum_diagonal_of_orthonormal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (k : ι)
    (horth : ∀ p q : ι,
      (g t).inner x (e.localFrame b p x) (e.localFrame b q x) =
        if p = q then 1 else 0) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    e.localFrameCoeff I b k x
      (standardDeTurckVectorField (I := I) (M := M) g background t x) =
      ∑ i, standardDeTurckCorrectionLocalComponent (I := I) (M := M)
        g background t e b k i i x := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hgram : (show Matrix ι ι ℝ from
      CovariantDerivative.localFrameGramMatrix (I := I) e b x) = 1 :=
    localFrameGramMatrix_eq_one_of_orthonormal (I := I) (M := M) g t e b hx horth
  have hinv : CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x =
      (1 : Matrix ι ι ℝ) := by
    change (show Matrix ι ι ℝ from
      CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹ = 1
    rw [hgram]
    exact inv_one
  rw [standardDeTurckVectorField_localFrameCoeff_eq_sum_correctionComponent
    (I := I) (M := M) g background t e b hx k, hinv]
  simp [Matrix.one_apply]

/-- The local inverse-Gram expression makes the standard DeTurck field
differentiatable whenever the complete correction tensor is differentiable. -/
private theorem standardDeTurckVectorField_mdifferentiableAt_of_mdiff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) y
        (explicitLeviCivitaCorrection (I := I) (M := M) g background t y)) x) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
    MDiffAt (T% (standardDeTurckVectorField (I := I) (M := M) g background t)) x := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  apply (mdifferentiableAt_iff_localFrameCoeff (I := I) (e := e) (b := b)
    (s := standardDeTurckVectorField (I := I) (M := M) g background t) hx).mpr
  intro k
  have hInv : ∀ i j : ι, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j) x := by
    intro i j
    have hmatrix := CovariantDerivative.contMDiffOn_localFrameGramMatrix_inv
      (I := I) (E := E) e b e.open_baseSet (fun _ hy => hy)
    rw [contMDiffOn_pi_space] at hmatrix
    have hi := hmatrix i
    rw [contMDiffOn_pi_space] at hi
    exact (hi j x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)
      |>.mdifferentiableAt (by norm_num)
  have hterm : ∀ i j : ι, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y =>
        CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j *
          standardDeTurckCorrectionLocalComponent (I := I) (M := M)
            g background t e b k i j y) x := by
    intro i j
    exact (hInv i j).mul
      (standardDeTurckCorrectionLocalComponent_mdifferentiableAt_of_mdiff
        (I := I) (M := M) g background t e b hx hA k i j)
  have hsum : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => ∑ i : ι, ∑ j : ι,
        CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j *
          standardDeTurckCorrectionLocalComponent (I := I) (M := M)
            g background t e b k i j y) x := by
    have mdiff_sum (F : ι → M → ℝ)
        (hF : ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, ℝ) (F i) x) :
        MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ∑ i : ι, F i y) x := by
      have hsumDiff (s : Finset ι) :
          MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ s, F i y) x := by
        induction s using Finset.induction_on with
        | empty => simpa using (mdifferentiableAt_const (c := (0 : ℝ)) (x := x))
        | @insert i s hnot ih =>
            simp only [Finset.sum_insert hnot]
            rw [show (fun y => F i y + ∑ j ∈ s, F j y) =
              F i + (fun y => ∑ j ∈ s, F j y) by rfl]
            exact (hF i).add ih
      simpa using hsumDiff Finset.univ
    have hinner (i : ι) : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y => ∑ j : ι,
          CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j *
            standardDeTurckCorrectionLocalComponent (I := I) (M := M)
              g background t e b k i j y) x :=
      mdiff_sum (fun j y =>
        CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j *
          standardDeTurckCorrectionLocalComponent (I := I) (M := M)
            g background t e b k i j y) (fun j => hterm i j)
    exact mdiff_sum (fun i y => ∑ j : ι,
      CovariantDerivative.localFrameInverseGramMatrix (I := I) e b y i j *
        standardDeTurckCorrectionLocalComponent (I := I) (M := M)
          g background t e b k i j y) hinner
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  simpa using
    (standardDeTurckVectorField_localFrameCoeff_eq_sum_correctionComponent
      (I := I) (M := M) g background t e b hy k)

/-- In a local frame calibrated at `x`, the covariant derivative of the
standard DeTurck trace has the intrinsic metric-defect correction. -/
private theorem localFrameCoeff_covariantDerivative_standardDeTurckVectorField_eq_trace_of_orthonormal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (u : TM x) (k : ι)
    (horth : ∀ p q : ι,
      (g t).inner x (e.localFrame b p x) (e.localFrame b q x) =
        if p = q then 1 else 0)
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) y
        (explicitLeviCivitaCorrection (I := I) (M := M) g background t y)) x) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
    e.localFrameCoeff I b k x
        ((background t) (standardDeTurckVectorField (I := I) (M := M)
          g background t) x u) =
      ((∑ i : ι, e.localFrameCoeff I b k x
        (CovariantDerivative.covariantDerivativeOneForm (background t)
          (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x u
          (e.localFrame b i x) (e.localFrame b i x)))) -
        (∑ i : ι, ∑ j : ι,
          (background t).metricDefect x (e.localFrame b i x)
            (e.localFrame b j x) u *
          standardDeTurckCorrectionLocalComponent (I := I) (M := M)
            g background t e b k i j x) := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let C : ι → ι → ι → ℝ := fun q i j =>
    standardDeTurckCorrectionLocalComponent (I := I) (M := M)
      g background t e b q i j x
  let Γ : ι → ι → ℝ := fun p i =>
    e.localFrameCoeff I b p x ((background t) (e.localFrame b i) x u)
  let D : ι → ι → ℝ := fun i j =>
    (background t).metricDefect x (e.localFrame b i x) (e.localFrame b j x) u
  let DA : ι → ι → ι → ℝ := fun q i j =>
    e.localFrameCoeff I b q x
      (CovariantDerivative.covariantDerivativeOneForm (background t)
        (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x u
        (e.localFrame b j x) (e.localFrame b i x))
  let dC : ι → ι → ι → ℝ := fun q i j =>
    mvfderiv (I := I)
      (standardDeTurckCorrectionLocalComponent (I := I) (M := M)
        g background t e b q i j) x u
  let dG : ι → ι → ℝ := fun i j =>
    mvfderiv (I := I)
      (fun y => CovariantDerivative.localFrameGramMatrix (I := I) e b y i j) x u
  let W : ι → ℝ := fun q =>
    e.localFrameCoeff I b q x
      (standardDeTurckVectorField (I := I) (M := M) g background t x)
  let dW : ι → ℝ := fun q =>
    mvfderiv (I := I) (fun y => e.localFrameCoeff I b q y
      (standardDeTurckVectorField (I := I) (M := M) g background t y)) x u
  let covW : ι → ℝ := fun q =>
    e.localFrameCoeff I b q x ((background t)
      (standardDeTurckVectorField (I := I) (M := M) g background t) x u)
  have horth' : ∀ p q : ι,
      inner ℝ (e.localFrame b p x) (e.localFrame b q x) =
        if p = q then 1 else 0 := by
    intro p q
    have hpq := horth p q
    change inner ℝ (e.localFrame b p x) (e.localFrame b q x) =
      if p = q then 1 else 0 at hpq
    exact hpq
  have hgram : (show Matrix ι ι ℝ from
      CovariantDerivative.localFrameGramMatrix (I := I) e b x) = 1 :=
    localFrameGramMatrix_eq_one_of_orthonormal (I := I) (M := M)
      g t e b hx horth
  have hinv : CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x =
      (1 : Matrix ι ι ℝ) := by
    change (show Matrix ι ι ℝ from
      CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹ = 1
    rw [hgram]
    exact inv_one
  have hgramInv :
      (show Matrix ι ι ℝ from
        CovariantDerivative.localFrameGramMatrix (I := I) e b x)⁻¹ =
        (1 : Matrix ι ι ℝ) := by
    rw [hgram]
    exact inv_one
  have hW (q : ι) : W q = ∑ i, C q i i := by
    dsimp [W, C]
    exact standardDeTurckVectorField_localFrameCoeff_eq_sum_diagonal_of_orthonormal
      (I := I) (M := M) g background t e b hx q horth
  have hdC (q i j : ι) : dC q i j =
      DA q i j + (∑ p, Γ p i * C q p j) +
        ((∑ p, Γ p j * C q i p) - ∑ p, C p i j * Γ q p) := by
    dsimp [dC, DA, Γ, C]
    simpa using
      (mvfderiv_standardDeTurckCorrectionLocalComponent_eq_covariantDerivative_add_connection
        (I := I) (M := M) g background t e b hx u q i j hA)
  have hdG (i j : ι) : dG i j = D i j + Γ j i + Γ i j := by
    dsimp [dG, D, Γ]
    simpa using
      (CovariantDerivative.mvfderiv_localFrameGramMatrix_apply_eq_metricDefect_add_connection
        (I := I) (E := E) (background t) e b hx u i j horth')
  have hraw (q : ι) : dW q = ∑ i, ∑ j,
      ((if i = j then 1 else 0) * dC q i j + C q i j * (- dG i j)) := by
    dsimp [dW, dC, C, dG]
    have hraw0 :=
      mvfderiv_standardDeTurckVectorField_localFrameCoeff_apply_of_mdiff
        (I := I) (M := M) g background t e b hx u q hA
    rw [hinv, hgramInv] at hraw0
    let dGm : Matrix ι ι ℝ := fun p r => mvfderiv (I := I)
      (fun y => CovariantDerivative.localFrameGramMatrix (I := I) e b y p r) x u
    change dW q = ∑ i, ∑ j,
      ((1 : Matrix ι ι ℝ) i j * dC q i j + C q i j *
        (- ((1 : Matrix ι ι ℝ) * dGm * (1 : Matrix ι ι ℝ))) i j) at hraw0
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.neg_apply] at hraw0
    simpa only [Matrix.one_apply, Matrix.neg_apply, ite_mul,
      one_mul, zero_mul, Finset.sum_add_distrib, mul_neg] using hraw0
  have hWdiff : MDiffAt
      (T% (standardDeTurckVectorField (I := I) (M := M) g background t)) x :=
    standardDeTurckVectorField_mdifferentiableAt_of_mdiff
      (I := I) (M := M) g background t e b hx hA
  have hcovW (q : ι) : covW q = dW q + ∑ r, W r * Γ q r := by
    dsimp [covW, dW, W, Γ]
    exact localFrameCoeff_covariantDerivative_eq_mvfderiv_add_connection
      (I := I) (M := M) background t e b hx hWdiff u q
  have hdW := normal_trace_mvfderiv_expansion C Γ D DA dC dG dW hdC hdG hraw
  have hresult := normal_trace_component_cancellation
    C Γ D (DA k) W dW covW hW k (hdW k) hcovW
  simpa [C, D, DA, covW] using hresult

/-- The calibrated local-frame coefficient formula determines the actual
vector identity before pairing against an arbitrary tangent vector. -/
private theorem covariantDerivative_standardDeTurckVectorField_eq_trace_of_orthonormal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (u : TM x)
    (horth : ∀ p q : ι,
      (g t).inner x (e.localFrame b p x) (e.localFrame b q x) =
        if p = q then 1 else 0)
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) y
        (explicitLeviCivitaCorrection (I := I) (M := M) g background t y)) x) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
    (background t) (standardDeTurckVectorField (I := I) (M := M)
      g background t) x u =
      ((∑ i : ι,
        CovariantDerivative.covariantDerivativeOneForm (background t)
          (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x u
          (e.localFrame b i x) (e.localFrame b i x))) -
        (∑ i : ι, ∑ j : ι,
          (background t).metricDefect x (e.localFrame b i x)
            (e.localFrame b j x) u •
          explicitLeviCivitaCorrection (I := I) (M := M) g background t x
            (e.localFrame b j x) (e.localFrame b i x)) := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let L : TM x := (background t)
    (standardDeTurckVectorField (I := I) (M := M) g background t) x u
  let R : TM x :=
    ((∑ i : ι,
      CovariantDerivative.covariantDerivativeOneForm (background t)
        (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x u
        (e.localFrame b i x) (e.localFrame b i x))) -
      (∑ i : ι, ∑ j : ι,
        (background t).metricDefect x (e.localFrame b i x)
          (e.localFrame b j x) u •
        explicitLeviCivitaCorrection (I := I) (M := M) g background t x
          (e.localFrame b j x) (e.localFrame b i x))
  have hcoeff (k : ι) : e.localFrameCoeff I b k x L =
      e.localFrameCoeff I b k x R := by
    dsimp [L, R]
    rw [localFrameCoeff_covariantDerivative_standardDeTurckVectorField_eq_trace_of_orthonormal
      (I := I) (M := M) g background t e b hx u k horth hA]
    simp only [standardDeTurckCorrectionLocalComponent,
      map_sum, map_sub, map_smul, smul_eq_mul]
  change L = R
  calc
    L = ∑ k, e.localFrameCoeff I b k x L • e.localFrame b k x :=
      localFrame_eq_sum_localFrameCoeff_smul (I := I) (M := M) e b hx L
    _ = ∑ k, e.localFrameCoeff I b k x R • e.localFrame b k x := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hcoeff k]
    _ = R := (localFrame_eq_sum_localFrameCoeff_smul (I := I) (M := M) e b hx R).symm

/-- **Intrinsic standard DeTurck trace derivative.**

Differentiating the standard DeTurck vector field through an arbitrary
background connection gives the covariant derivative of the explicit
Levi-Civita correction trace, together with the full metric-defect
contraction.  The regularity premise is precisely differentiability of the
complete correction tensor at the evaluation point. -/
theorem standardDeTurckVectorField_covariantDerivative_inner_eq_sum_covariantDerivative_sub_metricDefect
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) (t : ℝ) (x : M)
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) y
        (explicitLeviCivitaCorrection (I := I) (M := M) g background t y)) x) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (b : OrthonormalBasis ι ℝ (TM x)) (u v : TM x),
      (g t).inner x ((background t)
        (standardDeTurckVectorField (I := I) (M := M) g background t) x u) v =
        ((∑ i : ι, (g t).inner x
          (CovariantDerivative.covariantDerivativeOneForm (background t)
            (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x u
            (b i) (b i)) v)) -
          (∑ i : ι, ∑ r : ι,
            (background t).metricDefect x (b i) (b r) u *
              (g t).inner x
                (explicitLeviCivitaCorrection (I := I) (M := M) g background t x
                  (b r) (b i)) v) := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  intro ι _ _ b u v
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x
  have hx : x ∈ e.baseSet := by
    simpa [e] using (FiberBundle.mem_baseSet_trivializationAt E TM x)
  let β : Module.Basis ι ℝ E :=
    tangentModelBasisAt (I := I) x e b.toBasis hx
  have hframe (i : ι) : e.localFrame β i x = b i := by
    simpa [β] using
      (localFrame_tangentModelBasisAt_apply_center (I := I) x e b.toBasis hx i)
  have horth (p q : ι) :
      (g t).inner x (e.localFrame β p x) (e.localFrame β q x) =
        if p = q then 1 else 0 := by
    rw [hframe p, hframe q]
    change inner ℝ (b p) (b q) = _
    by_cases hpq : p = q
    · subst q
      rw [real_inner_self_eq_norm_sq, b.orthonormal.1 p]
      simp
    · rw [b.orthonormal.2 hpq]
      simp [hpq]
  have hvector :=
    covariantDerivative_standardDeTurckVectorField_eq_trace_of_orthonormal
      (I := I) (M := M) g background t e β hx u horth hA
  have hpair := congrArg (fun z : TM x => (g t).inner x z v) hvector
  simp_rw [hframe] at hpair
  change inner ℝ
      ((background t) (standardDeTurckVectorField (I := I) (M := M)
        g background t) x u) v =
    inner ℝ
      ((∑ i : ι,
        CovariantDerivative.covariantDerivativeOneForm (background t)
          (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x u
          (b i) (b i)) -
        ∑ i : ι, ∑ r : ι,
          (background t).metricDefect x (b i) (b r) u •
          explicitLeviCivitaCorrection (I := I) (M := M) g background t x
            (b r) (b i)) v at hpair
  rw [inner_sub_left] at hpair
  simp_rw [sum_inner, real_inner_smul_left] at hpair
  change inner ℝ
      ((background t) (standardDeTurckVectorField (I := I) (M := M)
        g background t) x u) v =
    (∑ i : ι, inner ℝ
      (CovariantDerivative.covariantDerivativeOneForm (background t)
        (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x u
        (b i) (b i)) v) -
      ∑ i : ι, ∑ r : ι,
        (background t).metricDefect x (b i) (b r) u * inner ℝ
          (explicitLeviCivitaCorrection (I := I) (M := M) g background t x
            (b r) (b i)) v
  exact hpair
end RicciFlow
