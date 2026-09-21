/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianLocalFrame
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.DowngradeNormFree
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Coordinate form of the connection Laplacian

This module develops finite local-frame coordinates for covariant two-tensors
and their induced connection.  It is the geometric-to-coordinate bridge used
by the parabolic construction.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

/-- The standard finite basis of continuous linear maps induced by bases of
the source and target. -/
noncomputable def continuousLinearMapBasis
    {F₁ F₂ ι₁ ι₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (b₁ : Module.Basis ι₁ ℝ F₁) (b₂ : Module.Basis ι₂ ℝ F₂) :
    Module.Basis (ι₂ × ι₁) ℝ (F₁ →L[ℝ] F₂) :=
  (b₁.linearMap b₂).map
    (LinearMap.toContinuousLinearMap :
      (F₁ →ₗ[ℝ] F₂) ≃ₗ[ℝ] (F₁ →L[ℝ] F₂))

@[simp]
theorem continuousLinearMapBasis_apply_apply
    {F₁ F₂ ι₁ ι₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (b₁ : Module.Basis ι₁ ℝ F₁) (b₂ : Module.Basis ι₂ ℝ F₂)
    (ij : ι₂ × ι₁) (k : ι₁) :
    continuousLinearMapBasis b₁ b₂ ij (b₁ k) =
      if ij.2 = k then b₂ ij.1 else 0 := by
  change LinearMap.toContinuousLinearMap (b₁.linearMap b₂ ij) (b₁ k) = _
  rw [LinearMap.coe_toContinuousLinearMap']
  exact Module.Basis.linearMap_apply_apply b₁ b₂ ij k

@[simp]
theorem continuousLinearMapBasis_repr
    {F₁ F₂ ι₁ ι₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (b₁ : Module.Basis ι₁ ℝ F₁) (b₂ : Module.Basis ι₂ ℝ F₂)
    (L : F₁ →L[ℝ] F₂) (ij : ι₂ × ι₁) :
    (continuousLinearMapBasis b₁ b₂).repr L ij =
      b₂.repr (L (b₁ ij.2)) ij.1 := by
  change (b₁.linearMap b₂).repr (L : F₁ →ₗ[ℝ] F₂) ij = _
  rw [Module.Basis.linearMap_repr_apply]
  change LinearMap.toMatrix b₁ b₂ (L : F₁ →ₗ[ℝ] F₂) ij.1 ij.2 = _
  exact LinearMap.toMatrix_apply b₁ b₂ (L : F₁ →ₗ[ℝ] F₂) ij.1 ij.2

/-- Coordinate functionals of a trivialization's local frame have the
Kronecker values. -/
@[simp]
theorem localFrameCoeff_localFrame
    {E₀ F H₀ M₀ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
    [TopologicalSpace M₀] [ChartedSpace H₀ M₀]
    [FiniteDimensional ℝ E₀] [CompleteSpace E₀]
    [FiniteDimensional ℝ F] [CompleteSpace F] [IsManifold I₀ 1 M₀]
    {V : M₀ → Type*} [∀ x, NormedAddCommGroup (V x)]
    [∀ x, NormedSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I₀]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M₀))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ F)
    {x : M₀} (hx : x ∈ e.baseSet) (i j : ι) :
    (e.localFrameCoeff I₀ b i x) (e.localFrame b j x) =
      if i = j then 1 else 0 := by
  rw [Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
    (e := e) (b := b) hx]
  rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
    (e := e) (b := b) hx]
  simp [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]

/-- Coefficientwise form of a covariant derivative in any genuine local
frame.  The derivative of the selected coefficient is the principal term;
the connection of the frame itself supplies the finite zeroth-order sum. -/
theorem localFrameCoeff_covariantDerivative
    {E₀ F H₀ M₀ : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
    [TopologicalSpace M₀] [ChartedSpace H₀ M₀]
    [FiniteDimensional ℝ E₀] [CompleteSpace E₀]
    [FiniteDimensional ℝ F] [CompleteSpace F] [IsManifold I₀ 1 M₀]
    {V : M₀ → Type*} [∀ x, NormedAddCommGroup (V x)]
    [∀ x, NormedSpace ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I₀]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M₀))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ F)
    (cov : CovariantDerivative I₀ F V)
    {σ : ∀ x : M₀, V x} {x : M₀} (hx : x ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) x) (v : TangentSpace I₀ x) (out : ι) :
    (e.localFrameCoeff I₀ b out x) (cov σ x v) =
      mvfderiv (I := I₀)
          ((LinearMap.piApply (e.localFrameCoeff I₀ b out)) σ) x v +
        ∑ input : ι,
          ((LinearMap.piApply (e.localFrameCoeff I₀ b input)) σ) x *
            (e.localFrameCoeff I₀ b out x)
              (cov (e.localFrame b input) x v) := by
  have hdec := e.covariantDerivative_apply_eq_sum_localFrame_add_sum_covariantDerivative_localFrame
    (I := I₀) b cov hx hσ v
  have hread := congrArg (fun w : V x => e.localFrameCoeff I₀ b out x w) hdec
  rw [hread]
  simp only [map_add, map_sum, map_smul, LinearMap.piApply_apply, smul_eq_mul]
  congr 1
  classical
  simp_rw [localFrameCoeff_localFrame (I₀ := I₀) e b hx]
  simp

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

-- Naming the nested operator-space instances keeps synthesis from unfolding
-- indefinitely while constructing the induced depth-three bundle.
local instance coordinateTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance coordinateTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance coordinateTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance coordinateTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance
local instance coordinateThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance coordinateThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance coordinateThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) := inferInstance
local instance coordinateThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) := inferInstance

/-- The vector-valued manifold derivative depends only on the germ of a
function at the base point. -/
theorem mvfderiv_eq_of_eventuallyEq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : M → F} {x : M} (hfg : f =ᶠ[nhds x] g) :
    mvfderiv (I := I) f x = mvfderiv (I := I) g x := by
  unfold mvfderiv
  rw [hfg.eq_of_nhds, hfg.mfderiv_eq]
  rfl

/-- The trivial real-line chart used to induce dual and tensor charts. -/
noncomputable def localRealLineTrivialization :
    Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ T₀ → M) :=
  Bundle.Trivial.trivialization M ℝ

instance localRealLineTrivialization_mem :
    MemTrivializationAtlas (localRealLineTrivialization (M := M)) := by
  constructor
  change Bundle.Trivial.trivialization M ℝ ∈
    ({Bundle.Trivial.trivialization M ℝ} : Set _)
  simp

/-- The cotangent trivialization induced by a tangent trivialization. -/
noncomputable def localCovectorTrivialization
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] :
    Trivialization (E →L[ℝ] ℝ) (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ) T₁ → M) :=
  e.continuousLinearMap (σ := RingHom.id ℝ)
    (localRealLineTrivialization (M := M))

instance localCovectorTrivialization_mem
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] :
    MemTrivializationAtlas (localCovectorTrivialization (I := I) e) := by
  unfold localCovectorTrivialization
  infer_instance

/-- The covariant-two-tensor trivialization induced twice from a tangent
trivialization. -/
noncomputable def localTwoTensorTrivialization
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] :
    Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) T₂ → M) :=
  e.continuousLinearMap (σ := RingHom.id ℝ)
    (localCovectorTrivialization (I := I) e)

instance localTwoTensorTrivialization_mem
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] :
    MemTrivializationAtlas (localTwoTensorTrivialization (I := I) e) := by
  unfold localTwoTensorTrivialization
  infer_instance

/-- The covariant-three-tensor trivialization induced from the tangent and
covariant-two-tensor trivializations. -/
noncomputable def localThreeTensorTrivialization
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] :
    Trivialization (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ → M) :=
  e.continuousLinearMap (σ := RingHom.id ℝ)
    (localTwoTensorTrivialization (I := I) e)

instance localThreeTensorTrivialization_mem
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] :
    MemTrivializationAtlas (localThreeTensorTrivialization (I := I) e) := by
  unfold localThreeTensorTrivialization
  infer_instance

/-- The matrix-unit basis of the model covariant-two-tensor fibre. -/
noncomputable def continuousTwoTensorBasis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) :
    Module.Basis (ι × ι) ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  continuousLinearMapBasis b (continuousDualBasis b)

/-- The standard basis of model covariant-three-tensors, ordered as an
output covariant-two-tensor index followed by the first input index. -/
noncomputable def continuousThreeTensorBasis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) :
    Module.Basis ((ι × ι) × ι) ℝ
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  continuousLinearMapBasis b (continuousTwoTensorBasis b)

@[simp]
theorem continuousTwoTensorBasis_apply_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (ij : ι × ι) (p q : ι) :
    continuousTwoTensorBasis b ij (b p) (b q) =
      if ij.2 = p then (if ij.1 = q then 1 else 0) else 0 := by
  rw [continuousTwoTensorBasis, continuousLinearMapBasis_apply_apply]
  by_cases hp : ij.2 = p
  · simp only [if_pos hp, if_pos hp.symm]
    have hrepr := continuousDualBasis_repr b (continuousDualBasis b ij.1) q
    simpa [Module.Basis.repr_self, Finsupp.single_apply, eq_comm] using hrepr.symm
  · have hp' : p ≠ ij.2 := fun h => hp h.symm
    simp only [if_neg hp, if_neg hp', zero_apply]

@[simp]
theorem continuousTwoTensorBasis_repr
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (h : E →L[ℝ] E →L[ℝ] ℝ)
    (p q : ι) :
    (continuousTwoTensorBasis b).repr h (q, p) = h (b p) (b q) := by
  simp [continuousTwoTensorBasis, continuousLinearMapBasis_repr,
    continuousDualBasis_repr]

/-- The induced tensor trivialization transports the standard matrix-unit
basis to the tensor products of the tangent local frame and its dual.  In
particular, evaluation on the tangent frame reads out the expected Kronecker
coefficients. -/
theorem localTwoTensorFrame_apply_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    (ij : ι × ι) (p q : ι) :
    (localTwoTensorTrivialization (I := I) e).localFrame
        (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
        (continuousTwoTensorBasis b) ij x
        (e.localFrame b p x) (e.localFrame b q x) =
      if ij.2 = p then (if ij.1 = q then 1 else 0) else 0 := by
  have hx₀ : x ∈ (localRealLineTrivialization (M := M)).baseSet := by
    change x ∈ Set.univ
    exact Set.mem_univ x
  have hx₁ : x ∈ (localCovectorTrivialization (I := I) e).baseSet := by
    exact ⟨hx, hx₀⟩
  have hx₂ : x ∈ (localTwoTensorTrivialization (I := I) e).baseSet := by
    exact ⟨hx, hx₁⟩
  rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
    (e := localTwoTensorTrivialization (I := I) e)
    (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
    (b := continuousTwoTensorBasis b) hx₂]
  rw [e.localFrame_apply_of_mem_baseSet b hx,
    e.localFrame_apply_of_mem_baseSet b hx]
  change
    (((localTwoTensorTrivialization (I := I) e).symm x
        (continuousTwoTensorBasis b ij))
      (e.symm x (b p))) (e.symm x (b q)) = _
  let qx : T₂ x :=
    (localTwoTensorTrivialization (I := I) e).symm x
      (continuousTwoTensorBasis b ij)
  have hcoord :
      ((localTwoTensorTrivialization (I := I) e)
        ⟨x, qx⟩).2 = continuousTwoTensorBasis b ij := by
    simpa [qx] using congrArg Prod.snd
      ((localTwoTensorTrivialization (I := I) e).apply_mk_symm
        hx₂ (continuousTwoTensorBasis b ij))
  have hpcoord := congrArg
    (fun A : E →L[ℝ] E →L[ℝ] ℝ => A (b p)) hcoord
  have hpqcoord := congrArg (fun A : E →L[ℝ] ℝ => A (b q)) hpcoord
  have hcovcoord :
      ((localCovectorTrivialization (I := I) e).linearMapAt ℝ x
          (qx (e.symm x (b p)))) (b q) =
        qx (e.symm x (b p)) (e.symm x (b q)) := by
    rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hx₁]
    simp [localCovectorTrivialization, localRealLineTrivialization,
      Bundle.Trivialization.continuousLinearMap_apply,
      Bundle.Trivial.symmL_trivialization, hx]
  have hforward :
      qx (e.symm x (b p)) (e.symm x (b q)) =
        continuousTwoTensorBasis b ij (b p) (b q) := by
    rw [← hcovcoord]
    simpa [localTwoTensorTrivialization,
      Bundle.Trivialization.continuousLinearMap_apply,
      hx] using hpqcoord
  exact hforward.trans (continuousTwoTensorBasis_apply_apply b ij p q)

/-- In the induced tensor frame, the coefficient indexed by `(q,p)` is the
actual value of the tensor on the `p`-th and `q`-th tangent-frame vectors. -/
theorem localTwoTensorFrameCoeff_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x)
    {x : M} (hx : x ∈ e.baseSet) (p q : ι) :
    (Bundle.Trivialization.localFrameCoeff
        (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
        I (localTwoTensorTrivialization (I := I) e)
        (continuousTwoTensorBasis b) (q, p) x) (h x) =
      h x (e.localFrame b p x) (e.localFrame b q x) := by
  have hx₀ : x ∈ (localRealLineTrivialization (M := M)).baseSet := by
    change x ∈ Set.univ
    exact Set.mem_univ x
  have hx₁ : x ∈ (localCovectorTrivialization (I := I) e).baseSet := ⟨hx, hx₀⟩
  have hx₂ : x ∈ (localTwoTensorTrivialization (I := I) e).baseSet := ⟨hx, hx₁⟩
  rw [Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
    (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
    (e := localTwoTensorTrivialization (I := I) e)
    (b := continuousTwoTensorBasis b) hx₂]
  simp [Bundle.Trivialization.basisAt, continuousTwoTensorBasis_repr,
    localTwoTensorTrivialization, localCovectorTrivialization,
    localRealLineTrivialization,
    Bundle.Trivialization.continuousLinearMap_apply, hx]

/-- A covariant-three-tensor coefficient is its evaluation on the
corresponding three tangent-frame vectors. -/
theorem localThreeTensorFrameCoeff_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (S : ∀ x : M, T₃ x)
    {x : M} (hx : x ∈ e.baseSet) (i p q : ι) :
    (Bundle.Trivialization.localFrameCoeff
        (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (V := T₃)
        I (localThreeTensorTrivialization (I := I) e)
        (continuousThreeTensorBasis b) ((q, p), i) x) (S x) =
      S x (e.localFrame b i x) (e.localFrame b p x)
        (e.localFrame b q x) := by
  have hx₀ : x ∈ (localRealLineTrivialization (M := M)).baseSet := by
    change x ∈ Set.univ
    exact Set.mem_univ x
  have hx₁ : x ∈ (localCovectorTrivialization (I := I) e).baseSet := ⟨hx, hx₀⟩
  have hx₂ : x ∈ (localTwoTensorTrivialization (I := I) e).baseSet := ⟨hx, hx₁⟩
  have hx₃ : x ∈ (localThreeTensorTrivialization (I := I) e).baseSet := ⟨hx, hx₂⟩
  rw [Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
    (e := localThreeTensorTrivialization (I := I) e)
    (b := continuousThreeTensorBasis b) hx₃]
  simp [Bundle.Trivialization.basisAt, continuousThreeTensorBasis,
    continuousLinearMapBasis_repr, continuousTwoTensorBasis_repr,
    localThreeTensorTrivialization, localTwoTensorTrivialization,
    localCovectorTrivialization, localRealLineTrivialization,
    Bundle.Trivialization.continuousLinearMap_apply, hx]

/-- The global (junk-extended outside the chart) scalar coefficient of a
covariant two-tensor section in the induced matrix-unit frame. -/
def localTwoTensorComponent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x)
    (ij : ι × ι) : M → ℝ :=
  fun x =>
    (Bundle.Trivialization.localFrameCoeff
      (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
      I (localTwoTensorTrivialization (I := I) e)
      (continuousTwoTensorBasis b) ij x) (h x)

@[simp]
theorem localTwoTensorComponent_apply_of_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x)
    {x : M} (hx : x ∈ e.baseSet) (p q : ι) :
    localTwoTensorComponent (I := I) e b h (q, p) x =
      h x (e.localFrame b p x) (e.localFrame b q x) := by
  exact localTwoTensorFrameCoeff_apply (I := I) e b h hx p q

/-- Coordinate formula for the induced connection on covariant two-tensors.
The leading term is the genuine manifold derivative of the tensor
coordinates; every remaining term is multiplication by the induced
connection evaluated on a matrix-unit frame section. -/
theorem localTwoTensorFrameCoeff_covariantDerivative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x} {x : M}
    (hx : x ∈ e.baseSet)
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (h y)) x)
    (v : TM x) (out : ι × ι) :
    (Bundle.Trivialization.localFrameCoeff
        (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
        I (localTwoTensorTrivialization (I := I) e)
        (continuousTwoTensorBasis b) out x)
        (covariantTwoTensorCovariantDerivative cov h x v) =
      mvfderiv (I := I) (localTwoTensorComponent (I := I) e b h out) x v +
        ∑ input : ι × ι,
          localTwoTensorComponent (I := I) e b h input x *
            (Bundle.Trivialization.localFrameCoeff
              (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
              I (localTwoTensorTrivialization (I := I) e)
              (continuousTwoTensorBasis b) out x)
              (covariantTwoTensorCovariantDerivative cov
                ((localTwoTensorTrivialization (I := I) e).localFrame
                  (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
                  (continuousTwoTensorBasis b) input) x v) := by
  have hx₀ : x ∈ (localRealLineTrivialization (M := M)).baseSet := by
    change x ∈ Set.univ
    exact Set.mem_univ x
  have hx₁ : x ∈ (localCovectorTrivialization (I := I) e).baseSet := ⟨hx, hx₀⟩
  have hx₂ : x ∈ (localTwoTensorTrivialization (I := I) e).baseSet := ⟨hx, hx₁⟩
  let e₂ := localTwoTensorTrivialization (I := I) e
  let b₂ := continuousTwoTensorBasis b
  let ℓ := Bundle.Trivialization.localFrameCoeff
    (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
    I e₂ b₂ out x
  have hdec := e₂.covariantDerivative_apply_eq_sum_localFrame_add_sum_covariantDerivative_localFrame
    (I := I) b₂ (covariantTwoTensorCovariantDerivative cov) hx₂ hh v
  have hread := congrArg (fun w : T₂ x => ℓ w) hdec
  rw [hread]
  simp only [map_add, map_sum, map_smul]
  simp only [e₂, b₂, ℓ, LinearMap.piApply_apply,
    localTwoTensorComponent, smul_eq_mul]
  congr 1
  classical
  rw [Finset.sum_eq_single out]
  · have hc :
        (Bundle.Trivialization.localFrameCoeff I
          (localTwoTensorTrivialization (I := I) e)
          (continuousTwoTensorBasis b) out x)
          ((localTwoTensorTrivialization (I := I) e).localFrame
            (continuousTwoTensorBasis b) out x) = 1 := by
      rw [Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
        (e := localTwoTensorTrivialization (I := I) e)
        (b := continuousTwoTensorBasis b) hx₂]
      rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
        (e := localTwoTensorTrivialization (I := I) e)
        (b := continuousTwoTensorBasis b) hx₂]
      simp
    rw [hc, mul_one]
    rfl
  · intro input hinput hne
    have hc :
        (Bundle.Trivialization.localFrameCoeff I
          (localTwoTensorTrivialization (I := I) e)
          (continuousTwoTensorBasis b) out x)
          ((localTwoTensorTrivialization (I := I) e).localFrame
            (continuousTwoTensorBasis b) input x) = 0 := by
      rw [Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
        (e := localTwoTensorTrivialization (I := I) e)
        (b := continuousTwoTensorBasis b) hx₂]
      rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
        (e := localTwoTensorTrivialization (I := I) e)
        (b := continuousTwoTensorBasis b) hx₂]
      simpa [Module.Basis.repr_self, Finsupp.single_apply] using hne
    rw [hc, mul_zero]
  · intro hout
    simp at hout

/-- The global coefficient of a covariant-three-tensor section in the
induced local frame. -/
def localThreeTensorComponent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (S : ∀ x : M, T₃ x)
    (idx : (ι × ι) × ι) : M → ℝ :=
  fun x =>
    (Bundle.Trivialization.localFrameCoeff
      (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (V := T₃)
      I (localThreeTensorTrivialization (I := I) e)
      (continuousThreeTensorBasis b) idx x) (S x)

@[simp]
theorem localThreeTensorComponent_apply_of_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (S : ∀ x : M, T₃ x)
    {x : M} (hx : x ∈ e.baseSet) (i p q : ι) :
    localThreeTensorComponent (I := I) e b S ((q, p), i) x =
      S x (e.localFrame b i x) (e.localFrame b p x)
        (e.localFrame b q x) := by
  exact localThreeTensorFrameCoeff_apply (I := I) e b S hx i p q

/-- The coefficient of the first covariant derivative is the directional
manifold derivative of the corresponding tensor coefficient plus the genuine
connection coefficient sum. -/
theorem localThreeTensorComponent_covariantTwoTensorDerivative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x} {x : M}
    (hx : x ∈ e.baseSet)
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (h y)) x)
    (i p q : ι) :
    localThreeTensorComponent (I := I) e b
        (covariantTwoTensorCovariantDerivative cov h) ((q, p), i) x =
      mvfderiv (I := I) (localTwoTensorComponent (I := I) e b h (q, p)) x
          (e.localFrame b i x) +
        ∑ input : ι × ι,
          localTwoTensorComponent (I := I) e b h input x *
            (Bundle.Trivialization.localFrameCoeff
              (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
              I (localTwoTensorTrivialization (I := I) e)
              (continuousTwoTensorBasis b) (q, p) x)
              (covariantTwoTensorCovariantDerivative cov
                ((localTwoTensorTrivialization (I := I) e).localFrame
                  (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
                  (continuousTwoTensorBasis b) input) x
                (e.localFrame b i x)) := by
  rw [localThreeTensorComponent_apply_of_mem (I := I) e b
    (covariantTwoTensorCovariantDerivative cov h) hx i p q]
  let R : ∀ y : M, T₂ y := fun y =>
    covariantTwoTensorCovariantDerivative cov h y (e.localFrame b i y)
  rw [← localTwoTensorFrameCoeff_apply (I := I) e b R hx p q]
  exact localTwoTensorFrameCoeff_covariantDerivative
    (I := I) cov e b hx hh (e.localFrame b i x) (q, p)

/-- Connection coefficient of the induced covariant-two-tensor frame. -/
def localTwoTensorConnectionCoefficient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (out input : ι × ι) (i : ι) (x : M) : ℝ :=
  (Bundle.Trivialization.localFrameCoeff
      (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
      I (localTwoTensorTrivialization (I := I) e)
      (continuousTwoTensorBasis b) out x)
    (covariantTwoTensorCovariantDerivative cov
      ((localTwoTensorTrivialization (I := I) e).localFrame
        (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
        (continuousTwoTensorBasis b) input) x
      (e.localFrame b i x))

/-- Exact coefficient expression for the first covariant derivative in the
induced local tensor frame. -/
def localFirstCovariantComponent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x)
    (out : ι × ι) (i : ι) : M → ℝ :=
  fun x =>
    mvfderiv (I := I) (localTwoTensorComponent (I := I) e b h out) x
        (e.localFrame b i x) +
      ∑ input : ι × ι,
        localTwoTensorComponent (I := I) e b h input x *
          localTwoTensorConnectionCoefficient (I := I) cov e b out input i x

/-- On the chart base, the named first-order coordinate expression is
literally the corresponding coefficient of the induced covariant
derivative. -/
theorem localThreeTensorComponent_covariantTwoTensorDerivative_eq_first
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x} {x : M}
    (hx : x ∈ e.baseSet)
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (h y)) x)
    (out : ι × ι) (i : ι) :
    localThreeTensorComponent (I := I) e b
        (covariantTwoTensorCovariantDerivative cov h) (out, i) x =
      localFirstCovariantComponent (I := I) cov e b h out i x := by
  rcases out with ⟨q, p⟩
  exact localThreeTensorComponent_covariantTwoTensorDerivative
    (I := I) cov e b hx hh i p q

/-- Coordinate formula for the induced connection on covariant
three-tensors. -/
theorem localThreeTensorFrameCoeff_covariantDerivative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {S : ∀ x : M, T₃ x} {x : M}
    (hx : x ∈ e.baseSet)
    (hS : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y (S y)) x)
    (v : TM x) (out : (ι × ι) × ι) :
    (Bundle.Trivialization.localFrameCoeff
        (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (V := T₃)
        I (localThreeTensorTrivialization (I := I) e)
        (continuousThreeTensorBasis b) out x)
        (covariantThreeTensorCovariantDerivative cov S x v) =
      mvfderiv (I := I) (localThreeTensorComponent (I := I) e b S out) x v +
        ∑ input : (ι × ι) × ι,
          localThreeTensorComponent (I := I) e b S input x *
            (Bundle.Trivialization.localFrameCoeff
              (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (V := T₃)
              I (localThreeTensorTrivialization (I := I) e)
              (continuousThreeTensorBasis b) out x)
              (covariantThreeTensorCovariantDerivative cov
                ((localThreeTensorTrivialization (I := I) e).localFrame
                  (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (V := T₃)
                  (continuousThreeTensorBasis b) input) x v) := by
  have hx₀ : x ∈ (localRealLineTrivialization (M := M)).baseSet := by
    change x ∈ Set.univ
    exact Set.mem_univ x
  have hx₁ : x ∈ (localCovectorTrivialization (I := I) e).baseSet := ⟨hx, hx₀⟩
  have hx₂ : x ∈ (localTwoTensorTrivialization (I := I) e).baseSet := ⟨hx, hx₁⟩
  have hx₃ : x ∈ (localThreeTensorTrivialization (I := I) e).baseSet := ⟨hx, hx₂⟩
  unfold localThreeTensorComponent
  simpa only [localThreeTensorComponent, LinearMap.piApply_apply] using
    (localFrameCoeff_covariantDerivative
      (I₀ := I) (e := localThreeTensorTrivialization (I := I) e)
      (b := continuousThreeTensorBasis b)
      (cov := covariantThreeTensorCovariantDerivative cov)
      hx₃ hS v out)

/-- Connection coefficient of the induced covariant-three-tensor frame. -/
def localThreeTensorConnectionCoefficient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (out input : (ι × ι) × ι)
    (i : ι) (x : M) : ℝ :=
  (Bundle.Trivialization.localFrameCoeff
      (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (V := T₃)
      I (localThreeTensorTrivialization (I := I) e)
      (continuousThreeTensorBasis b) out x)
    (covariantThreeTensorCovariantDerivative cov
      ((localThreeTensorTrivialization (I := I) e).localFrame
        (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (V := T₃)
        (continuousThreeTensorBasis b) input) x
      (e.localFrame b i x))

/-- Exact second covariant-derivative coefficient written solely in terms of
the local tensor components, their manifold derivatives, and the induced
frame-connection coefficients. -/
def localSecondCovariantComponent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x)
    (out : ι × ι) (j i : ι) : M → ℝ :=
  fun x =>
    mvfderiv (I := I)
        (localFirstCovariantComponent (I := I) cov e b h out j) x
        (e.localFrame b i x) +
      ∑ input : (ι × ι) × ι,
        localFirstCovariantComponent (I := I) cov e b h input.1 input.2 x *
          localThreeTensorConnectionCoefficient (I := I)
            cov e b (out, j) input i x

/-- The full local coefficient expression for the actual connection
Laplacian: inverse-metric contraction of the genuine second covariant
derivative expression. -/
def localConnectionLaplacianComponent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x)
    (out : ι × ι) : M → ℝ :=
  fun x =>
    ∑ i : ι, ∑ j : ι,
      localFrameInverseGramMatrix (I := I) e b x i j *
        localSecondCovariantComponent (I := I) cov e b h out j i x

/-- Coordinate formula for the genuine covariant Hessian of a covariant
two-tensor.  The selected Hessian coefficient is the manifold derivative of
the corresponding coefficient of `∇h`, plus the finite connection term for
the induced covariant-three-tensor frame.  In particular, this statement does
not replace the connection Laplacian by a componentwise Euclidean Laplacian:
all lower-order frame-connection terms remain visible. -/
theorem covariantHessianTwoTensor_apply_localFrame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x} {x : M}
    (hx : x ∈ e.baseSet)
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x)
    (i j p q : ι) :
    covariantHessianTwoTensor cov h x
        (e.localFrame b i x) (e.localFrame b j x)
        (e.localFrame b p x) (e.localFrame b q x) =
      mvfderiv (I := I)
          (localThreeTensorComponent (I := I) e b
            (covariantTwoTensorCovariantDerivative cov h) ((q, p), j)) x
          (e.localFrame b i x) +
        ∑ input : (ι × ι) × ι,
          localThreeTensorComponent (I := I) e b
              (covariantTwoTensorCovariantDerivative cov h) input x *
            (Bundle.Trivialization.localFrameCoeff
              (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (V := T₃)
              I (localThreeTensorTrivialization (I := I) e)
              (continuousThreeTensorBasis b) ((q, p), j) x)
              (covariantThreeTensorCovariantDerivative cov
                ((localThreeTensorTrivialization (I := I) e).localFrame
                  (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (V := T₃)
                  (continuousThreeTensorBasis b) input) x
                (e.localFrame b i x)) := by
  change
    covariantThreeTensorCovariantDerivative cov
        (covariantTwoTensorCovariantDerivative cov h) x
        (e.localFrame b i x) (e.localFrame b j x)
        (e.localFrame b p x) (e.localFrame b q x) = _
  let S := covariantTwoTensorCovariantDerivative cov h
  let R : ∀ y : M, T₃ y := fun y =>
    covariantThreeTensorCovariantDerivative cov S y (e.localFrame b i y)
  have hread := localThreeTensorFrameCoeff_apply
    (I := I) e b R hx j p q
  calc
    covariantHessianTwoTensor cov h x
          (e.localFrame b i x) (e.localFrame b j x)
          (e.localFrame b p x) (e.localFrame b q x) =
        (Bundle.Trivialization.localFrameCoeff
          (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (V := T₃)
          I (localThreeTensorTrivialization (I := I) e)
          (continuousThreeTensorBasis b) ((q, p), j) x)
          (covariantThreeTensorCovariantDerivative cov S x
            (e.localFrame b i x)) := by
              rw [hread]
              rfl
    _ = _ := localThreeTensorFrameCoeff_covariantDerivative
      (I := I) cov e b hx hfirst (e.localFrame b i x) ((q, p), j)

/-- The intrinsic covariant Hessian coefficient agrees with the named local
second-order expression.  The regularity assumption is imposed on the whole
frame domain because the outer derivative uses locality near the point. -/
theorem covariantHessianTwoTensor_apply_localSecondCovariantComponent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x}
    (hreg : ∀ y ∈ e.baseSet,
      MDiffAt
        (fun z => TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) z (h z)) y)
    {x : M} (hx : x ∈ e.baseSet)
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x)
    (i j p q : ι) :
    covariantHessianTwoTensor cov h x
        (e.localFrame b i x) (e.localFrame b j x)
        (e.localFrame b p x) (e.localFrame b q x) =
      localSecondCovariantComponent (I := I) cov e b h (q, p) j i x := by
  rw [covariantHessianTwoTensor_apply_localFrame
    (I := I) cov e b hx hfirst i j p q]
  unfold localSecondCovariantComponent
  have hevent :
      localThreeTensorComponent (I := I) e b
          (covariantTwoTensorCovariantDerivative cov h) ((q, p), j) =ᶠ[nhds x]
        localFirstCovariantComponent (I := I) cov e b h (q, p) j := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact localThreeTensorComponent_covariantTwoTensorDerivative_eq_first
      (I := I) cov e b hy (hreg y hy) (q, p) j
  rw [mvfderiv_eq_of_eventuallyEq (I := I) hevent]
  congr 1
  apply Finset.sum_congr rfl
  intro input hinput
  rcases input with ⟨out, k⟩
  rw [localThreeTensorComponent_covariantTwoTensorDerivative_eq_first
    (I := I) cov e b hx (hreg x hx) out k]
  rfl

/-- **Full local-frame coefficient formula for the actual connection
Laplacian.**  The inverse Gram matrix gives the uniformly elliptic principal
contraction, while both induced-connection sums are retained in the
coefficient of the covariant Hessian. -/
theorem connectionLaplacian_apply_localFrame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x} {x : M}
    (hx : x ∈ e.baseSet)
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x)
    (p q : ι) :
    connectionLaplacian cov h x
        (e.localFrame b p x) (e.localFrame b q x) =
      ∑ i : ι, ∑ j : ι,
        localFrameInverseGramMatrix (I := I) e b x i j *
          (mvfderiv (I := I)
              (localThreeTensorComponent (I := I) e b
                (covariantTwoTensorCovariantDerivative cov h) ((q, p), j)) x
              (e.localFrame b i x) +
            ∑ input : (ι × ι) × ι,
              localThreeTensorComponent (I := I) e b
                  (covariantTwoTensorCovariantDerivative cov h) input x *
                (Bundle.Trivialization.localFrameCoeff
                  (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (V := T₃)
                  I (localThreeTensorTrivialization (I := I) e)
                  (continuousThreeTensorBasis b) ((q, p), j) x)
                  (covariantThreeTensorCovariantDerivative cov
                    ((localThreeTensorTrivialization (I := I) e).localFrame
                      (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (V := T₃)
                      (continuousThreeTensorBasis b) input) x
                      (e.localFrame b i x))) := by
  rw [connectionLaplacian_eq_sum_localFrame_inverseGram cov h e b hx]
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_apply, smul_apply, smul_eq_mul]
  rw [covariantHessianTwoTensor_apply_localFrame
    (I := I) cov e b hx hfirst i j p q]

/-- The actual connection Laplacian, evaluated in a local tensor frame, is
exactly the named finite second-order coordinate expression. -/
theorem connectionLaplacian_apply_eq_localConnectionLaplacianComponent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E TM)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x}
    (hreg : ∀ y ∈ e.baseSet,
      MDiffAt
        (fun z => TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) z (h z)) y)
    {x : M} (hx : x ∈ e.baseSet)
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x)
    (p q : ι) :
    connectionLaplacian cov h x
        (e.localFrame b p x) (e.localFrame b q x) =
      localConnectionLaplacianComponent (I := I) cov e b h (q, p) x := by
  rw [connectionLaplacian_eq_sum_localFrame_inverseGram cov h e b hx]
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  unfold localConnectionLaplacianComponent
  apply Finset.sum_congr rfl
  intro i hi
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_apply, smul_apply, smul_eq_mul]
  rw [covariantHessianTwoTensor_apply_localSecondCovariantComponent
    (I := I) cov e b hreg hx hfirst i j p q]

end CovariantDerivative
