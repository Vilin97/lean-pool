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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFiniteSum

/-!
# Local reconstruction of covariant two-tensors

This file gives the algebraic synthesis map used by the manifold tensor-heat
parametrix. A finite matrix of coefficients is first made into a continuous
bilinear form on the model space and then pulled back through the genuine
tangent-bundle trivialization. On the trivialization domain, evaluating the
reconstructed tensor on the actual local frame recovers the original matrix
entry exactly.

The reconstruction is totalized by zero outside the trivialization domain.
Later a partition-of-unity function whose topological support lies inside that
domain erases this arbitrary branch before differentiability is used.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace RicciFlow
namespace AnalyticPDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₀" => (Bundle.Trivial M ℝ)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" =>
  (fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] ℝ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Explicit names keep nested operator-space synthesis deterministic.
local instance reconstructionTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance reconstructionTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance reconstructionTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance reconstructionTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance
local instance reconstructionThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance reconstructionThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance reconstructionThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) := inferInstance
local instance reconstructionThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) := inferInstance

/-- The continuous coordinate functional of a finite basis. -/
def basisCoordinateCLM (b : Module.Basis ι ℝ E) (i : ι) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    b.equivFun.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem basisCoordinateCLM_apply_basis
    (b : Module.Basis ι ℝ E) (i j : ι) :
    basisCoordinateCLM b i (b j) = if j = i then 1 else 0 := by
  change (b.repr (b j)) i = if j = i then 1 else 0
  rw [b.repr_self, Finsupp.single_apply]

/-- A finite matrix, regarded as a continuous bilinear form in the chosen
basis. -/
def matrixBilinearCLM (b : Module.Basis ι ℝ E) (q : ι → ι → ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, (basisCoordinateCLM b i).smulRight
    (∑ j, q i j • basisCoordinateCLM b j)

/-- Matrix-to-bilinear-form synthesis is a linear map. -/
def matrixBilinearLinearMap (b : Module.Basis ι ℝ E) :
    (ι → ι → ℝ) →ₗ[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) where
  toFun := matrixBilinearCLM b
  map_add' q r := by
    classical
    ext v w
    simp [matrixBilinearCLM, add_mul]
    simp_rw [Finset.sum_add_distrib, mul_add]
    exact Finset.sum_add_distrib
  map_smul' c q := by
    classical
    ext v w
    simp [matrixBilinearCLM, mul_assoc]
    simp_rw [← Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- The continuous linear matrix-synthesis operator. Finite dimensionality of
the source and target supplies continuity. -/
def matrixBilinearSynthesis (b : Module.Basis ι ℝ E) :
    (ι → ι → ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap (matrixBilinearLinearMap b)

@[simp]
theorem matrixBilinearSynthesis_apply
    (b : Module.Basis ι ℝ E) (q : ι → ι → ℝ) :
    matrixBilinearSynthesis b q = matrixBilinearCLM b q := rfl

/-- Smooth matrix-valued coefficients remain smooth after bilinear-form
synthesis. -/
theorem ContMDiffOn.matrixBilinearCLM {n : ℕ∞ω}
    (b : Module.Basis ι ℝ E) {s : Set M} {q : M → ι → ι → ℝ}
    (hq : ContMDiffOn I 𝓘(ℝ, ι → ι → ℝ) n q s) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) n
      (fun x => matrixBilinearCLM b (q x)) s := by
  simpa only [matrixBilinearSynthesis_apply] using
    (contMDiffOn_const.clm_apply hq :
      ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) n
        (fun x => matrixBilinearSynthesis b (q x)) s)

@[simp]
theorem matrixBilinearCLM_apply_basis
    (b : Module.Basis ι ℝ E) (q : ι → ι → ℝ) (i j : ι) :
    matrixBilinearCLM b q (b i) (b j) = q i j := by
  classical
  simp [matrixBilinearCLM, basisCoordinateCLM, Finsupp.single_apply]

/-- Matrix transposition is exactly slot-flip for the synthesized bilinear
form. -/
theorem matrixBilinearCLM_transpose_apply
    (b : Module.Basis ι ℝ E) (q : ι → ι → ℝ) (v w : E) :
    matrixBilinearCLM b (fun i j => q j i) v w =
      matrixBilinearCLM b q w v := by
  classical
  simp only [matrixBilinearCLM, _root_.sum_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, _root_.smul_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The tangent-fibre coordinate isomorphism as a continuous linear map. -/
def tangentCoordCLM
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (x : M) (hx : x ∈ e.baseSet) : TM x →L[ℝ] E :=
  (e.linearEquivAt ℝ x hx).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem tangentCoordCLM_apply
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (x : M) (hx : x ∈ e.baseSet) (v : TM x) :
    tangentCoordCLM e x hx v = (e (TotalSpace.mk' E x v)).2 := by
  exact e.linearEquivAt_apply (R := ℝ) x hx v

@[simp]
theorem tangentCoordCLM_localFrame
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (i : ι) :
    tangentCoordCLM e x hx (e.localFrame b i x) = b i := by
  rw [tangentCoordCLM_apply e x hx,
    e.localFrame_apply_of_mem_baseSet b hx]
  exact congrArg Prod.snd (e.apply_mk_symm hx (b i))

/-- The trivialization of the cotangent bundle induced from a tangent-bundle
trivialization and the canonical trivialization of the scalar bundle. -/
def covectorTrivialization (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] :
    Trivialization (E →L[ℝ] ℝ) (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ) T₁ → M) :=
  e.continuousLinearMap (RingHom.id ℝ) (trivializationAt ℝ T₀ p)

/-- The genuine covariant-two-tensor-bundle trivialization induced twice from
a tangent-bundle trivialization. -/
def covariantTwoTensorTrivialization (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] :
    Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) T₂ → M) := by
  let e₁ := covectorTrivialization p e
  letI : MemTrivializationAtlas e₁ := by
    dsimp [e₁, covectorTrivialization]
    infer_instance
  exact e.continuousLinearMap (RingHom.id ℝ) e₁

instance covariantTwoTensorTrivialization_mem (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] :
    MemTrivializationAtlas (covariantTwoTensorTrivialization p e) := by
  unfold covariantTwoTensorTrivialization
  dsimp only
  infer_instance

@[simp]
theorem covariantTwoTensorTrivialization_baseSet (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] :
    (covariantTwoTensorTrivialization p e).baseSet = e.baseSet := by
  simp [covariantTwoTensorTrivialization, covectorTrivialization]

/-- Reconstruct a covariant two-tensor from its matrix in the local tangent
frame. Outside the trivialization domain it is totalized by zero. -/
def localTensorOfMatrix
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q : M → ι → ι → ℝ) : ∀ x : M, T₂ x := by
  classical
  exact fun x => if hx : x ∈ e.baseSet then
    (matrixBilinearCLM b (q x)).bilinearComp
      (tangentCoordCLM e x hx) (tangentCoordCLM e x hx)
  else 0

@[simp]
theorem localTensorOfMatrix_apply_of_mem
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q : M → ι → ι → ℝ) {x : M} (hx : x ∈ e.baseSet)
    (v w : TM x) :
    localTensorOfMatrix e b q x v w =
      matrixBilinearCLM b (q x) (tangentCoordCLM e x hx v)
        (tangentCoordCLM e x hx w) := by
  classical
  simp [localTensorOfMatrix, hx]

/-- Reading a reconstructed tensor through the induced tensor-bundle
trivialization returns exactly the coefficient bilinear form. -/
@[simp]
theorem covariantTwoTensorTrivialization_localTensorOfMatrix
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q : M → ι → ι → ℝ) {x : M} (hx : x ∈ e.baseSet) :
    ((covariantTwoTensorTrivialization p e)
      (TotalSpace.mk' _ x (localTensorOfMatrix e b q x))).2 =
        matrixBilinearCLM b (q x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  classical
  simp [covariantTwoTensorTrivialization, covectorTrivialization,
    Bundle.Trivialization.continuousLinearMap_apply,
    localTensorOfMatrix, hx, tangentCoordCLM]

/-- Local differentiability of the coefficient bilinear form is precisely
enough to certify local differentiability of the reconstructed genuine tensor
section. -/
theorem contMDiffOn_localTensorOfMatrix (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q : M → ι → ι → ℝ)
    (hq : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) 2
      (fun x => matrixBilinearCLM b (q x)) e.baseSet) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x
        (localTensorOfMatrix e b q x)) e.baseSet := by
  rw [← covariantTwoTensorTrivialization_baseSet p e]
  apply (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
    (IB := I) (n := 2) (s := localTensorOfMatrix e b q)
      (covariantTwoTensorTrivialization p e)).mpr
  rw [covariantTwoTensorTrivialization_baseSet]
  exact hq.congr fun x hx =>
    covariantTwoTensorTrivialization_localTensorOfMatrix p e b q hx

/-- Open-subset form of local reconstruction regularity. -/
theorem contMDiffOn_localTensorOfMatrix_of_isOpen (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q : M → ι → ι → ℝ) {u : Set M} (hu : IsOpen u)
    (hue : u ⊆ e.baseSet)
    (hq : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) 2
      (fun x => matrixBilinearCLM b (q x)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x
        (localTensorOfMatrix e b q x)) u := by
  apply (Bundle.Trivialization.contMDiffOn_section_iff
    (IB := I) (n := 2) (s := localTensorOfMatrix e b q)
      (covariantTwoTensorTrivialization p e) hu ?_).mpr
  · exact hq.congr fun x hx =>
      covariantTwoTensorTrivialization_localTensorOfMatrix p e b q (hue hx)
  · simpa only [covariantTwoTensorTrivialization_baseSet] using hue

/-- Evaluation on the genuine local tangent frame exactly recovers the input
coefficient matrix. -/
@[simp]
theorem localTensorOfMatrix_localFrame
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q : M → ι → ι → ℝ) {x : M} (hx : x ∈ e.baseSet) (i j : ι) :
    localTensorOfMatrix e b q x (e.localFrame b i x)
        (e.localFrame b j x) = q x i j := by
  rw [localTensorOfMatrix_apply_of_mem e b q hx]
  rw [tangentCoordCLM_localFrame e b hx i,
    tangentCoordCLM_localFrame e b hx j]
  exact matrixBilinearCLM_apply_basis b (q x) i j

/-- Transposing the coefficient matrix flips the two covariant tensor slots. -/
theorem localTensorOfMatrix_transpose_apply
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q : M → ι → ι → ℝ) (x : M) (v w : TM x) :
    localTensorOfMatrix e b (fun y i j => q y j i) x v w =
      localTensorOfMatrix e b q x w v := by
  classical
  by_cases hx : x ∈ e.baseSet
  · simp only [localTensorOfMatrix, dif_pos hx,
      ContinuousLinearMap.bilinearComp_apply]
    exact matrixBilinearCLM_transpose_apply b (q x) _ _
  · simp [localTensorOfMatrix, hx]

/-- Symmetric coefficient matrices reconstruct symmetric covariant tensors. -/
theorem localTensorOfMatrix_isSymmetric
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q : M → ι → ι → ℝ) (hq : ∀ x i j, q x i j = q x j i) :
    ∀ x (v w : TM x), localTensorOfMatrix e b q x v w =
      localTensorOfMatrix e b q x w v := by
  intro x v w
  classical
  by_cases hx : x ∈ e.baseSet
  · simp only [localTensorOfMatrix, dif_pos hx,
      ContinuousLinearMap.bilinearComp_apply]
    simp only [matrixBilinearCLM, _root_.sum_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, _root_.smul_apply]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hq x i j]
    ring
  · simp [localTensorOfMatrix, hx]

/-- Multiply the reconstructed local tensor by a global scalar cutoff. This is
the summand used in the finite partition-of-unity synthesis. -/
def cutoffLocalTensorOfMatrix
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (q : M → ι → ι → ℝ) : ∀ x : M, T₂ x :=
  fun x => ψ x • localTensorOfMatrix e b q x

/-- Transposing coefficients also flips the slots after multiplication by a
scalar cutoff. -/
theorem cutoffLocalTensorOfMatrix_transpose_apply
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (psi : M → ℝ) (q : M → ι → ι → ℝ)
    (x : M) (v w : TM x) :
    cutoffLocalTensorOfMatrix e b psi (fun y i j => q y j i) x v w =
      cutoffLocalTensorOfMatrix e b psi q x w v := by
  simp only [cutoffLocalTensorOfMatrix, _root_.smul_apply, smul_eq_mul]
  rw [localTensorOfMatrix_transpose_apply]

/-- On the genuine local frame, cutoff reconstruction is exactly scalar
multiplication of the input matrix. -/
@[simp]
theorem cutoffLocalTensorOfMatrix_localFrame
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (q : M → ι → ι → ℝ)
    {x : M} (hx : x ∈ e.baseSet) (i j : ι) :
    cutoffLocalTensorOfMatrix e b ψ q x (e.localFrame b i x)
        (e.localFrame b j x) = ψ x * q x i j := by
  simp only [cutoffLocalTensorOfMatrix, _root_.smul_apply,
    smul_eq_mul]
  rw [localTensorOfMatrix_localFrame e b q hx]

/-- Cutoff reconstruction preserves pointwise symmetry. -/
theorem cutoffLocalTensorOfMatrix_isSymmetric
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (q : M → ι → ι → ℝ)
    (hq : ∀ x i j, q x i j = q x j i) :
    ∀ x (v w : TM x), cutoffLocalTensorOfMatrix e b ψ q x v w =
      cutoffLocalTensorOfMatrix e b ψ q x w v := by
  intro x v w
  simp only [cutoffLocalTensorOfMatrix, _root_.smul_apply,
    smul_eq_mul]
  rw [localTensorOfMatrix_isSymmetric e b q hq x v w]

/-- A smooth cutoff supported inside the coordinate domain turns a locally
`C²` coefficient matrix into a globally `C²` genuine tensor section. -/
theorem contMDiff_cutoffLocalTensorOfMatrix (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (q : M → ι → ι → ℝ)
    (hψ : ContMDiff I 𝓘(ℝ) 2 ψ)
    (hψsupp : tsupport ψ ⊆ e.baseSet)
    (hq : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) 2
      (fun x => matrixBilinearCLM b (q x)) e.baseSet) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x
        (cutoffLocalTensorOfMatrix e b ψ q x)) := by
  have h := ContMDiffOn.smul_section_of_tsupport
    (I := I) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
    (u := e.baseSet) (n := (2 : ℕ∞ω)) (ψ := ψ)
    hψ.contMDiffOn e.open_baseSet hψsupp
    (contMDiffOn_localTensorOfMatrix p e b q hq)
  exact h

/-- Open-subset form of cutoff reconstruction: only regularity on an open
neighbourhood of the cutoff support is needed. -/
theorem contMDiff_cutoffLocalTensorOfMatrix_of_isOpen (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (q : M → ι → ι → ℝ) {u : Set M}
    (hu : IsOpen u) (hue : u ⊆ e.baseSet)
    (hψ : ContMDiff I 𝓘(ℝ) 2 ψ) (hψsupp : tsupport ψ ⊆ u)
    (hq : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) 2
      (fun x => matrixBilinearCLM b (q x)) u) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x
        (cutoffLocalTensorOfMatrix e b ψ q x)) := by
  have h := ContMDiffOn.smul_section_of_tsupport
    (I := I) (F := E →L[ℝ] E →L[ℝ] ℝ) (V := T₂)
    (u := u) (n := (2 : ℕ∞ω)) (ψ := ψ)
    hψ.contMDiffOn hu hψsupp
    (contMDiffOn_localTensorOfMatrix_of_isOpen p e b q hu hue hq)
  exact h

/-- Coefficient-level form of `contMDiff_cutoffLocalTensorOfMatrix`: globally
`C²` matrix coefficients may be fed directly into cutoff reconstruction. -/
theorem contMDiff_cutoffLocalTensorOfMatrix_of_coefficients (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (q : M → ι → ι → ℝ)
    (hψ : ContMDiff I 𝓘(ℝ) 2 ψ)
    (hψsupp : tsupport ψ ⊆ e.baseSet)
    (hq : ContMDiffOn I 𝓘(ℝ, ι → ι → ℝ) 2 q e.baseSet) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x
        (cutoffLocalTensorOfMatrix e b ψ q x)) :=
  contMDiff_cutoffLocalTensorOfMatrix p e b ψ q hψ hψsupp
    (ContMDiffOn.matrixBilinearCLM b hq)

/-- Coefficient-level open-subset form of cutoff reconstruction. -/
theorem contMDiff_cutoffLocalTensorOfMatrix_of_coefficients_of_isOpen
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (q : M → ι → ι → ℝ) {u : Set M}
    (hu : IsOpen u) (hue : u ⊆ e.baseSet)
    (hψ : ContMDiff I 𝓘(ℝ) 2 ψ) (hψsupp : tsupport ψ ⊆ u)
    (hq : ContMDiffOn I 𝓘(ℝ, ι → ι → ℝ) 2 q u) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x
        (cutoffLocalTensorOfMatrix e b ψ q x)) :=
  contMDiff_cutoffLocalTensorOfMatrix_of_isOpen p e b ψ q hu hue hψ hψsupp
    (ContMDiffOn.matrixBilinearCLM b hq)

/-- A globally `C²` covariant two-tensor belongs to the genuine second-order
connection-Laplacian domain whenever the induced tensor connection has the
expected `C¹` regularity. -/
theorem connectionLaplacianDomain_of_contMDiff_two
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {h : ∀ x : M, T₂ x}
    (hh : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x (h x))) :
    h ∈ CovariantDerivative.ConnectionLaplacianDomain cov := by
  constructor
  · intro x
    exact (hh.contMDiffAt.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).mdifferentiableAt
      one_ne_zero
  · have hhOn : ContMDiffOn I
        (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (1 + 1)
        (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x (h x))
        Set.univ := by
      have hone : (1 : ℕ∞ω) + 1 = 2 := by norm_num
      simpa only [hone] using hh.contMDiffOn
    have hcov :=
      ((inferInstance : CovariantDerivative.ContMDiffCovariantDerivative
        (CovariantDerivative.covariantTwoTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 1).contMDiff.contMDiff hhOn)
    intro x
    exact ((hcov x (Set.mem_univ x)).contMDiffAt
      (isOpen_univ.mem_nhds (Set.mem_univ x))).mdifferentiableAt one_ne_zero

/-- The cutoff-reconstructed local summand lies in the actual
connection-Laplacian domain. -/
theorem cutoffLocalTensorOfMatrix_mem_connectionLaplacianDomain
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (q : M → ι → ι → ℝ)
    (hψ : ContMDiff I 𝓘(ℝ) 2 ψ)
    (hψsupp : tsupport ψ ⊆ e.baseSet)
    (hq : ContMDiffOn I 𝓘(ℝ, ι → ι → ℝ) 2 q e.baseSet) :
    cutoffLocalTensorOfMatrix e b ψ q ∈
      CovariantDerivative.ConnectionLaplacianDomain cov :=
  connectionLaplacianDomain_of_contMDiff_two cov
    (contMDiff_cutoffLocalTensorOfMatrix_of_coefficients
      p e b ψ q hψ hψsupp hq)

/-- Open-subset form of domain membership for a cutoff-reconstructed local
summand. -/
theorem cutoffLocalTensorOfMatrix_mem_connectionLaplacianDomain_of_isOpen
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (q : M → ι → ι → ℝ)
    {u : Set M} (hu : IsOpen u) (hue : u ⊆ e.baseSet)
    (hψ : ContMDiff I 𝓘(ℝ) 2 ψ) (hψsupp : tsupport ψ ⊆ u)
    (hq : ContMDiffOn I 𝓘(ℝ, ι → ι → ℝ) 2 q u) :
    cutoffLocalTensorOfMatrix e b ψ q ∈
      CovariantDerivative.ConnectionLaplacianDomain cov :=
  connectionLaplacianDomain_of_contMDiff_two cov
    (contMDiff_cutoffLocalTensorOfMatrix_of_coefficients_of_isOpen
      p e b ψ q hu hue hψ hψsupp hq)

/-- Reconstruction is additive in the coefficient matrix. -/
theorem localTensorOfMatrix_add
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (q r : M → ι → ι → ℝ) :
    localTensorOfMatrix e b (q + r) =
      localTensorOfMatrix e b q + localTensorOfMatrix e b r := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  classical
  by_cases hx : x ∈ e.baseSet <;>
    simp [localTensorOfMatrix, matrixBilinearCLM, hx, add_mul]
  simp_rw [Finset.sum_add_distrib, mul_add]
  exact Finset.sum_add_distrib

/-- Reconstruction commutes with scalar multiplication of the coefficient
matrix. -/
theorem localTensorOfMatrix_smul
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (c : ℝ) (q : M → ι → ι → ℝ) :
    localTensorOfMatrix e b (c • q) = c • localTensorOfMatrix e b q := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  classical
  by_cases hx : x ∈ e.baseSet <;>
    simp [localTensorOfMatrix, matrixBilinearCLM, hx, mul_assoc]
  simp_rw [← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Cutoff reconstruction is additive in the coefficient matrix. -/
theorem cutoffLocalTensorOfMatrix_add
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (q r : M → ι → ι → ℝ) :
    cutoffLocalTensorOfMatrix e b ψ (q + r) =
      cutoffLocalTensorOfMatrix e b ψ q +
        cutoffLocalTensorOfMatrix e b ψ r := by
  funext x
  simp only [cutoffLocalTensorOfMatrix, Pi.add_apply,
    localTensorOfMatrix_add, smul_add]

/-- Cutoff reconstruction commutes with scalar multiplication of the
coefficient matrix. -/
theorem cutoffLocalTensorOfMatrix_smul
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (c : ℝ) (q : M → ι → ι → ℝ) :
    cutoffLocalTensorOfMatrix e b ψ (c • q) =
      c • cutoffLocalTensorOfMatrix e b ψ q := by
  funext x
  simp only [cutoffLocalTensorOfMatrix, Pi.smul_apply,
    localTensorOfMatrix_smul, smul_smul]
  rw [mul_comm]

/-- At a fixed manifold point, cutoff reconstruction is a continuous linear
map from coefficient matrices to the genuine tensor fibre.  This is the
temporal chain-rule bridge used by finite-cylinder reconstruction. -/
def cutoffLocalTensorSynthesisAt
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (x : M) :
    letI : AddCommMonoid (ι → ι → ℝ) :=
      Pi.normedAddCommGroup.toAddCommMonoid
    letI : AddCommGroup (ι → ι → ℝ) :=
      Pi.normedAddCommGroup.toAddCommGroup
    letI : Module ℝ (ι → ι → ℝ) :=
      Pi.normedSpace.toModule
    letI : TopologicalSpace (ι → ι → ℝ) :=
      Pi.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (ι → ι → ℝ) →L[ℝ] T₂ x := by
  letI : AddCommMonoid (ι → ι → ℝ) :=
    Pi.normedAddCommGroup.toAddCommMonoid
  letI : AddCommGroup (ι → ι → ℝ) :=
    Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (ι → ι → ℝ) :=
    Pi.normedSpace.toModule
  letI : TopologicalSpace (ι → ι → ℝ) :=
    Pi.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact LinearMap.toContinuousLinearMap
    { toFun := fun q => cutoffLocalTensorOfMatrix e b ψ (fun _ => q) x
      map_add' := by
        intro q r
        exact congrFun (cutoffLocalTensorOfMatrix_add
          e b ψ (fun _ => q) (fun _ => r)) x
      map_smul' := by
        intro c q
        exact congrFun (cutoffLocalTensorOfMatrix_smul
          e b ψ c (fun _ => q)) x }

@[simp] theorem cutoffLocalTensorSynthesisAt_apply
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (x : M) (q : ι → ι → ℝ) :
    cutoffLocalTensorSynthesisAt e b ψ x q =
      cutoffLocalTensorOfMatrix e b ψ (fun _ => q) x :=
  rfl

/-- Fixed-fibre evaluation of cutoff reconstruction is a continuous linear
functional of the finite coefficient matrix, using the norm topology carried
by the parabolic Banach space. -/
def cutoffLocalTensorEvaluationSynthesisAt
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (x : M) (v w : TM x) :
    letI : AddCommMonoid (ι → ι → ℝ) :=
      Pi.normedAddCommGroup.toAddCommMonoid
    letI : AddCommGroup (ι → ι → ℝ) :=
      Pi.normedAddCommGroup.toAddCommGroup
    letI : Module ℝ (ι → ι → ℝ) := Pi.normedSpace.toModule
    letI : TopologicalSpace (ι → ι → ℝ) :=
      Pi.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (ι → ι → ℝ) →L[ℝ] ℝ := by
  letI : AddCommMonoid (ι → ι → ℝ) :=
    Pi.normedAddCommGroup.toAddCommMonoid
  letI : AddCommGroup (ι → ι → ℝ) :=
    Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (ι → ι → ℝ) := Pi.normedSpace.toModule
  letI : TopologicalSpace (ι → ι → ℝ) :=
    Pi.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact LinearMap.toContinuousLinearMap
    { toFun := fun q => cutoffLocalTensorOfMatrix e b ψ (fun _ => q) x v w
      map_add' := by
        intro q r
        exact congrArg (fun h : T₂ x => h v w)
          (congrFun (cutoffLocalTensorOfMatrix_add
            e b ψ (fun _ => q) (fun _ => r)) x)
      map_smul' := by
        intro c q
        exact congrArg (fun h : T₂ x => h v w)
          (congrFun (cutoffLocalTensorOfMatrix_smul
            e b ψ c (fun _ => q)) x) }

@[simp] theorem cutoffLocalTensorEvaluationSynthesisAt_apply
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (ψ : M → ℝ) (x : M) (v w : TM x) (q : ι → ι → ℝ) :
    cutoffLocalTensorEvaluationSynthesisAt e b ψ x v w q =
      cutoffLocalTensorOfMatrix e b ψ (fun _ => q) x v w :=
  rfl

end AnalyticPDE
end RicciFlow
