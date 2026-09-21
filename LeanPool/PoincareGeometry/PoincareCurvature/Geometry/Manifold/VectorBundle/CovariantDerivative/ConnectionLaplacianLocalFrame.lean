/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacian
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Local-frame formula for the connection Laplacian

The intrinsic definition of `connectionLaplacian` contracts the covariant
Hessian with the canonical inverse-metric tensor.  This file proves that in
an arbitrary (not necessarily orthonormal) local tangent frame the same
contraction is the familiar double sum against the inverse Gram matrix.

Unlike a coordinate-model hypothesis, the coefficients in the final theorem
are the inverse of the actual Riemannian Gram matrix of the local frame.
-/

@[expose] public noncomputable section
open Bundle FiberBundle TensorProduct
open scoped Manifold ContDiff

namespace InnerProductSpace

/-- The inverse-metric tensor expressed using an arbitrary finite basis and
its Riesz-dual basis. -/
theorem canonicalCovariantTensor_eq_sum_basis_rieszDual
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) :
    canonicalCovariantTensor V =
      ∑ i : ι,
        (toDual ℝ V).symm
            (LinearMap.toContinuousLinearMap (b.dualBasis i)) ⊗ₜ[ℝ] b i := by
  let o := stdOrthonormalBasis ℝ V
  rw [canonicalCovariantTensor_eq_sum V o]
  calc
    ∑ a, o a ⊗ₜ[ℝ] o a =
        ∑ a, o a ⊗ₜ[ℝ]
          (∑ i, (b.dualBasis i) (o a) • b i) := by
            apply Finset.sum_congr rfl
            intro a ha
            congr 1
            simpa [Module.Basis.coe_dualBasis] using (b.sum_repr (o a)).symm
    _ = ∑ a, ∑ i,
          (b.dualBasis i) (o a) • (o a ⊗ₜ[ℝ] b i) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [TensorProduct.tmul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    _ = ∑ i, ∑ a,
          (b.dualBasis i) (o a) • (o a ⊗ₜ[ℝ] b i) := by
            rw [Finset.sum_comm]
    _ = ∑ i,
          (∑ a, (b.dualBasis i) (o a) • o a) ⊗ₜ[ℝ] b i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [TensorProduct.sum_tmul]
            apply Finset.sum_congr rfl
            intro a ha
            rw [TensorProduct.smul_tmul']
    _ = ∑ i,
        (toDual ℝ V).symm
            (LinearMap.toContinuousLinearMap (b.dualBasis i)) ⊗ₜ[ℝ] b i := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          let φ : V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.dualBasis i)
          let v : V := (toDual ℝ V).symm φ
          calc
            ∑ a, (b.dualBasis i) (o a) • o a =
                ∑ a, ⟪o a, v⟫_ℝ • o a := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  congr 1
                  rw [real_inner_comm]
                  simpa [v, φ] using (toDual_symm_apply (𝕜 := ℝ) (x := o a) (y := φ))
            _ = v := o.sum_repr' v
            _ = (toDual ℝ V).symm
                (LinearMap.toContinuousLinearMap (b.dualBasis i)) := rfl

end InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-- The matrix inverse of the actual local-frame Riemannian Gram matrix.
The explicit instance selection avoids confusion with pointwise inversion of
the definitionally equal iterated function type. -/
noncomputable def localFrameInverseGramMatrix
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (x : M) : Matrix ι ι ℝ :=
  @Inv.inv (Matrix ι ι ℝ) Matrix.inv
    (localFrameGramMatrix (I := I) e b x)

/-- The inverse Gram matrix of a genuine local frame is symmetric. -/
theorem localFrameInverseGramMatrix_apply_comm
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (x : M) (i j : ι) :
    localFrameInverseGramMatrix (I := I) e b x i j =
      localFrameInverseGramMatrix (I := I) e b x j i := by
  let A : Matrix ι ι ℝ := localFrameGramMatrix (I := I) e b x
  have hA : A.transpose = A := by
    ext k l
    change localFrameGramMatrix (I := I) e b x l k =
      localFrameGramMatrix (I := I) e b x k l
    simp [localFrameGramMatrix, real_inner_comm]
  have hInv : (A⁻¹).transpose = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hA]
  have hij := congrFun (congrFun hInv j) i
  simpa [A, localFrameInverseGramMatrix] using hij

/-- The Riesz-dual vector to one member of a local frame. -/
noncomputable def localFrameRieszDual
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (x : M) (hx : x ∈ e.baseSet) (i : ι) : TM x :=
  (InnerProductSpace.toDual ℝ (TM x)).symm
    (LinearMap.toContinuousLinearMap ((e.basisAt b hx).dualBasis i))

/-- Coordinates of the Riesz-dual frame are the columns of the inverse
Riemannian Gram matrix. -/
theorem localFrameRieszDual_eq_sum_inverseGram
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) (i : ι) :
    localFrameRieszDual (I := I) e b x hx i =
      ∑ j : ι,
        localFrameInverseGramMatrix (I := I) e b x j i •
          e.localFrame b j x := by
  let basis : Module.Basis ι ℝ (TM x) := e.basisAt b hx
  let φ : TM x →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (basis.dualBasis i)
  let v : TM x := (InnerProductSpace.toDual ℝ (TM x)).symm φ
  rw [show localFrameRieszDual (I := I) e b x hx i = v by rfl]
  rw [← basis.sum_repr v]
  apply Finset.sum_congr rfl
  intro j hj
  have hcoeff := localFrameCoeff_rieszMap
    (I := I) (E := E) (e := e) (b := b)
    (omega := fun _ => φ) (x := x) hx j
  have hrepr : basis.repr v j = e.localFrameCoeff I b j x v := by
    simpa [basis] using
      (Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
        (I := I) (e := e) (b := b) (hx := hx)
        (s := fun _ => v) (i := j)).symm
  rw [hrepr]
  have hbasis : basis j = e.localFrame b j x := by
    simp [basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet
      (e := e) (b := b) hx]
  rw [hbasis]
  congr 1
  have hcoeff' :
      e.localFrameCoeff I b j x v =
        ∑ k,
          localFrameInverseGramMatrix (I := I) e b x j k *
            φ (e.localFrame b k x) := by
    change e.localFrameCoeff I b j x (rieszMap (I := I) x φ) = _
    exact hcoeff
  have hdual : ∀ k : ι, φ (e.localFrame b k x) = if k = i then 1 else 0 := by
    intro k
    change basis.dualBasis i (e.localFrame b k x) = _
    rw [show e.localFrame b k x = basis k by
      simp [basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet
        (e := e) (b := b) hx]]
    simp [Module.Basis.coe_dualBasis, Finsupp.single_apply, eq_comm]
  rw [hcoeff']
  simp_rw [hdual]
  simp

/-- The canonical inverse metric tensor in an arbitrary genuine local frame. -/
theorem canonicalCovariantTensor_eq_sum_localFrame_inverseGram
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) :
    InnerProductSpace.canonicalCovariantTensor (TM x) =
      ∑ i : ι, ∑ j : ι,
        localFrameInverseGramMatrix (I := I) e b x i j •
          (e.localFrame b i x ⊗ₜ[ℝ] e.localFrame b j x) := by
  let basis : Module.Basis ι ℝ (TM x) := e.basisAt b hx
  rw [InnerProductSpace.canonicalCovariantTensor_eq_sum_basis_rieszDual basis]
  calc
    ∑ i : ι,
        (InnerProductSpace.toDual ℝ (TM x)).symm
            (LinearMap.toContinuousLinearMap (basis.dualBasis i)) ⊗ₜ[ℝ] basis i =
        ∑ i : ι,
          localFrameRieszDual (I := I) e b x hx i ⊗ₜ[ℝ]
            e.localFrame b i x := by
              apply Finset.sum_congr rfl
              intro i hi
              congr 1
              simp [localFrameRieszDual, basis,
                Bundle.Trivialization.localFrame_apply_of_mem_baseSet
                  (e := e) (b := b) hx]
    _ = ∑ i : ι, ∑ j : ι,
          localFrameInverseGramMatrix (I := I) e b x j i •
            (e.localFrame b j x ⊗ₜ[ℝ] e.localFrame b i x) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [localFrameRieszDual_eq_sum_inverseGram (I := I) e b hx i,
                TensorProduct.sum_tmul]
              apply Finset.sum_congr rfl
              intro j hj
              rw [TensorProduct.smul_tmul']
    _ = ∑ i : ι, ∑ j : ι,
          localFrameInverseGramMatrix (I := I) e b x i j •
            (e.localFrame b i x ⊗ₜ[ℝ] e.localFrame b j x) := by
              rw [Finset.sum_comm]

/-- The Riesz representative of an arbitrary covector, expanded in a genuine
local frame using the inverse Gram matrix. -/
theorem riesz_eq_sum_localFrame_inverseGram
    {x : M} (φ : TM x →L[ℝ] ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (hx : x ∈ e.baseSet) :
    (InnerProductSpace.toDual ℝ (TM x)).symm φ =
      ∑ i : ι, ∑ j : ι,
        (localFrameInverseGramMatrix (I := I) e b x i j *
          φ (e.localFrame b i x)) • e.localFrame b j x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let L : TM x →ₗ[ℝ] TM x →ₗ[ℝ] TM x :=
    { toFun := fun u =>
        { toFun := fun v => φ u • v
          map_add' := by intro v w; simp [smul_add]
          map_smul' := by intro c v; simp [smul_smul, mul_comm] }
      map_add' := by intro u v; ext w; simp [add_smul]
      map_smul' := by intro c u; ext w; simp [smul_smul] }
  have hcanonical :
      TensorProduct.lift L (InnerProductSpace.canonicalCovariantTensor (TM x)) =
        (InnerProductSpace.toDual ℝ (TM x)).symm φ := by
    let o : OrthonormalBasis (Fin (Module.finrank ℝ (TM x))) ℝ (TM x) :=
      stdOrthonormalBasis ℝ (TM x)
    rw [InnerProductSpace.canonicalCovariantTensor_eq_sum (TM x) o, map_sum]
    calc
      ∑ i, TensorProduct.lift L (o i ⊗ₜ[ℝ] o i) =
          ∑ i, φ (o i) • o i := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ = ∑ i : Fin (Module.finrank ℝ (TM x)),
          inner ℝ (o i) ((InnerProductSpace.toDual ℝ (TM x)).symm φ) • o i := by
            apply Finset.sum_congr rfl
            intro i hi
            congr 1
            rw [real_inner_comm]
            exact
              (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := o i) (y := φ)).symm
      _ = (InnerProductSpace.toDual ℝ (TM x)).symm φ := o.sum_repr' _
  rw [← hcanonical,
    canonicalCovariantTensor_eq_sum_localFrame_inverseGram
      (I := I) (E := E) e b hx, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [L, mul_smul]

/-- **Local-frame formula for the actual connection Laplacian.**  Its
principal contraction coefficients are exactly the inverse Gram matrix of
the Riemannian metric in the chosen local tangent frame. -/
theorem connectionLaplacian_eq_sum_localFrame_inverseGram
    (cov : CovariantDerivative I E TM)
    (h : ∀ x : M, T₂ x)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) :
    connectionLaplacian cov h x =
      ∑ i : ι, ∑ j : ι,
        localFrameInverseGramMatrix (I := I) e b x i j •
          covariantHessianTwoTensor cov h x
            (e.localFrame b i x) (e.localFrame b j x) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [connectionLaplacian,
    canonicalCovariantTensor_eq_sum_localFrame_inverseGram
      (I := I) (E := E) e b hx, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMapClass.map_smul]
  rfl

/-- Contraction of any covariant two-tensor with the canonical inverse metric,
expressed in an arbitrary genuine local frame. -/
theorem bilinearContraction_eq_sum_localFrame_inverseGram
    {x : M} (B : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (hx : x ∈ e.baseSet) :
    TensorProduct.lift B (InnerProductSpace.canonicalCovariantTensor (TM x)) =
      ∑ i : ι, ∑ j : ι,
        localFrameInverseGramMatrix (I := I) e b x i j *
          B (e.localFrame b i x) (e.localFrame b j x) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [canonicalCovariantTensor_eq_sum_localFrame_inverseGram
    (I := I) (E := E) e b hx, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [TensorProduct.lift.tmul, LinearMapClass.map_smul, smul_eq_mul]

/-- The Hilbert--Schmidt square of a bilinear form, expressed in an arbitrary
genuine local frame. -/
theorem bilinearNormSq_eq_sum_localFrame_inverseGram
    {x : M} (B : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (hx : x ∈ e.baseSet) :
    (by
      let _ : FiniteDimensional ℝ (TM x) :=
        VectorBundle.finiteDimensional ℝ E TM x
      let o := stdOrthonormalBasis ℝ (TM x)
      exact ∑ a, ∑ c, (B (o a) (o c)) ^ 2) =
      ∑ i : ι, ∑ j : ι,
        localFrameInverseGramMatrix (I := I) e b x i j *
          (∑ k : ι, ∑ l : ι,
            localFrameInverseGramMatrix (I := I) e b x k l *
              B (e.localFrame b j x) (e.localFrame b k x) *
              B (e.localFrame b i x) (e.localFrame b l x)) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let o : OrthonormalBasis (Fin (Module.finrank ℝ (TM x))) ℝ (TM x) :=
    stdOrthonormalBasis ℝ (TM x)
  let sharp : TM x →ₗ[ℝ] TM x :=
    { toFun := fun u =>
        (InnerProductSpace.toDual ℝ (TM x)).symm
          (LinearMap.toContinuousLinearMap (B u))
      map_add' := by
        intro u v
        apply (InnerProductSpace.toDual ℝ (TM x)).injective
        ext w
        simp
      map_smul' := by
        intro c u
        apply (InnerProductSpace.toDual ℝ (TM x)).injective
        ext w
        simp }
  let C : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ :=
    { toFun := fun u =>
        { toFun := fun v => inner ℝ (sharp u) (sharp v)
          map_add' := by intro v w; rw [map_add, inner_add_right]
          map_smul' := by
            intro c v
            rw [map_smul, real_inner_smul_right]
            simp }
      map_add' := by
        intro u v
        ext w
        change inner ℝ (sharp (u + v)) (sharp w) =
          inner ℝ (sharp u) (sharp w) + inner ℝ (sharp v) (sharp w)
        rw [map_add, inner_add_left]
      map_smul' := by
        intro c u
        ext w
        change inner ℝ (sharp (c • u)) (sharp w) = c * inner ℝ (sharp u) (sharp w)
        rw [map_smul, real_inner_smul_left] }
  have hON :
      TensorProduct.lift C (InnerProductSpace.canonicalCovariantTensor (TM x)) =
        ∑ a, ∑ c, (B (o a) (o c)) ^ 2 := by
    rw [InnerProductSpace.canonicalCovariantTensor_eq_sum (TM x) o, map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [TensorProduct.lift.tmul]
    let φ : TM x →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (B (o a))
    calc
      C (o a) (o a) = inner ℝ (sharp (o a)) (sharp (o a)) := rfl
      _ = ‖sharp (o a)‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = ‖φ‖ ^ 2 := by
            congr 1
            exact (InnerProductSpace.toDual ℝ (TM x)).symm.norm_map φ
      _ = ∑ c, φ (o c) ^ 2 := OrthonormalBasis.norm_dual o φ
      _ = ∑ c, (B (o a) (o c)) ^ 2 := by rfl
  have hlocal := bilinearContraction_eq_sum_localFrame_inverseGram
    (I := I) (E := E) C e b hx
  rw [hON] at hlocal
  change (∑ a, ∑ c, (B (o a) (o c)) ^ 2) = _
  rw [hlocal]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  let φj : TM x →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (B (e.localFrame b j x))
  have hsharpj :
      sharp (e.localFrame b j x) =
        ∑ k : ι, ∑ l : ι,
          (localFrameInverseGramMatrix (I := I) e b x k l *
            φj (e.localFrame b k x)) • e.localFrame b l x := by
    exact riesz_eq_sum_localFrame_inverseGram
      (I := I) (E := E) φj e b hx
  change inner ℝ (sharp (e.localFrame b i x)) (sharp (e.localFrame b j x)) = _
  rw [hsharpj, inner_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [real_inner_smul_right]
  rw [show inner ℝ (sharp (e.localFrame b i x)) (e.localFrame b l x) =
      B (e.localFrame b i x) (e.localFrame b l x) by
    change inner ℝ
      ((InnerProductSpace.toDual ℝ (TM x)).symm
        (LinearMap.toContinuousLinearMap (B (e.localFrame b i x))))
      (e.localFrame b l x) = _
    exact InnerProductSpace.toDual_symm_apply]
  rfl

/-- Scalar curvature in an arbitrary genuine local frame is the contraction
of the actual Ricci tensor with the inverse Gram matrix. -/
theorem scalarCurvature_eq_sum_localFrame_inverseGram
    (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) :
    scalarCurvature (cov := cov) x =
      ∑ i : ι, ∑ j : ι,
        localFrameInverseGramMatrix (I := I) e b x i j *
          ricciCurvature (cov := cov) x
            (e.localFrame b i x) (e.localFrame b j x) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let B : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ := ricciCurvature (cov := cov) x
  have hON :
      TensorProduct.lift B (InnerProductSpace.canonicalCovariantTensor (TM x)) =
        ∑ i : Fin (Module.finrank ℝ (TM x)),
          B ((stdOrthonormalBasis ℝ (TM x)) i)
            ((stdOrthonormalBasis ℝ (TM x)) i) := by
    rw [InnerProductSpace.canonicalCovariantTensor_eq_sum
      (TM x) (stdOrthonormalBasis ℝ (TM x)), map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  calc
    scalarCurvature (cov := cov) x =
        ∑ i : Fin (Module.finrank ℝ (TM x)),
          B ((stdOrthonormalBasis ℝ (TM x)) i)
            ((stdOrthonormalBasis ℝ (TM x)) i) := by
              rw [scalarCurvature_eq_sum]
    _ = TensorProduct.lift B (InnerProductSpace.canonicalCovariantTensor (TM x)) := hON.symm
    _ = ∑ i : ι, ∑ j : ι,
        localFrameInverseGramMatrix (I := I) e b x i j *
          B (e.localFrame b i x) (e.localFrame b j x) := by
            exact bilinearContraction_eq_sum_localFrame_inverseGram
              (I := I) (E := E) B e b hx
    _ = ∑ i : ι, ∑ j : ι,
        localFrameInverseGramMatrix (I := I) e b x i j *
          ricciCurvature (cov := cov) x
            (e.localFrame b i x) (e.localFrame b j x) := rfl

end CovariantDerivative
