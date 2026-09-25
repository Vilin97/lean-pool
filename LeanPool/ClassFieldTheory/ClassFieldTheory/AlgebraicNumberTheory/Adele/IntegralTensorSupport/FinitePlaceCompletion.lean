/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Lattice
/-!
# Finite-place completion maps for relative tensor factors

This module compares the absolute-value and adic-completion models at finite
places and records how the resulting maps preserve norms and integrality.
-/

@[expose] public section

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The canonical dense map from the absolute-value model at a finite
place to mathlib's adic-completion model, universe-polymorphic in the
number field. -/
noncomputable def relativeFinitePlaceCompletionBaseMap
    (w : HeightOneSpectrum (𝓞 K)) :
    WithAbs (NumberField.HeightOneSpectrum.adicAbv K w) →+*
      w.adicCompletion K :=
  (FinitePlace.embedding w).comp
    (WithAbs.equiv
      (NumberField.HeightOneSpectrum.adicAbv K w)).toRingHom

/-- These lemmas record the canonical map and equivalence interfaces for the finite-place model. -/
@[simp]
theorem relativeFinitePlaceCompletionBaseMap_apply
    (w : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K w)) :
    relativeFinitePlaceCompletionBaseMap w x =
      FinitePlace.embedding w
        (WithAbs.equiv
          (NumberField.HeightOneSpectrum.adicAbv K w) x) :=
  rfl

/-- The canonical finite-place map preserves norms. -/
theorem relativeFinitePlaceCompletionBaseMap_norm
    (w : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K w)) :
    ‖relativeFinitePlaceCompletionBaseMap w x‖ = ‖x‖ := by
  rw [relativeFinitePlaceCompletionBaseMap_apply,
    FinitePlace.norm_embedding]
  rfl

/-- The canonical finite-place map is an isometry. -/
theorem relativeFinitePlaceCompletionBaseMap_isometry
    (w : HeightOneSpectrum (𝓞 K)) :
    Isometry (relativeFinitePlaceCompletionBaseMap w) :=
  AddMonoidHomClass.isometry_of_norm _
    (relativeFinitePlaceCompletionBaseMap_norm w)

/-- Extension of the preceding dense map to the completion. -/
noncomputable def relativeFinitePlaceCompletionRingHom
    (w : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K w).Completion →+*
      w.adicCompletion K :=
  UniformSpace.Completion.extensionHom
    (relativeFinitePlaceCompletionBaseMap w)
    (relativeFinitePlaceCompletionBaseMap_isometry w).continuous

/-- Coercion, isometry, and surjectivity facts for the canonical ring homomorphism. -/
@[simp]
theorem relativeFinitePlaceCompletionRingHom_coe
    (w : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K w)) :
    relativeFinitePlaceCompletionRingHom w
        (x :
          (NumberField.HeightOneSpectrum.adicAbv K w).Completion) =
      relativeFinitePlaceCompletionBaseMap w x :=
  UniformSpace.Completion.extensionHom_coe
    (relativeFinitePlaceCompletionBaseMap w)
    (relativeFinitePlaceCompletionBaseMap_isometry w).continuous x

/-- The canonical finite-place ring homomorphism is an isometry. -/
theorem relativeFinitePlaceCompletionRingHom_isometry
    (w : HeightOneSpectrum (𝓞 K)) :
    Isometry (relativeFinitePlaceCompletionRingHom w) :=
  (relativeFinitePlaceCompletionBaseMap_isometry w).completion_extension

/-- The canonical finite-place ring homomorphism is surjective. -/
theorem relativeFinitePlaceCompletionRingHom_surjective
    (w : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective
      (relativeFinitePlaceCompletionRingHom w) := by
  let f := relativeFinitePlaceCompletionRingHom w
  have hrangeClosed : IsClosed (Set.range f) :=
    (relativeFinitePlaceCompletionRingHom_isometry w).isClosedEmbedding.isClosed_range
  have hdense :
      DenseRange (algebraMap K (w.adicCompletion K)) :=
    w.denseRange_algebraMap K
  have hrange :
      Set.range (algebraMap K (w.adicCompletion K)) ⊆
        Set.range f := by
    rintro _ ⟨x, rfl⟩
    let x' : WithAbs
        (NumberField.HeightOneSpectrum.adicAbv K w) :=
      (WithAbs.equiv
        (NumberField.HeightOneSpectrum.adicAbv K w)).symm x
    refine
      ⟨(x' :
          (NumberField.HeightOneSpectrum.adicAbv K w).Completion),
        ?_⟩
    rw [relativeFinitePlaceCompletionRingHom_coe]
    rfl
  intro x
  have hx :
      x ∈ closure
        (Set.range (algebraMap K (w.adicCompletion K))) := by
    rw [hdense.closure_range]
    trivial
  exact closure_minimal hrange hrangeClosed hx

/-- Canonical ring equivalence between the two models of `K_w`. -/
noncomputable def relativeFinitePlaceCompletionRingEquiv
    (w : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K w).Completion ≃+*
      w.adicCompletion K :=
  RingEquiv.ofBijective
    (relativeFinitePlaceCompletionRingHom w)
    ⟨(relativeFinitePlaceCompletionRingHom_isometry w).injective,
      relativeFinitePlaceCompletionRingHom_surjective w⟩

/-- The same comparison as a `K`-algebra equivalence. -/
noncomputable def relativeFinitePlaceCompletionAlgEquiv
    (w : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K w).Completion ≃ₐ[K]
      w.adicCompletion K where
  __ := relativeFinitePlaceCompletionRingEquiv w
  commutes' x := by
    change
      relativeFinitePlaceCompletionRingHom w
          (((WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K w)).symm x :
              WithAbs
                (NumberField.HeightOneSpectrum.adicAbv K w)) :
            (NumberField.HeightOneSpectrum.adicAbv K w).Completion) =
        algebraMap K (w.adicCompletion K) x
    rw [relativeFinitePlaceCompletionRingHom_coe]
    rfl

/-- Base change in the first tensor factor, now without a universe
restriction. -/
noncomputable def relativeFinitePlaceLocalTensorAlgEquiv
    (w : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K w).Completion ⊗[K] L
        ≃ₐ[K]
      w.adicCompletion K ⊗[K] L :=
  Algebra.TensorProduct.congr
    (relativeFinitePlaceCompletionAlgEquiv w)
    (AlgEquiv.refl : L ≃ₐ[K] L)

/-- Membership in the concrete finite-place valuation ring implies the
usual norm bound. -/
theorem norm_le_one_of_mem_adicCompletionIntegers
    (w : HeightOneSpectrum (𝓞 K))
    {x : w.adicCompletion K}
    (hx : x ∈ w.adicCompletionIntegers K) :
    ‖x‖ ≤ 1 := by
  rw [FinitePlace.norm_def]
  exact_mod_cast
    (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w)).2 hx

/-- The concrete adic completion integers are exactly the elements of
norm at most one. -/
theorem mem_adicCompletionIntegers_of_norm_le_one
    (w : HeightOneSpectrum (𝓞 K))
    {x : w.adicCompletion K}
    (hx : ‖x‖ ≤ 1) :
    x ∈ w.adicCompletionIntegers K := by
  rw [FinitePlace.norm_def] at hx
  exact_mod_cast
    (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w)).1 hx

/-- The inverse of the universe-polymorphic completion comparison is
also an isometry. -/
theorem relativeFinitePlaceCompletionAlgEquiv_symm_norm
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K) :
    ‖(relativeFinitePlaceCompletionAlgEquiv w).symm x‖ =
      ‖x‖ := by
  let y :=
    (relativeFinitePlaceCompletionAlgEquiv w).symm x
  have h :=
    (relativeFinitePlaceCompletionRingHom_isometry w).norm_map_of_map_zero
      (map_zero
        (relativeFinitePlaceCompletionRingHom w)) y
  have hy :
      relativeFinitePlaceCompletionRingHom w y = x := by
    change
      relativeFinitePlaceCompletionAlgEquiv w y = x
    exact
      (relativeFinitePlaceCompletionAlgEquiv w).apply_symm_apply x
  rw [hy] at h
  exact h.symm

/-- Cramer's rule over an integrally closed base: coordinates are
integral once the trace matrix, the trace vector, and the inverse
discriminant are integral. -/
theorem basis_coord_isIntegral_of_integral_traces
    {R A B ι : Type*}
    [CommRing R] [Field A] [CommRing B]
    [Algebra R A] [Algebra A B]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A B)
    {x : B}
    (hM : ∀ j k, IsIntegral R
      (Algebra.trace A B (b j * b k)))
    (ht : ∀ j, IsIntegral R
      (Algebra.trace A B (x * b j)))
    (hdiscInv : IsIntegral R (Algebra.discr A b)⁻¹)
    (hdiscne : Algebra.discr A b ≠ 0)
    (i : ι) :
    IsIntegral R (b.equivFun x i) := by
  let M : Matrix ι ι A := Algebra.traceMatrix A b
  let c : ι → A := b.equivFun x
  let t : ι → A := fun j => Algebra.trace A B (x * b j)
  have hM' : ∀ j k, IsIntegral R (M j k) := by
    intro j k
    exact hM j k
  have ht' : ∀ j, IsIntegral R (t j) := by
    intro j
    exact ht j
  have hcramer : IsIntegral R (M.cramer t i) := by
    rw [Matrix.cramer_apply]
    apply IsIntegral.det
    intro j k
    by_cases hki : k = i
    · simpa [Matrix.updateCol_apply, hki] using ht' j
    · simpa [Matrix.updateCol_apply, hki] using hM' j k
  have hmul : M.mulVec c = t :=
    Algebra.traceMatrix_of_basis_mulVec b x
  have hcramerEq : M.det • c = M.cramer t := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hmul,
      Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcoord :
      Algebra.discr A b * c i = M.cramer t i := by
    have hi := congrFun hcramerEq i
    simpa [M, Algebra.discr_def, Pi.smul_apply] using hi
  have hcEq :
      c i = (Algebra.discr A b)⁻¹ * M.cramer t i := by
    rw [← hcoord, ← mul_assoc, inv_mul_cancel₀ hdiscne, one_mul]
  change IsIntegral R (c i)
  rw [hcEq]
  exact hdiscInv.mul hcramer

omit [NumberField L] in
/-- The trace matrix of the tensor-product basis is obtained from the
original trace matrix by scalar extension. -/
theorem trace_tensorProduct_basis_mul
    {ι : Type*}
    (b : Module.Basis ι K L)
    (A : Type*) [Field A] [Algebra K A]
    (i j : ι) :
    Algebra.trace A (A ⊗[K] L)
        ((Algebra.TensorProduct.basis A b i) *
          (Algebra.TensorProduct.basis A b j)) =
      algebraMap K A (Algebra.trace K L (b i * b j)) := by
  simp only [Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  change LinearMap.trace A (A ⊗[K] L)
      (Algebra.lmul A (A ⊗[K] L) (1 ⊗ₜ[K] (b i * b j))) =
    _
  rw [← Algebra.baseChange_lmul]
  exact LinearMap.trace_baseChange (Algebra.lmul K L (b i * b j)) A

omit [NumberField L] in
/-- Discriminants of tensor-product bases commute with scalar
extension. -/
theorem discr_tensorProduct_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L)
    (A : Type*) [Field A] [Algebra K A] :
    Algebra.discr A (Algebra.TensorProduct.basis A b) =
      algebraMap K A (Algebra.discr K b) := by
  rw [Algebra.discr_def, Algebra.discr_def]
  rw [(algebraMap K A).map_det]
  congr 1
  ext i j
  exact trace_tensorProduct_basis_mul b A i j

omit [NumberField K] [NumberField L] in
/-- Trace in the canonical local tensor algebra preserves integrality
when all completed-field components are integral. -/
theorem isIntegral_trace_tensor_of_components
    [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ))
    (hvK0 : vK.IsNontrivial)
    (x : vK.Completion ⊗[K] L)
    (hx : ∀ w : AbsoluteValueExtension vK L,
      completionTensorDecompositionLeft
          (K := K) (L := L) vK hvK0 x w ∈
        absoluteValueCompletionIntegers w.1
          (absoluteValueExtension_isNonarchimedean vK hvK w)) :
    IsIntegral (absoluteValueCompletionIntegers vK hvK)
      (Algebra.trace vK.Completion
        (vK.Completion ⊗[K] L) x) := by
  classical
  let : Fintype (AbsoluteValueExtension vK L) :=
    completionTensorDecompositionExtensionFintype
      (K := K) (L := L) vK hvK0
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w => AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w => completionModuleFinite vK hvK0 w
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Free vK.Completion w.1.Completion :=
    fun w => Module.Free.of_divisionRing
      vK.Completion w.1.Completion
  let y :
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion :=
    completionTensorDecompositionLeft
      (K := K) (L := L) vK hvK0 x
  have hy :
      ∀ w : AbsoluteValueExtension vK L,
        IsIntegral (absoluteValueCompletionIntegers vK hvK) (y w) := by
    intro w
    exact isIntegral_over_baseCompletionIntegers_of_mem
      (K := K) (L := L) vK hvK hvK0 w (hx w)
  have hsum :
      IsIntegral (absoluteValueCompletionIntegers vK hvK)
        (∑ w : AbsoluteValueExtension vK L,
          Algebra.trace vK.Completion w.1.Completion (y w)) := by
    apply IsIntegral.sum
    intro w _
    exact Algebra.isIntegral_trace (hy w)
  rw [← ValuationTheory.Completion.algebra_trace_pi_apply
    (fun w : AbsoluteValueExtension vK L => w.1.Completion) y] at hsum
  rw [Algebra.trace_eq_of_algEquiv
    (completionTensorDecompositionLeft
      (K := K) (L := L) vK hvK0) x] at hsum
  exact hsum
