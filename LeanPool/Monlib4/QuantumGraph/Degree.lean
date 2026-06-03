/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.PhiMap
import LeanPool.Monlib4.QuantumGraph.Basic
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import LeanPool.Monlib4.QuantumGraph.Example

/-!
# LeanPool.Monlib4.QuantumGraph.Degree

Imported Lean Pool material for `LeanPool.Monlib4.QuantumGraph.Degree`.
-/

open scoped InnerProductSpace ComplexOrder

theorem schurProjection.innerOne_map_one_nonneg
  {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A]
  [QuantumSet B]
  [PartialOrder A] [PartialOrder B] [StarOrderedRing A] [StarOrderedRing B]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b)
  (h₂ : ∀ ⦃a : B⦄, 0 ≤ a ↔ ∃ (b : B), a = star b * b)
  {f : A →ₗ[ℂ] B}
  (h : schurProjection f) :
    0 ≤ ⟪1, f 1⟫_ℂ :=
by
  have iPM := schurProjection.isPosMap h₁ h
  obtain ⟨x, hx⟩ := h₂.mp (@iPM 1 zero_le_one)
  rw [hx, ← inner_conj_symm, QuantumSet.inner_star_left, star_star, mul_one,
    inner_conj_symm, ← add_halves (-k B), ← QuantumSet.modAut_apply_modAut,
    ← AlgEquiv.toLinearMap_apply, ← LinearMap.adjoint_inner_right,
    QuantumSet.modAut_adjoint, AlgEquiv.toLinearMap_apply]
  exact inner_self_nonneg'

theorem QuantumGraph.toSubset_iff {A : Type*} [starAlgebra A] [h : QuantumSet A] {f :
    A →ₗ[ℂ] A} (r : ℝ) :
  letI := QuantumSet.instSubset (A := A) h r
  QuantumGraph (QuantumSet.subset r A)
  (LinearMap.toSubsetQuantumSet f r r) ↔ QuantumGraph A f :=
by
  simp only [quantumGraph_iff, schurMul_toSubsetQuantumSet, LinearMap.toSubsetQuantumSet_inj]

theorem QuantumGraph.real_toSubset_iff {A : Type*} [starAlgebra A] [h : QuantumSet A] {f :
    A →ₗ[ℂ] A} (r : ℝ) :
  letI := QuantumSet.instSubset (A := A) h r
  QuantumGraph.Real (QuantumSet.subset r A)
  (LinearMap.toSubsetQuantumSet f r r) ↔ QuantumGraph.Real A f :=
by
  simp only [real_iff, LinearMap.toSubsetQuantumSet_isReal_iff,
    schurMul_toSubsetQuantumSet, LinearMap.toSubsetQuantumSet_inj]

theorem QuantumGraph.Real.innerOne_map_one_nonneg
  {A : Type*} [starAlgebra A] [hA : QuantumSet A]
  [PartialOrder A] [StarOrderedRing A]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b) {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) :
    0 ≤ ⟪1, f 1⟫_ℂ :=
schurProjection.innerOne_map_one_nonneg h₁ h₁ (quantumGraphReal_iff_schurProjection.mp h)

open scoped TensorProduct

attribute [local instance] starAlgebra.mulOpposite
attribute [local instance] InnerProductAlgebra.mulOpposite
attribute [local instance] QuantumSet.mulOpposite
attribute [local instance] MulOpposite.starRing

theorem QuantumGraph.Real.innerOne_map_one_eq_zero_iff_of_kms
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) [kms : Fact (k A = -(1 / 2))] :
    ⟪1, f 1⟫_ℂ = 0 ↔ f = 0 :=
by
  rw [oneInner_map_one_eq_oneInner_Psi_map _ 0 (k A + (1/2)),
    ← (quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp h).1]
  nth_rw 1 [← (quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp h).2]
  simp_rw [Coalgebra.inner_eq_counit']
  rw [QuantumSet.counit_isFaithful, map_eq_zero_iff _ (LinearEquiv.injective _)]

theorem QuantumGraph.Real.innerOne_map_one_eq_zero_iff
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A} (h : QuantumGraph.Real A f) :
    ⟪1, f 1⟫_ℂ = 0 ↔ f = 0 :=
by
  letI := QuantumSet.instSubset (A := A) (by infer_instance) (-(1 / 2))
  have kms : Fact (k (QuantumSet.subset (-(1/2)) A) = -(1/2)) := Fact.mk rfl
  let f' := LinearMap.toSubsetQuantumSet f (-(1/2)) (-(1/2))
  rw [QuantumSet.innerOne_map_one_toSubset_eq (- (1/2)) (- (1/2)),
    QuantumGraph.Real.innerOne_map_one_eq_zero_iff_of_kms
      ((QuantumGraph.real_toSubset_iff (-(1/2))).mpr h) (kms := kms)]
  rfl

theorem QuantumGraph.real_iff_complement'_real
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A} :
  QuantumGraph.Real A f ↔ QuantumGraph.Real A (Qam.complement' f) :=
by
  simp only [real_iff, ← Qam.Nontracial.Complement'.qam, ← Qam.Nontracial.Complement'.qam.isReal]

theorem QuantumGraph.Real.innerOne_map_one_eq_norm_pow_four_iff_of_kms
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) [kms : Fact (k A = -(1 / 2))] :
    ⟪1, f 1⟫_ℂ = ‖(1 : A)‖ ^ 4 ↔ f = rankOne ℂ (1 : A) (1 : A) :=
by
  have : ‖(1 : A)‖ ^ 4 = ⟪(1 : A ⊗[ℂ] Aᵐᵒᵖ), 1⟫_ℂ :=
  by
    rw [Algebra.TensorProduct.one_def, TensorProduct.inner_tmul]
    simp only [inner_self_eq_norm_sq_to_K, MulOpposite.norm_eq, MulOpposite.unop_one]
    ring_nf
    rfl
  rw [oneInner_map_one_eq_oneInner_Psi_map _ 0 (k A + (1/2))]
  rw [this]
  nth_rw 3 [← QuantumSet.Psi_apply_one_one 0 (k A + ( 1 / 2))]
  rw [eq_comm, ← sub_eq_zero, ← inner_sub_right (𝕜 := ℂ) (E := A ⊗[ℂ] Aᵐᵒᵖ), ← map_sub,
    ← Qam.completeGraph_eq, ← Qam.complement'_eq]
  have := QuantumGraph.real_iff_complement'_real.mp h
  rw [← (quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp this).1]
  nth_rw 1 [← (quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp this).2]
  simp_rw [Coalgebra.inner_eq_counit']
  rw [QuantumSet.counit_isFaithful, map_eq_zero_iff _ (LinearEquiv.injective _),
    Qam.complement'_eq, sub_eq_zero, eq_comm]

theorem QuantumGraph.Real.innerOne_map_one_eq_norm_pow_four_iff
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A} (h : QuantumGraph.Real A f) :
    ⟪1, f 1⟫_ℂ = ‖(1 : A)‖ ^ 4 ↔ f = rankOne ℂ (1 : A) (1 : A) :=
by
  letI := QuantumSet.instSubset (A := A) (by infer_instance) (-(1 / 2))
  have kms : Fact (k (QuantumSet.subset (-(1/2)) A) = -(1/2)) := Fact.mk rfl
  let f' := LinearMap.toSubsetQuantumSet f (-(1/2)) (-(1/2))
  rw [QuantumSet.innerOne_map_one_toSubset_eq (- (1/2)) (- (1/2)), QuantumSet.normOne_toSubset]
  rw [QuantumGraph.Real.innerOne_map_one_eq_norm_pow_four_iff_of_kms
      ((QuantumGraph.real_toSubset_iff (-(1/2))).mpr h) (kms := kms)]
  rw [LinearMap.toSubsetQuantumSet_eq_iff, rankOne_ofSubsetQuantumSet]
  simp_rw [← QuantumSet.toSubsetAlgEquiv_symm_eq_toSubsetEquiv, map_one]

/-- Out-degree operator of a quantum graph. -/
@[simps]
noncomputable def QuantumGraph.outDegree {A : Type*} [starAlgebra A] [QuantumSet A] :
    (A →ₗ[ℂ] A) →ₗ[ℂ] (A →ₗ[ℂ] A) where
  toFun f := LinearMap.mul' ℂ _ ∘ₗ (LinearMap.rTensor _ f)
    ∘ₗ (LinearMap.rTensor _ (Algebra.linearMap ℂ _))
    ∘ₗ (TensorProduct.lid ℂ _).symm.toLinearMap
  map_add' _ _ := by simp only [LinearMap.rTensor_add, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' _ _ := by simp only [LinearMap.rTensor_smul, LinearMap.smul_comp,
    LinearMap.comp_smul]; rfl

theorem QuantumGraph.outDegree_eq {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A} :
  QuantumGraph.outDegree f = lmul (f 1) :=
by
  ext a
  simp only [outDegree_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, one_smul,
    lmul_apply, LinearMap.mul'_apply]

/-- In-degree operator of a quantum graph. -/
@[simps]
noncomputable def QuantumGraph.inDegree {A : Type*} [starAlgebra A] [QuantumSet A] :
    (A →ₗ[ℂ] A) →ₗ⋆[ℂ] (A →ₗ[ℂ] A) where
  toFun f := LinearMap.mul' ℂ _ ∘ₗ (LinearMap.lTensor _ (LinearMap.adjoint f))
    ∘ₗ (LinearMap.lTensor _ (Algebra.linearMap ℂ _))
    ∘ₗ (TensorProduct.rid ℂ _).symm.toLinearMap
  map_add' _ _ := by simp only [map_add, LinearMap.lTensor_add, LinearMap.add_comp,
    LinearMap.comp_add]
  map_smul' _ _ := by simp only [LinearMap.lTensor_smul, LinearMap.smul_comp,
    LinearMap.comp_smul, LinearMap.adjoint_smul]

theorem QuantumGraph.inDegree_eq {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A} :
  QuantumGraph.inDegree f = rmul (LinearMap.adjoint f 1) :=
by
  ext a
  simp only [inDegree_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, one_smul,
    rmul_apply, LinearMap.mul'_apply]

lemma QuantumGraph.outDegree_real_eq {A : Type*} [starAlgebra A] [QuantumSet A] {x : A →ₗ[ℂ] A} :
  LinearMap.real (QuantumGraph.outDegree x) = QuantumGraph.inDegree (symmMap ℂ _ _ x) :=
by
  rw [outDegree_eq, lmul_eq_mul, LinearMap.mulLeft_real,
    ← star_one, ← LinearMap.real_apply, inDegree_eq, symmMap_apply,
    LinearMap.adjoint_adjoint]
  rfl

lemma QuantumGraph.inDegree_real_eq {A : Type*} [starAlgebra A] [QuantumSet A] {x : A →ₗ[ℂ] A} :
  LinearMap.real (QuantumGraph.inDegree x) = QuantumGraph.outDegree ((symmMap ℂ _ _).symm x) :=
by
  rw [LinearMap.real_inj_eq, LinearMap.real_real,
    outDegree_real_eq, LinearEquiv.apply_symm_apply]

theorem QuantumGraph.outDegree_eq' {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A} :
  QuantumGraph.outDegree f =
    (TensorProduct.lid ℂ _).toLinearMap
      ∘ₗ (LinearMap.rTensor _ Coalgebra.counit)
      ∘ₗ (PhiMap f).1
      ∘ₗ (LinearMap.rTensor _ (Algebra.linearMap ℂ _))
      ∘ₗ (TensorProduct.lid ℂ _).symm.toLinearMap :=
by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne f
  simp only [map_sum, LinearMap.IsBimoduleMap.sum_coe, LinearMap.sum_comp, LinearMap.comp_sum]
  congr
  ext
  simp only [PhiMap_rankOne, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.lid_symm_apply,
    LinearMap.rTensor_tmul, TensorProduct.map_tmul,
    TensorProduct.lid_tmul, outDegree_eq, lmul_apply,
    ContinuousLinearMap.coe_coe, rankOne_apply, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, one_smul, ← Coalgebra.inner_eq_counit',
    LinearMap.adjoint_inner_right, rmul_apply, one_mul, smul_mul_assoc]

theorem QuantumGraph.inDegree_eq' {A : Type*} [starAlgebra A] [QuantumSet A]
  (gns : k A = 0) {f : A →ₗ[ℂ] A} :
  QuantumGraph.inDegree f =
    (TensorProduct.rid ℂ _).toLinearMap
      ∘ₗ (LinearMap.lTensor _ Coalgebra.counit)
      ∘ₗ (PhiMap (LinearMap.real f)).1
      ∘ₗ (LinearMap.lTensor _ (Algebra.linearMap ℂ _))
      ∘ₗ (TensorProduct.rid ℂ _).symm.toLinearMap :=
by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne f
  simp only [map_sum, LinearMap.IsBimoduleMap.sum_coe, LinearMap.sum_comp, LinearMap.comp_sum,
    LinearMap.real_sum]
  congr
  ext
  simp only [rankOne_real, PhiMap_rankOne, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.rid_symm_apply,
    LinearMap.lTensor_tmul, TensorProduct.map_tmul,
    TensorProduct.rid_tmul, inDegree_eq, lmul_apply,
    ContinuousLinearMap.coe_coe, rankOne_apply, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, one_smul, ← Coalgebra.inner_eq_counit', rmul_apply,
    rmul_adjoint, starAlgebra.modAut_star, starAlgebra.modAut_apply_modAut, star_star,
    ContinuousLinearMap.linearMap_adjoint, rankOne_adjoint, mul_one]
  ring_nf
  simp only [gns, starAlgebra.modAut_zero, mul_smul_comm,
    QuantumSet.inner_eq_counit, star_one, one_mul, AlgEquiv.one_apply, mul_one]

theorem QuantumGraph.outDegree_apply_schurMul
  {A : Type*} [starAlgebra A] [QuantumSet A] (gns : k A = 0) (f₁ f₂ : A →ₗ[ℂ] A) :
  QuantumGraph.outDegree (f₁ •ₛ f₂)
    = (f₁ ∘ₗ symmMap ℂ _ _ f₂) •ₛ 1 :=
by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne f₁
  obtain ⟨γ, δ, rfl⟩ := LinearMap.exists_sum_rankOne f₂
  simp only [map_sum, LinearMap.sum_apply, LinearMap.sum_comp, LinearMap.comp_sum,
    schurMul.apply_rankOne, QuantumGraph.outDegree_eq,
    ContinuousLinearMap.coe_coe, rankOne_apply, map_smul,
    symmMap_rankOne_apply, LinearMap.rankOne_comp,
    schurMul_one_right_rankOne, lmul_adjoint]
  simp only [lmul_eq_alg_lmul, map_mul, ContinuousLinearMap.linearMap_adjoint,
    rankOne_adjoint, ContinuousLinearMap.coe_coe, rankOne_apply,
    star_smul, star_star, Complex.star_def, inner_conj_symm, map_smul]
  simp only [QuantumSet.inner_conj_left, one_mul, gns]
  ring_nf
  simp only [starAlgebra.modAut_zero, AlgEquiv.one_apply]
  simp only [Module.End.mul_eq_comp, LinearMap.comp_smul]

theorem QuantumGraph.inDegree_apply_schurMul
  {A : Type*} [starAlgebra A] [QuantumSet A] (gns : k A = 0) (f₁ f₂ : A →ₗ[ℂ] A) :
  QuantumGraph.inDegree (f₁ •ₛ f₂)
    = 1 •ₛ (LinearMap.adjoint f₂ ∘ₗ LinearMap.real f₁) :=
by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne f₁
  obtain ⟨γ, δ, rfl⟩ := LinearMap.exists_sum_rankOne f₂
  simp only [map_sum, LinearMap.sum_apply, LinearMap.sum_comp, LinearMap.comp_sum,
    LinearMap.real_sum,
    schurMul.apply_rankOne, QuantumGraph.inDegree_eq,
    ContinuousLinearMap.coe_coe, rankOne_apply, map_smul,
    LinearMap.rankOne_comp, schurMul_one_left_rankOne, rmul_adjoint,
    rankOne_real, ContinuousLinearMap.linearMap_adjoint,
    rankOne_adjoint, ContinuousLinearMap.coe_coe,
    LinearMap.adjoint_smul,
    starAlgebra.modAut_star, starAlgebra.modAut_apply_modAut,
    star_star, inner_conj_symm]
  simp_rw [QuantumSet.inner_star_left, mul_one]
  simp only [gns]
  ring_nf
  simp only [starAlgebra.modAut_zero, AlgEquiv.one_apply]
  simp only [rmul_eq_mul, LinearMap.mulRight_mul]
  rw [Finset.sum_comm]
  simp only [LinearMap.comp_smul]

/-- A quantum graph is regular of degree `d` when both `f` and its adjoint send `1` to `d • 1`. -/
def QuantumGraph.IsRegular
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A}
  (h : QuantumGraph A f) (d : ℂ) : Prop :=
let _ := h
f 1 = d • 1 ∧ LinearMap.adjoint f 1 = d • 1

lemma QuantumGraph.degree_is_real_of_real
  {A : Type*} [starAlgebra A] [QuantumSet A] [Nontrivial A] {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) (d : ℂ)
  (h2 : (h.toQuantumGraph).IsRegular d) :
    d = Complex.re d :=
by
  have := calc d • (1 : A) = f 1 := h2.1.symm
    _ = f.real 1 := by rw [LinearMap.real_of_isReal h.isReal]
    _ = star (f 1) := by rw [LinearMap.real_apply, star_one]
    _ = star d • (1 : A) := by rw [h2.1, star_smul, star_one]
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero] at this
  simp_rw [one_ne_zero, or_false, sub_eq_zero] at this
  exact (Complex.conj_eq_iff_re.mp this.symm).symm

open scoped TensorProduct
lemma PhiMap_apply_one_one
  {A B : Type*} [starAlgebra B] [starAlgebra A] [QuantumSet A] [QuantumSet B] :
  (PhiMap (rankOne ℂ (1 : B) (1 : A))).1 = (1 : A ⊗[ℂ] B →ₗ[ℂ] _) :=
by
  simp_rw [PhiMap_apply, Upsilon_apply_one_one]
  exact rmulMapLmul_one

open scoped InnerProductSpace

lemma ContinuousLinearMap.isPositive_iff_complex' {E' :
    Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [CompleteSpace E'] (T : E' →L[ℂ] E') :
  T.IsPositive ↔ ∀ (x : E'), 0 ≤ ⟪T x, x⟫_ℂ :=
by simp [isPositive_iff_complex, RCLike.nonneg_def' (𝕜 := ℂ)]
lemma ContinuousLinearMap.isPositive_iff_complex'' {E' :
    Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [CompleteSpace E'] (T : E' →L[ℂ] E') :
  T.IsPositive ↔ ∀ (x : E'), 0 ≤ ⟪x, T x⟫_ℂ :=
by
  simp_rw [isPositive_iff_complex', ← inner_conj_symm (T _),
    Complex.nonneg_iff, Complex.conj_re, Complex.conj_im, zero_eq_neg, eq_comm]

lemma ContinuousLinearMap.le_iff_complex_inner_le {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E] {p q : E →L[ℂ] E} :
  p ≤ q ↔ ∀ (x : E), ⟪x, p x⟫_ℂ ≤ ⟪x, q x⟫_ℂ :=
by
  rw [ContinuousLinearMap.le_def, isPositive_iff_complex'']
  simp only [sub_apply, inner_sub_right, sub_nonneg]

theorem isOrthogonalProjection_iff_exists {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {p : E →L[ℂ] E} :
  p.IsOrthogonalProjection ↔ (∃ U, orthogonalProjection' U = p) :=
by
  rw [ContinuousLinearMap.isOrthogonalProjection_iff', and_comm, ← orthogonal_projection_iff]

theorem orthogonalProjection'_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [CompleteSpace (⊤ : Submodule ℂ E)]
  (U : Submodule ℂ E) [CompleteSpace U] :
  orthogonalProjection' U ≤ 1 :=
by
  rw [← orthogonalProjection_of_top, orthogonalProjection.is_le_iff_subset]
  exact fun _ _ ↦ trivial

theorem isOrthogonalProjection_le_one {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {p : E →L[ℂ] E} (hp : p.IsOrthogonalProjection) :
    p ≤ 1 :=
by
  obtain ⟨U, rfl⟩ := isOrthogonalProjection_iff_exists.mp hp
  exact orthogonalProjection'_le_one U

lemma QuantumGraph.Real.gns_le_one
  {A : Type*} [starAlgebra A] [QuantumSet A] {f : A →ₗ[ℂ] A}
  (hf : QuantumGraph.Real A f) (gns : k A = 0) :
    LinearMap.toContinuousLinearMap (PhiMap f).1 ≤ 1 :=
isOrthogonalProjection_le_one
  ((quantumGraphReal_iff_Upsilon_toBimodule_orthogonalProjection gns).mp hf)

theorem QuantumGraph.Real.innerOne_map_one_le_norm_one_pow_four_of_gns
  {A : Type*} [starAlgebra A] [QuantumSet A] [Nontrivial A]
  [PartialOrder A] [StarOrderedRing A]
  (gns : k A = 0)
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b)
  {f : A →ₗ[ℂ] A}
  (h : QuantumGraph.Real A f) :
    ⟪1, f 1⟫_ℂ ≤ ‖(1 : A)‖ ^ 4 :=
by
  have sP : schurProjection f := ⟨h.isIdempotentElem, h.isReal⟩
  have iPM := schurProjection.isPosMap h₁ sP
  calc ⟪1, f 1⟫_ℂ = Complex.re ⟪1, f 1⟫_ℂ :=
      QuantumSet.innerOne_map_one_isReal_ofReal h.isReal
    _ = Complex.re ⟪1, (PhiMap f).1 1⟫_ℂ := by rw [← oneInner_map_one_eq_oneInner_PhiMap_map_one]
    _ = (RCLike.re ⟪1, LinearMap.toContinuousLinearMap (PhiMap f).1 1⟫_ℂ) := rfl
    _ ≤ RCLike.re ⟪(1 : A ⊗[ℂ] A), (1 : (A ⊗[ℂ] A) →L[ℂ] (A ⊗[ℂ] A)) 1⟫_ℂ :=
        by
          rw [Complex.real_le_real]
          exact
            ((RCLike.le_def.mp ((ContinuousLinearMap.le_iff_complex_inner_le
                (p := LinearMap.toContinuousLinearMap (PhiMap f).1)
                (q := 1)).mp
              (QuantumGraph.Real.gns_le_one h gns) 1)).1)
    _ = (‖(1 : A)‖ ^ 2) ^ 2 :=
      by
        rw [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq (𝕜 := ℂ) (E := A ⊗[ℂ] A),
          Algebra.TensorProduct.one_def, norm_tmul, ← pow_two]
        simp
    _ = ‖(1 : A)‖ ^ 4 := by simp only [← pow_mul]

lemma QuantumGraph.zero_le_degree_le_norm_one_sq_of_gns
  {A : Type*} [starAlgebra A] [QuantumSet A] [Nontrivial A]
  [PartialOrder A] [StarOrderedRing A]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b) (gns : k A = 0)
  {f : A →ₗ[ℂ] A} (h : QuantumGraph.Real A f) (d : ℂ) (h2 : (h.toQuantumGraph).IsRegular d) :
    0 ≤ d ∧ d ≤ ‖(1 : A)‖ ^ 2 :=
by
  have sP : schurProjection f := ⟨h.isIdempotentElem, h.isReal⟩
  have iPM := schurProjection.isPosMap h₁ sP
  have hd : d = ⟪1, f 1⟫_ℂ / ⟪1, (1 : A)⟫_ℂ :=
    by
      rw [h2.1, inner_smul_right, mul_div_assoc, div_self, mul_one]
      norm_num
  rw [hd]
  refine ⟨mul_nonneg (QuantumGraph.Real.innerOne_map_one_nonneg h₁ h) ?_, ?_⟩
  · simp only [inner_self_eq_norm_sq_to_K]
    simp only [Complex.coe_algebraMap, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
      Complex.zero_le_real, inv_nonneg, pow_two_nonneg]
  rw [← ge_iff_le, ← Complex.ofReal_pow]
  calc ((‖(1 : A)‖ ^ 2 : ℝ) : ℂ) = ((‖(1 : A)‖ ^ 2) ^ 2 / ‖(1 : A)‖ ^ 2 : ℝ) :=
      by
        rw [pow_two, pow_two, mul_div_assoc, div_self, mul_one]
        norm_num
    _ = ((‖(1 : A)‖ ^ 4 / ‖(1 : A)‖ ^ 2 : ℝ) : ℂ) := by simp [← pow_mul]
    _ ≥ (⟪1, f 1⟫_ℂ / (‖(1 : A)‖ ^ 2 : ℝ) : ℂ) :=
        by
          rw [QuantumSet.innerOne_map_one_isReal_ofReal h.isReal]
          rw [← Complex.ofReal_div, ge_iff_le, Complex.real_le_real]
          apply div_le_div_of_nonneg_right ?_ (sq_nonneg _)
          · simpa only [← Complex.real_le_real,
              ← QuantumSet.innerOne_map_one_isReal_ofReal h.isReal, Complex.ofReal_pow] using
              Real.innerOne_map_one_le_norm_one_pow_four_of_gns gns h₁ h
  simp [inner_self_eq_norm_sq_to_K]

theorem StarOrderedRing.nonneg_iff_toQuantumSetSubset
  {A : Type*} [NonUnitalSemiring A] [StarRing A]
  [PartialOrder A] [StarOrderedRing A] (r : ℝ) :
  (∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b) ↔
    ∀ ⦃a : QuantumSet.subset r A⦄, 0 ≤ a ↔ ∃ (b : QuantumSet.subset r A), a = star b * b :=
Iff.rfl

theorem Coalgebra.comul_comp_mul_quantumSetSubset
  {A : Type*} [starAlgebra A] [QuantumSet A] (r : ℝ) :
  letI subsetA : QuantumSet (QuantumSet.subset r A) :=
    QuantumSet.instSubset (A := A) (by infer_instance) r
  letI frobSubsetA : FrobeniusAlgebra ℂ (QuantumSet.subset r A) :=
    QuantumSet.isFrobeniusAlgebra
  letI coalgebraSubsetA : Coalgebra ℂ (QuantumSet.subset r A) :=
    FrobeniusAlgebra.toCoalgebra
  Coalgebra.comul ∘ₗ LinearMap.mul' ℂ (QuantumSet.subset r A)
    = (TensorProduct.map (QuantumSet.toSubsetAlgEquiv r).toLinearMap
        (QuantumSet.toSubsetAlgEquiv r).toLinearMap)
      ∘ₗ (Coalgebra.comul (R := ℂ) (A := A)
      ∘ₗ (LinearMap.mul' ℂ A))
      ∘ₗ (TensorProduct.map (QuantumSet.toSubsetAlgEquiv r).symm.toLinearMap
          (QuantumSet.toSubsetAlgEquiv r).symm.toLinearMap) :=
by
  letI subsetA : QuantumSet (QuantumSet.subset r A) :=
    QuantumSet.instSubset (A := A) (by infer_instance) r
  letI frobSubsetA : FrobeniusAlgebra ℂ (QuantumSet.subset r A) :=
    QuantumSet.isFrobeniusAlgebra
  letI coalgebraSubsetA : Coalgebra ℂ (QuantumSet.subset r A) :=
    FrobeniusAlgebra.toCoalgebra
  letI : Fact (k A = k A) := Fact.mk rfl
  letI tensorA : QuantumSet (A ⊗[ℂ] A) :=
    QuantumSet.tensorProduct (A := A) (B := A) (h := Fact.mk rfl)
  letI subsetTensorA : QuantumSet (QuantumSet.subset r (A ⊗[ℂ] A)) :=
    QuantumSet.instSubset (A := A ⊗[ℂ] A) (by infer_instance) r
  calc
    Coalgebra.comul ∘ₗ LinearMap.mul' ℂ (QuantumSet.subset r A)
        = Coalgebra.comul ∘ₗ
            ((QuantumSet.toSubsetAlgEquiv r).toLinearMap ∘ₗ
              LinearMap.mul' ℂ A ∘ₗ
                TensorProduct.map (QuantumSet.toSubsetAlgEquiv r).symm.toLinearMap
                  (QuantumSet.toSubsetAlgEquiv r).symm.toLinearMap) :=
          congrArg (fun f => Coalgebra.comul ∘ₗ f)
            (LinearMap.mul'_quantumSet_subset_eq (A := A) r)
    _ = (TensorProduct.map (QuantumSet.toSubsetAlgEquiv r).toLinearMap
          (QuantumSet.toSubsetAlgEquiv r).toLinearMap)
        ∘ₗ (Coalgebra.comul (R := ℂ) (A := A)
        ∘ₗ LinearMap.mul' ℂ A)
        ∘ₗ (TensorProduct.map (QuantumSet.toSubsetAlgEquiv r).symm.toLinearMap
            (QuantumSet.toSubsetAlgEquiv r).symm.toLinearMap) := by
          rw [QuantumSet.comul_subset_eq r]
          simp only [← LinearMap.comp_assoc]
          rw [LinearMap.comp_assoc (QuantumSet.toSubsetAlgEquiv r).toLinearMap
            (QuantumSet.toSubsetAlgEquiv r).symm.toLinearMap
            ((TensorProduct.map (QuantumSet.toSubsetAlgEquiv r).toLinearMap
              (QuantumSet.toSubsetAlgEquiv r).toLinearMap) ∘ₗ
                Coalgebra.comul (R := ℂ) (A := A))]
          rw [AlgEquiv.symm_comp_toLinearMap]
          simp only [LinearMap.comp_id, LinearMap.comp_assoc]


theorem QuantumGraph.toSubset_isRegular_iff
  {A : Type*} [starAlgebra A] [QuantumSet A]
  {f : A →ₗ[ℂ] A} (r : ℝ) (h : QuantumGraph A f) (d : ℂ) :
  let h' := (QuantumGraph.toSubset_iff r).mpr h;
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r;
    h.IsRegular d ↔ h'.IsRegular d :=
by
  intro h'
  simp only [QuantumGraph.IsRegular, LinearMap.toSubsetQuantumSet_apply]
  rw [LinearMap.toSubsetQuantumSet_adjoint_apply]
  simp only [LinearMap.comp_apply, ← QuantumSet.toSubsetAlgEquiv_symm_eq_toSubsetEquiv,
    ← QuantumSet.toSubsetAlgEquiv_eq_toSubsetEquiv, map_one, AlgEquiv.toLinearMap_apply]
  nth_rw 3 [eq_comm]
  nth_rw 4 [eq_comm]
  simp_rw [← AlgEquiv.symm_apply_eq, map_smul, map_one]
  nth_rw 1 [eq_comm]
  nth_rw 2 [eq_comm]

lemma QuantumGraph.zero_le_degree_le_norm_one_sq
  {A : Type*} [starAlgebra A] [QuantumSet A] [Nontrivial A]
  [PartialOrder A] [StarOrderedRing A]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b)
  {f : A →ₗ[ℂ] A} (h : QuantumGraph.Real A f) (d : ℂ) (h2 : (h.toQuantumGraph).IsRegular d) :
    0 ≤ d ∧ d ≤ ‖(1 : A)‖ ^ 2 :=
by
  letI subsetStarAlgebra : starAlgebra (QuantumSet.subset 0 A) :=
    QuantumSet.subsetStarAlgebra 0
  letI subsetQuantumSet : QuantumSet (QuantumSet.subset 0 A) :=
    QuantumSet.instSubset (A := A) (by infer_instance) 0
  letI : NonUnitalNonAssocSemiring (QuantumSet.subset 0 A) := inferInstance
  letI : NonUnitalSemiring (QuantumSet.subset 0 A) := inferInstance
  letI : StarRing (QuantumSet.subset 0 A) := inferInstance
  letI subsetStarOrderedRing : StarOrderedRing (QuantumSet.subset 0 A) := inferInstance
  rw [QuantumSet.normOne_toSubset 0]
  exact @QuantumGraph.zero_le_degree_le_norm_one_sq_of_gns
    (QuantumSet.subset 0 A) subsetStarAlgebra subsetQuantumSet inferInstance inferInstance
    subsetStarOrderedRing
    ((StarOrderedRing.nonneg_iff_toQuantumSetSubset 0).mp h₁) rfl
    (f.toSubsetQuantumSet 0 0)
    ((QuantumGraph.real_toSubset_iff 0).mpr h) _
    ((QuantumGraph.toSubset_isRegular_iff 0 h.toQuantumGraph d).mp h2)
