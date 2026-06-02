/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.SchurMul
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Symm
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.Lemmas
import LeanPool.Monlib4.LinearAlgebra.Ips.MinimalProj
import LeanPool.Monlib4.LinearAlgebra.PosMapIsReal
import LeanPool.Monlib4.LinearAlgebra.MyBimodule
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.Submodule
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.PhiMap
import LeanPool.Monlib4.LinearAlgebra.Ips.Functional
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Subset

/-!
# LeanPool.Monlib4.QuantumGraph.Basic

Imported Lean Pool material for `LeanPool.Monlib4.QuantumGraph.Basic`.
-/
-- import LeanPool.Monlib4.LinearAlgebra.QuantumSet.TensorProduct

local notation x " ⊗ₘ " y => TensorProduct.map x y

instance FiniteDimensional.innerProductSpace.complete {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] : CompleteSpace E :=
  FiniteDimensional.complete ℂ E

theorem symmMap_apply_schurMul {A B : Type*} [starAlgebra A] [starAlgebra B]
    [hA : QuantumSet A] [QuantumSet B] (f g : A →ₗ[ℂ] B) :
  symmMap ℂ _ _ (f •ₛ g) = (symmMap _ _ _ g) •ₛ (symmMap _ _ _ f) :=
by
  rw [symmMap_apply, schurMul_real, schurMul_adjoint]
  rfl

alias QuantumSet.modAut_star := starAlgebra.modAut_star
alias QuantumSet.modAut_zero := starAlgebra.modAut_zero

theorem Psi_apply_linearMap_comp_linearMap_of_commute_modAut {A B C D : Type*}
  [ha : starAlgebra A] [hb : starAlgebra B]
  [hc : starAlgebra C] [hd : starAlgebra D]
  [hA : QuantumSet A] [hB : QuantumSet B]
  [hC : QuantumSet C] [hD : QuantumSet D]
  {f : A →ₗ[ℂ] B} {g : D →ₗ[ℂ] C}
  (t r : ℝ)
  (hf : (hb.modAut t).toLinearMap.comp f = f.comp (ha.modAut t).toLinearMap)
  (hg : (hc.modAut r).toLinearMap.comp g = g.comp (hd.modAut r).toLinearMap)
  (x : C →ₗ[ℂ] A) :
  QuantumSet.Psi t r (f ∘ₗ x ∘ₗ g)
    = (f ⊗ₘ ((symmMap ℂ _ _).symm g).op) (QuantumSet.Psi t r x) :=
by
  apply_fun LinearMap.adjoint at hg
  simp_rw [LinearMap.adjoint_comp, ← LinearMap.star_eq_adjoint,
    isSelfAdjoint_iff.mp (QuantumSet.modAut_isSelfAdjoint _)] at hg
  have : ∀ a b, QuantumSet.Psi t r (f ∘ₗ (rankOne ℂ a b).toLinearMap ∘ₗ g)
    = (f ⊗ₘ ((symmMap ℂ _ _).symm g).op) (QuantumSet.Psi t r (rankOne ℂ a b).toLinearMap) :=
      fun _ _ => by
    simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply] at hf hg
    simp only [symmMap_symm_apply,
      QuantumSet.Psi_apply, LinearMap.rankOne_comp, LinearMap.comp_rankOne,
      QuantumSet.PsiToFun_apply, TensorProduct.map_tmul,
      QuantumSet.modAut_star, LinearMap.real_apply,
      LinearMap.op_apply,
      MulOpposite.unop_op, neg_neg, star_star, ← hf, ← hg, QuantumSet.modAut_star]
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
  simp only [LinearMap.comp_sum, LinearMap.sum_comp, map_sum, this]

theorem symmMap_symm_comp {A B C : Type*} [starAlgebra A]
  [starAlgebra B] [hA : QuantumSet A] [hB : QuantumSet B]
  [starAlgebra C] [QuantumSet C]
  (x : A →ₗ[ℂ] B) (y : C →ₗ[ℂ] A) :
  (symmMap ℂ _ _).symm (x ∘ₗ y) = (symmMap ℂ _ _).symm y ∘ₗ (symmMap ℂ _ _).symm x :=
by
  simp only [symmMap_symm_apply, LinearMap.adjoint_comp, LinearMap.real_comp]

theorem linearMap_map_Psi_of_commute_modAut {A B C D : Type*}
  [ha : starAlgebra A] [hb : starAlgebra B]
  [hc : starAlgebra C] [hd : starAlgebra D]
  [hA : QuantumSet A] [hB : QuantumSet B]
  [hC : QuantumSet C] [hD : QuantumSet D]
  {f : A →ₗ[ℂ] B} {g : Cᵐᵒᵖ →ₗ[ℂ] Dᵐᵒᵖ}
  (t r : ℝ)
  (hf : (hb.modAut t).toLinearMap.comp f = f.comp (ha.modAut t).toLinearMap)
  (hg : (hd.modAut r).toLinearMap.comp g.unop = g.unop.comp (hc.modAut r).toLinearMap)
  (x : C →ₗ[ℂ] A) :
  (f ⊗ₘ g) (QuantumSet.Psi t r x) = QuantumSet.Psi t r (f ∘ₗ x ∘ₗ ((symmMap ℂ _ _) g.unop)) :=
by
  rw [Psi_apply_linearMap_comp_linearMap_of_commute_modAut,
    LinearEquiv.symm_apply_apply, LinearMap.unop_op]
  · exact hf
  · apply_fun (symmMap ℂ _ _).symm using LinearEquiv.injective _
    simp_rw [symmMap_symm_comp, LinearEquiv.symm_apply_apply,
      symmMap_symm_apply, ← LinearMap.star_eq_adjoint,
      isSelfAdjoint_iff.mp (QuantumSet.modAut_isSelfAdjoint _),
      QuantumSet.modAut_real, AlgEquiv.linearMap_comp_eq_iff, starAlgebra.modAut_symm,
      neg_neg, LinearMap.comp_assoc, ← hg, ← starAlgebra.modAut_symm,
      ← AlgEquiv.comp_linearMap_eq_iff]

@[simp]
theorem LinearMap.op_real {K E F : Type*}
  [AddCommMonoid E] [StarAddMonoid E] [AddCommMonoid F] [StarAddMonoid F]
  [Semiring K] [Module K E] [Module K F] [InvolutiveStar K] [StarModule K E] [StarModule K F]
  (φ : E →ₗ[K] F) :
  φ.op.real = φ.real.op :=
rfl

lemma modAut_map_comp_Psi {A B : Type*} [ha : starAlgebra A] [hb : starAlgebra B]
    [hA : QuantumSet A] [hB : QuantumSet B] (t₁ r₁ t₂ r₂ : ℝ) :
  ((hb.modAut t₁).toLinearMap ⊗ₘ ((ha.modAut r₁).op.toLinearMap)) ∘ₗ (hA.Psi t₂ r₂).toLinearMap
    = (hA.Psi (t₁ + t₂) (-r₁ + r₂)).toLinearMap :=
by
  apply LinearMap.ext_of_rank_one'
  intro _ _
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [linearMap_map_Psi_of_commute_modAut, AlgEquiv.op_toLinearMap,
    LinearMap.op_unop, symmMap_apply, LinearMap.rankOne_comp',
    LinearMap.comp_rankOne]
  · simp_rw [AlgEquiv.toLinearMap_apply, QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply,
      QuantumSet.modAut_real, AlgEquiv.toLinearMap_apply, QuantumSet.modAut_apply_modAut, add_comm]
  · ext
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      QuantumSet.modAut_apply_modAut, add_comm]
  · ext
    simp only [AlgEquiv.op_toLinearMap, LinearMap.op_unop,
      LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      QuantumSet.modAut_apply_modAut, add_comm]
lemma lTensor_modAut_comp_Psi {A B : Type*} [ha : starAlgebra A] [hb : starAlgebra B]
    [hA : QuantumSet A] [hB : QuantumSet B] (t₂ r₁ r₂ : ℝ) :
  (LinearMap.lTensor B (ha.modAut r₁).op.toLinearMap)
    ∘ₗ (hA.Psi t₂ r₂).toLinearMap
  = (hA.Psi t₂ (-r₁ + r₂)).toLinearMap :=
by
  nth_rw 2 [← zero_add t₂]
  rw [← modAut_map_comp_Psi, QuantumSet.modAut_zero]
  rfl
lemma rTensor_modAut_comp_Psi {A B : Type*} [ha : starAlgebra A] [hb : starAlgebra B]
    [hA : QuantumSet A] [hB : QuantumSet B] (t₁ t₂ r₂ : ℝ) :
  (LinearMap.rTensor Aᵐᵒᵖ (hb.modAut t₁).toLinearMap)
    ∘ₗ (hA.Psi t₂ r₂).toLinearMap
  = (hA.Psi (t₁ + t₂) r₂).toLinearMap :=
by
  nth_rw 2 [← zero_add r₂]
  rw [← neg_zero, ← modAut_map_comp_Psi, QuantumSet.modAut_zero]
  rfl

open scoped TensorProduct
variable {A B : Type*} [ha : starAlgebra A] [hb : starAlgebra B]
    [hA : QuantumSet A] [hB : QuantumSet B]

private noncomputable def rmulMapLmul_apply_Upsilon_apply_aux :
    (A →ₗ[ℂ] B) →ₗ[ℂ] ((A ⊗[ℂ] B) →ₗ[ℂ] (A ⊗[ℂ] B)) where
  toFun x :=
  { toFun := fun y => Upsilon (x •ₛ Upsilon.symm y)
    map_add' := fun _ _ => by simp only [LinearEquiv.trans_symm, map_add, LinearEquiv.trans_apply,
      LinearEquiv.TensorProduct.map_symm_apply, LinearEquiv.symm_symm, QuantumSet.Psi_symm_apply,
      schurMul_apply_apply, QuantumSet.Psi_apply, LinearEquiv.TensorProduct.map_apply]
    map_smul' := fun _ _ => by simp only [LinearEquiv.trans_symm, LinearMapClass.map_smul,
      LinearEquiv.trans_apply, LinearEquiv.TensorProduct.map_symm_apply, LinearEquiv.symm_symm,
      QuantumSet.Psi_symm_apply, schurMul_apply_apply, QuantumSet.Psi_apply,
      LinearEquiv.TensorProduct.map_apply, RingHom.id_apply] }
  map_add' _ _ := by
    simp_rw [map_add, LinearMap.add_apply, map_add]; rfl
  map_smul' _ _ := by
    simp_rw [map_smul, LinearMap.smul_apply, map_smul]; rfl

private lemma rmulMapLmul_apply_Upsilon_apply_aux_apply
  (x : A →ₗ[ℂ] B) (y : A ⊗[ℂ] B) :
  rmulMapLmul_apply_Upsilon_apply_aux x y = Upsilon (x •ₛ Upsilon.symm y) :=
rfl

theorem rmulMapLmul_apply_Upsilon_apply (x : A →ₗ[ℂ] B) (y : A ⊗[ℂ] B) :
  (rmulMapLmul (Upsilon x)) y = Upsilon (x •ₛ Upsilon.symm y) :=
by
  rw [← rmulMapLmul_apply_Upsilon_apply_aux_apply, ← LinearEquiv.coe_toLinearMap,
    ← LinearMap.comp_apply]
  revert y x
  simp_rw [← LinearMap.ext_iff]
  apply LinearMap.ext_of_rank_one'
  intro x y
  rw [TensorProduct.ext_iff']
  intro a b
  simp only [rmulMapLmul_apply_Upsilon_apply_aux_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, Upsilon_rankOne, Upsilon_symm_tmul,
    schurMul.apply_rankOne, rmulMapLmul_apply,
    TensorProduct.map_tmul, star_mul, map_mul,
    starAlgebra.modAut_star, QuantumSet.modAut_apply_modAut,
    add_neg_cancel, QuantumSet.modAut_zero, star_star]
  rfl


theorem QuantumSet.comm_op_modAut_map_comul_one_eq_Psi (r : ℝ) (f : A →ₗ[ℂ] B) :
  (TensorProduct.comm _ _ _)
  ((TensorProduct.map ((op ℂ).toLinearMap ∘ₗ (modAut r).toLinearMap) f) (Coalgebra.comul 1)) =
    Psi 0 (k A + 1 - r) f :=
by
  calc (TensorProduct.comm ℂ Aᵐᵒᵖ B)
        ((TensorProduct.map
        ((op ℂ).toLinearMap ∘ₗ (ha.modAut r).toLinearMap) f) (Coalgebra.comul 1 : A ⊗[ℂ] A))
      = (TensorProduct.comm ℂ Aᵐᵒᵖ B)
        ((TensorProduct.map ((op ℂ).toLinearMap ∘ₗ (modAut r).toLinearMap) (unop ℂ).toLinearMap)
        (tenSwap ℂ (Psi 0 (k A + 1) f))) := ?_
    _ = (TensorProduct.comm _ _ _)
        ((TensorProduct.map (op ℂ).toLinearMap (unop ℂ).toLinearMap)
        (tenSwap ℂ
        ((LinearMap.lTensor _ (modAut r).op.toLinearMap)
        (Psi 0 (k A + 1) f)))) := ?_
    _ = (TensorProduct.comm _ _ _)
      ((TensorProduct.map (op ℂ).toLinearMap (unop ℂ).toLinearMap)
      (tenSwap ℂ
      (Psi 0 (k A + 1 - r) f))) := ?_
    _ = Psi 0 (k A + 1 - r) f := ?_
  · rw [← tenSwap_lTensor_comul_one_eq_Psi, tenSwap_apply_tenSwap]
    simp_rw [LinearMap.lTensor, TensorProduct.map_apply_map_apply]
    simp only [LinearMap.comp_id, ← LinearMap.comp_assoc,
      unop_comp_op, LinearMap.one_comp]
  · congr 1
    simp_rw [AlgEquiv.op_toLinearMap, tenSwap_apply_lTensor,
      ← LinearMap.comp_apply,
      ← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply,
      ← LinearMap.comp_assoc, LinearMap.map_comp_rTensor]
  · simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply,
      lTensor_modAut_comp_Psi]
    ring_nf
  · suffices ∀ x,
    (TensorProduct.comm ℂ Aᵐᵒᵖ B) (((op ℂ).toLinearMap ⊗ₘ (unop ℂ).toLinearMap) (tenSwap ℂ x))
    = x by
      rw [this]
    intro x
    simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply]
    nth_rw 2 [← LinearMap.id_apply (R := ℂ) x]
    revert x
    rw [← LinearMap.ext_iff, TensorProduct.ext_iff']
    intro a b
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.id_coe,
      id_eq, tenSwap_apply, TensorProduct.map_tmul,
      TensorProduct.comm_tmul]
    rfl

open scoped TensorProduct

@[simp]
theorem AlgEquiv.symm_one {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (1 : A ≃ₐ[R] A).symm = 1 :=
rfl
theorem LinearMap.lTensor_eq {R M N P : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M]
  [Module R N] [Module R P] (f : N →ₗ[R] P) :
  lTensor M f = TensorProduct.map LinearMap.id f :=
rfl
theorem AlgEquiv.symm_op
  {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  (f : A ≃ₐ[R] B) :
  (AlgEquiv.op f).symm = AlgEquiv.op f.symm :=
rfl

alias QuantumSet.modAut_trans := starAlgebra.modAut_trans

variable {A B : Type*} [ha : starAlgebra A] [hb : starAlgebra B]
    [hA : QuantumSet A] [hB : QuantumSet B]
lemma isReal_iff_Psi (f : A →ₗ[ℂ] B) (t r : ℝ) :
  LinearMap.IsReal f ↔ star (hA.Psi t r f) = hA.Psi (-t) ((2 * hA.k) + 1 - r) f :=
by
  simp_rw [LinearMap.isReal_iff, ← Function.Injective.eq_iff (hA.Psi t r).injective,
    Psi.real_apply]
  nth_rw 1 [← Function.Injective.eq_iff
    (AlgEquiv.TensorProduct.map (hb.modAut (- (2 * t)))
      (AlgEquiv.op (ha.modAut (2 * r - 1)))).injective]
  simp_rw [← AlgEquiv.TensorProduct.map_toLinearMap, AlgEquiv.toLinearMap_apply,
    AlgEquiv.TensorProduct.map_map_toLinearMap, AlgEquiv.op_trans,
    QuantumSet.modAut_trans]
  simp only [add_neg_cancel, QuantumSet.modAut_zero]
  simp only [← LinearEquiv.coe_toLinearMap, ← AlgEquiv.toLinearMap_apply,
    ← LinearMap.comp_apply, AlgEquiv.TensorProduct.map_toLinearMap, modAut_map_comp_Psi,
    two_mul, neg_add, neg_sub, sub_add]
  ring_nf
  simp only [← AlgEquiv.TensorProduct.map_toLinearMap,
    AlgEquiv.toLinearMap_apply]
  rw [eq_comm, AlgEquiv.eq_apply_iff_symm_eq, AlgEquiv.TensorProduct.map_symm,
    AlgEquiv.symm_one, ← AlgEquiv.toLinearMap_apply,
    AlgEquiv.TensorProduct.map_toLinearMap, AlgEquiv.one_toLinearMap,
    Module.End.one_eq_id, ← LinearMap.lTensor_eq,
    AlgEquiv.symm_op, starAlgebra.modAut_symm]
  simp_rw [← LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [lTensor_modAut_comp_Psi, neg_neg, eq_comm, LinearEquiv.coe_toLinearMap]
  ring_nf


lemma isReal_iff_Psi_isSelfAdjoint (f : A →ₗ[ℂ] B) :
  LinearMap.IsReal f ↔ IsSelfAdjoint (hA.Psi 0 (hA.k + (1 / 2)) f) :=
by
  rw [_root_.IsSelfAdjoint, isReal_iff_Psi f 0 (hA.k + 1/2)]
  ring_nf

theorem real_Upsilon_toBimodule {f : A →ₗ[ℂ] B} (gns₁ : hA.k = 0)
  (gns₂ : hB.k = 0) :
  (Upsilon f.real).toIsBimoduleMap.1
    = LinearMap.adjoint
      (Upsilon f).toIsBimoduleMap.1 :=
by
  have : ∀ (a : B) (b : A),
    (Upsilon (rankOne ℂ a b).toLinearMap.real).toIsBimoduleMap.1
    = LinearMap.adjoint (Upsilon (rankOne ℂ a b).toLinearMap).toIsBimoduleMap.1 :=
  by
    intro a b
    simp_rw [Upsilon_rankOne, LinearEquiv.trans_apply, QuantumSet.Psi_apply,
      rankOne_real, QuantumSet.PsiToFun_apply,
      LinearEquiv.TensorProduct.map_apply,
      TensorProduct.toIsBimoduleMap_apply_coe,
      rmulMapLmul_apply, TensorProduct.map_adjoint,
      TensorProduct.comm_tmul, TensorProduct.map_tmul,
      LinearEquiv.lTensor_tmul, rmulMapLmul_apply,
      rmul_adjoint, QuantumSet.modAut_star, QuantumSet.modAut_apply_modAut,
      lmul_adjoint,]
    ring_nf
    simp only [star_star, LinearEquiv.coe_coe, unop_apply,
      MulOpposite.unop_op, starAlgebra.modAut_zero, AlgEquiv.one_apply, op_apply,
      MulOpposite.op_star, MulOpposite.unop_star, gns₁, gns₂, neg_zero]
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne f
  simp only [map_sum, LinearMap.real_sum, Submodule.coe_sum, this]


/-- A Schur projection is an idempotent real map for the Schur product. -/
class schurProjection (f : A →ₗ[ℂ] B) :
    Prop where
  /-- Schur idempotence. -/
  isIdempotentElem : f •ₛ f = f
  /-- Realness of the underlying linear map. -/
  isReal : LinearMap.IsReal f

theorem Coalgebra.comul_mul_of_gns (gns : k A = 0) (a b : A) :
  Coalgebra.comul (R := ℂ) (a * b) = ∑ i, (a * onb i) ⊗ₜ[ℂ] (star (onb i) * b) :=
by
  calc (Coalgebra.comul (R := ℂ) ∘ₗ LinearMap.mul' ℂ A) (a ⊗ₜ b)
    = (PhiMap (LinearMap.id : A →ₗ[ℂ] A)).1 (a ⊗ₜ b) :=
      by
        congr
        simp_rw [PhiMap_apply, TensorProduct.toIsBimoduleMap_apply_coe,
          rmulMapLmul_apply_Upsilon_eq, LinearMap.lTensor_id,
          LinearMap.rTensor_id, LinearMap.id_comp]
        exact (@FrobeniusAlgebra.lTensor_mul_comp_rTensor_comul_eq_comul_comp_mul _ _ _ _
          (QuantumSet.isFrobeniusAlgebra)).symm
  _ = rmulMapLmul (Upsilon (1 : A →ₗ[ℂ] A)) (a ⊗ₜ b) := rfl
  _ = LinearMap.adjoint (rmulMapLmul (Upsilon (1 : A →ₗ[ℂ] A))) (a ⊗ₜ b) :=
      by
        congr 1
        nth_rw 1 [← LinearMap.real_one]
        exact real_Upsilon_toBimodule gns gns
  _ = ∑ i,
    LinearMap.adjoint (TensorProduct.map (LinearMap.adjoint (rmul (onb i))) (lmul (onb i))) (a
    ⊗ₜ b) :=
      by
        rw [← LinearMap.sum_apply]
        congr 1
        rw [← rankOne.sum_orthonormalBasis_eq_id_lm onb]
        simp_rw [map_sum, Upsilon_rankOne, rmulMapLmul_apply, ← rmul_adjoint]
  _ = ∑ i, TensorProduct.map (rmul (onb i)) (LinearMap.adjoint (lmul (onb i))) (a ⊗ₜ b) :=
      by
        simp only [TensorProduct.map_adjoint, LinearMap.adjoint_adjoint]
  _ = ∑ i, (a * onb i) ⊗ₜ[ℂ] (star (onb i) * b) :=
      by
        simp_rw [lmul_adjoint, gns, neg_zero, QuantumSet.modAut_zero]
        rfl

open scoped InnerProductSpace
open Coalgebra in
theorem QuantumSet.counit_isReal {A : Type*} [starAlgebra A] [QuantumSet A] :
  LinearMap.IsReal (counit (R := ℂ) (A := A)) :=
by
  intro x
  calc counit (star x) = ⟪x, 1⟫_ℂ :=
      by simp only [QuantumSet.inner_eq_counit, map_one, mul_one]
    _ = star ⟪1, x⟫_ℂ := (inner_conj_symm _ _).symm
    _ = star (counit x) := by simp_rw [QuantumSet.inner_eq_counit']

theorem QuantumSet.innerOne_map_one_isReal_ofReal
  {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
  {f : A →ₗ[ℂ] B} (hf : LinearMap.IsReal f) :
    ⟪1, f 1⟫_ℂ = Complex.re ⟪1, f 1⟫_ℂ :=
by
  rw [eq_comm, ← Complex.conj_eq_iff_re]
  simp_rw [Coalgebra.inner_eq_counit']
  nth_rw 1 [← star_one]
  rw [hf, QuantumSet.counit_isReal]
  simp
/-- The star-algebra structure transported to the opposite algebra. -/
@[reducible]
noncomputable def starAlgebra.mulOpposite {A : Type*} [starAlgebra A] :
    starAlgebra Aᵐᵒᵖ where
  modAut r := (modAut (-r)).op
  modAut_trans _ _ := by simp [AlgEquiv.op_trans, add_comm]
  modAut_star _ x := by simp [← MulOpposite.op_star]
attribute [local instance] starAlgebra.mulOpposite
/-- The inner-product algebra structure transported to the opposite algebra. -/
@[reducible]
noncomputable def InnerProductAlgebra.mulOpposite {A :
    Type*} [starAlgebra A] [InnerProductAlgebra A] :
    InnerProductAlgebra (Aᵐᵒᵖ) where
  norm_smul_le c x := by
    change ‖c • x.unop‖ ≤ ‖c‖ * ‖x.unop‖
    exact InnerProductAlgebra.norm_smul_le c x.unop
  norm_sq_eq_inner x := by
    rw [MulOpposite.inner_eq]
    change ‖x.unop‖ ^ 2 = RCLike.re ⟪x.unop, x.unop⟫_ℂ
    exact InnerProductAlgebra.norm_sq_eq_inner x.unop
  dist_eq x y := by
    change dist x.unop y.unop = ‖-x.unop + y.unop‖
    exact InnerProductAlgebra.dist_eq x.unop y.unop
  conj_symm x y := by
    simp only [MulOpposite.inner_eq]
    exact InnerProductAlgebra.conj_symm x.unop y.unop
  add_left x y z := by
    simp only [MulOpposite.inner_eq, MulOpposite.unop_add]
    exact InnerProductAlgebra.add_left x.unop y.unop z.unop
  smul_left x y r := by
    simp only [MulOpposite.inner_eq, MulOpposite.unop_smul]
    exact InnerProductAlgebra.smul_left x.unop y.unop r
attribute [local instance] InnerProductAlgebra.mulOpposite
noncomputable instance QuantumSet.mulOpposite {A : Type*} [starAlgebra A] [QuantumSet A]
  [kms : Fact (k A = -(1 / 2))] :
    QuantumSet Aᵐᵒᵖ where
  modAut_isSymmetric r x y := by
    simp only [MulOpposite.inner_eq]
    exact QuantumSet.modAut_isSymmetric (-r) x.unop y.unop
  k := k A
  inner_star_left _ _ _ := by
    simp only [MulOpposite.inner_eq, modAut, MulOpposite.unop_mul, MulOpposite.unop_star,
      AlgEquiv.op_apply_apply, MulOpposite.unop_op]
    rw [inner_conj_left]
    simp [kms.out]
    norm_num
  inner_conj_left _ _ _ := by
    simp only [MulOpposite.inner_eq, modAut, MulOpposite.unop_mul, MulOpposite.unop_star,
      AlgEquiv.op_apply_apply, MulOpposite.unop_op]
    rw [inner_star_left]
    simp [kms.out]
    norm_num
  n := n A
  nIsFintype := nIsFintype
  nIsDecidableEq := nIsDecidableEq
  onb := onb.mulOpposite
attribute [local instance] QuantumSet.mulOpposite
noncomputable instance CoalgebraStruct.mulOpposite {A :
    Type*} [Semiring A] [Algebra ℂ A] [CoalgebraStruct ℂ A] :
    CoalgebraStruct ℂ Aᵐᵒᵖ where
  comul := (Algebra.TensorProduct.opAlgEquiv ℂ ℂ A A).symm.toLinearMap ∘ₗ Coalgebra.comul.op
  counit := (MulOpposite.opLinearEquiv ℂ).symm.toLinearMap ∘ₗ Coalgebra.counit.op
theorem Coalgebra.counit_mulOpposite_eq {A :
    Type*} [Semiring A] [Algebra ℂ A] [CoalgebraStruct ℂ A] (a : Aᵐᵒᵖ) :
  (Coalgebra.counit (R := ℂ) (A := Aᵐᵒᵖ)) a = Coalgebra.counit a.unop :=
rfl

theorem QuantumSet.counit_isFaithful {A : Type*} [starAlgebra A] [QuantumSet A] :
  Module.Dual.IsFaithful (Coalgebra.counit (R := ℂ) (A := A)) :=
by
  intro x
  simp only [← QuantumSet.inner_eq_counit']
  rw [← inner_conj_symm, QuantumSet.inner_star_left, star_star, mul_one, ← add_halves (- k A),
    ← modAut_apply_modAut, ← modAut_isSymmetric, inner_conj_symm, inner_self_eq_zero,
    map_eq_zero_iff _ (AlgEquiv.injective _)]

/-- Opposite-algebra version of a module dual functional. -/
def Module.Dual.op {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  (f : Module.Dual R A) :
  Module.Dual R Aᵐᵒᵖ :=
(unop R).toLinearMap ∘ₗ LinearMap.op f
theorem Module.Dual.op_apply {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  (f : Module.Dual R A) (x : Aᵐᵒᵖ) :
    Module.Dual.op f x = f x.unop :=
rfl

theorem Coalgebra.counit_moduleDualOp_eq {A : Type*} [Semiring A] [Algebra ℂ A]
  [CoalgebraStruct ℂ A] :
    Module.Dual.op (Coalgebra.counit (R := ℂ) (A := A)) = counit (R := ℂ) (A := Aᵐᵒᵖ) :=
rfl

/-- Star-ring structure on the opposite of a star ring. -/
@[reducible]
def MulOpposite.starRing {A : Type*} [NonUnitalNonAssocSemiring A] [hA : StarRing A] :
    StarRing Aᵐᵒᵖ where
  star_add _ _ := star_add _ _

attribute [local instance] MulOpposite.starRing

theorem Module.Dual.op_isFaithful_iff {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalSemiring A]
  [StarRing A] [Module 𝕜 A] (φ : Module.Dual 𝕜 A) :
    Module.Dual.IsFaithful φ ↔ Module.Dual.IsFaithful (Module.Dual.op φ) :=
by
  simp only [Module.Dual.IsFaithful, Module.Dual.op_apply, MulOpposite.unop_mul,
    MulOpposite.unop_star]
  refine ⟨fun h a => ?_, fun h a => ?_⟩
  · simpa [star_star, MulOpposite.unop_eq_zero_iff] using h (star a.unop)
  · simpa [star_star, MulOpposite.op_eq_zero_iff] using h (star (MulOpposite.op a))

theorem QuantumSet.counit_op_isFaithful {A : Type*} [starAlgebra A] [QuantumSet A] :
  Module.Dual.IsFaithful (Coalgebra.counit (R := ℂ) (A := Aᵐᵒᵖ)) :=
(Module.Dual.op_isFaithful_iff _).mp QuantumSet.counit_isFaithful

noncomputable instance QuantumSet.tensorOpSelf {A :
    Type*} [starAlgebra A] [QuantumSet A] [kms : Fact (k A = -(1 / 2))] :
  QuantumSet (A ⊗[ℂ] Aᵐᵒᵖ) :=
QuantumSet.tensorProduct (h := Fact.mk rfl)

theorem MulOpposite.norm_eq {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  (x : Hᵐᵒᵖ) : ‖x‖ = ‖x.unop‖ :=
rfl

theorem Coalgebra.comul_mul (a b : A) :
  Coalgebra.comul (R := ℂ) (a * b)
    = ∑ i, (a * (modAut ((k A / 2)) (hA.onb i)))
        ⊗ₜ[ℂ] (star (modAut ((k A / 2)) (hA.onb i)) * b) :=
by
  rw [QuantumSet.comul_of_subset 0]
  letI := hA.instSubset 0
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul]
  rw [Coalgebra.comul_mul_of_gns rfl]
  simp only [map_sum]
  congr
  ext i
  rw [QuantumSet.toSubset_onb 0]
  simp only [zero_div, neg_zero, add_zero]
  rw [← QuantumSet.toSubsetAlgEquiv_isReal]
  simp only [← map_mul, TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply,
    AlgEquiv.symm_apply_apply]

open scoped ComplexOrder
theorem schurProjection.isPosMap [PartialOrder A] [PartialOrder B]
  [StarOrderedRing B]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b)
  {f : A →ₗ[ℂ] B}
  (hf : schurProjection f) :
  LinearMap.IsPosMap f :=
by
  revert hf
  rintro ⟨h1, h2⟩ x hx
  obtain ⟨a, b, rfl⟩ := h₁.mp hx
  rw [← h1, schurMul_apply_apply]
  simp_rw [LinearMap.comp_apply]
  rw [Coalgebra.comul_mul]
  simp_rw [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply]
  nth_rw 2 [← star_star a]
  simp_rw [← star_mul, h2 _]
  exact Finset.sum_nonneg (fun _ _ => mul_star_self_nonneg _)

theorem schurIdempotent.isSchurProjection_iff_isPosMap
  [PartialOrder A] [PartialOrder B]
  [StarOrderedRing A] [StarOrderedRing B]
  (h₁ : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ (b : A), a = star b * b)
  (hh : isEquivToPiMat A) {f : A →ₗ[ℂ] B} (hf : f •ₛ f = f) :
  schurProjection f ↔ LinearMap.IsPosMap f :=
⟨fun h => h.isPosMap h₁,
 fun h => ⟨hf, isReal_of_isPosMap_of_starAlgEquiv_piMat hh h⟩⟩

/-- A quantum graph is a Schur-idempotent endomorphism of a quantum set. -/
class QuantumGraph (A : Type*) [starAlgebra A] [hA : QuantumSet A] [CoalgebraStruct ℂ A]
    (f : A →ₗ[ℂ] A) : Prop where
  /-- Schur idempotence of the adjacency map. -/
  isIdempotentElem : f •ₛ f = f

theorem quantumGraph_iff {A : Type*} [starAlgebra A] [QuantumSet A] [CoalgebraStruct ℂ A]
    {f : A →ₗ[ℂ] A} :
  QuantumGraph A f ↔ f •ₛ f = f :=
⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/-- Predicate asserting that a quantum graph is real. -/
class QuantumGraph.IsReal {A : Type*} [starAlgebra A] [hA : QuantumSet A] [CoalgebraStruct ℂ A]
    {f : A →ₗ[ℂ] A} (h : QuantumGraph A f) : Prop where
  /-- Realness of the adjacency map. -/
  isReal : LinearMap.IsReal f

/-- A real quantum graph bundles Schur idempotence and realness. -/
class QuantumGraph.Real (A : Type*) [starAlgebra A] [hA : QuantumSet A] [CoalgebraStruct ℂ A]
    (f : A →ₗ[ℂ] A) : Prop where
  /-- Schur idempotence of the adjacency map. -/
  isIdempotentElem : f •ₛ f = f
  /-- Realness of the adjacency map. -/
  isReal : LinearMap.IsReal f

theorem QuantumGraph.real_iff {A : Type*} [starAlgebra A] [QuantumSet A] [CoalgebraStruct ℂ A]
    {f : A →ₗ[ℂ] A} :
  QuantumGraph.Real A f ↔ f •ₛ f = f ∧ LinearMap.IsReal f :=
⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem quantumGraphReal_iff_schurProjection {f : A →ₗ[ℂ] A} :
  QuantumGraph.Real A f ↔ schurProjection f :=
⟨fun h => ⟨h.isIdempotentElem, h.isReal⟩,
 fun h => ⟨h.isIdempotentElem, h.isReal⟩⟩

theorem QuantumGraph.Real.toQuantumGraph {f : A →ₗ[ℂ] A} (h : QuantumGraph.Real A f) :
  QuantumGraph A f :=
⟨h.isIdempotentElem⟩

theorem quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint {f : A →ₗ[ℂ] A} :
  QuantumGraph.Real A f ↔
  (IsIdempotentElem (hA.Psi 0 (hA.k + 1/2) f) ∧
    IsSelfAdjoint (hA.Psi 0 (hA.k + 1/2) f)) :=
by
  rw [← schurIdempotent_iff_Psi_isIdempotentElem, ← isReal_iff_Psi_isSelfAdjoint]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem schurMul_Upsilon_toBimodule {f g : A →ₗ[ℂ] B} :
  (Upsilon (f •ₛ g)).toIsBimoduleMap.1
    = (Upsilon f).toIsBimoduleMap.1 * (Upsilon g).toIsBimoduleMap.1 :=
by
  have : ∀ (a c : B) (b d : A),
    (Upsilon ((rankOne ℂ a b).toLinearMap •ₛ (rankOne ℂ c d).toLinearMap)).toIsBimoduleMap.1
    = (Upsilon (rankOne ℂ a b).toLinearMap).toIsBimoduleMap.1
      * (Upsilon (rankOne ℂ c d).toLinearMap).toIsBimoduleMap.1 :=
  by
    intro a c b d
    simp_rw [schurMul.apply_rankOne, Upsilon_rankOne, TensorProduct.toIsBimoduleMap_apply_coe,
      rmulMapLmul_apply, ← TensorProduct.map_mul,
      rmul_eq_mul, Module.End.mul_eq_comp, ← LinearMap.mulRight_mul,
      lmul_eq_mul, ← LinearMap.mulLeft_mul, ← map_mul, ← star_mul]
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne f
  obtain ⟨γ, δ, rfl⟩ := LinearMap.exists_sum_rankOne g
  simp only [map_sum, LinearMap.sum_apply, Finset.sum_mul,
    Finset.mul_sum, Submodule.coe_sum, this]

theorem quantumGraphReal_iff_Upsilon_toBimodule_orthogonalProjection
  {f : A →ₗ[ℂ] A} (gns : hA.k = 0) :
  QuantumGraph.Real A f ↔
  ContinuousLinearMap.IsOrthogonalProjection
  (LinearMap.toContinuousLinearMap
    (Upsilon f).toIsBimoduleMap.1) :=
by
  rw [LinearMap.isOrthogonalProjection_iff,
    IsIdempotentElem, ← schurMul_Upsilon_toBimodule,
    isSelfAdjoint_iff, LinearMap.star_eq_adjoint,
    ← real_Upsilon_toBimodule gns gns]
  simp_rw [Subtype.val_inj, (LinearEquiv.injective _).eq_iff,
    ← LinearMap.isReal_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

section

theorem StarAlgEquiv.toAlgEquiv_toAlgHom_toLinearMap
  {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Star A] [Star B] (f : A ≃⋆ₐ[R] B) :
    f.toAlgEquiv.toAlgHom.toLinearMap = f.toLinearMap :=
rfl

attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass

/-- Real quantum graphs are preserved by isometric star-algebra equivalence conjugation. -/
theorem QuantumGraph.Real_conj_starAlgEquiv
  {A B : Type*} [starAlgebra A] [starAlgebra B]
  [QuantumSet A] [QuantumSet B]
  {x : A →ₗ[ℂ] A} (hx : QuantumGraph.Real A x)
  {f : A ≃⋆ₐ[ℂ] B} (hf : Isometry f) :
  QuantumGraph.Real _ (f.toLinearMap ∘ₗ x ∘ₗ (LinearMap.adjoint f.toLinearMap)) :=
by
  constructor
  · rw [← StarAlgEquiv.toAlgEquiv_toAlgHom_toLinearMap,
      QuantumSet.schurMul_algHom_comp_algHom_adjoint, hx.1]
  · suffices LinearMap.adjoint f.toLinearMap = f.symm.toLinearMap from ?_
    · simp_rw [this]
      change LinearMap.IsReal
        (f.toAlgEquiv.toLinearMap ∘ₗ x ∘ₗ f.symm.toAlgEquiv.toLinearMap)
      exact (LinearMap.real_starAlgEquiv_conj_iff x f).mpr hx.isReal
    · exact QuantumSet.starAlgEquiv_isometry_iff_adjoint_eq_symm.mp hf

theorem Submodule.eq_iff_orthogonalProjection_eq
  {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {U : Submodule ℂ E}
  {V : Submodule ℂ E} [CompleteSpace E] [CompleteSpace ↥U] [CompleteSpace ↥V] :
  U = V ↔ orthogonalProjection' U = orthogonalProjection' V :=
by simp_rw [le_antisymm_iff, orthogonalProjection.is_le_iff_subset]

open scoped FiniteDimensional in
theorem Submodule.adjoint_subtype {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Submodule ℂ E} :
  LinearMap.adjoint U.subtype = (orthogonalProjection U).toLinearMap :=
by
  rw [← Submodule.adjoint_subtypeL]
  rfl

theorem Submodule.map_orthogonalProjection_self {E :
    Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Submodule ℂ E} :
  Submodule.map (orthogonalProjection U).toLinearMap U = ⊤ :=
by
  ext x
  simp only [mem_map, ContinuousLinearMap.coe_coe, mem_top, iff_true]
  use x
  simp only [SetLike.coe_mem, orthogonalProjection_mem_subspace_eq_self, and_self]

theorem orthogonalProjection_submoduleMap {E E' :
    Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  {U : Submodule ℂ E}
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] (f : E ≃ₗᵢ[ℂ] E') :
  (orthogonalProjection' (Submodule.map (f.toLinearEquiv : E →ₗ[ℂ] E') U)).toLinearMap
    = f.toLinearMap
      ∘ₗ (orthogonalProjection' U).toLinearMap
      ∘ₗ f.symm.toLinearMap :=
by
  ext x
  exact Submodule.starProjection_map_apply f U x

theorem orthogonalProjection_submoduleMap_isometry {E E' :
    Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  {U : Submodule ℂ E}
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ E']
  {f : E ≃ₗ[ℂ] E'} (hf : Isometry f) :
  (orthogonalProjection' (Submodule.map f.toLinearMap U)).toLinearMap
    = f.toLinearMap
      ∘ₗ (orthogonalProjection' U).toLinearMap
      ∘ₗ f.symm.toLinearMap :=
by
  let f' : E ≃ₗᵢ[ℂ] E' := ⟨f, (isometry_iff_norm _).mp hf⟩
  simpa using orthogonalProjection_submoduleMap f'

instance
   StarAlgEquivClass.instLinearMapClass
  {R A B : Type*} [Semiring R] [AddCommMonoid A] [AddCommMonoid B]
  [Mul A] [Mul B] [Module R A] [Module R B] [Star A] [Star B]
  {F : Type*} [EquivLike F A B] [NonUnitalAlgEquivClass F R A B]
  [StarHomClass F A B] :
  LinearMapClass F R A B :=
SemilinearMapClass.mk

theorem orthogonalProjection_submoduleMap_isometry_starAlgEquiv
  {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  {U : Submodule ℂ E}
  [Mul E] [Mul E'] [Star E] [Star E']
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ E']
  {f : E ≃⋆ₐ[ℂ] E'} (hf : Isometry f) :
  (orthogonalProjection' (Submodule.map f.toLinearMap U)).toLinearMap
    = f.toLinearMap
      ∘ₗ (orthogonalProjection' U).toLinearMap
      ∘ₗ f.symm.toLinearMap :=
by
  have hf' : Isometry f.toLinearEquiv := hf
  calc (orthogonalProjection' (Submodule.map f.toLinearMap U)).toLinearMap
      = (orthogonalProjection' (Submodule.map f.toLinearEquiv.toLinearMap U)).toLinearMap := rfl
    _ = f.toLinearEquiv.toLinearMap
      ∘ₗ (orthogonalProjection' U).toLinearMap
      ∘ₗ f.toLinearEquiv.symm.toLinearMap := orthogonalProjection_submoduleMap_isometry hf'

theorem orthogonalProjection_submoduleMap' {E E' :
    Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  {U : Submodule ℂ E}
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] (f : E' ≃ₗᵢ[ℂ] E) :
  (orthogonalProjection' (Submodule.map (f.symm.toLinearEquiv : E →ₗ[ℂ] E') U)).toLinearMap
    = f.symm.toLinearMap
      ∘ₗ (orthogonalProjection' U).toLinearMap
      ∘ₗ f.toLinearMap :=
orthogonalProjection_submoduleMap f.symm

end
section

/-- The submodule whose orthogonal projection corresponds to `Upsilon f`. -/
noncomputable def QuantumGraph.Real.upsilonSubmodule
  {f : A →ₗ[ℂ] A} (gns : hA.k = 0)
  (hf : QuantumGraph.Real A f) :
  Submodule ℂ (A ⊗[ℂ] A) :=
Classical.choose
    (orthogonal_projection_iff.mpr
    (And.comm.mp
    (ContinuousLinearMap.isOrthogonalProjection_iff'.mp
      ((quantumGraphReal_iff_Upsilon_toBimodule_orthogonalProjection gns).mp hf))))

instance QuantumGraph.Real.upsilonSubmodule.hasOrthogonalProjection {f : A →ₗ[ℂ] A}
    (gns : hA.k = 0) (hf : QuantumGraph.Real A f) :
    (upsilonSubmodule gns hf).HasOrthogonalProjection := by
  letI : CompleteSpace (upsilonSubmodule gns hf) :=
    FiniteDimensional.complete ℂ (upsilonSubmodule gns hf)
  infer_instance

theorem QuantumGraph.Real.upsilonOrthogonalProjection {f : A →ₗ[ℂ] A}
  (gns : hA.k = 0)
  (hf : QuantumGraph.Real A f) :
  orthogonalProjection' (upsilonSubmodule gns hf)
    = LinearMap.toContinuousLinearMap
      ((TensorProduct.toIsBimoduleMap (Upsilon f)).1) :=
by
  unfold upsilonSubmodule
  exact Classical.choose_spec
    (orthogonal_projection_iff.mpr
    (And.comm.mp
    (ContinuousLinearMap.isOrthogonalProjection_iff'.mp
      ((quantumGraphReal_iff_Upsilon_toBimodule_orthogonalProjection gns).mp hf))))

theorem QuantumGraph.Real.upsilonOrthogonalProjection' {f : A →ₗ[ℂ] A}
  (gns : hA.k = 0)
  (hf : QuantumGraph.Real A f) :
  (orthogonalProjection' (upsilonSubmodule gns hf)).toLinearMap
    = rmulMapLmul ((orthogonalProjection' (upsilonSubmodule gns hf)).toLinearMap 1) :=
by
  symm
  rw [← LinearMap.isBimoduleMap_iff', ← LinearMap.mem_isBimoduleMaps_iff]
  rw [upsilonOrthogonalProjection gns hf, LinearMap.coe_toContinuousLinearMap]
  exact Submodule.coe_mem (TensorProduct.toIsBimoduleMap (Upsilon f))

/-- A canonical orthonormal basis of `upsilonSubmodule`. -/
noncomputable def QuantumGraph.Real.upsilonOrthonormalBasis {f : A →ₗ[ℂ] A}
  (gns : hA.k = 0) (hf : QuantumGraph.Real A f) :
  OrthonormalBasis (Fin (Module.finrank ℂ (upsilonSubmodule gns hf))) ℂ (upsilonSubmodule gns hf) :=
stdOrthonormalBasis ℂ (upsilonSubmodule gns hf)

theorem OrthonormalBasis.tensorProduct_toBasis {𝕜 E F : Type*}
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
  (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
  (b₁.tensorProduct b₂).toBasis = b₁.toBasis.tensorProduct b₂.toBasis :=
by aesop

theorem TensorProduct.of_orthonormalBasis_eq_span
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (x : TensorProduct 𝕜 E F)
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (b₁ : OrthonormalBasis ι₁ 𝕜 E)
  (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
  letI := Module.Basis.finiteDimensional_of_finite b₁.toBasis
  letI := Module.Basis.finiteDimensional_of_finite b₂.toBasis
  x = ∑ i : ι₁, ∑ j : ι₂, ((b₁.tensorProduct b₂).repr x) (i, j) • b₁ i ⊗ₜ[𝕜] b₂ j :=
by
  nth_rw 1 [TensorProduct.of_basis_eq_span x b₁.toBasis b₂.toBasis]
  rfl

/-- Coordinates of a tensor as a product-indexed family of scalar-weighted basis pairs. -/
noncomputable def TensorProduct.ofOrthonormalBasisProd
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (x : TensorProduct 𝕜 E F)
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (b₁ : OrthonormalBasis ι₁ 𝕜 E)
  (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
  letI := Module.Basis.finiteDimensional_of_finite b₁.toBasis
  letI := Module.Basis.finiteDimensional_of_finite b₂.toBasis
  (ι₁ × ι₂) → (E × F) :=
letI := Module.Basis.finiteDimensional_of_finite b₁.toBasis
letI := Module.Basis.finiteDimensional_of_finite b₂.toBasis
fun (i,j) => ((((b₁.tensorProduct b₂).repr x) (i,j)) • b₁ i, b₂ j)

@[simp]
theorem TensorProduct.of_othonormalBasis_prod_eq
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (x : E ⊗[𝕜] F)
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
  (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
  ∑ i : ι₁ × ι₂,
    (x.ofOrthonormalBasisProd b₁ b₂ i).1 ⊗ₜ[𝕜] (x.ofOrthonormalBasisProd b₁ b₂ i).2
      = x :=
by
  nth_rw 3 [TensorProduct.of_orthonormalBasis_eq_span x b₁ b₂]
  simp_rw [smul_tmul', Finset.sum_product_univ]
  rfl
@[simp]
theorem TensorProduct.of_othonormalBasis_prod_eq'
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (x : E ⊗[𝕜] F)
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
  (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
  ∑ i : ι₁ × ι₂,
    (x.ofOrthonormalBasisProd b₁ b₂ i).1 ⊗ₜ[𝕜] b₂ i.2
      = x :=
by
  nth_rw 2 [TensorProduct.of_orthonormalBasis_eq_span x b₁ b₂]
  simp_rw [smul_tmul', Finset.sum_product_univ]
  rfl

open scoped InnerProductSpace
theorem
  QuantumGraph.Real.upsilon_eq {f : A →ₗ[ℂ] A}
    (hf : QuantumGraph.Real A f) (gns : hA.k = 0) :
  let u := QuantumGraph.Real.upsilonOrthonormalBasis gns hf
  let b := hA.onb
  let a := fun (x : A ⊗[ℂ] A) =>
    fun i : (n A) × (n A) => (x.ofOrthonormalBasisProd b b i).1
  f = ∑ i, ∑ j, ⟪(u i : A ⊗[ℂ] A), 1⟫_ℂ
    • rankOne ℂ (b j.2) (modAut (-1) (star (a (u i : A ⊗[ℂ] A) j))) :=
by
  intro u b a
  symm
  have := Upsilon_symm_tmul (A := A) (B:=A)
  simp only [gns, neg_zero, zero_sub] at this
  simp_rw [ContinuousLinearMap.coe_sum, ContinuousLinearMap.coe_smul,
    ← this, ← map_smul]
  simp_rw [← map_sum, ← Finset.smul_sum, a, TensorProduct.of_othonormalBasis_prod_eq',
    ← rankOne_apply (𝕜 := ℂ) (1 : A ⊗[ℂ] A),
    ← ContinuousLinearMap.sum_apply,
    ← OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne]
  rw [upsilonOrthogonalProjection]
  simp_rw [TensorProduct.toIsBimoduleMap_apply_coe,
    LinearMap.coe_toContinuousLinearMap',
    rmulMapLmul_apply_one, LinearEquiv.symm_apply_apply]

theorem
  QuantumGraph.Real.upsilon_eq' {f : A →ₗ[ℂ] A}
    (hf : QuantumGraph.Real A f) (gns : hA.k = 0) :
  let u := QuantumGraph.Real.upsilonOrthonormalBasis gns hf
  let b := hA.onb
  let a := fun (x : A ⊗[ℂ] A) =>
    fun i : (n A) × (n A) => (x.ofOrthonormalBasisProd b b i).1
  f = ∑ i, ∑ j, ⟪1, (u i : A ⊗[ℂ] A)⟫_ℂ
    • rankOne ℂ (star (b j.2)) (a (u i : A ⊗[ℂ] A) j) :=
by
  intro u b a
  nth_rw 1 [← (LinearMap.isReal_iff _).mp hf.isReal]
  nth_rw 1 [QuantumGraph.Real.upsilon_eq hf gns]
  simp only [ContinuousLinearMap.coe_sum, ContinuousLinearMap.coe_smul,
    LinearMap.real_sum, LinearMap.real_smul, rankOne_real, gns, mul_zero, neg_zero,
    zero_sub, QuantumSet.modAut_star, QuantumSet.modAut_apply_modAut,
    add_neg_cancel, QuantumSet.modAut_zero, star_star, AlgEquiv.one_apply,
    TensorProduct.inner_conj_symm]
  rfl

/-- Linear map sending a tensor to its first-coordinate orthonormal-basis expansion data. -/
noncomputable def TensorProduct.ofOrthonormalBasisProd₁Lm
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (b₁ : OrthonormalBasis ι₁ 𝕜 E)
  (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    (E ⊗[𝕜] F) →ₗ[𝕜] ((ι₁ × ι₂) → E) :=
by
  letI := Module.Basis.finiteDimensional_of_finite b₁.toBasis
  letI := Module.Basis.finiteDimensional_of_finite b₂.toBasis
  exact
  { toFun := fun x i => (x.ofOrthonormalBasisProd b₁ b₂ i).1
    map_add' := fun _ _ => by simp [ofOrthonormalBasisProd, add_smul]; rfl
    map_smul' := fun _ _ => by ext; simp [ofOrthonormalBasisProd, smul_smul] }

lemma TensorProduct.ofOrthonormalBasisProd₁Lm_eq
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (b₁ : OrthonormalBasis ι₁ 𝕜 E)
  (b₂ : OrthonormalBasis ι₂ 𝕜 F) (x : E ⊗[𝕜] F) (i : ι₁ × ι₂) :
  (TensorProduct.ofOrthonormalBasisProd₁Lm b₁ b₂) x i
    = (TensorProduct.ofOrthonormalBasisProd x b₁ b₂ i).1 :=
rfl

theorem
  QuantumGraph.Real.upsilon_eq'' {f : A →ₗ[ℂ] A}
    (hf : QuantumGraph.Real A f) (gns : hA.k = 0) :
  let P := orthogonalProjection' (upsilonSubmodule gns hf);
  let a := fun x i => (TensorProduct.ofOrthonormalBasisProd x onb onb i).1
  f = ∑ j : n A × n A, rankOne ℂ (star (onb j.2)) (a (P 1 : A ⊗[ℂ] A) j) :=
by
  intro P a
  nth_rw 1 [QuantumGraph.Real.upsilon_eq' hf gns]
  let u := QuantumGraph.Real.upsilonOrthonormalBasis gns hf
  simp_rw [P, u.orthogonalProjection'_eq_sum_rankOne]
  simp only [ContinuousLinearMap.sum_apply, a, ← TensorProduct.ofOrthonormalBasisProd₁Lm_eq,
    map_sum, rankOne_apply, map_smul,
    Finset.sum_apply, Pi.smul_apply, map_smulₛₗ, inner_conj_symm]
  rw [Finset.sum_comm]

theorem QuantumSet.starAlgEquiv_commutes_with_modAut_of_isometry''
  {A B : Type*} [hb : starAlgebra B] [ha : starAlgebra A]
  [hA : QuantumSet A] [hB : QuantumSet B] {f : A ≃⋆ₐ[ℂ] B}
  (hf : Isometry f) :
  f.toLinearMap ∘ₗ (modAut (-(2 * k A + 1))).toLinearMap
    = (modAut (-(2 * k B + 1))).toLinearMap ∘ₗ f.toLinearMap :=
by
  rw [← starAlgebra.modAut_symm, AlgEquiv.linearMap_comp_eq_iff, AlgEquiv.symm_symm,
    LinearMap.comp_assoc, starAlgEquiv_commutes_with_modAut_of_isometry' hf,
    ← LinearMap.comp_assoc, ← starAlgebra.modAut_symm]
  simp only [AlgEquiv.coe_comp, AlgEquiv.self_trans_symm]
  rfl

theorem LinearMap.tensorProduct_map_isometry_of {𝕜 A B C D : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C] [NormedAddCommGroup D]
  [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [InnerProductSpace 𝕜 D]
  [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] [FiniteDimensional 𝕜 D]
  {f : A →ₗ[𝕜] B} (hf : Isometry f) {g : C →ₗ[𝕜] D} (hg : Isometry g) :
  Isometry (f ⊗ₘ g) :=
by
  rw [isometry_iff_inner] at hf hg
  rw [isometry_iff_norm]
  intro x
  simp_rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜)]
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  simp only [map_sum, sum_inner, inner_sum, TensorProduct.map_tmul]
  simp only [TensorProduct.inner_tmul, hf, hg, RCLike.mul_re,
    Finset.sum_sub_distrib]

theorem StarAlgEquiv.tensorProduct_map_isometry_of
  {A B C D : Type*} [starAlgebra A] [starAlgebra B] [starAlgebra C] [starAlgebra D]
  [QuantumSet A] [QuantumSet B] [QuantumSet C] [QuantumSet D]
  {f : A ≃⋆ₐ[ℂ] B} (hf : Isometry f) {g : C ≃⋆ₐ[ℂ] D}
  (hg : Isometry g) :
  Isometry (StarAlgEquiv.TensorProduct.map f g) :=
LinearMap.tensorProduct_map_isometry_of hf hg

/-- Tensor product of two linear isometry equivalences. -/
@[simps!]
noncomputable def LinearIsometryEquiv.TensorProduct.map {𝕜 A B C D : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C] [NormedAddCommGroup D]
  [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [InnerProductSpace 𝕜 D]
  [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] [FiniteDimensional 𝕜 D]
  (f : A ≃ₗᵢ[𝕜] B) (g : C ≃ₗᵢ[𝕜] D) :
    A ⊗[𝕜] C ≃ₗᵢ[𝕜] B ⊗[𝕜] D where
  toLinearEquiv := LinearEquiv.TensorProduct.map f.toLinearEquiv g.toLinearEquiv
  norm_map' := by
    rw [← isometry_iff_norm]
    exact LinearMap.tensorProduct_map_isometry_of f.isometry g.isometry

theorem LinearIsometryEquiv.TensorProduct.map_tmul
  {𝕜 A B C D : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C] [NormedAddCommGroup D]
  [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C] [InnerProductSpace 𝕜 D]
  [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] [FiniteDimensional 𝕜 D]
  (f : A ≃ₗᵢ[𝕜] B) (g : C ≃ₗᵢ[𝕜] D) (x : A) (y : C) :
  (LinearIsometryEquiv.TensorProduct.map f g) (x ⊗ₜ y) = f x ⊗ₜ g y :=
rfl

theorem oneHom_isometry_inner_one_right
  {𝕜 A B : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedAddCommGroup B]
  [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B]
  [One A] [One B]
  {F : Type*} [FunLike F A B] [LinearMapClass F 𝕜 A B]
  [OneHomClass F A B] {f : F}
  (hf : Isometry f) (x : A) :
  ⟪f x, 1⟫_𝕜 = ⟪x, 1⟫_𝕜 :=
by
  rw [← map_one f]
  exact (isometry_iff_inner _).mp hf _ _

theorem
  QuantumGraph.Real.upsilon_starAlgEquiv_conj_eq
  {f : A →ₗ[ℂ] A} (gns : hA.k = 0) (gns₂ : hB.k = 0)
  (hf : QuantumGraph.Real A f)
  {φ : A ≃⋆ₐ[ℂ] B} (hφ : Isometry φ) :
  let u := QuantumGraph.Real.upsilonOrthonormalBasis gns hf
  let b := hA.onb
  let a := fun (x : A ⊗[ℂ] A) =>
    fun i : (n A) × (n A) => (x.ofOrthonormalBasisProd b b i).1
  φ.toLinearMap ∘ₗ f ∘ₗ LinearMap.adjoint φ.toLinearMap
    = ∑ i, ∑ j, ∑ p,
      (⟪φ (a (u i : A ⊗[ℂ] A) p), 1⟫_ℂ
        * ⟪φ (b p.2), 1⟫_ℂ)
      • rankOne ℂ (φ (b j.2)) (modAut (-1) (star (φ (a (u i : A ⊗[ℂ] A) j)))) :=
by
  intro u b a
  nth_rw 1 [hf.upsilon_eq gns]
  simp only [ContinuousLinearMap.coe_sum,
    ContinuousLinearMap.coe_smul,
    LinearMap.comp_sum, LinearMap.sum_comp,
    LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.comp_rankOne, LinearMap.rankOne_comp']
  simp only [StarAlgEquiv.toLinearMap_apply]
  have := QuantumSet.starAlgEquiv_commutes_with_modAut_of_isometry'' hφ
  simp only [gns, gns₂, mul_zero, zero_add, LinearMap.ext_iff,
    LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    StarAlgEquiv.toLinearMap_apply] at this
  simp_rw [this, map_star, oneHom_isometry_inner_one_right hφ,
    ← TensorProduct.inner_tmul, ← Finset.sum_smul,
    ← sum_inner, ← Algebra.TensorProduct.one_def, a, TensorProduct.of_othonormalBasis_prod_eq']
  rfl

theorem LinearMapClass.apply_rankOne_apply
  {E₁ E₂ E₃ 𝕜 : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]
  [InnerProductSpace 𝕜 E₁] [InnerProductSpace 𝕜 E₂] [InnerProductSpace 𝕜 E₃]
  {F : Type*}
  [FunLike F E₁ E₃] [LinearMapClass F 𝕜 E₁ E₃]
  (x : E₁) (y z : E₂) (u : F) :
    u ((rankOne 𝕜 x y) z) = rankOne 𝕜 (u x) y z :=
by simp only [rankOne_apply, map_smul]

theorem Upsilon_apply_comp {C D : Type*} [starAlgebra C] [QuantumSet C]
  [starAlgebra D] [QuantumSet D]
  {f : A →ₗ[ℂ] B}
  {g : D →ₗ[ℂ] C} (x : C →ₗ[ℂ] A)
  (hcd : k C = k D)
  (h : (modAut (k C + 1)).toLinearMap ∘ₗ g = g ∘ₗ (modAut (k D + 1)).toLinearMap) :
  Upsilon (f ∘ₗ x ∘ₗ g) = ((symmMap ℂ _ _).symm g ⊗ₘ f) (Upsilon x) :=
by
  rw [Upsilon]
  simp only [LinearEquiv.trans_apply]
  rw [Psi_apply_linearMap_comp_linearMap_of_commute_modAut,
    ← TensorProduct.map_comm]
  · simp only [← LinearEquiv.coe_toLinearMap]
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
    symm
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
    congr
    rw [TensorProduct.ext_iff']
    intro _ _
    simp only [LinearEquiv.coe_coe, LinearEquiv.coe_lTensor, LinearMap.map_comp_lTensor,
      LinearMap.coe_comp, Function.comp_apply, LinearEquiv.TensorProduct.map_apply,
      TensorProduct.map_tmul, unop_apply, op_apply, MulOpposite.coe_opLinearEquiv_symm,
      MulOpposite.unop_op, symmMap_symm_apply, LinearMap.op_apply, LinearMap.real_apply,
      MulOpposite.op_star, MulOpposite.unop_star, LinearMap.lTensor_tmul]
  · simp only [starAlgebra.modAut_zero, AlgEquiv.one_toLinearMap]; rfl
  · rw [hcd] at h; exact h

theorem TensorProduct.toIsBimoduleMap_comp
  {R H₁ H₂ H₃ H₄ : Type*} [CommSemiring R]
  [Semiring H₁] [Semiring H₂] [Semiring H₃] [Semiring H₄] [Algebra R H₁] [Algebra R H₂]
  [Algebra R H₃] [Algebra R H₄]
  {f : H₁ ≃ₐ[R] H₃} {g : H₂ ≃ₐ[R] H₄} {x : H₁ ⊗[R] H₂} :
  (TensorProduct.toIsBimoduleMap
    ((AlgEquiv.TensorProduct.map f g) x)).1
    =
    (AlgEquiv.TensorProduct.map f g).toLinearMap
      ∘ₗ (TensorProduct.toIsBimoduleMap x).1
      ∘ₗ (AlgEquiv.TensorProduct.map f.symm g.symm).toLinearMap :=
by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, ZeroMemClass.coe_zero, AlgEquiv.TensorProduct.map_toLinearMap,
    LinearMap.zero_comp, LinearMap.comp_zero]
  | tmul _ _ =>
    rw [TensorProduct.toIsBimoduleMap_apply_coe, AlgEquiv.TensorProduct.map_tmul, rmulMapLmul_apply]
    rw [TensorProduct.ext_iff']
    intro _ _
    rw [map_tmul, lmul_eq_mul, rmul_eq_mul, ← LinearMap.mulLeft_conj_of_mulEquivClass_apply,
      ← LinearMap.mulRight_conj_of_mulEquivClass_apply]
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.TensorProduct.map_tmul,
      toIsBimoduleMap_apply_coe, rmulMapLmul_apply, map_tmul]
    rfl
  | add _ _ h1 h2 =>
    simp only [_root_.map_add, LinearMap.IsBimoduleMaps.coe_add, h1, h2,
      LinearMap.add_comp, LinearMap.comp_add]

open scoped FiniteDimensional in
theorem QuantumGraph.Real.upsilon_starAlgEquiv_conj_submodule
  {f : A →ₗ[ℂ] A} (gns : hA.k = 0) (gns₂ : hB.k = 0)
  (hf : QuantumGraph.Real A f)
  {φ : A ≃⋆ₐ[ℂ] B} (hφ : Isometry φ) :
  upsilonSubmodule gns₂ (QuantumGraph.Real_conj_starAlgEquiv hf hφ) =
    Submodule.map
      (StarAlgEquiv.TensorProduct.map φ φ).toLinearMap (upsilonSubmodule gns hf) :=
by
  rw [Submodule.eq_iff_orthogonalProjection_eq,
    ← ContinuousLinearMap.coe_inj,
    orthogonalProjection_submoduleMap_isometry_starAlgEquiv
      (StarAlgEquiv.tensorProduct_map_isometry_of hφ hφ)]
  rw [upsilonOrthogonalProjection, upsilonOrthogonalProjection]
  simp only [LinearMap.coe_toContinuousLinearMap]
  rw [Upsilon_apply_comp]
  · rw [symmMap_symm_apply, LinearMap.adjoint_adjoint,
      (LinearMap.isReal_iff _).mp (StarAlgEquiv.isReal _)]
    calc (TensorProduct.toIsBimoduleMap ((φ.toLinearMap ⊗ₘ φ.toLinearMap) (Upsilon f))).1
        = (TensorProduct.toIsBimoduleMap ((AlgEquiv.TensorProduct.map φ.toAlgEquiv
          φ.toAlgEquiv) (Upsilon f))).1 := rfl
      _ = (AlgEquiv.TensorProduct.map φ.toAlgEquiv φ.toAlgEquiv).toLinearMap
        ∘ₗ (TensorProduct.toIsBimoduleMap (Upsilon f)).1
        ∘ₗ (AlgEquiv.TensorProduct.map φ.toAlgEquiv.symm φ.toAlgEquiv.symm).toLinearMap :=
           TensorProduct.toIsBimoduleMap_comp
  · simp only [gns, gns₂]
  · have := QuantumSet.starAlgEquiv_commutes_with_modAut_of_isometry' hφ
    simp only [gns, gns₂, zero_add, mul_zero] at this ⊢
    apply_fun LinearMap.adjoint using LinearEquiv.injective _
    simp only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, QuantumSet.modAut_adjoint]
    exact this

theorem PhiMap.apply_real (gns : k B = 0) (A : B →ₗ[ℂ] B) :
  (PhiMap (LinearMap.real A)).1
    = LinearMap.adjoint (PhiMap A).1 :=
real_Upsilon_toBimodule gns gns

theorem PhiMap_rankOne (x y : B) :
  (PhiMap (rankOne ℂ x y)).1 =
    TensorProduct.map (LinearMap.adjoint (rmul y)) (lmul x) :=
by
  rw [PhiMap_apply, Upsilon_rankOne, TensorProduct.toIsBimoduleMap_apply_coe,
    rmulMapLmul_apply, ← rmul_adjoint]

theorem LinearMap.real_zero :
  LinearMap.real (0 : B →ₗ[ℂ] B) = 0 :=
by ext; simp only [real_apply, zero_apply, star_zero]

theorem lTensor_counit_PhiMap_rTensor_algebraLinearMap (x : B →ₗ[ℂ] B) :
  (modAut (-k B)).toLinearMap
    ∘ₗ (TensorProduct.rid ℂ _).toLinearMap
    ∘ₗ (LinearMap.lTensor _ Coalgebra.counit)
    ∘ₗ (PhiMap x).1
    ∘ₗ (LinearMap.rTensor _ (Algebra.linearMap ℂ _))
    ∘ₗ (TensorProduct.lid ℂ _).symm.toLinearMap
    ∘ₗ (modAut (k B)).toLinearMap
  = symmMap ℂ B B x :=
by
  rw [PhiMap_apply, TensorProduct.toIsBimoduleMap_apply_coe,
    rmulMapLmul_apply_Upsilon_eq, symmMap_eq]
  simp only [LinearMap.comp_assoc, LinearMap.rTensor_comp, LinearMap.lTensor_comp]

/-- Linear functional computing the weighted number of edges of a quantum graph. -/
noncomputable def QuantumGraph.NumOfEdges {A : Type*} [starAlgebra A] [QuantumSet A] :
    (A →ₗ[ℂ] A) →ₗ[ℂ] ℂ where
  toFun f := ⟪1, f 1⟫_ℂ
  map_add' _ _ := by simp only [LinearMap.add_apply, inner_add_right]
  map_smul' _ _ := by simp only [LinearMap.smul_apply, inner_smul_right]; rfl

end

-- class QuantumGraphHom {A B : Type*} [NormedAddCommGroupOfRing A]
--   [NormedAddCommGroupOfRing B] [hA : QuantumSet A] [hB : QuantumSet B]
--   {x : A →ₗ[ℂ] A} (hx : QuantumGraph A x)
--   {y : B →ₗ[ℂ] B} (hy : QuantumGraph B y)
--     extends A →⋆ₐ[ℂ] B where
--   isGraphHom :
--     y •ₛ (toStarAlgHom.toLinearMap ∘ₗ x ∘ₗ (LinearMap.adjoint toStarAlgHom.toLinearMap))
--       = toStarAlgHom.toLinearMap ∘ₗ x ∘ₗ (LinearMap.adjoint toStarAlgHom.toLinearMap)
