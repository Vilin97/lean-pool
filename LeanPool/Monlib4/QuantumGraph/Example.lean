/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.QuantumGraph.Basic
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Pi
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.TensorProduct
import LeanPool.Monlib4.LinearAlgebra.Ips.MatIps
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Instances
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.DeltaForm

/-!
  # Basic examples on quantum adjacency matrices

  This file contains elementary examples of quantum adjacency matrices,
    such as the complete graph and the trivial graph.
-/


-- import quantum_graph.basic
-- import quantum_graph.basic
open TensorProduct Matrix

open scoped TensorProduct BigOperators Kronecker Matrix Functional

variable {p : Type _} [Fintype p] [DecidableEq p] {n : p → Type _} [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (n i)]
  {p₂ : Type*} [Fintype p₂] [DecidableEq p₂] {n₂ : p₂ → Type*} [∀ i, Fintype (n₂ i)]
  [∀ i, DecidableEq (n₂ i)]

local notation "ℍ" => PiMat ℂ p n
local notation "ℍ₂" => PiMat ℂ p₂ n₂

-- local notation `⊗K` := matrix (n × n) (n × n) ℂ
local notation "l(" x ")" => x →ₗ[ℂ] x

variable {φ : Π i : p, Module.Dual ℂ (Matrix (n i) (n i) ℂ)} {ψ : Π i,
  Module.Dual ℂ (Matrix (n₂ i) (n₂ i) ℂ)}

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

local notation "m" => LinearMap.mul' ℂ ℍ

local notation "η" => Algebra.linearMap ℂ ℍ

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" =>
  LinearEquiv.toLinearMap (TensorProduct.assoc ℂ ℍ ℍ ℍ)

local notation "υ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.assoc ℂ ℍ ℍ ℍ))

local notation "ϰ" =>
  LinearEquiv.toLinearMap ((TensorProduct.comm ℂ ℍ ℂ))

local notation "ϰ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.comm ℂ ℍ ℂ))

local notation "τ" =>
  LinearEquiv.toLinearMap (TensorProduct.lid ℂ ℍ)

local notation "τ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.lid ℂ ℍ))

local notation "id" => (1 : ℍ →ₗ[ℂ] ℍ)

/-- The complete quantum adjacency map between two Hilbert spaces with chosen units. -/
noncomputable def Qam.completeGraph (E₁ E₂ : Type _) [One E₁] [One E₂] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂] :
    E₂ →ₗ[ℂ] E₁ :=
  |(1 : E₁)⟩⟨(1 : E₂)|

theorem Qam.completeGraph_eq {E₁ E₂ : Type _} [One E₁] [One E₂] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂] :
    Qam.completeGraph E₁ E₂ = |(1 : E₁)⟩⟨(1 : E₂)| :=
  rfl

variable {A B : Type*} [ha : starAlgebra A] [hb : starAlgebra B]
  [hA : QuantumSet A] [hB : QuantumSet B]

theorem Qam.completeGraph_eq' :
  Qam.completeGraph A B =
    Algebra.linearMap ℂ A ∘ₗ Coalgebra.counit :=
by
  rw [Coalgebra.counit_eq_bra_one]
  ext
  simp [Algebra.algebraMap_eq_smul_one]
  rfl

open scoped schurMul
theorem Qam.Nontracial.CompleteGraph.qam :
  ((Qam.completeGraph A B) •ₛ (Qam.completeGraph A B)) = Qam.completeGraph A B :=
schurMul_one_one_left _

open scoped FiniteDimensional

lemma Qam.Nontracial.CompleteGraph.adjoint_eq {E₁ E₂ : Type _} [NormedAddCommGroupOfRing E₁]
    [NormedAddCommGroupOfRing E₂] [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂]
    [FiniteDimensional ℂ E₁] [FiniteDimensional ℂ E₂]
    [IsScalarTower ℂ E₁ E₁] [IsScalarTower ℂ E₂ E₂]
    [SMulCommClass ℂ E₁ E₁] [SMulCommClass ℂ E₂ E₂] :
  LinearMap.adjoint (Qam.completeGraph E₁ E₂) = Qam.completeGraph E₂ E₁ :=
by rw [completeGraph_eq, ContinuousLinearMap.linearMap_adjoint, rankOne_adjoint]; rfl

theorem Qam.Nontracial.CompleteGraph.isSelfAdjoint {E : Type _} [One E] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] :
      _root_.IsSelfAdjoint (Qam.completeGraph E E) := by
  simp_rw [_root_.IsSelfAdjoint, Qam.completeGraph, LinearMap.star_eq_adjoint,
    ContinuousLinearMap.linearMap_adjoint, rankOne_adjoint]

theorem Qam.Nontracial.CompleteGraph.isReal :
    LinearMap.IsReal (Qam.completeGraph A B) := by
  simp_rw [Qam.completeGraph, LinearMap.isReal_iff, rankOne_real, star_one,
    _root_.map_one]

theorem Qam.Nontracial.CompleteGraph.symm_eq :
  symmMap ℂ _ _ (Qam.completeGraph A B) = Qam.completeGraph B A :=
by simp_rw [Qam.completeGraph, symmMap_rankOne_apply, star_one, _root_.map_one]
theorem Qam.Nontracial.CompleteGraph.is_symm :
  symmMap ℂ _ _ (Qam.completeGraph A A) = Qam.completeGraph A A :=
Qam.Nontracial.CompleteGraph.symm_eq

theorem Qam.Nontracial.CompleteGraph.is_reflexive :
  (Qam.completeGraph A A) •ₛ 1 = 1 :=
by
  obtain ⟨α, β, hαβ⟩ := (1 : l(A)).exists_sum_rankOne
  nth_rw 1 [hαβ]
  simp_rw [map_sum, Qam.completeGraph, schurMul.apply_rankOne, one_mul, ← hαβ]

/-- The trivial quantum graph on a quantum set with delta form. -/
noncomputable def Qam.trivialGraph (A : Type*) [starAlgebra A] [CoalgebraStruct ℂ A] [QuantumSet A]
  [QuantumSetDeltaForm A] :
  l(A) :=
⅟ (LinearMap.mul' ℂ A ∘ₗ Coalgebra.comul)

variable {A : Type*} [ha : starAlgebra A] [hA : QuantumSet A]

open scoped ComplexOrder

section TrivialGraph

variable [hAc : CoalgebraStruct ℂ A]

theorem Qam.trivialGraph_eq [hA2 : QuantumSetDeltaForm A] :
    Qam.trivialGraph A = hA2.delta⁻¹ • (1 : l(A)) :=
  by
  simp_rw [Qam.trivialGraph]
  apply invOf_eq_right_inv
  rw [hA2.mul_comp_comul_eq, smul_mul_smul_comm, one_mul, mul_inv_cancel₀,
    one_smul]
  · exact ne_of_gt hA2.delta_pos

theorem Qam.Nontracial.TrivialGraph.qam [hA2 : QuantumSetDeltaForm A] :
    (Qam.trivialGraph A) •ₛ (Qam.trivialGraph A) = Qam.trivialGraph A :=
  by
  rw [Qam.trivialGraph_eq]
  simp_rw [_root_.map_smul, LinearMap.smul_apply, smul_smul, schurMul]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [TensorProduct.map_one, Module.End.one_eq_id, LinearMap.id_comp,
    hA2.mul_comp_comul_eq, smul_smul, mul_assoc]
  rw [inv_mul_cancel₀ _, mul_one, Module.End.one_eq_id]
  · exact ne_of_gt hA2.delta_pos

theorem Qam.Nontracial.TrivialGraph.qam.is_self_adjoint [hA2 : QuantumSetDeltaForm A] :
    LinearMap.adjoint (Qam.trivialGraph A) = Qam.trivialGraph A :=
  by
  simp_rw [Qam.trivialGraph_eq, LinearMap.adjoint_smul, LinearMap.adjoint_one, starRingEnd_apply,
    star_inv₀, ← starRingEnd_apply]
  congr 2
  have := hA2.delta_pos
  rw [RCLike.pos_def, ← RCLike.conj_eq_iff_im] at this
  exact this.2

theorem Qam.Nontracial.trivialGraph [hA2 : QuantumSetDeltaForm A] :
    (Qam.trivialGraph A) •ₛ 1 = 1 :=
  by
  rw [Qam.trivialGraph_eq, _root_.map_smul, LinearMap.smul_apply]
  simp only [schurMul, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [TensorProduct.map_one, Module.End.one_eq_id,
    LinearMap.id_comp, hA2.mul_comp_comul_eq, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hA2.delta_pos), one_smul, Module.End.one_eq_id]

theorem Qam.refl_idempotent_one_one_of_delta [hA2 : QuantumSetDeltaForm A] :
    (1 : _) •ₛ (1 : l(A)) = hA2.delta • (1 : l(A)) := by
  simp_rw [schurMul_apply_apply, TensorProduct.map_one, LinearMap.one_comp, hA2.mul_comp_comul_eq]

theorem Qam.Lm.Nontracial.is_unreflexive_iff_reflexive_add_one [hA2 : QuantumSetDeltaForm A]
    (x : l(A)) :
    x •ₛ 1 = 0 ↔ (hA2.delta⁻¹ • (x + 1)) •ₛ 1 = 1 :=
  by
  simp_rw [_root_.map_smul, LinearMap.smul_apply, _root_.map_add, LinearMap.add_apply,
    Qam.refl_idempotent_one_one_of_delta, smul_add, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hA2.delta_pos), one_smul, add_eq_right]
  rw [smul_eq_zero_iff_right (inv_ne_zero (ne_of_gt hA2.delta_pos))]

end TrivialGraph

theorem Qam.refl_idempotent_completeGraph_left
  (x : A →ₗ[ℂ] B) : (Qam.completeGraph B A) •ₛ x = x :=
schurMul_one_one_left _

theorem Qam.refl_idempotent_completeGraph_right (x : A →ₗ[ℂ] B) :
  x •ₛ (Qam.completeGraph B A) = x :=
schurMul_one_one_right _

/-- The complement of a quantum adjacency map, relative to the complete graph. -/
noncomputable def Qam.complement' {E₁ E₂ : Type _} [One E₁] [One E₂]
    [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂]
  (x : E₂ →ₗ[ℂ] E₁) : E₂ →ₗ[ℂ] E₁ :=
Qam.completeGraph E₁ E₂ - x

theorem Qam.Nontracial.Complement'.qam
    (x : A →ₗ[ℂ] B) :
    x •ₛ x = x ↔
      (Qam.complement' x) •ₛ (Qam.complement' x) = Qam.complement' x :=
  by
  simp only [Qam.complement', _root_.map_sub, LinearMap.sub_apply,
    Qam.refl_idempotent_completeGraph_left, Qam.refl_idempotent_completeGraph_right]
  simp only [sub_eq_self]
  simp only [sub_eq_zero, @eq_comm _ x]

theorem Qam.Nontracial.Complement'.qam.isReal
    (x : A →ₗ[ℂ] B) : LinearMap.IsReal x ↔ LinearMap.IsReal (Qam.complement' x) :=
  by
  simp only [Qam.complement', LinearMap.isReal_iff, LinearMap.real_sub,
    (LinearMap.isReal_iff _).mp (Qam.Nontracial.CompleteGraph.isReal)]
  simp only [sub_right_inj]

theorem Qam.complement'_complement' {E₁ E₂ : Type _} [NormedAddCommGroupOfRing E₁]
    [NormedAddCommGroupOfRing E₂]
    [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂] [FiniteDimensional ℂ E₁]
    [FiniteDimensional ℂ E₂] [IsScalarTower ℂ E₁ E₁] [IsScalarTower ℂ E₂ E₂] [SMulCommClass ℂ E₁ E₁]
    [SMulCommClass ℂ E₂ E₂]
    (x : E₁ →ₗ[ℂ] E₂) : Qam.complement' (Qam.complement' x) = x :=
  sub_sub_cancel _ _

theorem Qam.Nontracial.Complement'.ir_reflexive
    (x : l(A)) (α : Prop) [Decidable α] :
    x •ₛ (1 : l(A)) = ite α (1 : l(A)) (0 : l(A)) ↔
      (Qam.complement' x) •ₛ (1 : l(A)) = ite α (0 : l(A)) (1 : l(A)) :=
by
  simp_rw [Qam.complement', _root_.map_sub, LinearMap.sub_apply,
    Qam.refl_idempotent_completeGraph_left]
  by_cases h : α <;> simp_rw [h]
  · simp_rw [if_true, sub_eq_zero, eq_comm]
  · simp_rw [if_false, sub_eq_self]

/-- A quantum adjacency map that is idempotent and reflexive. -/
class QamReflexive (x : l(A)) : Prop where
/-- Idempotence under Schur multiplication. -/
toQam : x •ₛ x = x
/-- Reflexivity condition. -/
toRefl : x •ₛ 1 = 1

lemma QamReflexive_iff (x : l(A)) :
    QamReflexive x ↔ x •ₛ x = x ∧ x •ₛ 1 = 1 :=
⟨fun h => ⟨h.toQam, h.toRefl⟩, fun h => ⟨h.1, h.2⟩⟩

/-- A quantum adjacency map that is idempotent and irreflexive. -/
class QamIrreflexive (x : l(A)) : Prop where
/-- Idempotence under Schur multiplication. -/
toQam : x •ₛ x = x
/-- Irreflexivity condition. -/
toIrrefl : x •ₛ 1 = 0

lemma QamIrreflexive_iff (x : l(A)) :
    QamIrreflexive x ↔ x •ₛ x = x ∧ x •ₛ 1 = 0 :=
⟨fun h => ⟨h.toQam, h.toIrrefl⟩, fun h => ⟨h.1, h.2⟩⟩

theorem Qam.complement'_is_irreflexive_iff
    (x : l(A)) : QamIrreflexive (Qam.complement' x) ↔ QamReflexive x :=
  by
  have := Qam.Nontracial.Complement'.ir_reflexive x True
  simp_rw [if_true] at this
  rw [QamReflexive_iff, QamIrreflexive_iff, ← Qam.Nontracial.Complement'.qam]
  simp_rw [this]

theorem Qam.complement'_is_reflexive_iff
    (x : l(A)) : QamReflexive (Qam.complement' x) ↔ QamIrreflexive x :=
  by
  have := Qam.Nontracial.Complement'.ir_reflexive x False
  simp_rw [if_false] at this
  rw [QamReflexive_iff, QamIrreflexive_iff, ← Qam.Nontracial.Complement'.qam, this]

/-- Complement relative to the trivial graph. -/
noncomputable def Qam.complement'' [QuantumSetDeltaForm A]
  (x : l(A)) :
    l(A) :=
  x - Qam.trivialGraph A

theorem Qam.complement''_is_irreflexive_iff [hA2 : QuantumSetDeltaForm A] {x : l(A)}
    (hx : LinearMap.IsReal x) : QamIrreflexive (Qam.complement'' x) ↔ QamReflexive x :=
  by
  rw [QamReflexive_iff, QamIrreflexive_iff]
  have t1 := @Qam.Nontracial.TrivialGraph.qam A _ _ _
  have t2 := @Qam.Nontracial.trivialGraph A _ _ _
  have t3 : (Qam.complement'' x) •ₛ 1 = 0 ↔ x •ₛ 1 = 1 := by
    simp_rw [Qam.complement'', map_sub, LinearMap.sub_apply, t2, sub_eq_zero]
  rw [t3]
  simp_rw [Qam.complement'', map_sub, LinearMap.sub_apply, t1, sub_sub]
  constructor <;> rintro ⟨h1, h2⟩
  all_goals
    exact ⟨by
      simp only [Qam.trivialGraph_eq, _root_.map_smul, LinearMap.smul_apply, h2,
        (schurMul_reflexive_of_isReal hx).mp h2, sub_self, add_zero, sub_left_inj] at h1 ⊢
      exact h1, h2⟩

/-- Complement operation producing the irreflexive complement. -/
noncomputable def Qam.irreflexiveComplement [QuantumSetDeltaForm A] (x : l(A)) :
    l(A) :=
Qam.completeGraph A A - Qam.trivialGraph A - x

/-- Complement operation producing the reflexive complement. -/
noncomputable def Qam.reflexiveComplement [QuantumSetDeltaForm A] (x : l(A)) :
  l(A) :=
Qam.completeGraph A A + Qam.trivialGraph A - x

theorem Qam.Nontracial.trivialGraph.isReal [hA2 : QuantumSetDeltaForm A] :
    LinearMap.IsReal (Qam.trivialGraph A) :=
  by
  rw [LinearMap.isReal_iff, Qam.trivialGraph_eq, LinearMap.real_smul, LinearMap.real_one,
    starRingEnd_apply, star_inv₀]
  congr
  have := hA2.delta_pos
  rw [RCLike.pos_def, ← RCLike.conj_eq_iff_im] at this
  exact this.2

theorem Qam.irreflexiveComplement.isReal [hA2 : QuantumSetDeltaForm A]
  {x : l(A)} (hx : LinearMap.IsReal x) : LinearMap.IsReal (Qam.irreflexiveComplement x) := by
  rw [LinearMap.isReal_iff, Qam.irreflexiveComplement, LinearMap.real_sub, LinearMap.real_sub,
    (LinearMap.isReal_iff (Qam.completeGraph A A)).mp Qam.Nontracial.CompleteGraph.isReal,
    (LinearMap.isReal_iff (Qam.trivialGraph A)).mp
      Qam.Nontracial.trivialGraph.isReal,
    (LinearMap.isReal_iff x).mp hx]

theorem Qam.reflexiveComplement.isReal [hA2 : QuantumSetDeltaForm A] {x : l(A)}
    (hx : LinearMap.IsReal x) : LinearMap.IsReal (Qam.reflexiveComplement x) := by
  rw [LinearMap.isReal_iff, Qam.reflexiveComplement, LinearMap.real_sub, LinearMap.real_add,
    (LinearMap.isReal_iff (Qam.completeGraph A A)).mp Qam.Nontracial.CompleteGraph.isReal,
    (LinearMap.isReal_iff (Qam.trivialGraph A)).mp
      Qam.Nontracial.trivialGraph.isReal,
    (LinearMap.isReal_iff x).mp hx]

theorem Qam.irreflexiveComplement_irreflexiveComplement [QuantumSetDeltaForm A]
    {x : l(A)} : Qam.irreflexiveComplement (Qam.irreflexiveComplement x) = x :=
  sub_sub_cancel _ _

theorem Qam.reflexiveComplement_reflexiveComplement [QuantumSetDeltaForm A] {x : l(A)} :
    Qam.reflexiveComplement (Qam.reflexiveComplement x) = x :=
  sub_sub_cancel _ _

theorem Qam.trivialGraph_reflexiveComplement_eq_completeGraph [QuantumSetDeltaForm A] :
    Qam.reflexiveComplement (Qam.trivialGraph A) = Qam.completeGraph A A :=
by simp_rw [reflexiveComplement, add_sub_cancel_right]

theorem Qam.completeGraph_reflexiveComplement_eq_trivialGraph [QuantumSetDeltaForm A] :
    Qam.reflexiveComplement (Qam.completeGraph A A) = Qam.trivialGraph A :=
  add_sub_cancel_left _ _

theorem Qam.complement'_eq {E₁ E₂ : Type _} [NormedAddCommGroupOfRing E₁]
    [NormedAddCommGroupOfRing E₂]
    [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂] [FiniteDimensional ℂ E₁]
    [FiniteDimensional ℂ E₂] [IsScalarTower ℂ E₁ E₁] [IsScalarTower ℂ E₂ E₂] [SMulCommClass ℂ E₁ E₁]
    [SMulCommClass ℂ E₂ E₂] (a : E₂ →ₗ[ℂ] E₁) :
    Qam.complement' a = Qam.completeGraph E₁ E₂ - a :=
  rfl

theorem Qam.irreflexiveComplement_is_irreflexive_qam_iff_irreflexive_qam
  [hA2 : QuantumSetDeltaForm A] {x : l(A)} (hx : LinearMap.IsReal x) :
    QamIrreflexive (Qam.irreflexiveComplement x) ↔ QamIrreflexive x :=
  by
  rw [Qam.irreflexiveComplement, sub_sub, ← Qam.complement'_eq,
    Qam.complement'_is_irreflexive_iff, ← Qam.complement''_is_irreflexive_iff,
    Qam.complement'', add_sub_cancel_left]
  · rw [LinearMap.isReal_iff, LinearMap.real_add, x.isReal_iff.mp hx,
      (Qam.trivialGraph A).isReal_iff.mp Qam.Nontracial.trivialGraph.isReal]

theorem Qam.reflexive_complment_is_reflexive_qam_iff_reflexive_qam
  [hA2 : QuantumSetDeltaForm A] {x : l(A)} (hx : LinearMap.IsReal x) :
    QamReflexive (Qam.reflexiveComplement x) ↔ QamReflexive x :=
  by
  rw [Qam.reflexiveComplement, ← sub_sub_eq_add_sub, ← Qam.complement'_eq,
    Qam.complement'_is_reflexive_iff]
  exact Qam.complement''_is_irreflexive_iff hx


theorem QuantumSet.Psi_apply_completeGraph {A : Type*} {B : Type*} [starAlgebra A]
    [starAlgebra B] [QuantumSet A] [QuantumSet B] (t r : ℝ) :
  QuantumSet.Psi t r (Qam.completeGraph A B) = 1 :=
QuantumSet.Psi_apply_one_one _ _
theorem QuantumSet.Psi_symm_one {A B : Type*} [starAlgebra A]
  [starAlgebra B] [QuantumSet A] [QuantumSet B] (t r : ℝ) :
  (QuantumSet.Psi t r).symm 1 = Qam.completeGraph A B :=
QuantumSet.Psi_symm_apply_one _ _
