/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import LeanPool.BrauerGroupNew.AlgClosedUnion
import LeanPool.BrauerGroupNew.ExtendScalar
import LeanPool.BrauerGroupNew.LemmasAboutSimpleRing
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Central.Matrix
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Splitting central simple algebras

This file ports the upstream splitting-field infrastructure for central simple algebras.
-/

suppress_compilation

universe u v w
variable (k A K : Type u) [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]

variable (k_bar : Type u) [Field k_bar] [Algebra k k_bar]
  [hk_bar : IsAlgClosure k k_bar] (k_s : Type u) [Field k_s] [Algebra k k_s]

open scoped TensorProduct
open RingCon

instance moduleOverOver (A : CSA k) (I : TwoSidedIdeal A) :
    Module k I := Module.compHom I (algebraMap k A)

theorem is_simple_A [IsSimpleRing (K ⊗[k] A)] : IsSimpleRing A := IsSimpleRing.right_of_tensor k K A

private lemma subsingleton_tensor [Subsingleton A] : Subsingleton (K ⊗[k] A) := by
  rw [← subsingleton_iff_zero_eq_one, show (0 : K ⊗[k] A) = 0 ⊗ₜ 0 by simp,
      show (1 : K ⊗[k] A) = 1 ⊗ₜ 1 by rfl, show (1 : A) = 0 from Subsingleton.elim _ _]
  simp

theorem central_over_extension_iff_subsingleton
    [Subsingleton A] [FiniteDimensional k A] [FiniteDimensional k K] :
    Algebra.IsCentral k A ↔ Algebra.IsCentral K (K ⊗[k] A) := by
  have : Subsingleton (K ⊗[k] A) := subsingleton_tensor k A K
  constructor <;>
  · intro h
    refine ⟨fun x hx => ?_⟩
    rw [show x = 0 from Subsingleton.elim _ _]
    exact Subalgebra.zero_mem ⊥

theorem isSimple_over_extension_iff_subsingleton
    [Subsingleton A] [FiniteDimensional k A] [FiniteDimensional k K] :
    IsSimpleRing A ↔ IsSimpleRing (K ⊗[k] A) := by
  have : Subsingleton (K ⊗[k] A) := subsingleton_tensor k A K
  constructor <;>
  · intro h
    have : Nontrivial (K ⊗[k] A) := inferInstance
    rw [← not_subsingleton_iff_nontrivial] at this
    contradiction

theorem centralSimple_over_extension_iff_nontrivial
    [Nontrivial A] [FiniteDimensional k A] [FiniteDimensional k K] :
    (Algebra.IsCentral k A ∧ IsSimpleRing A) ↔
    (Algebra.IsCentral K (K ⊗[k] A) ∧ IsSimpleRing (K ⊗[k] A)) where
  mp := fun ⟨_, _⟩ ↦ ⟨inferInstance, inferInstance⟩
  mpr := fun ⟨hAt, _⟩ ↦ ⟨by
    constructor
    by_contra h
    simp only [le_bot_iff] at h
    have : 1 < Module.finrank k (Subalgebra.center k A) := by
      have eq1 := Subalgebra.finrank_bot (F := k) (E := A)
      have ineq1 := Submodule.finrank_lt_finrank_of_lt
        (s := Subalgebra.toSubmodule (⊥ : Subalgebra k A))
        (t := Subalgebra.toSubmodule (Subalgebra.center k A)) (by
        simp only [OrderEmbedding.lt_iff_lt]
        rw [bot_lt_iff_ne_bot]
        exact h)
      erw [eq1] at ineq1
      exact ineq1
    let e : K ⊗[k] Subalgebra.center k A ≃ₗ[k] Subalgebra.center k (K ⊗[k] A) :=
      (TensorProduct.congr (Submodule.topEquiv.symm ≪≫ₗ
        show _ ≃ₗ[k] Subalgebra.toSubmodule (Subalgebra.center k K) from LinearEquiv.ofLinear
        (Submodule.inclusion (by simp)) (Submodule.inclusion (by simp)) rfl rfl)
        (LinearEquiv.refl _ _)) ≪≫ₗ
      (IsCentralSimple.centerTensor k K A)
    have eq1 : Module.finrank k (Subalgebra.center k (K ⊗[k] A)) =
              Module.finrank k K *
              Module.finrank k (Subalgebra.center k A) := by
      rw [LinearEquiv.finrank_eq e.symm, Module.finrank_tensorProduct]
    have eq2 : Module.finrank k (Subalgebra.center K (K ⊗[k] A)) =
              Module.finrank k K *
              Module.finrank k (Subalgebra.center k A) := by
      rw [← eq1]; congr
    have eq3 : Module.finrank k (Subalgebra.center K (K ⊗[k] A)) =
              Module.finrank k K *
              Module.finrank K (Subalgebra.center K (K ⊗[k] A)) := by
      rw [Module.finrank_mul_finrank]
    have eq4 : Module.finrank K (Subalgebra.center K (K ⊗[k] A)) = 1 := by
      rw [← Subalgebra.finrank_bot (F := K) (E := K ⊗[k] A)]
      have := hAt.center_eq_bot
      rw [this.symm]
    rw [eq4, mul_one] at eq3
    rw [eq3] at eq2
    have ineq0 : 0 < Module.finrank k K := Module.finrank_pos
    have ineq1 :
      Module.finrank k K <
      Module.finrank k K * Module.finrank k (Subalgebra.center k A) := by
      apply lt_mul_right <;> assumption
    conv_lhs at ineq1 => rw [eq2]
    exact Nat.lt_irrefl _ ineq1, is_simple_A k A K⟩

theorem centralsimple_over_extension_iff
    [FiniteDimensional k A] [FiniteDimensional k K] :
    (Algebra.IsCentral k A ∧ IsSimpleRing A) ↔
    (Algebra.IsCentral K (K ⊗[k] A) ∧ IsSimpleRing (K ⊗[k] A)) := by
  obtain h|h := subsingleton_or_nontrivial A
  · refine ⟨fun ⟨_, _⟩ ↦ ⟨?_, ?_⟩, fun ⟨_, _⟩ ↦ ⟨?_, ?_⟩⟩
    · rwa [← central_over_extension_iff_subsingleton]
    · rwa [← isSimple_over_extension_iff_subsingleton]
    · rwa [central_over_extension_iff_subsingleton k A K]
    · rwa [isSimple_over_extension_iff_subsingleton k A K]
  · apply centralSimple_over_extension_iff_nontrivial

/-- Scalar extension of a central simple algebra is again a central simple algebra. -/
def extensionCSA (A : CSA k) : CSA K where
  toAlgCat := .of K (K ⊗[k] A)
  fin_dim := Module.Finite.base_change k K A.carrier

/-- Descend a central simple algebra structure from a finite scalar extension. -/
def extensionInv [FiniteDimensional k A]
    [Algebra.IsCentral K (K ⊗[k] A)] [IsSimpleRing (K ⊗[k] A)]
    [FiniteDimensional K (K ⊗[k] A)]
    [FiniteDimensional k K] : CSA k where
  toAlgCat := .of k A
  isCentral := centralsimple_over_extension_iff k A K |>.2 ⟨inferInstance, inferInstance⟩ |>.1
  isSimple := centralsimple_over_extension_iff k A K |>.2 ⟨inferInstance, inferInstance⟩ |>.2
  fin_dim := by
    have := centralsimple_over_extension_iff k A K |>.2 ⟨inferInstance, inferInstance⟩ |>.2
    let to_ten: A →ₐ[k] K ⊗[k] A :=
    {
      toFun := fun a ↦ 1 ⊗ₜ a
      map_one' := rfl
      map_mul' := by simp
      map_zero' := TensorProduct.tmul_zero A 1
      map_add' := TensorProduct.tmul_add 1
      commutes' := fun _ ↦ Algebra.TensorProduct.algebraMap_apply' _|>.symm
    }
    have Isinj : Function.Injective to_ten := by
      have := IsSimpleRing.iff_eq_zero_or_injective' A k|>.1 inferInstance (B := K ⊗[k] A) to_ten
      have nezero : TwoSidedIdeal.ker to_ten ≠ ⊤ := by
        intro h
        have : (1 : A) ∈ (⊤ : TwoSidedIdeal A) := by simp
        rw [h.symm, TwoSidedIdeal.mem_ker] at this
        simp only [map_one, one_ne_zero] at this
      simp only [nezero, false_or] at this
      exact this
    haveI : FiniteDimensional k (K ⊗[k] A) := Module.Finite.trans (R := k) K (K ⊗[k] A)
    exact FiniteDimensional.of_injective (K := k) to_ten.toLinearMap Isinj

theorem CSA_iff_exist_split (k_bar : Type u) [Field k_bar] [Algebra k k_bar]
    [hk_bar : IsAlgClosure k k_bar] [hA : FiniteDimensional k A] :
    Algebra.IsCentral k A ∧ IsSimpleRing A ↔
      ∃ n ≠ 0, ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)  (_ : FiniteDimensional k L),
        Nonempty (L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  constructor
  · rintro ⟨_, _⟩
    haveI := hk_bar.1
    obtain ⟨n, hn, ⟨iso⟩⟩ := simple_eq_matrix_algClosed k_bar (k_bar ⊗[k] A)
    refine ⟨n, hn, ?_⟩
    use lemmaTto.ℒℒ n k k_bar A iso
    have : NeZero n := ⟨hn⟩
    exact ⟨_, _, inferInstance, ⟨lemmaTto.isoRestrict n k k_bar A iso⟩⟩
  · rintro ⟨n, hn, L, _, _, _, ⟨iso⟩⟩
    have : NeZero n := ⟨hn⟩
    refine (centralsimple_over_extension_iff k A L).mpr <| ⟨iso.symm.isCentral, ⟨?_⟩⟩
    rw [← TwoSidedIdeal.orderIsoOfRingEquiv iso.symm.toRingEquiv |>.isSimpleOrder_iff]
    exact IsSimpleRing.simple

lemma dim_is_sq (k_bar : Type u) [Field k_bar] [Algebra k k_bar] [hk_bar : IsAlgClosure k k_bar]
    [Algebra.IsCentral k A] [IsSimpleRing A] [FiniteDimensional k A] :
    IsSquare (Module.finrank k A) := by
  haveI := hk_bar.1
  obtain ⟨n, _, ⟨iso⟩⟩ := simple_eq_matrix_algClosed k_bar (k_bar ⊗[k] A)
  refine ⟨n, ?_⟩
  have := Module.finrank_matrix k_bar k_bar (Fin n) (Fin n)
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at this
  exact dim_eq k k_bar A|>.trans <| LinearEquiv.finrank_eq iso.toLinearEquiv|>.trans this

/-- The degree of a central simple algebra, defined by the square root of its dimension. -/
def deg (A : CSA k) : ℕ := dim_is_sq k A k_bar |>.choose

lemma deg_sq_eq_dim (A : CSA k) : (deg k k_bar A) ^ 2 = Module.finrank k A :=
  by rw [pow_two]; exact dim_is_sq k A k_bar |>.choose_spec.symm

instance deg_pos (A : CSA k) : NeZero (deg k k_bar A) := by
  constructor
  by_contra! h
  apply_fun (·^2) at h
  rw [deg_sq_eq_dim k k_bar A, pow_two, mul_zero] at h
  have := Module.finrank_pos_iff (R := k) (M := A)|>.2 inferInstance
  linarith

/-- Data witnessing that a field extension splits a central simple algebra. -/
structure split (A : CSA k) (K : Type*) [Field K] [Algebra k K] where
  /-- The matrix size after scalar extension. -/
  (n : ℕ) [hn : NeZero n]
  /-- The scalar-extended algebra is a matrix algebra over the extension field. -/
  (iso : K ⊗[k] A ≃ₐ[K] Matrix (Fin n) (Fin n) K)

/-- A field extension splits an algebra if the scalar extension is a matrix algebra. -/
def isSplit (L : Type u) [Field L] [Algebra k L] : Prop :=
  ∃ (n : ℕ) (_ : NeZero n),
  Nonempty (L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)

/-- Any algebraic closure splits a central simple algebra. -/
def splitByAlgClosure (A : CSA k) : split k A k_bar where
  n := deg k k_bar A
  iso := by
    haveI := hk_bar.1
    choose n _ iso using simple_eq_matrix_algClosed k_bar (k_bar ⊗[k] A)
    have iso' := iso.some; clear iso
    have e : Matrix (Fin n) (Fin n) k_bar ≃ₐ[k_bar] Matrix (Fin (deg k k_bar A))
      (Fin (deg k k_bar A)) k_bar := by
      suffices n = deg k k_bar A from Matrix.reindexAlgEquiv k_bar _ (finCongr this)
      have := deg_sq_eq_dim k k_bar A
      rw [pow_two] at this
      have e1 := LinearEquiv.finrank_eq iso'.toLinearEquiv|>.trans <|
        Module.finrank_matrix k_bar _ (Fin n) (Fin n)
      simp only [Module.finrank_tensorProduct, Module.finrank_self, one_mul, Fintype.card_fin,
        mul_one] at e1
      have := this.trans e1
      exact Nat.mul_self_inj.mp (id this.symm)
    exact iso'.trans e

/-- Splitting is preserved after extending the splitting field. -/
def extensionOverSplit (A : CSA k) (L L' : Type u) [Field L] [Field L'] [Algebra k L]
    (hA : split k A L) [Algebra L L'] [Algebra k L'] [IsScalarTower k L L'] : split k A L' where
  n := deg k k_bar A
  iso := by
    obtain ⟨n, iso⟩ := hA
    let e1 : L' ⊗[k] A ≃ₐ[L] L' ⊗[L] (L ⊗[k] A) := {
      __ := absorbEqv k L L' A
      commutes' _ := rfl
    }
    let e2 := e1.trans <| Algebra.TensorProduct.congr .refl iso
    let e3 : L' ⊗[k] A ≃ₐ[L'] L' ⊗[L] Matrix (Fin n) (Fin n) L := {
      __ := e2
      commutes' := fun l' => by
        simp only [AlgEquiv.toEquiv_eq_coe, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, Equiv.toFun_as_coe, EquivLike.coe_coe]
        simp only [AlgEquiv.toEquiv_eq_coe, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
          AlgEquiv.refl_toAlgHom, e2, e1]
        erw [absorbEqv_apply, Algebra.TensorProduct.map_tmul]
        simp only [AlgHom.coe_id, id_eq, Algebra.TensorProduct.one_def.symm, map_one]
    }
    let e4 : L' ⊗[L] Matrix (Fin n) (Fin n) L ≃ₐ[L'] Matrix (Fin n) (Fin n) L' := {
      __ := matrixEquivTensor _ _ _|>.symm
      commutes' := fun l' ↦ by
        simp only [AlgEquiv.toEquiv_eq_coe, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, Equiv.toFun_as_coe, EquivLike.coe_coe,
          matrixEquivTensor_apply_symm, Matrix.map]
        ext i j
        obtain rfl | hij := eq_or_ne i j
        · simp [Matrix.one_apply_eq, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
        · simp [hij, Matrix.one_apply_ne, Algebra.algebraMap_eq_smul_one]
    }
    let e5 : n = deg k k_bar A := by
      have := deg_sq_eq_dim k k_bar A
      rw [pow_two] at this
      have e6 := LinearEquiv.finrank_eq (e3.trans e4).toLinearEquiv|>.trans <|
        Module.finrank_matrix L' _ (Fin n) (Fin n)
      simp only [Module.finrank_tensorProduct, Module.finrank_self, one_mul, Fintype.card_fin,
        mul_one] at e6
      exact Nat.mul_self_inj.mp (id (this.trans e6).symm)
    exact (e3.trans e4).trans <| Matrix.reindexAlgEquiv L' _ (finCongr e5)

/-- Splitting of an algebra is preserved after extending the splitting field. -/
theorem extensionOverSplit' (k_bar : Type u) [Field k_bar] [Algebra k k_bar]
    [IsAlgClosure k k_bar] (A : Type u) [Ring A] [IsSimpleRing A] [Algebra k A]
    [Algebra.IsCentral k A] [FiniteDimensional k A] (L L' : Type u) [Field L] [Field L']
    [Algebra k L] (hA : isSplit k A L) [Algebra L L'] [Algebra k L'] [IsScalarTower k L L'] :
    isSplit k A L' := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hA
  obtain ⟨n, e⟩ := extensionOverSplit k k_bar ⟨.of k A⟩ L L' ⟨n, e⟩
  let e5 : n = deg k k_bar ⟨.of k A⟩ := by
      have := deg_sq_eq_dim k k_bar ⟨.of k A⟩
      rw [pow_two] at this
      have e6 := LinearEquiv.finrank_eq e.toLinearEquiv|>.trans <|
        Module.finrank_matrix L' _ (Fin n) (Fin n)
      simp only [Module.finrank_tensorProduct, Module.finrank_self, one_mul, Fintype.card_fin,
        mul_one] at e6
      exact Nat.mul_self_inj.mp (id (this.trans e6).symm)
  exact ⟨n, by rw[e5]; exact deg_pos k k_bar ⟨.of k A⟩, ⟨e⟩⟩
