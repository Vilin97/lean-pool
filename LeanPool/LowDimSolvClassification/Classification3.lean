/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import LeanPool.LowDimSolvClassification.GeneralResults
import LeanPool.LowDimSolvClassification.LemmasDim3
import LeanPool.LowDimSolvClassification.InstancesLowDim

open Module
open Submodule
namespace LieAlgebra.Dim3

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

lemma aux_dim_comm (dim3 : Module.finrank K L = 3) :
    Module.finrank K (commutator K L) = 0 ∨ Module.finrank K (commutator K L) = 1
    ∨ Module.finrank K (commutator K L) = 2 ∨ Module.finrank K (commutator K L) = 3 := by
  have hl : Module.finrank K (commutator K L) ≥ 0 := by apply zero_le
  have hu : Module.finrank K (commutator K L) ≤ 3 := by
    rw [← dim3]
    have : Module.Finite K L := Module.finite_of_finrank_eq_succ dim3
    apply Submodule.finrank_le
  interval_cases h : (Module.finrank K (commutator K L)) using hl, hu
  all_goals simp

/-- Characterization of the three-dimensional Heisenberg Lie algebra. -/
theorem heisenberg_iff : Nonempty (L ≃ₗ⁅K⁆ (Heisenberg K)) ↔
    Module.finrank K L = 3 ∧ Module.finrank K (commutator K L) = 1 ∧ IsTwoStepNilpotent K L := by
  rw [case1a']
  constructor
  · intro ⟨f⟩
    use Basis.ofEquivFun {f with}
    simp only [Basis.coe_ofEquivFun]
    constructor
    · change ⁅f.symm (Pi.single 1 1), f.symm (Pi.single 2 1)⁆ = f.symm (Pi.single 0 1)
      rw [← LieEquiv.map_lie f.symm]
      simp only [Heisenberg.bracket, Nat.succ_eq_add_one, Nat.reduceAdd,
        Pi.single_eq_same, mul_one, ne_eq, Fin.reduceEq, not_false_eq_true, Pi.single_eq_of_ne,
        mul_zero, sub_zero, EmbeddingLike.apply_eq_iff_eq]
      exact List.ofFn_inj.mp rfl
    · constructor
      · change ⁅f.symm (Pi.single 0 1), f.symm (Pi.single 1 1)⁆ = 0
        rw [← LieEquiv.map_lie f.symm]
        simp only [Heisenberg.bracket, Nat.succ_eq_add_one, Nat.reduceAdd, ne_eq,
          one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, Fin.reduceEq, mul_zero,
          Pi.single_eq_same, sub_self]
        rw [← LieEquiv.coe_toLinearEquiv, LinearEquiv.map_eq_zero_iff]
        change (![(0 : K), 0, 0] : Fin 3 → K) = 0
        ext i
        fin_cases i <;> simp
      · change ⁅f.symm (Pi.single 0 1), f.symm (Pi.single 2 1)⁆ = 0
        rw [← LieEquiv.map_lie f.symm]
        simp only [Heisenberg.bracket, Nat.succ_eq_add_one, Nat.reduceAdd, ne_eq,
          one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, Fin.reduceEq, mul_zero,
          Pi.single_eq_same]
        rw [← LieEquiv.coe_toLinearEquiv, LinearEquiv.map_eq_zero_iff]
        change (![(0 * 1 - 0 : K), 0, 0] : Fin 3 → K) = 0
        ext i
        fin_cases i <;> simp
  · intro ⟨B, hB01, hB02, hB12⟩
    exact ⟨{ Basis.equivFun B with
      map_lie' := by
        intro x y
        let bxy : Heisenberg K := B.equivFun ⁅x, y⁆
        let bx : Heisenberg K := B.equivFun x
        let by_ : Heisenberg K := B.equivFun y
        change bxy = ⁅bx, by_⁆
        rw [Heisenberg.bracket]
        change bxy = ![bx 1 * by_ 2 - by_ 1 * bx 2, (0 : K), (0 : K)]
        simp only [
          Basis.equivFun_apply, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, bxy, bx, by_]
        rw [Basis.repr_fin_three B x, Basis.repr_fin_three B y]
        simp only [lie_add, lie_smul, add_lie, smul_lie, lie_self, smul_zero,
          zero_add, smul_add, add_zero, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul,
          Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Pi.add_apply, ne_eq,
            not_false_eq_true, Finsupp.single_eq_of_ne, Finsupp.single_eq_same,
          Fin.reduceEq]
        rw [← lie_skew (B 1) (B 0), ← lie_skew (B 2) (B 0), ← lie_skew (B 2) (B 1)]
        rw [hB01, hB02, hB12]
        funext i
        simp only [neg_zero, map_zero, Finsupp.coe_zero, smul_zero, add_zero,
          map_neg, Basis.repr_self, Finsupp.coe_neg, smul_neg, zero_add, Pi.add_apply,
          Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
        fin_cases i
        · simp only [Fin.zero_eta, Finsupp.single_eq_same, mul_one,
            Matrix.cons_val_zero]
          ring
        · simp [Finsupp.single, Matrix.cons_val_one, Matrix.cons_val_zero]
        · simp [Finsupp.single, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    }⟩

/-- Characterization of the three-dimensional Lie algebra `AffinePlusAbelian`. -/
theorem affinePlusAbelian_iff : Nonempty (L ≃ₗ⁅K⁆ (AffinePlusAbelian K)) ↔
    Module.finrank K L = 3 ∧ Module.finrank K (commutator K L) = 1 ∧ ¬IsTwoStepNilpotent K L := by
  rw [case1b']
  constructor
  · intro ⟨f⟩
    use Basis.ofEquivFun {f with}
    simp only [Basis.coe_ofEquivFun]
    constructor
    · change ⁅f.symm (Pi.single 0 1), f.symm (Pi.single 1 1)⁆ = 0
      rw [← LieEquiv.map_lie f.symm]
      simp only [AffinePlusAbelian.bracket, Nat.succ_eq_add_one, Nat.reduceAdd,
          ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, Pi.single_eq_same,
          Fin.reduceEq, mul_zero, sub_self]
      rw [← LieEquiv.coe_toLinearEquiv, LinearEquiv.map_eq_zero_iff]
      change (![(0 : K), 0, 0] : Fin 3 → K) = 0
      ext i
      fin_cases i <;> simp
    · constructor
      · change ⁅f.symm (Pi.single 0 1), f.symm (Pi.single 2 1)⁆ = 0
        rw [← LieEquiv.map_lie f.symm]
        simp only [AffinePlusAbelian.bracket, Nat.succ_eq_add_one, Nat.reduceAdd,
          ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, Pi.single_eq_same, mul_one,
          Fin.reduceEq, mul_zero, sub_self]
        rw [← LieEquiv.coe_toLinearEquiv, LinearEquiv.map_eq_zero_iff]
        change (![(0 : K), 0, 0] : Fin 3 → K) = 0
        ext i
        fin_cases i <;> simp
      · change ⁅f.symm (Pi.single 1 1), f.symm (Pi.single 2 1)⁆ = f.symm (Pi.single 1 1)
        rw [← LieEquiv.map_lie f.symm]
        simp only [AffinePlusAbelian.bracket, Nat.succ_eq_add_one, Nat.reduceAdd,
          Pi.single_eq_same, mul_one, ne_eq, Fin.reduceEq, not_false_eq_true, Pi.single_eq_of_ne,
          mul_zero, sub_zero, EmbeddingLike.apply_eq_iff_eq]
        exact List.ofFn_inj.mp rfl
  · intro ⟨B, hB01, hB02, hB12⟩
    exact ⟨{ Basis.equivFun B with
      map_lie' := by
        intro x y
        let bxy : AffinePlusAbelian K := B.equivFun ⁅x, y⁆
        let bx : AffinePlusAbelian K := B.equivFun x
        let by_ : AffinePlusAbelian K := B.equivFun y
        change bxy = ⁅bx, by_⁆
        rw [AffinePlusAbelian.bracket]
        change bxy = ![(0 : K), bx 1 * by_ 2 - by_ 1 * bx 2, (0 : K)]
        simp only [Fin.isValue, Basis.equivFun_apply, Nat.succ_eq_add_one, Nat.reduceAdd,
          bxy, bx, by_]
        rw [Basis.repr_fin_three B x, Basis.repr_fin_three B y]
        simp only [Fin.isValue, lie_add, lie_smul, add_lie, smul_lie, lie_self, smul_zero,
          zero_add, smul_add, add_zero, map_add, map_smul, Finsupp.coe_add,
          Finsupp.coe_smul, Basis.repr_self,
          Finsupp.smul_single, smul_eq_mul, mul_one, Pi.add_apply, ne_eq,
          not_false_eq_true, Finsupp.single_eq_of_ne, Finsupp.single_eq_same, Fin.reduceEq]
        rw [← lie_skew (B 1) (B 0), ← lie_skew (B 2) (B 0), ← lie_skew (B 2) (B 1)]
        rw [hB01, hB02, hB12]
        funext i
        simp only [Fin.isValue, neg_zero, map_zero, Finsupp.coe_zero, smul_zero, add_zero,
          map_neg, Basis.repr_self, Finsupp.coe_neg, smul_neg, zero_add, Pi.add_apply,
          Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
        fin_cases i
        · simp [Finsupp.single, Matrix.cons_val_zero]
        · simp [Finsupp.single, Matrix.cons_val_one, Matrix.cons_val_zero]; ring
        · simp [Finsupp.single, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    }⟩

/-- Choice of basis for the three-dimensional Lie algebra `Hyperbolic`. -/
theorem hyperbolic_iff : Nonempty (L ≃ₗ⁅K⁆ (Hyperbolic K)) ↔
    ∃ B : Basis (Fin 3) K L, ⁅B 0, B 1⁆ = B 1 ∧ ⁅B 0, B 2⁆ = B 2 ∧ ⁅B 1, B 2⁆ = 0 := by
  constructor
  · intro ⟨f⟩
    use Basis.ofEquivFun {f with}
    simp only [Basis.coe_ofEquivFun]
    constructor
    · change ⁅f.symm (Pi.single 0 1), f.symm (Pi.single 1 1)⁆ = f.symm (Pi.single 1 1)
      rw [← LieEquiv.map_lie f.symm]
      simp only [Hyperbolic.bracket, Nat.succ_eq_add_one, Nat.reduceAdd,
        Pi.single_eq_same, mul_one, ne_eq, Fin.reduceEq, not_false_eq_true, Pi.single_eq_of_ne,
        mul_zero, sub_zero, EmbeddingLike.apply_eq_iff_eq]
      exact List.ofFn_inj.mp rfl
    · constructor
      · change ⁅f.symm (Pi.single 0 1), f.symm (Pi.single 2 1)⁆ = f.symm (Pi.single 2 1)
        rw [← LieEquiv.map_lie f.symm]
        simp only [Hyperbolic.bracket, Nat.succ_eq_add_one, Nat.reduceAdd,
          Pi.single_eq_same, mul_one, ne_eq, Fin.reduceEq, not_false_eq_true, Pi.single_eq_of_ne,
          mul_zero, sub_zero, EmbeddingLike.apply_eq_iff_eq]
        exact List.ofFn_inj.mp rfl
      · change ⁅f.symm (Pi.single 1 1), f.symm (Pi.single 2 1)⁆ = 0
        rw [← LieEquiv.map_lie f.symm]
        simp only [Hyperbolic.bracket, Nat.succ_eq_add_one, Nat.reduceAdd,
          ne_eq, not_false_eq_true, Pi.single_eq_of_ne, Pi.single_eq_same, mul_one,
          Fin.reduceEq, mul_zero, sub_self]
        rw [← LieEquiv.coe_toLinearEquiv, LinearEquiv.map_eq_zero_iff]
        change (![(0 : K), 0, 0] : Fin 3 → K) = 0
        ext i
        fin_cases i <;> simp
  · intro ⟨B, hB01, hB02, hB12⟩
    exact ⟨{ Basis.equivFun B with
      map_lie' := by
        intro x y
        let bxy : Hyperbolic K := B.equivFun ⁅x, y⁆
        let bx : Hyperbolic K := B.equivFun x
        let by_ : Hyperbolic K := B.equivFun y
        change bxy = ⁅bx, by_⁆
        rw [Hyperbolic.bracket]
        change bxy = ![(0 : K), bx 0 * by_ 1 - by_ 0 * bx 1, bx 0 * by_ 2 - by_ 0 * bx 2]
        simp only [Fin.isValue, Basis.equivFun_apply, Nat.succ_eq_add_one, Nat.reduceAdd,
          bxy, bx, by_]
        rw [Basis.repr_fin_three B x, Basis.repr_fin_three B y]
        simp only [Fin.isValue, lie_add, lie_smul, add_lie, smul_lie, lie_self, smul_zero,
          zero_add, smul_add, add_zero, map_add, map_smul, Finsupp.coe_add,
          Finsupp.coe_smul, Basis.repr_self,
          Finsupp.smul_single, smul_eq_mul, mul_one, Pi.add_apply, Finsupp.single_eq_same, ne_eq,
          one_ne_zero, not_false_eq_true, Finsupp.single_eq_of_ne, Fin.reduceEq, zero_ne_one]
        rw [← lie_skew (B 1) (B 0), ← lie_skew (B 2) (B 0), ← lie_skew (B 2) (B 1)]
        rw [hB01, hB02, hB12]
        funext i
        simp only [Fin.isValue, map_neg, Basis.repr_self, Finsupp.coe_neg, smul_neg, neg_zero,
          map_zero, Finsupp.coe_zero, smul_zero, add_zero, Pi.add_apply, Pi.neg_apply,
          Pi.smul_apply, smul_eq_mul]
        fin_cases i
        · simp [Finsupp.single, Matrix.cons_val_zero]
        · simp [Finsupp.single, Matrix.cons_val_one, Matrix.cons_val_zero]; ring
        · simp [Finsupp.single, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; ring
    }⟩

/-- Choice of basis for the three-dimensional Lie algebra `Family`. -/
theorem family_iff (α β : K) : Nonempty (L ≃ₗ⁅K⁆ (Family K α β)) ↔
    ∃ B : Basis (Fin 3) K L, ⁅B 0, B 1⁆ = B 2 ∧ ⁅B 1, B 2⁆ = 0 ∧ ⁅B 0,
      B 2⁆ = α • B 1 + β • B 2 := by
  constructor
  · intro ⟨f⟩
    use Basis.ofEquivFun {f with}
    simp only [Basis.coe_ofEquivFun]
    constructor
    · change ⁅f.symm (Pi.single 0 1), f.symm (Pi.single 1 1)⁆ = f.symm (Pi.single 2 1)
      rw [← LieEquiv.map_lie f.symm]
      simp only [Family.bracket, Nat.succ_eq_add_one, Nat.reduceAdd, Pi.single_eq_same, ne_eq,
        Fin.reduceEq, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, sub_zero, mul_one,
        EmbeddingLike.apply_eq_iff_eq, zero_mul, zero_add]
      exact List.ofFn_inj.mp rfl
    · constructor
      · change ⁅f.symm (Pi.single 1 1), f.symm (Pi.single 2 1)⁆ = 0
        rw [← LieEquiv.map_lie f.symm]
        simp only [Family.bracket, Nat.succ_eq_add_one, Nat.reduceAdd,
          ne_eq, not_false_eq_true, Pi.single_eq_of_ne, Pi.single_eq_same, mul_one,
          Fin.reduceEq, mul_zero, sub_self]
        rw [← LieEquiv.coe_toLinearEquiv, LinearEquiv.map_eq_zero_iff]
        change (![0, 0 * α, 0 * β + 0 - 0] : Fin 3 → K) = 0
        ext i
        fin_cases i <;> simp
      · change ⁅f.symm (Pi.single 0 1), f.symm (Pi.single 2 1)⁆ =
          α • f.symm (Pi.single 1 1) + β • f.symm (Pi.single 2 1)
        have key : ∀ (e0 e1 e2 : Family K α β), e0 = Pi.single 0 1 → e1 = Pi.single 1 1 →
            e2 = Pi.single 2 1 → ⁅e0, e2⁆ = α • e1 + β • e2 := by
          intro e0 e1 e2 he0 he1 he2
          subst he0
          subst he1
          subst he2
          rw [Family.bracket]
          funext i
          change (![0, _, _] : Fin 3 → K) i = (α • (Pi.single 1 1 : Fin 3 → K)) i
            + (β • (Pi.single 2 1 : Fin 3 → K)) i
          fin_cases i
          · simp
          · simp
          · simp
        rw [← LieEquiv.map_lie f.symm,
          key (Pi.single 0 1) (Pi.single 1 1) (Pi.single 2 1) rfl rfl rfl,
          map_add, map_smul, map_smul]
  · intro ⟨B, hB01, hB12, hB02⟩
    exact ⟨{ Basis.equivFun B with
      map_lie' := by
        intro x y
        let bxy : Family K α β := B.equivFun ⁅x, y⁆
        let bx : Family K α β := B.equivFun x
        let by_ : Family K α β := B.equivFun y
        change bxy = ⁅bx, by_⁆
        rw [Family.bracket]
        change bxy = ![(0 : K), (bx 0 * by_ 2 - bx 2 * by_ 0) * α,
          (bx 0 * by_ 2 - bx 2 * by_ 0) * β + bx 0 * by_ 1 - bx 1 * by_ 0]
        simp only [Fin.isValue, Basis.equivFun_apply, Nat.succ_eq_add_one, Nat.reduceAdd,
          bxy, bx, by_]
        rw [Basis.repr_fin_three B x, Basis.repr_fin_three B y]
        simp only [Fin.isValue, lie_add, lie_smul, add_lie, smul_lie, lie_self, smul_zero,
          zero_add, smul_add, add_zero, map_add, map_smul, Finsupp.coe_add,
          Finsupp.coe_smul, Basis.repr_self,
          Finsupp.smul_single, smul_eq_mul, mul_one, Pi.add_apply, Finsupp.single_eq_same,
          ne_eq, one_ne_zero, not_false_eq_true, Finsupp.single_eq_of_ne, Fin.reduceEq, zero_ne_one]
        rw [← lie_skew (B 1) (B 0), ← lie_skew (B 2) (B 0), ← lie_skew (B 2) (B 1)]
        rw [hB01, hB02, hB12]
        funext i
        simp only [Fin.isValue, map_neg, Basis.repr_self, Finsupp.coe_neg, smul_neg, smul_eq_mul,
          neg_zero, map_zero, Finsupp.coe_zero,
          smul_zero, add_zero, Pi.add_apply, Pi.neg_apply, Pi.smul_apply]
        fin_cases i
        · simp [Finsupp.single, Matrix.cons_val_zero]
        · simp [Finsupp.single, Matrix.cons_val_one, Matrix.cons_val_zero]; ring
        · simp [Finsupp.single, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; ring
    }⟩

theorem classification (dim3 : finrank K L = 3) (hs : IsSolvable L) :
    Nonempty (L ≃ₗ⁅K⁆ (Abelian K)) ∨
    Nonempty (L ≃ₗ⁅K⁆ (Heisenberg K)) ∨
    Nonempty (L ≃ₗ⁅K⁆ (AffinePlusAbelian K)) ∨
    Nonempty (L ≃ₗ⁅K⁆ (Hyperbolic K)) ∨
    (∃ α, α ≠ 0 ∧ Nonempty (L ≃ₗ⁅K⁆ (Family K α 0))) ∨
    (∃ α, α ≠ 0 ∧ Nonempty (L ≃ₗ⁅K⁆ (Family K α 1))) := by
  have : FiniteDimensional K L := by
    apply FiniteDimensional.of_finrank_pos
    rw [dim3]
    norm_num
  rcases aux_dim_comm dim3 with dc₀|dc₁|dc₂|dc₃
  · left -- dim commutator is 0
    rw [LieAlgebra.abelian_iff_dim_comm_zero] at dc₀
    have := finite_of_finrank_eq_succ dim3
    have B := finBasisOfFinrankEq K L dim3
    constructor
    exact ({ Basis.equivFun B with
      map_lie' := by
        intro x y
        simp only [trivial_lie_zero, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          LinearEquiv.coe_coe, Basis.equivFun_apply, map_zero]
        rfl
    })
  · right -- dim commutator is 1
    by_cases cc : IsTwoStepNilpotent K L
    · left --case1a' : commutator contained in center
      exact heisenberg_iff.mpr ⟨dim3, dc₁, cc⟩
    · right
      left -- case1b : commutator NOT contained in center
      exact affinePlusAbelian_iff.mpr ⟨dim3, dc₁, cc⟩
  · right
    right
    right -- dim commutator is 2
    obtain (⟨B, hB⟩ | ⟨B, hB01, hB02, α, hα, hB12⟩ | ⟨B, hB01, hB02, α, hα,
      hB12⟩) := case2.mp ⟨dim3, dc₂⟩
    · left -- Hyperbolic
      exact hyperbolic_iff.mpr ⟨B, hB⟩
    · right
      left -- Family_α_β α 0
      use α, hα
      rw [family_iff α 0]
      use B, hB01, hB02
      rw [zero_smul, add_zero]
      exact hB12
    · right
      right -- Family_α_β α 1
      use α, hα
      rw [family_iff α 1]
      use B, hB01, hB02
      rw [one_smul]
      exact hB12
  · have : Nontrivial L := nontrivial_of_finrank_pos (by exact Nat.lt_of_sub_eq_succ dim3)
    have := derivedSeries_lt_top_of_solvable K L
    rw [← dim3] at dc₃
    apply eq_top_of_finrank_eq at dc₃
    have : (derivedSeries K L 1).toSubmodule < ⊤ := by
      assumption
    rw [← dc₃] at this
    unfold commutator at this
    apply (lt_self_iff_false _).mp at this
    contradiction

namespace Family

/-- Forward direction of `Family.iso_iff`. Extracted as a private helper to keep the proof of
`iso_iff` itself within the per-proof size limit. -/
private lemma iso_iff_mp {α α' β β' : K} (hα : α ≠ 0) (hα' : α' ≠ 0)
    (f : Family K α β ≃ₗ⁅K⁆ Family K α' β') :
    ∃ (γ : Kˣ), α = γ^2 * α' ∧ β = γ * β' := by
  let v : Family K α' β' := f ![1,0,0]
  -- f preserves the commutator
  have fcc : LieIdeal.map f (LieAlgebra.commutator K (Family K α β)) = (LieAlgebra.commutator K
      (Family K α' β')) := LieEquiv.commutator_map f
  have finvcc : LieIdeal.map f.symm.toLieHom (commutator K (Family K α' β')) = commutator K
      (Family K α β) := LieEquiv.commutator_map f.symm
  -- the inverse of f preserves the commutator as well
  have fsymmv : f.symm.toLieHom v = ![1, 0, 0] := by
    simp only [LieEquiv.symm_apply_apply, v, LieEquiv.coe_toLieHom]
  have b0notinc : ![1,0,0] ∉ commutator K (Family K α β) := by
    intro hb0
    have hb0S : ![1, 0, 0] ∈ (commutator K (Family K α β)).toSubmodule := by
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
      assumption
    rw [Family.commutator_is_span_e₂e₃ hα] at hb0S
    have hb0S' := (@Submodule.mem_span_pair K (Family K α β) _ _ _ _ _ ![1,0,0]).mp hb0S
    let ⟨a, b, h⟩ := hb0S'
    unfold Family.e₂ Family.e₃ at h
    have h : (![(0 : K), a, b] : Fin 3 → K) = ![1, 0, 0] := by
      rw [← h]
      change (![(0 : K), a, b] : Fin 3 → K) =
        a • (![0, 1, 0] : Fin 3 → K) + b • (![0, 0, 1] : Fin 3 → K)
      ext i
      fin_cases i <;> simp [Matrix.smul_cons, Matrix.smul_empty]
    have : ![0, a, b] 0 = ![1, 0, 0] 0 := by
      rw [h]
    simp at this
  have vnotinc : v ∉ commutator K (Family K α' β') := by
    intro ha
    have := LieIdeal.mem_map (f := f.symm.toLieHom) (I := commutator K (Family K α' β')) ha
    rw [fsymmv, finvcc] at this
    exact (b0notinc this)
  have v0n0 : v 0 ≠ 0 := by
    intro hv0
    have : v ∈ span K {Family.e₂, Family.e₃} := by
      apply (@Submodule.mem_span_pair K (Family K α' β') _ _ _ _ _ v).mpr
      use v 1
      use v 2
      unfold Family.e₂ Family.e₃
      change v 1 • (![0, 1, 0] : Fin 3 → K) + v 2 • (![0, 0, 1] : Fin 3 → K) = v
      funext j
      fin_cases j <;> simp [Matrix.smul_cons, Matrix.smul_empty, hv0]
    rw [← Family.commutator_is_span_e₂e₃ hα'] at this
    exact (vnotinc this)
  let adb0' : End K (Family K α' β') := Family.ade₁
  let adb0 : End K (Family K α β) := Family.ade₁
  let adv : End K (Family K α' β') := ad K (Family K α' β') v
  let adv_restr : (commutator K (Family K α' β')) →ₗ[K] (commutator K (Family K α' β'))
      := Family.ad_restr v
  have v0b0v (u : commutator K (Family K α' β')) : ((v 0) •
      ((Family.ade₁_restr α' β') u)) = adv_restr u := by
    have : u.val 0 = 0 := by
      obtain ⟨u, hu⟩ := u
      have u_in_span : u ∈ span K {Family.e₂, Family.e₃} := by
        rw [← Family.commutator_is_span_e₂e₃ hα']
        exact hu
      let ⟨a, b, h⟩ := mem_span_pair.mp u_in_span
      have w := h
      unfold Family.e₂ Family.e₃ at h
      have h : (![(0 : K), a, b] : Fin 3 → K) = u := by
        rw [← h]
        change (![(0 : K), a, b] : Fin 3 → K) =
          a • (![0, 1, 0] : Fin 3 → K) + b • (![0, 0, 1] : Fin 3 → K)
        ext i
        fin_cases i <;> simp [Matrix.smul_cons, Matrix.smul_empty]
      symm at h
      apply_fun (fun x => x 0) at h
      exact h
    unfold Family.ade₁_restr adv_restr
    rw [Family.ad_restr_apply, Family.ad_restr_apply]
    rw [@SetLike.mk_smul_of_tower_mk]
    refine Subtype.mk_eq_mk.mpr ?_
    unfold Family.adjoint
    rw [ad_apply, ad_apply]
    rw [Family.bracket, Family.bracket]
    unfold Family.e₁
    simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_zero, one_mul,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, zero_mul, sub_zero,
      Matrix.cons_val_one]
    change v 0 • (![(0 : K), u.val 2 * α', u.val 2 * β' + u.val 1] : Fin 3 → K) =
      ![0, (v 0 * u.val 2 - v 2 * u.val 0) * α',
        (v 0 * u.val 2 - v 2 * u.val 0) * β' + v 0 * u.val 1 - v 1 * u.val 0]
    ext i
    fin_cases i <;>
      simp [this]
    · ring
    ring
  let B_basis' : Basis (Fin 2) K (commutator K (Family K α' β')) := commutatorBasis α' β' hα'
  let M_adb0'_restr : Matrix (Fin 2) (Fin 2) K := LinearMap.toMatrix (B_basis') (B_basis')
      (Family.ade₁_restr α' β')
  set M_adv_restr : Matrix (Fin 2) (Fin 2) K := LinearMap.toMatrix (B_basis')
      (B_basis') adv_restr with hM_adv_restr
  have eq_Matrix : (v 0) • M_adb0'_restr = M_adv_restr := by
    ext (i : Fin 2) (j : Fin 2)
    simp only [Matrix.smul_apply]
    unfold M_adb0'_restr M_adv_restr
    simp only [LinearMap.toMatrix_apply]
    have : ((v 0) • (Family.ade₁_restr α' β' (B_basis' j))) = adv_restr (B_basis' j) := by
      exact v0b0v (B_basis' j)
    rw [← this]
    rw [@LinearEquiv.map_smul]
    rw [← Pi.smul_apply]
    simp only [Fin.isValue, Pi.smul_apply, smul_eq_mul, Finsupp.coe_smul]
  have det_adv_restr_eq : LinearMap.det adv_restr = -((v 0)^2 * α') := by
    rw [← LinearMap.det_toMatrix (ι := Fin 2) (f := (adv_restr)) B_basis']
    rw [← hM_adv_restr]
    rw [← eq_Matrix]
    rw [Matrix.det_smul]
    rw [Fintype.card_fin]
    unfold M_adb0'_restr
    unfold B_basis'
    rw [Family.M_is_ade₁_restr]
    rw [Family.M_det]
    ring_nf
  have tr_adv_restr_eq : LinearMap.trace K _ adv_restr = (v 0) * β' := by
    rw [LinearMap.trace_eq_matrix_trace K B_basis' adv_restr]
    rw [← hM_adv_restr]
    rw [← eq_Matrix]
    rw [Matrix.trace_smul]
    unfold M_adb0'_restr
    unfold B_basis'
    rw [Family.M_is_ade₁_restr]
    rw [Family.M_trace]
    simp only [smul_eq_mul]
  let B_basis : Basis (Fin 2) K (commutator K (Family K α β)) := commutatorBasis α β hα
  let f_restr := LieEquiv.commutator_equiv f
  have conjad : f_restr ∘ₗ Family.ade₁_restr α β ∘ₗ f_restr.symm = adv_restr := by
    ext x
    unfold Family.ade₁_restr
    rw [LinearMap.coe_comp]
    rw [LinearEquiv.coe_coe, Function.comp_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [Family.ad_restr_apply, Family.ad_restr_apply]
    unfold Family.adjoint
    simp only [ad_apply]
    unfold f_restr
    rw [LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
    rw [LieEquiv.commutator_equiv_apply]
    simp only [LieEquiv.map_lie]
    rw [LieEquiv.coe_toLinearEquiv]
    rw [LieEquiv.commutator_equiv_symm]
    norm_cast
    congr
    rw [LieEquiv.commutator_equiv_apply]
    rw [LieEquiv.apply_symm_apply]
  have det_adv_restr_eq_det_adb0 : LinearMap.det adv_restr = LinearMap.det
      (Family.ade₁_restr α β) := by
    rw [← conjad]
    apply LinearMap.det_conj
  have tr_adv_restr_eq_tr_adb0 : LinearMap.trace K _ adv_restr = LinearMap.trace _ _
      (Family.ade₁_restr α β) := by
    rw [← conjad]
    exact LinearMap.trace_conj' (Family.ade₁_restr α β) f_restr.toLinearEquiv
  use (Units.mk0 (v 0) v0n0)
  simp only [Fin.isValue, Units.val_mk0]
  rw [← neg_eq_iff_eq_neg (b := (v 0)^2 * α')] at det_adv_restr_eq
  rw [← det_adv_restr_eq, ← tr_adv_restr_eq]
  rw [det_adv_restr_eq_det_adb0, tr_adv_restr_eq_tr_adb0]
  rw [Family.det_ade₁, Family.tr_ade₁]
  · simp only [neg_neg, and_self]
  · exact hα
  exact hα

theorem iso_iff {α α' β β' : K} (hα : α ≠ 0) (hα' : α' ≠ 0) :
    Nonempty ((Family K α β) ≃ₗ⁅K⁆ Family K α' β') ↔
    ∃ (γ : Kˣ), α = γ^2 * α' ∧ β = γ * β' := by
  constructor
  · intro ⟨f⟩
    exact iso_iff_mp hα hα' f
  · intro ⟨γ, hα, hβ⟩
    constructor
    exact {
      toFun := fun l => ![γ * l 0, l 1, γ * l 2]
      map_add' := by
        intro x y
        let x' : Fin 3 → K := x
        let y' : Fin 3 → K := y
        change (![γ * (x' + y') 0, (x' + y') 1, γ * (x' + y') 2] : Fin 3 → K) =
          (![γ * x' 0, x' 1, γ * x' 2] : Fin 3 → K) +
            (![γ * y' 0, y' 1, γ * y' 2] : Fin 3 → K)
        rw [Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.cons_add_cons,
          Matrix.empty_add_empty]
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Pi.add_apply,
          Matrix.vecCons_inj, and_true, true_and]; refine ⟨?_, ?_⟩ <;> ring
      map_smul' := by
        intro m x
        let x' : Fin 3 → K := x
        change (![γ * (m • x') 0, (m • x') 1, γ * (m • x') 2] : Fin 3 → K) =
          m • (![γ * x' 0, x' 1, γ * x' 2] : Fin 3 → K)
        rw [Matrix.smul_cons, Matrix.smul_cons, Matrix.smul_cons, Matrix.smul_empty]
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Pi.smul_apply, smul_eq_mul,
          Matrix.vecCons_inj, and_true, true_and]; refine ⟨?_, ?_⟩ <;> ring
      map_lie' := by
        intro x y
        simp only [Fin.isValue, bracket, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_zero,
          mul_zero, Matrix.cons_val_one, Matrix.cons_val]
        rw [hα, hβ]
        ring_nf
      invFun := fun l => ![γ⁻¹ * l 0, l 1, γ⁻¹ * l 2]
      left_inv := by
        intro x
        change (![γ⁻¹ * (γ * x 0), x 1, γ⁻¹ * (γ * x 2)] : Fin 3 → K) = x
        funext j
        fin_cases j <;> simp []
      right_inv := by
        intro x
        change (![γ * (γ⁻¹ * x 0), x 1, γ * (γ⁻¹ * x 2)] : Fin 3 → K) = x
        funext j
        fin_cases j <;> simp []
    }

theorem not_iso_hyperbolic {α β : K} (hα : α ≠ 0) : IsEmpty (Family K α β ≃ₗ⁅K⁆ Hyperbolic K) := by
  constructor
  intro f
  let f' := LieEquiv.commutator_equiv f
  --f(e₁) = t e₁ + w, with w in commutator, t ≠ 0
  have hfe₁ : ∃ (t : K) (w : Hyperbolic K), f Family.e₁ = t • Hyperbolic.e₁ + w ∧
      w ∈ commutator K (Hyperbolic K) := by
    have fe₁_repr := Basis.repr_fin_three Hyperbolic.stdBasis (f Family.e₁)
    rw [add_assoc, Hyperbolic.stdBasis₁, Hyperbolic.stdBasis₂, Hyperbolic.stdBasis₃] at fe₁_repr
    use (Hyperbolic.stdBasis.repr (f Hyperbolic.e₁)) 0
    use ((Hyperbolic.stdBasis.repr (f Hyperbolic.e₁)) 1 • Hyperbolic.e₂ +
      (Hyperbolic.stdBasis.repr (f Hyperbolic.e₁)) 2 • Hyperbolic.e₃)
    constructor
    · assumption
    · rw [Hyperbolic.commutator_repr]
      apply exists_apply_eq_apply2
  obtain ⟨t, w, hfe₁, wcomm⟩ := hfe₁
  have tne0 : t ≠ 0 := by
    intro h
    rw [h, zero_smul, zero_add] at hfe₁
    rw [← hfe₁] at wcomm
    apply Family.e₁_not_in_comm (β := β) hα
    let e₁up := f.symm.commutator_equiv ⟨f Family.e₁, wcomm⟩
    have : e₁up.val = Family.e₁ := by
      unfold e₁up
      rw [LieEquiv.commutator_equiv_apply]
      simp only [LieEquiv.symm_apply_apply]
    rw [← this]
    exact e₁up.prop
  --restrict ad(e₁) and ad(f(e₁)) to the respective commutators.
  let ade₁ := Family.ade₁_restr α β
  let adfe₁ := Hyperbolic.ad_restr (f Family.e₁)
  have ad_conj : adfe₁ = f' ∘ₗ ade₁ ∘ₗ f'.symm := by
    ext x
    rw [LinearMap.coe_comp]
    rw [LinearEquiv.coe_coe, Function.comp_apply, LinearMap.coe_comp, Function.comp_apply]
    unfold adfe₁ ade₁ Family.ade₁_restr
    rw [Hyperbolic.ad_restr_apply, Family.ad_restr_apply]
    unfold Hyperbolic.adjoint Family.adjoint
    simp only [ad_apply]
    unfold f'
    rw [LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
    rw [LieEquiv.commutator_equiv_apply]
    simp only [LieEquiv.map_lie]
    congr
    rw [LieEquiv.coe_toLinearEquiv, LieEquiv.commutator_equiv_symm, LieEquiv.commutator_equiv_apply,
      LieEquiv.apply_symm_apply]
  have adfe₁_id : adfe₁ = t • LinearMap.id := by
    unfold adfe₁
    rw [hfe₁, Hyperbolic.ad_restr_add, Hyperbolic.ad_restr_smul, Hyperbolic.ade₁_restr_id,
      Hyperbolic.ad_comm_restr wcomm, add_zero]
  have ade₁_id : ade₁ = t • LinearMap.id := by
    rw [ad_conj, ← LinearMap.comp_assoc, LieEquiv.symm_toLinearEquiv,
      ← LinearEquiv.conj_apply] at adfe₁_id
    calc
      ade₁ = f'.toLinearEquiv.symm.conj (f'.toLinearEquiv.conj ade₁)
          := by rw [← LinearEquiv.conj_symm, LinearEquiv.symm_apply_apply]
      _ = f'.toLinearEquiv.symm.conj (t • LinearMap.id) := by congr
      _ = t • f'.toLinearEquiv.symm.conj (LinearMap.id) := by rw [map_smul]
      _ = t • LinearMap.id := by rw [LinearEquiv.conj_id]
  -- we show that ⁅Family.e₁, Family.e₂⁆ = t • Family.e₂
  have : ade₁ ⟨Family.e₂, Family.e₂_in_comm (hα := hα)⟩ = t • ⟨Family.e₂,
    Family.e₂_in_comm (hα := hα)⟩ := by
    rw [ade₁_id]
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, SetLike.mk_smul_mk]
  unfold ade₁ Family.ade₁_restr at this
  rw [Family.ad_restr_apply] at this
  simp only [SetLike.mk_smul_mk, Subtype.mk.injEq] at this
  unfold Family.adjoint at this
  --this leads to a contradiction because ⁅Family.e₁, Family.e₂⁆ = Family.e₃
  rw [ad_apply, Family.e₃_bracket, Family.e₂_def, Family.e₃_def] at this
  unfold Family at this
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.smul_cons, smul_eq_mul, mul_zero, mul_one,
    Matrix.smul_empty] at this
  apply funext_iff.mp at this
  specialize this 2
  simp only [Fin.isValue, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons,
    Matrix.head_cons, one_ne_zero] at this

/-the following are corollaries of the above-/
theorem iso_1 {α α' : K} (hα : α ≠ 0) (hα' : α' ≠ 0) : (Family K α 1 ≃ₗ⁅K⁆ Family K α' 1) →
    α = α' := by
  intro f
  let ⟨γ, ha, hb⟩ := (Family.iso_iff hα hα').mp ⟨f⟩
  simp only [mul_one] at hb
  rw [← hb] at ha
  simp only [one_pow, one_mul] at ha
  exact ha

theorem not_iso_0_1 {α α' : K} (hα : α ≠ 0) (hα' : α' ≠ 0) : IsEmpty
    (Family K α 0 ≃ₗ⁅K⁆ Family K α' 1) := by
  rw [isEmpty_iff]
  intro f
  obtain ⟨γ, _, hβ⟩ := (Family.iso_iff hα' hα).mp ⟨f.symm⟩
  simp only [ne_eq, mul_zero, one_ne_zero] at *

theorem iso_0 {α α' : K} (hα : α ≠ 0) (hα' : α' ≠ 0) : (Family K α 0 ≃ₗ⁅K⁆ Family K α' 0) →
    ∃ (γ : K), α = γ^2 * α' := by
  intro f
  let ⟨γ, ha, hb⟩ := (Family.iso_iff hα hα').mp ⟨f⟩
  use γ

end Family

end Dim3

end LieAlgebra
