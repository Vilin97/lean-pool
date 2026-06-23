/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Abelian
import LeanPool.LowDimSolvClassification.InstancesLowDim
import LeanPool.LowDimSolvClassification.GeneralResults
import LeanPool.LowDimSolvClassification.Classification1

/-!
# LeanPool.LowDimSolvClassification.Classification2
-/

open Module
open Submodule
namespace LieAlgebra

section classification_dim_2

namespace Dim2

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

lemma abelian_or_basis (h : finrank K L = 2) :
  IsLieAbelian L ∨ (∃ B : Basis (Fin 2) K L, ⁅B 0, B 1⁆ = B 1) := by
  by_cases s : IsLieAbelian L
  · left
    assumption
  · right
    simp only [IsLieAbelian] at s
    have t : (∃ X Y : L, ⁅X,Y⁆ ≠ 0) := by
      have u : ¬ (∀ X Y : L, ⁅X,Y⁆ = 0) := fun H ↦ s ⟨ H ⟩
      push Not at u
      assumption
    rcases t with ⟨x, y, hxy⟩
    have ⟨S_b, S_b0, S_b1⟩ := basis_of_bracket_ne_zero h _ _ hxy
    have ⟨ α , β , pf ⟩ : ∃ (α β : K), ⁅ x , y ⁆ = α • x + β • y := by
      let c := S_b.linearCombination_repr ⁅ x , y ⁆
      let αβ := S_b.repr ⁅ x , y ⁆
      exists (αβ 0),(αβ 1)
      rw [Finsupp.linearCombination_apply] at c
      rw [← c, Finsupp.sum_fintype]
      · rw [Fin.sum_univ_two, S_b0, S_b1]
      · simp
    have ⟨ X , Y, pf1, pf2⟩ : ∃ X Y : L, ⁅X , Y⁆ = Y ∧ Y ≠ 0 := by
      by_cases hα : (α = 0)
      · exists (1 / β) • x, y
        have β_ne_zero : β ≠ 0 := by
          intro hβ
          rw [hα, hβ] at pf
          apply hxy
          simp at pf
          assumption
        constructor
        · calc ⁅(1 / β) • x, y⁆ = (1 / β) • ⁅x, y⁆  := by simp
              _ = ((1 / β) * β) • y := by rw [pf, hα]; simp [← smul_assoc]
              _ = y := by rw [one_div_mul_cancel β_ne_zero]; simp
        · rw [hα] at pf
          simp only [zero_smul, zero_add] at pf
          rw [pf] at hxy
          exact right_ne_zero_of_smul hxy
      · exists -(1 / α) • y, x + (β / α) • y
        constructor
        · calc ⁅-(1 / α) • y, x + (β / α) • y⁆ = (-(1 / α)) • (-1 : K) • ⁅x, y⁆ := by simp
              _ = ((-(1 / α)) * (-1)) • ⁅x, y⁆ := by rw [← mul_smul]
              _ = (1 / α) • ⁅x, y⁆ := by simp
              _ = (1 / α) • (α • x + β • y) := by rw [pf]
              _ = ((1 / α) • α • x + (1 / α) • β • y) := by simp
              _ = (((1 / α) * α) • x + (1 / α) • β • y) := by rw [mul_smul]
              _ = x + (1 / α) • β • y := by rw [one_div_mul_cancel hα];simp
              _ = x + α⁻¹ • β • y := by rw [@one_div]
              _ = x + (α⁻¹ * β) • y := by rw [← mul_smul]
              _ = x + (β / α) • y := by rw [@inv_mul_eq_div]
        · intro Heq
          apply hxy
          calc ⁅x, y⁆ = ⁅x, y⁆ + ((β / α) • ⁅y, y⁆) := by simp
              _ = ⁅x +(β / α) • y, y⁆ := by simp
              _ = 0 := by rw [Heq]; simp
    rw [← pf1] at pf2
    have ⟨ B, u ⟩ := basis_of_bracket_ne_zero h X Y pf2
    use B
    rw [u.1, u.2]
    assumption

theorem classification (h : finrank K L = 2) :
    Nonempty (L ≃ₗ⁅K⁆ Abelian K) ∨ Nonempty (L ≃ₗ⁅K⁆ Affine K) := by
  obtain (a | ⟨ B, pfB ⟩) := abelian_or_basis h
  · left
    have := finite_of_finrank_eq_succ h
    have B := finBasisOfFinrankEq K L h
    constructor
    exact ({ Basis.equivFun B with
      map_lie' := by
        intro x y
        simp only [trivial_lie_zero, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          LinearEquiv.coe_coe, Basis.equivFun_apply, map_zero]
        rfl
    })
  · right
    constructor
    exact {
      toFun := fun l => ![B.repr l 0, B.repr l 1]
      map_add' := by
        intro x y
        change ![(B.repr (x + y)) 0, (B.repr (x + y)) 1] =
          ![(B.repr x) 0, (B.repr x) 1] + ![(B.repr y) 0, (B.repr y) 1]
        rw [map_add, show (B.repr x + B.repr y) 0 = B.repr x 0 + B.repr y 0 from rfl,
          show (B.repr x + B.repr y) 1 = B.repr x 1 + B.repr y 1 from rfl,
          Matrix.cons_add_cons, Matrix.cons_add_cons, Matrix.empty_add_empty]
      map_smul' := by
        intro r x
        change ![(B.repr (r • x)) 0, (B.repr (r • x)) 1] =
          (RingHom.id K) r • ![(B.repr x) 0, (B.repr x) 1]
        rw [map_smul, show (r • B.repr x) 0 = r * B.repr x 0 from rfl,
          show (r • B.repr x) 1 = r * B.repr x 1 from rfl, RingHom.id_apply,
          Matrix.smul_cons, Matrix.smul_cons, Matrix.smul_empty, smul_eq_mul, smul_eq_mul]
      map_lie' := by
        intro x y
        have lie_repr : ⁅ x , y ⁆ = (B.repr x 0 * B.repr y 1 - B.repr y 0 * B.repr x 1) • B 1 := by
          rw [Basis.repr_fin_two  B x, Basis.repr_fin_two B y]
          simp only [lie_add, lie_smul, add_lie, smul_lie, lie_self, smul_zero,
            zero_add, add_zero, map_add, map_smul, Basis.repr_self, Finsupp.smul_single,
            smul_eq_mul, mul_one, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, ne_eq,
            one_ne_zero, not_false_eq_true, Finsupp.single_eq_of_ne, zero_ne_one]
          rw [pfB, ← lie_skew, pfB]
          module
        rw [lie_repr, @Affine.bracket K _]
        funext i; fin_cases i <;> simp
      invFun := fun α => α 0 • B 0 + α 1 • B 1
      left_inv := by
        intro x
        simp [Basis.ext_elem_iff B, Fin.forall_fin_two]
      right_inv := by
        intro α
        simp only [Affine, Fin.isValue, map_add, map_smul, Basis.repr_self,
          Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_add, Pi.add_apply,
          Finsupp.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true,
          Finsupp.single_eq_of_ne, add_zero, one_ne_zero, zero_add]
        exact List.ofFn_inj.mp rfl
    }

theorem not_iso : IsEmpty (Affine K ≃ₗ⁅K⁆ Abelian K) := by
  constructor
  intro iso
  have Hf : iso ![0, 1] = 0 := by
    let e₁ : Affine K := ![1, 0]
    let e₂ : Affine K := ![0, 1]
    calc
          iso e₂ = iso ⁅ e₁, e₂ ⁆ := by
            simp [Affine.bracket, e₂]
            rfl
          _ = 0 := by
            simp [iso.map_lie, trivial_lie_zero]
  have : iso.symm 0 = 0 := iso.symm.map_zero
  apply_fun (fun x => (iso.symm x) 1) at Hf
  simp [LieEquiv.symm_apply_apply, this] at Hf
  exact one_ne_zero (Hf.trans (Pi.zero_apply _))

end Dim2
end classification_dim_2

section corollaries_dim_2

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

theorem _root_.LieAlgebra.Dim2.solvable (dim2 : finrank K L = 2) :
    IsSolvable L := by
   obtain (a | ⟨ B, pfB ⟩) := Dim2.abelian_or_basis dim2
   · apply ofAbelianIsSolvable
   · have h1 : span K (span K {B 1}).carrier= span K {B 1} := by
      apply le_antisymm
      · exact span_le.mpr fun ⦃a⦄ a ↦ a
      · apply subset_span
     have hh : {m | ∃ (x : L) (n : L), ⁅x, n⁆ = m} = (span K {B 1}).carrier := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, n, hxn⟩ := hy
        rw [Basis.repr_fin_two B x,Basis.repr_fin_two B n] at hxn
        simp only [lie_add, lie_smul, add_lie, smul_lie, lie_self, smul_zero, zero_add,
          add_zero] at hxn
        rw [<- lie_skew, pfB] at hxn
        have u : y = ((-1: K) • B.repr n 0 • (B.repr x) 1 + (B.repr n) 1 • (B.repr x) 0) • B 1 := by
          rw [← hxn]
          simp only [smul_neg, smul_eq_mul, neg_mul, one_mul]
          module
        rw [u]
        refine
          (span K {B 1}).smul_mem' (-1 • (B.repr n) 0 • (B.repr x) 1 + (B.repr n) 1 • (B.repr x) 0)
            ?h.mp.intro.intro.a
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, mem_toAddSubmonoid]
        apply  mem_span_singleton_self
      · simp only [Fin.isValue, carrier_eq_coe, SetLike.mem_coe, Set.mem_setOf_eq]
        intro hy
        apply mem_span_singleton.mp at hy
        obtain ⟨α, hα⟩ := hy
        exists (α • B 0), B 1
        rw [← hα]
        simp only [smul_lie]
        rw [pfB]
     have : (commutator K L).toSubmodule = span K {x : L | ∃ (y : L) (z : L), ⁅y,
       z⁆ = x} := commutator_eq_span
     rw [hh, h1] at this
     have dimcomm : finrank K (commutator K L).toSubmodule = 1 := by
      rw [this]
      refine finrank_span_singleton ?hv
      exact Basis.ne_zero B 1
     have comsol : IsSolvable (commutator K L) := by
      apply Dim1.solvable (L := commutator K L) dimcomm
     apply solvable_of_commutator_solvable (K := K)
     exact comsol

theorem _root_.LieAlgebra.solvable_of_dim_comm_le_two [fin : FiniteDimensional K L]
    (dimcomm : finrank K (commutator K L) ≤ 2) :
    IsSolvable L := by
  have hl : finrank K (commutator K L) ≥ 0 := by apply zero_le
  interval_cases s : (finrank K (commutator K L)) using hl, dimcomm
  · simp [LieAlgebra.abelian_iff_dim_comm_zero] at s
    apply ofAbelianIsSolvable
  · apply solvable_of_commutator_solvable (K := K)
    apply Dim1.solvable (K := K)
    assumption
  · apply solvable_of_commutator_solvable (K := K)
    apply Dim2.solvable (K := K)
    assumption

end corollaries_dim_2

end LieAlgebra
