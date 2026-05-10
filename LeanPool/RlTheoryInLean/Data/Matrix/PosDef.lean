/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Real.StarOrdered

import LeanPool.RlTheoryInLean.Data.Matrix.Mul

open Real Finset Filter TopologicalSpace Preorder Matrix EuclideanSpace
open scoped InnerProductSpace RealInnerProductSpace

namespace Matrix

variable {α : Type*} [Fintype α] (A : Matrix α α ℝ)

/-- A real square matrix whose quadratic form has positive asymmetric part. -/
class PosDefAsymm : Prop where
  pd : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)

lemma posDefAsymm_iff : PosDefAsymm A ↔ Matrix.PosDef (A + Aᵀ) := by
  constructor
  case mp =>
    intro h
    apply PosDef.of_dotProduct_mulVec_pos
    · apply isHermitian_add_transpose_self
    · intro x hx
      simp only [star_trivial]
      rw [add_mulVec, dotProduct_add, dotProduct_transpose_mulVec]
      have := h.pd x hx
      linarith
  case mpr =>
    intro h
    constructor
    intro x hx
    have := h.dotProduct_mulVec_pos hx
    simp only [star_trivial] at this
    rw [add_mulVec, dotProduct_add, dotProduct_transpose_mulVec] at this
    linarith

theorem posDefAsymm_iff'
  {α : Type*} [Fintype α] (A : Matrix α α ℝ) :
  PosDefAsymm A ↔ ∃ η, 0 < η ∧ ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  classical
  by_cases hα : Nonempty α
  case neg =>
    simp at hα
    constructor
    case mp =>
      intro h
      use 1
      constructor
      · norm_num
      · intro x
        simp only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, le_refl]
    case mpr =>
      intro h
      constructor
      intro x hx
      apply False.elim
      simp at hx
      have : x = 0 := by
        ext i
        exact (IsEmpty.false i).elim
      contradiction
  case pos =>
    rw [posDefAsymm_iff]
    constructor
    case mp =>
      intro h
      let η := (Finset.univ : Finset α).inf' (by simp) h.1.eigenvalues
      have hηmin : ∀ i, η ≤ h.1.eigenvalues i := by
        intro i
        apply Finset.inf'_le
        simp
      have hηpos : 0 < η := by
        obtain ⟨i, _, hi⟩ :=
          exists_mem_eq_inf' (s := Finset.univ) (by simp) h.1.eigenvalues
        have := PosDef.eigenvalues_pos h i
        unfold η
        rw [hi]
        exact this
      refine ⟨?η, ?hηpos, ?hη⟩
      case η => exact (2⁻¹ : ℝ) * η
      case hηpos => positivity
      case hη =>
        intro x
        apply (mul_le_mul_iff_of_pos_left (a := 2) (by simp)).mp
        conv_rhs => rw [two_mul]
        nth_rw 2 [←dotProduct_transpose_mulVec]
        rw [←dotProduct_add, ←add_mulVec, h.1.spectral_theorem]
        simp only [RCLike.ofReal_real_eq_id, CompTriple.comp_eq, Unitary.conjStarAlgAut_apply]
        rw [←mulVec_mulVec, dotProduct_mulVec, ←vecMul_vecMul, ]
        rw [vecMul_diagonal_dotProduct]
        simp_rw [mul_assoc]
        rw [←mul_assoc, mul_inv_cancel₀]
        · set U : Matrix α α ℝ := ↑h.1.eigenvectorUnitary with hUdef
          simp only [one_mul]
          have hself := UnitaryGroup.star_mul_self h.1.eigenvectorUnitary
          rw [←hUdef] at hself
          have hmul := mem_unitaryGroup_iff.mp (mem_unitaryGroup_iff'.mpr hself)
          have hxx : x ⬝ᵥ x = x ᵥ* (U * star U) ⬝ᵥ x := by
            simp [hmul]
          rw [hxx]
          have hstarU : star U = Uᵀ := by simp [star, hUdef]
          rw [hstarU]
          rw [←vecMul_vecMul, ←dotProduct_mulVec, dotProduct]
          rw [mul_sum]
          apply sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg
          · apply hηmin
          · rfl
          · positivity
          · nth_rw 1 [←transpose_transpose U]
            rw [vecMul_transpose, ←pow_two]
            apply sq_nonneg
        · norm_num
    case mpr =>
      intro h
      obtain ⟨η, hηpos, hη⟩ := h
      apply PosDef.of_dotProduct_mulVec_pos
      · apply isHermitian_add_transpose_self
      · intro x hx
        simp only [star_trivial]
        rw [add_mulVec, dotProduct_add, dotProduct_transpose_mulVec]
        have h1 : x ⬝ᵥ A *ᵥ x + x ⬝ᵥ A *ᵥ x = 2 * (x ⬝ᵥ A *ᵥ x) := by ring
        rw [h1]
        have hxx_pos : 0 < x ⬝ᵥ x := by
          rw [← star_trivial x]
          exact dotProduct_star_self_pos_iff.mpr hx
        have hAxpos : 0 < x ⬝ᵥ A *ᵥ x :=
          lt_of_lt_of_le (mul_pos hηpos hxx_pos) (hη x)
        linarith

/-- A real square matrix whose negation is asymmetrically positive definite. -/
class NegDefAsymm : Prop where
  nd : PosDefAsymm (-A)

section invertible

variable [DecidableEq α]

noncomputable instance [PosDefAsymm A] : Invertible A.det := by
  apply invertibleOfNonzero
  apply IsUnit.ne_zero
  apply A.isUnit_iff_isUnit_det.mp
  apply isUnit_toLin'_iff.mp
  apply A.toLin'.isUnit_iff_ker_eq_bot.mpr
  apply ker_toLin'_eq_bot_iff.mpr
  intro x hx
  by_contra h
  have hA : PosDefAsymm A := by infer_instance
  have hA := hA.pd x h
  have : x ⬝ᵥ A *ᵥ x = 0 := by
    rw [hx]
    simp
  linarith

noncomputable instance [PosDefAsymm A] : Invertible A := by
  apply Matrix.invertibleOfDetInvertible

noncomputable instance [NegDefAsymm A] : Invertible A.det := by
  apply invertibleOfNonzero
  have hdet := det_neg A
  by_contra h
  rw [h] at hdet
  simp only [mul_zero] at hdet
  have := (inferInstance : NegDefAsymm A).nd
  have : Invertible (-A).det := by infer_instance
  have := this.ne_zero
  rw [hdet] at this
  simp at this

noncomputable instance [NegDefAsymm A] : Invertible A := by
  apply Matrix.invertibleOfDetInvertible

end invertible

end Matrix
