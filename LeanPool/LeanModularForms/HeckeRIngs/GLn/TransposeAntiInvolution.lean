/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.GLn.DiagonalCosets
import LeanPool.LeanModularForms.HeckeRIngs.AbstractHeckeRing.Commutativity

/-!
# GL_n Hecke Algebra Commutativity via Transpose

The transpose `ξ ↦ ᵗξ` is an anti-automorphism of `GL_n(ℚ)` that preserves `SL_n(ℤ)`
and the positive-determinant integer matrices `Δ`. Since every double coset has a
diagonal representative (which is fixed by transpose), Shimura's Proposition 3.8
gives commutativity of the Hecke ring.

## Main results

* `GLPairAntiInvolution` -- the transpose as an `AntiInvolution` for `GLPair n`
* `instCommRingHeckeAlgebra` -- `CommRing (HeckeAlgebra n)`
-/

open Matrix HeckeRing HeckeRing.GLn Matrix.SpecialLinearGroup

namespace HeckeRing.GLn

variable (n : ℕ)

/-- The transpose map `GL_n(ℚ) → GL_n(ℚ)ᵐᵒᵖ` as a multiplicative equivalence. -/
noncomputable def GLTransposeEquiv :
    GL (Fin n) ℚ ≃* (GL (Fin n) ℚ)ᵐᵒᵖ :=
  (Units.mapEquiv (transposeRingEquiv (Fin n) ℚ).toMulEquiv).trans Units.opEquiv

lemma GL_transposeEquiv_val (g : GL (Fin n) ℚ) :
    ((GLTransposeEquiv n g).unop : Matrix (Fin n) (Fin n) ℚ) =
    (↑g : Matrix (Fin n) (Fin n) ℚ)ᵀ := by
  simp [GLTransposeEquiv, Units.opEquiv, Units.mapEquiv, transposeRingEquiv]

lemma GL_transposeEquiv_involutive (g : GL (Fin n) ℚ) :
    (GLTransposeEquiv n (GLTransposeEquiv n g).unop).unop = g := by
  ext i j; simp [GL_transposeEquiv_val]

lemma SLnZ_to_GLnQ_transpose (σ : SpecialLinearGroup (Fin n) ℤ) :
    (GLTransposeEquiv n (σ : GL (Fin n) ℚ)).unop = (σ.transpose : GL (Fin n) ℚ) := by
  ext i j
  simp [GL_transposeEquiv_val, mapGL_coe_matrix, algebraMap_int_eq,
    SpecialLinearGroup.coe_transpose]

lemma GL_transpose_mem_SLnZ {g : GL (Fin n) ℚ} (hg : g ∈ SLnZSubgroup n) :
    (GLTransposeEquiv n g).unop ∈ SLnZSubgroup n := by
  rw [MonoidHom.mem_range] at hg ⊢
  obtain ⟨σ, rfl⟩ := hg
  exact ⟨σ.transpose, (SLnZ_to_GLnQ_transpose n σ).symm⟩

lemma HasIntEntries.transpose {g : GL (Fin n) ℚ} (hg : HasIntEntries n g) :
    HasIntEntries n (GLTransposeEquiv n g).unop := by
  obtain ⟨A, hA⟩ := hg
  exact ⟨Aᵀ, by rw [GL_transposeEquiv_val, hA, Matrix.transpose_map]⟩

lemma GL_transpose_mem_posDetInt {g : GL (Fin n) ℚ} (hg : g ∈ posDetIntSubmonoid n) :
    (GLTransposeEquiv n g).unop ∈ posDetIntSubmonoid n :=
  ⟨hg.1.transpose, by rw [GL_transposeEquiv_val, Matrix.det_transpose]; exact hg.2⟩

lemma diagMat_GL_transpose_eq (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (GLTransposeEquiv n (diagMat n a)).unop = diagMat n a := by
  apply Units.ext; change (diagMat n a).val.transpose = (diagMat n a).val
  rw [diagMat_val n a ha, Matrix.diagonal_transpose]

variable [NeZero n]

/-- The transpose as an `AntiInvolution` for `GLPair n`. -/
noncomputable def GLPairAntiInvolution : AntiInvolution (GLPair n) where
  toFun := (GLTransposeEquiv n).toMonoidHom
  involutive := GL_transposeEquiv_involutive n
  map_H := fun _g hg => GL_transpose_mem_SLnZ n hg
  map_Δ := fun _g hg => GL_transpose_mem_posDetInt n hg

/-- Transpose fixes every double coset of `GLPair n`. -/
lemma GL_pair_onHeckeCoset_eq (D : HeckeCoset (GLPair n)) :
    (GLPairAntiInvolution n).onHeckeCoset D = D := by
  obtain ⟨a, ha, _hdiv, hrep⟩ := exists_diagonal_representative n (HeckeCoset.rep D)
  rw [show D = TDiag a from by rw [← hrep]; exact (Quotient.out_eq D).symm]
  simp only [TDiag, AntiInvolution.onHeckeCoset_mk]
  rw [HeckeCoset.eq_iff]
  simp only [AntiInvolution.bar, GLPairAntiInvolution, diagMat_delta_val n a ha]
  rw [show (GLTransposeEquiv n).toMonoidHom (diagMat n a) =
      GLTransposeEquiv n (diagMat n a) from rfl, diagMat_GL_transpose_eq n a ha]

/-- **Shimura Proposition 3.8 for GL_n**: the Hecke algebra is commutative. -/
noncomputable instance instCommRingHeckeAlgebra : CommRing (HeckeAlgebra n) :=
  instCommRingOfAntiInvolution (GLPairAntiInvolution n) (GL_pair_onHeckeCoset_eq n)

end HeckeRing.GLn
