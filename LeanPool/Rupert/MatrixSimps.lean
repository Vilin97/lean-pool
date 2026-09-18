/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
module


public import Mathlib.Analysis.Normed.Lp.PiLp
import LeanPool.Rupert.Attr

/-!
# LeanPool.Rupert.MatrixSimps

Imported Lean Pool material for `LeanPool.Rupert.MatrixSimps`.
-/

@[expose] public section

/-- Reduce natural additions in concrete matrix expressions. -/
dsimproc_decl matrixReduceNatAdd ((_ + _ : Nat)) := Nat.reduceAdd

/-- Normalize finite indices in concrete matrix expressions. -/
dsimproc_decl matrixNormalizeFin ((OfNat.ofNat _ : Fin _)) := Fin.isValue

attribute [matrix_simps] Matrix.cons_dotProduct even_two Even.neg_pow neg_mul matrixReduceNatAdd
            sub_neg_eq_add mul_neg neg_neg matrixNormalizeFin Matrix.cons_mulVec
            Matrix.cons_dotProduct Matrix.dotProduct_of_isEmpty add_zero Matrix.empty_mulVec
            Matrix.cons_val_zero Matrix.cons_val_one smul_smul Matrix.head_cons
            mul_one Matrix.tail_cons Matrix.cons_val zero_mul zero_smul
            Matrix.mulVec_cons Nat.succ_eq_add_one neg_smul one_smul
            Matrix.mulVec_empty Pi.add_apply Pi.neg_apply Function.comp_apply
            Matrix.smul_cons smul_eq_mul Matrix.smul_empty Matrix.add_cons
            Matrix.head_cons Matrix.tail_cons Matrix.empty_add_empty
            Matrix.vecHead Matrix.vecTail PiLp.toLp_apply Fin.succ_zero_eq_one
            Fin.succ_one_eq_two
