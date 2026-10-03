/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import Mathlib.LinearAlgebra.Matrix.SchurComplement

public import LeanPool.Zeta5Irrational.Arith.Val
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring.Basic

/-! # Lemma 4.2 (simplified): determinants with a low-rank `p⁻¹`-correction

If `v(A_{st}) ≥ w_s + w_t` with `w ≤ 0`, and `U`, `V` are `p`-integral of inner dimension `r`, then
`v_p^G(det(A + p⁻¹ U V)) ≥ 2 ∑ w - r` (via the Schur complement).
-/

public section

open Finset Polynomial Matrix

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

theorem det_lowrank_bound {h r : ℕ} (A : Matrix (Fin h) (Fin h) ℚ[X])
    (U : Matrix (Fin h) (Fin r) ℚ) (V : Matrix (Fin r) (Fin h) ℚ) (w : Fin h → ℚ)
    (hw : ∀ s, w s ≤ 0) (hA : ∀ s t, GV p (A s t) (w s + w t)) (hU : ∀ s u, VG p (U s u) 0)
    (hV : ∀ u t, VG p (V u t) 0) :
    GV p (A + (((p : ℚ)⁻¹ • (U * V)).map (C : ℚ →+* ℚ[X]))).det (2 * ∑ s, w s - r) := by
  set B : Matrix (Fin h) (Fin r) ℚ[X] := (-U).map (C : ℚ →+* ℚ[X])
  set Cm : Matrix (Fin r) (Fin h) ℚ[X] := ((p : ℚ)⁻¹ • V).map (C : ℚ →+* ℚ[X])
  have hdet :
    (A + (((p : ℚ)⁻¹ • (U * V)).map (C : ℚ →+* ℚ[X]))).det = (Matrix.fromBlocks A B Cm 1).det := by
    rw [det_fromBlocks_one₂₂]
    congr 1
    refine Matrix.ext fun s t => ?_
    simp only [B, Cm, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply,
      Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_neg, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  rw [hdet]
  have hinv : VG p ((p : ℚ)⁻¹) (-1) := by
    have := VG.primePow (p := p) (-1)
    simpa using this
  have key :=
    det_GV (Matrix.fromBlocks A B Cm 1) (Sum.elim w fun _ => (-1 : ℚ))
      (Sum.elim w fun _ => (0 : ℚ))
      (by
        intro i j
        rcases i with s | u <;> rcases j with t | u'
        · exact hA s t
        · simp only [Matrix.fromBlocks_apply₁₂, B, Matrix.map_apply, Matrix.neg_apply,
            Sum.elim_inl, Sum.elim_inr, add_zero]
          exact (GV.C (hU s u').neg).mono (hw s)
        · simp only [Matrix.fromBlocks_apply₂₁, Cm, Matrix.map_apply, Matrix.smul_apply,
            smul_eq_mul, Sum.elim_inl, Sum.elim_inr]
          refine (GV.C (hinv.mul (hV u t))).mono ?_
          linarith [hw t]
        · simp only [Matrix.fromBlocks_apply₂₂, Sum.elim_inr, add_zero]
          rw [Matrix.one_apply]
          split_ifs
          · exact (GV.C (p := p) VG.one).mono (by norm_num)
          · exact GV.zero _)
  refine key.mono (le_of_eq ?_)
  simp [Fintype.sum_sum_type]
  ring

end Zeta5Irrational
