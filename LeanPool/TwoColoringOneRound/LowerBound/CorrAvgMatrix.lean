/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Rat.Star

import LeanPool.TwoColoringOneRound.LowerBound.Correlation

namespace Distributed2Coloring.LowerBound

namespace Correlation

open scoped BigOperators
open scoped Matrix

/-- The rank-1 correlation kernel as a matrix indexed by vertices. -/
def corrMatrix {n : Nat} (f : Coloring n) : Matrix (Vertex n) (Vertex n) Correlation.Q :=
  fun u v => corr f u v

/-- The orbit-averaged correlation kernel as a matrix indexed by vertices. -/
noncomputable def corrAvgMatrix {n : Nat} (f : Coloring n) :
    Matrix (Vertex n) (Vertex n) Correlation.Q :=
  fun u v => corrAvg f u v

theorem corrMatrix_posSemidef {n : Nat} (f : Coloring n) : (corrMatrix f).PosSemidef := by
  -- `corrMatrix f = vecMulVec a (star a)` where `a u = spin (f u)`.
  simpa [corrMatrix, corr, Matrix.vecMulVec] using
    (Matrix.posSemidef_vecMulVec_self_star (R := Correlation.Q) (n := Vertex n)
      (a := fun u => spin (f u)))

theorem corrAvgMatrix_posSemidef {n : Nat} (f : Coloring n) : (corrAvgMatrix f).PosSemidef := by
  classical
  let G : Type := Correlation.G n
  let corrMat : G → Matrix (Vertex n) (Vertex n) Correlation.Q :=
    fun σ u v => corr f (σ • u) (σ • v)
  have hsum : (∑ σ : G, corrMat σ).PosSemidef := by
    -- finite sum of PSD matrices is PSD
    have hterm : ∀ σ ∈ (Finset.univ : Finset G), (corrMat σ).PosSemidef := by
      intro σ _hσ
      -- again rank-1 PSD
      simpa [corrMat, corr, Matrix.vecMulVec] using
        (Matrix.posSemidef_vecMulVec_self_star (R := Correlation.Q) (n := Vertex n)
          (a := fun u => spin (f (σ • u))))
    -- `Matrix.posSemidef_sum` is stated for a finset-indexed sum.
    have hsum' := Matrix.posSemidef_sum (s := (Finset.univ : Finset G)) (x := corrMat) hterm
    simpa [corrMat] using hsum'
  have havg :
      corrAvgMatrix f =
        ((Fintype.card (Correlation.G n) : Correlation.Q)⁻¹) •
          (∑ σ : Correlation.G n, corrMat σ) := by
    ext u v
    simp [corrAvgMatrix, corrAvg, corrMat, Matrix.smul_apply, Matrix.sum_apply, div_eq_mul_inv,
      mul_comm]
  have hinv_nonneg : 0 ≤ (Fintype.card (Correlation.G n) : Q)⁻¹ := by
    exact le_of_lt (inv_pos.2 (cardG_pos n))
  simpa [havg] using Matrix.PosSemidef.smul (x := (∑ σ : Correlation.G n, corrMat σ)) hsum
    (a := (Fintype.card (Correlation.G n) : Q)⁻¹) hinv_nonneg

end Correlation

end Distributed2Coloring.LowerBound
