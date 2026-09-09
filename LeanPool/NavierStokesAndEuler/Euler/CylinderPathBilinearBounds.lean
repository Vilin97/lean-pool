/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathBilinear
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathProductBounds
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevFiniteSum
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear

/-! Fixed bounded vector operations preserve the genuine nonlinear H6 word estimates. -/

@[expose] public section


noncomputable section

namespace EulerCylinderPathProduct

open Set MeasureTheory ContinuousLinearMap Finset EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerCylinderConstantMap
  EulerCylinderSobolev EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderPathBilinearBounds1 : NormedAddCommGroup (LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderPathBilinearBounds2 : NormedSpace ℝ (LiftL2 P) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instCylinderPathBilinearBounds3 : NormedAddCommGroup C(K,LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderPathBilinearBounds4 : NormedSpace ℝ C(K,LiftL2 P) := inferInstance

theorem pathMap_block_le (A : Space →L[ℝ] Space) (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (q n : ℕ) (a : LiftTangent) :
    block standardDirection q (fun b : LiftTangent => pathTranslate P b (pathMap P A p)) n a ≤
      ‖A‖*block standardDirection q (fun b : LiftTangent => pathTranslate P b p) n a := by
  have he : (fun b : LiftTangent => pathTranslate P b (pathMap P A p)) =
      pathMap P A ∘ (fun b : LiftTangent => pathTranslate P b p) :=
    funext (fun b => (pathMap_translation P A b p).symm)
  rw [he]
  have hnorm : ‖pathMap (K := K) P A‖ ≤ ‖A‖ := pathMap_norm (K := K) P A
  have h := block_comp_clm_le (P := LiftTangent) (E := C(K,LiftL2 P)) (F := C(K,LiftL2 P))
    standardDirection q (pathMap (K := K) P A)
    (fun b : LiftTangent => pathTranslate P b p) hp n a
  exact h.trans (mul_le_mul_of_nonneg_right hnorm
    (block_nonneg standardDirection q (fun b : LiftTangent => pathTranslate P b p) n a))

variable (B : Space →L[ℝ] Space →L[ℝ] Space) (p q : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))

/-- The field word radius is unchanged by an arbitrary fixed bounded bilinear vector map. -/
theorem bilinearProductPath_majorant (R A C : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (d e : ℕ) (a : LiftTangent)
    (hb : ∀ n, block standardDirection 6 (fun b : LiftTangent => pathTranslate P b p) n a ≤
      A*majorant R d n)
    (hc : ∀ n, block standardDirection 6 (fun b : LiftTangent => pathTranslate P b q) n a ≤
      C*majorant R e n) (n : ℕ) :
    block standardDirection 6
      (fun b : LiftTangent => pathTranslate P b (bilinearProductPath P B p q hp hq)) n a ≤
      (9*productBlockConstant P*‖B‖*A*C)*majorant R (d+e) n := by
  have ht (i : Fin 3) :
      block standardDirection 6
        (fun b : LiftTangent => pathTranslate P b (bilinearTerm P B p q hp hq i)) n a ≤
      (3*productBlockConstant P*‖B‖*A*C)*majorant R (d+e) n := by
    have hi : ‖B (basisVector i)‖ ≤ ‖B‖ := by
      simpa [basisVector] using B.le_opNorm (basisVector i)
    have hs := scalarProductPath_majorant P (component i) (component_norm i)
      p q hp hq R A C hR hA hC d e a hb hc n
    have hpos : 0 ≤ (3*productBlockConstant P*A*C)*majorant R (d+e) n :=
      mul_nonneg (by have := productBlockConstant_nonneg P; positivity) (majorant_nonneg R hR _ _)
    have h := (pathMap_block_le P (B (basisVector i))
      (scalarProductPath P (component i) (component_norm i) p q hp hq)
      (scalarProductPath_orbit P (component i) (component_norm i) p q hp hq) 6 n a).trans
      (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
    exact h.trans ((mul_le_mul_of_nonneg_right hi hpos).trans_eq (by ring))
  let f := fun i : Fin 3 => fun b : LiftTangent => pathTranslate P b (bilinearTerm P B p q hp hq i)
  have he : (fun b : LiftTangent => pathTranslate P b (bilinearProductPath P B p q hp hq)) =
      ∑ i : Fin 3, f i := by
    funext b
    simp only [bilinearProductPath, map_sum, f, Finset.sum_apply]
  rw [he]
  have h := block_finset_sum_le standardDirection 6 univ f
    (fun i _ => bilinearTerm_orbit P B p q hp hq i) n a
  exact h.trans ((sum_le_sum (fun i _ => ht i)).trans_eq (by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    ring))

end EulerCylinderPathProduct
