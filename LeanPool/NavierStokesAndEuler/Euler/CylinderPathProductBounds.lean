/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathProduct
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevWordBounds
public import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus

@[expose] public section

/-!
# Same-radius fixed-H6 estimates for actual cylinder products

The product is the literal pointwise product already constructed in H6.
Both input word sums pass directly through the bilinear Leibniz formula.
The only norm equivalence constant is the fixed size of the H6 array.
-/

noncomputable section

namespace EulerCylinderPathProduct

open Set MeasureTheory ContinuousLinearMap Finset EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSmoothOrbit EulerLpCylinderTranslation
  EulerSobolevL2Product EulerParameterWordGevrey EulerCylinderSobolev
  EulerJetProductBounds EulerGevrey
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup (C(K,SobolevSpace P 6)) := inferInstance
private local instance : NormedSpace ℝ (C(K,SobolevSpace P 6)) := inferInstance
private local instance : NormedAddCommGroup (C(K,SobolevSpace P 6) →L[ℝ] C(K,SobolevSpace P 6)) :=
  inferInstance
private local instance : NormedSpace ℝ (C(K,SobolevSpace P 6) →L[ℝ] C(K,SobolevSpace P 6)) :=
  inferInstance

variable (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (p q : C(K,LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))

theorem scalarProductPath_sobolevOrbit (a : LiftTangent) :
    sobolevOrbit P 6 (scalarProductPath P L hL p q hp hq)
        (scalarProductPath_orbit P L hL p q hp hq) a =
      pathBilinear (productHqBilinear P (by norm_num : 6 ≤ 6) L hL)
        (sobolevOrbit P 6 p hp a) (sobolevOrbit P 6 q hq a) := by
  apply ContinuousMap.ext
  intro t
  apply value_injective P
  exact (sobolevOrbit_value P 6 (scalarProductPath P L hL p q hp hq)
    (scalarProductPath_orbit P L hL p q hp hq) a t).trans
      (congrArg (fun u : C(K,LiftL2 P) => u t)
        (scalarProductPath_orbit_formula P L hL p q hp hq a))

/-- A numerical fixed-order constant, independent of external derivative order and grade. -/
def productBlockConstant : ℝ :=
  (Fintype.card (SobolevWord 6) : ℝ)*sobolevProductConstant P 6

theorem productBlockConstant_nonneg : 0 ≤ productBlockConstant P :=
  mul_nonneg (Nat.cast_nonneg _) (sobolevProductConstant_nonneg P 6)

theorem productH6PathBilinear_norm :
    ‖pathBilinear (K := K) (productHqBilinear P (by norm_num : 6 ≤ 6) L hL)‖ ≤
      sobolevProductConstant P 6 := by
  apply (pathBilinear_norm _).trans
  exact opNorm_le_bound _ (sobolevProductConstant_nonneg P 6)
    (productHqRight_norm P (by norm_num : 6 ≤ 6) L hL)

/-- Actual external word blocks of the genuine product obey the H6 algebra convolution. -/
theorem scalarProductPath_block_bound (n : ℕ) (a : LiftTangent) :
    block standardDirection 6
      (fun b : LiftTangent => pathTranslate P b (scalarProductPath P L hL p q hp hq)) n a ≤
      productBlockConstant P * leibnizConvolution
        (fun k => block standardDirection 6 (fun b : LiftTangent => pathTranslate P b p) k a)
        (fun k => block standardDirection 6 (fun b : LiftTangent => pathTranslate P b q) k a) n :=
          by
  let B := pathBilinear (K := K) (productHqBilinear P (by norm_num : 6 ≤ 6) L hL)
  have he := funext (scalarProductPath_sobolevOrbit P L hL p q hp hq)
  have hc : leibnizConvolution
      (fun k => wordSum standardDirection (sobolevOrbit P 6 p hp) k a)
      (fun k => wordSum standardDirection (sobolevOrbit P 6 q hq) k a) n ≤
      leibnizConvolution
        (fun k => block standardDirection 6 (fun b : LiftTangent => pathTranslate P b p) k a)
        (fun k => block standardDirection 6 (fun b : LiftTangent => pathTranslate P b q) k a) n :=
          by
    unfold leibnizConvolution
    apply sum_le_sum
    intro k _
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (sobolevOrbit_wordSum_le_block P 6 p hp k a) (Nat.cast_nonneg _))
      (sobolevOrbit_wordSum_le_block P 6 q hq (n-k) a)
      (wordSum_nonneg _ _ _ _)
      (mul_nonneg (Nat.cast_nonneg _) (block_nonneg _ _ _ _ _))
  have hn : 0 ≤ leibnizConvolution
      (fun k => wordSum standardDirection (sobolevOrbit P 6 p hp) k a)
      (fun k => wordSum standardDirection (sobolevOrbit P 6 q hq) k a) n :=
    sum_nonneg (fun k _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (wordSum_nonneg _ _ _ _)) (wordSum_nonneg _ _ _ _))
  have hprod := wordSum_bilinear_le standardDirection B
    (sobolevOrbit P 6 p hp) (sobolevOrbit P 6 q hq)
    (sobolevOrbit_contDiff P 6 p hp) (sobolevOrbit_contDiff P 6 q hq) n a
  have hb := hprod.trans (mul_le_mul (productH6PathBilinear_norm (K := K) P L hL)
    hc hn (sobolevProductConstant_nonneg P 6))
  have h := block_le_card_sobolevOrbit_wordSum P 6
    (scalarProductPath P L hL p q hp hq) (scalarProductPath_orbit P L hL p q hp hq) n a
  rw [he] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)).trans_eq
    (by unfold productBlockConstant; ring))

/-- The actual product retains the input radius and adds only the two factorial shifts. -/
theorem scalarProductPath_majorant (R A C : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (d e : ℕ) (a : LiftTangent)
    (hb : ∀ n, block standardDirection 6 (fun b : LiftTangent => pathTranslate P b p) n a ≤
      A*majorant R d n)
    (hc : ∀ n, block standardDirection 6 (fun b : LiftTangent => pathTranslate P b q) n a ≤
      C*majorant R e n) (n : ℕ) :
    block standardDirection 6
      (fun b : LiftTangent => pathTranslate P b (scalarProductPath P L hL p q hp hq)) n a ≤
      (3*productBlockConstant P*A*C)*majorant R (d+e) n := by
  have hs := sequence_product_majorant R A C hR hA hC d e
    (fun k => block standardDirection 6 (fun b : LiftTangent => pathTranslate P b p) k a)
    (fun k => block standardDirection 6 (fun b : LiftTangent => pathTranslate P b q) k a)
    (fun k => by rw [abs_of_nonneg (block_nonneg _ _ _ _ _)]; exact hb k)
    (fun k => by rw [abs_of_nonneg (block_nonneg _ _ _ _ _)]; exact hc k) n
  have hs' := (le_abs_self _).trans hs
  exact (scalarProductPath_block_bound P L hL p q hp hq n a).trans
    ((mul_le_mul_of_nonneg_left hs' (productBlockConstant_nonneg P)).trans_eq
      (by ring))

end EulerCylinderPathProduct
