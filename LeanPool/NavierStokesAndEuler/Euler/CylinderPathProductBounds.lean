/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathProduct
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordProduct
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOrbit
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.ParameterWordGevrey
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordCalculus
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordHigher
public import LeanPool.NavierStokesAndEuler.Euler.CylinderConstantMap
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl

/-! Related estimates used together by the same construction modules. -/

section

/-!
# Same-radius fixed-H6 estimates for actual cylinder products

The product is the literal pointwise product already constructed in H6.
Both input word sums pass directly through the bilinear Leibniz formula.
The only norm equivalence constant is the fixed size of the H6 array.
-/

section

/-!
# Fixed Sobolev path norms and actual external word sums

The finite Sobolev array gives equivalent norms with constants depending
only on its fixed order. No tensor norm conversion or external-order
alphabet factor enters either comparison.
-/

section

/-! The finite sum of nested genuine derivative words is the corresponding longer word sum. -/

@[expose] public section

noncomputable section

namespace EulerParameterWordGevrey

open Finset
open scoped ContDiff

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem sum_wordSum_wordDerivative (directions : ι → P) (f : P → E)
    (hf : ContDiff ℝ ∞ f) (k n : ℕ) (x : P) :
    (∑ w : Fin k → ι, wordSum directions (wordDerivative directions f w) n x) =
      wordSum directions f (k+n) x := by
  induction k generalizing f with
  | zero =>
    have he (w : Fin 0 → ι) : wordDerivative directions f w = f :=
      funext (wordDerivative_zero directions f w)
    simp only [he, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero,
      one_smul, Nat.zero_add]
  | succ k ih =>
    rw [sum_words_snoc]
    have he (i : ι) (w : Fin k → ι) :
        wordDerivative directions f (Fin.snoc w i) =
          wordDerivative directions (directional directions f i) w :=
      funext (wordDerivative_snoc directions f hf w i)
    simp_rw [he, ih _ (directional_contDiff directions f hf _)]
    simpa only [show k+1+n=k+n+1 by omega] using (wordSum_succ directions f hf (k+n) x).symm

end EulerParameterWordGevrey

end
end

end

@[expose] public section

noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory ContinuousLinearMap Finset EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerLpCylinderTranslation EulerParameterWordGevrey
  EulerCylinderSobolev
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Path word operator, given by `(wordOperator P w).compLeftContinuous ℝ K`. -/
def pathWordOperator {q : ℕ} (w : SobolevWord q) :
    C(K,SobolevSpace P q) →L[ℝ] C(K,LiftL2 P) :=
  (wordOperator P w).compLeftContinuous ℝ K

theorem pathWordOperator_norm_le {q : ℕ} (w : SobolevWord q) (u : C(K, SobolevSpace P q)) :
    ‖pathWordOperator P w u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro t
  exact (word_norm_le P (u t) w).trans (u.norm_coe_le_norm t)

theorem path_norm_le_sum_words {q : ℕ} (u : C(K, SobolevSpace P q)) :
    ‖u‖ ≤ ∑ w : SobolevWord q, ‖pathWordOperator P w u‖ := by
  apply (ContinuousMap.norm_le _ (sum_nonneg (fun _ _ => norm_nonneg _))).mpr
  intro t
  apply (norm_le_sumNorm P (u t)).trans
  exact sum_le_sum (fun w _ => (pathWordOperator P w u).norm_coe_le_norm t)

variable (q : ℕ) (p : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

theorem pathWordOperator_sobolevOrbit (w : SobolevWord q) :
    pathWordOperator P w ∘ sobolevOrbit P q p hp =
      wordDerivative standardDirection (fun a : LiftTangent => pathTranslate P a p) w.2 := by
  funext a
  apply ContinuousMap.ext
  intro t
  exact sobolevOrbit_coordinate P q p hp a t w

theorem sobolevOrbit_word_coordinate {n : ℕ} (v : Fin n → Fin 4)
    (w : SobolevWord q) (a : LiftTangent) :
    pathWordOperator P w (wordDerivative standardDirection (sobolevOrbit P q p hp) v a) =
      wordDerivative standardDirection
        (wordDerivative standardDirection (fun b : LiftTangent => pathTranslate P b p) w.2) v a :=
            by
  have h := wordDerivative_comp_clm standardDirection (pathWordOperator P w)
    (sobolevOrbit P q p hp) (sobolevOrbit_contDiff P q p hp) v a
  rw [pathWordOperator_sobolevOrbit P q p hp w] at h
  exact h.symm

include hp in
theorem sum_sobolev_word_levels (n : ℕ) (a : LiftTangent) :
    (∑ w : SobolevWord q,
      wordSum standardDirection
        (wordDerivative standardDirection (fun b : LiftTangent => pathTranslate P b p) w.2) n a) =
      block standardDirection q (fun b : LiftTangent => pathTranslate P b p) n a := by
  simp only [Fintype.sum_sigma]
  simp_rw [sum_wordSum_wordDerivative standardDirection _ hp]
  rw [block_eq_sum_levels standardDirection q _ hp]
  rw [← Fin.sum_univ_eq_sum_range (fun k =>
    wordSum standardDirection (fun b : LiftTangent => pathTranslate P b p) (n+k) a) (q+1)]
  exact sum_congr rfl (fun k _ => by rw [Nat.add_comm k.val n])

/-- Promotion to the actual Hq path norm costs no external-order factor. -/
theorem sobolevOrbit_wordSum_le_block (n : ℕ) (a : LiftTangent) :
    wordSum standardDirection (sobolevOrbit P q p hp) n a ≤
      block standardDirection q (fun b : LiftTangent => pathTranslate P b p) n a := by
  rw [← sum_sobolev_word_levels P q p hp n a]
  unfold wordSum
  calc
    _ ≤ ∑ v : Fin n → Fin 4, ∑ w : SobolevWord q,
        ‖pathWordOperator P w (wordDerivative standardDirection (sobolevOrbit P q p hp) v a)‖ :=
      sum_le_sum (fun v _ => path_norm_le_sum_words P _)
    _ = _ := by
      rw [sum_comm]
      simp_rw [sobolevOrbit_word_coordinate P q p hp]

/-- Returning to the source derivative sum costs only the fixed Hq array size. -/
theorem block_le_card_sobolevOrbit_wordSum (n : ℕ) (a : LiftTangent) :
    block standardDirection q (fun b : LiftTangent => pathTranslate P b p) n a ≤
      (Fintype.card (SobolevWord q) : ℝ)*wordSum standardDirection (sobolevOrbit P q p hp) n a := by
  rw [← sum_sobolev_word_levels P q p hp n a]
  calc
    _ ≤ ∑ _w : SobolevWord q, wordSum standardDirection (sobolevOrbit P q p hp) n a := by
      apply sum_le_sum
      intro w _
      unfold wordSum
      apply sum_le_sum
      intro v _
      rw [← sobolevOrbit_word_coordinate P q p hp v w a]
      exact pathWordOperator_norm_le P w _
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]

end EulerCylinderSmoothOrbit

end
end

end

@[expose] public section

noncomputable section

namespace EulerCylinderPathProduct

open Set MeasureTheory ContinuousLinearMap Finset EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSmoothOrbit EulerLpCylinderTranslation
  EulerSobolevL2Product EulerParameterWordGevrey EulerCylinderSobolev
  EulerJetProductBounds EulerGevrey
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup (C(K,SobolevSpace P 6))` instance to shorten
typeclass synthesis. -/
local instance instCylinderPathProductBounds1 : NormedAddCommGroup (C(K,SobolevSpace P 6)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,SobolevSpace P 6))` instance to shorten typeclass
synthesis. -/
local instance instCylinderPathProductBounds2 : NormedSpace ℝ (C(K,SobolevSpace P 6)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,SobolevSpace P 6) →L[ℝ] C(K,SobolevSpace P 6))`
instance to shorten typeclass synthesis. -/
local instance instCylinderPathProductBounds3 : NormedAddCommGroup (C(K,SobolevSpace P 6) →L[ℝ]
    C(K,SobolevSpace P 6)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,SobolevSpace P 6) →L[ℝ] C(K,SobolevSpace P 6))`
instance to shorten typeclass synthesis. -/
local instance instCylinderPathProductBounds4 : NormedSpace ℝ (C(K,SobolevSpace P 6) →L[ℝ]
    C(K,SobolevSpace P 6)) :=
    inferInstance

variable (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (p q : C(K, LiftL2 P))
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

end
end

end

section

/-! Literal bounded bilinear nonlinearities preserve smooth continuous cylinder L² paths. -/

@[expose] public section

noncomputable section

namespace EulerCylinderPathProduct

open Set MeasureTheory ContinuousLinearMap Finset EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSmoothOrbit EulerLpCylinderTranslation
  EulerCylinderConstantMap EulerMetricTransport
open scoped ContDiff

/-- Component, given by `EuclideanSpace.proj i`. -/
def component (i : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj i

theorem component_norm (i : Fin 3) : ‖component i‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro u
  change ‖u i‖ ≤ (1 : ℝ)*‖u‖
  simpa only [one_mul] using PiLp.norm_apply_le u i

/-- Basis vector, given by `EuclideanSpace.single i 1`. -/
def basisVector (i : Fin 3) : Space := EuclideanSpace.single i 1

theorem sum_components (u : Space) : (∑ i : Fin 3, component i u • basisVector i) = u := by
  ext i
  simp [component, basisVector, Pi.single_apply, mul_ite]

theorem bilinear_components (B : Space →L[ℝ] Space →L[ℝ] Space) (u v : Space) :
    (∑ i : Fin 3, B (basisVector i) (component i u • v)) = B u v := by
  have h := congrArg (fun z : Space => B z v) (sum_components u)
  simpa only [map_sum, _root_.sum_apply, map_smul, smul_apply] using h

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (B : Space →L[ℝ] Space →L[ℝ] Space) (p q : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))

/-- Bilinear term, given by `pathMap P (B (basisVector i)) (scalarProductPath P (component i)
(component_norm i) p q hp hq)`. -/
def bilinearTerm (i : Fin 3) : C(K,LiftL2 P) :=
  pathMap P (B (basisVector i))
    (scalarProductPath P (component i) (component_norm i) p q hp hq)

theorem bilinearTerm_orbit (i : Fin 3) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (bilinearTerm P B p q hp hq i)) :=
  pathMap_orbit_contDiff P (B (basisVector i)) _
    (scalarProductPath_orbit P (component i) (component_norm i) p q hp hq)

/-- An arbitrary fixed bilinear vector operation on the actual L² paths. -/
def bilinearProductPath : C(K,LiftL2 P) := ∑ i : Fin 3, bilinearTerm P B p q hp hq i

theorem bilinearProductPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (bilinearProductPath P B p q hp hq)) :=
        by
  simp only [bilinearProductPath, map_sum]
  exact ContDiff.sum (fun i _ => bilinearTerm_orbit P B p q hp hq i)

theorem bilinearTerm_ae (i : Fin 3) (t : K) :
    (bilinearTerm P B p q hp hq i t : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => B (basisVector i) (component i (pointField P p hp t x) • pointField P q hq t x) := by
  filter_upwards [map_ae P (B (basisVector i))
      (scalarProductPath P (component i) (component_norm i) p q hp hq t),
    scalarProductPath_ae P (component i) (component_norm i) p q hp hq t] with x hm hp
  exact hm.trans (congrArg (B (basisVector i)) hp)

theorem bilinearProductPath_ae (t : K) :
    (bilinearProductPath P B p q hp hq t : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => B (pointField P p hp t x) (pointField P q hq t x) := by
  have ht : ∀ᶠ x in ae (liftMeasure P), ∀ i : Fin 3,
      bilinearTerm P B p q hp hq i t x =
        B (basisVector i) (component i (pointField P p hp t x) • pointField P q hq t x) :=
    Filter.eventually_all.mpr (fun i => bilinearTerm_ae P B p q hp hq i t)
  have hs := Lp.coeFn_fun_finsetSum (univ : Finset (Fin 3))
    (fun i => bilinearTerm P B p q hp hq i t)
  filter_upwards [hs,ht] with x hs ht
  change (∑ i : Fin 3, bilinearTerm P B p q hp hq i t) x = _
  rw [hs]
  exact (sum_congr rfl (fun i _ => ht i)).trans
    (bilinear_components B (pointField P p hp t x) (pointField P q hq t x))

/-- The reconstructed field agrees everywhere with the literal nonlinearity. -/
theorem pointField_bilinearProductPath (t : K) (x : LiftDomain P) :
    pointField P (bilinearProductPath P B p q hp hq)
      (bilinearProductPath_orbit P B p q hp hq) t x =
        B (pointField P p hp t x) (pointField P q hq t x) := by
  have he := Measure.eq_of_ae_eq
    ((pointField_ae P _ (bilinearProductPath_orbit P B p q hp hq) t).symm.trans
      (bilinearProductPath_ae P B p q hp hq t))
    (smoothField_continuous P _ (pointField_smooth P _ _ t))
    ((B.continuous.comp (smoothField_continuous P _ (pointField_smooth P p hp t))).clm_apply
      (smoothField_continuous P _ (pointField_smooth P q hq t)))
  exact congrFun he x

end EulerCylinderPathProduct

end
end

end
