/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativePositiveSup
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.GradSnorm

/-! # Relative Positive Product

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open scoped ContDiff
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section5.RelativeError
open AVenhance AVenhance.FaaDiBruno AVenhance.Infra.Section5.AnalyticBridge

/-- Step 2: `⟦∂_v f⟧_{n,2a} ≤ 3 sc K B a³` for every order `n`. -/
theorem snorm_fderiv_le {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) (hp : IsZ2Periodic f)
    {B a K : ℝ} (hB : 0 ≤ B) (ha : 1 ≤ a)
    (hK : ∀ n : ℕ, ((n : ℝ) + 3) ^ 5 ≤ K * 2 ^ n)
    (hreg : ∀ (n : ℕ) (i : Fin n → Fin 2), 0 < n →
      Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j)))) ≤
        B * n.factorial * a ^ n)
    (v : Fin 2) (n : ℕ) :
    snorm (fun y => fderiv ℝ f y (basisVec v)) n (2 * a) ≤
      ENNReal.ofReal (3 * sobolevConst * B * K * a ^ 3) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hg := contDiff_fderiv_apply_basis hf v
  have hsc := sobolevConst_pos
  refine snorm_le_of_derivativeSup_le _ (by positivity) ?_
  unfold derivativeSup
  refine iSup_le fun I => ?_
  unfold partialSup
  refine (eLpNormEssSup_le_of_ae_bound (C := 3 * sobolevConst * (B * ((n + 3).factorial : ℝ) *
      a ^ (n + 3))) (Filter.Eventually.of_forall fun x => ?_)).trans ?_
  · rw [orderedPartial_eq_iteratedFDeriv hg, Real.norm_eq_abs]
    exact abs_iteratedFDeriv_fderiv_le hf hp hB ha hreg n I v x
  · apply ENNReal.ofReal_le_ofReal
    have := grad_bound_le_radius_form hK (c := 3 * sobolevConst * B) (a := a)
      (by positivity) ha0 n
    calc 3 * sobolevConst * (B * ((n + 3).factorial : ℝ) * a ^ (n + 3))
        = 3 * sobolevConst * B * (((n + 3).factorial : ℝ) * a ^ (n + 3)) := by ring
      _ ≤ _ := this
      _ = _ := by ring

/-- `snormMax` of `∂_v f` up to order `n`. -/
theorem snormMax_fderiv_le {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) (hp : IsZ2Periodic f)
    {B a K : ℝ} (hB : 0 ≤ B) (ha : 1 ≤ a)
    (hK : ∀ n : ℕ, ((n : ℝ) + 3) ^ 5 ≤ K * 2 ^ n)
    (hreg : ∀ (n : ℕ) (i : Fin n → Fin 2), 0 < n →
      Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j)))) ≤
        B * n.factorial * a ^ n)
    (v : Fin 2) (n : ℕ) :
    snormMax (fun y => fderiv ℝ f y (basisVec v)) n (2 * a) ≤
      ENNReal.ofReal (3 * sobolevConst * B * K * a ^ 3) :=
  iSup_le fun k => snorm_fderiv_le hf hp hB ha hK hreg v k

/-- Step 3: `⟦∂_i f ∂_j f⟧_{n,2a} ≤ 4 C_h²`. -/
theorem snorm_fderiv_mul_le {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) (hp : IsZ2Periodic f)
    {B a K : ℝ} (hB : 0 ≤ B) (ha : 1 ≤ a)
    (hK : ∀ n : ℕ, ((n : ℝ) + 3) ^ 5 ≤ K * 2 ^ n)
    (hreg : ∀ (n : ℕ) (i : Fin n → Fin 2), 0 < n →
      Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j)))) ≤
        B * n.factorial * a ^ n)
    (i j : Fin 2) (n : ℕ) :
    snorm (fun y => fderiv ℝ f y (basisVec i) * fderiv ℝ f y (basisVec j)) n (2 * a) ≤
      ENNReal.ofReal (4 * (3 * sobolevConst * B * K * a ^ 3) ^ 2) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hi := contDiff_fderiv_apply_basis hf i
  have hj := contDiff_fderiv_apply_basis hf j
  have hprod := productEstimate (n := n) (fun y => fderiv ℝ f y (basisVec i))
    (fun y => fderiv ℝ f y (basisVec j))
    (hi.of_le (by exact_mod_cast le_top)) (hj.of_le (by exact_mod_cast le_top))
    (R := 2 * a) (by positivity)
  refine hprod.trans ?_
  have hCi := snormMax_fderiv_le hf hp hB ha hK hreg i n
  have hCj := snormMax_fderiv_le hf hp hB ha hK hreg j n
  have hsc := sobolevConst_pos
  have hC : 0 ≤ 3 * sobolevConst * B * K * a ^ 3 := by
    have hK0 : 0 ≤ K := by
      have := hK 0
      simp only [Nat.cast_zero, zero_add, pow_zero, mul_one] at this
      exact le_trans (by positivity) this
    positivity
  calc 4 * snormMax (fun y => fderiv ℝ f y (basisVec i)) n (2 * a) *
        snormMax (fun y => fderiv ℝ f y (basisVec j)) n (2 * a)
      ≤ 4 * ENNReal.ofReal (3 * sobolevConst * B * K * a ^ 3) *
        ENNReal.ofReal (3 * sobolevConst * B * K * a ^ 3) := by gcongr
    _ = ENNReal.ofReal (4 * (3 * sobolevConst * B * K * a ^ 3) ^ 2) := by
        rw [show (4 : ENNReal) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end AVenhance.Infra.Section5.RelativeError
