/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnalyticBridge.SupBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Product
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Composition

/-! # Steps 2 and 3: analytic `snorm` bounds for `∂_i T` and `∂_i T ∂_j T`

From the pointwise bounds of `SupBound` we obtain `⟦∂_i T⟧_{n,2a} ≤ C_h` for every `n`, and then
`⟦∂_i T ∂_j T⟧_{n,2a} ≤ 4 C_h²` by the Appendix B product estimate.
-/

@[expose] public section

noncomputable section

open scoped ContDiff
open Homogenization MeasureTheory

namespace AVenhance.Infra.Section5.AnalyticBridge

open AVenhance AVenhance.FaaDiBruno

/-- An absolute constant dominating `(n+3)⁵ / 2ⁿ`. -/
theorem exists_poly_le_two_pow :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, ((n : ℝ) + 3) ^ 5 ≤ K * 2 ^ n := by
  have ht : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ 5 / 2 ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 5 (by norm_num)
  have ht' := ht.comp (Filter.tendsto_add_atTop_nat 3)
  obtain ⟨M, hM⟩ := ht'.bddAbove_range
  refine ⟨max 1 (8 * M), le_max_left _ _, fun n => ?_⟩
  have h1 : ((n + 3 : ℕ) : ℝ) ^ 5 / 2 ^ (n + 3) ≤ M :=
    hM ⟨n, rfl⟩
  have h2 : (0 : ℝ) < 2 ^ (n + 3) := by positivity
  rw [div_le_iff₀ h2] at h1
  have h3 : ((n : ℝ) + 3) ^ 5 ≤ M * 2 ^ (n + 3) := by simpa using h1
  have h4 : (M * 2 ^ (n + 3) : ℝ) = 8 * M * 2 ^ n := by ring
  rw [h4] at h3
  exact h3.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- `(n+3)! (n+1)² ≤ K 2ⁿ n!`. -/
theorem factorial_mul_sq_le {K : ℝ} (hK : ∀ n : ℕ, ((n : ℝ) + 3) ^ 5 ≤ K * 2 ^ n) (n : ℕ) :
    ((n + 3).factorial : ℝ) * ((n : ℝ) + 1) ^ 2 ≤ K * 2 ^ n * n.factorial := by
  have hf : ((n + 3).factorial : ℝ) = n.factorial * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) +
      3)) := by
    rw [show n + 3 = (n + 2) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    ring
  have hpoly : ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 2) * ((n : ℝ) + 3) ≤ ((n : ℝ) + 3) ^ 5 := by
    have h1 : (n : ℝ) + 1 ≤ (n : ℝ) + 3 := by linarith
    have h2 : (n : ℝ) + 2 ≤ (n : ℝ) + 3 := by linarith
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 2) * ((n : ℝ) + 3)
        ≤ ((n : ℝ) + 3) ^ 3 * ((n : ℝ) + 3) * ((n : ℝ) + 3) := by gcongr
      _ = ((n : ℝ) + 3) ^ 5 := by ring
  have hfac : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  calc ((n + 3).factorial : ℝ) * ((n : ℝ) + 1) ^ 2
      = n.factorial * (((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
        rw [hf]; ring
    _ ≤ n.factorial * (K * 2 ^ n) := mul_le_mul_of_nonneg_left (hpoly.trans (hK n)) hfac
    _ = K * 2 ^ n * n.factorial := by ring

/-- Abstract-real core of step 2. -/
theorem grad_bound_le_radius_form {K : ℝ}
    (hK : ∀ n : ℕ, ((n : ℝ) + 3) ^ 5 ≤ K * 2 ^ n) {c a : ℝ} (hc : 0 ≤ c) (ha : 0 < a)
    (n : ℕ) :
    c * (((n + 3).factorial : ℝ) * a ^ (n + 3)) ≤
      (c * K * a ^ 3) * (2 * a) ^ n * n.factorial / ((n : ℝ) + 1) ^ 2 := by
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  have h := factorial_mul_sq_le hK n
  have ha' : (0 : ℝ) ≤ a ^ (n + 3) := by positivity
  calc c * (((n + 3).factorial : ℝ) * a ^ (n + 3)) * ((n : ℝ) + 1) ^ 2
      = c * a ^ (n + 3) * (((n + 3).factorial : ℝ) * ((n : ℝ) + 1) ^ 2) := by ring
    _ ≤ c * a ^ (n + 3) * (K * 2 ^ n * n.factorial) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg hc ha')
    _ = (c * K * a ^ 3) * (2 * a) ^ n * n.factorial := by
        rw [mul_pow, pow_add]; ring

/-- Smoothness of the coordinate derivative `∂_v f`. -/
theorem contDiff_fderiv_apply_basis {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) (v : Fin 2) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ f y (basisVec v)) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  exact (ContinuousLinearMap.apply ℝ ℝ (basisVec v)).contDiff.comp hd

/-- Step 2: `⟦∂_v f⟧_{n,2a} ≤ 3 sc K B a³` for every order `n`. -/
theorem snorm_fderiv_le {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) (hp : IsZ2Periodic f)
    {B a K : ℝ} (hB : 0 ≤ B) (ha : 1 ≤ a)
    (hK : ∀ n : ℕ, ((n : ℝ) + 3) ^ 5 ≤ K * 2 ^ n)
    (hreg : ∀ (n : ℕ) (i : Fin n → Fin 2),
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
    (hreg : ∀ (n : ℕ) (i : Fin n → Fin 2),
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
    (hreg : ∀ (n : ℕ) (i : Fin n → Fin 2),
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

end AVenhance.Infra.Section5.AnalyticBridge

end
