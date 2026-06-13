/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Defs
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Iterated Derivative Helpers

Bounds on iterated derivatives of continuous linear maps and quadratic forms,
used in the Schwartz decay proof for the equilibrium Maxwellian.
-/

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

namespace VML

-- ============================================================================
-- Iterated derivative helpers for continuous linear maps
-- ============================================================================

/-- The iterated derivative of a continuous linear map vanishes at order ≥ 2. -/
lemma iteratedFDeriv_clm_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →L[𝕜] F) (n : ℕ) (hn : 2 ≤ n) (x : E) :
    iteratedFDeriv 𝕜 n f x = 0 := by
  rw [show n = (n - 1) + 1 from by omega, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp, show (fun y => fderiv 𝕜 (↑f) y) = fun _ => (f : E →L[𝕜] F) from
    funext fun y => f.hasFDerivAt.fderiv]
  rw [iteratedFDeriv_const_of_ne (by omega : n - 1 ≠ 0)]; simp

/-- The norm of the first iterated derivative of a CLM equals the operator norm. -/
lemma norm_iteratedFDeriv_one_clm {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E →L[𝕜] F) (x : E) :
    ‖iteratedFDeriv 𝕜 1 f x‖ = ‖f‖ := by
  rw [show (1:ℕ) = 0 + 1 from rfl, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp, show (fun y => fderiv 𝕜 (↑f) y) = fun _ => (f : E →L[𝕜] F) from
    funext fun y => f.hasFDerivAt.fderiv, iteratedFDeriv_zero_eq_comp,
    LinearIsometryEquiv.norm_map]

/-- `‖fderiv f v‖ = ‖iteratedFDeriv 1 f v‖`. Converts between the ContinuousLinearMap
    norm and the ContinuousMultilinearMap norm at order 1. -/
lemma norm_fderiv_eq_iteratedFDeriv_one {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E → F) (v : E) :
    ‖fderiv 𝕜 f v‖ = ‖iteratedFDeriv 𝕜 1 f v‖ := by
  rw [← norm_iteratedFDeriv_zero (𝕜 := 𝕜) (f := fderiv 𝕜 f), norm_iteratedFDeriv_fderiv]

-- ============================================================================
-- Polynomial/quadratic iterated derivative bounds
-- ============================================================================

/-- For `Fin 3 → ℝ` with sup norm: ‖v‖² ≤ normSq v = ∑ vᵢ². -/
lemma norm_sq_le_normSq (v : Fin 3 → ℝ) : ‖v‖ ^ 2 ≤ normSq v := by
  unfold normSq dotProduct; simp only [Fin.sum_univ_three]
  obtain ⟨j, _, hj⟩ := (Finset.univ (α := Fin 3)).exists_max_image
    (fun i => ‖v i‖) ⟨0, Finset.mem_univ _⟩
  have hj_eq : ‖v‖ = ‖v j‖ :=
    le_antisymm
      (pi_norm_le_iff_of_nonneg (norm_nonneg (v j)) |>.mpr
        (fun i => hj i (Finset.mem_univ i)))
      (norm_le_pi_norm v j)
  calc ‖v‖ ^ 2 = ‖v j‖ ^ 2 := by rw [hj_eq]
    _ = |v j| ^ 2 := by rw [Real.norm_eq_abs]
    _ = v j * v j := by rw [sq_abs]; ring
    _ ≤ ∑ i : Fin 3, v i * v i :=
        Finset.single_le_sum (fun i _ => mul_self_nonneg (v i)) (Finset.mem_univ j)
    _ = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := by simp [Fin.sum_univ_three]

lemma contDiff_negNormSq_div (T : ℝ) :
    ContDiff ℝ ⊤ (fun v : Fin 3 → ℝ => -(normSq v) / (2 * T)) := by
  apply ContDiff.div_const
  apply ContDiff.neg
  unfold normSq dotProduct
  exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)

/-- ‖iteratedFDeriv i (v_j²) v‖ ≤ 2(1+‖v‖) for i ≥ 1, via Leibniz on proj_j * proj_j. -/
lemma norm_iteratedFDeriv_proj_sq_le (j : Fin 3) (i : ℕ) (hi : 1 ≤ i)
    (v : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ i (fun w : Fin 3 → ℝ => w j * w j) v‖ ≤ 2 * (1 + ‖v‖) := by
  set pj := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) j
  have hpj : ContDiff ℝ ⊤ (fun w : Fin 3 → ℝ => w j) := contDiff_apply ℝ ℝ j
  have hleib := norm_iteratedFDeriv_mul_le hpj hpj v (n := i) le_top
  have hpj_le : ‖pj‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      simp only [one_mul]; exact norm_le_pi_norm w j
  have hpj_eq : (fun w : Fin 3 → ℝ => w j) = (pj : (Fin 3 → ℝ) →L[ℝ] ℝ) := rfl
  have hpj_sq : ‖pj‖ * ‖pj‖ ≤ 1 := mul_le_one₀ hpj_le (norm_nonneg pj) hpj_le
  refine le_trans hleib ?_
  by_cases h3 : 3 ≤ i
  · refine le_trans (Finset.sum_nonpos fun s hs => ?_) (by positivity)
    rw [Finset.mem_range] at hs
    rcases show s ≥ 2 ∨ i - s ≥ 2 from by omega with h | h
    · simp [hpj_eq, iteratedFDeriv_clm_zero pj s h v]
    · simp [hpj_eq, iteratedFDeriv_clm_zero pj (i - s) h v]
  · push Not at h3; interval_cases i
    · -- i = 1
      simp only [Nat.reduceAdd, Nat.reduceSub, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, Nat.choose, norm_iteratedFDeriv_zero, hpj_eq,
        norm_iteratedFDeriv_one_clm pj v]
      push_cast
      have := mul_le_mul_of_nonneg_right (pj.le_opNorm v) (norm_nonneg pj)
      nlinarith [norm_nonneg v]
    · -- i = 2
      simp only [Nat.reduceAdd, Nat.reduceSub, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, Nat.choose, norm_iteratedFDeriv_zero, hpj_eq,
        norm_iteratedFDeriv_one_clm pj v,
        iteratedFDeriv_clm_zero pj 2 le_rfl v, norm_zero]
      push_cast; linarith [norm_nonneg v]

/-- Derivative bound for the quadratic form q(v) = -normSq(v)/(2T).
    Since q is a degree-2 polynomial: fderiv is O(1+‖v‖), second derivative is constant,
    and all higher derivatives vanish. -/
lemma quadratic_iteratedFDeriv_bound (T : ℝ) (hT : 0 < T) (k : ℕ) :
    ∃ c > 0, ∀ v : Fin 3 → ℝ, ∀ i : ℕ, 1 ≤ i → i ≤ k →
      ‖iteratedFDeriv ℝ i (fun v => -(normSq v) / (2 * T)) v‖ ≤ (c * (1 + ‖v‖)) ^ i := by
  refine ⟨3 / T + 1, by positivity, fun v i hi1 hik => ?_⟩
  set c := 3 / T + 1
  -- Step 1: Express q as sum of scaled components and bound iteratedFDeriv
  have hfn_eq : (fun v : Fin 3 → ℝ => -(normSq v) / (2 * T)) =
      (fun v => ∑ j : Fin 3, -(v j * v j) / (2 * T)) := by
    ext w
    unfold normSq dotProduct
    simp [Fin.sum_univ_three]
    ring
  have hcomp_smooth : ∀ j : Fin 3,
      ContDiff ℝ ⊤ (fun v : Fin 3 → ℝ => -(v j * v j) / (2 * T)) := fun j =>
    ((contDiff_apply ℝ ℝ j).mul (contDiff_apply ℝ ℝ j)).neg.div_const _
  -- Each component: -(v_j²)/(2T) = (-1/(2T)) • (v_j²)
  have hcomp_eq : ∀ j : Fin 3, (fun v : Fin 3 → ℝ => -(v j * v j) / (2 * T)) =
      (-1 / (2 * T)) • (fun v : Fin 3 → ℝ => v j * v j) := by
    intro j; ext w; simp [Pi.smul_apply, smul_eq_mul]; ring
  -- Bound: ‖iteratedFDeriv i q v‖ ≤ (3/T)(1+‖v‖)
  have hbound : ‖iteratedFDeriv ℝ i (fun v : Fin 3 → ℝ => -(normSq v) / (2 * T)) v‖ ≤
      3 / T * (1 + ‖v‖) := by
    rw [hfn_eq]
    -- Distribute iteratedFDeriv through the sum
    have hsmooth_i : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
        ContDiff ℝ (↑i) (fun v : Fin 3 → ℝ => -(v j * v j) / (2 * T)) :=
      fun j _ => (hcomp_smooth j).of_le le_top
    rw [show (fun v : Fin 3 → ℝ => ∑ j : Fin 3, -(v j * v j) / (2 * T)) =
      (fun v => ∑ j ∈ Finset.univ, (fun j (v : Fin 3 → ℝ) => -(v j * v j) / (2 * T)) j v) from
      by ext w; simp]
    have hsum := congrFun (iteratedFDeriv_sum (fun j hj => hsmooth_i j hj)) v
    -- hsum rewrites LHS to the sum form
    rw [hsum, Finset.sum_apply]
    refine le_trans (norm_sum_le _ _) ?_
    -- Bound each component using smul decomposition
    have habs : |(-1 : ℝ) / (2 * T)| = 1 / (2 * T) := by
      rw [abs_of_nonpos (by exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith))]; ring
    refine le_trans (Finset.sum_le_sum (g := fun _ => 1 / T * (1 + ‖v‖))
      fun j _ => ?_) ?_
    · rw [show (fun v : Fin 3 → ℝ => -(v j * v j) / (2 * T)) =
        ((-1 / (2 * T)) • fun v : Fin 3 → ℝ => v j * v j) from hcomp_eq j]
      rw [iteratedFDeriv_const_smul_apply
        (((contDiff_apply ℝ ℝ j).mul (contDiff_apply ℝ ℝ j)).contDiffAt.of_le le_top),
        norm_smul, Real.norm_eq_abs, habs]
      calc 1 / (2 * T) * ‖iteratedFDeriv ℝ i (fun w : Fin 3 → ℝ => w j * w j) v‖
          ≤ 1 / (2 * T) * (2 * (1 + ‖v‖)) :=
            mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_proj_sq_le j i hi1 v)
              (by positivity)
        _ = 1 / T * (1 + ‖v‖) := by ring
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring_nf
      exact le_refl _
  -- Step 2: (3/T)(1+‖v‖) ≤ c(1+‖v‖) ≤ (c(1+‖v‖))^i
  calc ‖iteratedFDeriv ℝ i (fun v => -(normSq v) / (2 * T)) v‖
      ≤ 3 / T * (1 + ‖v‖) := hbound
    _ ≤ c * (1 + ‖v‖) := by nlinarith [norm_nonneg v]
    _ ≤ (c * (1 + ‖v‖)) ^ i := le_self_pow₀
        (by nlinarith [norm_nonneg v, show (0:ℝ) ≤ 3 / T from by positivity])
        (by omega)

end VML
