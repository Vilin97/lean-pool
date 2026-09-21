/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
import LeanPool.NashEmbedding.NashEmbedding.Torus.Basic

/-!
# Bump construction for Theorem A

A fixed one-dimensional bump `η`, its dilations `η(β·)` with closed-form
mass identities, and the product bump `∏ₖ η(βₖ yₖ)` on `ℝⁿ` with its Gram
matrix `∫ ∂ᵢψ ∂ⱼψ` (diagonal, explicit).

## Main contents

* `bumpRadius n` — radius `ρ` with `ρ √n < π/2`, so a rotated product bump
  supported in the box of radius `ρ` lies in `(-π,π)ⁿ`.
* `eta n` — a `C^∞` bump on `ℝ`, `η = 1` on `[-ρ/2, ρ/2]`, `supp η = (-ρ,ρ)`.
* `etaMass n = ∫ η²`, `etaDerivMass n = ∫ η'²`, both positive.
* `dil n β t = η (β t)`; `∫ (dil β)² = etaMass/β`, `∫ (dil β)'² = β·etaDerivMass`,
  `∫ dil β · (dil β)' = 0`.
-/

open scoped BigOperators ContDiff
open MeasureTheory Real
open scoped Matrix

noncomputable section

namespace NashEmbedding

/-! ## The basic one-dimensional bump -/

/-- Radius `ρ := π / (2√n + 1)`; then `ρ √n < π/2` for every `n`. -/
def bumpRadius (n : ℕ) : ℝ := π / (2 * Real.sqrt n + 1)

lemma bumpRadius_pos (n : ℕ) : 0 < bumpRadius n := by
  unfold bumpRadius
  positivity

lemma bumpRadius_mul_sqrt_lt (n : ℕ) : bumpRadius n * Real.sqrt n < π / 2 := by
  unfold bumpRadius
  have h : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Real.pi_pos]

/-- The basic bump as a `ContDiffBump` centred at `0`, `rIn = ρ/2`, `rOut = ρ`. -/
def bump1D (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨bumpRadius n / 2, bumpRadius n, by linarith [bumpRadius_pos n], by linarith [bumpRadius_pos n]⟩

/-- The basic bump as a function `ℝ → ℝ`. -/
def eta (n : ℕ) : ℝ → ℝ := fun t => bump1D n t

lemma eta_contDiff (n : ℕ) : ContDiff ℝ ∞ (eta n) := (bump1D n).contDiff

lemma eta_continuous (n : ℕ) : Continuous (eta n) := (eta_contDiff n).continuous

lemma eta_hasCompactSupport (n : ℕ) : HasCompactSupport (eta n) := (bump1D n).hasCompactSupport

lemma eta_nonneg (n : ℕ) (t : ℝ) : 0 ≤ eta n t := (bump1D n).nonneg

lemma eta_zero (n : ℕ) : eta n 0 = 1 :=
  (bump1D n).one_of_mem_closedBall (by simp [bump1D]; linarith [bumpRadius_pos n])

lemma eta_eq_zero_of_le {n : ℕ} {t : ℝ} (ht : bumpRadius n ≤ |t|) : eta n t = 0 :=
  (bump1D n).zero_of_le_dist (by simpa [bump1D, Real.dist_eq] using ht)

lemma eta_support (n : ℕ) : Function.support (eta n) = Metric.ball 0 (bumpRadius n) :=
  (bump1D n).support_eq

lemma abs_lt_of_eta_ne_zero {n : ℕ} {t : ℝ} (h : eta n t ≠ 0) : |t| < bumpRadius n := by
  by_contra hc
  exact h (eta_eq_zero_of_le (not_lt.mp hc))

/-- `∫ η²`. -/
def etaMass (n : ℕ) : ℝ := ∫ t, eta n t ^ 2

/-- `∫ η'²`. -/
def etaDerivMass (n : ℕ) : ℝ := ∫ t, deriv (eta n) t ^ 2

lemma deriv_eta_continuous (n : ℕ) : Continuous (deriv (eta n)) :=
  (eta_contDiff n).continuous_deriv NashEmbedding.Sobolev.one_le_infty

lemma deriv_eta_hasCompactSupport (n : ℕ) : HasCompactSupport (deriv (eta n)) :=
  (eta_hasCompactSupport n).deriv

lemma etaMass_pos (n : ℕ) : 0 < etaMass n := by
  unfold etaMass
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
  · exact (eta_continuous n).pow 2
  · exact (eta_hasCompactSupport n).comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  · intro t; positivity
  · simp [eta_zero]

lemma etaDerivMass_pos (n : ℕ) : 0 < etaDerivMass n := by
  unfold etaDerivMass
  -- some point has nonzero derivative, else η would be constant
  have hnc : ∃ t, deriv (eta n) t ≠ 0 := by
    by_contra h
    push Not at h
    have hdiff : Differentiable ℝ (eta n) := (eta_contDiff n).differentiable NashEmbedding.Sobolev.infty_ne_zero
    have hconst := is_const_of_deriv_eq_zero hdiff h
    have h1 := hconst 0 (bumpRadius n)
    rw [eta_zero, eta_eq_zero_of_le (by rw [abs_of_pos (bumpRadius_pos n)])] at h1
    exact one_ne_zero h1
  obtain ⟨t, ht⟩ := hnc
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := t)
  · exact (deriv_eta_continuous n).pow 2
  · exact (deriv_eta_hasCompactSupport n).comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  · intro s; positivity
  · simpa using ht

/-! ## Dilations -/

/-- The dilated bump `η(βt)`. -/
def dil (n : ℕ) (β : ℝ) : ℝ → ℝ := fun t => eta n (β * t)

lemma dil_contDiff (n : ℕ) (β : ℝ) : ContDiff ℝ ∞ (dil n β) :=
  (eta_contDiff n).comp (contDiff_const.mul contDiff_id)

lemma dil_continuous (n : ℕ) (β : ℝ) : Continuous (dil n β) := (dil_contDiff n β).continuous

lemma dil_hasCompactSupport (n : ℕ) {β : ℝ} (hβ : 0 < β) : HasCompactSupport (dil n β) := by
  have h : dil n β = eta n ∘ (Homeomorph.mulLeft₀ β hβ.ne') := by
    rfl
  rw [h]
  exact (eta_hasCompactSupport n).comp_homeomorph _

lemma abs_lt_of_dil_ne_zero {n : ℕ} {β t : ℝ} (hβ : 1 ≤ β) (h : dil n β t ≠ 0) :
    |t| < bumpRadius n := by
  have h1 := abs_lt_of_eta_ne_zero h
  rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < β)] at h1
  nlinarith [abs_nonneg t]

lemma deriv_dil (n : ℕ) (β : ℝ) (t : ℝ) :
    deriv (dil n β) t = β * deriv (eta n) (β * t) := by
  unfold dil
  rw [deriv_comp_mul_left, smul_eq_mul]

lemma deriv_dil_continuous (n : ℕ) (β : ℝ) : Continuous (deriv (dil n β)) :=
  (dil_contDiff n β).continuous_deriv NashEmbedding.Sobolev.one_le_infty

lemma deriv_dil_hasCompactSupport (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    HasCompactSupport (deriv (dil n β)) :=
  (dil_hasCompactSupport n hβ).deriv

lemma integral_dil_sq (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∫ t, dil n β t ^ 2 = etaMass n / β := by
  unfold dil etaMass
  have h := Measure.integral_comp_mul_left (fun t => eta n t ^ 2) β
  try simp only at h
  rw [h, abs_of_pos (inv_pos.mpr hβ), smul_eq_mul, inv_mul_eq_div]

lemma integral_deriv_dil_sq (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∫ t, deriv (dil n β) t ^ 2 = β * etaDerivMass n := by
  simp_rw [deriv_dil]
  have h := Measure.integral_comp_mul_left (fun t => deriv (eta n) t ^ 2) β
  try simp only at h
  simp_rw [mul_pow]
  rw [integral_const_mul, h, abs_of_pos (inv_pos.mpr hβ), smul_eq_mul]
  unfold etaDerivMass
  field_simp

lemma integral_dil_mul_deriv (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∫ t, dil n β t * deriv (dil n β) t = 0 := by
  have hd : Differentiable ℝ (dil n β) := (dil_contDiff n β).differentiable NashEmbedding.Sobolev.infty_ne_zero
  have hint : ∀ f g : ℝ → ℝ, Continuous f → Continuous g → HasCompactSupport g →
      Integrable (fun t => f t * g t) := fun f g hf hg hgs =>
    (hf.mul hg).integrable_of_hasCompactSupport (hgs.mul_left)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := dil n β) (g := dil n β) (v := (1 : ℝ))
    (hint _ _ (deriv_dil_continuous n β) (dil_continuous n β) (dil_hasCompactSupport n hβ))
    (hint _ _ (dil_continuous n β) (deriv_dil_continuous n β) (deriv_dil_hasCompactSupport n hβ))
    (hint _ _ (dil_continuous n β) (dil_continuous n β) (dil_hasCompactSupport n hβ))
    (fun x _ => hd.differentiableAt) (fun x _ => hd.differentiableAt)
  simp only [fderiv_apply_one_eq_deriv] at key
  have h2 : ∫ t, dil n β t * deriv (dil n β) t = ∫ t, deriv (dil n β) t * dil n β t := by
    congr 1; funext t; ring
  linarith

/-! ## The product bump on `ℝⁿ` -/

variable {n : ℕ}

/-- The product bump `ψ_β(y) = ∏ₖ η(βₖ yₖ)`. -/
def prodBump (n : ℕ) (β : Fin n → ℝ) (y : Fin n → ℝ) : ℝ := ∏ k, dil n (β k) (y k)

lemma prodBump_contDiff (β : Fin n → ℝ) : ContDiff ℝ ∞ (prodBump n β) := by
  have h : prodBump n β = ∏ k : Fin n, (fun y : Fin n → ℝ => dil n (β k) (y k)) := by
    funext y; simp [prodBump, Finset.prod_apply]
  rw [h]
  exact contDiff_prod' fun k _ => (dil_contDiff n (β k)).comp (contDiff_apply ℝ ℝ k)

lemma prodBump_continuous (β : Fin n → ℝ) : Continuous (prodBump n β) :=
  (prodBump_contDiff β).continuous

lemma abs_lt_of_prodBump_ne_zero {β : Fin n → ℝ} (hβ : ∀ k, 1 ≤ β k) {y : Fin n → ℝ}
    (h : prodBump n β y ≠ 0) (k : Fin n) : |y k| < bumpRadius n := by
  unfold prodBump at h
  rw [Finset.prod_ne_zero_iff] at h
  exact abs_lt_of_dil_ne_zero (hβ k) (h k (Finset.mem_univ k))

lemma prodBump_hasCompactSupport {β : Fin n → ℝ} (hβ : ∀ k, 1 ≤ β k) :
    HasCompactSupport (prodBump n β) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(bumpRadius n • (1 : Fin n → ℝ)))
    (b := bumpRadius n • (1 : Fin n → ℝ)))
  intro y hy
  by_contra h
  apply hy
  constructor <;> intro k <;>
    simp only [Pi.neg_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] <;>
    linarith [abs_lt.mp (abs_lt_of_prodBump_ne_zero hβ h k)]

/-- The `k`-th factor of `∂ᵢψ_β`: the derivative of the dilated bump when `k = i`,
the dilated bump itself otherwise. -/
def factor (n : ℕ) (β : Fin n → ℝ) (i k : Fin n) : ℝ → ℝ :=
  if k = i then deriv (dil n (β k)) else dil n (β k)

lemma prodBump_update (β : Fin n → ℝ) (y : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    prodBump n β (Function.update y i t)
      = dil n (β i) t * ∏ k ∈ Finset.univ.erase i, dil n (β k) (y k) := by
  unfold prodBump
  rw [← Finset.mul_prod_erase Finset.univ (fun k => dil n (β k) (Function.update y i t k))
    (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

lemma fderiv_prodBump_single (β : Fin n → ℝ) (y : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (prodBump n β) y (Pi.single i 1) = ∏ k, factor n β i k (y k) := by
  have hd : HasFDerivAt (prodBump n β) (fderiv ℝ (prodBump n β) y) y :=
    ((prodBump_contDiff β).differentiable NashEmbedding.Sobolev.infty_ne_zero y).hasFDerivAt
  have h1 := NashEmbedding.Sobolev.hasDerivAt_update_of_hasFDerivAt hd i
  have h2 : HasDerivAt (fun t => prodBump n β (Function.update y i t))
      (deriv (dil n (β i)) (y i) * ∏ k ∈ Finset.univ.erase i, dil n (β k) (y k)) (y i) := by
    simp_rw [prodBump_update]
    exact ((dil_contDiff n (β i)).differentiable NashEmbedding.Sobolev.infty_ne_zero (y i)).hasDerivAt.mul_const _
  rw [h1.unique h2, ← Finset.mul_prod_erase Finset.univ (fun k => factor n β i k (y k))
    (Finset.mem_univ i)]
  simp only [factor, if_true]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [if_neg (Finset.ne_of_mem_erase hk)]

/-! ## The Gram matrix -/

/-- The Gram matrix `∫ ∂ᵢχ ∂ⱼχ` of a real function on `ℝⁿ`. -/
def gram (χ : (Fin n → ℝ) → ℝ) (i j : Fin n) : ℝ :=
  ∫ x, fderiv ℝ χ x (Pi.single i 1) * fderiv ℝ χ x (Pi.single j 1)

/-- The Gram matrix of the product bump is diagonal with explicit entries. -/
theorem gram_prodBump {β : Fin n → ℝ} (hβ : ∀ k, 0 < β k) (i j : Fin n) :
    gram (prodBump n β) i j
      = if i = j then β i * etaDerivMass n * ∏ k ∈ Finset.univ.erase i, etaMass n / β k
        else 0 := by
  unfold gram
  simp_rw [fderiv_prodBump_single, ← Finset.prod_mul_distrib]
  rw [volume_pi, integral_fintype_prod_eq_prod (fun k t => factor n β i k t * factor n β j k t)]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp only [factor, if_true, ← sq]
      exact integral_deriv_dil_sq n (hβ i)
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hk' := Finset.ne_of_mem_erase hk
      simp only [factor, if_neg hk', ← sq]
      exact integral_dil_sq n (hβ k)
  · rw [if_neg hij]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [factor, if_true, if_neg hij]
    have h := integral_dil_mul_deriv n (hβ i)
    simp_rw [mul_comm (dil n (β i) _)] at h
    exact h

/-! ## Rotation by a matrix with `|det| = 1` -/

/-- `χ(x) = ψ_β(M x)`. -/
def rotBump (n : ℕ) (β : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  prodBump n β (M.mulVec x)

lemma mulVec_eq_clm (M : Matrix (Fin n) (Fin n) ℝ) :
    (fun x : Fin n → ℝ => M.mulVec x)
      = ⇑(LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)) := by
  funext x; simp

lemma mulVec_contDiff (M : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ ∞ (fun x : Fin n → ℝ => M.mulVec x) := by
  rw [mulVec_eq_clm]; exact ContinuousLinearMap.contDiff _

lemma rotBump_contDiff (β : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ ∞ (rotBump n β M) :=
  (prodBump_contDiff β).comp (mulVec_contDiff M)

lemma fderiv_rotBump_single (β : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin n) :
    fderiv ℝ (rotBump n β M) x (Pi.single i 1)
      = ∑ k, M k i * fderiv ℝ (prodBump n β) (M.mulVec x) (Pi.single k 1) := by
  have hψ : DifferentiableAt ℝ (prodBump n β) (M.mulVec x) :=
    (prodBump_contDiff β).differentiable NashEmbedding.Sobolev.infty_ne_zero _
  have hL : HasFDerivAt (fun x : Fin n → ℝ => M.mulVec x)
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)) x := by
    rw [mulVec_eq_clm]; exact ContinuousLinearMap.hasFDerivAt _
  have hc : HasFDerivAt (rotBump n β M)
      ((fderiv ℝ (prodBump n β) (M.mulVec x)).comp
        (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M))) x :=
    hψ.hasFDerivAt.comp x hL
  rw [hc.fderiv, ContinuousLinearMap.comp_apply]
  have hcol : (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)) (Pi.single i 1)
      = ∑ k, M k i • (Pi.single k (1 : ℝ) : Fin n → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hcol, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul]

lemma det_ne_zero_of_abs_det_eq_one {M : Matrix (Fin n) (Fin n) ℝ} (hdet : |M.det| = 1) :
    M.det ≠ 0 := by
  intro h; rw [h, abs_zero] at hdet; exact zero_ne_one hdet

lemma integrable_comp_mulVec {M : Matrix (Fin n) (Fin n) ℝ} (hdet : |M.det| = 1)
    {G : (Fin n → ℝ) → ℝ} (hG : Continuous G) (hGi : Integrable G) :
    Integrable (fun x => G (M.mulVec x)) := by
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (det_ne_zero_of_abs_det_eq_one hdet)
  have h2 : Integrable G (Measure.map (Matrix.toLin' M) volume) := by
    rw [hmap]; exact hGi.smul_measure (by simp)
  have h3 := (integrable_map_measure hG.aestronglyMeasurable
    (Matrix.toLin' M).continuous_of_finiteDimensional.aemeasurable).mp h2
  simpa [Function.comp_def, Matrix.toLin'_apply] using h3

lemma integral_comp_mulVec {M : Matrix (Fin n) (Fin n) ℝ} (hdet : |M.det| = 1)
    {G : (Fin n → ℝ) → ℝ} (hG : Continuous G) :
    ∫ x, G (M.mulVec x) = ∫ y, G y := by
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (det_ne_zero_of_abs_det_eq_one hdet)
  have h1 : ∫ y, G y ∂(Measure.map (Matrix.toLin' M) volume) = ∫ x, G (M.mulVec x) := by
    rw [integral_map (Matrix.toLin' M).continuous_of_finiteDimensional.aemeasurable
      hG.aestronglyMeasurable]
    simp [Matrix.toLin'_apply]
  rw [← h1, hmap, integral_smul_measure]
  have : |M.det⁻¹| = 1 := by rw [abs_inv, hdet, inv_one]
  rw [this]; simp

/-- The `k`-th partial derivative of the product bump, as a function. -/
def prodBumpPD (n : ℕ) (β : Fin n → ℝ) (k : Fin n) (y : Fin n → ℝ) : ℝ :=
  fderiv ℝ (prodBump n β) y (Pi.single k 1)

lemma prodBumpPD_continuous (β : Fin n → ℝ) (k : Fin n) : Continuous (prodBumpPD n β k) :=
  ((prodBump_contDiff β).continuous_fderiv NashEmbedding.Sobolev.infty_ne_zero).clm_apply continuous_const

lemma prodBumpPD_hasCompactSupport {β : Fin n → ℝ} (hβ : ∀ k, 1 ≤ β k) (k : Fin n) :
    HasCompactSupport (prodBumpPD n β k) :=
  (prodBump_hasCompactSupport hβ).fderiv_apply ℝ _

/-- Gram of the rotated bump: `Gram_χ = Mᵀ Gram_ψ M`, with `Gram_ψ` diagonal. -/
theorem gram_rotBump {β : Fin n → ℝ} (hβ : ∀ k, 1 ≤ β k) {M : Matrix (Fin n) (Fin n) ℝ}
    (hdet : |M.det| = 1) (i j : Fin n) :
    gram (rotBump n β M) i j
      = ∑ k, M k i * M k j *
          (β k * etaDerivMass n * ∏ l ∈ Finset.univ.erase k, etaMass n / β l) := by
  have hβ0 : ∀ k, 0 < β k := fun k => by linarith [hβ k]
  unfold gram
  simp_rw [fderiv_rotBump_single]
  have hsum : ∀ x : Fin n → ℝ,
      (∑ k, M k i * fderiv ℝ (prodBump n β) (M.mulVec x) (Pi.single k 1))
        * (∑ l, M l j * fderiv ℝ (prodBump n β) (M.mulVec x) (Pi.single l 1))
      = ∑ k, ∑ l, M k i * M l j *
          (fun y => prodBumpPD n β k y * prodBumpPD n β l y) (M.mulVec x) := by
    intro x
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [prodBumpPD]; ring
  simp_rw [hsum]
  have hint : ∀ k l : Fin n, Integrable
      (fun x => M k i * M l j * (fun y => prodBumpPD n β k y * prodBumpPD n β l y) (M.mulVec x)) := by
    intro k l
    refine Integrable.const_mul ?_ _
    refine integrable_comp_mulVec hdet
      ((prodBumpPD_continuous β k).mul (prodBumpPD_continuous β l)) ?_
    exact ((prodBumpPD_continuous β k).mul (prodBumpPD_continuous β l)).integrable_of_hasCompactSupport
      ((prodBumpPD_hasCompactSupport hβ l).mul_left)
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hint k l))]
  simp_rw [integral_finsetSum _ (fun l _ => hint _ l), integral_const_mul]
  have hcv : ∀ k l : Fin n,
      ∫ x, (fun y => prodBumpPD n β k y * prodBumpPD n β l y) (M.mulVec x)
        = gram (prodBump n β) k l := by
    intro k l
    rw [integral_comp_mulVec hdet (G := fun y => prodBumpPD n β k y * prodBumpPD n β l y)
      ((prodBumpPD_continuous β k).mul (prodBumpPD_continuous β l))]
    rfl
  simp_rw [hcv, gram_prodBump hβ0]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hlk
    rw [if_neg (Ne.symm hlk), mul_zero]
  · simp

/-! ## Amplitude -/

lemma gram_const_mul {χ : (Fin n → ℝ) → ℝ} (hχ : Differentiable ℝ χ) (A : ℝ) (i j : Fin n) :
    gram (fun x => A * χ x) i j = A ^ 2 * gram χ i j := by
  unfold gram
  simp_rw [fderiv_const_mul (hχ _), _root_.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

/-! ## Spectral assembly -/

/-! Orthogonality facts for a real orthogonal (unitary) matrix. -/
section Orthogonal

variable {U : Matrix (Fin n) (Fin n) ℝ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℝ)
include hU

lemma mul_transpose_eq_one_of_unitary : U * Uᵀ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hU
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h

lemma row_sq_sum_of_unitary (i : Fin n) : ∑ k, U i k ^ 2 = 1 := by
  have h := congrFun (congrFun (mul_transpose_eq_one_of_unitary hU) i) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  simpa [sq] using h

lemma abs_det_transpose_of_unitary : |Uᵀ.det| = 1 := by
  rw [Matrix.det_transpose]
  have h := Matrix.det_of_mem_unitary hU
  have h2 : U.det * U.det = 1 := by
    have := Unitary.star_mul_self_of_mem h
    simpa using this
  rcases mul_self_eq_one_iff.mp h2 with h3 | h3 <;> simp [h3]

lemma sum_sq_transpose_mulVec_of_unitary (x : Fin n → ℝ) :
    ∑ k, (Uᵀ.mulVec x) k ^ 2 = ∑ j, x j ^ 2 := by
  have h1 : (Uᵀ.mulVec x) ⬝ᵥ (Uᵀ.mulVec x) = x ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
      mul_transpose_eq_one_of_unitary hU, Matrix.one_mulVec]
  simpa [dotProduct, sq] using h1

/-- Row-wise Cauchy–Schwarz: `∑ₖ |Uᵢₖ| |Uⱼₖ| ≤ 1`. -/
lemma sum_abs_mul_abs_le_one_of_unitary (i j : Fin n) : ∑ k, |U i k| * |U j k| ≤ 1 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => |U i k|) (fun k => |U j k|)
  simp only [sq_abs] at hcs
  rw [row_sq_sum_of_unitary hU i, row_sq_sum_of_unitary hU j, mul_one] at hcs
  have hnn : 0 ≤ ∑ k, |U i k| * |U j k| :=
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith [hcs, hnn]

end Orthogonal

/-- **Bump with prescribed Gram matrix up to `K`.** For every real PSD matrix `B` and every
`K > 0` there is a `C^∞` compactly supported `χ` with `supp χ ⊂ (-π,π)ⁿ` and
`|∫ ∂ᵢχ ∂ⱼχ − Bᵢⱼ| ≤ K` for all `i, j`. -/
theorem exists_bump_gram_approx {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef)
    {K : ℝ} (hK : 0 < K) :
    ∃ χ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, χ x ≠ 0 → ∀ j : Fin n, |x j| < π) ∧
      ∀ i j, |gram χ i j - B i j| ≤ K := by
  classical
  set hH := hB.isHermitian with hHdef
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hUdef
  have hU : U ∈ Matrix.unitaryGroup (Fin n) ℝ := hH.eigenvectorUnitary.2
  set lam : Fin n → ℝ := hH.eigenvalues with hlam
  have hlam_nn : ∀ k, 0 ≤ lam k := fun k => hB.eigenvalues_nonneg k
  -- spectral decomposition entrywise
  have hspec : ∀ i j, B i j = ∑ k, U i k * U j k * lam k := by
    intro i j
    have h := hH.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [← hUdef] at h
    have h2 := congrFun (congrFun h i) j
    rw [h2, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Matrix.mul_diagonal, Matrix.transpose_apply, hlam]
    ring
  -- parameters
  set d : Fin n → ℝ := fun k => max (lam k) K with hd
  have hdK : ∀ k, K ≤ d k := fun k => le_max_right _ _
  set β : Fin n → ℝ := fun k => Real.sqrt (d k / K) with hβ
  have hβ1 : ∀ k, 1 ≤ β k := fun k => by
    simp only [hβ]
    rw [Real.one_le_sqrt]
    exact (one_le_div hK).mpr (hdK k)
  have hβsq : ∀ k, β k ^ 2 = d k / K := fun k => by
    simp only [hβ]
    rw [Real.sq_sqrt (div_nonneg (by linarith [hdK k]) hK.le)]
  have hβpos : ∀ k, 0 < β k := fun k => by linarith [hβ1 k]
  set Q : ℝ := ∏ l, etaMass n / β l with hQ
  have hQpos : 0 < Q := Finset.prod_pos fun l _ => div_pos (etaMass_pos n) (hβpos l)
  set r0 : ℝ := etaDerivMass n / etaMass n with hr0
  have hr0pos : 0 < r0 := div_pos (etaDerivMass_pos n) (etaMass_pos n)
  set A : ℝ := Real.sqrt (K / (Q * r0)) with hA
  have hAsq : A ^ 2 = K / (Q * r0) := by
    simp only [hA]; rw [Real.sq_sqrt (div_nonneg hK.le (mul_nonneg hQpos.le hr0pos.le))]
  -- the Gram diagonal of the product bump
  have hD : ∀ k, β k * etaDerivMass n * ∏ l ∈ Finset.univ.erase k, etaMass n / β l
      = β k ^ 2 * Q * r0 := by
    intro k
    set P : ℝ := ∏ l ∈ Finset.univ.erase k, etaMass n / β l with hP
    have h1 : Q = etaMass n / β k * P := by
      simp only [hQ, hP]; rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    have hM : etaMass n ≠ 0 := (etaMass_pos n).ne'
    have hβk : β k ≠ 0 := (hβpos k).ne'
    rw [h1, hr0]
    field_simp
  -- support of the rotated bump lies in (-π,π)ⁿ
  have hsupp : ∀ x, rotBump n β Uᵀ x ≠ 0 → ∀ j : Fin n, |x j| < π := by
    intro x hx j
    have hψ : prodBump n β (Uᵀ.mulVec x) ≠ 0 := hx
    have hk := abs_lt_of_prodBump_ne_zero hβ1 hψ
    have hsum : ∑ k, (Uᵀ.mulVec x) k ^ 2 < n * bumpRadius n ^ 2 := by
      have hn : 0 < n := Fin.pos j
      calc ∑ k, (Uᵀ.mulVec x) k ^ 2 < ∑ _k : Fin n, bumpRadius n ^ 2 :=
            Finset.sum_lt_sum_of_nonempty ⟨j, Finset.mem_univ j⟩ fun k _ => by
              have := hk k
              nlinarith [abs_nonneg ((Uᵀ.mulVec x) k), sq_abs ((Uᵀ.mulVec x) k)]
        _ = n * bumpRadius n ^ 2 := by simp
    rw [sum_sq_transpose_mulVec_of_unitary hU] at hsum
    have hxj : x j ^ 2 ≤ ∑ l, x l ^ 2 :=
      Finset.single_le_sum (fun l _ => sq_nonneg (x l)) (Finset.mem_univ j)
    have hρ := bumpRadius_mul_sqrt_lt n
    have hρ' : bumpRadius n * Real.sqrt n < π := by linarith [Real.pi_pos]
    have hsq : (bumpRadius n * Real.sqrt n) ^ 2 = n * bumpRadius n ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]; ring
    have hxj2 : x j ^ 2 < (bumpRadius n * Real.sqrt n) ^ 2 := by rw [hsq]; linarith
    have hpos : 0 ≤ bumpRadius n * Real.sqrt n := mul_nonneg (bumpRadius_pos n).le (Real.sqrt_nonneg _)
    calc |x j| = Real.sqrt (x j ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ < Real.sqrt ((bumpRadius n * Real.sqrt n) ^ 2) :=
          Real.sqrt_lt_sqrt (sq_nonneg _) hxj2
      _ = bumpRadius n * Real.sqrt n := Real.sqrt_sq hpos
      _ < π := hρ'
  refine ⟨fun x => A * rotBump n β Uᵀ x, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.mul (rotBump_contDiff β Uᵀ)
  · -- compact support
    apply HasCompactSupport.intro (isCompact_Icc (a := -(π • (1 : Fin n → ℝ)))
      (b := π • (1 : Fin n → ℝ)))
    intro x hx
    by_contra h
    apply hx
    have h' : rotBump n β Uᵀ x ≠ 0 := fun h0 => h (by simp [h0])
    constructor <;> intro j <;>
      simp only [Pi.neg_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] <;>
      linarith [abs_lt.mp (hsupp x h' j)]
  · intro x hx j
    exact hsupp x (fun h0 => hx (by simp [h0])) j
  · -- Gram estimate
    intro i j
    have hdiff : Differentiable ℝ (rotBump n β Uᵀ) :=
      (rotBump_contDiff β Uᵀ).differentiable NashEmbedding.Sobolev.infty_ne_zero
    rw [gram_const_mul hdiff, gram_rotBump hβ1 (abs_det_transpose_of_unitary hU)]
    simp_rw [hD, Matrix.transpose_apply]
    have hg : A ^ 2 * ∑ k, U i k * U j k * (β k ^ 2 * Q * r0) = ∑ k, U i k * U j k * d k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hβsq, hAsq]
      field_simp
    rw [hg, hspec i j, ← Finset.sum_sub_distrib]
    have hterm : ∀ k, U i k * U j k * d k - U i k * U j k * lam k = U i k * U j k * (d k - lam k) := by
      intro k; ring
    simp_rw [hterm]
    calc |∑ k, U i k * U j k * (d k - lam k)|
        ≤ ∑ k, |U i k * U j k * (d k - lam k)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |U i k| * |U j k| * |d k - lam k| := by simp_rw [abs_mul]
      _ ≤ ∑ k, |U i k| * |U j k| * K := by
          refine Finset.sum_le_sum fun k _ => ?_
          have h1 : |d k - lam k| ≤ K := by
            rw [abs_of_nonneg (by simp [hd])]
            simp only [hd]
            rcases le_total (lam k) K with h | h
            · rw [max_eq_right h]; linarith [hlam_nn k]
            · rw [max_eq_left h]; linarith
          exact mul_le_mul_of_nonneg_left h1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (∑ k, |U i k| * |U j k|) * K := by rw [Finset.sum_mul]
      _ ≤ 1 * K := by gcongr; exact sum_abs_mul_abs_le_one_of_unitary hU i j
      _ = K := one_mul K

end NashEmbedding

end
