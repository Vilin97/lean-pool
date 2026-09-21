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
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Summability
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Differentiation
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.FourierSynthesis
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Periodicity
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Periodization
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.MultiplicationSharp

/-!
# Regularity and multiplicativity of Fourier synthesis

Bridge lemmas from momentum space back to position space, needed for
Theorem B (Günther's perturbation theorem), whose fixed-point iteration is
run on coefficient sequences.

* **B1 (regularity).** If `a : ℤⁿ → ℂ` is rapidly decaying (lies in every
  weighted `ℓ²_(s)`), then its Fourier synthesis `ǎ(θ) = ∑ aₘ eₘ(θ)` is
  `C^∞`, `2πℤⁿ`-periodic, and its partial derivatives are the syntheses of
  the formal derivative coefficients: `∂ⱼ ǎ = (i mⱼ aₘ)ˇ`.
* **B2 (multiplicativity).** If `a, b ∈ ℓ¹(ℤⁿ)`, then the synthesis of the
  convolution `a ∗ b` is the pointwise product `ǎ · b̌`.

Conventions: `fourierSynthesis n a θ = ∑' m, a m * fourierExp n m θ` with
`fourierExp n m θ = exp(i ∑ⱼ mⱼ θⱼ)`; `partialCoeff j a m = i * mⱼ * a m`;
`seqConv a b m = ∑' i, a i * b (m - i)`; `partialDeriv j g θ = fderiv ℝ g θ (eⱼ)`;
smoothness is `ContDiff ℝ ∞` (`open scoped ContDiff`), never `⊤`.
-/

open scoped BigOperators ContDiff
open NashEmbedding.Sobolev Complex

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-- A coefficient sequence is *rapidly decaying* if it lies in every weighted
`ℓ²_(s)`, `s ∈ ℝ`. This is the momentum-space image of `C^∞(𝕋ⁿ)`
(cf. `smooth_periodic_memSobolevDistrib`). -/
def IsRapidDecay (n : ℕ) (a : (Fin n → ℤ) → ℂ) : Prop :=
  ∀ s : ℝ, MemSobolev n s a

/-! ## Elementary consequences of rapid decay -/

/-- Rapid decay implies absolute summability (when `n ≥ 1`). -/
lemma IsRapidDecay.summable_norm (hn : 0 < n) {a : (Fin n → ℤ) → ℂ}
    (ha : IsRapidDecay n a) : Summable (fun m => ‖a m‖) := by
  have h : (0 : ℝ) < n := by exact_mod_cast hn
  exact summable_norm_of_memSobolev hn (by linarith : (n : ℝ) < 2 * (n : ℝ)) (ha n)

/-- The formal derivative of a rapidly decaying sequence is rapidly decaying. -/
lemma IsRapidDecay.partialCoeff {a : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a)
    (j : Fin n) : IsRapidDecay n (partialCoeff j a) := by
  intro s
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (weight_nonneg _ _) (sq_nonneg _)) (fun m => ?_) (ha (s + 1))
  rw [norm_partialCoeff, mul_pow]
  have h1 : |(m j : ℝ)| ^ 2 ≤ 1 + ∑ i : Fin n, ((m i : ℝ)) ^ 2 := by
    have hle := Finset.single_le_sum (f := fun i : Fin n => ((m i : ℝ)) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    rw [sq_abs]; linarith
  have h2 : weight n s m * |(m j : ℝ)| ^ 2 ≤ weight n (s + 1) m := by
    rw [← weight_mul s 1 m]
    have hw : weight n 1 m = 1 + ∑ i : Fin n, ((m i : ℝ)) ^ 2 := by
      simp [weight, Real.rpow_one]
    rw [hw]
    exact mul_le_mul_of_nonneg_left h1 (weight_nonneg _ _)
  calc weight n s m * (|(m j : ℝ)| ^ 2 * ‖a m‖ ^ 2)
      = (weight n s m * |(m j : ℝ)| ^ 2) * ‖a m‖ ^ 2 := by ring
    _ ≤ weight n (s + 1) m * ‖a m‖ ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

/-! ### Auxiliary material for smoothness -/

/-- The frequency `m` viewed as a continuous linear functional `θ ↦ ∑ⱼ mⱼ θⱼ`. -/
private def freqCLM (n : ℕ) (m : Fin n → ℤ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ j, (m j : ℝ) • (ContinuousLinearMap.proj j)

private lemma freqCLM_apply (m : Fin n → ℤ) (θ : Fin n → ℝ) :
    freqCLM n m θ = ∑ j, (m j : ℝ) * θ j := by
  simp [freqCLM, _root_.sum_apply]

private lemma norm_freqCLM_le (m : Fin n → ℤ) : ‖freqCLM n m‖ ≤ ∑ j, |(m j : ℝ)| := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun θ => ?_
  rw [freqCLM_apply, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  have hj : |θ j| ≤ ‖θ‖ := by simpa using norm_le_pi_norm θ j
  exact mul_le_mul_of_nonneg_left hj (abs_nonneg _)

private lemma iteratedDeriv_expI (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) t
      = Complex.I ^ k * Complex.exp (Complex.I * (t : ℂ)) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have he : deriv (iteratedDeriv k fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) t
          = deriv (fun t : ℝ => Complex.I ^ k * Complex.exp (Complex.I * (t : ℂ))) t :=
        Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall ih)
      rw [he]
      have h1 : HasDerivAt (fun t : ℝ => (Complex.I * (t : ℂ))) Complex.I t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I
      rw [((h1.cexp).const_mul (Complex.I ^ k)).deriv]
      ring

private lemma contDiff_expI : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

private lemma norm_iteratedFDeriv_expI (k : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) t‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expI]
  simp [Complex.norm_exp]

/-- Every iterated derivative of `eₘ` is bounded by `(∑ⱼ |mⱼ|)^k`. -/
private lemma norm_iteratedFDeriv_fourierExp_le (m : Fin n → ℤ) (k : ℕ) (θ : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ k (fourierExp n m) θ‖ ≤ (∑ j, |(m j : ℝ)|) ^ k := by
  have hcomp : fourierExp n m
      = (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) ∘ (freqCLM n m) := by
    funext θ; simp [fourierExp, Function.comp, freqCLM_apply]
  have hk : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ contDiff_expI θ hk]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_expI]
  simp only [one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_freqCLM_le m) k

/-- `∑ⱼ |mⱼ| ≤ n · (1+|m|²)^{1/2}`. -/
private lemma sum_abs_le_weight (m : Fin n → ℤ) :
    ∑ j, |(m j : ℝ)| ≤ (n : ℝ) * weight n (1 / 2 : ℝ) m := by
  have hb : ∀ j : Fin n, |(m j : ℝ)| ≤ weight n (1 / 2 : ℝ) m := by
    intro j
    have hle := Finset.single_le_sum (f := fun i : Fin n => ((m i : ℝ)) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have hw : weight n (1 / 2 : ℝ) m = Real.sqrt (1 + ∑ i : Fin n, ((m i : ℝ)) ^ 2) := by
      rw [weight, Real.sqrt_eq_rpow]
    have hle' : (m j : ℝ) ^ 2 ≤ ∑ i : Fin n, ((m i : ℝ)) ^ 2 := hle
    rw [hw]
    exact Real.abs_le_sqrt (by linarith)
  calc ∑ j, |(m j : ℝ)| ≤ ∑ _j : Fin n, weight n (1 / 2 : ℝ) m :=
        Finset.sum_le_sum fun j _ => hb j
    _ = (n : ℝ) * weight n (1 / 2 : ℝ) m := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private lemma weight_half_pow (k : ℕ) (m : Fin n → ℤ) :
    weight n (1 / 2 : ℝ) m ^ k = weight n (k / 2 : ℝ) m := by
  rw [weight, weight, ← Real.rpow_natCast (((1 : ℝ) + ∑ i : Fin n, ((m i : ℝ)) ^ 2) ^ (1 / 2 :
      ℝ)) k,
    ← Real.rpow_mul (le_trans zero_le_one (one_le_weight_base m))]
  ring_nf

/-- Rapid decay gives summability against every weight. -/
private lemma summable_weight_mul_norm (hn : 0 < n) {a : (Fin n → ℤ) → ℂ}
    (ha : IsRapidDecay n a) (t : ℝ) : Summable (fun m => weight n t m * ‖a m‖) := by
  have hnn : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ∀ m : Fin n → ℤ,
      weight n ((n : ℝ) + 2 * t) m = weight n n m * (weight n t m * weight n t m) := by
    intro m; rw [weight_mul, weight_mul]; congr 1; ring
  have hnorm : ∀ m : Fin n → ℤ, ‖(weight n t m : ℂ) * a m‖ = weight n t m * ‖a m‖ := by
    intro m
    simp [abs_of_nonneg (weight_nonneg t m)]
  have hmem : MemSobolev n n (fun m => (weight n t m : ℂ) * a m) := by
    refine (ha ((n : ℝ) + 2 * t)).congr fun m => ?_
    rw [hnorm, mul_pow, hw m]; ring
  have hs := summable_norm_of_memSobolev hn (by linarith : (n : ℝ) < 2 * (n : ℝ)) hmem
  exact hs.congr hnorm

/-! ## B1: regularity of Fourier synthesis -/

/-- **B1 (smoothness).** The Fourier synthesis of a rapidly decaying sequence is `C^∞`. -/
theorem fourierSynthesis_contDiff (hn : 0 < n) {a : (Fin n → ℤ) → ℂ}
    (ha : IsRapidDecay n a) :
    ContDiff ℝ ∞ (fourierSynthesis n a) := by
  have hfun : fourierSynthesis n a
      = fun θ => ∑' m : Fin n → ℤ, (fun m θ => a m * fourierExp n m θ) m θ := rfl
  rw [hfun]
  refine contDiff_tsum (N := (⊤ : ℕ∞))
    (v := fun k m => (n : ℝ) ^ k * (weight n (k / 2 : ℝ) m * ‖a m‖)) ?_ ?_ ?_
  · exact fun m => contDiff_const.mul (fourierExp_contDiff m)
  · exact fun k _ => (summable_weight_mul_norm hn ha (k / 2 : ℝ)).mul_left _
  · intro k m θ _
    have hsmul : (fun θ => a m * fourierExp n m θ) = a m • fourierExp n m := by
      funext θ; simp [smul_eq_mul]
    have hcd : ContDiffAt ℝ (k : WithTop ℕ∞) (fourierExp n m) θ :=
      ((fourierExp_contDiff m).of_le (by exact_mod_cast le_top)).contDiffAt
    rw [hsmul, iteratedFDeriv_const_smul_apply hcd, norm_smul]
    have h1 : ‖iteratedFDeriv ℝ k (fourierExp n m) θ‖ ≤ ((n : ℝ) * weight n (1 / 2 : ℝ) m) ^ k :=
      (norm_iteratedFDeriv_fourierExp_le m k θ).trans
        (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (sum_abs_le_weight m) k)
    have h2 : ((n : ℝ) * weight n (1 / 2 : ℝ) m) ^ k = (n : ℝ) ^ k * weight n (k / 2 : ℝ) m := by
      rw [mul_pow, weight_half_pow]
    rw [h2] at h1
    calc ‖a m‖ * ‖iteratedFDeriv ℝ k (fourierExp n m) θ‖
        ≤ ‖a m‖ * ((n : ℝ) ^ k * weight n (k / 2 : ℝ) m) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (n : ℝ) ^ k * (weight n (k / 2 : ℝ) m * ‖a m‖) := by ring

/-- **B1 (periodicity).** The Fourier synthesis of any coefficient sequence is
`2πℤⁿ`-periodic (the `IsPeriodic2Pi` form of `fourierSynthesis_periodic`); no
summability is needed since each term `eₘ` is periodic and `tsum` respects
termwise equality. -/
theorem fourierSynthesis_isPeriodic2Pi {a : (Fin n → ℤ) → ℂ} :
    IsPeriodic2Pi (fourierSynthesis n a) := by
  intro x k
  refine tsum_congr fun m => ?_
  rw [fourierExp_isPeriodic2Pi m x k]

/-- **B1 (derivatives).** Partial derivatives of the synthesis are syntheses of the
formal derivative coefficients: `∂ⱼ ǎ = (partialCoeff j a)ˇ`. -/
theorem partialDeriv_fourierSynthesis (hn : 0 < n) {a : (Fin n → ℤ) → ℂ}
    (ha : IsRapidDecay n a) (j : Fin n) :
    partialDeriv j (fourierSynthesis n a) = fourierSynthesis n (partialCoeff j a) := by
  funext θ
  have hdiff : Differentiable ℝ (fourierSynthesis n a) :=
    (fourierSynthesis_contDiff hn ha).differentiable infty_ne_zero
  have h1 : HasFDerivAt (fourierSynthesis n a) (fderiv ℝ (fourierSynthesis n a) θ) θ :=
    (hdiff θ).hasFDerivAt
  have h2 := hasDerivAt_update_of_hasFDerivAt h1 j
  have h3 := hasDerivAt_fourierSeries_partial hn (ha.summable_norm hn) j
    ((ha.partialCoeff j).summable_norm hn) θ
  exact h2.unique h3

/-- Round trip: the standard Fourier coefficients of the synthesis of a rapidly
decaying sequence recover the sequence (specialisation of
`stdFourierCoeff_fourierSynthesis`). -/
theorem stdFourierCoeff_fourierSynthesis_of_rapidDecay (hn : 0 < n)
    {a : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a) (m : Fin n → ℤ) :
    stdFourierCoeff n (fourierSynthesis n a) m = a m :=
  stdFourierCoeff_fourierSynthesis (ha.summable_norm hn) m

/-! ## B2: synthesis of a convolution is the product of syntheses -/

/-- `e_{m₁+m₂} = e_{m₁} · e_{m₂}`. -/
private lemma fourierExp_add (m₁ m₂ : Fin n → ℤ) (θ : Fin n → ℝ) :
    fourierExp n (m₁ + m₂) θ = fourierExp n m₁ θ * fourierExp n m₂ θ := by
  have hsum : (∑ j : Fin n, (((m₁ + m₂) j : ℤ) : ℝ) * θ j)
      = (∑ j : Fin n, (m₁ j : ℝ) * θ j) + (∑ j : Fin n, (m₂ j : ℝ) * θ j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.add_apply]
    push_cast
    ring
  simp only [fourierExp, hsum]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The shear `(i, j) ↦ (i + j, i)` of `ℤⁿ × ℤⁿ`. -/
private def shearEquiv (n : ℕ) :
    ((Fin n → ℤ) × (Fin n → ℤ)) ≃ ((Fin n → ℤ) × (Fin n → ℤ)) where
  toFun p := (p.1 + p.2, p.1)
  invFun q := (q.2, q.1 - q.2)
  left_inv p := by simp
  right_inv q := by simp

private lemma summable_norm_prod_shear {a b : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖)) (hb : Summable (fun m => ‖b m‖)) :
    Summable (fun q : (Fin n → ℤ) × (Fin n → ℤ) => ‖a q.2‖ * ‖b (q.1 - q.2)‖) := by
  have hmul : Summable (fun p : (Fin n → ℤ) × (Fin n → ℤ) => ‖a p.1‖ * ‖b p.2‖) :=
    ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact ((shearEquiv n).symm.summable_iff).mpr hmul

/-- **B2.** For `a, b ∈ ℓ¹(ℤⁿ)`, `(a ∗ b)ˇ = ǎ · b̌` pointwise. -/
theorem fourierSynthesis_seqConv {a b : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖)) (hb : Summable (fun m => ‖b m‖))
    (θ : Fin n → ℝ) :
    fourierSynthesis n (seqConv a b) θ =
      fourierSynthesis n a θ * fourierSynthesis n b θ := by
  have hf : Summable (fun i : Fin n → ℤ => ‖a i * fourierExp n i θ‖) := by
    simpa [norm_fourierExp] using ha
  have hg : Summable (fun i : Fin n → ℤ => ‖b i * fourierExp n i θ‖) := by
    simpa [norm_fourierExp] using hb
  have key := tsum_mul_tsum_of_summable_norm hf hg
  have hP : Summable (fun q : (Fin n → ℤ) × (Fin n → ℤ) => ‖a q.2‖ * ‖b (q.1 - q.2)‖) :=
    summable_norm_prod_shear ha hb
  have hH : Summable (fun q : (Fin n → ℤ) × (Fin n → ℤ) =>
      a q.2 * b (q.1 - q.2) * fourierExp n q.1 θ) := by
    refine Summable.of_norm (hP.congr fun q => ?_)
    rw [norm_mul, norm_mul, norm_fourierExp, mul_one]
  have hreindex : (∑' p : (Fin n → ℤ) × (Fin n → ℤ),
      (a p.1 * fourierExp n p.1 θ) * (b p.2 * fourierExp n p.2 θ))
      = ∑' q : (Fin n → ℤ) × (Fin n → ℤ), a q.2 * b (q.1 - q.2) * fourierExp n q.1 θ := by
    rw [← (shearEquiv n).tsum_eq
      (fun q : (Fin n → ℤ) × (Fin n → ℤ) => a q.2 * b (q.1 - q.2) * fourierExp n q.1 θ)]
    refine tsum_congr fun p => ?_
    simp only [shearEquiv, Equiv.coe_fn_mk, add_sub_cancel_left]
    rw [fourierExp_add]
    ring
  have hprod : fourierSynthesis n a θ * fourierSynthesis n b θ
      = ∑' q : (Fin n → ℤ) × (Fin n → ℤ), a q.2 * b (q.1 - q.2) * fourierExp n q.1 θ := by
    rw [fourierSynthesis, fourierSynthesis, key, hreindex]
  rw [hprod, hH.tsum_prod, fourierSynthesis]
  refine tsum_congr fun m => ?_
  rw [seqConv, ← tsum_mul_right]

/-- The convolution of two `ℓ¹` sequences is `ℓ¹` (Young `ℓ¹ ∗ ℓ¹ ⊂ ℓ¹`), so B2 can be
iterated. -/
lemma summable_norm_seqConv {a b : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖)) (hb : Summable (fun m => ‖b m‖)) :
    Summable (fun m => ‖seqConv a b m‖) := by
  have hP : Summable (fun q : (Fin n → ℤ) × (Fin n → ℤ) => ‖a q.2‖ * ‖b (q.1 - q.2)‖) :=
    summable_norm_prod_shear ha hb
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hP.prod
  rw [seqConv]
  refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr fun i => by rw [norm_mul])
  refine (hP.prod_factor m).congr fun i => ?_
  rw [norm_mul]

end NashEmbedding.Sobolev

end
